//! Benchmarks of the general-purpose SNARK path, mirroring `fp-blackbox/benches/vouch.rs`: key
//! generation, credential issuance and vouching (Schnorr signatures over Jubjub, the
//! Pedersen-hash Merkle tree, the DDH PRF), and Groth16 proving and verification of the ShowVRC
//! presentation circuit over BLS12-381 in `tests/common/show_vrc.rs`. Groth16 setup is a one-time
//! cost per circuit and is not timed; the sizes of the keys and the proof are printed instead.
//!
//! [CGLMPS26, §10] measures on one CPU core. `fp-snark` builds arkworks with its `parallel`
//! feature, so these benchmarks limit rayon to one thread unless `RAYON_NUM_THREADS` is set.
//! Run them with `cargo bench -p fp-snark --bench show_vrc`: a `cargo bench` that selects both
//! workspace members unifies their dependency features.
//!
//! [CGLMPS26]: https://eprint.iacr.org/2026/333

#[path = "../tests/common/show_vrc.rs"]
mod show_vrc;

use ark_bls12_381::Bls12_381;
use ark_ed_on_bls12_381::EdwardsConfig;
use ark_groth16::{Groth16, Proof, ProvingKey, VerifyingKey};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_serialize::CanonicalSerialize;
use ark_snark::SNARK;
use criterion::{criterion_group, criterion_main, BatchSize, Criterion, SamplingMode};
use rand_chacha::{rand_core::SeedableRng, ChaCha8Rng};

use fp_snark::credential::{CredentialSchema, Leaf};
use fp_snark::merkle_tree::MerkleTree;
use fp_snark::prf::ddh;
use fp_snark::signature::SignatureScheme;
use fp_snark::utils;
use fp_snark::vector_commitment::bytes::pedersen::{JZVectorCommitmentParams, JZVectorDB};
use show_vrc::*;

/// Limits rayon's global pool to one thread unless `RAYON_NUM_THREADS` is set.
fn limit_threads() {
    if std::env::var_os("RAYON_NUM_THREADS").is_none() {
        rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build_global()
            .expect("the rayon pool is configured before its first use");
    }
}

fn report_sizes(pk: &ProvingKey<Bls12_381>, vk: &VerifyingKey<Bls12_381>, proof: &Proof<Bls12_381>) {
    let cs = ConstraintSystem::<ConstraintF>::new_ref();
    setup_witness(&Scenario::honest()).generate_constraints(cs.clone()).unwrap();
    println!(
        "ShowVRC circuit: {} constraints, {} public inputs; Groth16 proving key {} bytes compressed \
         ({} uncompressed), verifying key {} bytes, proof {} bytes (compressed); rayon threads: {}",
        cs.num_constraints(),
        cs.num_instance_variables() - 1,
        pk.compressed_size(),
        pk.uncompressed_size(),
        vk.compressed_size(),
        proof.compressed_size(),
        rayon::current_num_threads(),
    );
}

fn show_vrc_benchmark(c: &mut Criterion) {
    limit_threads();
    let mut rng = ChaCha8Rng::from_seed([0u8; 32]);
    let schnorr_parameters = S::setup(&mut rng).unwrap();
    // `fp-blackbox` names its benchmarks without a prefix; both crates write to the same
    // `target/criterion`, so these are grouped under `snark`.
    let mut group = c.benchmark_group("snark");

    // 0. Key generation: a Schnorr key pair for the issuer; a Schnorr key pair and a PRF key for
    // the user
    group.bench_function("issuer_keygen", |b| b.iter(|| S::keygen(&schnorr_parameters, &mut rng).unwrap()));
    group.bench_function("user_keygen", |b| {
        b.iter(|| (S::keygen(&schnorr_parameters, &mut rng).unwrap(), ddh::keygen::<EdwardsConfig, _>(&mut rng)))
    });
    let (issuer_public_key, issuer_secret_key) = S::keygen(&schnorr_parameters, &mut rng).unwrap();
    let (user_public_key, user_secret_key) = S::keygen(&schnorr_parameters, &mut rng).unwrap();
    let prf_key = ddh::keygen::<EdwardsConfig, _>(&mut rng);

    // The user derives the issuer-specific pseudonym k_U = PRF_K(ipk) that the credential certifies
    let issuer_key = encode_public_key(&issuer_public_key);
    group.bench_function("derive_pseudonym", |b| b.iter(|| ddh::evaluate::<EdwardsConfig>(&prf_key, &issuer_key)));
    let pseudonym = ddh::evaluate::<EdwardsConfig>(&prf_key, &issuer_key);

    // 1. Issue credential: encode the attributes into leaves, build the Merkle tree and sign
    // (schema id || root). `JZVectorDB::new` also verifies every path of the new tree, which is
    // not part of issuance, so the tree is built directly from the database's parameters.
    let schema = schema();
    let values = attribute_values(&user_public_key, &pseudonym, &Scenario::honest());
    let reference = JZVectorDB::<MT, Leaf>::new(
        JZVectorCommitmentParams::<MT>::trusted_setup(&mut rng),
        &CredentialSchema::pad_leaves_to_pow2(schema.encode_leaves(&values).unwrap()),
    );
    let params = &reference.vc_params;
    let issue = |rng: &mut ChaCha8Rng| {
        let leaves = CredentialSchema::pad_leaves_to_pow2(schema.encode_leaves(&values).unwrap());
        let leaves: Vec<Vec<u8>> = leaves.iter().map(utils::serialize).collect();
        let tree = MerkleTree::<MT>::new(&params.leaf_crh_params, &params.two_to_one_params, leaves.iter().map(|leaf| leaf.as_slice()))
            .unwrap();
        let root = tree.root();
        let certification = S::sign(&schnorr_parameters, &issuer_secret_key, &issuer_message(&schema, &root), rng).unwrap();
        (root, certification)
    };
    assert_eq!(issue(&mut rng).0, reference.commitment(), "the issued root must match JZVectorDB's");
    group.bench_function("issue_credential", |b| b.iter(|| issue(&mut rng)));

    // 2. Vouch: the user's Schnorr signature on the statement that the show proves
    let statement = hash_statement("Bob is a cryptographer");
    group.bench_function("generate_vouch", |b| {
        b.iter(|| S::sign(&schnorr_parameters, &user_secret_key, &statement, &mut rng).unwrap())
    });
    group.finish();

    // 3. Groth16 proof of the ShowVRC circuit; witnesses are generated outside the measurement
    let (pk, vk) = circuit_setup();
    let circuit = setup_witness(&Scenario::honest());
    let public_input = public_inputs(&circuit);
    let proof = Groth16::<Bls12_381>::prove(&pk, circuit, &mut rng).unwrap();
    let pvk = Groth16::<Bls12_381>::process_vk(&vk).unwrap();
    assert!(Groth16::<Bls12_381>::verify_with_processed_vk(&pvk, &public_input, &proof).unwrap());
    report_sizes(&pk, &vk, &proof);

    let mut group = c.benchmark_group("snark_show_vrc");
    group.sampling_mode(SamplingMode::Flat).sample_size(10);
    group.bench_function("groth16_prove", |b| {
        b.iter_batched(
            || setup_witness(&Scenario::honest()),
            |circuit| Groth16::<Bls12_381>::prove(&pk, circuit, &mut rng).unwrap(),
            BatchSize::PerIteration,
        )
    });
    // 4. Verification with the processed verifying key, as a verifier checking many proofs would
    group.bench_function("groth16_verify", |b| {
        b.iter(|| Groth16::<Bls12_381>::verify_with_processed_vk(&pvk, &public_input, &proof).unwrap())
    });
    group.finish();
}

criterion_group!(benches, show_vrc_benchmark);
criterion_main!(benches);
