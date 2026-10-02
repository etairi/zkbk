//! Tests of the ShowVRC presentation circuit over BLS12-381 in `common/show_vrc.rs`: the honest
//! show is satisfiable and proves and verifies with Groth16, and negative tests check that each
//! binding of the circuit is enforced. Two more tests demonstrate the hole in the unpinned
//! `app6`-style Merkle opening and the linearity of the Pedersen-CRH PRF of `fp_snark::prf`.

mod common;

use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField};
use ark_groth16::Groth16;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::*;
use ark_serialize::CanonicalSerialize;
use ark_snark::SNARK;
use rand_chacha::rand_core::SeedableRng;

use common::show_vrc::*;
use fp_snark::prf::{self, JZPRFInstance, JZPRFParams};
use fp_snark::utils;

type H = prf::config::ed_on_bls12_381::Hash;

/// First 32 bytes of the PRF output: the x-coordinate of the Pedersen-hash point.
fn prf_output(prf: &JZPRFInstance<H>) -> Vec<u8> {
    prf.evaluate().iter().take(32).cloned().collect()
}

// ---------------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------------

#[test]
fn honest_show_is_satisfiable_and_reports_size() {
    let cs = ConstraintSystem::<ConstraintF>::new_ref();
    setup_witness(&Scenario::honest()).generate_constraints(cs.clone()).unwrap();
    assert!(cs.is_satisfied().unwrap());
    println!(
        "ShowVRC circuit over BLS12-381: {} constraints, {} witness variables, {} public inputs",
        cs.num_constraints(),
        cs.num_witness_variables(),
        cs.num_instance_variables() - 1
    );
}

/// Groth16 over BLS12-381 end to end, plus checks on the serialized artefacts: a 192-byte
/// compressed proof (G1 || G2 || G1 in ZCash/IETF encoding) and a verifying key with
/// `#public inputs + 1` G1 elements.
#[test]
fn groth16_bls12_381_prove_verify_and_compressed_encoding() {
    let mut rng = rand_chacha::ChaCha8Rng::from_seed([2u8; 32]);

    let now = std::time::Instant::now();
    let (pk, vk) = circuit_setup();
    println!("Groth16 setup time: {:.2?}", now.elapsed());

    let circuit = setup_witness(&Scenario::honest());
    let public_input = public_inputs(&circuit);

    let now = std::time::Instant::now();
    let proof = Groth16::<Bls12_381>::prove(&pk, circuit, &mut rng).unwrap();
    println!("Prover time: {:.2?}", now.elapsed());

    let now = std::time::Instant::now();
    assert!(Groth16::<Bls12_381>::verify(&vk, &public_input, &proof).unwrap());
    println!("Verifier time: {:.2?}", now.elapsed());

    // a wrong public input (e.g. another context pseudonym) must not verify
    let mut wrong_input = public_input.clone();
    wrong_input[2] += Fr::from(1u64);
    assert!(!Groth16::<Bls12_381>::verify(&vk, &wrong_input, &proof).unwrap());

    // ZCash compressed encoding
    let mut proof_bytes = Vec::new();
    proof.serialize_compressed(&mut proof_bytes).unwrap();
    assert_eq!(proof_bytes.len(), 48 + 96 + 48, "compressed Groth16 proof must be 192 bytes");
    let (a, b, c) = (
        {
            let mut v = Vec::new();
            proof.a.serialize_compressed(&mut v).unwrap();
            v
        },
        {
            let mut v = Vec::new();
            proof.b.serialize_compressed(&mut v).unwrap();
            v
        },
        {
            let mut v = Vec::new();
            proof.c.serialize_compressed(&mut v).unwrap();
            v
        },
    );
    assert_eq!((a.len(), b.len(), c.len()), (48, 96, 48));
    // ZCash serialization: big-endian x with the compression flag in the most significant bit
    assert!(a[0] & 0x80 != 0 && b[0] & 0x80 != 0 && c[0] & 0x80 != 0);
    assert_eq!(proof_bytes, [a.clone(), b.clone(), c.clone()].concat());
    assert_eq!(vk.gamma_abc_g1.len(), public_input.len() + 1);
    let mut vk_bytes = Vec::new();
    vk.serialize_compressed(&mut vk_bytes).unwrap();
    println!("compressed proof: {} bytes, compressed vk: {} bytes", proof_bytes.len(), vk_bytes.len());
    println!("proof (hex): {}", hex::encode(&proof_bytes));
}

#[test]
fn predicate_failures_are_rejected() {
    // not an allowed citizenship
    let mut s = Scenario::honest();
    s.citizenship = Country::India;
    assert!(!is_satisfied(&s));
    // too young: born one day after the cut-off
    let mut s = Scenario::honest();
    s.date_of_birth = (SHOW_DATE.0 - 18, SHOW_DATE.1, SHOW_DATE.2 + 1);
    assert!(!is_satisfied(&s));
    // exactly on the cut-off is fine
    let mut s = Scenario::honest();
    s.date_of_birth = (SHOW_DATE.0 - 18, SHOW_DATE.1, SHOW_DATE.2);
    assert!(is_satisfied(&s));
    // wrong occupation
    let mut s = Scenario::honest();
    s.occupation = Occupation::Developer;
    assert!(!is_satisfied(&s));
}

/// The prover has an Indian citizenship but a `Cryptographer` occupation, whose label (0) is
/// also the label of `USA`. Opening the occupation leaf in the citizenship slot must fail.
#[test]
fn opening_another_leaf_in_the_citizenship_slot_is_rejected() {
    let mut s = Scenario::honest();
    s.citizenship = Country::India;
    s.occupation = Occupation::Cryptographer;
    assert_eq!(Country::USA as u8, Occupation::Cryptographer as u8);
    s.citizenship_opening_from = Some(OCCUPATION_INDEX);
    assert!(!is_satisfied(&s));
}

/// Changing the opened bytes without the issuer's signature: the Merkle root no longer matches.
#[test]
fn tampered_leaf_is_rejected() {
    let mut s = Scenario::honest();
    s.citizenship = Country::India;
    s.tamper_citizenship_leaf = true;
    assert!(!is_satisfied(&s));
}

/// The context pseudonym must be derived from the same PRF key as the certified pseudonym.
#[test]
fn context_pseudonym_under_another_key_is_rejected() {
    let mut s = Scenario::honest();
    s.wrong_context_key = true;
    assert!(!is_satisfied(&s));
}

/// The hole in the `first_person_test_app{5,6}` circuits: the leaf position of a Merkle opening
/// is a free witness, so "leaf 0 (citizenship) == USA" can be satisfied by opening any leaf
/// whose first byte happens to be `USA`, e.g. an age of 1. Pinning the position closes it.
#[test]
fn app6_style_unpinned_opening_lets_the_prover_pick_the_attribute() {
    use ark_ff::BigInteger256;
    use fp_snark::vector_commitment::bytes::sha256 as sha;

    const APP6_USA: u8 = 1; // `Country::USA = 1` in app6
    let mut rng = rand_chacha::ChaCha8Rng::from_seed([3u8; 32]);
    let vc_params = sha::JZVectorCommitmentParams::trusted_setup(&mut rng);
    // app6 layout: [citizenship, age, profession, organ_donor], one byte each
    let attributes: Vec<BigInteger256> = [91u8 /* India */, 1 /* age */, 0, 0].iter().map(|&b| BigInteger256::from(b)).collect();
    let db = sha::JZVectorDB::<BigInteger256>::new(&vc_params, &attributes);

    let check = |opened_index: usize, pin: bool| -> bool {
        let cs = ConstraintSystem::<ConstraintF>::new_ref();
        let params_var = sha::constraints::JZVectorCommitmentParamsVar::<ConstraintF>::new_constant(cs.clone(), &vc_params).unwrap();
        let proof = sha::JZVectorCommitmentOpeningProof::<BigInteger256> {
            root: db.commitment(),
            record: db.get_record(opened_index).clone(),
            path: db.proof(opened_index),
        };
        let mut proof_var = sha::constraints::JZVectorCommitmentOpeningProofVar::<ConstraintF>::new_witness(cs.clone(), || Ok(&proof)).unwrap();
        if pin {
            sha::constraints::generate_constraints_at_position(cs.clone(), &params_var, &mut proof_var, 0);
        } else {
            sha::constraints::generate_constraints(cs.clone(), &params_var, &proof_var);
        }
        // app6's check: "only American vouches are allowed"
        proof_var.leaf_var[0].enforce_equal(&UInt8::constant(APP6_USA)).unwrap();
        cs.is_satisfied().unwrap()
    };

    // honest opening of the citizenship leaf fails the check (India)
    assert!(!check(0, false));
    // ... but opening the *age* leaf satisfies it when the position is unconstrained
    assert!(check(1, false), "the unpinned circuit accepts a leaf from the wrong position");
    // pinning the position to the citizenship slot closes the hole
    assert!(!check(1, true));
}

/// Known issue of `fp_snark::prf` (the circuit above uses `fp_snark::prf::ddh` instead): it
/// builds the PRF from the Pedersen hash `P` used in [CGLMPS26, §10] as `x(P(x || k))`. `P` is
/// *linear* in its input bits, so for inputs `x_1, x_2` of equal length
/// `P(x_2 || k) = P(x_1 || k) + Δ` with the public `Δ = P(x_2 || 0) - P(x_1 || 0)`. Given
/// `p_1 = x(P(x_1 || k))` for a public `x_1` (e.g. an issuer identity or a context), anyone can
/// take the two points with x-coordinate `p_1` (`Q_1` and `-Q_1 + T`, where `T = (0, -1)` has
/// order two), add `Δ` and obtain `p_2 = x(P(x_2 || k))`. Outputs on all inputs of the same
/// length are thus predictable from one of them, which links pseudonyms across issuers or
/// contexts, contrary to the unlinkability goals of [CGLMPS26, §2.2] and to the PRF assumption
/// in the proof of §7.2. `prf_ddh_vs_pedersen_bls12_381.rs` checks the equal-length condition.
#[test]
fn known_issue_pedersen_crh_prf_outputs_are_linkable() {
    use ark_crypto_primitives::crh::CRHScheme;
    use ark_ed_on_bls12_381::{EdwardsAffine, EdwardsConfig, Fq};
    use ark_ec::twisted_edwards::TECurveConfig;

    let mut rng = rand_chacha::ChaCha8Rng::from_seed([4u8; 32]);
    let prf_params = JZPRFParams::<H>::trusted_setup(&mut rng);
    let key = [7u8; 32];
    let (x1, x2) = ([1u8; 32], [2u8; 32]);
    let p1 = prf_output(&JZPRFInstance::<H>::new(&prf_params, &x1, &key));
    let p2 = prf_output(&JZPRFInstance::<H>::new(&prf_params, &x2, &key));

    // --- attacker: knows only prf_params (public), x1, x2, p1, p2 ---
    let hash = |input: &[u8], k: &[u8]| -> EdwardsAffine {
        let mut m = input.to_vec();
        m.extend_from_slice(k);
        <H as CRHScheme>::evaluate(&prf_params.crh_params, m).unwrap()
    };
    let delta = (hash(&x2, &[0u8; 32]).into_group() - hash(&x1, &[0u8; 32]).into_group()).into_affine();
    // the two points with x-coordinate p1 (Q1 and -Q1 + T): a x^2 + y^2 = 1 + d x^2 y^2
    let x = Fq::from_le_bytes_mod_order(&p1);
    let x2_ = x.square();
    let y2 = (Fq::ONE - EdwardsConfig::COEFF_A * x2_) / (Fq::ONE - EdwardsConfig::COEFF_D * x2_);
    let y = y2.sqrt().expect("p1 is the x-coordinate of a curve point");
    let linked = [y, -y].iter().any(|&y| {
        let q1 = EdwardsAffine::new_unchecked(x, y);
        let candidate = (q1.into_group() + delta.into_group()).into_affine();
        utils::serialize(&candidate.x) == p2
    });
    assert!(linked, "the two pseudonyms of the same key are linkable by anyone");
}
