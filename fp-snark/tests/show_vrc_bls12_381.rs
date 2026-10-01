//! End-to-end credential presentation ("ShowVRC"-style) proof over **BLS12-381**, using the
//! instantiation described in [CGLMPS26, §10]: Groth16 over BLS12-381, Schnorr signatures
//! over Jubjub, a Pedersen-hash Merkle tree over Jubjub for the attribute vector, and a PRF
//! whose outputs are field elements of the SNARK's scalar field.
//!
//! Compared with `first_person_test_app6.rs` (which is the same flow over BLS12-377) this test
//! also closes the *credential encoding* gap:
//!
//! * the attribute vector follows a [`CredentialSchema`] with a canonical byte encoding, and
//!   every opened leaf is parsed **inside the circuit** ([`parse_leaf`]) before the predicate
//!   is evaluated on the decoded, range-checked value;
//! * each opened leaf is pinned to its schema position ([`generate_constraints_at_position`]),
//!   and additionally carries its index, so the prover cannot open a different attribute;
//! * the issuer signs `schema.id || root`, so a credential cannot be presented under another
//!   schema.
//!
//! Negative tests check that each of these bindings is actually enforced, and one test
//! demonstrates the hole in the unpinned `app6`-style Merkle opening.

use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInt, BigInteger, Field, PrimeField};
use ark_groth16::{Groth16, ProvingKey, VerifyingKey};
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::*;
use ark_serialize::CanonicalSerialize;
use ark_snark::SNARK;
use rand_chacha::rand_core::SeedableRng;

use fp_snark::credential::constraints::{parse_leaf, AttributeVar};
use fp_snark::credential::{AttributeSpec, AttributeType, AttributeValue, CredentialSchema, Leaf};
use fp_snark::prf::{self, constraints::*, JZPRFInstance, JZPRFParams};
use fp_snark::random_oracle::{blake2s::RO, RandomOracle};
use fp_snark::signature::{schnorr, schnorr::constraints::*, SigVerifyGadget, SignatureScheme};
use fp_snark::utils;
use fp_snark::vector_commitment::bytes::pedersen::{
    self, constraints::*, JZVectorCommitmentOpeningProof, JZVectorCommitmentParams, JZVectorDB,
};

use ark_ed_on_bls12_381::constraints::{EdwardsVar as JubJubVar, FqVar};
use ark_ed_on_bls12_381::EdwardsProjective as JubJub;

// The constraint field is BLS12-381's scalar field, which is Jubjub's base field.
type ConstraintF = Fr;
type MT = pedersen::config::ed_on_bls12_381::MerkleTreeParams;
type MTVar = pedersen::config::ed_on_bls12_381::MerkleTreeParamsVar;
type H = prf::config::ed_on_bls12_381::Hash;
type HG = prf::config::ed_on_bls12_381::HashGadget;
type S = schnorr::Schnorr<JubJub>;
type SG = SchnorrSignatureVerifyGadget<JubJub, JubJubVar>;
type SVar = schnorr::constraints::PublicKeyVar<JubJub, JubJubVar>;
type Opening = JZVectorCommitmentOpeningProof<MT, Leaf>;
type OpeningVar = JZVectorCommitmentOpeningProofVar<ConstraintF, MT, MTVar>;

// ---------------------------------------------------------------------------------------------
// Credential schema (the attribute set of [CGLMPS26, §2] plus the key material of §2.3/§9.1)
// ---------------------------------------------------------------------------------------------

// Attribute positions; `name` and `phone` are certified but never opened by this show.
#[allow(dead_code)]
const PK_INDEX: usize = 0;
const PSEUDONYM_INDEX: usize = 1;
#[allow(dead_code)]
const NAME_INDEX: usize = 2;
const CITIZENSHIP_INDEX: usize = 3;
const DOB_INDEX: usize = 4;
const OCCUPATION_INDEX: usize = 5;
#[allow(dead_code)]
const PHONE_INDEX: usize = 6;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum Country {
    USA = 0,
    India = 1,
    UnitedKingdom = 2,
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum Occupation {
    Cryptographer = 0,
    Developer = 1,
    Professor = 2,
}

fn schema() -> CredentialSchema {
    CredentialSchema::new(
        *b"PHC/v1\0\0",
        vec![
            // x-coordinate of the holder's Jubjub public key
            AttributeSpec::new("pk", AttributeType::Bytes { len: 32 }),
            // issuer-specific pseudonym k_U = PRF_K(ipk)
            AttributeSpec::new("pseudonym", AttributeType::Bytes { len: 32 }),
            AttributeSpec::new("name", AttributeType::String { max_len: 20 }),
            AttributeSpec::new("citizenship", AttributeType::Enum { cardinality: 3 }),
            AttributeSpec::new("date_of_birth", AttributeType::Date),
            AttributeSpec::new("occupation", AttributeType::Enum { cardinality: 3 }),
            AttributeSpec::new("phone", AttributeType::UInt { bits: 36 }),
        ],
    )
    .unwrap()
}

/// The predicate `f` of the show: adult (born on or before `SHOW_DATE` minus 18 years),
/// citizen of one of `ALLOWED_COUNTRIES`, and a cryptographer.
const SHOW_DATE: (u16, u8, u8) = (2026, 9, 21);
const ALLOWED_COUNTRIES: [Country; 2] = [Country::USA, Country::UnitedKingdom];
const REQUIRED_OCCUPATION: Occupation = Occupation::Cryptographer;
const CONTEXT: &[u8] = b"example.org/forum";

// ---------------------------------------------------------------------------------------------
// Circuit
// ---------------------------------------------------------------------------------------------

struct ShowCircuit {
    schema: CredentialSchema,
    /// The credential's attribute tree (leaves + Merkle parameters).
    db: JZVectorDB<MT, Leaf>,
    /// Openings supplied by the prover for `OPENED_ATTRIBUTES`, in that order.
    openings: Vec<Opening>,
    prf_params: JZPRFParams<H>,
    schnorr_parameters: <S as SignatureScheme>::Parameters,
    issuer_public_key: <S as SignatureScheme>::PublicKey,
    /// Issuer's Schnorr signature on `schema.id || root`.
    certification: <S as SignatureScheme>::Signature,
    user_public_key: <S as SignatureScheme>::PublicKey,
    /// Holder's Schnorr signature on the statement digest.
    attestation: <S as SignatureScheme>::Signature,
    /// PRF_K(ipk): the pseudonym certified in the credential.
    pseudonym_prf: JZPRFInstance<H>,
    /// PRF_K(ctx): the pseudonym revealed for this show.
    context_prf: JZPRFInstance<H>,
    // public inputs
    statement_digest: ConstraintF,
    context_pseudonym: ConstraintF,
}

const OPENED_ATTRIBUTES: [usize; 5] = [PK_INDEX, PSEUDONYM_INDEX, CITIZENSHIP_INDEX, DOB_INDEX, OCCUPATION_INDEX];

fn generate_schnorr_verification_constraints<SG: SigVerifyGadget<S, ConstraintF>>(
    cs: ConstraintSystemRef<ConstraintF>,
    schnorr_parameters: &<S as SignatureScheme>::Parameters,
    signature: &<S as SignatureScheme>::Signature,
    public_key: &<S as SignatureScheme>::PublicKey,
    message: &[u8],
) -> Result<(SG::PublicKeyVar, Vec<UInt8<ConstraintF>>)> {
    let parameters_var = SG::ParametersVar::new_constant(cs.clone(), schnorr_parameters)?;
    let signature_var = SG::SignatureVar::new_witness(cs.clone(), || Ok(signature))?;
    let pk_var = SG::PublicKeyVar::new_witness(cs.clone(), || Ok(public_key))?;
    let msg_var = message
        .iter()
        .map(|b| UInt8::new_witness(cs.clone(), || Ok(b)))
        .collect::<Result<Vec<_>>>()?;
    SG::verify(&parameters_var, &pk_var, &msg_var, &signature_var)?.enforce_equal(&Boolean::TRUE)?;
    Ok((pk_var, msg_var))
}

fn enforce_bytes_eq(a: &[UInt8<ConstraintF>], b: &[UInt8<ConstraintF>]) -> Result<()> {
    assert_eq!(a.len(), b.len());
    for (x, y) in a.iter().zip(b) {
        x.enforce_equal(y)?;
    }
    Ok(())
}

impl ConstraintSynthesizer<ConstraintF> for ShowCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<ConstraintF>) -> Result<()> {
        // ---------------- Public inputs (allocation order = verifier's input order) ----------
        let issuer_pk_x_input = FqVar::new_input(ark_relations::ns!(cs, "issuer_public_key_x"), || Ok(self.issuer_public_key.x))?;
        let statement_digest_var = FqVar::new_input(ark_relations::ns!(cs, "statement_digest"), || Ok(self.statement_digest))?;
        let context_pseudonym_var = FqVar::new_input(ark_relations::ns!(cs, "context_pseudonym"), || Ok(self.context_pseudonym))?;

        // ---------------- Merkle openings, pinned to their schema position ----------------
        let params_var = JZVectorCommitmentParamsVar::<ConstraintF, MT, MTVar>::new_constant(cs.clone(), &self.db.vc_params)?;
        let mut root_var = None;
        let mut parsed: Vec<AttributeVar<ConstraintF>> = Vec::new();
        for (k, &index) in OPENED_ATTRIBUTES.iter().enumerate() {
            let mut opening_var = OpeningVar::new_witness(cs.clone(), || Ok(&self.openings[k]))?;
            generate_constraints_at_position(cs.clone(), &params_var, &mut opening_var, index);
            // all openings are against one root
            match &root_var {
                None => root_var = Some(opening_var.root_var.clone()),
                Some(root) => opening_var.root_var.enforce_equal(root)?,
            }
            // parse and range-check the leaf according to the schema
            parsed.push(parse_leaf(&self.schema, index, &opening_var.leaf_var)?);
        }
        let root_var = root_var.unwrap();

        // ---------------- Issuer signature on (schema id || root) ----------------
        let issuer_message = issuer_message(&self.schema, &self.db.commitment());
        let (issuer_pk_var, issuer_msg_var) = generate_schnorr_verification_constraints::<SG>(
            cs.clone(),
            &self.schnorr_parameters,
            &self.certification,
            &self.issuer_public_key,
            &issuer_message,
        )?;
        let issuer_pk_var: SVar = issuer_pk_var;
        issuer_pk_var.pub_key.x.enforce_equal(&issuer_pk_x_input)?;
        let schema_id_var: Vec<UInt8<ConstraintF>> = self.schema.id.iter().map(|b| UInt8::constant(*b)).collect();
        enforce_bytes_eq(&issuer_msg_var[..8], &schema_id_var)?;
        enforce_bytes_eq(&issuer_msg_var[8..], &root_var.to_bytes_le()?)?;

        // ---------------- Holder signature on the statement ----------------
        let (user_pk_var, user_msg_var) = generate_schnorr_verification_constraints::<SG>(
            cs.clone(),
            &self.schnorr_parameters,
            &self.attestation,
            &self.user_public_key,
            &encode_statement(&self.statement_digest),
        )?;
        let user_pk_var: SVar = user_pk_var;
        enforce_bytes_eq(&user_msg_var, &statement_digest_var.to_bytes_le()?)?;
        // the signing key is the one certified in the credential (leaf PK_INDEX)
        parsed[0].enforce_bytes_equal(&user_pk_var.pub_key.x.to_bytes_le()?)?;

        // ---------------- Pseudonyms: PRF_K(ipk) is certified, PRF_K(ctx) is revealed ------
        let prf_params_var = JZPRFParamsVar::<H, HG, ConstraintF>::new_constant(cs.clone(), &self.prf_params)?;
        let pseudonym_prf_var = JZPRFInstanceVar::<ConstraintF>::new_witness(cs.clone(), || Ok(&self.pseudonym_prf))?;
        prf::constraints::generate_constraints(cs.clone(), &prf_params_var, &pseudonym_prf_var);
        let context_prf_var = JZPRFInstanceVar::<ConstraintF>::new_witness(cs.clone(), || Ok(&self.context_prf))?;
        prf::constraints::generate_constraints(cs.clone(), &prf_params_var, &context_prf_var);
        // same key K in both evaluations
        enforce_bytes_eq(&pseudonym_prf_var.key_var, &context_prf_var.key_var)?;
        // PRF_K(ipk): input is the issuer key that verified the certification
        enforce_bytes_eq(&pseudonym_prf_var.input_var, &issuer_pk_var.pub_key.x.to_bytes_le()?)?;
        // ... and its output is the certified pseudonym (leaf PSEUDONYM_INDEX)
        parsed[1].enforce_bytes_equal(&pseudonym_prf_var.output_var[..32])?;
        // PRF_K(ctx): input is the (constant) context, output is the public pseudonym
        let context_var: Vec<UInt8<ConstraintF>> = CONTEXT.iter().map(|b| UInt8::constant(*b)).collect();
        enforce_bytes_eq(&context_prf_var.input_var, &context_var)?;
        enforce_bytes_eq(&context_prf_var.output_var[..32], &context_pseudonym_var.to_bytes_le()?)?;

        // ---------------- The predicate f, on the decoded attributes ----------------
        parsed[2].enforce_enum_in(&ALLOWED_COUNTRIES.map(|c| c as u8))?;
        let (y, m, d) = SHOW_DATE;
        parsed[3].enforce_date_at_most(y - 18, m, d)?;
        parsed[4].enforce_enum_in(&[REQUIRED_OCCUPATION as u8])?;

        Ok(())
    }
}

// ---------------------------------------------------------------------------------------------
// Native side: issuance and witness generation
// ---------------------------------------------------------------------------------------------

fn issuer_message(schema: &CredentialSchema, root: &<MT as fp_snark::merkle_tree::Config>::InnerDigest) -> Vec<u8> {
    let mut msg = schema.id.to_vec();
    msg.extend(utils::serialize(root));
    msg
}

fn encode_public_key(pk: &<S as SignatureScheme>::PublicKey) -> Vec<u8> {
    utils::serialize(pk).iter().take(32).cloned().collect()
}

fn encode_statement(statement: &ConstraintF) -> Vec<u8> {
    statement.into_bigint().to_bytes_le().iter().take(32).cloned().collect()
}

fn hash_statement(statement: &str) -> [u8; 32] {
    let mut h = RO::evaluate(&(), statement.as_bytes()).unwrap();
    h[31] = 0u8; // fit in the 255-bit scalar field
    h
}

fn field_from_bytes(bytes: &[u8]) -> ConstraintF {
    ConstraintF::from(BigInt::<4>::from_bits_le(utils::bytes_to_bits(bytes).as_slice()))
}

/// First 32 bytes of the PRF output: the x-coordinate of the Pedersen-hash point.
fn prf_output(prf: &JZPRFInstance<H>) -> Vec<u8> {
    prf.evaluate().iter().take(32).cloned().collect()
}

#[derive(Clone)]
struct Scenario {
    citizenship: Country,
    date_of_birth: (u16, u8, u8),
    occupation: Occupation,
    /// Replace the opening supplied for `CITIZENSHIP_INDEX` by the opening of this leaf.
    citizenship_opening_from: Option<usize>,
    /// Flip the citizenship byte in the opened leaf without re-issuing (root no longer matches).
    tamper_citizenship_leaf: bool,
    /// Use a different PRF key for the context pseudonym than for the certified one.
    wrong_context_key: bool,
}

impl Scenario {
    fn honest() -> Self {
        Scenario {
            citizenship: Country::USA,
            date_of_birth: (1991, 3, 14),
            occupation: Occupation::Cryptographer,
            citizenship_opening_from: None,
            tamper_citizenship_leaf: false,
            wrong_context_key: false,
        }
    }
}

fn setup_witness(scenario: &Scenario) -> ShowCircuit {
    let seed = [0u8; 32];
    let mut rng = rand_chacha::ChaCha8Rng::from_seed(seed);
    let schema = schema();

    // public parameters
    let prf_params = JZPRFParams::<H>::trusted_setup(&mut rng);
    let vc_params = JZVectorCommitmentParams::<MT>::trusted_setup(&mut rng);
    let schnorr_parameters = S::setup(&mut rng).unwrap();

    // keys
    let (issuer_public_key, issuer_secret_key) = S::keygen(&schnorr_parameters, &mut rng).unwrap();
    let (user_public_key, user_secret_key) = S::keygen(&schnorr_parameters, &mut rng).unwrap();
    let prf_key = [42u8; 32];

    // issuer-specific pseudonym k_U = PRF_K(ipk), an attribute of the credential (§9.1)
    let pseudonym_prf = JZPRFInstance::new(&prf_params, &encode_public_key(&issuer_public_key), &prf_key);

    // the attribute vector, canonically encoded into self-describing leaves
    let (y, m, d) = scenario.date_of_birth;
    let values = vec![
        AttributeValue::Bytes(encode_public_key(&user_public_key)),
        AttributeValue::Bytes(prf_output(&pseudonym_prf)),
        AttributeValue::String("Alice".into()),
        AttributeValue::Enum(scenario.citizenship as u8),
        AttributeValue::Date { year: y, month: m, day: d },
        AttributeValue::Enum(scenario.occupation as u8),
        AttributeValue::UInt(5553141),
    ];
    let leaves = CredentialSchema::pad_leaves_to_pow2(schema.encode_leaves(&values).unwrap());
    let db = JZVectorDB::<MT, Leaf>::new(vc_params, &leaves);
    let root = db.commitment();

    // IssuePHC: the issuer signs (schema id || root)
    let certification = S::sign(&schnorr_parameters, &issuer_secret_key, &issuer_message(&schema, &root), &mut rng).unwrap();
    assert!(S::verify(&schnorr_parameters, &issuer_public_key, &issuer_message(&schema, &root), &certification).unwrap());

    // the holder signs the statement
    let statement_digest_encoding = hash_statement("Bob is a cryptographer");
    let statement_digest = field_from_bytes(&statement_digest_encoding);
    let attestation = S::sign(&schnorr_parameters, &user_secret_key, &statement_digest_encoding, &mut rng).unwrap();

    // context pseudonym
    let context_key = if scenario.wrong_context_key { [43u8; 32] } else { prf_key };
    let context_prf = JZPRFInstance::new(&prf_params, CONTEXT, &context_key);
    let context_pseudonym = field_from_bytes(&prf_output(&context_prf));

    // openings
    let opening = |index: usize| Opening { root: db.commitment(), record: db.get_record(index).clone(), path: db.proof(index) };
    let mut openings: Vec<Opening> = OPENED_ATTRIBUTES.iter().map(|&i| opening(i)).collect();
    if let Some(from) = scenario.citizenship_opening_from {
        openings[2] = opening(from);
    }
    if scenario.tamper_citizenship_leaf {
        openings[2].record.0[1] = Country::USA as u8;
    }

    ShowCircuit {
        schema,
        db,
        openings,
        prf_params,
        schnorr_parameters,
        issuer_public_key,
        certification,
        user_public_key,
        attestation,
        pseudonym_prf,
        context_prf,
        statement_digest,
        context_pseudonym,
    }
}

fn is_satisfied(scenario: &Scenario) -> bool {
    let cs = ConstraintSystem::<ConstraintF>::new_ref();
    setup_witness(scenario).generate_constraints(cs.clone()).unwrap();
    cs.is_satisfied().unwrap()
}

fn circuit_setup() -> (ProvingKey<Bls12_381>, VerifyingKey<Bls12_381>) {
    let mut rng = rand_chacha::ChaCha8Rng::from_seed([1u8; 32]);
    let circuit = setup_witness(&Scenario::honest());
    Groth16::<Bls12_381>::circuit_specific_setup(circuit, &mut rng).unwrap()
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
    let public_input = [circuit.issuer_public_key.x, circuit.statement_digest, circuit.context_pseudonym];

    let now = std::time::Instant::now();
    let proof = Groth16::<Bls12_381>::prove(&pk, circuit, &mut rng).unwrap();
    println!("Prover time: {:.2?}", now.elapsed());

    let now = std::time::Instant::now();
    assert!(Groth16::<Bls12_381>::verify(&vk, &public_input, &proof).unwrap());
    println!("Verifier time: {:.2?}", now.elapsed());

    // a wrong public input (e.g. another context pseudonym) must not verify
    let mut wrong_input = public_input;
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

/// Known issue (not fixed here): the `prf` module instantiates the PRF as a Pedersen CRH of
/// `input || key`. A Pedersen hash is *linear* in its input bits, so
/// `P(x || k) - P(x || 0) = P(0 || k)` is independent of `x`. Given two pseudonyms
/// `p_1 = x(P(x_1 || k))`, `p_2 = x(P(x_2 || k))` for public inputs `x_1, x_2` (e.g. two
/// issuer identities or contexts), anyone can compute `Δ = P(x_2 || 0) - P(x_1 || 0)`, recover
/// `±Q_1` from `p_1`, and test whether `x(±Q_1 + Δ) = p_2`. This links pseudonyms across
/// contexts, contrary to the unlinkability goal of [CGLMPS26, §2.3]. The paper's own
/// instantiation (§9.1) uses the DDH-based PRF `H(x)^k`; a Poseidon-based PRF would also do.
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
    // recover ±Q1 from the x-coordinate p1: a x^2 + y^2 = 1 + d x^2 y^2
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
