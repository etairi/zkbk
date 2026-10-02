//! End-to-end credential presentation ("ShowVRC"-style) proof over **BLS12-381**, using the
//! instantiation described in [CGLMPS26, §10]: Groth16 over BLS12-381, Schnorr signatures
//! over Jubjub and a Pedersen-hash Merkle tree over Jubjub for the attribute vector. The
//! pseudonyms use the DDH PRF `x([K]·H(x))` over Jubjub (`fp_snark::prf::ddh`), the
//! curve-native form of the `H(x)^sk` suggested in [CGLMPS26, §9.1], instead of the
//! Pedersen-CRH PRF of `fp_snark::prf`, which is linear and therefore not a PRF (see
//! `known_issue_pedersen_crh_prf_outputs_are_linkable`).
//!
//! Compared with `first_person_test_app6.rs` (which is the same flow over BLS12-377) this circuit
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
//! Shared by `tests/show_vrc_bls12_381.rs` and `benches/show_vrc.rs`.

#![allow(dead_code)]

use ark_bls12_381::{Bls12_381, Fr};
use ark_ff::{BigInt, BigInteger, PrimeField};
use ark_groth16::{Groth16, ProvingKey, VerifyingKey};
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::*;
use ark_snark::SNARK;
use rand_chacha::rand_core::SeedableRng;

use fp_snark::credential::constraints::{parse_leaf, AttributeVar};
use fp_snark::credential::{AttributeSpec, AttributeType, AttributeValue, CredentialSchema, Leaf};
use fp_snark::prf::ddh::{self, constraints::KeyVar};
use fp_snark::random_oracle::{blake2s::RO, RandomOracle};
use fp_snark::signature::{schnorr, schnorr::constraints::*, SigVerifyGadget, SignatureScheme};
use fp_snark::utils;
use fp_snark::vector_commitment::bytes::pedersen::{
    self, constraints::*, JZVectorCommitmentOpeningProof, JZVectorCommitmentParams, JZVectorDB,
};

use ark_ed_on_bls12_381::constraints::{EdwardsVar as JubJubVar, FqVar};
use ark_ed_on_bls12_381::{EdwardsAffine, EdwardsConfig, EdwardsProjective as JubJub, Fr as JubjubScalar};

// The constraint field is BLS12-381's scalar field, which is Jubjub's base field.
pub type ConstraintF = Fr;
pub type MT = pedersen::config::ed_on_bls12_381::MerkleTreeParams;
pub type MTVar = pedersen::config::ed_on_bls12_381::MerkleTreeParamsVar;
pub type S = schnorr::Schnorr<JubJub>;
pub type SG = SchnorrSignatureVerifyGadget<JubJub, JubJubVar>;
pub type SVar = schnorr::constraints::PublicKeyVar<JubJub, JubJubVar>;
pub type Opening = JZVectorCommitmentOpeningProof<MT, Leaf>;
pub type OpeningVar = JZVectorCommitmentOpeningProofVar<ConstraintF, MT, MTVar>;

// ---------------------------------------------------------------------------------------------
// Credential schema (the attribute set of [CGLMPS26, §2] plus the key material of §2.3/§9.1)
// ---------------------------------------------------------------------------------------------

// Attribute positions; `name` and `phone` are certified but never opened by this show.
pub const PK_INDEX: usize = 0;
pub const PSEUDONYM_INDEX: usize = 1;
pub const NAME_INDEX: usize = 2;
pub const CITIZENSHIP_INDEX: usize = 3;
pub const DOB_INDEX: usize = 4;
pub const OCCUPATION_INDEX: usize = 5;
pub const PHONE_INDEX: usize = 6;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Country {
    USA = 0,
    India = 1,
    UnitedKingdom = 2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Occupation {
    Cryptographer = 0,
    Developer = 1,
    Professor = 2,
}

pub fn schema() -> CredentialSchema {
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
pub const SHOW_DATE: (u16, u8, u8) = (2026, 9, 21);
pub const ALLOWED_COUNTRIES: [Country; 2] = [Country::USA, Country::UnitedKingdom];
pub const REQUIRED_OCCUPATION: Occupation = Occupation::Cryptographer;
pub const CONTEXT: &[u8] = b"example.org/forum";

// ---------------------------------------------------------------------------------------------
// Circuit
// ---------------------------------------------------------------------------------------------

pub struct ShowCircuit {
    pub schema: CredentialSchema,
    /// The credential's attribute tree (leaves + Merkle parameters).
    pub db: JZVectorDB<MT, Leaf>,
    /// Openings supplied by the prover for `OPENED_ATTRIBUTES`, in that order.
    pub openings: Vec<Opening>,
    pub schnorr_parameters: <S as SignatureScheme>::Parameters,
    pub issuer_public_key: <S as SignatureScheme>::PublicKey,
    /// Issuer's Schnorr signature on `schema.id || root`.
    pub certification: <S as SignatureScheme>::Signature,
    pub user_public_key: <S as SignatureScheme>::PublicKey,
    /// Holder's Schnorr signature on the statement digest.
    pub attestation: <S as SignatureScheme>::Signature,
    /// The holder's PRF key K.
    pub prf_key: JubjubScalar,
    // public inputs
    pub statement_digest: ConstraintF,
    /// PRF_K(ctx): the pseudonym revealed for this show.
    pub context_pseudonym: ConstraintF,
    /// H(ipk), computed by the verifier from the issuer key it passes as `issuer_public_key.x`.
    pub issuer_prf_base: EdwardsAffine,
}

pub const OPENED_ATTRIBUTES: [usize; 5] = [PK_INDEX, PSEUDONYM_INDEX, CITIZENSHIP_INDEX, DOB_INDEX, OCCUPATION_INDEX];

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
        // H(ipk) for the certified pseudonym PRF_K(ipk); allocated as x, then y
        let issuer_prf_base_var = JubJubVar::new_input(ark_relations::ns!(cs, "issuer_prf_base"), || Ok(self.issuer_prf_base))?;

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
        // DDH PRF over Jubjub, PRF(K, x) = x([K]·H(x)), with one key K for both evaluations.
        let key_var = KeyVar::<JubjubScalar, ConstraintF>::new_witness(ark_relations::ns!(cs, "prf_key"), || Ok(self.prf_key))?;
        // PRF_K(ipk): the verifier derives the public input H(ipk) from the same issuer key it
        // passes as `issuer_public_key_x`; the output is the certified pseudonym (leaf
        // PSEUDONYM_INDEX)
        let pseudonym_var = ddh::constraints::evaluate_input_base(&key_var, &issuer_prf_base_var)?;
        parsed[1].enforce_bytes_equal(&pseudonym_var.to_bytes_le()?)?;
        // PRF_K(ctx): the context is a circuit constant, so H(ctx) is a fixed base; the output
        // is the public pseudonym
        let context_base = ddh::hash_to_curve::<EdwardsConfig>(CONTEXT);
        ddh::constraints::evaluate_constant_base(&key_var, &context_base)?.enforce_equal(&context_pseudonym_var)?;

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

pub fn issuer_message(schema: &CredentialSchema, root: &<MT as fp_snark::merkle_tree::Config>::InnerDigest) -> Vec<u8> {
    let mut msg = schema.id.to_vec();
    msg.extend(utils::serialize(root));
    msg
}

pub fn encode_public_key(pk: &<S as SignatureScheme>::PublicKey) -> Vec<u8> {
    utils::serialize(pk).iter().take(32).cloned().collect()
}

pub fn encode_statement(statement: &ConstraintF) -> Vec<u8> {
    statement.into_bigint().to_bytes_le().iter().take(32).cloned().collect()
}

pub fn hash_statement(statement: &str) -> [u8; 32] {
    let mut h = RO::evaluate(&(), statement.as_bytes()).unwrap();
    h[31] = 0u8; // fit in the 255-bit scalar field
    h
}

pub fn field_from_bytes(bytes: &[u8]) -> ConstraintF {
    ConstraintF::from(BigInt::<4>::from_bits_le(utils::bytes_to_bits(bytes).as_slice()))
}

#[derive(Clone)]
pub struct Scenario {
    pub citizenship: Country,
    pub date_of_birth: (u16, u8, u8),
    pub occupation: Occupation,
    /// Replace the opening supplied for `CITIZENSHIP_INDEX` by the opening of this leaf.
    pub citizenship_opening_from: Option<usize>,
    /// Flip the citizenship byte in the opened leaf without re-issuing (root no longer matches).
    pub tamper_citizenship_leaf: bool,
    /// Use a different PRF key for the context pseudonym than for the certified one.
    pub wrong_context_key: bool,
}

impl Scenario {
    pub fn honest() -> Self {
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

/// The attribute vector of the credential, in schema order.
pub fn attribute_values(
    user_public_key: &<S as SignatureScheme>::PublicKey,
    pseudonym: &ConstraintF,
    scenario: &Scenario,
) -> Vec<AttributeValue> {
    let (y, m, d) = scenario.date_of_birth;
    vec![
        AttributeValue::Bytes(encode_public_key(user_public_key)),
        AttributeValue::Bytes(pseudonym.into_bigint().to_bytes_le()),
        AttributeValue::String("Alice".into()),
        AttributeValue::Enum(scenario.citizenship as u8),
        AttributeValue::Date { year: y, month: m, day: d },
        AttributeValue::Enum(scenario.occupation as u8),
        AttributeValue::UInt(5553141),
    ]
}

pub fn setup_witness(scenario: &Scenario) -> ShowCircuit {
    let seed = [0u8; 32];
    let mut rng = rand_chacha::ChaCha8Rng::from_seed(seed);
    let schema = schema();

    // public parameters
    let vc_params = JZVectorCommitmentParams::<MT>::trusted_setup(&mut rng);
    let schnorr_parameters = S::setup(&mut rng).unwrap();

    // keys
    let (issuer_public_key, issuer_secret_key) = S::keygen(&schnorr_parameters, &mut rng).unwrap();
    let (user_public_key, user_secret_key) = S::keygen(&schnorr_parameters, &mut rng).unwrap();
    let prf_key = JubjubScalar::from_le_bytes_mod_order(&[42u8; 32]);

    // issuer-specific pseudonym k_U = PRF_K(ipk), an attribute of the credential (§9.1)
    let issuer_prf_base = ddh::hash_to_curve::<EdwardsConfig>(&encode_public_key(&issuer_public_key));
    let pseudonym = ddh::evaluate_with_base(&prf_key, &issuer_prf_base);

    // the attribute vector, canonically encoded into self-describing leaves
    let values = attribute_values(&user_public_key, &pseudonym, scenario);
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
    let context_key = if scenario.wrong_context_key { JubjubScalar::from_le_bytes_mod_order(&[43u8; 32]) } else { prf_key };
    let context_pseudonym = ddh::evaluate::<EdwardsConfig>(&context_key, CONTEXT);

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
        schnorr_parameters,
        issuer_public_key,
        certification,
        user_public_key,
        attestation,
        prf_key,
        statement_digest,
        context_pseudonym,
        issuer_prf_base,
    }
}

/// The verifier's public inputs, in allocation order. The verifier computes `H(ipk)` itself from
/// the issuer key.
pub fn public_inputs(circuit: &ShowCircuit) -> Vec<ConstraintF> {
    let issuer_prf_base = ddh::hash_to_curve::<EdwardsConfig>(&encode_public_key(&circuit.issuer_public_key));
    vec![
        circuit.issuer_public_key.x,
        circuit.statement_digest,
        circuit.context_pseudonym,
        issuer_prf_base.x,
        issuer_prf_base.y,
    ]
}

pub fn is_satisfied(scenario: &Scenario) -> bool {
    let cs = ConstraintSystem::<ConstraintF>::new_ref();
    setup_witness(scenario).generate_constraints(cs.clone()).unwrap();
    cs.is_satisfied().unwrap()
}

pub fn circuit_setup() -> (ProvingKey<Bls12_381>, VerifyingKey<Bls12_381>) {
    let mut rng = rand_chacha::ChaCha8Rng::from_seed([1u8; 32]);
    let circuit = setup_witness(&Scenario::honest());
    Groth16::<Bls12_381>::circuit_specific_setup(circuit, &mut rng).unwrap()
}
