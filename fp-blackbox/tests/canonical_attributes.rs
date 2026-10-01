//! The attribute vector of the black-box vouchable credential [CGLMPS26, §8] is a vector of
//! scalar-field elements: the credential signs a KZG commitment to the polynomial whose roots
//! are the attributes, and a vouch reveals a subset of them. Nothing in that construction says
//! what a revealed scalar *means*. This test derives the scalars from typed attribute values
//! with the canonical, index-separated encoding of `fp_snark::credential`, runs issuance,
//! vouching and verification on them, and checks that the verifier can decode every revealed
//! scalar back to `(attribute index, typed value)`.
//!
//! Two properties of the encoding matter here:
//! * it is injective, so a revealed scalar corresponds to exactly one attribute value;
//! * the attribute index is part of the encoding, so equal labels in different slots (e.g.
//!   `citizenship = 0` and `occupation = 0`) are different roots. With the root-based
//!   polynomial `∏ (X − att_i)` used by `fp_blackbox::vouch`, attributes carry no position of
//!   their own, so without the index prefix a vouch for "occupation = 0" would verify as a vouch
//!   for "citizenship = 0".

use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_std::test_rng;

use fp_blackbox::gro15::{flipped, standard};
use fp_blackbox::vouch::{credential::Credential, params::PublicParams};
use fp_snark::credential::{AttributeSpec, AttributeType, AttributeValue, CredentialSchema};

type Fr = <Bls12_381 as Pairing>::ScalarField;

const NAME: usize = 0;
const CITIZENSHIP: usize = 1;
const DATE_OF_BIRTH: usize = 2;
const OCCUPATION: usize = 3;

fn schema() -> CredentialSchema {
    CredentialSchema::new(
        *b"PHC/bb1\0",
        vec![
            AttributeSpec::new("name", AttributeType::String { max_len: 20 }),
            AttributeSpec::new("citizenship", AttributeType::Enum { cardinality: 3 }),
            AttributeSpec::new("date_of_birth", AttributeType::Date),
            AttributeSpec::new("occupation", AttributeType::Enum { cardinality: 3 }),
        ],
    )
    .unwrap()
}

#[test]
fn issue_vouch_verify_with_canonically_encoded_attributes() {
    let rng = &mut test_rng();
    let schema = schema();
    let values = vec![
        AttributeValue::String("Alice".into()),
        AttributeValue::Enum(0),
        AttributeValue::Date { year: 1991, month: 3, day: 14 },
        AttributeValue::Enum(0),
    ];
    let attributes: Vec<Fr> = (0..values.len())
        .map(|i| schema.attribute_to_field(i, &values[i]).unwrap())
        .collect();
    // equal labels in different slots are different roots
    assert_ne!(attributes[CITIZENSHIP], attributes[OCCUPATION]);
    for i in 0..attributes.len() {
        for j in 0..i {
            assert_ne!(attributes[i], attributes[j]);
        }
    }

    // Setup, issuer and user keys (as in `fp_blackbox::vouch::tests`)
    let pp = PublicParams::<Bls12_381>::new(10, rng);
    let (issuer_pk, issuer_sk) = standard::SecretKey::new(&pp.gro15_params, rng);
    let (user_vk, user_sk) = flipped::SecretKey::new(&pp.flipped_params, rng);
    let user_proof = user_sk.prove_knowledge(&pp.flipped_params, rng);

    // IssuePHC on the encoded attribute vector
    let mut cred = Credential::issue(&pp, &issuer_sk, &user_vk, &user_proof, &attributes, rng).expect("issuance");
    cred.v_u_sk = Some(user_sk);

    // Vouch revealing citizenship and date of birth
    let idx = vec![CITIZENSHIP, DATE_OF_BIRTH];
    let statement = Fr::from(12345u64);
    let vouch = cred.vouch(&pp, &attributes, &idx, &statement, rng);
    assert!(vouch.verify(&pp, &issuer_pk, &statement));

    // The verifier decodes the revealed scalars: which attribute, and what value.
    assert_eq!(vouch.revealed_indices, idx);
    for (k, fe) in vouch.revealed_values.iter().enumerate() {
        let (index, value) = schema.decode_field_element(*fe).expect("revealed scalar is a canonical attribute");
        assert_eq!(index, idx[k]);
        assert_eq!(value, values[index]);
        assert!(schema.verify_field_element(index, &value, *fe).unwrap());
    }
    let (_, dob) = schema.decode_field_element(vouch.revealed_values[1]).unwrap();
    assert_eq!(dob, AttributeValue::Date { year: 1991, month: 3, day: 14 });

    // A scalar that is not a canonical attribute encoding is recognised as such.
    assert!(schema.decode_field_element(Fr::from(7u64)).is_err()); // index 7 does not exist
    assert!(schema.decode_field_element(Fr::from(1u64 + (5u64 << 8))).is_err()); // citizenship label 5 >= 3
    assert_eq!(schema.decode_field_element(Fr::from(NAME as u64)).unwrap(), (NAME, AttributeValue::String(String::new())));
}
