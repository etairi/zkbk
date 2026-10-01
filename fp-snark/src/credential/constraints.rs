// SPDX-License-Identifier: Apache-2.0

//! R1CS parsing of canonically encoded attributes.
//!
//! [`parse_leaf`] takes the bytes of a Merkle leaf `[index] || encode(value)` as gadget
//! variables and enforces exactly the checks of [`CredentialSchema::decode_value`]: the index
//! byte, the length, and per type
//!
//! * `Enum`: label `< cardinality`;
//! * `UInt`: the bits above the declared width are zero;
//! * `Date`: the packed integer is `y * 10000 + m * 100 + d` with `1 <= y <= 9999`,
//!   `1 <= m <= 12`, `1 <= d <= 31` (which makes `(y, m, d)` uniquely determined);
//! * `String`: the length byte is `<= max_len` and every byte after the `len`-th is zero;
//! * `Bytes`: nothing beyond the length.
//!
//! The result is an [`AttributeVar`], a typed value on which predicates are evaluated with
//! the `enforce_*` helpers. Because the same byte variables are hashed into the Merkle root
//! that the issuer signed, a satisfied predicate is a statement about the value the issuer
//! certified, not about bytes chosen by the prover.
//!
//! [`value_to_field_element`] and [`parse_field_element`] are the in-circuit counterparts of
//! [`CredentialSchema::attribute_to_field`], for circuits whose witness is the field-element
//! form of an attribute (the commit-and-prove link to the KZG commitment of the black-box
//! construction).

use core::cmp::Ordering;

use ark_ff::PrimeField;
use ark_r1cs_std::{
    boolean::Boolean,
    cmp::CmpGadget,
    convert::ToBitsGadget,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    prelude::AllocVar,
    uint8::UInt8,
    R1CSVar,
};
use ark_relations::r1cs::SynthesisError;

use crate::random_oracle::blake2s::constraints::{ParametersVar as B2SParamsVar, ROGadget};
use crate::random_oracle::RandomOracleGadget;

use super::{AttributeType, CredentialSchema, HASHED_FE_BYTES, MAX_PACKED_LEN};

/// A parsed date: `packed = year * 10000 + month * 100 + day`, all components range-checked.
#[derive(Clone, Debug)]
pub struct DateVar<F: PrimeField> {
    pub packed: FpVar<F>,
    pub year: FpVar<F>,
    pub month: FpVar<F>,
    pub day: FpVar<F>,
}

/// A parsed, well-formed attribute value.
#[derive(Clone, Debug)]
pub enum AttributeVar<F: PrimeField> {
    Enum(UInt8<F>),
    /// The integer as a field element; guaranteed `< 2^bits`.
    UInt(FpVar<F>),
    Date(DateVar<F>),
    /// `len` is guaranteed `<= max_len` and `bytes[len..]` are guaranteed zero.
    String { len: UInt8<F>, bytes: Vec<UInt8<F>> },
    Bytes(Vec<UInt8<F>>),
}

fn fp_const<F: PrimeField>(v: u64) -> FpVar<F> {
    FpVar::constant(F::from(v))
}

fn u64_of<F: PrimeField>(f: F) -> u64 {
    f.into_bigint().as_ref()[0]
}

/// Parses the leaf `[index] || value_bytes` of attribute `index`, enforcing the index byte and
/// the well-formedness of the value.
///
/// Panics if `leaf.len()` differs from the schema's leaf length: the shape of the leaf is fixed
/// by the schema at circuit-construction time, so a mismatch is a programming error, not a
/// prover choice.
pub fn parse_leaf<F: PrimeField>(
    schema: &CredentialSchema,
    index: usize,
    leaf: &[UInt8<F>],
) -> Result<AttributeVar<F>, SynthesisError> {
    let expected = schema.leaf_len(index).expect("attribute index out of range");
    assert_eq!(leaf.len(), expected, "leaf of attribute {} must have {} bytes, got {}", index, expected, leaf.len());
    leaf[0].enforce_equal(&UInt8::constant(index as u8))?;
    let ty = schema.attribute_type(index).expect("attribute index out of range");
    parse_value(&ty, &leaf[1..])
}

/// Parses canonical value bytes of type `ty` (no index byte), enforcing well-formedness.
///
/// Panics if `bytes.len() != ty.value_len()` (see [`parse_leaf`]).
pub fn parse_value<F: PrimeField>(ty: &AttributeType, bytes: &[UInt8<F>]) -> Result<AttributeVar<F>, SynthesisError> {
    assert_eq!(bytes.len(), ty.value_len(), "value of type {:?} must have {} bytes, got {}", ty, ty.value_len(), bytes.len());
    match *ty {
        AttributeType::Enum { cardinality } => {
            if cardinality <= 255 {
                bytes[0].is_lt(&UInt8::constant(cardinality as u8))?.enforce_equal(&Boolean::TRUE)?;
            }
            Ok(AttributeVar::Enum(bytes[0].clone()))
        }
        AttributeType::UInt { bits } => {
            let bits = bits as usize;
            let all_bits = bytes.to_bits_le()?;
            for high_bit in &all_bits[bits..] {
                high_bit.enforce_equal(&Boolean::FALSE)?;
            }
            Ok(AttributeVar::UInt(Boolean::le_bits_to_fp(&all_bits[..bits])?))
        }
        AttributeType::Date => {
            let packed = Boolean::le_bits_to_fp(&bytes.to_bits_le()?)?;
            let cs = bytes.cs();
            let packed_value = packed.value().map(u64_of);
            let year = FpVar::new_witness(cs.clone(), || packed_value.clone().map(|p| F::from(p / 10_000)))?;
            let month = FpVar::new_witness(cs.clone(), || packed_value.clone().map(|p| F::from((p / 100) % 100)))?;
            let day = FpVar::new_witness(cs, || packed_value.clone().map(|p| F::from(p % 100)))?;
            // Range checks. First bound each component by a small power of two (this is what
            // makes the `_unchecked` comparisons below sound: they require both operands to be
            // <= (p-1)/2), then enforce the exact ranges against constants.
            let _ = year.to_bits_le_with_top_bits_zero(14)?;
            let _ = month.to_bits_le_with_top_bits_zero(4)?;
            let _ = day.to_bits_le_with_top_bits_zero(5)?;
            year.enforce_cmp_unchecked(&fp_const(1), Ordering::Greater, true)?;
            year.enforce_cmp_unchecked(&fp_const(9999), Ordering::Less, true)?;
            month.enforce_cmp_unchecked(&fp_const(1), Ordering::Greater, true)?;
            month.enforce_cmp_unchecked(&fp_const(12), Ordering::Less, true)?;
            day.enforce_cmp_unchecked(&fp_const(1), Ordering::Greater, true)?;
            day.enforce_cmp_unchecked(&fp_const(31), Ordering::Less, true)?;
            // With the ranges above, (year, month, day) -> packed is injective, so this
            // equation determines the components.
            let recomposed = &year * F::from(10_000u64) + &month * F::from(100u64) + &day;
            packed.enforce_equal(&recomposed)?;
            Ok(AttributeVar::Date(DateVar { packed, year, month, day }))
        }
        AttributeType::String { max_len } => {
            let len = bytes[0].clone();
            len.is_le(&UInt8::constant(max_len))?.enforce_equal(&Boolean::TRUE)?;
            let zero = UInt8::constant(0u8);
            for (j, byte) in bytes[1..].iter().enumerate() {
                let unused = len.is_le(&UInt8::constant(j as u8))?; // j >= len
                byte.conditional_enforce_equal(&zero, &unused)?;
            }
            Ok(AttributeVar::String { len, bytes: bytes[1..].to_vec() })
        }
        AttributeType::Bytes { .. } => Ok(AttributeVar::Bytes(bytes.to_vec())),
    }
}

impl<F: PrimeField> AttributeVar<F> {
    /// Enforces that an enum label is one of `allowed`.
    pub fn enforce_enum_in(&self, allowed: &[u8]) -> Result<(), SynthesisError> {
        match self {
            AttributeVar::Enum(label) => {
                let hits = allowed
                    .iter()
                    .map(|&a| label.is_eq(&UInt8::constant(a)))
                    .collect::<Result<Vec<_>, _>>()?;
                Boolean::kary_or(&hits)?.enforce_equal(&Boolean::TRUE)
            }
            _ => panic!("enforce_enum_in on a non-enum attribute"),
        }
    }

    // The comparisons below use the `_unchecked` variants of `enforce_cmp`, which are sound
    // only if both operands are <= (p-1)/2. This holds by construction: a parsed `UInt` is
    // < 2^64 and a parsed date is < 2^32 (both enforced by `parse_value`), and the constants
    // are u64s.

    /// Enforces `min <= value <= max` for an unsigned integer attribute.
    pub fn enforce_uint_in_range(&self, min: u64, max: u64) -> Result<(), SynthesisError> {
        match self {
            AttributeVar::UInt(v) => {
                v.enforce_cmp_unchecked(&fp_const(min), Ordering::Greater, true)?;
                v.enforce_cmp_unchecked(&fp_const(max), Ordering::Less, true)
            }
            _ => panic!("enforce_uint_in_range on a non-uint attribute"),
        }
    }

    /// Enforces `date <= (year, month, day)` (e.g. "born on or before" for an age check).
    pub fn enforce_date_at_most(&self, year: u16, month: u8, day: u8) -> Result<(), SynthesisError> {
        match self {
            AttributeVar::Date(d) => d.packed.enforce_cmp_unchecked(
                &fp_const(super::AttributeValue::packed_date(year, month, day) as u64),
                Ordering::Less,
                true,
            ),
            _ => panic!("enforce_date_at_most on a non-date attribute"),
        }
    }

    /// Enforces `date >= (year, month, day)`.
    pub fn enforce_date_at_least(&self, year: u16, month: u8, day: u8) -> Result<(), SynthesisError> {
        match self {
            AttributeVar::Date(d) => d.packed.enforce_cmp_unchecked(
                &fp_const(super::AttributeValue::packed_date(year, month, day) as u64),
                Ordering::Greater,
                true,
            ),
            _ => panic!("enforce_date_at_least on a non-date attribute"),
        }
    }

    /// Enforces that a string attribute equals `expected` (byte-wise, including the length).
    pub fn enforce_string_equals(&self, expected: &str) -> Result<(), SynthesisError> {
        match self {
            AttributeVar::String { len, bytes } => {
                let e = expected.as_bytes();
                assert!(e.len() <= bytes.len(), "expected string longer than max_len");
                len.enforce_equal(&UInt8::constant(e.len() as u8))?;
                for (j, byte) in bytes.iter().enumerate() {
                    let expected_byte = if j < e.len() { e[j] } else { 0 };
                    byte.enforce_equal(&UInt8::constant(expected_byte))?;
                }
                Ok(())
            }
            _ => panic!("enforce_string_equals on a non-string attribute"),
        }
    }

    /// Enforces that a byte-string attribute equals `expected`.
    pub fn enforce_bytes_equal(&self, expected: &[UInt8<F>]) -> Result<(), SynthesisError> {
        match self {
            AttributeVar::Bytes(bytes) => {
                assert_eq!(bytes.len(), expected.len(), "byte length mismatch");
                for (a, b) in bytes.iter().zip(expected) {
                    a.enforce_equal(b)?;
                }
                Ok(())
            }
            _ => panic!("enforce_bytes_equal on a non-bytes attribute"),
        }
    }
}

/// In-circuit [`CredentialSchema::attribute_to_field`]: maps the canonical value bytes of
/// attribute `index` to the field element used in the polynomial commitment.
pub fn value_to_field_element<F: PrimeField>(
    schema: &CredentialSchema,
    index: usize,
    value_bytes: &[UInt8<F>],
) -> Result<FpVar<F>, SynthesisError> {
    let ty = schema.attribute_type(index).expect("attribute index out of range");
    assert_eq!(value_bytes.len(), ty.value_len());
    if ty.uses_packed_field_encoding() {
        let mut bits = UInt8::constant(index as u8).to_bits_le()?;
        bits.extend(value_bytes.to_bits_le()?);
        Boolean::le_bits_to_fp(&bits)
    } else {
        let mut preimage: Vec<UInt8<F>> = schema
            .hashed_field_encoding_preimage(index, &[])
            .iter()
            .map(|&b| UInt8::constant(b))
            .collect();
        preimage.extend_from_slice(value_bytes);
        let params = B2SParamsVar::new_constant(value_bytes.cs(), ())?;
        let digest = ROGadget::evaluate(&params, &preimage)?.0;
        Boolean::le_bits_to_fp(&digest[..HASHED_FE_BYTES].to_bits_le()?)
    }
}

/// Inverse of [`value_to_field_element`]: given the field element `fe` of attribute `index`
/// (typically a witness shared with a commit-and-prove commitment), recovers and parses the
/// value bytes, enforcing that they encode to `fe`.
///
/// For packed types the bytes are obtained by decomposing `fe` (with the high bits enforced to
/// be zero), so no extra witness is needed and `value_bytes` is not called. For hashed types
/// the bytes must be supplied as a witness through `value_bytes`, and the circuit enforces
/// `fe == pack(Blake2s(preimage)[..31])`.
///
/// Returns the parsed attribute together with its canonical value bytes.
pub fn parse_field_element<F: PrimeField>(
    schema: &CredentialSchema,
    index: usize,
    fe: &FpVar<F>,
    value_bytes: impl FnOnce() -> Result<Vec<u8>, SynthesisError>,
) -> Result<(AttributeVar<F>, Vec<UInt8<F>>), SynthesisError> {
    let ty = schema.attribute_type(index).expect("attribute index out of range");
    let bytes: Vec<UInt8<F>> = if ty.uses_packed_field_encoding() {
        let num_bytes = 1 + ty.value_len();
        assert!(num_bytes <= MAX_PACKED_LEN);
        let (bits, _) = fe.to_bits_le_with_top_bits_zero(8 * num_bytes)?;
        let bytes: Vec<UInt8<F>> = bits.chunks(8).map(UInt8::from_bits_le).collect();
        bytes[0].enforce_equal(&UInt8::constant(index as u8))?;
        bytes[1..].to_vec()
    } else {
        let cs = fe.cs();
        let native = value_bytes();
        let mut bytes = Vec::with_capacity(ty.value_len());
        for j in 0..ty.value_len() {
            bytes.push(UInt8::new_witness(cs.clone(), || native.as_ref().map(|v| v[j]).map_err(|e| e.clone()))?);
        }
        value_to_field_element(schema, index, &bytes)?.enforce_equal(fe)?;
        bytes
    };
    let parsed = parse_value(&ty, &bytes)?;
    Ok((parsed, bytes))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::credential::{tests::{example_schema, example_values}, AttributeValue, EncodingError, Leaf};
    use ark_bls12_381::Fr;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{rand::RngCore, test_rng};

    fn alloc_bytes(cs: &ark_relations::r1cs::ConstraintSystemRef<Fr>, bytes: &[u8]) -> Vec<UInt8<Fr>> {
        bytes.iter().map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)).unwrap()).collect()
    }

    /// The gadget accepts a leaf iff the native strict decoder does.
    fn gadget_accepts_leaf(schema: &CredentialSchema, index: usize, leaf: &[u8]) -> bool {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let leaf_var = alloc_bytes(&cs, leaf);
        parse_leaf(schema, index, &leaf_var).unwrap();
        cs.is_satisfied().unwrap()
    }

    #[test]
    fn accepts_canonical_leaves() {
        let schema = example_schema();
        let leaves = schema.encode_leaves(&example_values()).unwrap();
        for (i, leaf) in leaves.iter().enumerate() {
            assert!(gadget_accepts_leaf(&schema, i, &leaf.0), "attribute {}", i);
        }
    }

    #[test]
    fn rejects_exactly_what_the_native_decoder_rejects() {
        let schema = example_schema();
        let leaves = schema.encode_leaves(&example_values()).unwrap();
        let mut rng = test_rng();
        let mut checked = 0;
        for (i, Leaf(leaf)) in leaves.iter().enumerate() {
            // The circuit enforces canonical form but not UTF-8 validity of strings (see the
            // module docs), so a native `InvalidUtf8` rejection corresponds to acceptance.
            let native_accepts = |bytes: &[u8]| match schema.decode_leaf(bytes) {
                Ok((j, _)) => j == i,
                Err(EncodingError::InvalidUtf8 { index }) => index == i,
                Err(_) => false,
            };
            // every single-byte mutation of every leaf
            for pos in 0..leaf.len() {
                for delta in [1u8, 0x10, 0x80, 0xFF] {
                    let mut mutated = leaf.clone();
                    mutated[pos] = mutated[pos].wrapping_add(delta);
                    assert_eq!(gadget_accepts_leaf(&schema, i, &mutated), native_accepts(&mutated), "attribute {} pos {} delta {}", i, pos, delta);
                    checked += 1;
                }
            }
            // random leaves of the right length
            for _ in 0..20 {
                let mut random = vec![0u8; leaf.len()];
                rng.fill_bytes(&mut random);
                random[0] = i as u8;
                assert_eq!(gadget_accepts_leaf(&schema, i, &random), native_accepts(&random));
                checked += 1;
            }
        }
        assert!(checked > 300);
    }

    #[test]
    fn specific_malformed_encodings_are_rejected() {
        let schema = example_schema();
        // wrong index byte (a well-formed enum value, but claiming to be attribute 3)
        assert!(!gadget_accepts_leaf(&schema, 2, &[3, 1]));
        // enum label == cardinality
        assert!(!gadget_accepts_leaf(&schema, 2, &[2, 3]));
        // uint with bit 36 set
        assert!(!gadget_accepts_leaf(&schema, 4, &[4, 0, 0, 0, 0, 0x10]));
        // month 13, day 0, year 0
        assert!(!gadget_accepts_leaf(&schema, 3, &[&[3u8][..], &20001301u32.to_le_bytes()[..]].concat()));
        assert!(!gadget_accepts_leaf(&schema, 3, &[&[3u8][..], &20000100u32.to_le_bytes()[..]].concat()));
        assert!(!gadget_accepts_leaf(&schema, 3, &[&[3u8][..], &101u32.to_le_bytes()[..]].concat()));
        // a packed value that is not of the form y*10000+m*100+d with valid components,
        // e.g. 2000-13-01 written as 20001301 is caught above; also a large garbage integer
        assert!(!gadget_accepts_leaf(&schema, 3, &[&[3u8][..], &0xFFFF_FFFFu32.to_le_bytes()[..]].concat()));
        // string with non-zero padding / length > max_len
        let mut s = schema.encode_leaf(1, &AttributeValue::String("Bob".into())).unwrap().0;
        s[1 + 1 + 3] = b'!';
        assert!(!gadget_accepts_leaf(&schema, 1, &s));
        let mut s = vec![0u8; 22];
        s[0] = 1;
        s[1] = 21;
        assert!(!gadget_accepts_leaf(&schema, 1, &s));
    }

    #[test]
    fn predicates() {
        let schema = example_schema();
        let leaves = schema.encode_leaves(&example_values()).unwrap();
        let cs = ConstraintSystem::<Fr>::new_ref();
        let name = parse_leaf(&schema, 1, &alloc_bytes(&cs, &leaves[1].0)).unwrap();
        let citizenship = parse_leaf(&schema, 2, &alloc_bytes(&cs, &leaves[2].0)).unwrap();
        let dob = parse_leaf(&schema, 3, &alloc_bytes(&cs, &leaves[3].0)).unwrap();
        let phone = parse_leaf(&schema, 4, &alloc_bytes(&cs, &leaves[4].0)).unwrap();
        name.enforce_string_equals("Alice").unwrap();
        citizenship.enforce_enum_in(&[0, 1]).unwrap();
        dob.enforce_date_at_most(2008, 9, 21).unwrap();
        dob.enforce_date_at_least(1991, 3, 14).unwrap();
        phone.enforce_uint_in_range(5553141, 5553141).unwrap();
        assert!(cs.is_satisfied().unwrap());
        let n = cs.num_constraints();

        // each failing predicate makes the system unsatisfiable
        citizenship.enforce_enum_in(&[0, 2]).unwrap();
        assert!(!cs.is_satisfied().unwrap());
        let cs = ConstraintSystem::<Fr>::new_ref();
        let dob = parse_leaf(&schema, 3, &alloc_bytes(&cs, &leaves[3].0)).unwrap();
        dob.enforce_date_at_most(1991, 3, 13).unwrap();
        assert!(!cs.is_satisfied().unwrap());
        let cs = ConstraintSystem::<Fr>::new_ref();
        let name = parse_leaf(&schema, 1, &alloc_bytes(&cs, &leaves[1].0)).unwrap();
        name.enforce_string_equals("Alicf").unwrap();
        assert!(!cs.is_satisfied().unwrap());
        let cs = ConstraintSystem::<Fr>::new_ref();
        let phone = parse_leaf(&schema, 4, &alloc_bytes(&cs, &leaves[4].0)).unwrap();
        phone.enforce_uint_in_range(0, 5553140).unwrap();
        assert!(!cs.is_satisfied().unwrap());
        println!("constraints for parsing 4 attributes + 5 predicates: {}", n);
    }

    #[test]
    fn field_element_encoding_matches_native_and_roundtrips() {
        let schema = example_schema();
        let values = example_values();
        for i in 0..values.len() {
            let value_bytes = schema.encode_value(i, &values[i]).unwrap();
            let native_fe: Fr = schema.attribute_to_field(i, &values[i]).unwrap();

            // bytes -> field element
            let cs = ConstraintSystem::<Fr>::new_ref();
            let bytes_var = alloc_bytes(&cs, &value_bytes);
            let fe_var = value_to_field_element(&schema, i, &bytes_var).unwrap();
            assert_eq!(fe_var.value().unwrap(), native_fe);
            fe_var.enforce_equal(&FpVar::constant(native_fe)).unwrap();
            assert!(cs.is_satisfied().unwrap());

            // field element -> parsed bytes
            let cs = ConstraintSystem::<Fr>::new_ref();
            let fe_var = FpVar::new_witness(cs.clone(), || Ok(native_fe)).unwrap();
            let vb = value_bytes.clone();
            let (_, recovered) = parse_field_element(&schema, i, &fe_var, || Ok(vb)).unwrap();
            assert_eq!(recovered.value().unwrap(), value_bytes);
            assert!(cs.is_satisfied().unwrap());

            // a different field element does not parse to these bytes (+1 changes the index
            // byte of a packed encoding, and is not the hash-derived element of a hashed one)
            let cs = ConstraintSystem::<Fr>::new_ref();
            let fe_var = FpVar::new_witness(cs.clone(), || Ok(native_fe + Fr::from(1u64))).unwrap();
            let vb = value_bytes.clone();
            let _ = parse_field_element(&schema, i, &fe_var, || Ok(vb));
            assert!(!cs.is_satisfied().unwrap(), "attribute {}", i);
        }
    }

    #[test]
    fn field_element_with_wrong_index_is_rejected() {
        let schema = example_schema();
        // the packed element of (index 2, Enum(1)) presented as attribute 4? types differ in
        // length so the top-bits-zero check or the index byte check must fail
        let fe: Fr = schema.attribute_to_field(2, &AttributeValue::Enum(1)).unwrap();
        let cs = ConstraintSystem::<Fr>::new_ref();
        let fe_var = FpVar::new_witness(cs.clone(), || Ok(fe)).unwrap();
        let _ = parse_field_element(&schema, 4, &fe_var, || Ok(vec![]));
        assert!(!cs.is_satisfied().unwrap());
        // same length, different slot: schema with two enums
        let schema2 = CredentialSchema::new(
            *b"two-enum",
            vec![
                super::super::AttributeSpec::new("a", AttributeType::Enum { cardinality: 3 }),
                super::super::AttributeSpec::new("b", AttributeType::Enum { cardinality: 3 }),
            ],
        )
        .unwrap();
        let fe: Fr = schema2.attribute_to_field(0, &AttributeValue::Enum(1)).unwrap();
        let cs = ConstraintSystem::<Fr>::new_ref();
        let fe_var = FpVar::new_witness(cs.clone(), || Ok(fe)).unwrap();
        let _ = parse_field_element(&schema2, 1, &fe_var, || Ok(vec![]));
        assert!(!cs.is_satisfied().unwrap());
    }
}
