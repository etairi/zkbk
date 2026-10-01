// SPDX-License-Identifier: Apache-2.0

//! Canonical credential encoding.
//!
//! The zero-knowledge gadgets in this crate treat their inputs as opaque byte strings, field
//! elements and curve points. Nothing in the proof system itself says that the byte string
//! sitting at leaf 3 of a Merkle tree *is* the holder's citizenship, or that the field element
//! `20080921` *is* a date. This module fixes that binding by defining, for a given
//! [`CredentialSchema`]:
//!
//! 1. a **canonical byte encoding** of every attribute value (total and injective: every value
//!    has exactly one encoding, and every byte string is the encoding of at most one value),
//! 2. a **self-describing Merkle leaf** `leaf_i = [i] || encode(att_i)` (the attribute index is
//!    part of the leaf, so a leaf cannot be re-interpreted as a different attribute), and
//! 3. an **injective map from attributes to field elements**, for the polynomial/KZG
//!    commitments of the black-box construction [CGLMPS26, §8–9], where attributes are roots
//!    or evaluations of a polynomial over the scalar field.
//!
//! The companion module [`constraints`] re-implements the *decoding* side inside R1CS: given
//! the leaf bytes (or the field element) as a witness, it enforces well-formedness (enum in
//! range, integer within its bit width, date components in range, zero padding of strings)
//! and returns typed gadget values on which predicates can be evaluated. Together with an
//! issuer signature over the Merkle root, this is what makes the statement "the attribute the
//! issuer certified satisfies `f`" hold for the *decoded* value rather than for whatever bytes
//! the prover chose to open. The only check of the native decoder that the circuit does not
//! replicate is UTF-8 validity of strings (see [`EncodingError::InvalidUtf8`]).
//!
//! What this module does **not** do: it cannot check that the issuer verified the attribute
//! correctly. That is the personhood-attribute-validation oracle of the paper and is a trust
//! assumption on the issuer, not something a circuit can enforce.

pub mod constraints;

use ark_ff::{BigInteger, PrimeField};
use ark_serialize::{CanonicalSerialize, Compress, SerializationError, Write};
use blake2::Blake2s;
use digest::Digest;

/// Attributes whose `1 + value_len()` fits in this many bytes are mapped to a field element by
/// packing (no hashing). 31 bytes = 248 bits, which is below the modulus of every field this
/// crate is used with (BLS12-381 Fr: 255 bits, BLS12-377 Fr: 253 bits, BW6-761 Fr: 377 bits).
pub const MAX_PACKED_LEN: usize = 31;

/// Number of bytes of a Blake2s digest that are packed into a field element for attributes
/// that are too long for the packed encoding.
pub const HASHED_FE_BYTES: usize = 31;

/// Domain separator for the hashed field-element encoding.
pub const FIELD_ENCODING_DOMAIN: &[u8] = b"fp-snark/credential/attribute-to-field/v1";

/// First byte of padding leaves (positions beyond the schema's attributes, used to bring the
/// number of Merkle leaves to a power of two). A real leaf always starts with its attribute
/// index, which is `< MAX_ATTRIBUTES <= 0xFF`, so padding can never parse as an attribute.
pub const PADDING_LEAF_TAG: u8 = 0xFF;

/// Upper bound on the number of attributes in a schema (indices must fit in one byte and must
/// not collide with [`PADDING_LEAF_TAG`]).
pub const MAX_ATTRIBUTES: usize = 128;

/// Types of attribute values. Every type has a fixed-width canonical byte encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AttributeType {
    /// A value from a finite set of `cardinality` labels, stored as one byte `< cardinality`.
    Enum { cardinality: u16 },
    /// An unsigned integer of at most `bits` bits (1..=64), little-endian in `ceil(bits/8)`
    /// bytes; the unused high bits of the last byte must be zero.
    UInt { bits: u8 },
    /// A calendar date, stored as the `u32` `year * 10000 + month * 100 + day` (little-endian,
    /// 4 bytes) with `1 <= year <= 9999`, `1 <= month <= 12`, `1 <= day <= 31`. The packed
    /// integer is order-preserving, so date comparisons are integer comparisons.
    Date,
    /// A UTF-8 string of at most `max_len` bytes: one length byte followed by `max_len` bytes,
    /// zero-padded after the `len`-th byte.
    String { max_len: u8 },
    /// An opaque byte string of exactly `len` bytes (keys, hashes, PRF outputs).
    Bytes { len: u8 },
}

impl AttributeType {
    /// Length in bytes of the canonical encoding of a value of this type (without the leaf's
    /// index byte).
    pub fn value_len(&self) -> usize {
        match self {
            AttributeType::Enum { .. } => 1,
            AttributeType::UInt { bits } => (*bits as usize + 7) / 8,
            AttributeType::Date => 4,
            AttributeType::String { max_len } => 1 + *max_len as usize,
            AttributeType::Bytes { len } => *len as usize,
        }
    }

    /// Whether values of this type are mapped to field elements by packing (as opposed to
    /// hashing). See [`CredentialSchema::attribute_to_field`].
    pub fn uses_packed_field_encoding(&self) -> bool {
        1 + self.value_len() <= MAX_PACKED_LEN
    }

    fn validate(&self, index: usize) -> Result<(), EncodingError> {
        let bad = |reason: &str| EncodingError::InvalidSchema { index, reason: reason.into() };
        match self {
            AttributeType::Enum { cardinality } => {
                if *cardinality == 0 || *cardinality > 256 {
                    return Err(bad("enum cardinality must be in 1..=256"));
                }
            }
            AttributeType::UInt { bits } => {
                if *bits == 0 || *bits > 64 {
                    return Err(bad("uint bit width must be in 1..=64"));
                }
            }
            AttributeType::Date => {}
            AttributeType::String { max_len } => {
                if *max_len == 0 {
                    return Err(bad("string max_len must be >= 1"));
                }
            }
            AttributeType::Bytes { len } => {
                if *len == 0 {
                    return Err(bad("bytes len must be >= 1"));
                }
            }
        }
        Ok(())
    }
}

/// A typed attribute value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AttributeValue {
    Enum(u8),
    UInt(u64),
    Date { year: u16, month: u8, day: u8 },
    String(String),
    Bytes(Vec<u8>),
}

impl AttributeValue {
    /// The order-preserving packed representation of a date, `year * 10000 + month * 100 + day`.
    pub fn packed_date(year: u16, month: u8, day: u8) -> u32 {
        year as u32 * 10_000 + month as u32 * 100 + day as u32
    }
}

/// A named, typed attribute slot of a schema.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttributeSpec {
    pub name: String,
    pub ty: AttributeType,
}

impl AttributeSpec {
    pub fn new(name: &str, ty: AttributeType) -> Self {
        AttributeSpec { name: name.into(), ty }
    }
}

/// An ordered list of attribute slots. The position of an attribute in the schema is the
/// position of its leaf in the credential's Merkle tree, and is also embedded in the leaf.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CredentialSchema {
    /// Identifier of the schema; the issuer must sign it together with the commitment to the
    /// attributes so that a credential cannot be presented under a different schema.
    pub id: [u8; 8],
    pub attributes: Vec<AttributeSpec>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncodingError {
    InvalidSchema { index: usize, reason: String },
    IndexOutOfRange(usize),
    TypeMismatch { index: usize },
    ValueOutOfRange { index: usize, reason: String },
    NonCanonical { index: usize, reason: String },
    /// The string bytes are in canonical form (length, zero padding) but are not valid UTF-8.
    /// This is the one property of the encoding that the R1CS parser does **not** enforce:
    /// strings are treated as byte strings in-circuit (predicates on them are byte-wise), and
    /// whether the issuer signed valid UTF-8 does not affect the soundness of those predicates.
    InvalidUtf8 { index: usize },
    WrongLength { index: usize, expected: usize, got: usize },
    WrongAttributeCount { expected: usize, got: usize },
}

/// A Merkle leaf: raw bytes, serialised **without** a length prefix (unlike `Vec<u8>`, whose
/// `CanonicalSerialize` impl prepends a `u64` length), so that the bytes hashed into the tree
/// are exactly `[index] || encode(value)`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Leaf(pub Vec<u8>);

impl CanonicalSerialize for Leaf {
    fn serialize_with_mode<W: Write>(&self, mut writer: W, _: Compress) -> Result<(), SerializationError> {
        writer.write_all(&self.0)?;
        Ok(())
    }

    fn serialized_size(&self, _: Compress) -> usize {
        self.0.len()
    }
}

impl CredentialSchema {
    pub fn new(id: [u8; 8], attributes: Vec<AttributeSpec>) -> Result<Self, EncodingError> {
        if attributes.is_empty() || attributes.len() > MAX_ATTRIBUTES {
            return Err(EncodingError::InvalidSchema {
                index: attributes.len(),
                reason: format!("schemas must have between 1 and {} attributes", MAX_ATTRIBUTES),
            });
        }
        for (i, spec) in attributes.iter().enumerate() {
            spec.ty.validate(i)?;
        }
        Ok(CredentialSchema { id, attributes })
    }

    pub fn num_attributes(&self) -> usize {
        self.attributes.len()
    }

    pub fn attribute_type(&self, index: usize) -> Result<AttributeType, EncodingError> {
        self.attributes
            .get(index)
            .map(|s| s.ty)
            .ok_or(EncodingError::IndexOutOfRange(index))
    }

    /// Index of the attribute called `name`.
    pub fn index_of(&self, name: &str) -> Option<usize> {
        self.attributes.iter().position(|s| s.name == name)
    }

    /// Length of the Merkle leaf of attribute `index`: one index byte plus the value encoding.
    pub fn leaf_len(&self, index: usize) -> Result<usize, EncodingError> {
        Ok(1 + self.attribute_type(index)?.value_len())
    }

    /// Canonical byte encoding of `value` as attribute `index` (without the index byte).
    pub fn encode_value(&self, index: usize, value: &AttributeValue) -> Result<Vec<u8>, EncodingError> {
        let ty = self.attribute_type(index)?;
        let out_of_range = |reason: &str| EncodingError::ValueOutOfRange { index, reason: reason.into() };
        match (ty, value) {
            (AttributeType::Enum { cardinality }, AttributeValue::Enum(v)) => {
                if *v as u16 >= cardinality {
                    return Err(out_of_range("enum label >= cardinality"));
                }
                Ok(vec![*v])
            }
            (AttributeType::UInt { bits }, AttributeValue::UInt(v)) => {
                if bits < 64 && *v >= (1u64 << bits) {
                    return Err(out_of_range("integer does not fit in the declared bit width"));
                }
                Ok(v.to_le_bytes()[..ty.value_len()].to_vec())
            }
            (AttributeType::Date, AttributeValue::Date { year, month, day }) => {
                if *year == 0 || *year > 9999 {
                    return Err(out_of_range("year must be in 1..=9999"));
                }
                if *month == 0 || *month > 12 {
                    return Err(out_of_range("month must be in 1..=12"));
                }
                if *day == 0 || *day > 31 {
                    return Err(out_of_range("day must be in 1..=31"));
                }
                Ok(AttributeValue::packed_date(*year, *month, *day).to_le_bytes().to_vec())
            }
            (AttributeType::String { max_len }, AttributeValue::String(s)) => {
                let bytes = s.as_bytes();
                if bytes.len() > max_len as usize {
                    return Err(out_of_range("string longer than max_len"));
                }
                let mut out = vec![0u8; 1 + max_len as usize];
                out[0] = bytes.len() as u8;
                out[1..1 + bytes.len()].copy_from_slice(bytes);
                Ok(out)
            }
            (AttributeType::Bytes { len }, AttributeValue::Bytes(b)) => {
                if b.len() != len as usize {
                    return Err(EncodingError::WrongLength { index, expected: len as usize, got: b.len() });
                }
                Ok(b.clone())
            }
            _ => Err(EncodingError::TypeMismatch { index }),
        }
    }

    /// Strict inverse of [`encode_value`](Self::encode_value): rejects every byte string that is
    /// not the canonical encoding of some value (wrong length, out-of-range components, non-zero
    /// padding, invalid UTF-8). This is the specification that the R1CS parser in
    /// [`constraints`] enforces.
    pub fn decode_value(&self, index: usize, bytes: &[u8]) -> Result<AttributeValue, EncodingError> {
        let ty = self.attribute_type(index)?;
        if bytes.len() != ty.value_len() {
            return Err(EncodingError::WrongLength { index, expected: ty.value_len(), got: bytes.len() });
        }
        let non_canonical = |reason: &str| EncodingError::NonCanonical { index, reason: reason.into() };
        match ty {
            AttributeType::Enum { cardinality } => {
                if bytes[0] as u16 >= cardinality {
                    return Err(non_canonical("enum label >= cardinality"));
                }
                Ok(AttributeValue::Enum(bytes[0]))
            }
            AttributeType::UInt { bits } => {
                let mut buf = [0u8; 8];
                buf[..bytes.len()].copy_from_slice(bytes);
                let v = u64::from_le_bytes(buf);
                if bits < 64 && v >= (1u64 << bits) {
                    return Err(non_canonical("high bits beyond the declared width are set"));
                }
                Ok(AttributeValue::UInt(v))
            }
            AttributeType::Date => {
                let packed = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
                let year = packed / 10_000;
                let month = (packed / 100) % 100;
                let day = packed % 100;
                if year == 0 || year > 9999 || month == 0 || month > 12 || day == 0 || day > 31 {
                    return Err(non_canonical("date components out of range"));
                }
                Ok(AttributeValue::Date { year: year as u16, month: month as u8, day: day as u8 })
            }
            AttributeType::String { max_len } => {
                let len = bytes[0] as usize;
                if len > max_len as usize {
                    return Err(non_canonical("string length byte > max_len"));
                }
                if bytes[1 + len..].iter().any(|&b| b != 0) {
                    return Err(non_canonical("non-zero padding after the string"));
                }
                let s = core::str::from_utf8(&bytes[1..1 + len]).map_err(|_| EncodingError::InvalidUtf8 { index })?;
                Ok(AttributeValue::String(s.into()))
            }
            AttributeType::Bytes { .. } => Ok(AttributeValue::Bytes(bytes.to_vec())),
        }
    }

    /// The Merkle leaf of attribute `index`: `[index] || encode_value(index, value)`.
    pub fn encode_leaf(&self, index: usize, value: &AttributeValue) -> Result<Leaf, EncodingError> {
        let mut leaf = Vec::with_capacity(self.leaf_len(index)?);
        leaf.push(index as u8);
        leaf.extend(self.encode_value(index, value)?);
        Ok(Leaf(leaf))
    }

    /// Strict inverse of [`encode_leaf`](Self::encode_leaf).
    pub fn decode_leaf(&self, leaf: &[u8]) -> Result<(usize, AttributeValue), EncodingError> {
        let index = *leaf.first().ok_or(EncodingError::WrongLength { index: 0, expected: 1, got: 0 })? as usize;
        if index >= self.attributes.len() {
            return Err(EncodingError::IndexOutOfRange(index));
        }
        Ok((index, self.decode_value(index, &leaf[1..])?))
    }

    /// Encodes a full attribute vector (one value per schema slot, in order) into leaves.
    pub fn encode_leaves(&self, values: &[AttributeValue]) -> Result<Vec<Leaf>, EncodingError> {
        if values.len() != self.attributes.len() {
            return Err(EncodingError::WrongAttributeCount { expected: self.attributes.len(), got: values.len() });
        }
        values.iter().enumerate().map(|(i, v)| self.encode_leaf(i, v)).collect()
    }

    /// Appends padding leaves until the number of leaves is a power of two (and at least two),
    /// as required by [`crate::merkle_tree::MerkleTree`]. Padding leaves start with
    /// [`PADDING_LEAF_TAG`] and can never be decoded as an attribute.
    pub fn pad_leaves_to_pow2(mut leaves: Vec<Leaf>) -> Vec<Leaf> {
        let target = leaves.len().max(2).next_power_of_two();
        while leaves.len() < target {
            leaves.push(Leaf(vec![PADDING_LEAF_TAG, leaves.len() as u8]));
        }
        leaves
    }

    /// Preimage of the hashed field-element encoding of attribute `index` with canonical value
    /// bytes `value_bytes`: `FIELD_ENCODING_DOMAIN || schema.id || [index] || value_bytes`.
    pub fn hashed_field_encoding_preimage(&self, index: usize, value_bytes: &[u8]) -> Vec<u8> {
        let mut preimage = Vec::with_capacity(FIELD_ENCODING_DOMAIN.len() + 9 + value_bytes.len());
        preimage.extend_from_slice(FIELD_ENCODING_DOMAIN);
        preimage.extend_from_slice(&self.id);
        preimage.push(index as u8);
        preimage.extend_from_slice(value_bytes);
        preimage
    }

    /// Injective map from an attribute (index and value) to a field element, for use as an
    /// attribute in the KZG/polynomial commitments of the black-box construction.
    ///
    /// * If `1 + value_len <= MAX_PACKED_LEN`, the element is the little-endian integer
    ///   `[index] || value_bytes` (at most 248 bits, so no modular reduction takes place and
    ///   the map is injective; the index prefix separates attributes with equal values).
    /// * Otherwise the element is the little-endian integer formed by the first
    ///   [`HASHED_FE_BYTES`] bytes of `Blake2s(hashed_field_encoding_preimage)`; injectivity
    ///   then holds up to collisions of the hash.
    ///
    /// The in-circuit counterparts are [`constraints::value_to_field_element`] and
    /// [`constraints::parse_field_element`].
    pub fn attribute_to_field<F: PrimeField>(&self, index: usize, value: &AttributeValue) -> Result<F, EncodingError> {
        assert!(F::MODULUS_BIT_SIZE as usize > 8 * MAX_PACKED_LEN, "field too small for the packed encoding");
        let value_bytes = self.encode_value(index, value)?;
        Ok(field_from_value_bytes::<F>(self, index, &value_bytes))
    }

    /// Inverse of [`attribute_to_field`](Self::attribute_to_field) for attributes that use the
    /// packed encoding: recovers `(index, value)` from a field element, rejecting elements that
    /// are not the packed encoding of a well-formed attribute of this schema (unknown index,
    /// hashed type, bits set beyond the packed width, non-canonical value bytes).
    ///
    /// This is what the verifier of a vouch runs on the revealed values `att'` of the black-box
    /// construction to learn *which* attribute was revealed and what it says. Hashed encodings
    /// cannot be inverted; check a claimed opening with
    /// [`verify_field_element`](Self::verify_field_element) instead.
    pub fn decode_field_element<F: PrimeField>(&self, fe: F) -> Result<(usize, AttributeValue), EncodingError> {
        let bytes = fe.into_bigint().to_bytes_le();
        let index = bytes[0] as usize;
        let ty = self.attribute_type(index)?;
        if !ty.uses_packed_field_encoding() {
            return Err(EncodingError::NonCanonical { index, reason: "attribute uses the hashed field encoding".into() });
        }
        let packed_len = 1 + ty.value_len();
        if bytes[packed_len..].iter().any(|&b| b != 0) {
            return Err(EncodingError::NonCanonical { index, reason: "field element exceeds the packed width".into() });
        }
        Ok((index, self.decode_value(index, &bytes[1..packed_len])?))
    }

    /// Checks that `fe` is the field element of attribute `index` with value `value`.
    pub fn verify_field_element<F: PrimeField>(&self, index: usize, value: &AttributeValue, fe: F) -> Result<bool, EncodingError> {
        Ok(self.attribute_to_field::<F>(index, value)? == fe)
    }
}

/// [`CredentialSchema::attribute_to_field`] on already-encoded value bytes.
pub fn field_from_value_bytes<F: PrimeField>(schema: &CredentialSchema, index: usize, value_bytes: &[u8]) -> F {
    if 1 + value_bytes.len() <= MAX_PACKED_LEN {
        let mut packed = Vec::with_capacity(1 + value_bytes.len());
        packed.push(index as u8);
        packed.extend_from_slice(value_bytes);
        F::from_le_bytes_mod_order(&packed)
    } else {
        let digest = Blake2s::digest(&schema.hashed_field_encoding_preimage(index, value_bytes));
        F::from_le_bytes_mod_order(&digest[..HASHED_FE_BYTES])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ff::Field;

    pub(crate) fn example_schema() -> CredentialSchema {
        CredentialSchema::new(
            *b"PHC-v1\0\0",
            vec![
                AttributeSpec::new("pk", AttributeType::Bytes { len: 32 }),
                AttributeSpec::new("name", AttributeType::String { max_len: 20 }),
                AttributeSpec::new("citizenship", AttributeType::Enum { cardinality: 3 }),
                AttributeSpec::new("date_of_birth", AttributeType::Date),
                AttributeSpec::new("phone", AttributeType::UInt { bits: 36 }),
            ],
        )
        .unwrap()
    }

    pub(crate) fn example_values() -> Vec<AttributeValue> {
        vec![
            AttributeValue::Bytes(vec![7u8; 32]),
            AttributeValue::String("Alice".into()),
            AttributeValue::Enum(1),
            AttributeValue::Date { year: 1991, month: 3, day: 14 },
            AttributeValue::UInt(5553141),
        ]
    }

    #[test]
    fn roundtrip() {
        let schema = example_schema();
        let values = example_values();
        let leaves = schema.encode_leaves(&values).unwrap();
        assert_eq!(leaves.len(), 5);
        for (i, leaf) in leaves.iter().enumerate() {
            assert_eq!(leaf.0.len(), schema.leaf_len(i).unwrap());
            assert_eq!(leaf.0[0], i as u8);
            assert_eq!(schema.decode_leaf(&leaf.0).unwrap(), (i, values[i].clone()));
        }
        // fixed layouts
        assert_eq!(leaves[1].0, [&[1u8, 5][..], b"Alice", &[0u8; 15][..]].concat());
        assert_eq!(leaves[2].0, vec![2, 1]);
        assert_eq!(leaves[3].0, [&[3u8][..], &19910314u32.to_le_bytes()[..]].concat());
        assert_eq!(leaves[4].0, [&[4u8][..], &5553141u64.to_le_bytes()[..5]].concat());
    }

    #[test]
    fn rejects_out_of_range_values() {
        let schema = example_schema();
        assert!(matches!(schema.encode_value(2, &AttributeValue::Enum(3)), Err(EncodingError::ValueOutOfRange { .. })));
        assert!(matches!(schema.encode_value(4, &AttributeValue::UInt(1 << 36)), Err(EncodingError::ValueOutOfRange { .. })));
        assert!(matches!(
            schema.encode_value(3, &AttributeValue::Date { year: 2000, month: 13, day: 1 }),
            Err(EncodingError::ValueOutOfRange { .. })
        ));
        assert!(matches!(
            schema.encode_value(1, &AttributeValue::String("x".repeat(21))),
            Err(EncodingError::ValueOutOfRange { .. })
        ));
        assert!(matches!(schema.encode_value(0, &AttributeValue::Bytes(vec![1; 31])), Err(EncodingError::WrongLength { .. })));
        assert!(matches!(schema.encode_value(2, &AttributeValue::UInt(1)), Err(EncodingError::TypeMismatch { .. })));
        assert!(matches!(schema.encode_value(9, &AttributeValue::Enum(1)), Err(EncodingError::IndexOutOfRange(9))));
    }

    #[test]
    fn decode_is_strict() {
        let schema = example_schema();
        // enum out of range
        assert!(schema.decode_value(2, &[3]).is_err());
        // uint with a high bit beyond 36 bits set
        assert!(schema.decode_value(4, &[0, 0, 0, 0, 0x10]).is_err());
        assert!(schema.decode_value(4, &[0, 0, 0, 0, 0x0F]).is_ok());
        // dates
        assert!(schema.decode_value(3, &20001301u32.to_le_bytes()).is_err());
        assert!(schema.decode_value(3, &20000100u32.to_le_bytes()).is_err());
        assert!(schema.decode_value(3, &20000132u32.to_le_bytes()).is_err());
        assert!(schema.decode_value(3, &0u32.to_le_bytes()).is_err());
        assert!(schema.decode_value(3, &99991231u32.to_le_bytes()).is_ok());
        // string: non-zero padding, length > max, invalid utf-8
        let mut s = schema.encode_value(1, &AttributeValue::String("Bob".into())).unwrap();
        s[20] = 1;
        assert!(schema.decode_value(1, &s).is_err());
        let mut s = vec![0u8; 21];
        s[0] = 21;
        assert!(schema.decode_value(1, &s).is_err());
        let mut s = vec![0u8; 21];
        s[0] = 1;
        s[1] = 0xFF;
        assert_eq!(schema.decode_value(1, &s), Err(EncodingError::InvalidUtf8 { index: 1 }));
        // wrong lengths
        assert!(schema.decode_value(2, &[1, 0]).is_err());
        assert!(schema.decode_leaf(&[]).is_err());
        assert!(schema.decode_leaf(&[PADDING_LEAF_TAG, 5]).is_err());
    }

    #[test]
    fn padding() {
        let schema = example_schema();
        let leaves = CredentialSchema::pad_leaves_to_pow2(schema.encode_leaves(&example_values()).unwrap());
        assert_eq!(leaves.len(), 8);
        for leaf in &leaves[5..] {
            assert_eq!(leaf.0[0], PADDING_LEAF_TAG);
            assert!(schema.decode_leaf(&leaf.0).is_err());
        }
        assert_eq!(CredentialSchema::pad_leaves_to_pow2(vec![Leaf(vec![0, 1])]).len(), 2);
    }

    #[test]
    fn field_encoding_is_injective_on_examples_and_index_separated() {
        let schema = example_schema();
        let values = example_values();
        let fes: Vec<Fr> = (0..5).map(|i| schema.attribute_to_field::<Fr>(i, &values[i]).unwrap()).collect();
        for i in 0..5 {
            for j in 0..5 {
                assert_eq!(fes[i] == fes[j], i == j);
            }
        }
        // packed: the index is the lowest byte, the value follows
        let fe = schema.attribute_to_field::<Fr>(2, &AttributeValue::Enum(1)).unwrap();
        assert_eq!(fe, Fr::from(2u64 + (1u64 << 8)));
        let bytes = fe.into_bigint().to_bytes_le();
        assert_eq!(&bytes[..2], &[2, 1]);
        // the same label in a different slot gives a different element
        let schema2 = CredentialSchema::new(
            *b"other\0\0\0",
            vec![
                AttributeSpec::new("a", AttributeType::Enum { cardinality: 3 }),
                AttributeSpec::new("b", AttributeType::Enum { cardinality: 3 }),
            ],
        )
        .unwrap();
        assert_ne!(
            schema2.attribute_to_field::<Fr>(0, &AttributeValue::Enum(1)).unwrap(),
            schema2.attribute_to_field::<Fr>(1, &AttributeValue::Enum(1)).unwrap()
        );
        // hashed (32-byte value): depends on the schema id and index
        assert!(!AttributeType::Bytes { len: 32 }.uses_packed_field_encoding());
        let schema3 = CredentialSchema::new(*b"PHC-v2\0\0", schema.attributes.clone()).unwrap();
        assert_ne!(
            schema.attribute_to_field::<Fr>(0, &values[0]).unwrap(),
            schema3.attribute_to_field::<Fr>(0, &values[0]).unwrap()
        );
    }

    #[test]
    fn field_element_decoding() {
        let schema = example_schema();
        let values = example_values();
        for i in 1..5 {
            let fe: Fr = schema.attribute_to_field(i, &values[i]).unwrap();
            assert_eq!(schema.decode_field_element(fe).unwrap(), (i, values[i].clone()));
            assert!(schema.verify_field_element(i, &values[i], fe).unwrap());
            assert!(!schema.verify_field_element(i, &values[i], fe + Fr::from(1u64)).unwrap());
        }
        // hashed attribute: not invertible (the first byte is hash-derived, so decoding fails
        // with `IndexOutOfRange` or `NonCanonical`), but verifiable
        let fe: Fr = schema.attribute_to_field(0, &values[0]).unwrap();
        assert!(schema.decode_field_element(fe).is_err());
        assert!(schema.verify_field_element(0, &values[0], fe).unwrap());
        // garbage: unknown index, bits beyond the packed width, non-canonical value
        assert!(matches!(schema.decode_field_element(Fr::from(200u64)), Err(EncodingError::IndexOutOfRange(200))));
        let fe = Fr::from(2u64 + (1u64 << 8)) + Fr::from(2u64).pow([250u64]);
        assert!(matches!(schema.decode_field_element(fe), Err(EncodingError::NonCanonical { .. })));
        assert!(matches!(schema.decode_field_element(Fr::from(2u64 + (3u64 << 8))), Err(EncodingError::NonCanonical { .. })));
    }

    #[test]
    fn leaf_serialises_without_length_prefix() {
        let leaf = Leaf(vec![1, 2, 3]);
        let mut buf = Vec::new();
        leaf.serialize_uncompressed(&mut buf).unwrap();
        assert_eq!(buf, vec![1, 2, 3]);
        assert_eq!(leaf.uncompressed_size(), 3);
    }

    #[test]
    fn schema_validation() {
        assert!(CredentialSchema::new([0; 8], vec![]).is_err());
        assert!(CredentialSchema::new([0; 8], vec![AttributeSpec::new("e", AttributeType::Enum { cardinality: 0 })]).is_err());
        assert!(CredentialSchema::new([0; 8], vec![AttributeSpec::new("e", AttributeType::Enum { cardinality: 257 })]).is_err());
        assert!(CredentialSchema::new([0; 8], vec![AttributeSpec::new("u", AttributeType::UInt { bits: 65 })]).is_err());
        assert!(CredentialSchema::new([0; 8], vec![AttributeSpec::new("s", AttributeType::String { max_len: 0 })]).is_err());
        assert!(CredentialSchema::new([0; 8], vec![AttributeSpec::new("b", AttributeType::Bytes { len: 0 })]).is_err());
        let too_many = (0..=MAX_ATTRIBUTES).map(|_| AttributeSpec::new("e", AttributeType::Enum { cardinality: 2 })).collect();
        assert!(CredentialSchema::new([0; 8], too_many).is_err());
    }
}
