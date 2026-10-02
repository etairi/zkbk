// SPDX-License-Identifier: Apache-2.0

//! R1CS gadgets for [`super::evaluate`] with a secret key and a public input `x`.
//!
//! The key is allocated once as a little-endian bit vector ([`KeyVar`]) and shared by all
//! evaluations that must use the same key. `H(x)` is computed outside the circuit, so an
//! evaluation is a single scalar multiplication:
//!
//! * [`evaluate_constant_base`]: `x` is fixed when the circuit is built (e.g. a context string);
//!   fixed-base multiplication with 2-bit lookup tables over precomputed multiples of `H(x)`;
//! * [`evaluate_input_base`]: `H(x)` is a public input that the verifier computes from the
//!   public `x` (e.g. an issuer key that varies per proof); variable-base double-and-add.
//!
//! The base must be a constant or a public input, never a prover-chosen witness: the relation
//! proven is "`y` is the x-coordinate of `[K]·base`". Secret inputs `x` would require evaluating
//! `H` inside the circuit, which these gadgets do not do.

use ark_ec::twisted_edwards::{Affine, Projective, TECurveConfig};
use ark_ec::{AdditiveGroup, CurveConfig};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::curves::twisted_edwards::AffineVar;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::{borrow::Borrow, marker::PhantomData};

/// A point of the twisted Edwards curve `P`, in R1CS over `P`'s base field.
pub type PointVar<P> = AffineVar<P, FpVar<<P as CurveConfig>::BaseField>>;

/// The PRF key `K` (a scalar of the curve, type `S`) as `S::MODULUS_BIT_SIZE` little-endian
/// bits over the constraint field `F`.
pub struct KeyVar<S: PrimeField, F: PrimeField> {
    pub bits: Vec<Boolean<F>>,
    _scalar: PhantomData<S>,
}

impl<S: PrimeField, F: PrimeField> AllocVar<S, F> for KeyVar<S, F> {
    fn new_variable<T: Borrow<S>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let value = f().map(|key| key.borrow().into_bigint().to_bits_le());
        let bits = (0..S::MODULUS_BIT_SIZE as usize)
            .map(|i| Boolean::new_variable(cs.clone(), || value.as_ref().map(|b| b[i]).map_err(|e| *e), mode))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(KeyVar { bits, _scalar: PhantomData })
    }
}

/// `PRF(K, x)` for an `x` known when the circuit is built: the x-coordinate of `[K]·base`, where
/// `base = H(x)` (see [`super::hash_to_curve`]) is a circuit constant.
pub fn evaluate_constant_base<P>(
    key: &KeyVar<P::ScalarField, P::BaseField>,
    base: &Affine<P>,
) -> Result<FpVar<P::BaseField>, SynthesisError>
where
    P: TECurveConfig,
    P::BaseField: PrimeField,
{
    let mut multiples = Vec::with_capacity(key.bits.len());
    let mut multiple = Projective::<P>::from(*base);
    for _ in 0..key.bits.len() {
        multiples.push(multiple);
        multiple.double_in_place();
    }
    let mut result = PointVar::<P>::zero();
    result.precomputed_base_scalar_mul_le(key.bits.iter().zip(multiples.iter()))?;
    Ok(result.x)
}

/// `PRF(K, x)` for `base = H(x)` allocated by the caller as a public input (computed by the
/// verifier from the public `x`): the x-coordinate of `[K]·base`.
pub fn evaluate_input_base<P>(
    key: &KeyVar<P::ScalarField, P::BaseField>,
    base: &PointVar<P>,
) -> Result<FpVar<P::BaseField>, SynthesisError>
where
    P: TECurveConfig,
    P::BaseField: PrimeField,
{
    Ok(base.scalar_mul_le(key.bits.iter())?.x)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prf::ddh;
    use ark_ed_on_bls12_381::{EdwardsConfig, Fq, Fr};
    use ark_ff::{Field, UniformRand};
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSystemRef};
    use rand::SeedableRng;

    fn keys() -> Vec<Fr> {
        let mut rng = rand_chacha::ChaCha8Rng::from_seed([8u8; 32]);
        let mut keys = vec![Fr::ZERO, Fr::ONE, -Fr::ONE, Fr::from_le_bytes_mod_order(&[42u8; 32])];
        keys.extend((0..4).map(|_| Fr::rand(&mut rng)));
        keys
    }

    const INPUTS: [&[u8]; 3] = [b"", b"example.org/forum", &[7u8; 32]];

    /// Allocates `key`, evaluates `PRF(key, input)` with the requested gadget and enforces the
    /// result to equal the public `claimed` output.
    fn prove(key: Fr, input: &[u8], claimed: Fq, input_base: bool) -> ConstraintSystemRef<Fq> {
        let cs = ConstraintSystem::<Fq>::new_ref();
        let claimed_var = FpVar::new_input(cs.clone(), || Ok(claimed)).unwrap();
        let key_var = KeyVar::<Fr, Fq>::new_witness(cs.clone(), || Ok(key)).unwrap();
        let base = ddh::hash_to_curve::<EdwardsConfig>(input);
        let output = if input_base {
            let base_var = PointVar::<EdwardsConfig>::new_input(cs.clone(), || Ok(base)).unwrap();
            evaluate_input_base(&key_var, &base_var).unwrap()
        } else {
            evaluate_constant_base(&key_var, &base).unwrap()
        };
        assert_eq!(output.value().unwrap(), ddh::evaluate::<EdwardsConfig>(&key, input));
        output.enforce_equal(&claimed_var).unwrap();
        cs
    }

    #[test]
    fn gadgets_match_the_native_evaluation() {
        for key in keys() {
            for input in INPUTS {
                let y = ddh::evaluate::<EdwardsConfig>(&key, input);
                for input_base in [false, true] {
                    assert!(prove(key, input, y, input_base).is_satisfied().unwrap());
                }
            }
        }
    }

    #[test]
    fn output_under_another_key_is_rejected() {
        let mut rng = rand_chacha::ChaCha8Rng::from_seed([9u8; 32]);
        let (key, other) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
        let y_other = ddh::evaluate::<EdwardsConfig>(&other, INPUTS[1]);
        for input_base in [false, true] {
            assert!(!prove(key, INPUTS[1], y_other, input_base).is_satisfied().unwrap());
        }
    }

    #[test]
    fn output_for_another_input_is_rejected() {
        let mut rng = rand_chacha::ChaCha8Rng::from_seed([10u8; 32]);
        let key = Fr::rand(&mut rng);
        let y_other_input = ddh::evaluate::<EdwardsConfig>(&key, INPUTS[2]);
        for input_base in [false, true] {
            assert!(!prove(key, INPUTS[1], y_other_input, input_base).is_satisfied().unwrap());
        }
    }
}
