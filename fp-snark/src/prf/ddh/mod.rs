// SPDX-License-Identifier: Apache-2.0

//! DDH-based PRF on a twisted Edwards curve:
//!
//! `PRF(K, x) = x-coordinate of [K]·H(x)`,
//!
//! where `K` is a uniformly random scalar and `H` hashes onto the prime-order subgroup `G`. This
//! is the `H(x)^sk` instantiation suggested in [CGLMPS26, §9.1], moved from BLS12-381 G1 to an
//! embedded curve: over Jubjub (`ark-ed-on-bls12-381`) the group law is native arithmetic in a
//! `Groth16::<Bls12_381>` circuit, whereas G1 points have coordinates in BLS12-381's 381-bit base
//! field.
//!
//! Security: with `H` modelled as a random oracle into `G`, the outputs `[K]·H(x)` are
//! pseudorandom in `G` under the DDH assumption in `G` (the usual random-self-reducibility
//! argument). Taking the x-coordinate loses nothing: on a twisted Edwards curve the only other
//! point with the x-coordinate of `Q` is `-Q + T`, with `T = (0, -1)` of order two, which is not
//! in `G`. The outputs are x-coordinates of pseudorandom points of `G`, not uniform field
//! elements; hash them if uniform bits are needed.
//!
//! Requirement on `H`: nobody may know discrete-log relations between its outputs. `H(x) =
//! h(x)·G` for a fixed generator would be insecure (one output determines all others), and so
//! would a Pedersen hash, which is linear in the bits of `x` like the PRF in [`crate::prf`].
//! [`hash_to_curve`] uses try-and-increment over Blake2b-512 with cofactor clearing. Its running
//! time depends on the input, so it is meant for public inputs (issuer keys, contexts); this is
//! also how the gadgets in [`constraints`] use it: `H(x)` is computed outside the circuit, which
//! only multiplies it by the secret key.
//!
//! [CGLMPS26]: https://eprint.iacr.org/2026/333

pub mod constraints;

use ark_ec::twisted_edwards::{Affine, TECurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{PrimeField, UniformRand};
use ark_std::rand::Rng;
use blake2::Blake2b;
use digest::Digest;

/// Domain-separation tag of [`hash_to_curve`].
pub const HASH_TO_CURVE_DOMAIN: &[u8] = b"fp-snark/prf/ddh/hash-to-curve/v1";

/// Hashes `input` onto the prime-order subgroup of `P`; the result is never the identity.
///
/// Try-and-increment: for `counter = 0, 1, ...` compute
/// `d = Blake2b-512(HASH_TO_CURVE_DOMAIN || len(input) as u64 LE || input || counter as u32 LE)`,
/// take `y = d[0..63]` as a little-endian integer reduced modulo the base field (504 bits, so the
/// bias is negligible) and the choice between the two x-coordinates from the low bit of `d[63]`,
/// and return the first point found, multiplied by the cofactor. Each attempt succeeds with
/// probability about 1/2. Not constant time: use it on public inputs only.
pub fn hash_to_curve<P: TECurveConfig>(input: &[u8]) -> Affine<P>
where
    P::BaseField: PrimeField,
{
    for counter in 0u32.. {
        let mut hasher = Blake2b::new();
        hasher.update(HASH_TO_CURVE_DOMAIN);
        hasher.update((input.len() as u64).to_le_bytes());
        hasher.update(input);
        hasher.update(counter.to_le_bytes());
        let digest = hasher.finalize();
        let y = P::BaseField::from_le_bytes_mod_order(&digest[..63]);
        let greatest = digest[63] & 1 == 1;
        if let Some(point) = Affine::<P>::get_point_from_y_unchecked(y, greatest) {
            let point = point.clear_cofactor();
            if !point.is_zero() {
                return point;
            }
        }
    }
    unreachable!("hash_to_curve: no point found for 2^32 counters")
}

/// Samples a PRF key: a uniformly random scalar.
pub fn keygen<P: TECurveConfig, R: Rng>(rng: &mut R) -> P::ScalarField {
    P::ScalarField::rand(rng)
}

/// `PRF(K, x)`: the x-coordinate of `[K]·H(x)`.
pub fn evaluate<P: TECurveConfig>(key: &P::ScalarField, input: &[u8]) -> P::BaseField
where
    P::BaseField: PrimeField,
{
    evaluate_with_base(key, &hash_to_curve::<P>(input))
}

/// `PRF(K, x)` for a precomputed `base = H(x)`.
pub fn evaluate_with_base<P: TECurveConfig>(key: &P::ScalarField, base: &Affine<P>) -> P::BaseField {
    (*base * key).into_affine().x
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::PrimeGroup;
    use ark_ed_on_bls12_381::{EdwardsAffine, EdwardsConfig, EdwardsProjective, Fq, Fr};
    use ark_ff::{AdditiveGroup, Field};
    use rand::SeedableRng;

    fn inputs() -> Vec<Vec<u8>> {
        let mut inputs = vec![
            vec![],
            b"a".to_vec(),
            b"ab".to_vec(),
            vec![0u8; 32],
            vec![0u8; 33],
            b"example.org/forum".to_vec(),
        ];
        inputs.extend((0u32..200).map(|i| i.to_le_bytes().to_vec()));
        inputs
    }

    #[test]
    fn hash_to_curve_lands_in_the_prime_order_subgroup() {
        let mut seen = std::collections::HashSet::new();
        for input in inputs() {
            let p = hash_to_curve::<EdwardsConfig>(&input);
            assert!(p.is_on_curve());
            assert!(p.is_in_correct_subgroup_assuming_on_curve());
            assert!(!p.is_zero());
            assert_eq!(p, hash_to_curve::<EdwardsConfig>(&input), "deterministic");
            assert!(seen.insert((p.x, p.y)), "distinct inputs gave the same point");
        }
    }

    /// The claim behind using the x-coordinate as the output: for `Q` in the prime-order
    /// subgroup, the other point with the same x-coordinate is `-Q + T` with `T = (0, -1)`, and it
    /// is outside the subgroup.
    #[test]
    fn x_coordinate_is_injective_on_the_prime_order_subgroup() {
        let t = EdwardsAffine::new_unchecked(Fq::ZERO, -Fq::ONE);
        assert!(t.is_on_curve() && !t.is_zero() && t.into_group().double().into_affine().is_zero());
        let mut rng = rand_chacha::ChaCha8Rng::from_seed([5u8; 32]);
        for _ in 0..200 {
            let q = (EdwardsProjective::generator() * Fr::rand(&mut rng)).into_affine();
            let other = EdwardsAffine::new_unchecked(q.x, -q.y);
            assert!(other.is_on_curve());
            assert_ne!(other, q);
            assert_eq!(other, (-q.into_group() + t).into_affine());
            assert!(!other.is_in_correct_subgroup_assuming_on_curve());
        }
    }

    #[test]
    fn evaluate_is_the_x_coordinate_of_the_key_times_the_hash() {
        let mut rng = rand_chacha::ChaCha8Rng::from_seed([6u8; 32]);
        for input in inputs().iter().take(20) {
            let key = keygen::<EdwardsConfig, _>(&mut rng);
            let expected = (hash_to_curve::<EdwardsConfig>(input).into_group() * key).into_affine().x;
            assert_eq!(evaluate::<EdwardsConfig>(&key, input), expected);
        }
        // K = 0 gives the identity (0, 1)
        assert_eq!(evaluate::<EdwardsConfig>(&Fr::ZERO, b"x"), Fq::ZERO);
    }

    /// The computation that predicts outputs of the Pedersen-CRH PRF (see
    /// `known_issue_pedersen_crh_prf_outputs_are_linkable`) has no analogue here: shifting a
    /// recovered output point by `H(x_2) - H(x_1)` does not give `PRF(K, x_2)`. A sanity check,
    /// not a security argument.
    #[test]
    fn the_linear_prediction_does_not_carry_over() {
        let mut rng = rand_chacha::ChaCha8Rng::from_seed([7u8; 32]);
        let (x1, x2) = (b"context-one".as_slice(), b"context-two".as_slice());
        for _ in 0..20 {
            let key = keygen::<EdwardsConfig, _>(&mut rng);
            let (y1, y2) = (evaluate::<EdwardsConfig>(&key, x1), evaluate::<EdwardsConfig>(&key, x2));
            let delta = hash_to_curve::<EdwardsConfig>(x2).into_group() - hash_to_curve::<EdwardsConfig>(x1).into_group();
            // both points with x-coordinate y1: a x^2 + y^2 = 1 + d x^2 y^2
            let x2_ = y1.square();
            let yy = (Fq::ONE - EdwardsConfig::COEFF_A * x2_) / (Fq::ONE - EdwardsConfig::COEFF_D * x2_);
            let y = yy.sqrt().expect("y1 is an x-coordinate");
            for y in [y, -y] {
                let q1 = EdwardsAffine::new_unchecked(y1, y);
                assert_ne!((q1.into_group() + delta).into_affine().x, y2);
            }
        }
    }
}
