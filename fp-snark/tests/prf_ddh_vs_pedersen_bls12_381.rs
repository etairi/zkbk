//! Constraint cost of the pseudonym PRF in a circuit over BLS12-381's scalar field: the
//! Pedersen-CRH PRF of `fp_snark::prf` (`x(Ped(x || K))`) versus the DDH PRF of
//! `fp_snark::prf::ddh` (`x([K]·H(x))`), both over Jubjub.
//!
//! The statement is the one made in `show_vrc_bls12_381.rs`: `y = PRF(K, x)` for a secret key `K`
//! and a public output `y` (a field element), where `x` is either a constant of the circuit (the
//! 17-byte context of the show) or a public input (an issuer key's x-coordinate). Three variants:
//!
//! * `Pedersen, as used`: the `JZPRFInstanceVar` gadget, wired as in `show_vrc_bls12_381.rs`;
//! * `Pedersen, lean`: the same function through the Pedersen CRH gadget directly, with a
//!   field-element output (the cheapest way to evaluate it with arkworks);
//! * `DDH`: `prf::ddh::constraints`, with `H(x)` a constant or a public input.
//!
//! Also checks the scope of the linear attack on the Pedersen PRF.

use ark_bls12_381::Fr as ConstraintF;
use ark_crypto_primitives::crh::{CRHScheme, CRHSchemeGadget};
use ark_ec::{twisted_edwards::TECurveConfig, AffineRepr, CurveGroup};
use ark_ed_on_bls12_381::constraints::EdwardsVar;
use ark_ed_on_bls12_381::{EdwardsAffine, EdwardsConfig, Fq, Fr as JubjubScalar};
use ark_ff::{BigInteger, Field, PrimeField, UniformRand};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSystem, ConstraintSystemRef};
use rand_chacha::{rand_core::SeedableRng, ChaCha8Rng};

use fp_snark::prf::constraints::{JZPRFInstanceVar, JZPRFParamsVar};
use fp_snark::prf::ddh::{self, constraints::KeyVar};
use fp_snark::prf::{self, JZPRFInstance, JZPRFParams};
use fp_snark::utils;

type H = prf::config::ed_on_bls12_381::Hash;
type HG = prf::config::ed_on_bls12_381::HashGadget;

const CONTEXT: &[u8] = b"example.org/forum";
const KEY_BYTES: [u8; 32] = [42u8; 32];

/// Constraints spent on each part of proving `y = PRF(K, x)`.
#[derive(Default)]
struct Cost {
    /// allocating the secret key
    key: usize,
    /// making `x` available to the PRF (bytes, decomposition, or the on-curve check of `H(x)`)
    input: usize,
    /// the hash / scalar multiplication (for `Pedersen, as used`: also serialising the output
    /// point and matching it against the gadget's output bytes)
    evaluation: usize,
    /// binding the result to the public `y`
    output: usize,
    public_inputs: usize,
}

impl Cost {
    fn total(&self) -> usize {
        self.key + self.input + self.evaluation + self.output
    }
}

fn public_x() -> ConstraintF {
    ConstraintF::rand(&mut ChaCha8Rng::from_seed([12u8; 32]))
}

fn constant_bytes(bytes: &[u8]) -> Vec<UInt8<ConstraintF>> {
    bytes.iter().map(|b| UInt8::constant(*b)).collect()
}

fn enforce_bytes_eq(a: &[UInt8<ConstraintF>], b: &[UInt8<ConstraintF>]) {
    assert_eq!(a.len(), b.len());
    for (x, y) in a.iter().zip(b) {
        x.enforce_equal(y).unwrap();
    }
}

/// Runs `step` and returns the number of constraints it added.
fn measure<T>(cs: &ConstraintSystemRef<ConstraintF>, step: impl FnOnce() -> T) -> (T, usize) {
    let before = cs.num_constraints();
    let result = step();
    (result, cs.num_constraints() - before)
}

fn finish(cs: &ConstraintSystemRef<ConstraintF>, cost: Cost) -> Cost {
    assert!(cs.is_satisfied().unwrap(), "measured circuit must be satisfied");
    assert_eq!(cs.num_constraints(), cost.total(), "every constraint is attributed");
    Cost { public_inputs: cs.num_instance_variables() - 1, ..cost }
}

fn pedersen_as_used(x_is_public: bool) -> Cost {
    let params = JZPRFParams::<H>::trusted_setup(&mut ChaCha8Rng::from_seed([11u8; 32]));
    let x = public_x();
    let input = if x_is_public { x.into_bigint().to_bytes_le() } else { CONTEXT.to_vec() };
    let instance = JZPRFInstance::new(&params, &input, &KEY_BYTES);
    let y = ConstraintF::from_le_bytes_mod_order(&instance.evaluate()[..32]);

    let cs = ConstraintSystem::<ConstraintF>::new_ref();
    let y_var = FpVar::new_input(cs.clone(), || Ok(y)).unwrap();
    let x_var = x_is_public.then(|| FpVar::new_input(cs.clone(), || Ok(x)).unwrap());
    let params_var = JZPRFParamsVar::<H, HG, ConstraintF>::new_constant(cs.clone(), &params).unwrap();
    // allocates input, key and output (64 bytes: the uncompressed point) as witness bytes
    let (instance_var, alloc) = measure(&cs, || JZPRFInstanceVar::<ConstraintF>::new_witness(cs.clone(), || Ok(&instance)).unwrap());
    assert_eq!(alloc, 8 * (input.len() + 32 + 64), "8 boolean constraints per allocated byte");
    let (_, evaluation) = measure(&cs, || prf::constraints::generate_constraints(cs.clone(), &params_var, &instance_var));
    let (_, input_binding) = measure(&cs, || match &x_var {
        Some(x_var) => enforce_bytes_eq(&instance_var.input_var, &x_var.to_bytes_le().unwrap()),
        None => enforce_bytes_eq(&instance_var.input_var, &constant_bytes(CONTEXT)),
    });
    let (_, output_binding) = measure(&cs, || enforce_bytes_eq(&instance_var.output_var[..32], &y_var.to_bytes_le().unwrap()));
    finish(
        &cs,
        Cost {
            key: 8 * 32,
            input: 8 * input.len() + input_binding,
            evaluation,
            output: 8 * 64 + output_binding,
            public_inputs: 0,
        },
    )
}

fn pedersen_lean(x_is_public: bool) -> Cost {
    let params = JZPRFParams::<H>::trusted_setup(&mut ChaCha8Rng::from_seed([11u8; 32]));
    let x = public_x();
    let input = if x_is_public { x.into_bigint().to_bytes_le() } else { CONTEXT.to_vec() };
    let y = ConstraintF::from_le_bytes_mod_order(&JZPRFInstance::new(&params, &input, &KEY_BYTES).evaluate()[..32]);

    let cs = ConstraintSystem::<ConstraintF>::new_ref();
    let y_var = FpVar::new_input(cs.clone(), || Ok(y)).unwrap();
    let x_var = x_is_public.then(|| FpVar::new_input(cs.clone(), || Ok(x)).unwrap());
    let params_var = <HG as CRHSchemeGadget<H, ConstraintF>>::ParametersVar::new_constant(cs.clone(), &params.crh_params).unwrap();
    let (key_var, key) = measure(&cs, || {
        KEY_BYTES.iter().map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)).unwrap()).collect::<Vec<_>>()
    });
    let (mut message, input_cost) = measure(&cs, || match &x_var {
        Some(x_var) => x_var.to_bytes_le().unwrap(),
        None => constant_bytes(CONTEXT),
    });
    message.extend(key_var);
    let (point, evaluation) = measure(&cs, || HG::evaluate(&params_var, &message).unwrap());
    let (_, output) = measure(&cs, || point.x.enforce_equal(&y_var).unwrap());
    finish(&cs, Cost { key, input: input_cost, evaluation, output, public_inputs: 0 })
}

fn ddh(x_is_public: bool) -> Cost {
    let key = JubjubScalar::from_le_bytes_mod_order(&KEY_BYTES);
    let x = public_x();
    let input = if x_is_public { x.into_bigint().to_bytes_le() } else { CONTEXT.to_vec() };
    let base = ddh::hash_to_curve::<EdwardsConfig>(&input);
    let y = ddh::evaluate_with_base(&key, &base);

    let cs = ConstraintSystem::<ConstraintF>::new_ref();
    let y_var = FpVar::new_input(cs.clone(), || Ok(y)).unwrap();
    let (key_var, key_cost) = measure(&cs, || KeyVar::<JubjubScalar, ConstraintF>::new_witness(cs.clone(), || Ok(key)).unwrap());
    // public case: the verifier computes H(x) from x and supplies it; the circuit checks it is on
    // the curve
    let (base_var, input_cost) = measure(&cs, || x_is_public.then(|| EdwardsVar::new_input(cs.clone(), || Ok(base)).unwrap()));
    let (out, evaluation) = measure(&cs, || match &base_var {
        Some(base_var) => ddh::constraints::evaluate_input_base(&key_var, base_var).unwrap(),
        None => ddh::constraints::evaluate_constant_base(&key_var, &base).unwrap(),
    });
    let (_, output) = measure(&cs, || out.enforce_equal(&y_var).unwrap());
    finish(&cs, Cost { key: key_cost, input: input_cost, evaluation, output, public_inputs: 0 })
}

#[test]
fn report_prf_constraint_costs() {
    println!(
        "\n{:<44} {:>6} {:>7} {:>10} {:>7} {:>7} {:>7}",
        "y = PRF(K, x), over BLS12-381 Fr / Jubjub", "key", "input", "evaluation", "output", "TOTAL", "pub.in"
    );
    for (scenario, x_is_public) in [("x constant (17-byte context)", false), ("x public input (issuer key x-coord.)", true)] {
        println!("{}", scenario);
        for (name, cost) in [
            ("  Pedersen PRF, as used (JZPRFInstanceVar)", pedersen_as_used(x_is_public)),
            ("  Pedersen PRF, lean (CRH gadget, Fq output)", pedersen_lean(x_is_public)),
            ("  DDH PRF", ddh(x_is_public)),
        ] {
            println!(
                "{:<44} {:>6} {:>7} {:>10} {:>7} {:>7} {:>7}",
                name, cost.key, cost.input, cost.evaluation, cost.output, cost.total(), cost.public_inputs
            );
        }
    }
}

/// Predicts `PRF(K, x2)` from `(x1, PRF(K, x1))` for the Pedersen PRF using linearity,
/// `Ped(x2 || K) = Ped(x1 || K) + Ped(x2 || 0) - Ped(x1 || 0)`, which holds when `|x1| = |x2|`.
/// Returns both candidates (a point is fixed by its x-coordinate only up to two choices).
fn predict(params: &JZPRFParams<H>, x1: &[u8], p1: &[u8], x2: &[u8]) -> Vec<Vec<u8>> {
    let ped = |x: &[u8]| -> EdwardsAffine {
        let mut m = x.to_vec();
        m.extend_from_slice(&[0u8; 32]);
        <H as CRHScheme>::evaluate(&params.crh_params, m).unwrap()
    };
    let delta = ped(x2).into_group() - ped(x1).into_group();
    let x = Fq::from_le_bytes_mod_order(p1);
    let yy = (Fq::ONE - EdwardsConfig::COEFF_A * x.square()) / (Fq::ONE - EdwardsConfig::COEFF_D * x.square());
    let y = yy.sqrt().expect("p1 is an x-coordinate");
    [y, -y]
        .iter()
        .map(|&y| utils::serialize(&(EdwardsAffine::new_unchecked(x, y).into_group() + delta).into_affine().x))
        .collect()
}

/// Scope of `known_issue_pedersen_crh_prf_outputs_are_linkable`: one output with a known input
/// predicts the output on every other input of the same length; with a different length the key
/// bits meet different generators and this computation fails. (Its failure is not a security
/// argument for inputs of different lengths.)
#[test]
fn pedersen_prf_linear_prediction_needs_equal_length_inputs() {
    let params = JZPRFParams::<H>::trusted_setup(&mut ChaCha8Rng::from_seed([13u8; 32]));
    let out = |x: &[u8]| JZPRFInstance::new(&params, x, &KEY_BYTES).evaluate()[..32].to_vec();
    let equal_length: [(&[u8], &[u8]); 2] = [(&[1u8; 32], &[2u8; 32]), (b"example.org/forum", b"example.com/forum")];
    for (x1, x2) in equal_length {
        assert!(predict(&params, x1, &out(x1), x2).contains(&out(x2)), "predicted for equal lengths");
    }
    let (x1, x2): (&[u8], &[u8]) = (&[1u8; 32], b"example.org/forum");
    assert!(!predict(&params, x1, &out(x1), x2).contains(&out(x2)));
}
