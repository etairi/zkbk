// SPDX-License-Identifier: Apache-2.0

//! Pedersen-CRH configuration over Jubjub (`ark-ed-on-bls12-381`), whose base field is the
//! scalar field of BLS12-381. This is the configuration to use when the outer SNARK is
//! `Groth16::<Bls12_381>`.

use ark_crypto_primitives::crh::pedersen;

/// 4-bit windows, 256 windows: hashes inputs of up to 1024 bits (128 bytes).
#[derive(Clone)]
pub struct Window4x256;
impl pedersen::Window for Window4x256 {
    const WINDOW_SIZE: usize = 4;
    const NUM_WINDOWS: usize = 256;
}

pub type Hash = pedersen::CRH<
    ark_ed_on_bls12_381::EdwardsProjective, Window4x256
>;

pub type HashGadget = pedersen::constraints::CRHGadget<
    ark_ed_on_bls12_381::EdwardsProjective,
    ark_ed_on_bls12_381::constraints::EdwardsVar,
    Window4x256
>;
