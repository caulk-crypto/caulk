/*
This file includes a prover and verifier for demonstrating knowledge of an opening of a Pedersen commitment.
The protocol is informally described in Appendix A.2, Proof of Opening of a Pedersen Commitment
*/

use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::PrimeField;
use ark_std::Zero;
use ark_std::{rand::RngCore, UniformRand};

use crate::tools::hash_caulk_single;

// Structure of proof output by prove_pedersen
pub struct ProofPed<E: PairingEngine> {
    pub g1_r: E::G1Affine,
    pub t1: E::Fr,
    pub t2: E::Fr,
}

// prove knowledge of a and b such that  cm = g^a h^b
pub fn prove_pedersen<E: PairingEngine, R: RngCore>(
    g1: &E::G1Affine,
    h1: &E::G1Affine,
    hash_input: &mut E::Fr,
    cm: &E::G1Affine,
    a: &E::Fr,
    b: &E::Fr,
    rng: &mut R,
) -> ProofPed<E> {
    // R = g^s1 h^s2
    let s1 = E::Fr::rand(rng);
    let s2 = E::Fr::rand(rng);

    let g1_r = (g1.mul(s1.into_repr()) + h1.mul(s2.into_repr())).into_affine();

    // c = Hash(cm, R)
    let c = hash_caulk_single::<E>(hash_input, Some(&[*cm, g1_r]), None, None);
    *hash_input = c;

    let t1 = s1 + c * a;
    let t2 = s2 + c * b;

    ProofPed { g1_r, t1, t2 }
}

// Verify that prover knows a and b such that  cm = g^a h^b
pub fn verify_pedersen<E: PairingEngine>(
    g1: &E::G1Affine,
    h1: &E::G1Affine,
    hash_input: &mut E::Fr,
    cm: &E::G1Affine,
    proof: &ProofPed<E>,
) -> bool {
    // compute c = Hash(cm, R)

    let c = hash_caulk_single::<E>(hash_input, Some(&[*cm, proof.g1_r]), None, None);
    *hash_input = c;

    // check that R  g^(-t1) h^(-t2) cm^(c) = 1
    let check = proof.g1_r.into_projective() + g1.mul(-proof.t1) + h1.mul(-proof.t2) + cm.mul(c);

    check.is_zero()
}
