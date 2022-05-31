/*
This file includes a prover and verifier for demonstrating knowledge of an opening of a Pedersen commitment.
The protocol is informally described in Appendix A.2, Proof of Opening of a Pedersen Commitment
*/

use crate::CaulkTranscript;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::PrimeField;
use ark_std::Zero;
use ark_std::{rand::RngCore, UniformRand};

// Parameters for perdersen commitment
pub struct PedersonParam<C: AffineCurve> {
    pub g: C,
    pub h: C,
}

// Structure of proof output by prove_pedersen
pub struct ProofPed<E: PairingEngine> {
    pub g1_r: E::G1Affine,
    pub t1: E::Fr,
    pub t2: E::Fr,
}

// prove knowledge of a and b such that  cm = g^a h^b
pub fn prove_pedersen<E: PairingEngine, R: RngCore>(
    param: &PedersonParam<E::G1Affine>,
    transcript: &mut CaulkTranscript<E::Fr>,
    cm: &E::G1Affine,
    a: &E::Fr,
    b: &E::Fr,
    rng: &mut R,
) -> ProofPed<E> {
    // R = g^s1 h^s2
    let s1 = E::Fr::rand(rng);
    let s2 = E::Fr::rand(rng);

    let g1_r = (param.g.mul(s1) + param.h.mul(s2.into_repr())).into_affine();

    // c = Hash(cm, R)
    transcript.append_element(b"commitment", cm);
    transcript.append_element(b"commitment", &g1_r);
    let c = transcript.get_and_append_challenge(b"get c");

    let t1 = s1 + c * a;
    let t2 = s2 + c * b;

    ProofPed { g1_r, t1, t2 }
}

// Verify that prover knows a and b such that  cm = g^a h^b
pub fn verify_pedersen<E: PairingEngine>(
    param: &PedersonParam<E::G1Affine>,
    transcript: &mut CaulkTranscript<E::Fr>,
    cm: &E::G1Affine,
    proof: &ProofPed<E>,
) -> bool {
    // compute c = Hash(cm, R)
    transcript.append_element(b"commitment", cm);
    transcript.append_element(b"commitment", &proof.g1_r);
    let c = transcript.get_and_append_challenge(b"get c");

    // check that R  g^(-t1) h^(-t2) cm^(c) = 1
    let check =
        proof.g1_r.into_projective() + param.g.mul(-proof.t1) + param.h.mul(-proof.t2) + cm.mul(c);

    check.is_zero()
}
