// This file includes a prover and verifier for demonstrating knowledge of an
// opening of a Pedersen commitment. The protocol is informally described in
// Appendix A.2, Proof of Opening of a Pedersen Commitment

use crate::CaulkTranscript;
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::PrimeField;
use ark_std::{rand::RngCore, UniformRand};
use std::marker::PhantomData;

// Parameters for pedersen commitment
pub struct PedersenParam<C: AffineCurve> {
    pub g: C,
    pub h: C,
}

// Structure of proof output by prove_pedersen
pub struct PedersenProof<C: AffineCurve> {
    pub g1_r: C,
    pub t1: C::ScalarField,
    pub t2: C::ScalarField,
}

pub struct PedersenCommit<C: AffineCurve> {
    phantom: PhantomData<C>,
}

impl<C: AffineCurve> PedersenCommit<C> {
    // prove knowledge of a and b such that  cm = g^a h^b
    pub fn prove<R: RngCore>(
        param: &PedersenParam<C>,
        transcript: &mut CaulkTranscript<C::ScalarField>,
        cm: &C,
        a: &C::ScalarField,
        b: &C::ScalarField,
        rng: &mut R,
    ) -> PedersenProof<C> {
        // R = g^s1 h^s2
        let s1 = C::ScalarField::rand(rng);
        let s2 = C::ScalarField::rand(rng);

        let g1_r = (param.g.mul(s1) + param.h.mul(s2.into_repr())).into_affine();

        // c = Hash(cm, R)
        transcript.append_element(b"commitment", cm);
        transcript.append_element(b"commitment", &g1_r);
        let c = transcript.get_and_append_challenge(b"get c");

        let t1 = s1 + c * a;
        let t2 = s2 + c * b;

        PedersenProof { g1_r, t1, t2 }
    }

    // Verify that prover knows a and b such that  cm = g^a h^b
    pub fn verify(
        param: &PedersenParam<C>,
        transcript: &mut CaulkTranscript<C::ScalarField>,
        cm: &C,
        proof: &PedersenProof<C>,
    ) -> bool {
        // compute c = Hash(cm, R)
        transcript.append_element(b"commitment", cm);
        transcript.append_element(b"commitment", &proof.g1_r);
        let c = transcript.get_and_append_challenge(b"get c");

        // check that R  g^(-t1) h^(-t2) cm^(c) = 1
        proof.g1_r.into_projective() + cm.mul(c) == param.g.mul(proof.t1) + param.h.mul(proof.t2)
    }
}
