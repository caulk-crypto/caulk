// This file includes the Caulk prover and verifier for single openings.
// The protocol is described in Figure 1.

pub mod setup;
pub mod unity;

use crate::{
    pedersen::{PedersenCommit, PedersenProof},
    CaulkTranscript,
};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, PrimeField};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_std::{rand::RngCore, One, UniformRand, Zero};
use setup::{PublicParameters, VerifierPublicParameters};
use std::ops::Neg;
use unity::{
    caulk_single_unity_prove, caulk_single_unity_verify, CaulkProofUnity, PublicParametersUnity,
    VerifierPublicParametersUnity,
};

// Structure of opening proofs output by prove.
#[allow(non_snake_case)]
pub struct CaulkProof<E: PairingEngine> {
    pub g2_z: E::G2Affine,
    pub g1_T: E::G1Affine,
    pub g2_S: E::G2Affine,
    pub pi_ped: PedersenProof<E::G1Affine>,
    pub pi_unity: CaulkProofUnity<E>,
}

// Proves knowledge of (i, Q, z, r) such that
// 1) Q is a KZG opening proof that  g1_C opens to z at i
// 2) cm = g^z h^r

// Takes as input opening proof Q. Does not need knowledge of contents of C  =
// g1_C.
#[allow(non_snake_case)]
#[allow(clippy::too_many_arguments)]
pub fn caulk_single_prove<E: PairingEngine, R: RngCore>(
    pp: &PublicParameters<E>,
    transcript: &mut CaulkTranscript<E::Fr>,
    g1_C: &E::G1Affine,
    cm: &E::G1Affine,
    index: usize,
    g1_q: &E::G1Affine,
    v: &E::Fr,
    r: &E::Fr,
    rng: &mut R,
) -> CaulkProof<E> {
    // provers blinders for zero-knowledge
    let a = E::Fr::rand(rng);
    let s = E::Fr::rand(rng);

    let domain_H: GeneralEvaluationDomain<E::Fr> =
        GeneralEvaluationDomain::new(pp.verifier_pp.domain_H_size).unwrap();

    ///////////////////////////////
    // Compute [z]_2, [T]_1, and [S]_2
    ///////////////////////////////

    // [z]_2 = [ a (x - omega^i) ]_2
    let g2_z = (pp.verifier_pp.poly_vk.beta_h.mul(a)
        + pp.verifier_pp.poly_vk.h.mul(-a * domain_H.element(index)))
    .into_affine();

    // [T]_1 = [ (  a^(-1) Q  + s h]_1 for Q precomputed KZG opening.
    let g1_T =
        (g1_q.mul(a.inverse().unwrap()) + pp.verifier_pp.pedersen_param.h.mul(s)).into_affine();

    // [S]_2 = [ - r - s z ]_2
    let g2_S = (pp.verifier_pp.poly_vk.h.mul((-*r).into_repr()) + g2_z.mul((-s).into_repr()))
        .into_affine();

    ///////////////////////////////
    // Pedersen prove
    ///////////////////////////////

    // hash the instance and the proof elements to determine hash inputs for
    // Pedersen prover

    transcript.append_element(b"0", &E::Fr::zero());
    transcript.append_element(b"C", g1_C);
    transcript.append_element(b"T", &g1_T);
    transcript.append_element(b"z", &g2_z);
    transcript.append_element(b"S", &g2_S);

    // proof that cm = g^z h^rs
    let pi_ped = PedersenCommit::prove(&pp.verifier_pp.pedersen_param, transcript, cm, v, r, rng);

    ///////////////////////////////
    // Unity prove
    ///////////////////////////////

    // hash the last round of the pedersen proof to determine hash input to the
    // unity prover
    transcript.append_element(b"t1", &pi_ped.t1);
    transcript.append_element(b"t2", &pi_ped.t2);

    // Setting up the public parameters for the unity prover
    let pp_unity = PublicParametersUnity::from(pp);

    // proof that A = [a x - b ]_2 for a^n = b^n
    let pi_unity = caulk_single_unity_prove(
        &pp_unity,
        transcript,
        &g2_z,
        &a,
        &(a * domain_H.element(index)),
        rng,
    );

    CaulkProof {
        g2_z,
        g1_T,
        g2_S,
        pi_ped,
        pi_unity,
    }
}

// Verifies that the prover knows of (i, Q, z, r) such that
// 1) Q is a KZG opening proof that  g1_C opens to z at i
// 2) cm = g^z h^r
#[allow(non_snake_case)]
pub fn caulk_single_verify<E: PairingEngine>(
    vk: &VerifierPublicParameters<E>,
    transcript: &mut CaulkTranscript<E::Fr>,
    g1_C: &E::G1Affine,
    cm: &E::G1Affine,
    proof: &CaulkProof<E>,
) -> bool {
    ///////////////////////////////
    // Pairing check
    ///////////////////////////////

    // check that e( - C + cm, [1]_2) + e( [T]_1, [z]_2 ) + e( [h]_1, [S]_2 ) = 1
    let eq1: Vec<(E::G1Prepared, E::G2Prepared)> = vec![
        ((g1_C.neg() + *cm).into(), vk.poly_vk.prepared_h.clone()),
        ((proof.g1_T).into(), proof.g2_z.into()),
        (vk.pedersen_param.h.into(), proof.g2_S.into()),
    ];

    let check1 = E::product_of_pairings(&eq1).is_one();

    ///////////////////////////////
    // Pedersen check
    ///////////////////////////////

    // hash the instance and the proof elements to determine hash inputs for
    // Pedersen prover
    transcript.append_element(b"0", &E::Fr::zero());
    transcript.append_element(b"C", g1_C);
    transcript.append_element(b"T", &proof.g1_T);
    transcript.append_element(b"z", &proof.g2_z);
    transcript.append_element(b"S", &proof.g2_S);

    // verify that cm = [v + r h]
    let check2 = PedersenCommit::verify(&vk.pedersen_param, transcript, cm, &proof.pi_ped);

    ///////////////////////////////
    // Unity check
    ///////////////////////////////

    // hash the last round of the pedersen proof to determine hash input to the
    // unity prover
    transcript.append_element(b"t1", &proof.pi_ped.t1);
    transcript.append_element(b"t2", &proof.pi_ped.t2);

    let vk_unity = VerifierPublicParametersUnity::from(vk);

    // Verify that g2_z = [ ax - b ]_1 for (a/b)**N = 1
    let check3 = caulk_single_unity_verify(&vk_unity, transcript, &proof.g2_z, &proof.pi_unity);

    check1 && check2 && check3
}