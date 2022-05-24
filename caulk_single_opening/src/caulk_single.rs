/*
This file includes the Caulk prover and verifier for single openings.
The protocol is described in Figure 1.
*/

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G2Affine};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, PrimeField};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_std::{One, Zero};

use crate::caulk_single_setup::{PublicParameters, VerifierPublicParameters};
use crate::caulk_single_unity::{
    caulk_single_unity_prove, caulk_single_unity_verify, CaulkProofUnity, PublicParametersUnity,
    VerifierPublicParametersUnity,
};
use crate::pedersen::{prove_pedersen, verify_pedersen, ProofPed};
use crate::tools::{hash_caulk_single, random_field};

// Structure of opening proofs output by prove.
#[allow(non_snake_case)]
pub struct CaulkProof {
    pub g2_z: G2Affine,
    pub g1_T: G1Affine,
    pub g2_S: G2Affine,
    pub pi_ped: ProofPed,
    pub pi_unity: CaulkProofUnity,
}

//Proves knowledge of (i, Q, z, r) such that
// 1) Q is a KZG opening proof that  g1_C opens to z at i
// 2) cm = g^z h^r

//Takes as input opening proof Q. Does not need knowledge of contents of C  = g1_C.
#[allow(non_snake_case)]
pub fn caulk_single_prove(
    pp: &PublicParameters,
    g1_C: &G1Affine,
    cm: &G1Affine,
    index: usize,
    g1_q: &G1Affine,
    v: &Fr,
    r: &Fr,
) -> CaulkProof {
    // provers blinders for zero-knowledge
    let a: Fr = random_field::<Fr>();
    let s: Fr = random_field::<Fr>();

    let domain_H: GeneralEvaluationDomain<Fr> =
        GeneralEvaluationDomain::new(pp.domain_H_size).unwrap();

    ///////////////////////////////
    // Compute [z]_2, [T]_1, and [S]_2
    ///////////////////////////////

    // [z]_2 = [ a (x - omega^i) ]_2
    let g2_z =
        (pp.poly_vk.beta_h.mul(a) + pp.poly_vk.h.mul(-a * domain_H.element(index))).into_affine();

    // [T]_1 = [ (  a^(-1) Q  + s h]_1 for Q precomputed KZG opening.
    let g1_T = (g1_q.mul(a.inverse().unwrap()) + pp.ped_h.mul(s)).into_affine();

    // [S]_2 = [ - r - s z ]_2
    let g2_S = (pp.poly_vk.h.mul((-*r).into_repr()) + g2_z.mul((-s).into_repr())).into_affine();

    ///////////////////////////////
    // Pedersen prove
    ///////////////////////////////

    // hash the instance and the proof elements to determine hash inputs for Pedersen prover
    let mut hash_input = hash_caulk_single::<Fr>(
        Fr::zero(),
        Some(&[g1_C.clone(), g1_T.clone()].to_vec()),
        Some(&[g2_z.clone(), g2_S.clone()].to_vec()),
        None,
    );

    // proof that cm = g^z h^rs
    let pi_ped = prove_pedersen(&pp.ped_g, &pp.ped_h, &mut hash_input, &cm, v, r);

    ///////////////////////////////
    // Unity prove
    ///////////////////////////////

    // hash the last round of the pedersen proof to determine hash input to the unity prover
    hash_input = hash_caulk_single::<Fr>(
        hash_input,
        None,
        None,
        Some(&[pi_ped.t1.clone(), pi_ped.t2.clone()].to_vec()),
    );

    // Setting up the public parameters for the unity prover
    let pp_unity = PublicParametersUnity {
        poly_ck: pp.poly_ck.clone(),
        gxd: pp.poly_ck_d.clone(),
        gxpen: pp.poly_ck_pen.clone(),
        lagrange_polynomials_Vn: pp.lagrange_polynomials_Vn.clone(),
        poly_prod: pp.poly_prod.clone(),
        logN: pp.logN.clone(),
        domain_Vn: pp.domain_Vn.clone(),
    };

    // proof that A = [a x - b ]_2 for a^n = b^n
    let pi_unity = caulk_single_unity_prove(
        &pp_unity,
        &mut hash_input,
        g2_z,
        a,
        a * domain_H.element(index),
    );

    let proof = CaulkProof {
        g2_z: g2_z,
        g1_T: g1_T,
        g2_S: g2_S,
        pi_ped: pi_ped,
        pi_unity: pi_unity,
    };

    proof
}

//Verifies that the prover knows of (i, Q, z, r) such that
// 1) Q is a KZG opening proof that  g1_C opens to z at i
// 2) cm = g^z h^r
#[allow(non_snake_case)]
pub fn caulk_single_verify(
    vk: &VerifierPublicParameters,
    g1_C: &G1Affine,
    cm: &G1Affine,
    proof: &CaulkProof,
) -> bool {
    ///////////////////////////////
    // Pairing check
    ///////////////////////////////

    // check that e( - C + cm, [1]_2) + e( [T]_1, [z]_2 ) + e( [h]_1, [S]_2 ) = 1
    let eq1: Vec<(
        ark_ec::bls12::G1Prepared<ark_bls12_381::Parameters>,
        ark_ec::bls12::G2Prepared<ark_bls12_381::Parameters>,
    )> = vec![
        (
            (g1_C.mul(-Fr::one()) + cm.into_projective())
                .into_affine()
                .into(),
            vk.poly_vk.prepared_h.clone(),
        ),
        ((proof.g1_T).into(), proof.g2_z.into()),
        (vk.ped_h.into(), proof.g2_S.into()),
    ];

    let check1 = Bls12_381::product_of_pairings(&eq1).is_one();

    ///////////////////////////////
    // Pedersen check
    ///////////////////////////////

    // hash the instance and the proof elements to determine hash inputs for Pedersen prover
    let mut hash_input = hash_caulk_single::<Fr>(
        Fr::zero(),
        Some(&[g1_C.clone(), proof.g1_T.clone()].to_vec()),
        Some(&[proof.g2_z.clone(), proof.g2_S.clone()].to_vec()),
        None,
    );

    // verify that cm = [v + r h]
    let check2 = verify_pedersen(&vk.ped_g, &vk.ped_h, &mut hash_input, &cm, &proof.pi_ped);

    ///////////////////////////////
    // Unity check
    ///////////////////////////////

    // hash the last round of the pedersen proof to determine hash input to the unity prover
    hash_input = hash_caulk_single::<Fr>(
        hash_input,
        None,
        None,
        Some(&[proof.pi_ped.t1.clone(), proof.pi_ped.t2.clone()].to_vec()),
    );

    let vk_unity = VerifierPublicParametersUnity {
        poly_vk: vk.poly_vk.clone(),
        gxpen: vk.poly_ck_pen.clone(),
        g1: vk.ped_g.clone(),
        g1_x: vk.g1_x.clone(),
        lagrange_scalars_Vn: vk.lagrange_scalars_Vn.clone(),
        poly_prod: vk.poly_prod.clone(),
        logN: vk.logN.clone(),
        domain_Vn: vk.domain_Vn.clone(),
        powers_of_g2: vk.powers_of_g2.clone(),
    };

    // Verify that g2_z = [ ax - b ]_1 for (a/b)**N = 1
    let check3 =
        caulk_single_unity_verify(&vk_unity, &mut hash_input, &proof.g2_z, &proof.pi_unity);

    return check1 && check2 && check3;
}
