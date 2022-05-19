/*
This file includes a prover and verifier for demonstrating knowledge of an opening of a Pedersen commitment.
The protocol is informally described in Appendix A.2, Proof of Opening of a Pedersen Commitment
*/

use ark_ec::{ProjectiveCurve, AffineCurve};
use ark_ff::{Fp256, PrimeField};
use ark_bls12_381::{G1Affine, FrParameters, Fr};
use ark_std::Zero;

use crate::tools::{hash_caulk_single, random_field};

// Structure of proof output by prove_pedersen
pub struct ProofPed {
    pub g1_r: G1Affine,
    pub t1: Fp256<FrParameters>,
    pub t2: Fp256<FrParameters>,
}

// prove knowledge of a and b such that  cm = g^a h^b
pub fn prove_pedersen(
    g1: &G1Affine,
    h1: &G1Affine,
    hash_input: &mut Fr,
    cm: &G1Affine,
    a: &Fp256<FrParameters>,
    b: &Fp256<FrParameters>,
) -> ProofPed {

    // R = g^s1 h^s2
    let s1: Fr = random_field::<Fr>();
    let s2: Fr = random_field::<Fr>();

    let g1_r =  (g1.mul( s1.into_repr() ) + h1.mul( s2.into_repr() )).into_affine();

    // c = Hash(cm, R)

    let c = hash_caulk_single::<Fr>( hash_input.clone(), Some(& [cm.clone(), g1_r].to_vec()), None, None );
    *hash_input = c.clone();

    let t1 = s1 + c * a;
    let t2 = s2 + c * b;

    let proof = ProofPed {
        g1_r: g1_r, t1: t1, t2: t2
    };

    return proof
}

// Verify that prover knows a and b such that  cm = g^a h^b
pub fn verify_pedersen(
    g1: &G1Affine,
    h1: &G1Affine,
    hash_input: &mut Fr,
    cm: &G1Affine,
    proof: &ProofPed,
) -> bool {

    // compute c = Hash(cm, R)


    let c = hash_caulk_single::<Fr>( hash_input.clone(), Some(& [cm.clone(), proof.g1_r.clone()].to_vec()), None, None );
    *hash_input = c.clone();

    // check that R  g^(-t1) h^(-t2) cm^(c) = 1
    let check = proof.g1_r.into_projective() + g1.mul( - proof.t1 )
    + h1.mul( - proof.t2 )  + cm.mul( c );

    return check.is_zero()
}
