/*
This file includes the setup algorithm for Caulk with single openings.
A full description of the setup is not formally given in the paper.
*/

use crate::PedersenParam;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, UniformRand};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Evaluations as EvaluationsOnDomain,
    GeneralEvaluationDomain, UVPolynomial,
};
use ark_poly_commit::kzg10::*;
use ark_std::{cfg_into_iter, rand::RngCore, One, Zero};
use ark_std::{end_timer, start_timer};
#[cfg(feature = "parallel")]
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use std::cmp::max;

// structure of public parameters
#[allow(non_snake_case)]
pub struct PublicParameters<E: PairingEngine> {
    pub poly_ck: Powers<'static, E>,
    pub poly_ck_d: E::G1Affine,
    pub lagrange_polynomials_Vn: Vec<DensePolynomial<E::Fr>>,
    pub verifier_pp: VerifierPublicParameters<E>,
}

// smaller set of public parameters used by verifier
#[allow(non_snake_case)]
pub struct VerifierPublicParameters<E: PairingEngine> {
    pub poly_ck_pen: E::G1Affine,
    pub lagrange_scalars_Vn: Vec<E::Fr>,
    pub poly_prod: DensePolynomial<E::Fr>,
    pub poly_vk: VerifierKey<E>,
    pub pedersen_param: PedersenParam<E::G1Affine>,
    pub g1_x: E::G1Affine,
    pub domain_H_size: usize,
    pub logN: usize,
    pub domain_Vn: GeneralEvaluationDomain<E::Fr>,
    pub powers_of_g2: Vec<E::G2Affine>,
}

// Reduces full srs down to smaller srs for smaller polynomials
// Copied from arkworks library (where same function is private)
fn trim<E: PairingEngine, P: UVPolynomial<E::Fr>>(
    srs: &UniversalParams<E>,
    mut supported_degree: usize,
) -> (Powers<'static, E>, VerifierKey<E>) {
    if supported_degree == 1 {
        supported_degree += 1;
    }
    let pp = srs.clone();
    let powers_of_g = pp.powers_of_g[..=supported_degree].to_vec();
    let powers_of_gamma_g = (0..=supported_degree)
        .map(|i| pp.powers_of_gamma_g[&i])
        .collect();

    let powers = Powers {
        powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
        powers_of_gamma_g: ark_std::borrow::Cow::Owned(powers_of_gamma_g),
    };
    let vk = VerifierKey {
        g: pp.powers_of_g[0],
        gamma_g: pp.powers_of_gamma_g[&0],
        h: pp.h,
        beta_h: pp.beta_h,
        prepared_h: pp.prepared_h.clone(),
        prepared_beta_h: pp.prepared_beta_h.clone(),
    };
    (powers, vk)
}

// setup algorithm for Caulk with single openings
// also includes a bunch of precomputation.
#[allow(non_snake_case)]
pub fn caulk_single_setup<E: PairingEngine, R: RngCore>(
    max_degree: usize,
    actual_degree: usize,
    rng: &mut R,
) -> PublicParameters<E> {
    let total_time = start_timer!(|| "total srs setup");

    // domain where vector commitment is defined
    let domain_H: GeneralEvaluationDomain<E::Fr> =
        GeneralEvaluationDomain::new(actual_degree).unwrap();

    let logN: usize = ((actual_degree as f32).log(2.0)).ceil() as usize;

    // smaller domain  for unity proofs with generator w
    let domain_Vn: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::new(6 + logN).unwrap();

    // Determining how big an srs we need.
    // Need an srs of size actual_degree to commit to the polynomial.
    // Need an srs of size 2 * domain_Vn_size + 3 to run the unity prover.
    // We take the larger of the two.
    let poly_ck_size = max(actual_degree, 2 * domain_Vn.size() + 3);

    // Setup algorithm. To be replaced by output of a universal setup before being production ready.
    let powers_time = start_timer!(|| "setup powers");
    let srs = KZG10::<E, DensePolynomial<E::Fr>>::setup(max(max_degree, poly_ck_size), true, rng)
        .unwrap();
    end_timer!(powers_time);

    // trim down to size.
    let (poly_ck, poly_vk) = trim::<E, DensePolynomial<E::Fr>>(&srs, poly_ck_size);

    //  g^x^d = maximum power given in setup
    let poly_ck_d = srs.powers_of_g[srs.powers_of_g.len() - 1];

    //  g^x^(d-1) = penultimate power given in setup
    let poly_ck_pen = srs.powers_of_g[srs.powers_of_g.len() - 2];

    // random pedersen commitment generatoor
    let ped_h: E::G1Affine = E::G1Projective::rand(rng).into_affine();

    // precomputation to speed up prover
    // lagrange_polynomials_Vn[i] = polynomial equal to 0 at w^j for j!= i and 1  at w^i
    let mut lagrange_polynomials_Vn: Vec<DensePolynomial<E::Fr>> = Vec::new();

    // precomputation to speed up verifier.
    // scalars such that lagrange_scalars_Vn[i] = prod_(j != i) (w^i - w^j)^(-1)
    let mut lagrange_scalars_Vn: Vec<E::Fr> = Vec::new();

    for i in 0..domain_Vn.size() {
        let evals: Vec<E::Fr> = cfg_into_iter!(0..domain_Vn.size())
            .map(|k| if k == i { E::Fr::one() } else { E::Fr::zero() })
            .collect();
        lagrange_polynomials_Vn
            .push(EvaluationsOnDomain::from_vec_and_domain(evals, domain_Vn).interpolate());
    }

    for i in 0..5 {
        let mut temp = E::Fr::one();
        for j in 0..domain_Vn.size() {
            if j != i {
                temp *= domain_Vn.element(i) - domain_Vn.element(j);
            }
        }
        lagrange_scalars_Vn.push(temp.inverse().unwrap());
    }

    // also want lagrange_scalars_Vn[logN + 5]
    let mut temp = E::Fr::one();
    for j in 0..domain_Vn.size() {
        if j != (logN + 5) {
            temp *= domain_Vn.element(logN + 5) - domain_Vn.element(j);
        }
    }
    lagrange_scalars_Vn.push(temp.inverse().unwrap());

    // poly_prod = (X - 1) (X - w) (X - w^2) (X - w^3) (X - w^4) (X - w^(5 + logN)) (X - w^(6 + logN))
    // for efficiency not including (X - w^i) for i  > 6 + logN
    // prover sets these evaluations to 0 anyway.
    let mut poly_prod = DensePolynomial::from_coefficients_slice(&[E::Fr::one()]);
    for i in 0..domain_Vn.size() {
        if i < 5 {
            poly_prod = &poly_prod
                * (&DensePolynomial::from_coefficients_slice(&[
                    -domain_Vn.element(i),
                    E::Fr::one(),
                ]))
        }
        if i == (5 + logN) {
            poly_prod = &poly_prod
                * (&DensePolynomial::from_coefficients_slice(&[
                    -domain_Vn.element(i),
                    E::Fr::one(),
                ]))
        }
        if i == (6 + logN) {
            poly_prod = &poly_prod
                * (&DensePolynomial::from_coefficients_slice(&[
                    -domain_Vn.element(i),
                    E::Fr::one(),
                ]))
        }
    }

    // ped_g  = g^x^0 from kzg commitment key.
    let ped_g = poly_ck.powers_of_g[0];

    // need some powers of g2
    // arkworks setup doesn't give these powers but the setup does use a fixed randomness to generate them.
    // so we can generate powers of g2 directly.
    let rng = &mut ark_std::test_rng();
    let beta = E::Fr::rand(rng);
    let mut temp = poly_vk.h;

    let mut powers_of_g2: Vec<E::G2Affine> = Vec::new();
    for _ in 0..3 {
        powers_of_g2.push(temp);
        temp = temp.mul(beta).into_affine();
    }

    let verifier_pp = VerifierPublicParameters {
        poly_ck_pen,
        lagrange_scalars_Vn,
        poly_prod,
        poly_vk,
        pedersen_param: PedersenParam { g: ped_g, h: ped_h },
        g1_x: srs.powers_of_g[1],
        domain_H_size: domain_H.size(),
        logN,
        domain_Vn,
        powers_of_g2,
    };

    let pp = PublicParameters {
        poly_ck,
        poly_ck_d,
        lagrange_polynomials_Vn,
        verifier_pp,
    };

    end_timer!(total_time);
    pp
}
