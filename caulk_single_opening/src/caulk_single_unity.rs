/*
This file includes the Caulk's unity prover and verifier for single openings.
The protocol is described in Figure 2.
*/

use crate::tools::{hash_caulk_single, kzg_open_g1, kzg_verify_g1};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::Field;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Evaluations as EvaluationsOnDomain,
    GeneralEvaluationDomain, Polynomial, UVPolynomial,
};
use ark_poly_commit::kzg10::*;
use ark_std::{cfg_into_iter, One, Zero};
use ark_std::{rand::RngCore, UniformRand};

// prover public parameters structure for caulk_single_unity_prove
#[allow(non_snake_case)]
pub struct PublicParametersUnity<E: PairingEngine> {
    pub poly_ck: Powers<'static, E>,
    pub gxd: E::G1Affine,
    pub gxpen: E::G1Affine,
    pub lagrange_polynomials_Vn: Vec<DensePolynomial<E::Fr>>,
    pub poly_prod: DensePolynomial<E::Fr>,
    pub logN: usize,
    pub domain_Vn: GeneralEvaluationDomain<E::Fr>,
}

// verifier parameters structure for caulk_single_unity_verify
#[allow(non_snake_case)]
pub struct VerifierPublicParametersUnity<E: PairingEngine> {
    pub poly_vk: VerifierKey<E>,
    pub gxpen: E::G1Affine,
    pub g1: E::G1Affine,
    pub g1_x: E::G1Affine,
    pub lagrange_scalars_Vn: Vec<E::Fr>,
    pub poly_prod: DensePolynomial<E::Fr>,
    pub logN: usize,
    pub domain_Vn: GeneralEvaluationDomain<E::Fr>,
    pub powers_of_g2: Vec<E::G2Affine>,
}

// output structure of caulk_single_unity_prove
#[allow(non_snake_case)]
pub struct CaulkProofUnity<E: PairingEngine> {
    pub g1_F: E::G1Affine,
    pub g1_H: E::G1Affine,
    pub v1: E::Fr,
    pub v2: E::Fr,
    pub pi1: E::G1Affine,
    pub pi2: E::G1Affine,
}

// Prove knowledge of a, b such that g2_z = [ax - b]_2 and a^n = b^n
#[allow(non_snake_case)]
pub fn caulk_single_unity_prove<E: PairingEngine, R: RngCore>(
    pp: &PublicParametersUnity<E>,
    hash_input: &mut E::Fr,
    g2_z: &E::G2Affine,
    a: &E::Fr,
    b: &E::Fr,
    rng: &mut R,
) -> CaulkProofUnity<E> {
    // a_poly = a X - b
    let a_poly = DensePolynomial::from_coefficients_slice(&[-*b, *a]);

    // provers blinders for zero-knowledge
    let r0 = E::Fr::rand(rng);
    let r1 = E::Fr::rand(rng);
    let r2 = E::Fr::rand(rng);
    let r3 = E::Fr::rand(rng);

    let r_poly = DensePolynomial::from_coefficients_slice(&[r1, r2, r3]);

    // roots of unity in domain of size m = log_2(n) + 6
    let sigma = pp.domain_Vn.element(1);

    // X^n - 1
    let z: DensePolynomial<E::Fr> = pp.domain_Vn.vanishing_polynomial().into();

    // computing [ (a/b), (a/b)^2, (a/b)^4, ..., (a/b)^(2^logN) = (a/b)^n ]
    let mut a_div_b = *a * ((*b).inverse()).unwrap();
    let mut vec_a_div_b: Vec<E::Fr> = Vec::new();
    for _ in 0..(pp.logN + 1) {
        vec_a_div_b.push(a_div_b);
        a_div_b = a_div_b * a_div_b;
    }

    ////////////////////////////
    // computing f(X).  First compute in domain.
    ////////////////////////////
    let f_evals: Vec<E::Fr> = cfg_into_iter!(0..pp.domain_Vn.size())
        .map(|k| {
            if k == 0 {
                *a - *b
            } else if k == 1 {
                *a * sigma - *b
            } else if k == 2 {
                *a
            } else if k == 3 {
                *b
            } else if k > 3 && k < (pp.logN + 5) {
                vec_a_div_b[k - 4]
            } else if k == pp.logN + 5 {
                r0
            } else {
                E::Fr::zero()
            }
        })
        .collect();

    let f_poly = &EvaluationsOnDomain::from_vec_and_domain(f_evals, pp.domain_Vn).interpolate()
        + &(&r_poly * &z);

    // computing f( sigma^(-1) X) and f( sigma^(-2) X)
    let mut f_poly_shift_1 = f_poly.clone();
    let mut f_poly_shift_2 = f_poly.clone();
    let mut shift_1 = E::Fr::one();
    let mut shift_2 = E::Fr::one();

    for i in 0..f_poly.len() {
        f_poly_shift_1[i]  *= shift_1;
        f_poly_shift_2[i]  *= shift_2;
        shift_1  *= pp.domain_Vn.element(pp.domain_Vn.size() - 1);
        shift_2  *= pp.domain_Vn.element(pp.domain_Vn.size() - 2);
    }

    ////////////////////////////
    // computing h(X).  First compute p(X) then divide.
    ////////////////////////////

    // p(X) = p(X) + (f(X) - a(X)) (rho_1(X) + rho_2(X))
    let mut p_poly =
        &(&f_poly - &a_poly) * &(&pp.lagrange_polynomials_Vn[0] + &pp.lagrange_polynomials_Vn[1]);

    // p(X) = p(X) + ( (1 - sigma) f(X) -  f(sigma^(-2)X) + f(sigma^(-1) X) ) rho_3(X)
    p_poly = &p_poly
        + &(&(&(&(&DensePolynomial::from_coefficients_slice(&[(E::Fr::one() - sigma)])
            * &f_poly)
            - &f_poly_shift_2)
            + &f_poly_shift_1)
            * &pp.lagrange_polynomials_Vn[2]);

    // p(X) = p(X) + ( -sigma f(sigma^(-1) X) +  f(sigma^(-2)X) + f(X)   ) rho_4(X)
    p_poly = &p_poly
        + &(&(&(&(&DensePolynomial::from_coefficients_slice(&[-sigma]) * &f_poly_shift_1)
            + &f_poly_shift_2)
            + &f_poly)
            * &pp.lagrange_polynomials_Vn[3]);

    // p(X) = p(X) + ( f(X) f(sigma^(-1) X) -  f(sigma^(-2)X)    ) rho_5(X)
    p_poly = &p_poly
        + &(&(&(&f_poly * &f_poly_shift_1) - &f_poly_shift_2) * &pp.lagrange_polynomials_Vn[4]);

    // p(X) = p(X) + ( f(X)  - f(sigma^(-1) X) *  f(sigma^(-1)X)    ) prod_(i not in [5, .. , logN + 4]) (X - sigma^i)
    p_poly = &p_poly + &(&(&f_poly - &(&f_poly_shift_1 * &f_poly_shift_1)) * &pp.poly_prod);

    // p(X) = p(X) + (  f(sigma^(-1) X) -  1    ) rho_(logN + 6)(X)
    p_poly = &p_poly
        + &(&(&f_poly_shift_1 - &(DensePolynomial::from_coefficients_slice(&[E::Fr::one()])))
            * &pp.lagrange_polynomials_Vn[pp.logN + 5]);

    // Compute h_hat_poly = p(X) / z_Vn(X) and abort if division is not perfect
    let (h_hat_poly, remainder) = p_poly.divide_by_vanishing_poly(pp.domain_Vn).unwrap();
    assert!(remainder.is_zero(), "z_Vn(X) does not divide p(X)");

    ////////////////////////////
    // Commit to f(X) and h(X)
    ////////////////////////////
    let (g1_F, _) = KZG10::commit(&pp.poly_ck, &f_poly, None, None).unwrap();
    let g1_F: E::G1Affine = g1_F.0;
    let (h_hat_com, _) = KZG10::commit(&pp.poly_ck, &h_hat_poly, None, None).unwrap();

    // g1_H is a commitment to h_hat_poly + X^(d-1) z(X)
    let g1_H = h_hat_com.0 + (pp.gxd.mul(-*a) + pp.gxpen.mul(*b)).into_affine();

    ////////////////////////////
    // alpha = Hash([z]_2, [F]_1, [H]_1)
    ////////////////////////////

    let alpha = hash_caulk_single::<E>(hash_input, Some(&[g1_F, g1_H]), Some(&[*g2_z]), None);

    *hash_input = alpha;

    ////////////////////////////
    // v1 = f(sigma^(-1) alpha) and v2 = f(w^(-2) alpha)
    ////////////////////////////
    let alpha1 = alpha * pp.domain_Vn.element(pp.domain_Vn.size() - 1);
    let alpha2 = alpha * pp.domain_Vn.element(pp.domain_Vn.size() - 2);
    let v1 = f_poly.evaluate(&alpha1);
    let v2 = f_poly.evaluate(&alpha2);

    ////////////////////////////
    // Compute polynomial p_alpha(X) that opens at alpha to 0
    ////////////////////////////

    // restating some field elements as polynomials so that can multiply polynomials
    let pz_alpha = DensePolynomial::from_coefficients_slice(&[-z.evaluate(&alpha)]);
    let pv1 = DensePolynomial::from_coefficients_slice(&[v1]);
    let pv2 = DensePolynomial::from_coefficients_slice(&[v2]);
    let prho1_add_2 = DensePolynomial::from_coefficients_slice(&[pp.lagrange_polynomials_Vn[0]
        .evaluate(&alpha)
        + pp.lagrange_polynomials_Vn[1].evaluate(&alpha)]);
    let prho3 =
        DensePolynomial::from_coefficients_slice(&[pp.lagrange_polynomials_Vn[2].evaluate(&alpha)]);
    let prho4 =
        DensePolynomial::from_coefficients_slice(&[pp.lagrange_polynomials_Vn[3].evaluate(&alpha)]);
    let prho5 =
        DensePolynomial::from_coefficients_slice(&[pp.lagrange_polynomials_Vn[4].evaluate(&alpha)]);
    let ppolyprod = DensePolynomial::from_coefficients_slice(&[pp.poly_prod.evaluate(&alpha)]);
    let prhologN6 = DensePolynomial::from_coefficients_slice(&[pp.lagrange_polynomials_Vn
        [pp.logN + 5]
        .evaluate(&alpha)]);

    // p_alpha(X) = - zVn(alpha) h(X)
    let mut p_alpha_poly = &pz_alpha * &h_hat_poly;

    // p_alpha(X) = p_alpha(X) + ( f(X) - z(X) )(rho1(alpha) + rho2(alpha))
    p_alpha_poly = &p_alpha_poly + &(&(&f_poly - &a_poly) * &prho1_add_2);

    // p_alpha(X) = p_alpha(X) + ( (1-sigma) f(X) - v2 + v1 ) rho3(alpha)
    p_alpha_poly = &p_alpha_poly
        + &(&(&(&(&DensePolynomial::from_coefficients_slice(&[(E::Fr::one() - sigma)])
            * &f_poly)
            - &pv2)
            + &pv1)
            * &prho3);

    // p_alpha(X) = p_alpha(X) + ( f(X) + v2 - sigma v1 ) rho4(alpha)
    p_alpha_poly = &p_alpha_poly
        + &(&(&(&(&DensePolynomial::from_coefficients_slice(&[-sigma]) * &pv1) + &pv2) + &f_poly)
            * &prho4);

    // p_alpha(X) = p_alpha(X) + ( v1 f(X) - v2  ) rho5(alpha)
    p_alpha_poly = &p_alpha_poly + &(&(&(&f_poly * &pv1) - &pv2) * &prho5);

    // p_alpha(X) = p_alpha(X) + (  f(X) - v1^2  ) prod_(i not in [5, .. , logN + 4]) (alpha - sigma^i)
    p_alpha_poly = &p_alpha_poly + &(&(&f_poly - &(&pv1 * &pv1)) * &ppolyprod);

    /*
    Differing slightly from paper
    Paper uses p_alpha(X) = p_alpha(X) + ( v1 - 1 ) rho_(n)(alpha) assuming that logN  = n - 6
    We use p_alpha(X) = p_alpha(X) + ( v1 - 1 ) rho_(logN + 6)(alpha) to allow for any value of logN
     */
    p_alpha_poly = &p_alpha_poly
        + &(&(&pv1 - &(DensePolynomial::from_coefficients_slice(&[E::Fr::one()]))) * &prhologN6);

    ////////////////////////////
    // Compute opening proofs
    ////////////////////////////

    // KZG.Open(srs_KZG, f(X), deg = bot, (alpha1, alpha2))
    let (_evals1, pi1) = kzg_open_g1(&pp.poly_ck, &f_poly, None, [alpha1, alpha2].as_ref());

    // KZG.Open(srs_KZG, p_alpha(X), deg = bot, alpha)
    let (evals2, pi2) = kzg_open_g1(&pp.poly_ck, &p_alpha_poly, None, &[alpha]);

    // abort if p_alpha( alpha) != 0
    assert!(
        evals2[0] == E::Fr::zero(),
        "p_alpha(X) does not equal 0 at alpha"
    );

    CaulkProofUnity {
        g1_F,
        g1_H,
        v1,
        v2,
        pi1,
        pi2,
    }
}

// Verify that the prover knows a, b such that g2_z = g2^(a x - b) and a^n = b^n
#[allow(non_snake_case)]
pub fn caulk_single_unity_verify<E: PairingEngine>(
    vk: &VerifierPublicParametersUnity<E>,
    hash_input: &mut E::Fr,
    g2_z: &E::G2Affine,
    proof: &CaulkProofUnity<E>,
) -> bool {
    // g2_z must not be the identity
    assert!(!g2_z.is_zero(), "g2_z is the identity");

    // roots of unity in domain of size m = log1_2(n) + 6
    let sigma = vk.domain_Vn.element(1);
    let v1 = proof.v1;
    let v2 = proof.v2;

    ////////////////////////////
    // alpha = Hash(A, F, H)
    ////////////////////////////

    let alpha = hash_caulk_single::<E>(
        hash_input,
        Some(&[proof.g1_F, proof.g1_H]),
        Some(&[*g2_z]),
        None,
    );
    *hash_input = alpha;

    // alpha1 = sigma^(-1) alpha and alpha2 = sigma^(-2) alpha
    let alpha1: E::Fr = alpha * vk.domain_Vn.element(vk.domain_Vn.size() - 1);
    let alpha2: E::Fr = alpha * vk.domain_Vn.element(vk.domain_Vn.size() - 2);

    ///////////////////////////////
    // Compute P = commitment to p_alpha(X)
    ///////////////////////////////

    // Useful field elements.

    // zalpha =  z(alpha) = alpha^n - 1,
    let zalpha = vk.domain_Vn.vanishing_polynomial().evaluate(&alpha);

    // rhoi = L_i(alpha) = ls_i * [(X^m - 1) / (alpha - w^i) ]
    // where ls_i = lagrange_scalars_Vn[i] = prod_{j neq i} (w_i - w_j)^(-1)
    let rho0 =
        zalpha * (alpha - vk.domain_Vn.element(0)).inverse().unwrap() * vk.lagrange_scalars_Vn[0];
    let rho1 =
        zalpha * (alpha - vk.domain_Vn.element(1)).inverse().unwrap() * vk.lagrange_scalars_Vn[1];
    let rho2 =
        zalpha * (alpha - vk.domain_Vn.element(2)).inverse().unwrap() * vk.lagrange_scalars_Vn[2];
    let rho3 =
        zalpha * (alpha - vk.domain_Vn.element(3)).inverse().unwrap() * vk.lagrange_scalars_Vn[3];
    let rho4 =
        zalpha * (alpha - vk.domain_Vn.element(4)).inverse().unwrap() * vk.lagrange_scalars_Vn[4];
    let rhologN5 = zalpha
        * (alpha - vk.domain_Vn.element(vk.logN + 5))
            .inverse()
            .unwrap()
        * vk.lagrange_scalars_Vn[5];

    // pprod = prod_(i not in  [5,..,logN+4]) (alpha - w^i)
    let pprod = vk.poly_prod.evaluate(&alpha);

    // P = H^(-z(alpha)) * F^(rho0(alpha) + L_1(alpha) + (1 - w)L_2(alpha) + L_3(alpha) + v1 L_4(alpha)
    //                      + prod_(i not in  [5,..,logN+4]) (alpha - w^i))
    //                 * g^( (v1 -v2)L_2(alpha) + (v2 - w v1)L_3(alpha) - v2 L_4(alpha) + (v1 - 1)L_(logN+5)(alpha)
    //                      - v1^2 * prod_(i not in  [5,..,logN+4]) (alpha - w^i) )
    let g1_p = proof.g1_H.mul(-zalpha)
        + proof
            .g1_F
            .mul(rho0 + rho1 + (E::Fr::one() - sigma) * rho2 + rho3 + v1 * rho4 + pprod)
        + vk.g1.mul(
            (v1 - v2) * rho2 + (v2 - sigma * v1) * rho3 - v2 * rho4
                + (v1 - E::Fr::one()) * rhologN5
                - v1 * v1 * pprod,
        );

    ///////////////////////////////
    // Pairing checks
    ///////////////////////////////

    ///////////////////////////////
    // KZG opening check
    ///////////////////////////////

    let check1 = kzg_verify_g1::<E>(
        [vk.g1, vk.g1_x].as_ref(),
        &vk.powers_of_g2,
        &proof.g1_F,
        None,
        [alpha1, alpha2].as_ref(),
        [proof.v1, proof.v2].as_ref(),
        &proof.pi1,
    );

    let g1_q = proof.pi2;

    // check that e(P Q3^(-alpha), g2)e( g^(-(rho0 + rho1) - zH(alpha) x^(d-1)), A ) e( Q3, g2^x ) = 1
    // Had  to move A from affine to projective and back to affine to get it to compile.
    // No idea what difference this makes.
    let eq1 = vec![
        (
            (g1_p + g1_q.mul(alpha)).into_affine().into(),
            vk.poly_vk.prepared_h.clone(),
        ),
        (
            ((vk.g1.mul(-rho0 - rho1) + vk.gxpen.mul(-zalpha)).into_affine()).into(),
            g2_z.into_projective().into_affine().into(),
        ),
        ((-g1_q).into(), vk.poly_vk.prepared_beta_h.clone()),
    ];

    let check2 = E::product_of_pairings(&eq1).is_one();

    check1 && check2
}
