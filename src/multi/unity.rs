// This file includes the Caulk's unity prover and verifier for multi openings.
// The protocol is described in Figure 4.

use super::setup::PublicParameters;
use crate::{util::convert_to_bigints, CaulkTranscript, KZGCommit};
use ark_ec::{msm::VariableBaseMSM, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::Field;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Evaluations as EvaluationsOnDomain, Polynomial,
    UVPolynomial,
};
use ark_std::{One, Zero};

// output structure of prove_unity
pub struct ProofMultiUnity<E: PairingEngine> {
    pub g1_u_bar: E::G1Affine,
    pub g1_h_1: E::G1Affine,
    pub g1_h_2: E::G1Affine,
    pub g1_u_bar_alpha: E::G1Affine,
    pub g1_h_2_alpha: E::G1Affine,
    pub v1: E::Fr,
    pub v2: E::Fr,
    pub v3: E::Fr,
    pub pi_1: E::G1Affine,
    pub pi_2: E::G1Affine,
    pub pi_3: E::G1Affine,
    pub pi_4: E::G1Affine,
    pub pi_5: E::G1Affine,
}

// Prove knowledge of vec_u_evals such that g1_u = g1^(sum_j u_j mu_j(x)) and
// u_j^N = 1
#[allow(non_snake_case)]
pub fn prove_multiunity<E: PairingEngine>(
    pp: &PublicParameters<E>,
    transcript: &mut CaulkTranscript<E::Fr>,
    g1_u: &E::G1Affine,
    mut vec_u_evals: Vec<E::Fr>,
    u_poly_quotient: DensePolynomial<E::Fr>,
) -> ProofMultiUnity<E> {
    // The test_rng is deterministic.  Should be replaced with actual random
    // generator.
    let rng_arkworks = &mut ark_std::test_rng();

    // let rng_arkworks = &mut ark_std::test_rng();
    let n = pp.n;
    let deg_blinders = 11 / n;
    let z_Vm: DensePolynomial<E::Fr> = pp.domain_m.vanishing_polynomial().into();

    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    // 1. Compute polynomials u_s(X) = vec_u_polys[s] such that u_s( nu_i ) =
    // w_i^{2^s}
    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    let mut vec_u_polys = vec![
        EvaluationsOnDomain::from_vec_and_domain(vec_u_evals.clone(), pp.domain_m).interpolate()
            + (&z_Vm * &u_poly_quotient),
    ];

    for _ in 1..pp.domain_n.size() {
        for u_eval in &mut vec_u_evals {
            *u_eval = u_eval.square();
        }

        vec_u_polys.push(
            EvaluationsOnDomain::from_vec_and_domain(vec_u_evals.clone(), pp.domain_m)
                .interpolate()
                + (&z_Vm * &DensePolynomial::<E::Fr>::rand(deg_blinders, rng_arkworks)),
        );
    }

    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    // 2. Compute U_bar(X,Y) = sum_{s= 1}^n u_{s-1} rho_s(Y)
    //////////////////////////////////////////////////////////////////////////////////////////////////////////

    // bivariate polynomials such that bipoly_U_bar[j] = a_j(Y) where U_bar(X,Y) =
    // sum_j X^j a_j(Y)
    let mut bipoly_U_bar = Vec::new();

    // vec_u_polys[0]  has an extended degree because it is blinded so use
    // vec_u_polys[1] for the length
    for j in 0..vec_u_polys[1].len() {
        /*
        Denoting u_{s-1}(X) = sum_j u_{s-1, j} X^j then
        temp is a_j(Y) = sum_{s=1}^n u_{s-1, j} * rho_s(Y)
         */
        let mut temp = DensePolynomial::from_coefficients_slice(&[E::Fr::zero()]);

        for (s, u_poly) in vec_u_polys.iter().enumerate().take(n).skip(1){
            let u_s_j = DensePolynomial::from_coefficients_slice(&[u_poly[j]]);
            temp += &(&u_s_j * &pp.lagrange_polynomials_n[s]);
        }

        // add a_j(X) to U_bar(X,Y)
        bipoly_U_bar.push(temp);
    }

    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    // 3. Hs(X) = u_{s-1}^2(X) - u_s(X)
    //////////////////////////////////////////////////////////////////////////////////////////////////////////

    // id_poly(X) = 1 for omega_m in range and 0 for omega_m not in range.
    let id_poly = pp.id_poly.clone();

    // Hs(X) = (u_{s-1}^2(X) - u_s(X)) / zVm(X).  Abort if doesn't divide.
    let mut vec_H_s_polys: Vec<DensePolynomial<E::Fr>> = Vec::new();
    for s in 1..n {
        let (poly_H_s, remainder) = (&(&vec_u_polys[s - 1] * &vec_u_polys[s - 1])
            - &vec_u_polys[s])
            .divide_by_vanishing_poly(pp.domain_m)
            .unwrap();
        assert!(remainder.is_zero());
        vec_H_s_polys.push(poly_H_s);
    }

    // Hn(X) = u_{n-1}^2(X) - id(X) / zVm(X).  Abort if doesn't divide.
    let (poly_H_s, remainder) = (&(&vec_u_polys[n - 1] * &vec_u_polys[n - 1]) - &id_poly)
        .divide_by_vanishing_poly(pp.domain_m)
        .unwrap();
    assert!(remainder.is_zero());
    vec_H_s_polys.push(poly_H_s);

    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    // 4. h_2(X,Y) = sum_{s=1}^n rho_s(Y) H_s(X)
    //////////////////////////////////////////////////////////////////////////////////////////////////////////

    // h_2[j] = a_j(Y) where h_2(X,Y) = sum_j X^j a_j(Y)
    let mut bipoly_h_2 = Vec::new();

    // first add H_1(X) rho_1(Y)
    for j in 0..vec_H_s_polys[0].len() {
        let h_0_j = DensePolynomial::from_coefficients_slice(&[vec_H_s_polys[0][j]]);
        bipoly_h_2.push(&h_0_j * &pp.lagrange_polynomials_n[0]);
    }

    // In case length of H_1(X) and H_2(X) is different pad with zeros.
    for _ in vec_H_s_polys[0].len()..vec_H_s_polys[1].len() {
        let h_0_j = DensePolynomial::from_coefficients_slice(&[E::Fr::zero()]);
        bipoly_h_2.push(h_0_j);
    }

    // h_2(X,Y) = sum_j ( sum_s H_{s,j} * rho_s(Y) ) X^j
    for (j, coeff) in bipoly_h_2
        .iter_mut()
        .enumerate()
        .take(vec_H_s_polys[1].len())
    {
        // h_2[j] = sum_s H_{s,j} * rho_s(Y)
        for (s, H_s_poly) in vec_H_s_polys.iter().enumerate().take(n).skip(1) {
            let h_s_j = DensePolynomial::from_coefficients_slice(&[H_s_poly[j]]);

            // h_2[j] += H_{s,j} * rho_s(Y)
            *coeff += &(&h_s_j * &pp.lagrange_polynomials_n[s]);
        }
    }

    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    // 5. Commit to U_bar(X^n, X) and h_2(X^n, X)
    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    let g1_u_bar = KZGCommit::<E>::bipoly_commit(pp, &bipoly_U_bar, pp.domain_n.size());
    let g1_h_2 = KZGCommit::<E>::bipoly_commit(pp, &bipoly_h_2, pp.domain_n.size());

    ////////////////////////////
    // 6. alpha = Hash(g1_u, g1_u_bar, g1_h_2)
    ////////////////////////////
    transcript.append_element(b"u", g1_u);
    transcript.append_element(b"u_bar", &g1_u_bar);
    transcript.append_element(b"h2", &g1_h_2);
    let alpha = transcript.get_and_append_challenge(b"alpha");

    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    // 7. Compute h_1(Y)
    //////////////////////////////////////////////////////////////////////////////////////////////////////////

    // poly_U_alpha = sum_{s=1}^n u_{s-1}(alpha) rho_s(Y)
    let mut poly_U_alpha = DensePolynomial::from_coefficients_slice(&[E::Fr::zero()]);

    // poly_Usq_alpha = sum_{s=1}^n u_{s-1}^2(alpha) rho_s(Y)
    let mut poly_Usq_alpha = DensePolynomial::from_coefficients_slice(&[E::Fr::zero()]);

    for (s, u_poly) in vec_u_polys.iter().enumerate().take(n) {
        let u_s_alpha = u_poly.evaluate(&alpha);
        let mut temp = DensePolynomial::from_coefficients_slice(&[u_s_alpha]);
        poly_U_alpha += &(&temp * &pp.lagrange_polynomials_n[s]);

        temp = DensePolynomial::from_coefficients_slice(&[u_s_alpha.square()]);
        poly_Usq_alpha += &(&temp * &pp.lagrange_polynomials_n[s]);
    }

    // divide h1(Y) = [ U^2(alpha,Y) - sum_{s=1}^n u_{s-1}^2(alpha) rho_s(Y) ) ] /
    // zVn(Y) return an error if division fails
    let (poly_h_1, remainder) = (&(&poly_U_alpha * &poly_U_alpha) - &poly_Usq_alpha)
        .divide_by_vanishing_poly(pp.domain_n)
        .unwrap();
    assert!(remainder.is_zero(), "poly_h_1 does not divide");

    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    // 8. Commit to h_1(Y)
    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    assert!(pp.poly_ck.powers_of_g.len() >= poly_h_1.len());
    let g1_h_1 = VariableBaseMSM::multi_scalar_mul(
        &pp.poly_ck.powers_of_g,
        convert_to_bigints(&poly_h_1.coeffs).as_slice(),
    )
    .into_affine();

    ////////////////////////////
    // 9.  beta = Hash( g1_h_1 )
    ////////////////////////////

    transcript.append_element(b"h1", &g1_h_1);
    let beta = transcript.get_and_append_challenge(b"beta");

    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    // 10. Compute p(Y) = (U^2(alpha, beta) - h1(Y) zVn(beta) ) - (u_bar(alpha, beta
    // sigma^(-1)) + id(alpha) rho_n(Y)) - zVm(alpha )h2(alpha,Y)
    //////////////////////////////////////////////////////////////////////////////////////////////////////////

    // p(Y) = U^2(alpha, beta)
    let u_alpha_beta = poly_U_alpha.evaluate(&beta);
    let mut poly_p = DensePolynomial::from_coefficients_slice(&[u_alpha_beta.square()]);

    ////////////////////////////
    // p(Y) = p(Y) - ( u_bar(alpha, beta sigma) + id(alpha) rho_n(beta))

    // u_bar_alpha_shiftbeta = u_bar(alpha, beta sigma)
    let mut u_bar_alpha_shiftbeta = E::Fr::zero();
    let beta_shift = beta * pp.domain_n.element(1);
    for (s, u_ploy) in vec_u_polys.iter().enumerate().take(n).skip(1) {
        let u_s_alpha = u_ploy.evaluate(&alpha);
        u_bar_alpha_shiftbeta += u_s_alpha * pp.lagrange_polynomials_n[s].evaluate(&beta_shift);
    }

    // temp = u_bar(alpha, beta sigma) + id(alpha) rho_n(beta)
    let temp = u_bar_alpha_shiftbeta
        + (id_poly.evaluate(&alpha) * pp.lagrange_polynomials_n[n - 1].evaluate(&beta));
    let temp = DensePolynomial::from_coefficients_slice(&[temp]);

    poly_p = &poly_p - &temp;

    ////////////////////////////
    // p(Y) = p(Y) - h1(Y) zVn(beta)
    let z_Vn: DensePolynomial<E::Fr> = pp.domain_n.vanishing_polynomial().into();
    let temp = &DensePolynomial::from_coefficients_slice(&[z_Vn.evaluate(&beta)]) * &poly_h_1;
    poly_p = &poly_p - &temp;

    ////////////////////////////
    // p(Y) = p(Y) - z_Vm(alpha) h_2(alpha, Y)

    // poly_h_2_alpha = h_2(alpha, Y)
    let mut poly_h_2_alpha = DensePolynomial::from_coefficients_slice(&[E::Fr::zero()]);
    for (s, H_s_poly) in vec_H_s_polys.iter().enumerate() {
        let h_s_j = DensePolynomial::from_coefficients_slice(&[H_s_poly.evaluate(&alpha)]);
        poly_h_2_alpha = &poly_h_2_alpha + &(&h_s_j * &pp.lagrange_polynomials_n[s]);
    }

    let temp =
        &DensePolynomial::from_coefficients_slice(&[z_Vm.evaluate(&alpha)]) * &poly_h_2_alpha;
    poly_p = &poly_p - &temp;

    // check p(beta) = 0
    assert!(poly_p.evaluate(&beta) == E::Fr::zero());

    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    // 11. Open KZG commitments
    //////////////////////////////////////////////////////////////////////////////////////////////////////////

    // KZG.Open( srs, u(X), deg = bot, X = alpha )
    let (evals_1, pi_1) = KZGCommit::open_g1_batch(&pp.poly_ck, &vec_u_polys[0], None, &[alpha]);

    // KZG.Open( srs, U_bar(X,Y), deg = bot, X = alpha )
    let (g1_u_bar_alpha, pi_2, poly_u_bar_alpha) =
        KZGCommit::partial_open_g1(pp, &bipoly_U_bar, pp.domain_n.size(), &alpha);

    // KZG.Open( srs, h_2(X,Y), deg = bot, X = alpha )
    let (g1_h_2_alpha, pi_3, _) =
        KZGCommit::partial_open_g1(pp, &bipoly_h_2, pp.domain_n.size(), &alpha);

    // KZG.Open( srs, U_bar(alpha,Y), deg = bot, Y = [1, beta, beta * sigma] )
    // should evaluate to (0, v2, v3)
    let (evals_2, pi_4) = KZGCommit::open_g1_batch(
        &pp.poly_ck,
        &poly_u_bar_alpha,
        Some(&(pp.domain_n.size() - 1)),
        &[E::Fr::one(), beta, beta * pp.domain_n.element(1)],
    );
    assert!(evals_2[0] == E::Fr::zero());

    // KZG.Open(srs, p(Y), deg = n-1, Y = beta)
    let (evals_3, pi_5) = KZGCommit::open_g1_batch(
        &pp.poly_ck,
        &poly_p,
        Some(&(pp.domain_n.size() - 1)),
        &[beta],
    );
    assert!(evals_3[0] == E::Fr::zero());

    ProofMultiUnity {
        g1_u_bar,
        g1_h_1,
        g1_h_2,
        g1_u_bar_alpha,
        g1_h_2_alpha,
        v1: evals_1[0],
        v2: evals_2[1],
        v3: evals_2[2],
        pi_1,
        pi_2,
        pi_3,
        pi_4,
        pi_5,
    }
}

// Verify that the prover knows vec_u_evals such that g1_u = g1^(sum_j u_j
// mu_j(x)) and u_j^N = 1
#[allow(non_snake_case)]
pub fn verify_multiunity<E: PairingEngine>(
    pp: &PublicParameters<E>,
    transcript: &mut CaulkTranscript<E::Fr>,
    g1_u: &E::G1Affine,
    pi_unity: &ProofMultiUnity<E>,
) -> bool {
    ////////////////////////////
    // alpha = Hash(g1_u, g1_u_bar, g1_h_2)
    ////////////////////////////
    transcript.append_element(b"u", g1_u);
    transcript.append_element(b"u_bar", &pi_unity.g1_u_bar);
    transcript.append_element(b"h2", &pi_unity.g1_h_2);
    let alpha = transcript.get_and_append_challenge(b"alpha");

    ////////////////////////////
    // beta = Hash( g1_h_1 )
    ////////////////////////////
    transcript.append_element(b"h1", &pi_unity.g1_h_1);
    let beta = transcript.get_and_append_challenge(b"beta");

    /////////////////////////////
    // Compute [P]_1
    ////////////////////////////

    let u_alpha_beta = pi_unity.v1 * pp.lagrange_polynomials_n[0].evaluate(&beta) + pi_unity.v2;

    // g1_P = [ U^2 - (v3 + id(alpha)* pn(beta) )]_1
    let mut g1_P = pp.poly_ck.powers_of_g[0].mul(
        u_alpha_beta * u_alpha_beta
            - (pi_unity.v3
                + (pp.id_poly.evaluate(&alpha)
                    * pp.lagrange_polynomials_n[pp.n - 1].evaluate(&beta))),
    );

    // g1_P = g1_P  - h1 zVn(beta)
    let zVn = pp.domain_n.vanishing_polynomial();
    g1_P -= pi_unity.g1_h_1.mul(zVn.evaluate(&beta));

    // g1_P = g1_P  - h2_alpha zVm(alpha)
    let zVm = pp.domain_m.vanishing_polynomial();
    g1_P -= pi_unity.g1_h_2_alpha.mul(zVm.evaluate(&alpha));

    /////////////////////////////
    // Check the KZG openings
    ////////////////////////////

    let check1 = KZGCommit::<E>::verify_g1(
        &pp.poly_ck.powers_of_g,
        &pp.g2_powers,
        g1_u,
        None,
        &[alpha],
        &[pi_unity.v1],
        &pi_unity.pi_1,
    );
    let check2 = KZGCommit::partial_verify_g1(
        pp,
        &pi_unity.g1_u_bar,
        pp.domain_n.size(),
        &alpha,
        &pi_unity.g1_u_bar_alpha,
        &pi_unity.pi_2,
    );
    let check3 = KZGCommit::partial_verify_g1(
        pp,
        &pi_unity.g1_h_2,
        pp.domain_n.size(),
        &alpha,
        &pi_unity.g1_h_2_alpha,
        &pi_unity.pi_3,
    );
    let check4 = KZGCommit::<E>::verify_g1(
        &pp.poly_ck.powers_of_g,
        &pp.g2_powers,
        &pi_unity.g1_u_bar_alpha,
        Some(&(pp.domain_n.size() - 1)),
        &[E::Fr::one(), beta, beta * pp.domain_n.element(1)],
        &[E::Fr::zero(), pi_unity.v2, pi_unity.v3],
        &pi_unity.pi_4,
    );
    let check5 = KZGCommit::<E>::verify_g1(
        &pp.poly_ck.powers_of_g,
        &pp.g2_powers,
        &g1_P.into_affine(),
        Some(&(pp.domain_n.size() - 1)),
        &[beta],
        &[E::Fr::zero()],
        &pi_unity.pi_5,
    );

    check1 && check2 && check3 && check4 && check5
}

#[cfg(test)]
pub mod tests {
    use super::{prove_multiunity, verify_multiunity};
    use crate::{util::convert_to_bigints, CaulkTranscript};
    use ark_bls12_377::Bls12_377;
    use ark_bls12_381::Bls12_381;
    use ark_ec::{msm::VariableBaseMSM, PairingEngine, ProjectiveCurve};
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, Evaluations as EvaluationsOnDomain,
        UVPolynomial,
    };
    use ark_std::test_rng;
    use rand::Rng;
    use std::time::Instant;

    #[test]
    fn test_unity() {
        test_unity_helper::<Bls12_377>();
        test_unity_helper::<Bls12_381>();
    }

    #[allow(non_snake_case)]
    fn test_unity_helper<E: PairingEngine>() {
        let mut rng = test_rng();

        let n: usize = 8; // bitlength of poly degree
        let max_degree: usize = (1 << n) + 2;
        let N: usize = (1 << n) - 1;

        let m_bitsize: usize = 3;
        let m: usize = (1 << m_bitsize) - 1;

        // run the setup
        let now = Instant::now();
        let pp = crate::multi::PublicParameters::<E>::setup(&max_degree, &N, &m, &n);
        println!(
            "time to setup single openings of table size {:?} = {:?}",
            N + 1,
            now.elapsed()
        );

        ////////////////////////////////////////////////////////////////////////////////////
        // generating values for testing
        ////////////////////////////////////////////////////////////////////////////////////

        // choose [u1, ..., um] such that uj**N = 1
        let mut vec_u_evals: Vec<E::Fr> = Vec::new();
        for _ in 0..m {
            let j = rng.gen_range(0..pp.domain_N.size());
            vec_u_evals.push(pp.domain_N.element(j));
        }

        // choose random quotient polynomial of degree 1.
        let u_poly_quotient = DensePolynomial::<E::Fr>::rand(5, &mut rng);

        // X^m - 1
        let z_Vm: DensePolynomial<E::Fr> = pp.domain_m.vanishing_polynomial().into();

        // commit to polynomial u(X) = sum_j uj muj(X) + u_quotient(X) z_Vm(X)
        let u_poly = &EvaluationsOnDomain::from_vec_and_domain(vec_u_evals.clone(), pp.domain_m)
            .interpolate()
            + &(&u_poly_quotient * &z_Vm);

        assert!(pp.poly_ck.powers_of_g.len() >= u_poly.len());
        let g1_u = VariableBaseMSM::multi_scalar_mul(
            &pp.poly_ck.powers_of_g,
            convert_to_bigints(&u_poly.coeffs).as_slice(),
        )
        .into_affine();

        ////////////////////////////////////////////////////////////////////////////////////
        // run the prover
        ////////////////////////////////////////////////////////////////////////////////////
        let mut prover_transcript = CaulkTranscript::new();
        let pi_unity = prove_multiunity::<E>(
            &pp,
            &mut prover_transcript,
            &g1_u,
            vec_u_evals.clone(),
            u_poly_quotient,
        );

        ////////////////////////////////////////////////////////////////////////////////////
        // run the verifier
        ////////////////////////////////////////////////////////////////////////////////////
        let mut verifier_transcript = CaulkTranscript::new();
        println!(
            "unity proof verifies {:?}",
            verify_multiunity::<E>(&pp, &mut verifier_transcript, &g1_u, &pi_unity)
        );
    }
}
