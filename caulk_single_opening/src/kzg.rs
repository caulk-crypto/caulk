/*
This file includes backend tools:
(1) read_line() is for taking inputs from the user
(2) kzg_open_g1 is for opening KZG commitments
(3) kzg_verify_g1 is for verifying KZG commitments
(4) hash_caulk_single is for hashing group and field elements into a field element
(5) random_field is for generating random field elements
*/

use crate::{compute_h, dft_g1};
use ark_ec::{msm::VariableBaseMSM, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, PrimeField};
use ark_poly::{univariate::DensePolynomial, Polynomial, UVPolynomial};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::kzg10::*;
use ark_std::{end_timer, start_timer};
use ark_std::{One, Zero};
#[cfg(feature = "parallel")]
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use std::marker::PhantomData;

////////////////////////////////////////////////
//

//copied from arkworks
fn convert_to_bigints<F: PrimeField>(p: &[F]) -> Vec<F::BigInt> {
    ark_std::cfg_iter!(p)
        .map(|s| s.into_repr())
        .collect::<Vec<_>>()
}

/////////////////////////////////////////////////////////////////////
// KZG opening and verifying
/////////////////////////////////////////////////////////////////////

pub struct KZGCommit<E: PairingEngine> {
    phantom: PhantomData<E>,
}

impl<E: PairingEngine> KZGCommit<E> {
    pub fn commit(powers: &Powers<E>, polynomial: &DensePolynomial<E::Fr>) -> E::G1Affine {
        let (com, _randomness) = KZG10::<E, _>::commit(powers, polynomial, None, None).unwrap();
        com.0
    }

    // compute all openings to c_poly using a smart formula
    // This Code implements an algorithm for calculating n openings of a KZG vector commitment of size n in n log(n) time.
    // The algorithm is by Feist and Khovratovich.
    // It is useful for preprocessing.
    // The full algorithm is described here https://github.com/khovratovich/Kate/blob/master/Kate_amortized.pdf
    pub fn multiple_open(
        c_poly: &DensePolynomial<E::Fr>, //c(X)
        poly_ck: &Powers<E>,             //SRS
        p: usize,
    ) -> Vec<E::G1Affine> {
        let timer = start_timer!(|| "multiple open");

        let degree = c_poly.coeffs.len() - 1;
        let input_domain: GeneralEvaluationDomain<E::Fr> = EvaluationDomain::new(degree).unwrap();

        let h_timer = start_timer!(|| "compute h");
        let h2 = compute_h(c_poly, poly_ck, p);
        end_timer!(h_timer);

        let dom_size = input_domain.size();
        assert_eq!(1 << p, dom_size);
        assert_eq!(degree + 1, dom_size);

        let dft_timer = start_timer!(|| "G1 dft");
        let q2 = dft_g1::<E>(&h2, p);
        end_timer!(dft_timer);

        let res = E::G1Projective::batch_normalization_into_affine(q2.as_ref());

        end_timer!(timer);
        res
    }

    /*
    KZG.Open( srs_KZG, f(X), deg, (alpha1, alpha2, ..., alphan) )
    returns ([f(alpha1), ..., f(alphan)], pi)
    Algorithm described in Section 4.6.1, Multiple Openings
    */
    pub fn open_g1_batch(
        poly_ck: &Powers<E>,
        poly: &DensePolynomial<E::Fr>,
        max_deg: Option<&usize>,
        points: &[E::Fr],
    ) -> (Vec<E::Fr>, E::G1Affine) {
        let mut evals = Vec::new();
        let mut proofs = Vec::new();
        for p in points.iter() {
            let (eval, pi) = Self::open_g1_single(poly_ck, poly, max_deg, p);
            evals.push(eval);
            proofs.push(pi);
        }

        let mut res = E::G1Projective::zero(); //default value

        for j in 0..points.len() {
            let w_j = points[j];
            //1. Computing coefficient [1/prod]
            let mut prod = E::Fr::one();
            for (k, p) in points.iter().enumerate() {
                if k != j {
                    prod *= w_j - p;
                }
            }
            //2. Summation
            let q_add = proofs[j].mul(prod.inverse().unwrap()); //[1/prod]Q_{j}
            res += q_add;
        }

        (evals, res.into_affine())
    }

    //KZG.Open( srs_KZG, f(X), deg, alpha ) returns (f(alpha), pi)
    fn open_g1_single(
        poly_ck: &Powers<E>,
        poly: &DensePolynomial<E::Fr>,
        max_deg: Option<&usize>,
        point: &E::Fr,
    ) -> (E::Fr, E::G1Affine) {
        let eval = poly.evaluate(point);

        let global_max_deg = poly_ck.powers_of_g.len();

        let mut d: usize = 0;
        if max_deg == None {
            d += global_max_deg;
        } else {
            d += max_deg.unwrap();
        }
        let divisor = DensePolynomial::from_coefficients_vec(vec![-*point, E::Fr::one()]);
        let witness_polynomial = poly / &divisor;

        assert!(poly_ck.powers_of_g[(global_max_deg - d)..].len() >= witness_polynomial.len());
        let proof = VariableBaseMSM::multi_scalar_mul(
            &poly_ck.powers_of_g[(global_max_deg - d)..],
            convert_to_bigints(&witness_polynomial.coeffs).as_slice(),
        )
        .into_affine();
        (eval, proof)
    }

    /*
    // KZG.Verify( srs_KZG, F, deg, (alpha1, alpha2, ..., alphan), (v1, ..., vn), pi )
    Algorithm described in Section 4.6.1, Multiple Openings
    */
    pub fn verify_g1(
        // Verify that @c_com is a commitment to C(X) such that C(x)=z
        powers_of_g1: &[E::G1Affine], // generator of G1
        powers_of_g2: &[E::G2Affine], // [1]_2, [x]_2, [x^2]_2, ...
        c_com: &E::G1Affine,          //commitment
        max_deg: Option<&usize>,      // max degree
        points: &[E::Fr],             // x such that eval = C(x)
        evals: &[E::Fr],              //evaluation
        pi: &E::G1Affine,             //proof
    ) -> bool {
        // Interpolation set
        // tau_i(X) = lagrange_tau[i] = polynomial equal to 0 at point[j] for j!= i and 1  at points[i]

        let mut lagrange_tau = DensePolynomial::from_coefficients_slice(&[E::Fr::zero()]);
        let mut prod = DensePolynomial::from_coefficients_slice(&[E::Fr::one()]);
        let mut components = vec![];
        for &p in points.iter() {
            let poly = DensePolynomial::from_coefficients_slice(&[-p, E::Fr::one()]);
            prod = &prod * (&poly);
            components.push(poly);
        }

        for i in 0..points.len() {
            let mut temp = &prod / &components[i];
            let lagrange_scalar = temp.evaluate(&points[i]).inverse().unwrap() * evals[i];
            temp.coeffs.iter_mut().for_each(|x| *x *= lagrange_scalar);
            lagrange_tau = lagrange_tau + temp;
        }

        // commit to sum evals[i] tau_i(X)
        assert!(
            powers_of_g1.len() >= lagrange_tau.len(),
            "KZG verifier doesn't have enough g1 powers"
        );
        let g1_tau = VariableBaseMSM::multi_scalar_mul(
            &powers_of_g1[..lagrange_tau.len()],
            convert_to_bigints(&lagrange_tau.coeffs).as_slice(),
        );

        // vanishing polynomial
        let z_tau = prod;

        // commit to z_tau(X) in g2
        assert!(
            powers_of_g2.len() >= z_tau.len(),
            "KZG verifier doesn't have enough g2 powers"
        );
        let g2_z_tau = VariableBaseMSM::multi_scalar_mul(
            &powers_of_g2[..z_tau.len()],
            convert_to_bigints(&z_tau.coeffs).as_slice(),
        );

        let global_max_deg = powers_of_g1.len();

        let mut d: usize = 0;
        if max_deg == None {
            d += global_max_deg;
        } else {
            d += max_deg.unwrap();
        }

        let pairing_inputs = vec![
            (
                E::G1Prepared::from((g1_tau - c_com.into_projective()).into_affine()),
                E::G2Prepared::from(powers_of_g2[global_max_deg - d]),
            ),
            (
                E::G1Prepared::from(*pi),
                E::G2Prepared::from(g2_z_tau.into_affine()),
            ),
        ];

        E::product_of_pairings(pairing_inputs.iter()).is_one()
    }
}
