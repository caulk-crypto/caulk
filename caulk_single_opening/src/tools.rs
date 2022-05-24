/*
This file includes backend tools:
(1) read_line() is for taking inputs from the user
(2) kzg_open_g1 is for opening KZG commitments
(3) kzg_verify_g1 is for verifying KZG commitments
(4) hash_caulk_single is for hashing group and field elements into a field element
(5) random_field is for generating random field elements
*/

use ark_ec::{msm::VariableBaseMSM, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, PrimeField};
use ark_poly::{univariate::DensePolynomial, Polynomial, UVPolynomial};
use ark_poly_commit::kzg10::*;
use ark_serialize::CanonicalSerialize;
use ark_std::{One, Zero};
use blake2s_simd::Params;
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaChaRng;
use std::{error::Error, io, str::FromStr};

// Function for reading inputs from the command line.
pub fn read_line<T: FromStr>() -> T
where
    <T as FromStr>::Err: Error + 'static,
{
    let mut input = String::new();
    io::stdin()
        .read_line(&mut input)
        .expect("Failed to get console input.");
    let output: T = input.trim().parse().expect("Console input is invalid.");
    output
}

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

/*
KZG.Open( srs_KZG, f(X), deg, (alpha1, alpha2, ..., alphan) )
returns ([f(alpha1), ..., f(alphan)], pi)
Algorithm described in Section 4.6.1, Multiple Openings
*/
pub fn kzg_open_g1<E: PairingEngine>(
    poly_ck: &Powers<E>,
    poly: &DensePolynomial<E::Fr>,
    max_deg: Option<&usize>,
    points: &[E::Fr],
) -> (Vec<E::Fr>, E::G1Affine) {
    let mut evals = Vec::new();
    let mut proofs = Vec::new();
    for p in points.iter() {
        let (eval, pi) = kzg_open_g1_single(poly_ck, poly, max_deg, p);
        evals.push(eval);
        proofs.push(pi);
    }

    let mut res: E::G1Projective = E::G1Projective::zero(); //default value

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
fn kzg_open_g1_single<E: PairingEngine>(
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
pub fn kzg_verify_g1<E: PairingEngine>(
    //Verify that @c_com is a commitment to C(X) such that C(x)=z
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
    // TODO: improve the efficiency here to linear
    for i in 0..points.len() {
        let mut temp = DensePolynomial::from_coefficients_slice(&[E::Fr::one()]);
        for (j, &p) in points.iter().enumerate() {
            if i != j {
                temp = &temp * (&DensePolynomial::from_coefficients_slice(&[-p, E::Fr::one()]));
            }
        }
        let lagrange_scalar = temp.evaluate(&points[i]).inverse().unwrap() * evals[i];
        lagrange_tau =
            lagrange_tau + &temp * (&DensePolynomial::from_coefficients_slice(&[lagrange_scalar]));
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
    // z_tau[i] = polynomial equal to 0 at point[j]
    let mut z_tau = DensePolynomial::from_coefficients_slice(&[E::Fr::one()]);
    for &p in points.iter() {
        z_tau = &z_tau * (&DensePolynomial::from_coefficients_slice(&[-p, E::Fr::one()]));
    }

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
            E::G1Prepared::from((c_com.into_projective() - g1_tau).into_affine()),
            E::G2Prepared::from(powers_of_g2[global_max_deg - d]),
        ),
        (
            E::G1Prepared::from(*pi),
            E::G2Prepared::from(g2_z_tau.into_affine()),
        ),
    ];

    E::product_of_pairings(pairing_inputs.iter()).is_one()
}

/////////////////////////////////////////////////////////////////////
// Hashing
/////////////////////////////////////////////////////////////////////

// hashing to field copied from
// https://github.com/kobigurk/aggregatable-dkg/blob/main/src/signature/utils/hash.rs
fn rng_from_message(personalization: &[u8], message: &[u8]) -> ChaChaRng {
    let hash = Params::new()
        .hash_length(32)
        .personal(personalization)
        .to_state()
        .update(message)
        .finalize();
    let mut seed = [0u8; 32];
    seed.copy_from_slice(hash.as_bytes());
    ChaChaRng::from_seed(seed)
}

// statistical uniform with bias < 2^-128 for field size < 384 bits
fn hash_to_field<F: PrimeField>(personalization: &[u8], message: &[u8]) -> F {
    let mut rng = rng_from_message(personalization, message);
    let mut buf = [0u8; 64];
    rng.fill_bytes(&mut buf);
    F::from_le_bytes_mod_order(buf.as_ref())
}

/* hash function that takes as input:
    (1) some state (either equal to the last hash output or zero)
    (2) a vector of g1 elements
    (3) a vector of g2 elements
    (4) a vector of field elements

It returns a field element.
*/
pub fn hash_caulk_single<E: PairingEngine>(
    state: &E::Fr,
    g1_elements: Option<&[E::G1Affine]>,
    g2_elements: Option<&[E::G2Affine]>,
    field_elements: Option<&[E::Fr]>,
) -> E::Fr {
    // PERSONALIZATION distinguishes this hash from other hashes that may be in the system
    const PERSONALIZATION: &[u8] = b"CAULK1";

    let mut hash_input = vec![];
    state.serialize(&mut hash_input).ok();

    match g1_elements {
        None => (),
        Some(p) => p.iter().for_each(|x| x.serialize(&mut hash_input).unwrap()),
    }
    match g2_elements {
        None => (),
        Some(p) => p.iter().for_each(|x| x.serialize(&mut hash_input).unwrap()),
    }
    match field_elements {
        None => (),
        Some(p) => p.iter().for_each(|x| x.serialize(&mut hash_input).unwrap()),
    }

    // hash_to_field
    hash_to_field::<E::Fr>(PERSONALIZATION, &hash_input)
}
