/*
This file includes backend tools:
(1) read_line() is for taking inputs from the user
(2) kzg_open_g1 is for opening KZG commitments
(3) kzg_verify_g1 is for verifying KZG commitments
(4) hash_caulk_single is for hashing group and field elements into a field element
(5) random_field is for generating random field elements
*/

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G2Affine, G1Projective};
use ark_ff::{PrimeField, Field};
use ark_poly::{univariate::DensePolynomial, UVPolynomial, Polynomial};
use ark_serialize::CanonicalSerialize;
use ark_std::{One, Zero};

use blake2s_simd::Params;
use rand::{Rng, SeedableRng, thread_rng};
use rand_chacha::ChaChaRng;
use std::{io, str::FromStr, error::Error};

use ark_poly_commit::kzg10::*;
use ark_poly::univariate::DensePolynomial as DensePoly;
use ark_ec::{PairingEngine, AffineCurve, ProjectiveCurve, msm::VariableBaseMSM};

pub type UniPoly381 = DensePoly<<Bls12_381 as PairingEngine>::Fr>;
pub type KzgBls12_381 = KZG10<Bls12_381, UniPoly381>;

// Function for reading inputs from the command line.
pub fn read_line<T: FromStr>() -> T
where <T as FromStr>::Err: Error + 'static
{
    let mut input = String::new();
    io::stdin().read_line(&mut input).expect("Failed to get console input.");
    let output: T = input.trim().parse().expect("Console input is invalid.");
    output
}

////////////////////////////////////////////////
//

//copied from arkworks
fn convert_to_bigints<F: PrimeField>(p: &Vec<F>) -> Vec<F::BigInt> {
    let coeffs = ark_std::cfg_iter!(p)
        .map(|s| s.into_repr())
        .collect::<Vec<_>>();
    coeffs
}

/////////////////////////////////////////////////////////////////////
// KZG opening and verifying
/////////////////////////////////////////////////////////////////////

/*
KZG.Open( srs_KZG, f(X), deg, (alpha1, alpha2, ..., alphan) )
returns ([f(alpha1), ..., f(alphan)], pi)
Algorithm described in Section 4.6.1, Multiple Openings
*/
pub fn kzg_open_g1(poly_ck: &Powers<Bls12_381>,
    poly: &DensePolynomial<Fr>,
    max_deg: Option<&usize>,
    points: Vec<&Fr>) -> (Vec<Fr>, G1Affine) {

    let mut evals = Vec::new();
    let mut proofs = Vec::new();
    for i in 0..points.len() {
        let (eval, pi) = kzg_open_g1_single( poly_ck, poly, max_deg, points[i] );
        evals.push( eval );
        proofs.push( pi );
    }

    let mut res: G1Projective = G1Projective::zero(); //default value

    for j in 0..points.len()
    {
        let w_j= points[j].clone();
        //1. Computing coefficient [1/prod]
        let mut prod =Fr::one();
        for k in 0..points.len() {
            let w_k = points[k];
            if k!=j{
                prod = prod*(w_j-w_k);
            }
        }
        //2. Summation
        let q_add = proofs[j].mul(prod.inverse().unwrap()); //[1/prod]Q_{j}
        res = res + q_add;
    }

    return (evals, res.into_affine());
}


//KZG.Open( srs_KZG, f(X), deg, alpha ) returns (f(alpha), pi)
fn kzg_open_g1_single(poly_ck: &Powers<Bls12_381>,
    poly: &DensePolynomial<Fr>,
    max_deg: Option<&usize>,
    point: &Fr) -> (Fr, G1Affine) {

    let eval = poly.evaluate( &point);

    let global_max_deg = poly_ck.powers_of_g.len();

    let mut d: usize = 0;
    if max_deg == None {
        d += global_max_deg;
    }
    else {
        d += max_deg.unwrap();
    }
    let divisor = DensePolynomial::from_coefficients_vec(vec![-point.clone(), Fr::one()]);
    let witness_polynomial = poly / &divisor;

    assert!( poly_ck.powers_of_g[(global_max_deg - d)..].len() >= witness_polynomial.len());
    let proof = VariableBaseMSM::multi_scalar_mul(&poly_ck.powers_of_g[(global_max_deg - d)..], &convert_to_bigints(&witness_polynomial.coeffs).as_slice() ).into_affine();
    return (eval, proof)

}

/*
// KZG.Verify( srs_KZG, F, deg, (alpha1, alpha2, ..., alphan), (v1, ..., vn), pi )
Algorithm described in Section 4.6.1, Multiple Openings
*/
pub fn kzg_verify_g1(    //Verify that @c_com is a commitment to C(X) such that C(x)=z
    powers_of_g1: &Vec<G1Affine>, // generator of G1
    powers_of_g2: &Vec<G2Affine>, // [1]_2, [x]_2, [x^2]_2, ...
    c_com: G1Affine, //commitment
    max_deg: Option<&usize>,  // max degree
    points: Vec<Fr>,      // x such that eval = C(x)
    evals: Vec<Fr>,       //evaluation
    pi: G1Affine, //proof

)
->bool{

    // Interpolation set
    // tau_i(X) = lagrange_tau[i] = polynomial equal to 0 at point[j] for j!= i and 1  at points[i]

    let mut lagrange_tau  = DensePolynomial::from_coefficients_slice(&[Fr::zero()]);
    for i in 0..points.len() {
        let mut temp : UniPoly381 = DensePolynomial::from_coefficients_slice(&[Fr::one()]);
        for j in 0..points.len() {
            if i != j {
            temp = &temp * (&DensePolynomial::from_coefficients_slice(&[-points[j] ,Fr::one()]));
            }
        }
        let lagrange_scalar = temp.evaluate(&points[i]).inverse().unwrap() * &evals[i] ;
        lagrange_tau = lagrange_tau + &temp * (&DensePolynomial::from_coefficients_slice(&[lagrange_scalar])) ;
     }

     // commit to sum evals[i] tau_i(X)

    assert!( powers_of_g1.len() >= lagrange_tau.len(), "KZG verifier doesn't have enough g1 powers" );
    let g1_tau = VariableBaseMSM::multi_scalar_mul(&powers_of_g1[..lagrange_tau.len()], convert_to_bigints(&lagrange_tau.coeffs).as_slice());


    // vanishing polynomial
    // z_tau[i] = polynomial equal to 0 at point[j]
    let mut z_tau  = DensePolynomial::from_coefficients_slice(&[Fr::one()]);
    for i in 0..points.len() {
            z_tau = &z_tau * (&DensePolynomial::from_coefficients_slice(&[-points[i] ,Fr::one()]));
        }

    // commit to z_tau(X) in g2
    assert!( powers_of_g2.len() >= z_tau.len(), "KZG verifier doesn't have enough g2 powers" );
    let g2_z_tau = VariableBaseMSM::multi_scalar_mul(&powers_of_g2[..z_tau.len()], convert_to_bigints(&z_tau.coeffs).as_slice());


    let global_max_deg = powers_of_g1.len();

    let mut d: usize = 0;
    if max_deg == None {
        d += global_max_deg;
    }
    else {
        d += max_deg.unwrap();
    }

     let pairing1 = Bls12_381::pairing(
        c_com.into_projective()-g1_tau,
        powers_of_g2[global_max_deg - d]
    );
    let pairing2  =Bls12_381::pairing(
        pi,
        g2_z_tau
    );

    return pairing1==pairing2;
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
    let rng = ChaChaRng::from_seed(seed);
    rng
}

fn hash_to_field<F: PrimeField>(
    personalization: &[u8],
    message: &[u8],
) -> F {
    let mut rng = rng_from_message(personalization, message);
    loop {
        let bytes: Vec<u8> = (0..F::zero().serialized_size())
            .map(|_| rng.gen())
            .collect();
        if let Some(p) = F::from_random_bytes(&bytes) {
            return p;
        }
    }
}

/* hash function that takes as input:
    (1) some state (either equal to the last hash output or zero)
    (2) a vector of g1 elements
    (3) a vector of g2 elements
    (4) a vector of field elements

It returns a field element.
*/
pub fn hash_caulk_single<F: PrimeField>(
    state: Fr,
    g1_elements: Option< &Vec<G1Affine>>,
    g2_elements: Option< &Vec<G2Affine>>,
    field_elements: Option< &Vec<Fr>> ) -> Fr
    {

    // PERSONALIZATION distinguishes this hash from other hashes that may be in the system
    const PERSONALIZATION: &[u8] = b"CAULK1";

    ///////////////////////////////////////////////////////////
    // Handling cases where no g1_elements or no g1_elements or no field elements are input
    ///////////////////////////////////////////////////////////
    let g1_elements_len: usize;
    let g2_elements_len: usize;
    let field_elements_len: usize;

    if g1_elements == None {
        g1_elements_len = 0;
    }
    else {
        g1_elements_len = g1_elements.unwrap().len();
    }

    if g2_elements == None {
        g2_elements_len = 0;
    }
    else {
        g2_elements_len = g2_elements.unwrap().len();
    }

    if field_elements == None {
        field_elements_len = 0;
    }
    else {
        field_elements_len = field_elements.unwrap().len();
    }

    ///////////////////////////////////////////////////////////
    // Transform inputs into bytes
    ///////////////////////////////////////////////////////////
    let mut state_bytes = vec![];
    state.serialize(&mut state_bytes).ok();

    let mut g1_elements_bytes = Vec::new();
    for i in 0..g1_elements_len {
        let mut temp = vec![];
        g1_elements.unwrap()[i].serialize( &mut temp ).ok();
        g1_elements_bytes.append( &mut temp.clone() );
    }

    let mut g2_elements_bytes = Vec::new();
    for i in 0..g2_elements_len {
        let mut temp = vec![];
        g2_elements.unwrap()[i].serialize( &mut temp ).ok();
        g2_elements_bytes.append( &mut temp.clone() );
    }



    let mut field_elements_bytes = Vec::new();
    for i in 0..field_elements_len {
        let mut temp = vec![];
        field_elements.unwrap()[i].serialize( &mut temp ).ok();
        field_elements_bytes.append( &mut temp.clone() );
    }

    // Transform bytes into vector of bytes of the form expected by hash_to_field
    let mut hash_input: Vec<u8> = state_bytes.clone();
    for i in 0..g1_elements_bytes.len() {
        hash_input = [ &hash_input as &[_], &[g1_elements_bytes[i]] ].concat();
    }

    for i in 0..g2_elements_bytes.len() {
        hash_input = [ &hash_input as &[_], &[g2_elements_bytes[i]] ].concat();
    }

    for i in 0..field_elements_bytes.len() {
        hash_input = [ &hash_input as &[_], &[field_elements_bytes[i]] ].concat();
    }

    // hash_to_field
    return hash_to_field::<Fr>(
            PERSONALIZATION,
            &hash_input
       );
}

/////////////////////////////////////////////////////////////////////
// Random field element
/////////////////////////////////////////////////////////////////////

// generating a random field element
pub fn random_field< F: PrimeField >() -> F {

   let mut rng = thread_rng();
   loop {
       let bytes: Vec<u8> = (0..F::zero().serialized_size())
           .map(|_| rng.gen())
           .collect();
       if let Some(p) = F::from_random_bytes(&bytes) {
           return p;
       }
   }
}
