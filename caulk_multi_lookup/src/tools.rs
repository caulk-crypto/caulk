/*
This file includes backend tools:
(1) read_line() is for taking inputs from the user
(2) bipoly_commit commits to bivariate polynomials
(3) hash_caulk_single is for hashing group and field elements into a field element
(4) random_field is for generating random field elements
(5) convert_to_bigints is for formatting inputs into multiscalar operations
(6) kzg_open_g1_native is for opening KZG commitments
(7) kzg_partial_open_g1_native is for partially opening bivariate commitments to univariate commitments
(8) kzg_verify_g1_native is for verifying KZG commitments
(9) kzg_partial_open_g1_native is for partially verifying bivariate commitments to univariate commitments
(10) generate_lagrange_polynomials_subset is for generating lagrange polynomials over a subset that is not roots of unity.
(11) aggregate_kzg_proofs_g2 is for aggregating KZG proofs
*/

use ark_bls12_381::{Bls12_381, Fr, FrParameters, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{msm::VariableBaseMSM, AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, Fp256, PrimeField};
use ark_poly::{
    univariate::DensePolynomial as DensePoly, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial, UVPolynomial,
};
use ark_poly_commit::kzg10::*;
use ark_serialize::CanonicalSerialize;
use ark_std::One;
use ark_std::Zero;

use blake2s_simd::Params;
use rand::{thread_rng, Rng, SeedableRng};
use rand_chacha::ChaChaRng;
use std::{error::Error, io, str::FromStr};

use crate::caulk_multi_setup::PublicParameters;

pub type UniPoly381 = DensePoly<<Bls12_381 as PairingEngine>::Fr>;
pub type KzgBls12_381 = KZG10<Bls12_381, UniPoly381>;

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

/*
Function to commit to f(X,Y)
here f = [ [a0, a1, a2], [b1, b2, b3] ] represents (a0 + a1 Y + a2 Y^2 ) + X (b1 + b2 Y + b3 Y^2)

First we unwrap to get a vector of form [a0, a1, a2, b0, b1, b2]
Then we commit to f as a commitment to f'(X) = a0 + a1 X + a2 X^2 + b0 X^3 + b1 X^4 + b2 X^5

We also need to know the maximum degree of (a0 + a1 Y + a2 Y^2 ) to prevent overflow errors.

This is described in Section 4.6.2
*/
pub fn bipoly_commit(
    pp: &PublicParameters,
    poly: &Vec<DensePoly<Fp256<FrParameters>>>,
    deg_x: usize,
) -> G1Affine {
    let mut poly_formatted = Vec::new();

    for i in 0..poly.len() {
        let temp = convert_to_bigints(&poly[i].coeffs);
        for j in 0..poly[i].len() {
            poly_formatted.push(temp[j]);
        }
        let temp = convert_to_bigints(&[Fr::zero()].to_vec())[0];
        for _ in poly[i].len()..deg_x {
            poly_formatted.push(temp);
        }
    }

    assert!(pp.poly_ck.powers_of_g.len() >= poly_formatted.len());
    let g1_poly =
        VariableBaseMSM::multi_scalar_mul(&pp.poly_ck.powers_of_g, poly_formatted.as_slice())
            .into_affine();

    return g1_poly;
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

pub fn hash_to_field<F: PrimeField>(personalization: &[u8], message: &[u8]) -> F {
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
pub fn hash_caulk_multi<F: PrimeField>(
    state: Fr,
    g1_elements: Option<&Vec<&G1Affine>>,
    g2_elements: Option<&Vec<&G2Affine>>,
    field_elements: Option<&Vec<&Fr>>,
) -> Fr {
    // PERSONALIZATION distinguishes this hash from other hashes that may be in the system
    const PERSONALIZATION: &[u8] = b"CAULK2";

    ///////////////////////////////////////////////////////////
    // Handling cases where no g1_elements or no g1_elements or no field elements are input
    ///////////////////////////////////////////////////////////
    let g1_elements_len: usize;
    let g2_elements_len: usize;
    let field_elements_len: usize;

    if g1_elements == None {
        g1_elements_len = 0;
    } else {
        g1_elements_len = g1_elements.unwrap().len();
    }

    if g2_elements == None {
        g2_elements_len = 0;
    } else {
        g2_elements_len = g2_elements.unwrap().len();
    }

    if field_elements == None {
        field_elements_len = 0;
    } else {
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
        g1_elements.unwrap()[i].clone().serialize(&mut temp).ok();
        g1_elements_bytes.append(&mut temp.clone());
    }

    let mut g2_elements_bytes = Vec::new();
    for i in 0..g2_elements_len {
        let mut temp = vec![];
        g2_elements.unwrap()[i].clone().serialize(&mut temp).ok();
        g2_elements_bytes.append(&mut temp.clone());
    }

    let mut field_elements_bytes = Vec::new();
    for i in 0..field_elements_len {
        let mut temp = vec![];
        field_elements.unwrap()[i].clone().serialize(&mut temp).ok();
        field_elements_bytes.append(&mut temp.clone());
    }

    // Transform bytes into vector of bytes of the form expected by hash_to_field
    let mut hash_input: Vec<u8> = state_bytes.clone();
    for i in 0..g1_elements_bytes.len() {
        hash_input = [&hash_input as &[_], &[g1_elements_bytes[i]]].concat();
    }

    for i in 0..g2_elements_bytes.len() {
        hash_input = [&hash_input as &[_], &[g2_elements_bytes[i]]].concat();
    }

    for i in 0..field_elements_bytes.len() {
        hash_input = [&hash_input as &[_], &[field_elements_bytes[i]]].concat();
    }

    // hash_to_field
    return hash_to_field::<Fr>(PERSONALIZATION, &hash_input);
}

//////////////////////////////////////////////////

pub fn random_field<F: PrimeField>() -> F {
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

//copied from arkworks
pub fn convert_to_bigints<F: PrimeField>(p: &Vec<F>) -> Vec<F::BigInt> {
    let coeffs = ark_std::cfg_iter!(p)
        .map(|s| s.into_repr())
        .collect::<Vec<_>>();
    coeffs
}

////////////////////////////////////////////////
//
/*
KZG.Open( srs_KZG, f(X), deg, (alpha1, alpha2, ..., alphan) )
returns ([f(alpha1), ..., f(alphan)], pi)
Algorithm described in Section 4.6.1, Multiple Openings
*/
pub fn kzg_open_g1_native(
    poly_ck: &Powers<Bls12_381>,
    poly: &DensePoly<Fr>,
    max_deg: Option<&usize>,
    points: Vec<&Fr>,
) -> (Vec<Fr>, G1Affine) {
    let mut evals = Vec::new();
    let mut proofs = Vec::new();
    for i in 0..points.len() {
        let (eval, pi) = kzg_open_g1_native_single(poly_ck, poly, max_deg, points[i]);
        evals.push(eval);
        proofs.push(pi);
    }

    let mut res: G1Projective = G1Projective::zero(); //default value

    for j in 0..points.len() {
        let w_j = points[j].clone();
        //1. Computing coefficient [1/prod]
        let mut prod = Fr::one();
        for k in 0..points.len() {
            let w_k = points[k];
            if k != j {
                prod = prod * (w_j - w_k);
            }
        }
        //2. Summation
        let q_add = proofs[j].mul(prod.inverse().unwrap()); //[1/prod]Q_{j}
        res = res + q_add;
    }

    return (evals, res.into_affine());
}

fn kzg_open_g1_native_single(
    poly_ck: &Powers<Bls12_381>,
    poly: &DensePoly<Fr>,
    max_deg: Option<&usize>,
    point: &Fr,
) -> (Fr, G1Affine) {
    let eval = poly.evaluate(&point);

    let global_max_deg = poly_ck.powers_of_g.len();

    let mut d: usize = 0;
    if max_deg == None {
        d += global_max_deg;
    } else {
        d += max_deg.unwrap();
    }
    let divisor = DensePoly::from_coefficients_vec(vec![-point.clone(), Fr::one()]);
    let witness_polynomial = poly / &divisor;

    assert!(poly_ck.powers_of_g[(global_max_deg - d)..].len() >= witness_polynomial.len());
    let proof = VariableBaseMSM::multi_scalar_mul(
        &poly_ck.powers_of_g[(global_max_deg - d)..],
        &convert_to_bigints(&witness_polynomial.coeffs).as_slice(),
    )
    .into_affine();
    return (eval, proof);
}

////////////////////////////////////////////////
//
/*
KZG.Open( srs_KZG, f(X, Y), deg, alpha )
returns ([f(alpha, x)]_1, pi)
Algorithm described in Section 4.6.2, KZG for Bivariate Polynomials
*/
pub fn kzg_partial_open_g1_native(
    pp: &PublicParameters,
    poly: &Vec<DensePoly<Fr>>,
    deg_x: usize,
    point: &Fr,
) -> (G1Affine, G1Affine, DensePoly<Fr>) {
    let mut poly_partial_eval = DensePoly::from_coefficients_vec(vec![Fr::zero()]);
    let mut alpha = Fr::one();
    for i in 0..poly.len() {
        let pow_alpha = DensePoly::from_coefficients_vec(vec![alpha.clone()]);
        poly_partial_eval = poly_partial_eval + &pow_alpha * &poly[i];
        alpha = alpha * point;
    }

    let eval = VariableBaseMSM::multi_scalar_mul(
        &pp.poly_ck.powers_of_g,
        convert_to_bigints(&poly_partial_eval.coeffs).as_slice(),
    )
    .into_affine();

    let mut witness_bipolynomial = Vec::new();
    let poly_reverse: Vec<_> = poly.into_iter().rev().collect();
    witness_bipolynomial.push(poly_reverse[0].clone());

    let alpha = DensePoly::from_coefficients_vec(vec![point.clone()]);
    for i in 1..(poly_reverse.len() - 1) {
        witness_bipolynomial.push(poly_reverse[i].clone() + &alpha * &witness_bipolynomial[i - 1]);
    }

    witness_bipolynomial.reverse();

    let proof = bipoly_commit(pp, &witness_bipolynomial, deg_x);

    return (eval, proof, poly_partial_eval);
}

/*
// KZG.Verify( srs_KZG, F, deg, (alpha1, alpha2, ..., alphan), (v1, ..., vn), pi )
Algorithm described in Section 4.6.1, Multiple Openings
*/
pub fn kzg_verify_g1_native(
    //Verify that @c_com is a commitment to C(X) such that C(x)=z
    srs: &PublicParameters,
    c_com: G1Affine,         //commitment
    max_deg: Option<&usize>, // max degree
    points: Vec<Fr>,         // x such that eval = C(x)
    evals: Vec<Fr>,          //evaluation
    pi: G1Affine,            //proof
) -> bool {
    // Interpolation set
    // tau_i(X) = lagrange_tau[i] = polynomial equal to 0 at point[j] for j!= i and 1  at points[i]

    let mut lagrange_tau = DensePoly::from_coefficients_slice(&[Fr::zero()]);
    for i in 0..points.len() {
        let mut temp: UniPoly381 = DensePoly::from_coefficients_slice(&[Fr::one()]);
        for j in 0..points.len() {
            if i != j {
                temp = &temp * (&DensePoly::from_coefficients_slice(&[-points[j], Fr::one()]));
            }
        }
        let lagrange_scalar = temp.evaluate(&points[i]).inverse().unwrap() * &evals[i];
        lagrange_tau =
            lagrange_tau + &temp * (&DensePoly::from_coefficients_slice(&[lagrange_scalar]));
    }

    // commit to sum evals[i] tau_i(X)

    // println!( "lagrange_tau = {:?}", lagrange_tau.evaluate(&points[0]) == evals[0] );
    assert!(
        srs.poly_ck.powers_of_g.len() >= lagrange_tau.len(),
        "not enough powers of g in kzg_verify_g1_native"
    );
    let g1_tau = VariableBaseMSM::multi_scalar_mul(
        &srs.poly_ck.powers_of_g[..lagrange_tau.len()],
        convert_to_bigints(&lagrange_tau.coeffs).as_slice(),
    );

    // vanishing polynomial
    // z_tau[i] = polynomial equal to 0 at point[j]

    let mut z_tau = DensePoly::from_coefficients_slice(&[Fr::one()]);
    for i in 0..points.len() {
        z_tau = &z_tau * (&DensePoly::from_coefficients_slice(&[-points[i], Fr::one()]));
    }

    // commit to z_tau(X) in g2
    assert!(srs.g2_powers.len() >= z_tau.len());
    let g2_z_tau = VariableBaseMSM::multi_scalar_mul(
        &srs.g2_powers[..z_tau.len()],
        convert_to_bigints(&z_tau.coeffs).as_slice(),
    );

    let global_max_deg = srs.poly_ck.powers_of_g.len();

    let mut d: usize = 0;
    if max_deg == None {
        d += global_max_deg;
    } else {
        d += max_deg.unwrap();
    }

    let pairing1 = Bls12_381::pairing(
        c_com.into_projective() - g1_tau,
        srs.g2_powers[global_max_deg - d],
    );

    let pairing2 = Bls12_381::pairing(pi, g2_z_tau);

    return pairing1 == pairing2;
}

/*
KZG.Verify( srs_KZG, F, deg, alpha, F_alpha, pi )
Algorithm described in Section 4.6.2, KZG for Bivariate Polynomials
Be very careful here.  Verification is only valid if it is paired with a degree check.
*/
pub fn kzg_partial_verify_g1_native(
    srs: &PublicParameters,
    c_com: G1Affine, //commitment
    deg_x: usize,
    point: Fr,
    partial_eval: G1Affine,
    pi: G1Affine, //proof
) -> bool {
    let pairing1 = Bls12_381::pairing(
        c_com.into_projective() - partial_eval.into_projective(),
        srs.g2_powers[0],
    );
    let pairing2 = Bls12_381::pairing(
        pi,
        srs.g2_powers[deg_x].into_projective() - srs.g2_powers[0].mul(point),
    );

    return pairing1 == pairing2;
}

pub fn kzg_commit_g2(poly: &DensePoly<Fp256<FrParameters>>, srs: &PublicParameters) -> G2Affine {
    let mut res = srs.g2_powers[0].mul(poly[0]);
    for i in 1..poly.len() {
        res = res + srs.g2_powers[i].mul(poly[i])
    }
    return res.into_affine();
}

//////////////////////////////////////////////////////

pub fn generate_lagrange_polynomials_subset(
    positions: &Vec<usize>,
    srs: &PublicParameters,
) -> Vec<DensePoly<Fp256<FrParameters>>> {
    let mut tau_polys = vec![];
    let m = positions.len();
    for j in 0..m {
        let mut tau_j = DensePoly::from_coefficients_slice(&[Fr::one()]); //start from tau_j =1
        for k in 0..m {
            if k != j {
                //tau_j = prod_{k\neq j} (X-w^(i_k))/(w^(i_j)-w^(i_k))
                let denum = srs.domain_N.element(positions[j]) - srs.domain_N.element(positions[k]);
                tau_j = &tau_j
                    * &DensePoly::from_coefficients_slice(&[
                        -srs.domain_N.element(positions[k]) / denum, //-w^(i_k))/(w^(i_j)-w^(i_k)
                        Fr::one() / denum,                           //1//(w^(i_j)-w^(i_k))
                    ]);
            }
        }
        tau_polys.push(tau_j.clone());
    }
    tau_polys
}

/*
Algorithm for aggregating KZG proofs into a single proof
Described in Section 4.6.3 Subset openings
compute Q =\sum_{j=1}^m \frac{Q_{i_j}}}{\prod_{1\leq k\leq m,\; k\neq j}(\omega^{i_j}-\omega^{i_k})}
*/
pub fn aggregate_kzg_proofs_g2(
    openings: &Vec<G2Affine>, //Q_i
    positions: &Vec<usize>,   //i_j
    input_domain: &GeneralEvaluationDomain<Fr>,
) -> G2Affine {
    let m = positions.len();
    let mut res: G2Projective = openings[0].into_projective(); //default value

    for j in 0..m {
        let i_j = positions[j];
        let w_ij = input_domain.element(i_j);
        //1. Computing coefficient [1/prod]
        let mut prod = Fr::one();
        for k in 0..m {
            let i_k = positions[k];
            let w_ik = input_domain.element(i_k);
            if k != j {
                prod = prod * (w_ij - w_ik);
            }
        }
        //2. Summation
        let q_add = openings[i_j].mul(prod.inverse().unwrap()); //[1/prod]Q_{j}
        if j == 0 {
            res = q_add;
        } else {
            res = res + q_add;
        }
    }
    return res.into_affine();
}

//////////////////////////////////////////////////////

#[cfg(test)]
pub mod tests {

    use crate::caulk_multi_setup::setup_multi_lookup;

    use crate::multiopen::multiple_open_g2;
    use crate::tools::{
        aggregate_kzg_proofs_g2, generate_lagrange_polynomials_subset, KzgBls12_381, UniPoly381,
    };

    use ark_poly::{
        univariate::DensePolynomial as DensePoly, EvaluationDomain, Polynomial, UVPolynomial,
    };

    use ark_bls12_381::{Bls12_381, Fr, G2Affine};
    use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
    use ark_std::{One, Zero};
    use std::time::Instant;

    #[allow(non_snake_case)]
    #[test]
    pub fn test_lagrange() {
        let p: usize = 8; //bitlength of poly degree
        let max_degree: usize = (1 << p) + 2;
        let m: usize = 8;
        let N: usize = 1 << p;
        let pp = setup_multi_lookup(&max_degree, &N, &m, &p);
        let now = Instant::now();
        println!("time to setup {:?}", now.elapsed());

        let mut positions: Vec<usize> = vec![];
        for i in 0..m {
            //generate positions evenly distributed in the set
            let i_j: usize = i * (max_degree / m);
            positions.push(i_j);
        }

        let tau_polys = generate_lagrange_polynomials_subset(&positions, &pp);
        for j in 0..m {
            for k in 0..m {
                if k == j {
                    assert_eq!(
                        tau_polys[j].evaluate(&pp.domain_N.element(positions[k])),
                        Fr::one()
                    )
                } else {
                    assert_eq!(
                        tau_polys[j].evaluate(&pp.domain_N.element(positions[k])),
                        Fr::zero()
                    )
                }
            }
        }
    }

    #[allow(non_snake_case)]
    #[test]
    pub fn test_Q_g2() {
        // current kzg setup should be changed with output from a setup ceremony
        let p: usize = 6; //bitlength of poly degree
        let max_degree: usize = (1 << p) + 2;
        let actual_degree: usize = (1 << p) - 1;
        let m: usize = 1 << (p / 2);
        let N: usize = 1 << p;
        let pp = setup_multi_lookup(&max_degree, &N, &m, &p);

        // Setting up test instance to run evaluate on.
        // test randomness for c_poly is same everytime.
        // test index equals 5 everytime
        // g_c = g^(c(x))
        let rng = &mut ark_std::test_rng();
        let c_poly = UniPoly381::rand(actual_degree, rng);
        let (c_com, _) = KzgBls12_381::commit(&pp.poly_ck, &c_poly, None, None).unwrap();

        let now = Instant::now();
        let openings = multiple_open_g2(&pp.g2_powers, &c_poly, p);
        println!("Multi advanced computed in {:?}", now.elapsed());

        let mut positions: Vec<usize> = vec![];
        for i in 0..m {
            let i_j: usize = i * (max_degree / m);
            positions.push(i_j);
        }

        let now = Instant::now();

        //Compute proof
        let Q: G2Affine = aggregate_kzg_proofs_g2(&openings, &positions, &pp.domain_N);
        println!(
            "Full proof for {:?} positions computed in {:?}",
            m,
            now.elapsed()
        );

        //Compute commitment to C_I
        let mut C_I = DensePoly::from_coefficients_slice(&[Fr::zero()]); //C_I =  sum_j c_j*tau_j
        let tau_polys = generate_lagrange_polynomials_subset(&positions, &pp);
        for j in 0..m {
            C_I = &C_I + &(&tau_polys[j] * c_poly.evaluate(&pp.domain_N.element(positions[j])));
            //sum_j c_j*tau_j
        }
        let (c_I_com, _c_I_com_open) = KzgBls12_381::commit(&pp.poly_ck, &C_I, None, None).unwrap();

        //Compute commitment to z_I
        let mut z_I = DensePoly::from_coefficients_slice(&[Fr::one()]);
        for j in 0..m {
            z_I = &z_I
                * &DensePoly::from_coefficients_slice(&[
                    -pp.domain_N.element(positions[j]),
                    Fr::one(),
                ]);
        }
        let (z_I_com, _) = KzgBls12_381::commit(&pp.poly_ck, &z_I, None, None).unwrap();

        //pairing check
        let pairing1 = Bls12_381::pairing(
            (c_com.0.into_projective() - c_I_com.0.into_projective()).into_affine(),
            pp.g2_powers[0],
        );
        let pairing2 = Bls12_381::pairing(z_I_com.0, Q);
        assert_eq!(pairing1, pairing2);
    }
}
