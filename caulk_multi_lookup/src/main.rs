mod caulk_multi_setup;
mod caulk_multi_unity;
mod tools;
mod caulk_multi_lookup;
mod multiopen;

use crate::tools::{read_line, KzgBls12_381, random_field};
use crate::caulk_multi_setup::setup_multi_lookup;
use crate::caulk_multi_lookup::{LookupProverInput, LookupInstance,
    get_poly_and_g2_openings,
    compute_lookup_proof, verify_lookup_proof};

use ark_poly_commit::{Polynomial, UVPolynomial};
use ark_bls12_381::{Fr, FrParameters};
use ark_ff::Fp256;
use ark_std::time::Instant;
use ark_poly::{EvaluationDomain, univariate::DensePolynomial};

use std::cmp::max;
use rand::Rng;

#[allow(non_snake_case)]
fn main() {

    //1. Setup
    // setting public parameters
    // current kzg setup should be changed with output from a setup ceremony
    println!("What is the bitsize of the degree of the polynomial inside the commitment? ");
    let n: usize = read_line();
    println!("How many positions m do you want to open the polynomial at? ");
    let m: usize = read_line();


    let N: usize = 1 << n;
    let powers_size: usize = max( N + 2,  1024 ) ;
    let actual_degree = N - 1;
    let temp_m = n; //dummy

    let now = Instant::now();
    let mut pp =setup_multi_lookup(&powers_size, &N, &temp_m, &n);
    println!("Time to setup multi openings of table size {:?} = {:?}", actual_degree + 1, now.elapsed());

    //2. Poly and openings
    let now = Instant::now();
    let table=get_poly_and_g2_openings(&pp, actual_degree);
    println!("Time to generate commitment table = {:?}", now.elapsed());

    //3. Setup



    pp.regenerate_lookup_params(m);

    //4. Positions
    let mut rng = rand::thread_rng();
    let mut positions: Vec<usize> = vec![];
    for _ in 0..m { //generate positions randomly in the set
        //let i_j: usize = j*(actual_degree/m);
        let i_j: usize = rng.gen_range(0,actual_degree);
        positions.push(i_j);
    };

    println!("positions = {:?}", positions);

    //5. generating phi
    let blinder: Fp256<FrParameters> = random_field::<Fr>();
    let a_m = DensePolynomial::from_coefficients_slice(&[blinder]);
    let mut phi_poly = a_m.mul_by_vanishing_poly(pp.domain_m);
    let c_poly_local = table.c_poly.clone();

    for j in 0..m
    {
        phi_poly = &phi_poly +
        &(&pp.lagrange_polynomials_m[j]
            * c_poly_local.evaluate(&pp.domain_N.element(positions[j])));  //adding c(w^{i_j})*mu_j(X)
    }

    for j in m..pp.domain_m.size()
    {
        phi_poly = &phi_poly +
        &(&pp.lagrange_polynomials_m[j]
            * c_poly_local.evaluate( &pp.domain_N.element(0) ) );  //adding c(w^{i_j})*mu_j(X)
    }

    //6. Running proofs
    let now = Instant::now();
    let (c_com, _) = KzgBls12_381::commit(&pp.poly_ck, &table.c_poly, None, None).unwrap();
    let (phi_com, _) = KzgBls12_381::commit(&pp.poly_ck, &phi_poly, None, None).unwrap();
    println!("Time to generate inputs = {:?}", now.elapsed());

    let lookup_instance = LookupInstance{
        c_com: c_com.0.clone(),
        phi_com: phi_com.0.clone(),
    };

    let prover_input = LookupProverInput{
        c_poly: table.c_poly.clone(),
        phi_poly:phi_poly,
        positions: positions,
        openings: table.openings.clone()};

    println!("We are now ready to run the prover.  How many times should we run it?" );
    let number_of_openings: usize = read_line();
    let now = Instant::now();
    let (proof, unity_proof) = compute_lookup_proof(&lookup_instance, &prover_input,&pp);
    for _ in 1..number_of_openings {
        _ = compute_lookup_proof(&lookup_instance, &prover_input,&pp);
    }
    println!("Time to evaluate {} times {} multi-openings of table size {:?} = {:?} ", number_of_openings, m, N, now.elapsed());

    let now = Instant::now();
    for _ in 0..number_of_openings {
        verify_lookup_proof(table.c_com, phi_com.0, &proof, &unity_proof, &pp);
    }
    println!("Time to verify {} times {} multi-openings of table size {:?} = {:?} ", number_of_openings, m, N, now.elapsed());


    assert!(verify_lookup_proof(table.c_com, phi_com.0, &proof, &unity_proof, &pp), "Result does not verify");

    }
