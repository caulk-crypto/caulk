use ark_bls12_381::{Bls12_381, Fr, G1Affine};
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial};
use ark_poly_commit::kzg10::KZG10;
use ark_std::test_rng;
use ark_std::UniformRand;
use caulk_single_opening::caulk_single_setup;
use caulk_single_opening::kzg_open_g1;
use caulk_single_opening::multiple_open;
use caulk_single_opening::CaulkTranscript;
use caulk_single_opening::{caulk_single_prove, caulk_single_verify};
use std::time::Instant;
use std::{error::Error, io, str::FromStr};

type UniPoly381 = DensePolynomial<Fr>;
type KzgBls12_381 = KZG10<Bls12_381, UniPoly381>;

// Function for reading inputs from the command line.
fn read_line<T: FromStr>() -> T
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

#[allow(non_snake_case)]
fn main() {
    let mut rng = test_rng();

    // setting public parameters
    // current kzg setup should be changed with output from a setup ceremony
    println!("What is the bitsize of the degree of the polynomial inside the commitment? ");
    let p: usize = read_line();
    let max_degree: usize = (1 << p) + 2;
    let actual_degree: usize = (1 << p) - 1;

    // run the setup
    let now = Instant::now();
    let pp = caulk_single_setup(max_degree, actual_degree, &mut rng);
    println!(
        "Time to setup single openings of table size {:?} = {:?}",
        actual_degree + 1,
        now.elapsed()
    );

    //polynomial and commitment
    let now = Instant::now();
    // deterministic randomness.  Should never be used in practice.
    let c_poly = UniPoly381::rand(actual_degree, &mut rng);
    let (g1_C, _) = KzgBls12_381::commit(&pp.poly_ck, &c_poly, None, None).unwrap();
    let g1_C = g1_C.0;
    println!(
        "Time to KZG commit one element from table size {:?} = {:?}",
        actual_degree + 1,
        now.elapsed()
    );

    //point at which we will open c_com
    let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(actual_degree).unwrap();
    println!("Which position in the vector should we open at? ");
    let position: usize = read_line();
    assert!(0 < position, "This position does not exist in this vector.");
    assert!(
        position <= (actual_degree + 1),
        "This position does not exist in this vector."
    );
    let omega_i = input_domain.element(position);

    //Deciding whether to open all positions or just the one position.
    println!("Should we open all possible positions? Opening all possible positions is slow.  Please input either YES or NO" );
    let open_all: String = read_line();

    let g1_q: G1Affine;
    if (open_all == "NO") || (open_all == "No") || (open_all == "no") {
        // Q = g1_q = g^( (c(x) - c(w_i)) / (x - w_i) )
        let now = Instant::now();
        let a = kzg_open_g1(&pp.poly_ck, &c_poly, None, &[omega_i]);
        println!(
            "Time to KZG open one element from table size {:?} = {:?}",
            actual_degree + 1,
            now.elapsed()
        );
        g1_q = a.1;
    } else {
        assert!(
            (open_all == "YES") || (open_all == "Yes") || (open_all == "yes"),
            "Console input is invalid"
        );

        //compute all openings
        let now = Instant::now();
        let g1_qs = multiple_open(&c_poly, &pp.poly_ck, p);
        g1_q = g1_qs[position];
        println!("Time to compute all KZG openings {:?}", now.elapsed());
    }

    // z = c(w_i) and cm = g^z h^r for random r
    let z = c_poly.evaluate(&omega_i);
    let r = Fr::rand(&mut rng);
    let cm = (pp.pedersen_param.g.mul(z) + pp.pedersen_param.h.mul(r)).into_affine();

    let mut prover_transcript = CaulkTranscript::<Fr>::new();
    let mut verifier_transcript = CaulkTranscript::<Fr>::new();

    // run the prover
    println!("We are now ready to run the prover.  How many times should we run it?");
    let number_of_openings: usize = read_line();
    let now = Instant::now();

    let mut proof_evaluate = caulk_single_prove(
        &pp,
        &mut prover_transcript,
        &g1_C,
        &cm,
        position,
        &g1_q,
        &z,
        &r,
        &mut rng,
    );
    for _ in 1..(number_of_openings - 1) {
        proof_evaluate = caulk_single_prove(
            &pp,
            &mut prover_transcript,
            &g1_C,
            &cm,
            position,
            &g1_q,
            &z,
            &r,
            &mut rng,
        );
    }
    println!(
        "Time to evaluate {} single openings of table size {:?} = {:?}",
        number_of_openings,
        actual_degree + 1,
        now.elapsed()
    );

    // run the verifier
    println!(
        "The proof verifies = {:?}",
        caulk_single_verify(
            &pp.verifier_pp,
            &mut verifier_transcript,
            &g1_C,
            &cm,
            &proof_evaluate,
        )
    );
    let now = Instant::now();
    for _ in 0..(number_of_openings - 1) {
        caulk_single_verify(
            &pp.verifier_pp,
            &mut verifier_transcript,
            &g1_C,
            &cm,
            &proof_evaluate,
        );
    }
    println!(
        "Time to verify {} single openings of table size {:?} = {:?}",
        number_of_openings,
        actual_degree + 1,
        now.elapsed()
    );
}
