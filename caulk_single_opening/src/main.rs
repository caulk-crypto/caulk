use ark_bls12_381::{Bls12_381, Fr, G1Affine};
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, Polynomial, UVPolynomial};
use ark_poly_commit::kzg10::KZG10;
use std::time::Instant;

mod caulk_single;
mod caulk_single_setup;
mod caulk_single_unity;
mod multiopen;
mod pedersen;
mod tools;

use crate::caulk_single::{caulk_single_prove, caulk_single_verify};
use crate::caulk_single_setup::caulk_single_setup;
use crate::multiopen::multiple_open;
use crate::tools::{kzg_open_g1, random_field, read_line, UniPoly381};

pub type KzgBls12_381 = KZG10<Bls12_381, UniPoly381>;

#[allow(non_snake_case)]
fn main() {
    // setting public parameters
    // current kzg setup should be changed with output from a setup ceremony
    println!("What is the bitsize of the degree of the polynomial inside the commitment? ");
    let p: usize = read_line();
    let max_degree: usize = (1 << p) + 2;
    let actual_degree: usize = (1 << p) - 1;

    // run the setup
    let now = Instant::now();
    let pp = caulk_single_setup(max_degree, actual_degree);
    println!(
        "Time to setup single openings of table size {:?} = {:?}",
        actual_degree + 1,
        now.elapsed()
    );

    //polynomial and commitment
    let now = Instant::now();
    // deterministic randomness.  Should never be used in practice.
    let rng = &mut ark_std::test_rng();
    let c_poly = UniPoly381::rand(actual_degree, rng);
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
        let a = kzg_open_g1(&pp.poly_ck, &c_poly, None, [&omega_i].to_vec());
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
    let r = random_field::<Fr>();
    let cm = (pp.ped_g.mul(z) + pp.ped_h.mul(r)).into_affine();

    // run the prover
    println!("We are now ready to run the prover.  How many times should we run it?");
    let number_of_openings: usize = read_line();
    let now = Instant::now();

    let mut proof_evaluate = caulk_single_prove(&pp, &g1_C, &cm, position, &g1_q, &z, &r);
    for _ in 1..(number_of_openings - 1) {
        proof_evaluate = caulk_single_prove(&pp, &g1_C, &cm, position, &g1_q, &z, &r);
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
        caulk_single_verify(&pp.verifier_pp, &g1_C, &cm, &proof_evaluate)
    );
    let now = Instant::now();
    for _ in 0..(number_of_openings - 1) {
        caulk_single_verify(&pp.verifier_pp, &g1_C, &cm, &proof_evaluate);
    }
    println!(
        "Time to verify {} single openings of table size {:?} = {:?}",
        number_of_openings,
        actual_degree + 1,
        now.elapsed()
    );
}
