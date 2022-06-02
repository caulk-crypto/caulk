mod dft;
mod kzg;
pub mod multi;
mod pedersen;
mod single;
mod transcript;
pub(crate) mod util;

pub use dft::*;
pub use kzg::KZGCommit;
pub use multi::PublicParameters;
pub use pedersen::PedersenParam;
pub use single::{caulk_single_prove, caulk_single_verify, setup::caulk_single_setup};
pub use transcript::CaulkTranscript;

#[cfg(test)]
mod tests {

    use crate::{
        caulk_single_prove, caulk_single_setup, caulk_single_verify, CaulkTranscript, KZGCommit,
    };
    use ark_bls12_381::{Bls12_381, Fr, G1Affine};
    use ark_ec::{AffineCurve, ProjectiveCurve};
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial,
        UVPolynomial,
    };
    use ark_poly_commit::kzg10::KZG10;
    use ark_std::{test_rng, UniformRand};

    type UniPoly381 = DensePolynomial<Fr>;
    type KzgBls12_381 = KZG10<Bls12_381, UniPoly381>;

    #[test]
    #[allow(non_snake_case)]
    fn test_caulk_single_end_to_end() {
        for p in 4..7 {
            let mut rng = test_rng();
            // setting public parameters
            // current kzg setup should be changed with output from a setup ceremony
            let max_degree: usize = (1 << p) + 2;
            let actual_degree: usize = (1 << p) - 1;

            // run the setup
            let pp = caulk_single_setup(max_degree, actual_degree, &mut rng);

            // polynomial and commitment
            // deterministic randomness.  Should never be used in practice.
            let c_poly = UniPoly381::rand(actual_degree, &mut rng);
            let (g1_C, _) = KzgBls12_381::commit(&pp.poly_ck, &c_poly, None, None).unwrap();
            let g1_C = g1_C.0;

            // point at which we will open c_com
            let input_domain: GeneralEvaluationDomain<Fr> =
                EvaluationDomain::new(actual_degree).unwrap();

            let position = 1;
            let omega_i = input_domain.element(position);

            // z = c(w_i) and cm = g^z h^r for random r
            let z = c_poly.evaluate(&omega_i);
            let r = Fr::rand(&mut rng);
            let cm = (pp.verifier_pp.pedersen_param.g.mul(z)
                + pp.verifier_pp.pedersen_param.h.mul(r))
            .into_affine();

            let mut prover_transcript = CaulkTranscript::<Fr>::new();
            let mut verifier_transcript = CaulkTranscript::<Fr>::new();

            // open single position at 0
            {
                let a = KZGCommit::open_g1_batch(&pp.poly_ck, &c_poly, None, &[omega_i]);
                let g1_q = a.1;

                // run the prover
                let proof_evaluate = caulk_single_prove(
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

                // run the verifier
                assert!(caulk_single_verify(
                    &pp.verifier_pp,
                    &mut verifier_transcript,
                    &g1_C,
                    &cm,
                    &proof_evaluate,
                ));
            }
            // compute all openings
            {
                let g1_qs = KZGCommit::<Bls12_381>::multiple_open::<G1Affine>(
                    &c_poly,
                    &pp.poly_ck.powers_of_g,
                    p,
                );
                let g1_q = g1_qs[position];

                // run the prover
                let proof_evaluate = caulk_single_prove(
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
                // run the verifier
                assert!(caulk_single_verify(
                    &pp.verifier_pp,
                    &mut verifier_transcript,
                    &g1_C,
                    &cm,
                    &proof_evaluate,
                ));
            }
        }
    }
}