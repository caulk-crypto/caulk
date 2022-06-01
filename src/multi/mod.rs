// This file includes the Caulk prover and verifier for single openings.
// The protocol is described in Figure 3.

pub mod setup;
mod unity;

use crate::{kzg::generate_lagrange_polynomials_subset, CaulkTranscript, KZGCommit};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, PrimeField};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Evaluations as EvaluationsOnDomain, Evaluations,
    GeneralEvaluationDomain, Polynomial, UVPolynomial,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{cfg_into_iter, rand::RngCore, One, UniformRand, Zero};
pub use setup::PublicParameters;
use std::{
    convert::TryInto,
    fs::File,
    io::{Read, Write},
    time::Instant,
    vec::Vec,
};
use unity::{prove_multiunity, verify_multiunity, ProofMultiUnity};

pub struct LookupInstance<C: AffineCurve> {
    pub c_com: C,   // polynomial C(X) that represents a table
    pub phi_com: C, // polynomial phi(X) that represents the values to look up
}

pub struct LookupProverInput<E: PairingEngine> {
    pub c_poly: DensePolynomial<E::Fr>, // polynomial C(X) that represents a table
    pub phi_poly: DensePolynomial<E::Fr>, // polynomial phi(X) that represents the values to look up
    pub positions: Vec<usize>,          //
    pub openings: Vec<E::G2Affine>,
}

#[derive(Debug, PartialEq)]
// Data structure to be stored in a file: polynomial, its commitment, and its
// openings (for certain SRS)
pub struct TableInput<E: PairingEngine> {
    pub c_poly: DensePolynomial<E::Fr>,
    pub c_com: E::G1Affine,
    pub openings: Vec<E::G2Affine>,
}

// Lookup proof data structure
#[allow(non_snake_case)]
pub struct LookupProof<E: PairingEngine> {
    pub C_I_com: E::G1Affine, // Commitment to C_I(X)
    pub H1_com: E::G2Affine,  // Commitment to H_1(X)
    pub H2_com: E::G1Affine,  // Commitment to H_2(X)
    pub u_com: E::G1Affine,   // Commitment to u(X)
    pub z_I_com: E::G1Affine, // Commitment to z_I(X)
    pub v1: E::Fr,
    pub v2: E::Fr,
    pub pi1: E::G1Affine,
    pub pi2: E::G1Affine,
    pub pi3: E::G1Affine,
}

impl<E: PairingEngine> TableInput<E> {
    fn store(&self, path: &str) {
        // 1. Polynomial
        let mut o_bytes = vec![];
        let mut f = File::create(path).expect("Unable to create file");
        let len: u32 = self.c_poly.len().try_into().unwrap();
        let len_bytes = len.to_be_bytes();
        f.write_all(&len_bytes).expect("Unable to write data");
        let len32: usize = len.try_into().unwrap();
        for i in 0..len32 {
            self.c_poly.coeffs[i]
                .serialize_uncompressed(&mut o_bytes)
                .ok();
        }
        f.write_all(&o_bytes).expect("Unable to write data");

        // 2. Commitment
        o_bytes.clear();
        self.c_com.serialize_uncompressed(&mut o_bytes).ok();
        f.write_all(&o_bytes).expect("Unable to write data");

        // 3. Openings
        o_bytes.clear();
        let len: u32 = self.openings.len().try_into().unwrap();
        let len_bytes = len.to_be_bytes();
        f.write_all(&len_bytes).expect("Unable to write data");
        let len32: usize = len.try_into().unwrap();
        for i in 0..len32 {
            self.openings[i].serialize_uncompressed(&mut o_bytes).ok();
        }
        f.write_all(&o_bytes).expect("Unable to write data");
    }

    fn load(path: &str) -> TableInput<E> {
        const FR_UNCOMPR_SIZE: usize = 32;
        const G1_UNCOMPR_SIZE: usize = 96;
        const G2_UNCOMPR_SIZE: usize = 192;
        let mut data = Vec::new();
        let mut f = File::open(path).expect("Unable to open file");
        f.read_to_end(&mut data).expect("Unable to read data");

        // 1. reading  c_poly
        let mut cur_counter: usize = 0;
        let len_bytes: [u8; 4] = (&data[0..4]).try_into().unwrap();
        let len: u32 = u32::from_be_bytes(len_bytes);
        let mut coeffs = vec![];
        let len32: usize = len.try_into().unwrap();
        cur_counter += 4;
        for i in 0..len32 {
            let buf_bytes =
                &data[cur_counter + i * FR_UNCOMPR_SIZE..cur_counter + (i + 1) * FR_UNCOMPR_SIZE];
            let tmp = E::Fr::deserialize_unchecked(buf_bytes).unwrap();
            coeffs.push(tmp);
        }
        cur_counter += len32 * FR_UNCOMPR_SIZE;

        // 2. c_com
        let buf_bytes = &data[cur_counter..cur_counter + G1_UNCOMPR_SIZE];
        let c_com = E::G1Affine::deserialize_unchecked(buf_bytes).unwrap();
        cur_counter += G1_UNCOMPR_SIZE;

        // 3 openings
        let len_bytes: [u8; 4] = (&data[cur_counter..cur_counter + 4]).try_into().unwrap();
        let len: u32 = u32::from_be_bytes(len_bytes);
        let mut openings = vec![];
        let len32: usize = len.try_into().unwrap();
        cur_counter += 4;
        for _ in 0..len32 {
            let buf_bytes = &data[cur_counter..cur_counter + G2_UNCOMPR_SIZE];
            let tmp = E::G2Affine::deserialize_unchecked(buf_bytes).unwrap();
            openings.push(tmp);
            cur_counter += G2_UNCOMPR_SIZE;
        }

        return TableInput {
            c_poly: DensePolynomial { coeffs },
            c_com,
            openings,
        };
    }
}

#[allow(non_snake_case)]
pub fn compute_lookup_proof<E: PairingEngine, R: RngCore>(
    instance: &LookupInstance<E::G1Affine>,
    input: &LookupProverInput<E>,
    srs: &PublicParameters<E>,
    rng: &mut R,
) -> (LookupProof<E>, ProofMultiUnity<E>) {
    let m = input.positions.len();

    ///////////////////////////////////////////////////////////////////
    // 1. Blinders
    ///////////////////////////////////////////////////////////////////

    // provers blinders for zero-knowledge
    let r1 = E::Fr::rand(rng);
    let r2 = E::Fr::rand(rng);
    let r3 = E::Fr::rand(rng);
    let r4 = E::Fr::rand(rng);
    let r5 = E::Fr::rand(rng);
    let r6 = E::Fr::rand(rng);
    let r7 = E::Fr::rand(rng);

    ///////////////////////////////////////////////////////////////////
    // 2. Compute z_I(X) = r1 prod_{i in I} (X - w^i)
    ///////////////////////////////////////////////////////////////////

    // z_I includes each position only once.
    let mut positions_no_repeats = Vec::new();
    for i in 0..input.positions.len() {
        if positions_no_repeats.contains(&input.positions[i]) {
        } else {
            positions_no_repeats.push(input.positions[i]);
        }
    }

    // insert 0 into z_I so that we can pad when m is not a power of 2.
    if positions_no_repeats.contains(&(0 as usize)) {
    } else {
        positions_no_repeats.push(0 as usize);
    }

    // z_I(X)
    let mut z_I = DensePolynomial::from_coefficients_slice(&[r1]);
    for j in 0..positions_no_repeats.len() {
        z_I = &z_I
            * &DensePolynomial::from_coefficients_slice(&[
                -srs.domain_N.element(positions_no_repeats[j]),
                E::Fr::one(),
            ]);
    }

    ///////////////////////////////////////////////////////////////////
    // 2. Compute C_I(X) = (r_2+r_3X + r4X^2)*Z_I(X) + sum_j c_j*tau_j(X)
    ///////////////////////////////////////////////////////////////////

    let mut c_I_poly = DensePolynomial::from_coefficients_slice(&[E::Fr::zero()]);

    // tau_polys[i] = 1 at positions_no_repeats[i] and 0 at positions_no_repeats[j]
    // Takes m^2 time, or 36ms when m = 32.  Can be done in m log^2(m) time if this
    // ever becomes a bottleneck. See https://people.csail.mit.edu/devadas/pubs/scalable_thresh.pdf
    let tau_polys = generate_lagrange_polynomials_subset(&positions_no_repeats, srs);

    // C_I(X) =  sum_j c_j*tau_j(X)
    // Takes m^2 time, or 38ms when m = 32.  Can be done faster if we store c_poly
    // evaluations.
    for j in 0..positions_no_repeats.len() {
        c_I_poly = &c_I_poly
            + &(&tau_polys[j]
                * input
                    .c_poly
                    .evaluate(&srs.domain_N.element(positions_no_repeats[j]))); // sum_j c_j*tau_j
    }

    // extra_blinder = r2 + r3 X + r4 X^2
    let extra_blinder = DensePolynomial::from_coefficients_slice(&[r2, r3, r4]);

    // C_I(X) =  C_I(X) + z_I(X) * (r2 + r3 X + r4 X^2)
    c_I_poly = &c_I_poly + &(&z_I * &extra_blinder);

    ///////////////////////////////////////////////////////////////////
    // 4. Compute H1
    ///////////////////////////////////////////////////////////////////

    // Compute [Q(x)]_2 by aggregating kzg proofs such that
    // Q(X) = (  C(X) - sum_{i in I} c_{i+1} tau_i(X)  ) /  ( prod_{i in I} (X -
    // w^i) )
    let g2_Q =
        KZGCommit::<E>::aggregate_proof_g2(&input.openings, &positions_no_repeats, &srs.domain_N);

    // blind_com = [ r2 + r3 x + r4 x^2 ]_2
    let blind_com = KZGCommit::<E>::commit_g2(&srs.g2_powers, &extra_blinder);

    // H1_com = [ r1^{-1} Q(x) ]_2 - blind_com
    let H1_com = (g2_Q.mul(r1.inverse().unwrap()) - blind_com.into_projective()).into_affine();

    ///////////////////////////////////////////////////////////////////
    // 5. Compute u(X) = sum_j w^{i_j} mu_j(X) + (r5 + r6 X + r7 X^2) z_{Vm}(X)
    ///////////////////////////////////////////////////////////////////

    // u(X) = sum_j w^{i_j} mu_j(X)
    let mut u_vals = vec![];
    for j in 0..m {
        u_vals.push(srs.domain_N.element(input.positions[j]));
    }

    // u(X) = u(X) + (r5 + r6 X + r7 X^2) z_{Vm}(X)
    let extra_blinder2 = DensePolynomial::from_coefficients_slice(&[r5, r6, r7]);
    let u_poly = &EvaluationsOnDomain::from_vec_and_domain(u_vals.clone(), srs.domain_m)
        .interpolate()
        + &(extra_blinder2.mul_by_vanishing_poly(srs.domain_m));

    ///////////////////////////////////////////////////////////////////
    // 6. Commitments
    ///////////////////////////////////////////////////////////////////
    let z_I_com = KZGCommit::<E>::commit_g1(&srs.poly_ck, &z_I);
    let C_I_com = KZGCommit::<E>::commit_g1(&srs.poly_ck, &c_I_poly);
    let u_com = KZGCommit::<E>::commit_g1(&srs.poly_ck, &u_poly);

    ///////////////////////////////////////////////////////////////////
    // 7 Prepare unity proof
    ///////////////////////////////////////////////////////////////////

    // transcript initialised to zero
    let mut transcript = CaulkTranscript::new();

    // let now = Instant::now();
    let unity_proof = prove_multiunity(
        &srs,
        &mut transcript,
        &u_com,
        u_vals.clone(),
        extra_blinder2,
    );
    // println!("Time to prove unity  {:?}",  now.elapsed());

    // quick test can be uncommented to check if unity proof verifies
    // let unity_check = verify_multiunity( &srs, &mut Fr::zero(), u_com.0.clone(),
    // &unity_proof ); println!("unity_check = {}", unity_check);

    ///////////////////////////////////////////////////////////////////
    // 8. Hash outputs to get chi
    ///////////////////////////////////////////////////////////////////

    transcript.append_element(b"c_com", &instance.c_com);
    transcript.append_element(b"phi_com", &instance.phi_com);
    transcript.append_element(b"u_bar_alpha", &unity_proof.g1_u_bar_alpha);
    transcript.append_element(b"h2_alpha", &unity_proof.g1_h_2_alpha);
    transcript.append_element(b"pi_1", &unity_proof.pi_1);
    transcript.append_element(b"pi_2", &unity_proof.pi_2);
    transcript.append_element(b"pi_3", &unity_proof.pi_3);
    transcript.append_element(b"pi_4", &unity_proof.pi_4);
    transcript.append_element(b"pi_5", &unity_proof.pi_5);
    transcript.append_element(b"C_I_com", &C_I_com);
    transcript.append_element(b"z_I_com", &z_I_com);
    transcript.append_element(b"u_com", &u_com);

    transcript.append_element(b"h1_com", &H1_com);

    transcript.append_element(b"v1", &unity_proof.v1);
    transcript.append_element(b"v2", &unity_proof.v2);
    transcript.append_element(b"v3", &unity_proof.v3);

    let chi = transcript.get_and_append_challenge(b"chi");

    ///////////////////////////////////////////////////////////////////
    // 9. Compute z_I( u(X) )
    ///////////////////////////////////////////////////////////////////

    // Need a bigger domain to compute z_I(u(X)) over.
    // Has size O(m^2)
    let domain_m_sq: GeneralEvaluationDomain<E::Fr> =
        GeneralEvaluationDomain::new(z_I.len() * u_poly.len() + 2).unwrap();

    // id_poly(X) = 0 for sigma_i < m and 1 for sigma_i > m
    // used for when m is not a power of 2
    let mut id_poly = DensePolynomial::from_coefficients_slice(&[E::Fr::one()]);
    id_poly = &id_poly - &srs.id_poly;

    // Compute z_I( u(X) + w^0 id(X) )
    // Computing z_I(u(X)) is done naively and could be faster.  Currently this is
    // not a bottleneck
    let evals: Vec<E::Fr> = cfg_into_iter!(0..domain_m_sq.size())
        .map(|k| {
            z_I.evaluate(
                &(u_poly.evaluate(&domain_m_sq.element(k))
                    + id_poly.evaluate(&domain_m_sq.element(k))),
            )
        })
        .collect();
    let z_I_u_poly = Evaluations::from_vec_and_domain(evals, domain_m_sq).interpolate();

    ///////////////////////////////////////////////////////////////////
    // 10. Compute C_I(u(X))-phi(X)
    ///////////////////////////////////////////////////////////////////

    // Compute C_I( u(X) )
    // Computing C_I(u(X)) is done naively and could be faster.  Currently this is
    // not a bottleneck

    // Actually compute c_I( u(X) + id(X) ) in case m is not a power of 2
    let evals: Vec<E::Fr> = cfg_into_iter!(0..domain_m_sq.size())
        .map(|k| {
            c_I_poly.evaluate(
                &(u_poly.evaluate(&domain_m_sq.element(k))
                    + id_poly.evaluate(&domain_m_sq.element(k))),
            )
        })
        .collect();

    // c_I_u_poly =  C_I( u(X) ) - phi(X)
    let c_I_u_poly =
        &Evaluations::from_vec_and_domain(evals, domain_m_sq).interpolate() - &input.phi_poly;

    ///////////////////////////////////////////////////////////////////
    // 11. Compute H2
    ///////////////////////////////////////////////////////////////////

    // temp_poly(X) = z_I(u(X)) + chi [ C_I(u(X)) - phi(X) ]
    let temp_poly = &z_I_u_poly + &(&c_I_u_poly * chi);

    // H2(X) = temp_poly / z_Vm(X)
    let (H2_poly, rem) = temp_poly.divide_by_vanishing_poly(srs.domain_m).unwrap();
    assert!(
        rem == DensePolynomial::from_coefficients_slice(&[E::Fr::zero()]),
        "H_2(X) doesn't divide"
    );

    ///////////////////////////////////////////////////////////////////
    // 12. Compute commitments to H2
    ///////////////////////////////////////////////////////////////////
    // let now = Instant::now();
    let H2_com = KZGCommit::<E>::commit_g1(&srs.poly_ck, &H2_poly);
    // println!("Time to commit to H2  {:?}",  now.elapsed());

    ///////////////////////////////////////////////////////////////////
    // 13. Hash outputs to get alpha
    ///////////////////////////////////////////////////////////////////
    transcript.append_element(b"h2", &H2_com);
    let alpha = transcript.get_and_append_challenge(b"alpha");

    // last hash so don't need to update hash_input
    // hash_input = alpha.clone();

    ///////////////////////////////////////////////////////////////////
    // 14. Open u at alpha, get v1
    ///////////////////////////////////////////////////////////////////
    let (evals1, pi1) = KZGCommit::<E>::open_g1_batch(&srs.poly_ck, &u_poly, None, &[alpha]);
    let v1 = evals1[0];

    ///////////////////////////////////////////////////////////////////
    // 15. Compute p1(X) and open  at v1
    ///////////////////////////////////////////////////////////////////

    // v1_id = u(alpha) + id(alpha) for when m is not a power of 2
    let v1_id = v1 + id_poly.evaluate(&alpha);

    // p1(X) = z_IX() + chi cI(X)
    let p1_poly = &z_I + &(&c_I_poly * chi);

    let (evals2, pi2) = KZGCommit::<E>::open_g1_batch(&srs.poly_ck, &p1_poly, None, &[v1_id]);

    ///////////////////////////////////////////////////////////////////
    // 16. Compute p2(X) and open p2 at alpha
    ///////////////////////////////////////////////////////////////////

    // p2(X) = zI(u(alpha)) + chi C_I( u(alpha) )
    let mut p2_poly = DensePolynomial::from_coefficients_slice(&[
        z_I.evaluate(&v1_id) + chi * c_I_poly.evaluate(&v1_id)
    ]);

    // p2(X) = p2(X) - chi phi(X)
    p2_poly = &p2_poly - &(&input.phi_poly * chi);

    // p2(X) = p2(X) - zVm(alpha) H2(X)
    let zVm: DensePolynomial<E::Fr> = srs.domain_m.vanishing_polynomial().into();

    p2_poly = &p2_poly - &(&H2_poly * zVm.evaluate(&alpha));

    // Open p2(X) at alpha
    let (evals3, pi3) = KZGCommit::<E>::open_g1_batch(&srs.poly_ck, &p2_poly, None, &[alpha]);

    // check that p2_poly(alpha) = 0
    assert!(evals3[0] == E::Fr::zero(), "p2(alpha) does not equal 0");

    ///////////////////////////////////////////////////////////////////
    // 17. Compose proof
    ///////////////////////////////////////////////////////////////////
    let proof = LookupProof {
        C_I_com,
        H1_com,
        H2_com,
        z_I_com,
        u_com,
        v1,
        v2: evals2[0],
        pi1,
        pi2,
        pi3,
    };

    (proof, unity_proof)
}

#[allow(non_snake_case)]
pub fn verify_lookup_proof<E: PairingEngine>(
    c_com: &E::G1Affine,
    phi_com: &E::G1Affine,
    proof: &LookupProof<E>,
    unity_proof: &ProofMultiUnity<E>,
    srs: &PublicParameters<E>,
) -> bool {
    ///////////////////////////////////////////////////////////////////
    // 1. check unity
    ///////////////////////////////////////////////////////////////////

    // hash_input initialised to zero
    let mut transcript = CaulkTranscript::new();

    let unity_check = verify_multiunity(srs, &mut transcript, &proof.u_com, unity_proof);
    assert!(unity_check, "failure on unity");

    ///////////////////////////////////////////////////////////////////
    // 2. Hash outputs to get chi
    ///////////////////////////////////////////////////////////////////

    transcript.append_element(b"c_com", c_com);
    transcript.append_element(b"phi_com", phi_com);
    transcript.append_element(b"u_bar_alpha", &unity_proof.g1_u_bar_alpha);
    transcript.append_element(b"h2_alpha", &unity_proof.g1_h_2_alpha);
    transcript.append_element(b"pi_1", &unity_proof.pi_1);
    transcript.append_element(b"pi_2", &unity_proof.pi_2);
    transcript.append_element(b"pi_3", &unity_proof.pi_3);
    transcript.append_element(b"pi_4", &unity_proof.pi_4);
    transcript.append_element(b"pi_5", &unity_proof.pi_5);
    transcript.append_element(b"C_I_com", &proof.C_I_com);
    transcript.append_element(b"z_I_com", &proof.z_I_com);
    transcript.append_element(b"u_com", &proof.u_com);

    transcript.append_element(b"h1_com", &proof.H1_com);

    transcript.append_element(b"v1", &unity_proof.v1);
    transcript.append_element(b"v2", &unity_proof.v2);
    transcript.append_element(b"v3", &unity_proof.v3);

    let chi = transcript.get_and_append_challenge(b"chi");

    ///////////////////////////////////////////////////////////////////
    // 3. Hash outputs to get alpha
    ///////////////////////////////////////////////////////////////////
    transcript.append_element(b"h2", &proof.H2_com);
    let alpha = transcript.get_and_append_challenge(b"alpha");

    // last hash so don't need to update hash_input
    // hash_input = alpha.clone();

    ///////////////////////////////////////////////////////////////////
    // 4. Check pi_1
    ///////////////////////////////////////////////////////////////////

    // KZG.Verify(srs_KZG, [u]_1, deg = bot, alpha, v1, pi1)
    let check1 = KZGCommit::<E>::verify_g1(
        &srs.poly_ck.powers_of_g,
        &srs.g2_powers,
        &proof.u_com,
        None,
        &[alpha],
        &[proof.v1],
        &proof.pi1,
    );

    assert!(check1, "failure on pi_1 check");

    ///////////////////////////////////////////////////////////////////
    // 5. Check pi_2
    ///////////////////////////////////////////////////////////////////

    // v1_id = u(alpha)+ id(alpha) for when m is not a power of 2
    let v1_id = proof.v1 + (E::Fr::one() - srs.id_poly.evaluate(&alpha));

    // [P1]_1 = [z_I]_1 + chi [c_I]_1
    let p1_com = (proof.z_I_com.into_projective() + proof.C_I_com.mul(chi)).into_affine();

    // KZG.Verify(srs_KZG, [P1]_1, deg = bot, v1_id, v2, pi2)
    let check2 = KZGCommit::<E>::verify_g1(
        &srs.poly_ck.powers_of_g,
        &srs.g2_powers,
        &p1_com,
        None,
        &[v1_id],
        &[proof.v2],
        &proof.pi2,
    );
    assert!(check2, "failure on pi_2 check");

    ///////////////////////////////////////////////////////////////////
    // 6. Check pi_3
    ///////////////////////////////////////////////////////////////////

    // z_Vm(X)
    let zVm: DensePolynomial<E::Fr> = srs.domain_m.vanishing_polynomial().into(); // z_V_m(alpah)

    // [P2]_1 = [v2]_1 - chi cm - zVm(alpha) [H_2]_1
    let p2_com = (
        srs.poly_ck.powers_of_g[0].mul(proof.v2 )   // [v2]_1
                - phi_com.mul( chi )    //[phi]_1
                - proof.H2_com.mul(zVm.evaluate(&alpha))
        // [H2]_1 * zVm(alpha)
    )
    .into_affine();

    // KZG.Verify(srs_KZG, [P2]_1, deg = bot, alpha, 0, pi3)
    let check3 = KZGCommit::<E>::verify_g1(
        &srs.poly_ck.powers_of_g,
        &srs.g2_powers,
        &p2_com,
        None,
        &[alpha],
        &[E::Fr::zero()],
        &proof.pi3,
    );
    assert!(check3, "failure on check 3");

    ///////////////////////////////////////////////////////////////////
    // 7. Check final pairing
    ///////////////////////////////////////////////////////////////////

    // pairing1 = e([C]_1 - [C_I]_1, [1]_2)
    let pairing1 = E::pairing(
        (c_com.into_projective() - proof.C_I_com.into_projective()).into_affine(),
        srs.g2_powers[0],
    );

    // pairing2 = e([z_I]_1, [H_1]_2)
    let pairing2 = E::pairing(proof.z_I_com, proof.H1_com);

    assert!(pairing1 == pairing2, "failure on pairing check");

    return true;
}

#[allow(non_snake_case)]
#[allow(dead_code)]
pub fn generate_lookup_input<E: PairingEngine, R: RngCore>(
    rng: &mut R,
) -> (
    LookupProverInput<E>,
    PublicParameters<E>, // SRS
) {
    let n: usize = 8; // bitlength of poly degree
    let m: usize = 4;
    // let m: usize = (1<<(n/2-1)); //should be power of 2
    let N: usize = 1 << n;
    let max_degree: usize = if N > 2 * m * m { N - 1 } else { 2 * m * m };
    let actual_degree = N - 1;
    let now = Instant::now();
    let pp = PublicParameters::<E>::setup(&max_degree, &N, &m, &n);
    println!("Time to setup {:?}", now.elapsed());

    let c_poly = DensePolynomial::<E::Fr>::rand(actual_degree, rng);

    let mut positions: Vec<usize> = vec![];
    for j in 0..m {
        // generate positions evenly distributed in the set
        let i_j: usize = j * (N / m);
        positions.push(i_j);
    }

    // generating phi
    let blinder = E::Fr::rand(rng);
    let a_m = DensePolynomial::from_coefficients_slice(&[blinder]);
    let mut phi_poly = a_m.mul_by_vanishing_poly(pp.domain_m);
    for j in 0..m {
        phi_poly = &phi_poly
            + &(&pp.lagrange_polynomials_m[j]
                * c_poly.evaluate(&pp.domain_N.element(positions[j]))); // adding c(w^{i_j})*mu_j(X)
    }

    for j in m..pp.domain_m.size() {
        phi_poly =
            &phi_poly + &(&pp.lagrange_polynomials_m[j] * c_poly.evaluate(&pp.domain_N.element(0)));
    }

    let now = Instant::now();
    let openings = KZGCommit::<E>::multiple_open::<E::G2Affine>(&c_poly, &pp.g2_powers, n);
    println!("Time to generate openings {:?}", now.elapsed());

    return (
        LookupProverInput {
            c_poly,
            phi_poly,
            positions,
            openings,
        },
        pp,
    );
}

pub fn get_poly_and_g2_openings<E: PairingEngine>(
    pp: &PublicParameters<E>,
    actual_degree: usize,
) -> TableInput<E> {
    // try opening the file. If it exists load the setup from there, otherwise
    // generate
    let path = format!(
        "polys/poly_{}_openings_{}_{}.setup",
        actual_degree,
        pp.N,
        E::Fq::size_in_bits()
    );
    let res = File::open(path.clone());
    match res {
        Ok(_) => {
            let now = Instant::now();
            let table = TableInput::load(&path);
            println!("Time to load openings = {:?}", now.elapsed());
            return table;
        },
        Err(_) => {
            let rng = &mut ark_std::test_rng();
            let c_poly = DensePolynomial::<E::Fr>::rand(actual_degree, rng);
            let c_comx = KZGCommit::<E>::commit_g1(&pp.poly_ck, &c_poly);
            let now = Instant::now();
            let openings =
                KZGCommit::<E>::multiple_open::<E::G2Affine>(&c_poly, &pp.g2_powers, pp.n);
            println!("Time to generate openings = {:?}", now.elapsed());
            let table = TableInput {
                c_poly,
                c_com: c_comx,
                openings,
            };
            table.store(&path);
            return table;
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_377::Bls12_377;
    use ark_bls12_381::Bls12_381;
    use ark_ff::PrimeField;

    #[test]
    fn test_store() {
        test_store_helper::<Bls12_381>();
        test_store_helper::<Bls12_377>();
    }

    #[allow(non_snake_case)]
    pub fn test_store_helper<E: PairingEngine>() {
        // 1. Setup
        let n: usize = 6;
        let N: usize = 1 << n;
        let powers_size: usize = N + 2; // SRS SIZE
        let temp_m = n; // dummy
        let pp = PublicParameters::<E>::setup(&powers_size, &N, &temp_m, &n);
        let actual_degree = N - 1;
        let path = format!("tmp/poly_openings_{}.log", E::Fq::size_in_bits());

        // 2. Store
        let rng = &mut ark_std::test_rng();
        let c_poly = DensePolynomial::<E::Fr>::rand(actual_degree, rng);
        let c_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &c_poly);
        let openings = KZGCommit::<E>::multiple_open::<E::G2Affine>(&c_poly, &pp.g2_powers, pp.n);
        let table = TableInput::<E> {
            c_poly,
            c_com,
            openings,
        };
        table.store(&path);

        // 3. Load
        let table_loaded = TableInput::load(&path);

        // 4. Test
        assert_eq!(table, table_loaded);
        std::fs::remove_file(&path).expect("File can not be deleted");
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_multiple_lookups() {
        do_multiple_lookups::<Bls12_381>();
        do_multiple_lookups::<Bls12_377>();
    }

    #[allow(non_snake_case)]
    fn do_multiple_lookups<E: PairingEngine>() {
        let mut rng = ark_std::test_rng();

        const MIN_LOG_N: usize = 7;
        const MAX_LOG_N: usize = 15;
        const EPS: usize = 1;
        const MIN_LOG_M: usize = 2;
        const MAX_LOG_M: usize = 5;

        for n in MIN_LOG_N..=MAX_LOG_N {
            // 1. Setup
            let N: usize = 1 << n;
            let powers_size: usize = N + 2; // SRS SIZE
            println!("N={}", N);
            let temp_m = n; // dummy
            let mut pp = PublicParameters::<E>::setup(&powers_size, &N, &temp_m, &n);
            let actual_degree = N - EPS;
            // println!("time for powers of tau {:?} for N={:?}", now.elapsed(),N);

            // 2. Poly and openings
            let table = get_poly_and_g2_openings(&pp, actual_degree);

            for logm in MIN_LOG_M..=std::cmp::min(MAX_LOG_M, n / 2 - 1) {
                // 3. Setup
                let now = Instant::now();
                let mut m = 1 << logm;
                m = m + 1;

                println!("m={}", m);
                pp.regenerate_lookup_params(m);
                println!("Time to generate aux domain {:?}", now.elapsed());

                // 4. Positions
                let mut positions: Vec<usize> = vec![];
                for j in 0..m {
                    // generate positions evenly distributed in the set
                    let i_j: usize = j * (actual_degree / m);
                    positions.push(i_j);
                }

                // 5. generating phi
                let blinder = E::Fr::rand(&mut rng);
                let a_m = DensePolynomial::from_coefficients_slice(&[blinder]);
                let mut phi_poly = a_m.mul_by_vanishing_poly(pp.domain_m);
                let c_poly_local = table.c_poly.clone();
                for j in 0..m {
                    phi_poly = &phi_poly
                        + &(&pp.lagrange_polynomials_m[j]
                            * c_poly_local.evaluate(&pp.domain_N.element(positions[j])));
                    // adding c(w^{i_j})*mu_j(X)
                }

                for j in m..pp.domain_m.size() {
                    phi_poly = &phi_poly
                        + &(&pp.lagrange_polynomials_m[j]
                            * c_poly_local.evaluate(&pp.domain_N.element(0)));
                    // adding c(w^{i_j})*mu_j(X)
                }

                // 6. Running proofs
                let now = Instant::now();
                let c_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &table.c_poly);
                let phi_com = KZGCommit::<E>::commit_g1(&pp.poly_ck, &phi_poly);
                println!("Time to generate inputs = {:?}", now.elapsed());

                let lookup_instance = LookupInstance { c_com, phi_com };

                let prover_input = LookupProverInput {
                    c_poly: table.c_poly.clone(),
                    phi_poly,
                    positions,
                    openings: table.openings.clone(),
                };

                let now = Instant::now();
                let (proof, unity_proof) =
                    compute_lookup_proof::<E, _>(&lookup_instance, &prover_input, &pp, &mut rng);
                println!("Time to generate proof for = {:?}", now.elapsed());
                let now = Instant::now();
                let res = verify_lookup_proof(&table.c_com, &phi_com, &proof, &unity_proof, &pp);
                println!("Time to verify proof for  = {:?}", now.elapsed());
                assert!(res);
                println!("Lookup test succeeded");
            }
        }
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_lookup() {
        do_lookup::<Bls12_381>();
        do_lookup::<Bls12_377>();
    }

    fn do_lookup<E: PairingEngine>() {
        let mut rng = ark_std::test_rng();

        let now = Instant::now();
        let (prover_input, srs) = generate_lookup_input(&mut rng);
        println!(
            "Time to generate parameters for n={:?} = {:?}",
            srs.n,
            now.elapsed()
        );
        // kzg_test(&srs);
        let c_com = KZGCommit::<E>::commit_g1(&srs.poly_ck, &prover_input.c_poly);
        let phi_com = KZGCommit::<E>::commit_g1(&srs.poly_ck, &prover_input.phi_poly);

        let lookup_instance = LookupInstance { c_com, phi_com };

        let now = Instant::now();
        let (proof, unity_proof) =
            compute_lookup_proof(&lookup_instance, &prover_input, &srs, &mut rng);
        println!(
            "Time to generate proof for m={:?} = {:?}",
            srs.m,
            now.elapsed()
        );
        let now = Instant::now();
        let res = verify_lookup_proof(&c_com, &phi_com, &proof, &unity_proof, &srs);
        println!(
            "Time to verify proof for n={:?} = {:?}",
            srs.n,
            now.elapsed()
        );
        assert!(res);
        println!("Lookup test succeeded");
    }
}
