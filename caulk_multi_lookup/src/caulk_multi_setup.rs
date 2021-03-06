/*
This file includes the setup algorithm for Caulk with multi openings.
A full description of the setup is not formally given in the paper.
*/

use ark_poly_commit::kzg10::*;
use ark_ec::{bls12::Bls12, PairingEngine,AffineCurve,ProjectiveCurve};
use ark_poly::{  UVPolynomial, GeneralEvaluationDomain, Evaluations as EvaluationsOnDomain,
        EvaluationDomain};
use ark_bls12_381::{Bls12_381, Fr, FrParameters,G1Affine, G2Affine};
use ark_ff::{Fp256, UniformRand};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};

use crate::tools::{UniPoly381, KzgBls12_381};
use std::{time::{Instant}, fs::File, io::Read};
use ark_std::{One, Zero,cfg_into_iter};


// structure of public parameters
#[allow(non_snake_case)]
pub struct PublicParameters {
    pub poly_ck: Powers<'static, Bls12<ark_bls12_381::Parameters> >,
    pub poly_vk: VerifierKey<Bls12<ark_bls12_381::Parameters>>,
    pub domain_m: GeneralEvaluationDomain<Fr>,
    pub domain_n: GeneralEvaluationDomain<Fr>,
    pub domain_N: GeneralEvaluationDomain<Fr>,
    pub verifier_pp: VerifierPublicParameters,
    pub lagrange_polynomials_n: Vec< UniPoly381>,
    pub lagrange_polynomials_m: Vec< UniPoly381>,
    pub id_poly: UniPoly381,
    pub N: usize,
    pub m: usize,
    pub n: usize,
    pub g2_powers: Vec<G2Affine>,
}

pub struct LookupParameters{
    m: usize,
    lagrange_polynomials_m: Vec< UniPoly381>,
    domain_m: GeneralEvaluationDomain<Fr>,
    id_poly: UniPoly381,
}

impl PublicParameters{
    pub fn regenerate_lookup_params(&mut self, m: usize){
        let lp = generate_lookup_params(m);
        self.m = lp.m;
        self.lagrange_polynomials_m = lp.lagrange_polynomials_m;
        self.domain_m = lp.domain_m;
        self.id_poly = lp.id_poly;
    }


    //store powers of g in a file
    pub fn store(&self, path: &str) {
        use std::io::Write;

        //1. Powers of g
        let mut g_bytes = vec![];
        let mut f = File::create(path).expect("Unable to create file");
        let deg: u32 = self.poly_ck.powers_of_g.len().try_into().unwrap();
        let deg_bytes = deg.to_be_bytes();
        f.write_all(&deg_bytes).expect("Unable to write data");
        let deg32: usize = deg.try_into().unwrap();
        for i in 0..deg32
        {
            self.poly_ck.powers_of_g[i].into_projective().into_affine().serialize_uncompressed(&mut g_bytes).ok();
        }
        f.write_all(&g_bytes).expect("Unable to write data");

        //2. Powers of gammag
        let deg_gamma: u32 = self.poly_ck.powers_of_gamma_g.len().try_into().unwrap();
        let mut gg_bytes = vec![];
        let deg_bytes = deg_gamma.to_be_bytes();
        f.write_all(&deg_bytes).expect("Unable to write data");
        let deg32: usize = deg.try_into().unwrap();
        for i in 0..deg32
        {
            self.poly_ck.powers_of_gamma_g[i].into_projective().into_affine().serialize_uncompressed(&mut gg_bytes).ok();
        }
        f.write_all(&gg_bytes).expect("Unable to write data");


        //3. Verifier key
        let mut h_bytes = vec![];
        self.poly_vk.h.serialize_uncompressed(&mut h_bytes).ok();
        self.poly_vk.beta_h.serialize_uncompressed(&mut h_bytes).ok();
        f.write_all(&h_bytes).expect("Unable to write data");

        //4. g2 powers
        let mut g2_bytes = vec![];
        let deg2: u32 = self.g2_powers.len().try_into().unwrap();
        let deg2_bytes = deg2.to_be_bytes();
        f.write_all(&deg2_bytes).expect("Unable to write data");
        let deg2_32: usize = deg2.try_into().unwrap();
        for i in 0..deg2_32
        {
            self.g2_powers[i].into_projective().into_affine().serialize_uncompressed(&mut g2_bytes).ok();
        }
        f.write_all(&g2_bytes).expect("Unable to write data");

    }

    //load powers of g from a file
    pub fn load(path: &str)
    ->(
        Powers<'static, Bls12<ark_bls12_381::Parameters> >,
        VerifierKey<Bls12<ark_bls12_381::Parameters>>,
        Vec<G2Affine>
    )
     {
        const G1_UNCOMPR_SIZE: usize =96;
        const G2_UNCOMPR_SIZE: usize =192;
        let mut data = Vec::new();
        let mut f = File::open(path).expect("Unable to open file");
        f.read_to_end(&mut data).expect("Unable to read data");

        //1. reading g powers
        let mut cur_counter:usize  = 0;
        let deg_bytes: [u8; 4] = (&data[0..4]).try_into().unwrap();
        let deg: u32 = u32::from_be_bytes(deg_bytes);
        let mut powers_of_g = vec![];
        let deg32: usize = deg.try_into().unwrap();
        cur_counter += 4;
        for i in 0..deg32
        {
            let buf_bytes = &data[cur_counter+i*G1_UNCOMPR_SIZE..cur_counter+(i+1)*G1_UNCOMPR_SIZE];
            let tmp = G1Affine::deserialize_unchecked(buf_bytes).unwrap();
            powers_of_g.push(tmp);
        }
        cur_counter+=deg32*G1_UNCOMPR_SIZE;

        //2. reading gamma g powers
        let deg_bytes: [u8; 4] = (&data[cur_counter..cur_counter+4]).try_into().unwrap();
        let deg: u32 = u32::from_be_bytes(deg_bytes);
        let mut powers_of_gamma_g = vec![];
        let deg32: usize = deg.try_into().unwrap();
        cur_counter += 4;
        for i in 0..deg32
        {
            let buf_bytes = &data[cur_counter+i*G1_UNCOMPR_SIZE..cur_counter+(i+1)*G1_UNCOMPR_SIZE];
            let tmp = G1Affine::deserialize_unchecked(buf_bytes).unwrap();
            powers_of_gamma_g.push(tmp);
        }
        cur_counter+=deg32*G1_UNCOMPR_SIZE;



        //3. reading verifier key
        let buf_bytes = &data[cur_counter..cur_counter+G2_UNCOMPR_SIZE];
        let h = G2Affine::deserialize_unchecked(buf_bytes).unwrap();
        cur_counter+= G2_UNCOMPR_SIZE;
        let buf_bytes = &data[cur_counter..cur_counter+G2_UNCOMPR_SIZE];
        let beta_h = G2Affine::deserialize_unchecked(buf_bytes).unwrap();
        cur_counter+= G2_UNCOMPR_SIZE;

        //4. reading G2 powers
        let deg2_bytes: [u8; 4] = (&data[cur_counter..cur_counter+4]).try_into().unwrap();
        let deg2: u32 = u32::from_be_bytes(deg2_bytes);
        let mut g2_powers = vec![];
        let deg2_32: usize = deg2.try_into().unwrap();
        cur_counter += 4;
        for _ in 0..deg2_32
        {
            let buf_bytes = &data[cur_counter ..cur_counter+G2_UNCOMPR_SIZE];
            let tmp = G2Affine::deserialize_unchecked(buf_bytes).unwrap();
            g2_powers.push(tmp);
            cur_counter+=G2_UNCOMPR_SIZE;
        }

        let vk = VerifierKey {
            g: powers_of_g[0].clone(),
            gamma_g: powers_of_gamma_g[0].clone(),
            h: h,
            beta_h: beta_h,
            prepared_h: h.into(),
            prepared_beta_h: beta_h.into(),
        };

        let powers = Powers {
            powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
            powers_of_gamma_g: ark_std::borrow::Cow::Owned(powers_of_gamma_g),
        };

        (powers, vk, g2_powers)
    }


}

// smaller set of public parameters used by verifier
pub struct VerifierPublicParameters {
    pub poly_vk: VerifierKey<Bls12<ark_bls12_381::Parameters>>,
    pub domain_m_size: usize,
}

fn generate_lookup_params(m: usize)
->LookupParameters
{
    let domain_m: GeneralEvaluationDomain<Fr> = GeneralEvaluationDomain::new( m.clone() ).unwrap();

     // id_poly(X) = 1 for omega_m in range and 0 for omega_m not in range.
     let mut id_vec = Vec::new();
     for _ in 0..m.clone() {
         id_vec.push( Fr::one() );
     }
     for _ in m.clone() .. domain_m.size() {
         id_vec.push( Fr::zero() );
     }
     let id_poly = EvaluationsOnDomain::from_vec_and_domain(id_vec, domain_m).interpolate();
     let mut lagrange_polynomials_m: Vec< UniPoly381 > = Vec::new();

    for i in 0..domain_m.size() {
        let evals: Vec<Fp256<FrParameters>> = cfg_into_iter!(0..domain_m.size())
        .map(|k| {
            if k == i { Fr::one() }
            else { Fr::zero() }
            }).collect();
        lagrange_polynomials_m.push(EvaluationsOnDomain::from_vec_and_domain(evals, domain_m).interpolate());
    }

     return LookupParameters {
         m: m,
         lagrange_polynomials_m: lagrange_polynomials_m,
         domain_m: domain_m,
         id_poly: id_poly };
}

// Reduces full srs down to smaller srs for smaller polynomials
// Copied from arkworks library (where same function is private)
fn trim<E: PairingEngine, P: UVPolynomial<E::Fr>>(
        srs: UniversalParams<E>,
        mut supported_degree: usize,
    ) -> (Powers<'static, E>, VerifierKey<E>) {
        if supported_degree == 1 {
            supported_degree += 1;
        }
        let pp = srs.clone();
        let powers_of_g = pp.powers_of_g[..=supported_degree].to_vec();
        let powers_of_gamma_g = (0..=supported_degree)
            .map(|i| pp.powers_of_gamma_g[&i])
            .collect();

        let powers = Powers {
            powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
            powers_of_gamma_g: ark_std::borrow::Cow::Owned(powers_of_gamma_g),
        };
        let vk = VerifierKey {
            g: pp.powers_of_g[0],
            gamma_g: pp.powers_of_gamma_g[&0],
            h: pp.h,
            beta_h: pp.beta_h,
            prepared_h: pp.prepared_h.clone(),
            prepared_beta_h: pp.prepared_beta_h.clone(),
        };
        (powers, vk)
    }



// setup algorithm for index_hiding_polycommit
// also includes a bunch of precomputation.
// @max_degree max degree of table polynomial C(X), also the size of the trusted setup
// @N domain size on which proofs are constructed. Should not be smaller than max_degree
// @m lookup size. Can be changed later
// @n suppl domain for the unity proofs. Should be at least 6+log N
#[allow(non_snake_case)]
pub fn setup_multi_lookup(max_degree: &usize, N: &usize, m: &usize, n: &usize) -> PublicParameters
 {

    let rng = &mut ark_std::test_rng();

    // Setup algorithm. To be replaced by output of a universal setup before being production ready.


    //let mut srs = KzgBls12_381::setup(4, true, rng).unwrap();
    let  poly_ck: Powers<'static, Bls12<ark_bls12_381::Parameters> >;
    let  poly_vk:  VerifierKey<Bls12<ark_bls12_381::Parameters>>;
    let mut g2_powers: Vec<G2Affine>=Vec::new();

    //try opening the file. If it exists load the setup from there, otherwise generate
    let path=format!("srs/srs_{}.setup",max_degree);
    let res = File::open(path.clone());
    let  store_to_file:bool;
    match res{
        Ok(_)=>{
            let now = Instant::now();
            let (_poly_ck, _poly_vk, _g2_powers) = PublicParameters::load(&path);
            println!("time to load powers = {:?}", now.elapsed());
            store_to_file = false;
            g2_powers = _g2_powers;
            poly_ck = _poly_ck;
            poly_vk = _poly_vk;
        }
        Err(_)=>{
            let now = Instant::now();
            let srs = KzgBls12_381::setup(max_degree.clone(), true, rng).unwrap();
            println!("time to setup powers = {:?}", now.elapsed());

            // trim down to size
            let (poly_ck2, poly_vk2) = trim::<Bls12_381, UniPoly381>(srs, max_degree.clone());
              poly_ck = Powers {
                powers_of_g: ark_std::borrow::Cow::Owned(poly_ck2.powers_of_g.into()),
                powers_of_gamma_g: ark_std::borrow::Cow::Owned(poly_ck2.powers_of_gamma_g.into()),
            };
            poly_vk = poly_vk2;

            // need some powers of g2
            // arkworks setup doesn't give these powers but the setup does use a fixed randomness to generate them.
            // so we can generate powers of g2 directly.
            let rng = &mut ark_std::test_rng();
            let beta: Fp256<FrParameters>  = Fr::rand(rng);
            let mut temp = poly_vk.h.clone();

            for _ in 0..poly_ck.powers_of_g.len() {
                g2_powers.push( temp.clone() );
                temp = temp.mul( beta ).into_affine();
            }

            store_to_file = true;
        }
    }



    // domain where openings {w_i}_{i in I} are embedded
    let domain_n: GeneralEvaluationDomain<Fr> = GeneralEvaluationDomain::new( n.clone() ).unwrap();
    let domain_N: GeneralEvaluationDomain<Fr> = GeneralEvaluationDomain::new( N.clone() ).unwrap();



    // precomputation to speed up prover
    // lagrange_polynomials[i] = polynomial equal to 0 at w^j for j!= i and 1  at w^i
    let mut lagrange_polynomials_n: Vec< UniPoly381 > = Vec::new();

    for i in 0..domain_n.size() {
        let evals: Vec<Fp256<FrParameters>> = cfg_into_iter!(0..domain_n.size())
        .map(|k| {
            if k == i { Fr::one() }
            else { Fr::zero() }
            }).collect();
        lagrange_polynomials_n.push(EvaluationsOnDomain::from_vec_and_domain(evals, domain_n).interpolate());
    }







    let lp = generate_lookup_params(m.clone());

    let verifier_pp = VerifierPublicParameters {
        poly_vk: poly_vk.clone(),
        domain_m_size: lp.domain_m.size(),
    };

    let pp = PublicParameters {
        poly_ck: poly_ck,
        domain_m: lp.domain_m,
        domain_n: domain_n,
        lagrange_polynomials_n: lagrange_polynomials_n,
        lagrange_polynomials_m: lp.lagrange_polynomials_m,
        id_poly: lp.id_poly,
        domain_N: domain_N,
        poly_vk: poly_vk,
        verifier_pp: verifier_pp,
        N: N.clone(),
        n: n.clone(),
        m: lp.m.clone(),
        g2_powers: g2_powers.clone()
    };
     if store_to_file
    {
        pp.store(&path);
    }
    return pp
}


#[test]
#[allow(non_snake_case)]
pub fn test_load()
{
    let n: usize = 4;
    let N: usize = 1<<n;
    let powers_size: usize = 4*N; //SRS SIZE
    let temp_m = n; //dummy
    let pp =setup_multi_lookup(&powers_size,&N,&temp_m,&n);
    let path = "powers.log";
    pp.store(path);
    let loaded = PublicParameters::load(path);
    assert_eq!(pp.poly_ck.powers_of_g,loaded.0.powers_of_g);
    assert_eq!(pp.poly_ck.powers_of_gamma_g,loaded.0.powers_of_gamma_g);
    assert_eq!(pp.poly_vk.h,loaded.1.h);
    assert_eq!(pp.poly_vk.beta_h,loaded.1.beta_h);
    assert_eq!(pp.g2_powers,loaded.2);
    std::fs::remove_file(&path).expect("File can not be deleted");
}
