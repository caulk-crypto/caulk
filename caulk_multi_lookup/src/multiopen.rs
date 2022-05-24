/*
This file includes an algorithm for calculating n openings of a KZG vector commitment of size n in n log(n) time.
The algorithm is by Feist and khovratovich.
It is useful for preprocessing.
The full algorithm is described here https://github.com/khovratovich/Kate/blob/master/Kate_amortized.pdf
*/

use std::str::FromStr;
//use std::time::{Instant};
use std::vec::Vec;

use ark_bls12_381::{Fr, FrParameters, G2Affine, G2Projective};
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{Field, Fp256, PrimeField};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain, UVPolynomial,
};

pub fn compute_h_opt_g2(
    c_poly: &DensePolynomial<Fp256<FrParameters>>, //c(X) degree up to d<2^p , i.e. c_poly has at most d+1 coeffs non-zero
    g2powers: &Vec<G2Affine>,                      //SRS
    p: usize,
) -> Vec<G2Projective> {
    let mut coeffs = c_poly.coeffs().to_vec();
    let dom_size = 1 << p;
    let fpzero = Fp256::from_str("0").unwrap();
    coeffs.resize(dom_size, fpzero);

    //let now = Instant::now();
    //1. x_ext = [[x^(d-1)], [x^{d-2},...,[x],[1], d+2 [0]'s]
    let mut x_ext = vec![];
    for i in 0..=dom_size - 2 {
        x_ext.push(g2powers[dom_size - 2 - i].into_projective());
    }
    let g1inf = g2powers[0].mul(fpzero);
    x_ext.resize(2 * dom_size, g1inf); //filling 2d+2 neutral elements

    let y = dft_g2_opt(&x_ext, p + 1);
    //println!("Step 1 computed in {:?}", now.elapsed());

    //2. c_ext = [c_d, d zeroes, c_d,c_{0},c_1,...,c_{d-2},c_{d-1}]
    //let now = Instant::now();
    let mut c_ext = vec![];
    c_ext.push(coeffs[coeffs.len() - 1]);
    c_ext.resize(dom_size, fpzero);
    c_ext.push(coeffs[coeffs.len() - 1]);
    for i in 0..coeffs.len() - 1 {
        c_ext.push(coeffs[i]);
    }
    assert_eq!(c_ext.len(), 2 * dom_size);
    let v = dft_opt(&c_ext, p + 1);
    //println!("Step 2 computed in {:?}", now.elapsed());

    //3. u = y o v

    //let now = Instant::now();
    let u = y
        .into_iter()
        .zip(v.into_iter())
        .map(|(a, b)| a.mul(b.into_repr()))
        .collect();
    //    println!("Step 3 computed in {:?}", now.elapsed());

    //4. h_ext = idft_{2d+2}(u)
    //let now = Instant::now();
    let h_ext = idft_g2_opt(&u, p + 1);
    //println!("Step 4 computed in {:?}", now.elapsed());

    return h_ext[0..dom_size].to_vec();
}

//compute dft of size @dom_size over vector of G1 elements
//q_i = h_0 + h_1w^i + h_2w^{2i}+\cdots + h_{dom_size-1}w^{(dom_size-1)i} for 0<= i< dom_size=2^p
pub fn dft_g2_opt(h: &Vec<G2Projective>, p: usize) -> Vec<G2Projective> {
    let dom_size = 1 << p;
    assert_eq!(h.len(), dom_size); //we do not support inputs of size not power of 2
    let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(dom_size).unwrap();
    let mut l = dom_size / 2;
    let mut m: usize = 1;
    //Stockham FFT
    let mut xprev = h.to_vec();
    for _ in 1..=p {
        let mut xnext = vec![];
        xnext.resize(xprev.len(), h[0]);
        for j in 0..l {
            for k in 0..m {
                let c0 = xprev[k + j * m].clone();
                let c1 = &xprev[k + j * m + l * m];
                xnext[k + 2 * j * m] = c0 + c1;
                let wj_2l = input_domain.element((j * dom_size / (2 * l)) % dom_size);
                xnext[k + 2 * j * m + m] = (c0 - c1).mul(wj_2l.into_repr());
            }
        }
        l = l / 2;
        m = m * 2;
        xprev = xnext;
    }
    return xprev;
}

//compute dft of size @dom_size over vector of Fr elements
//q_i = h_0 + h_1w^i + h_2w^{2i}+\cdots + h_{dom_size-1}w^{(dom_size-1)i} for 0<= i< dom_size=2^p
pub fn dft_opt(h: &Vec<Fr>, p: usize) -> Vec<Fr> {
    let dom_size = 1 << p;
    assert_eq!(h.len(), dom_size); //we do not support inputs of size not power of 2
    let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(dom_size).unwrap();
    let mut l = dom_size / 2;
    let mut m: usize = 1;
    //Stockham FFT
    let mut xprev = h.to_vec();
    for _ in 1..=p {
        let mut xnext = vec![];
        xnext.resize(xprev.len(), h[0]);
        for j in 0..l {
            for k in 0..m {
                let c0 = xprev[k + j * m].clone();
                let c1 = &xprev[k + j * m + l * m];
                xnext[k + 2 * j * m] = c0 + c1;
                let wj_2l = input_domain.element((j * dom_size / (2 * l)) % dom_size);
                xnext[k + 2 * j * m + m] = (c0 - c1) * (wj_2l);
            }
        }
        l = l / 2;
        m = m * 2;
        xprev = xnext;
    }
    return xprev;
}

//compute idft of size @dom_size over vector of G1 elements
//q_i = (h_0 + h_1w^-i + h_2w^{-2i}+\cdots + h_{dom_size-1}w^{-(dom_size-1)i})/dom_size for 0<= i< dom_size=2^p
pub fn idft_g2_opt(h: &Vec<G2Projective>, p: usize) -> Vec<G2Projective> {
    let dom_size = 1 << p;
    assert_eq!(h.len(), dom_size); //we do not support inputs of size not power of 2
    let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(dom_size).unwrap();
    let mut l = dom_size / 2;
    let mut m: usize = 1;
    let mut dom_fr = Fr::from_str("1").unwrap();
    //Stockham FFT
    let mut xprev = h.to_vec();
    for _ in 1..=p {
        let mut xnext = vec![];
        xnext.resize(xprev.len(), h[0]);
        for j in 0..l {
            for k in 0..m {
                let c0 = xprev[k + j * m].clone();
                let c1 = &xprev[k + j * m + l * m];
                xnext[k + 2 * j * m] = c0 + c1;
                let wj_2l = input_domain
                    .element((dom_size - (j * dom_size / (2 * l)) % dom_size) % dom_size);
                xnext[k + 2 * j * m + m] = (c0 - c1).mul(wj_2l.into_repr()); //Difference #1 to forward dft
            }
        }
        l = l / 2;
        m = m * 2;
        dom_fr = dom_fr + dom_fr;
        xprev = xnext;
    }
    let res = xprev
        .iter()
        .map(|x| x.mul(dom_fr.inverse().unwrap().into_repr()))
        .collect();
    return res;
}

//compute all openings to c_poly using a smart formula
pub fn multiple_open_g2(
    g2powers: &Vec<G2Affine>,                      //SRS
    c_poly: &DensePolynomial<Fp256<FrParameters>>, //c(X)
    p: usize,
) -> Vec<G2Affine> {
    let degree = c_poly.coeffs.len() - 1;
    let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(degree).unwrap();

    //let now = Instant::now();
    let h2 = compute_h_opt_g2(c_poly, g2powers, p);
    //println!("H2 computed in {:?}", now.elapsed());
    //assert_eq!(h,h2);

    let dom_size = input_domain.size();
    assert_eq!(1 << p, dom_size);
    assert_eq!(degree + 1, dom_size);
    /*let now = Instant::now();
    let q = dftG1(&h,p);
    println!("Q computed in {:?}", now.elapsed());*/

    //let now = Instant::now();
    let q2 = dft_g2_opt(&h2, p);
    //println!("Q2 computed in {:?}", now.elapsed());
    //assert_eq!(q,q2);

    let mut res: Vec<G2Affine> = vec![];
    for i in 0..dom_size {
        res.push(q2[i].into_affine());
    }
    return res;
}

#[cfg(test)]
pub mod tests {

    use std::time::Instant;

    use ark_bls12_381::{Bls12_381, G1Affine, G1Projective};
    use ark_ec::{AffineCurve, ProjectiveCurve};
    use ark_ff::Fp256;
    use ark_poly::univariate::DensePolynomial;
    use ark_poly::EvaluationDomain;
    use ark_poly_commit::kzg10::*;
    use ark_poly_commit::UVPolynomial;
    use ark_std::One;

    use crate::caulk_multi_setup::{setup_multi_lookup, PublicParameters};
    use crate::multiopen::*;
    use crate::tools::{kzg_commit_g2, kzg_open_g1, KzgBls12_381, UniPoly381};

    pub fn commit_direct(
        c_poly: &DensePolynomial<Fp256<FrParameters>>, //c(X)
        poly_ck: &Powers<Bls12_381>,                   //SRS
    ) -> G1Affine {
        assert!(c_poly.coeffs.len() <= poly_ck.powers_of_g.len());
        let mut com = poly_ck.powers_of_g[0].mul(c_poly.coeffs[0]);
        for i in 1..c_poly.coeffs.len() {
            com = com + poly_ck.powers_of_g[i].mul(c_poly.coeffs[i]);
        }
        return com.into_affine();
    }

    //compute dft of size @dom_size over vector of G1 elements
    //q_i = h_0 + h_1w^i + h_2w^{2i}+\cdots + h_{dom_size-1}w^{(dom_size-1)i} for 0<= i< dom_size=2^p
    #[allow(dead_code)]
    pub fn dft_g1_opt(h: &Vec<G1Projective>, p: usize) -> Vec<G1Projective> {
        let dom_size = 1 << p;
        assert_eq!(h.len(), dom_size); //we do not support inputs of size not power of 2
        let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(dom_size).unwrap();
        let mut l = dom_size / 2;
        let mut m: usize = 1;
        //Stockham FFT
        let mut xprev = h.to_vec();
        for _ in 1..=p {
            let mut xnext = vec![];
            xnext.resize(xprev.len(), h[0]);
            for j in 0..l {
                for k in 0..m {
                    let c0 = xprev[k + j * m].clone();
                    let c1 = &xprev[k + j * m + l * m];
                    xnext[k + 2 * j * m] = c0 + c1;
                    let wj_2l = input_domain.element((j * dom_size / (2 * l)) % dom_size);
                    xnext[k + 2 * j * m + m] = (c0 - c1).mul(wj_2l.into_repr());
                }
            }
            l = l / 2;
            m = m * 2;
            xprev = xnext;
        }
        return xprev;
    }

    //compute idft of size @dom_size over vector of G1 elements
    //q_i = (h_0 + h_1w^-i + h_2w^{-2i}+\cdots + h_{dom_size-1}w^{-(dom_size-1)i})/dom_size for 0<= i< dom_size=2^p
    #[allow(dead_code)]
    pub fn idft_g1_opt(h: &Vec<G1Projective>, p: usize) -> Vec<G1Projective> {
        let dom_size = 1 << p;
        assert_eq!(h.len(), dom_size); //we do not support inputs of size not power of 2
        let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(dom_size).unwrap();
        let mut l = dom_size / 2;
        let mut m: usize = 1;
        let mut dom_fr = Fr::from_str("1").unwrap();
        //Stockham FFT
        let mut xprev = h.to_vec();
        for _ in 1..=p {
            let mut xnext = vec![];
            xnext.resize(xprev.len(), h[0]);
            for j in 0..l {
                for k in 0..m {
                    let c0 = xprev[k + j * m].clone();
                    let c1 = &xprev[k + j * m + l * m];
                    xnext[k + 2 * j * m] = c0 + c1;
                    let wj_2l = input_domain
                        .element((dom_size - (j * dom_size / (2 * l)) % dom_size) % dom_size);
                    xnext[k + 2 * j * m + m] = (c0 - c1).mul(wj_2l.into_repr());
                    //Difference #1 to forward dft
                }
            }
            l = l / 2;
            m = m * 2;
            dom_fr = dom_fr + dom_fr;
            xprev = xnext;
        }
        let res = xprev
            .iter()
            .map(|x| x.mul(dom_fr.inverse().unwrap().into_repr()))
            .collect();
        return res;
    }

    //compute all openings to c_poly by mere calling `open` N times
    #[allow(dead_code)]
    pub fn multiple_open_naive(
        c_poly: &DensePolynomial<Fp256<FrParameters>>,
        c_com_open: &Randomness<Fp256<FrParameters>, DensePolynomial<Fp256<FrParameters>>>,
        poly_ck: &Powers<Bls12_381>,
        degree: usize,
    ) -> Vec<G1Affine> {
        let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(degree).unwrap();
        let mut res: Vec<G1Affine> = vec![];
        for i in 0..input_domain.size() {
            let omega_i = input_domain.element(i);
            res.push(kzg_open_g1(&c_poly, &omega_i, &c_com_open, &poly_ck).w);
        }
        return res;
    }

    //compute all openings to c_poly by mere calling `open` N times
    pub fn multiple_open_naive_g2(
        c_poly: &DensePolynomial<Fp256<FrParameters>>,
        srs: &PublicParameters,
        degree: usize,
    ) -> Vec<G2Affine> {
        let input_domain: GeneralEvaluationDomain<Fr> = EvaluationDomain::new(degree).unwrap();
        let mut res: Vec<G2Affine> = vec![];
        for i in 0..input_domain.size() {
            let omega_i = input_domain.element(i);
            res.push(kzg_open_g2(&c_poly, &omega_i, srs));
        }
        return res;
    }

    pub fn kzg_open_g2(
        p: &DensePolynomial<Fp256<FrParameters>>,
        x: &Fp256<FrParameters>, //point
        srs: &PublicParameters,
    ) -> G2Affine {
        let tmp = DensePolynomial::from_coefficients_slice(&[Fr::one()]);
        let (_tmp_com, tmp_com_open) =
            KzgBls12_381::commit(&srs.poly_ck, &tmp, None, None).unwrap();
        let (witness_polynomial, _random_witness_polynomial) =
            KzgBls12_381::compute_witness_polynomial(p, x.clone(), &tmp_com_open).unwrap();

        return kzg_commit_g2(&witness_polynomial, srs);
    }

    #[allow(non_snake_case)]
    #[test]
    pub fn test_commit() {
        // current kzg setup should be changed with output from a setup ceremony
        let p: usize = 8; //bitlength of poly degree
        let max_degree: usize = (1 << p) + 2;
        let actual_degree: usize = (1 << p) - 1;
        let m: usize = 1 << (p / 2);
        let N: usize = 1 << p;
        let pp = setup_multi_lookup(&max_degree, &N, &m, &p);

        // Setting up test instance to run evaluate on.
        // test randomness for c_poly is same everytime.
        // g_c = g^(c(x))
        let rng = &mut ark_std::test_rng();
        let c_poly = UniPoly381::rand(actual_degree, rng);
        let (c_com, _) = KzgBls12_381::commit(&pp.poly_ck, &c_poly, None, None).unwrap();
        let g_c1 = c_com.0;

        let g_c2 = commit_direct(&c_poly, &pp.poly_ck);
        assert_eq!(g_c1, g_c2);
        println!("commit test passed")
    }

    #[allow(non_snake_case)]
    #[test]
    pub fn test_multi_g2() {
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

        let now = Instant::now();
        let q = multiple_open_naive_g2(&c_poly, &pp, actual_degree);
        println!("Multi naive computed in {:?}", now.elapsed());

        let now = Instant::now();
        let q2 = multiple_open_g2(&pp.g2_powers, &c_poly, p);
        println!("Multi advanced computed in {:?}", now.elapsed());
        assert_eq!(q, q2);
    }
}
