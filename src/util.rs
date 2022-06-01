use ark_ec::PairingEngine;
use ark_ff::PrimeField;
use ark_poly::UVPolynomial;
use ark_poly_commit::kzg10::*;

// Reduces full srs down to smaller srs for smaller polynomials
// Copied from arkworks library (where same function is private)
pub(crate) fn trim<E: PairingEngine, P: UVPolynomial<E::Fr>>(
    srs: &UniversalParams<E>,
    mut supported_degree: usize,
) -> (Powers<'static, E>, VerifierKey<E>) {
    if supported_degree == 1 {
        supported_degree += 1;
    }

    let powers_of_g = srs.powers_of_g[..=supported_degree].to_vec();
    let powers_of_gamma_g = (0..=supported_degree)
        .map(|i| srs.powers_of_gamma_g[&i])
        .collect();

    let powers = Powers {
        powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
        powers_of_gamma_g: ark_std::borrow::Cow::Owned(powers_of_gamma_g),
    };
    let vk = VerifierKey {
        g: srs.powers_of_g[0],
        gamma_g: srs.powers_of_gamma_g[&0],
        h: srs.h,
        beta_h: srs.beta_h,
        prepared_h: srs.prepared_h.clone(),
        prepared_beta_h: srs.prepared_beta_h.clone(),
    };
    (powers, vk)
}

////////////////////////////////////////////////
//

// copied from arkworks
pub(crate) fn convert_to_bigints<F: PrimeField>(p: &[F]) -> Vec<F::BigInt> {
    ark_std::cfg_iter!(p)
        .map(|s| s.into_repr())
        .collect::<Vec<_>>()
}
