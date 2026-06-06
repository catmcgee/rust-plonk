//! Small polynomial helpers shared by the prover, verifier and preprocessing.

use ark_ff::{batch_inversion, FftField};
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Radix2EvaluationDomain,
};

/// Interpolate evaluations over the domain.
pub fn interpolate<F: FftField>(
    domain: &Radix2EvaluationDomain<F>,
    evals: &[F],
) -> DensePolynomial<F> {
    DensePolynomial::from_coefficients_vec(domain.ifft(evals))
}

/// `zeta^n`, `Z_H(zeta) = zeta^n - 1` and `L_0(zeta)`.
///
/// `Z_H(zeta)` is zero exactly when `zeta` is in the domain, in which case
/// `L_0` is undefined and the caller must bail out.
pub fn vanishing_at<F: FftField>(n: usize, zeta: F) -> (F, F, F) {
    let zeta_n = zeta.pow([n as u64]);
    let z_h = zeta_n - F::one();
    let l0 = z_h / (F::from(n as u64) * (zeta - F::one()));
    (zeta_n, z_h, l0)
}

/// `L_0(zeta), ..., L_{count-1}(zeta)` with one batch inversion, where
/// `L_i(zeta) = omega^i (zeta^n - 1) / (n (zeta - omega^i))`.
/// `zeta` must not be in the domain.
pub fn lagrange_at<F: FftField>(
    domain: &Radix2EvaluationDomain<F>,
    zeta: F,
    count: usize,
) -> Vec<F> {
    let n = domain.size() as u64;
    let z_h = zeta.pow([n]) - F::one();
    let n_inv = F::from(n).inverse().expect("n is nonzero");
    let mut denoms: Vec<F> = (0..count).map(|i| zeta - domain.element(i)).collect();
    batch_inversion(&mut denoms);
    denoms
        .iter()
        .enumerate()
        .map(|(i, d)| domain.element(i) * z_h * n_inv * d)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ff::UniformRand;
    use ark_std::test_rng;

    #[test]
    fn lagrange_matches_arkworks() {
        let mut rng = test_rng();
        let domain = Radix2EvaluationDomain::<Fr>::new(16).unwrap();
        let zeta = Fr::rand(&mut rng);
        let all = domain.evaluate_all_lagrange_coefficients(zeta);
        assert_eq!(lagrange_at(&domain, zeta, 5), all[..5]);
        assert_eq!(lagrange_at(&domain, zeta, 16), all);
        let (_, z_h, l0) = vanishing_at(16, zeta);
        assert_eq!(l0, all[0]);
        assert_eq!(z_h, domain.evaluate_vanishing_polynomial(zeta));
    }
}
