//! KZG polynomial commitments over a pairing-friendly curve.
//!
//! The setup is a plain powers-of-tau with the secret sampled locally, which is
//! only fine for tests. A real deployment needs an MPC ceremony.

use ark_ec::{pairing::Pairing, scalar_mul::variable_base::VariableBaseMSM, AffineRepr, CurveGroup};
use ark_ff::{Field, One, PrimeField, UniformRand, Zero};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use ark_std::rand::RngCore;

/// Structured reference string: `[1, tau, tau^2, ..., tau^d]` in G1 and `[1, tau]` in G2.
#[derive(Clone, Debug)]
pub struct Srs<E: Pairing> {
    pub powers_of_g: Vec<E::G1Affine>,
    pub h: E::G2Affine,
    pub tau_h: E::G2Affine,
}

/// Everything the verifier needs from the SRS.
#[derive(Clone, Debug)]
pub struct VerifierKey<E: Pairing> {
    pub g: E::G1Affine,
    pub h: E::G2Affine,
    pub tau_h: E::G2Affine,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Commitment<E: Pairing>(pub E::G1Affine);

/// Witness `[(p(X) - p(z)) / (X - z)]_1` for an evaluation at `z`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Proof<E: Pairing>(pub E::G1Affine);

impl<E: Pairing> Srs<E> {
    /// Sample a fresh `tau` and compute powers up to `max_degree`.
    pub fn setup<R: RngCore>(max_degree: usize, rng: &mut R) -> Self {
        let tau = E::ScalarField::rand(rng);
        let g = E::G1::rand(rng);
        let h = E::G2::rand(rng);

        let mut powers = Vec::with_capacity(max_degree + 1);
        let mut cur = E::ScalarField::one();
        for _ in 0..=max_degree {
            powers.push(cur);
            cur *= tau;
        }
        let powers_of_g: Vec<E::G1> = powers.iter().map(|p| g * p).collect();

        Srs {
            powers_of_g: E::G1::normalize_batch(&powers_of_g),
            h: h.into_affine(),
            tau_h: (h * tau).into_affine(),
        }
    }

    pub fn max_degree(&self) -> usize {
        self.powers_of_g.len() - 1
    }

    pub fn verifier_key(&self) -> VerifierKey<E> {
        VerifierKey {
            g: self.powers_of_g[0],
            h: self.h,
            tau_h: self.tau_h,
        }
    }

    pub fn commit(&self, p: &DensePolynomial<E::ScalarField>) -> Commitment<E> {
        assert!(
            p.degree() <= self.max_degree(),
            "polynomial degree {} exceeds srs degree {}",
            p.degree(),
            self.max_degree()
        );
        let coeffs: Vec<<E::ScalarField as PrimeField>::BigInt> =
            p.coeffs.iter().map(|c| c.into_bigint()).collect();
        let c = E::G1::msm_bigint(&self.powers_of_g[..coeffs.len()], &coeffs);
        Commitment(c.into_affine())
    }

    /// Evaluate `p` at `z` and produce the opening proof.
    pub fn open(
        &self,
        p: &DensePolynomial<E::ScalarField>,
        z: E::ScalarField,
    ) -> (E::ScalarField, Proof<E>) {
        let value = p.evaluate(&z);
        let (q, rem) = divide_by_linear(p, z);
        debug_assert!(rem == value);
        (value, Proof(self.commit(&q).0))
    }

    /// Open several polynomials at the same point with one proof.
    ///
    /// The verifier supplies a random `gamma`; the polynomials are folded into
    /// `sum_i gamma^i p_i` and that is opened once. Returns each `p_i(z)` and
    /// the proof for the folded polynomial.
    pub fn open_batch(
        &self,
        polys: &[&DensePolynomial<E::ScalarField>],
        z: E::ScalarField,
        gamma: E::ScalarField,
    ) -> (Vec<E::ScalarField>, Proof<E>) {
        let values: Vec<_> = polys.iter().map(|p| p.evaluate(&z)).collect();
        let folded = fold(polys, gamma);
        let (q, _) = divide_by_linear(&folded, z);
        (values, Proof(self.commit(&q).0))
    }
}

/// `sum_i gamma^i p_i`
pub fn fold<F: Field>(polys: &[&DensePolynomial<F>], gamma: F) -> DensePolynomial<F> {
    let mut acc = DensePolynomial::zero();
    let mut coeff = F::one();
    for p in polys {
        acc += (coeff, *p);
        coeff *= gamma;
    }
    acc
}

impl<E: Pairing> VerifierKey<E> {
    /// Check `e(C - [v]_1, [1]_2) == e(W, [tau - z]_2)`.
    pub fn verify(
        &self,
        comm: &Commitment<E>,
        z: E::ScalarField,
        value: E::ScalarField,
        proof: &Proof<E>,
    ) -> bool {
        // e(C - v*G + z*W, H) * e(-W, tau*H) == 1
        let lhs = comm.0.into_group() - self.g * value + proof.0 * z;
        let rhs = -proof.0.into_group();
        E::multi_pairing([lhs, rhs], [self.h, self.tau_h]).0.is_one()
    }

    /// Counterpart of [`Srs::open_batch`]: fold commitments and values with
    /// the same `gamma` and check the single proof.
    pub fn verify_batch(
        &self,
        comms: &[Commitment<E>],
        z: E::ScalarField,
        values: &[E::ScalarField],
        gamma: E::ScalarField,
        proof: &Proof<E>,
    ) -> bool {
        assert_eq!(comms.len(), values.len());
        let mut folded_comm = E::G1::zero();
        let mut folded_value = E::ScalarField::zero();
        let mut coeff = E::ScalarField::one();
        for (c, v) in comms.iter().zip(values) {
            folded_comm += c.0 * coeff;
            folded_value += *v * coeff;
            coeff *= gamma;
        }
        self.verify(&Commitment(folded_comm.into_affine()), z, folded_value, proof)
    }
}

/// Divide `p` by `(X - z)`. Returns `(quotient, remainder)`; the remainder is `p(z)`.
pub fn divide_by_linear<F: Field>(p: &DensePolynomial<F>, z: F) -> (DensePolynomial<F>, F) {
    if p.is_zero() {
        return (DensePolynomial::zero(), F::zero());
    }
    // Synthetic division, highest coefficient first.
    let mut q = vec![F::zero(); p.coeffs.len() - 1];
    let mut carry = F::zero();
    for (i, c) in p.coeffs.iter().enumerate().rev() {
        let v = *c + carry;
        if i == 0 {
            return (DensePolynomial::from_coefficients_vec(q), v);
        }
        q[i - 1] = v;
        carry = v * z;
    }
    unreachable!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_std::test_rng;

    #[test]
    fn linear_division() {
        let mut rng = test_rng();
        let p = DensePolynomial::<Fr>::rand(17, &mut rng);
        let z = Fr::rand(&mut rng);
        let (q, r) = divide_by_linear(&p, z);
        assert_eq!(r, p.evaluate(&z));
        let x_minus_z = DensePolynomial::from_coefficients_vec(vec![-z, Fr::one()]);
        let back = &q * &x_minus_z + DensePolynomial::from_coefficients_vec(vec![r]);
        assert_eq!(back, p);
    }

    #[test]
    fn commit_open_verify() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(32, &mut rng);
        let vk = srs.verifier_key();

        let p = DensePolynomial::<Fr>::rand(20, &mut rng);
        let c = srs.commit(&p);
        let z = Fr::rand(&mut rng);
        let (v, proof) = srs.open(&p, z);
        assert_eq!(v, p.evaluate(&z));
        assert!(vk.verify(&c, z, v, &proof));

        // wrong value
        assert!(!vk.verify(&c, z, v + Fr::one(), &proof));
        // wrong point
        assert!(!vk.verify(&c, z + Fr::one(), v, &proof));
        // wrong commitment
        let c2 = srs.commit(&DensePolynomial::rand(20, &mut rng));
        assert!(!vk.verify(&c2, z, v, &proof));
    }

    #[test]
    fn batch_open() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(32, &mut rng);
        let vk = srs.verifier_key();

        let polys: Vec<DensePolynomial<Fr>> = (0..4)
            .map(|i| DensePolynomial::rand(10 + i, &mut rng))
            .collect();
        let refs: Vec<&DensePolynomial<Fr>> = polys.iter().collect();
        let comms: Vec<_> = polys.iter().map(|p| srs.commit(p)).collect();

        let z = Fr::rand(&mut rng);
        let gamma = Fr::rand(&mut rng);
        let (values, proof) = srs.open_batch(&refs, z, gamma);
        for (p, v) in polys.iter().zip(&values) {
            assert_eq!(p.evaluate(&z), *v);
        }
        assert!(vk.verify_batch(&comms, z, &values, gamma, &proof));

        let mut bad = values.clone();
        bad[2] += Fr::one();
        assert!(!vk.verify_batch(&comms, z, &bad, gamma, &proof));
        assert!(!vk.verify_batch(&comms, z, &values, gamma + Fr::one(), &proof));
    }

    #[test]
    fn constant_and_zero_polys() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(4, &mut rng);
        let vk = srs.verifier_key();
        let z = Fr::rand(&mut rng);

        let zero = DensePolynomial::<Fr>::zero();
        let c = srs.commit(&zero);
        let (v, pi) = srs.open(&zero, z);
        assert!(v.is_zero());
        assert!(vk.verify(&c, z, v, &pi));

        let k = DensePolynomial::from_coefficients_vec(vec![Fr::from(7u64)]);
        let c = srs.commit(&k);
        let (v, pi) = srs.open(&k, z);
        assert_eq!(v, Fr::from(7u64));
        assert!(vk.verify(&c, z, v, &pi));
    }
}
