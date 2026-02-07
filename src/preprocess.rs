//! Turn a circuit into prover and verifier keys.

use crate::circuit::Circuit;
use crate::kzg::{self, Commitment, Srs};
use crate::permutation::{coset_generators, Permutation};
use crate::transcript::Transcript;
use ark_ec::pairing::Pairing;
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Radix2EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

#[derive(Clone, Debug)]
pub struct ProverKey<E: Pairing> {
    pub domain: Radix2EvaluationDomain<E::ScalarField>,
    pub k1: E::ScalarField,
    pub k2: E::ScalarField,
    pub q_l: DensePolynomial<E::ScalarField>,
    pub q_r: DensePolynomial<E::ScalarField>,
    pub q_o: DensePolynomial<E::ScalarField>,
    pub q_m: DensePolynomial<E::ScalarField>,
    pub q_c: DensePolynomial<E::ScalarField>,
    pub s_sigma: [DensePolynomial<E::ScalarField>; 3],
    pub permutation: Permutation,
    pub vk: VerifierKey<E>,
}

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierKey<E: Pairing> {
    pub n: usize,
    pub k1: E::ScalarField,
    pub k2: E::ScalarField,
    pub q_l: Commitment<E>,
    pub q_r: Commitment<E>,
    pub q_o: Commitment<E>,
    pub q_m: Commitment<E>,
    pub q_c: Commitment<E>,
    pub s_sigma: [Commitment<E>; 3],
    pub num_public_inputs: usize,
    pub kzg: kzg::VerifierKey<E>,
}

impl<E: Pairing> VerifierKey<E> {
    /// Start a transcript bound to this key and the public inputs. The
    /// prover and verifier both go through here so the challenges can't be
    /// independent of the circuit, which would let a prover who picks the
    /// circuit pick selectors that satisfy an arbitrary "proof".
    pub fn transcript(&self, public_inputs: &[E::ScalarField]) -> Transcript {
        let mut t = Transcript::new(b"plonk");
        t.absorb(b"n", &(self.n as u64));
        t.absorb(b"k1", &self.k1);
        t.absorb(b"k2", &self.k2);
        t.absorb(b"q_l", &self.q_l.0);
        t.absorb(b"q_r", &self.q_r.0);
        t.absorb(b"q_o", &self.q_o.0);
        t.absorb(b"q_m", &self.q_m.0);
        t.absorb(b"q_c", &self.q_c.0);
        t.absorb(b"s_sigma1", &self.s_sigma[0].0);
        t.absorb(b"s_sigma2", &self.s_sigma[1].0);
        t.absorb(b"s_sigma3", &self.s_sigma[2].0);
        t.absorb(b"g", &self.kzg.g);
        t.absorb(b"h", &self.kzg.h);
        t.absorb(b"tau_h", &self.kzg.tau_h);
        t.absorb(b"public inputs", &public_inputs.to_vec());
        t
    }
}

/// Smallest domain we'll use. The blinded quotient has degree 3n+5 and is
/// recovered from 4n coset evaluations, which needs n >= 8.
pub const MIN_DOMAIN_SIZE: usize = 8;

/// Domain size for a circuit: gates padded to a power of two.
pub fn domain_size(num_gates: usize) -> usize {
    num_gates.next_power_of_two().max(MIN_DOMAIN_SIZE)
}

pub fn preprocess<E: Pairing>(circuit: &Circuit<E::ScalarField>, srs: &Srs<E>) -> ProverKey<E> {
    let n = domain_size(circuit.num_gates());
    let domain = Radix2EvaluationDomain::<E::ScalarField>::new(n)
        .expect("field has no subgroup of that size");
    // the blinded quotient's last chunk has degree n+5
    assert!(srs.max_degree() >= n + 5, "srs too small for {} gates", n);

    let (k1, k2) = coset_generators(&domain);

    let mut q_l = Vec::with_capacity(n);
    let mut q_r = Vec::with_capacity(n);
    let mut q_o = Vec::with_capacity(n);
    let mut q_m = Vec::with_capacity(n);
    let mut q_c = Vec::with_capacity(n);
    for g in circuit.gates() {
        q_l.push(g.q_l);
        q_r.push(g.q_r);
        q_o.push(g.q_o);
        q_m.push(g.q_m);
        q_c.push(g.q_c);
    }
    let interpolate = |mut evals: Vec<E::ScalarField>| {
        evals.resize(n, E::ScalarField::from(0u64));
        DensePolynomial::from_coefficients_vec(domain.ifft(&evals))
    };
    let q_l = interpolate(q_l);
    let q_r = interpolate(q_r);
    let q_o = interpolate(q_o);
    let q_m = interpolate(q_m);
    let q_c = interpolate(q_c);

    let permutation = Permutation::from_circuit(circuit, n);
    let s_sigma = permutation.sigma_polys(&domain, k1, k2);

    let vk = VerifierKey {
        n,
        k1,
        k2,
        q_l: srs.commit(&q_l),
        q_r: srs.commit(&q_r),
        q_o: srs.commit(&q_o),
        q_m: srs.commit(&q_m),
        q_c: srs.commit(&q_c),
        s_sigma: [srs.commit(&s_sigma[0]), srs.commit(&s_sigma[1]), srs.commit(&s_sigma[2])],
        num_public_inputs: circuit.num_public_inputs(),
        kzg: srs.verifier_key(),
    };

    ProverKey {
        domain,
        k1,
        k2,
        q_l,
        q_r,
        q_o,
        q_m,
        q_c,
        s_sigma,
        permutation,
        vk,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::Zero;
    use ark_poly::Polynomial;
    use ark_std::test_rng;

    fn circuit(x: u64, y: u64) -> Circuit<Fr> {
        let mut c = Circuit::<Fr>::new();
        let x = c.alloc(Fr::from(x));
        let y = c.alloc(Fr::from(y));
        let xy = c.mul(x, y);
        let s = c.add(xy, x);
        let k = c.constant(Fr::from(15u64));
        c.assert_equal(s, k);
        c
    }

    #[test]
    fn selectors_interpolate_gates() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(16, &mut rng);
        let c = circuit(3, 4);
        let pk = preprocess(&c, &srs);
        assert_eq!(pk.vk.n, 8);
        for (i, g) in c.gates().iter().enumerate() {
            let w = pk.domain.element(i);
            assert_eq!(pk.q_l.evaluate(&w), g.q_l);
            assert_eq!(pk.q_r.evaluate(&w), g.q_r);
            assert_eq!(pk.q_o.evaluate(&w), g.q_o);
            assert_eq!(pk.q_m.evaluate(&w), g.q_m);
            assert_eq!(pk.q_c.evaluate(&w), g.q_c);
        }
        // padding rows are empty gates
        for i in c.num_gates()..pk.vk.n {
            let w = pk.domain.element(i);
            assert!(pk.q_l.evaluate(&w).is_zero());
            assert!(pk.q_c.evaluate(&w).is_zero());
        }
    }

    #[test]
    fn verifier_key_is_witness_independent() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(16, &mut rng);
        let a = preprocess(&circuit(3, 4), &srs);
        let b = preprocess(&circuit(5, 2), &srs);
        assert_eq!(a.vk.q_l, b.vk.q_l);
        assert_eq!(a.vk.q_m, b.vk.q_m);
        assert_eq!(a.vk.s_sigma, b.vk.s_sigma);
        assert_eq!(a.permutation, b.permutation);
    }
}
