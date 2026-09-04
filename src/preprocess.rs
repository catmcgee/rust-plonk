//! Turn a circuit into prover and verifier keys.

use crate::circuit::Circuit;
use crate::kzg::{self, Commitment, Srs};
use crate::permutation::{coset_generators, Permutation};
use crate::transcript::Transcript;
use ark_ec::pairing::Pairing;
use ark_ff::{FftField, Field, One, Zero};
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Radix2EvaluationDomain,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// A polynomial fixed by the circuit, kept in every form the prover needs so
/// nothing about the circuit is recomputed per proof.
#[derive(Clone, Debug)]
pub struct Fixed<F: FftField> {
    pub poly: DensePolynomial<F>,
    /// Evaluations over the domain `H`.
    pub on_h: Vec<F>,
    /// Evaluations over the 4n coset used for the quotient.
    pub on_coset: Vec<F>,
}

#[derive(Clone, Debug)]
pub struct ProverKey<E: Pairing> {
    pub domain: Radix2EvaluationDomain<E::ScalarField>,
    /// Size 4n, shifted off `H` by the field's generator.
    pub coset: Radix2EvaluationDomain<E::ScalarField>,
    pub coset_points: Vec<E::ScalarField>,
    /// `1 / Z_H(x)` for `x` on the coset. `x^n` only takes four values there
    /// (`g^n` times a fourth root of unity), so it's indexed by `i % 4`.
    pub z_h_inv_coset: [E::ScalarField; 4],
    pub k1: E::ScalarField,
    pub k2: E::ScalarField,
    /// `q_l, q_r, q_o, q_m, q_c`
    pub selectors: [Fixed<E::ScalarField>; 5],
    pub s_sigma: [Fixed<E::ScalarField>; 3],
    /// Identity labels `k_col * omega^row`, column-major.
    pub id_labels: Vec<E::ScalarField>,
    pub l1: Fixed<E::ScalarField>,
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
        let mut t = Transcript::new(b"plonk v1 kzg bls12-381");
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
        t.absorb(b"public inputs", public_inputs);
        t
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PreprocessError {
    /// The SRS doesn't have enough powers for this many gates.
    SrsTooSmall { needed: usize, have: usize },
    /// The field has no multiplicative subgroup of the required size.
    NoDomain { size: usize },
}

impl std::fmt::Display for PreprocessError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PreprocessError::SrsTooSmall { needed, have } => {
                write!(f, "srs supports degree {have}, need {needed}")
            }
            PreprocessError::NoDomain { size } => write!(f, "no evaluation domain of size {size}"),
        }
    }
}

impl std::error::Error for PreprocessError {}

/// Smallest domain we'll use. The blinded quotient has degree 3n+5 and is
/// recovered from 4n coset evaluations, which needs n >= 8.
pub const MIN_DOMAIN_SIZE: usize = 8;

/// Domain size for a circuit: gates padded to a power of two.
pub fn domain_size(num_gates: usize) -> usize {
    num_gates.next_power_of_two().max(MIN_DOMAIN_SIZE)
}

/// The SRS degree needed to prove a circuit with this many gates. The
/// blinded quotient's last chunk has degree n+5.
pub fn required_srs_degree(num_gates: usize) -> usize {
    domain_size(num_gates) + 5
}

pub fn preprocess<E: Pairing>(
    circuit: &Circuit<E::ScalarField>,
    srs: &Srs<E>,
) -> Result<ProverKey<E>, PreprocessError> {
    let n = domain_size(circuit.num_gates());
    let domain = Radix2EvaluationDomain::<E::ScalarField>::new(n)
        .ok_or(PreprocessError::NoDomain { size: n })?;
    let needed = required_srs_degree(circuit.num_gates());
    if srs.max_degree() < needed {
        return Err(PreprocessError::SrsTooSmall {
            needed,
            have: srs.max_degree(),
        });
    }

    let (k1, k2) = coset_generators(&domain);

    let coset = Radix2EvaluationDomain::<E::ScalarField>::new(4 * n)
        .and_then(|d| d.get_coset(E::ScalarField::GENERATOR))
        .ok_or(PreprocessError::NoDomain { size: 4 * n })?;
    let coset_points: Vec<E::ScalarField> = coset.elements().collect();
    let z_h_inv_coset = [0, 1, 2, 3].map(|i| {
        (coset_points[i].pow([n as u64]) - E::ScalarField::one())
            .inverse()
            .expect("Z_H doesn't vanish off H")
    });

    let fixed = |mut on_h: Vec<E::ScalarField>| {
        on_h.resize(n, E::ScalarField::zero());
        let poly = DensePolynomial::from_coefficients_vec(domain.ifft(&on_h));
        let on_coset = coset.fft(&poly.coeffs);
        Fixed {
            poly,
            on_h,
            on_coset,
        }
    };

    let mut columns: [Vec<E::ScalarField>; 5] = Default::default();
    for g in circuit.gates() {
        for (col, q) in columns.iter_mut().zip([g.q_l, g.q_r, g.q_o, g.q_m, g.q_c]) {
            col.push(q);
        }
    }
    let selectors = columns.map(fixed);

    let permutation = Permutation::from_circuit(circuit, n);
    let (id_labels, perm_labels) = permutation.labels(&domain, k1, k2);
    let s_sigma = [0, 1, 2].map(|col| fixed(perm_labels[col * n..(col + 1) * n].to_vec()));

    let mut l1_on_h = vec![E::ScalarField::zero(); n];
    l1_on_h[0] = E::ScalarField::one();
    let l1 = fixed(l1_on_h);

    let vk = VerifierKey {
        n,
        k1,
        k2,
        q_l: srs.commit(&selectors[0].poly),
        q_r: srs.commit(&selectors[1].poly),
        q_o: srs.commit(&selectors[2].poly),
        q_m: srs.commit(&selectors[3].poly),
        q_c: srs.commit(&selectors[4].poly),
        s_sigma: [
            srs.commit(&s_sigma[0].poly),
            srs.commit(&s_sigma[1].poly),
            srs.commit(&s_sigma[2].poly),
        ],
        num_public_inputs: circuit.num_public_inputs(),
        kzg: srs.verifier_key(),
    };

    Ok(ProverKey {
        domain,
        coset,
        coset_points,
        z_h_inv_coset,
        k1,
        k2,
        selectors,
        s_sigma,
        id_labels,
        l1,
        permutation,
        vk,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr};
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
        let pk = preprocess(&c, &srs).unwrap();
        assert_eq!(pk.vk.n, 8);
        let [q_l, q_r, q_o, q_m, q_c] = &pk.selectors;
        for (i, g) in c.gates().iter().enumerate() {
            let w = pk.domain.element(i);
            assert_eq!(q_l.poly.evaluate(&w), g.q_l);
            assert_eq!(q_r.poly.evaluate(&w), g.q_r);
            assert_eq!(q_o.poly.evaluate(&w), g.q_o);
            assert_eq!(q_m.poly.evaluate(&w), g.q_m);
            assert_eq!(q_c.poly.evaluate(&w), g.q_c);
            assert_eq!(q_m.on_h[i], g.q_m);
        }
        // padding rows are empty gates
        for i in c.num_gates()..pk.vk.n {
            let w = pk.domain.element(i);
            assert!(q_l.poly.evaluate(&w).is_zero());
            assert!(q_c.poly.evaluate(&w).is_zero());
        }
        // coset evaluations agree with the polynomial
        for (x, v) in pk.coset_points.iter().zip(&q_m.on_coset) {
            assert_eq!(q_m.poly.evaluate(x), *v);
        }
        for (i, x) in pk.coset_points.iter().enumerate() {
            assert_eq!(
                pk.z_h_inv_coset[i % 4] * pk.domain.evaluate_vanishing_polynomial(*x),
                Fr::one()
            );
        }
    }

    #[test]
    fn srs_too_small() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(12, &mut rng);
        assert_eq!(
            preprocess(&circuit(3, 4), &srs).err(),
            Some(PreprocessError::SrsTooSmall {
                needed: 13,
                have: 12
            })
        );
        let srs = Srs::<Bls12_381>::setup(13, &mut rng);
        assert!(preprocess(&circuit(3, 4), &srs).is_ok());
    }

    #[test]
    fn verifier_key_is_witness_independent() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(16, &mut rng);
        let a = preprocess(&circuit(3, 4), &srs).unwrap();
        let b = preprocess(&circuit(5, 2), &srs).unwrap();
        assert_eq!(a.vk.q_l, b.vk.q_l);
        assert_eq!(a.vk.q_m, b.vk.q_m);
        assert_eq!(a.vk.s_sigma, b.vk.s_sigma);
        assert_eq!(a.permutation, b.permutation);
    }
}
