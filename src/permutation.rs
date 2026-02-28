//! Copy constraints as a permutation over the 3n wire slots.
//!
//! Slot `(col, row)` is indexed as `col * n + row`. Slots pointing at the same
//! variable form a cycle; `sigma` maps each slot to the next one in its cycle.
//! The three columns are labelled by the cosets `H`, `k1 H`, `k2 H` so that
//! the identity map `id(col, row) = k_col * omega^row` is injective.

use crate::circuit::{Circuit, Variable};
use ark_ff::{FftField, Field};
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Radix2EvaluationDomain,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Permutation {
    n: usize,
    sigma: Vec<usize>,
}

impl Permutation {
    /// Build from a circuit, padding with the zero variable up to `n` rows.
    pub fn from_circuit<F: Field>(circuit: &Circuit<F>, n: usize) -> Self {
        assert!(n >= circuit.num_gates());
        let mut slots = vec![Circuit::<F>::ZERO; 3 * n];
        for (row, g) in circuit.gates().iter().enumerate() {
            slots[row] = g.a;
            slots[n + row] = g.b;
            slots[2 * n + row] = g.c;
        }
        Self::from_slots(&slots, n)
    }

    pub fn from_slots(slots: &[Variable], n: usize) -> Self {
        assert_eq!(slots.len(), 3 * n);
        let num_vars = slots.iter().map(|v| v.0).max().map_or(0, |m| m + 1);
        let mut occurrences: Vec<Vec<usize>> = vec![Vec::new(); num_vars];
        for (pos, v) in slots.iter().enumerate() {
            occurrences[v.0].push(pos);
        }
        let mut sigma = vec![usize::MAX; 3 * n];
        for cycle in occurrences {
            for (i, &pos) in cycle.iter().enumerate() {
                sigma[pos] = cycle[(i + 1) % cycle.len()];
            }
        }
        debug_assert!(sigma.iter().all(|&s| s != usize::MAX));
        Permutation { n, sigma }
    }

    pub fn n(&self) -> usize {
        self.n
    }

    pub fn sigma(&self) -> &[usize] {
        &self.sigma
    }

    /// The identity labelling and its permuted version, as field elements,
    /// laid out column by column. `id[col*n+row] = k_col * omega^row` and
    /// `perm[col*n+row] = id[sigma[col*n+row]]`.
    pub fn labels<F: FftField>(
        &self,
        domain: &Radix2EvaluationDomain<F>,
        k1: F,
        k2: F,
    ) -> (Vec<F>, Vec<F>) {
        assert_eq!(domain.size(), self.n);
        let ks = [F::one(), k1, k2];
        let mut id = Vec::with_capacity(3 * self.n);
        for k in ks {
            for row in 0..self.n {
                id.push(k * domain.element(row));
            }
        }
        let perm = self.sigma.iter().map(|&s| id[s]).collect();
        (id, perm)
    }

    /// Interpolate `S_sigma1, S_sigma2, S_sigma3` over the domain.
    pub fn sigma_polys<F: FftField>(
        &self,
        domain: &Radix2EvaluationDomain<F>,
        k1: F,
        k2: F,
    ) -> [DensePolynomial<F>; 3] {
        let (_, perm) = self.labels(domain, k1, k2);
        let n = self.n;
        let poly = |col: usize| {
            DensePolynomial::from_coefficients_vec(domain.ifft(&perm[col * n..(col + 1) * n]))
        };
        [poly(0), poly(1), poly(2)]
    }
}

/// Find `k1, k2` such that `H`, `k1 H`, `k2 H` are disjoint cosets.
///
/// `k` is outside `H` iff `k^n != 1`. Smallest integers that work are chosen
/// so the result is deterministic and cheap to recompute on the verifier side.
pub fn coset_generators<F: FftField>(domain: &Radix2EvaluationDomain<F>) -> (F, F) {
    let n = domain.size() as u64;
    let in_h = |x: F| x.pow([n]).is_one();
    let mut k = F::from(2u64);
    while in_h(k) {
        k += F::one();
    }
    let k1 = k;
    k += F::one();
    while in_h(k) || in_h(k / k1) {
        k += F::one();
    }
    (k1, k)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ff::{One, UniformRand};
    use ark_poly::EvaluationDomain;
    use ark_std::test_rng;

    fn small_circuit() -> Circuit<Fr> {
        let mut c = Circuit::<Fr>::new();
        let x = c.alloc(Fr::from(3u64));
        let y = c.alloc(Fr::from(4u64));
        let xy = c.mul(x, y);
        let s = c.add(xy, x);
        let k = c.constant(Fr::from(15u64));
        c.assert_equal(s, k);
        c
    }

    #[test]
    fn sigma_is_a_permutation() {
        let c = small_circuit();
        let n = 8;
        let p = Permutation::from_circuit(&c, n);
        let mut seen = vec![false; 3 * n];
        for &s in p.sigma() {
            assert!(!seen[s]);
            seen[s] = true;
        }
        assert!(seen.iter().all(|&b| b));
    }

    #[test]
    fn cycles_follow_variables() {
        let c = small_circuit();
        let n = 8;
        let p = Permutation::from_circuit(&c, n);
        let mut slots = vec![Circuit::<Fr>::ZERO; 3 * n];
        for (row, g) in c.gates().iter().enumerate() {
            slots[row] = g.a;
            slots[n + row] = g.b;
            slots[2 * n + row] = g.c;
        }
        for (pos, &next) in p.sigma().iter().enumerate() {
            assert_eq!(slots[pos], slots[next]);
        }
    }

    #[test]
    fn cosets_are_disjoint() {
        for log in 1..8 {
            let domain = Radix2EvaluationDomain::<Fr>::new(1 << log).unwrap();
            let (k1, k2) = coset_generators(&domain);
            let n = domain.size() as u64;
            assert!(!k1.pow([n]).is_one());
            assert!(!k2.pow([n]).is_one());
            assert!(!(k2 / k1).pow([n]).is_one());
        }
    }

    /// The whole point: the product over slots of `(w + beta*id + gamma)` equals
    /// the product of `(w + beta*perm + gamma)` iff wires respect the copies.
    #[test]
    fn grand_product_identity() {
        let mut rng = test_rng();
        let c = small_circuit();
        let n = 8;
        let domain = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
        let (k1, k2) = coset_generators(&domain);
        let p = Permutation::from_circuit(&c, n);
        let (id, perm) = p.labels(&domain, k1, k2);

        let mut w = vec![Fr::from(0u64); 3 * n];
        for (row, g) in c.gates().iter().enumerate() {
            w[row] = c.value(g.a);
            w[n + row] = c.value(g.b);
            w[2 * n + row] = c.value(g.c);
        }
        let beta = Fr::rand(&mut rng);
        let gamma = Fr::rand(&mut rng);
        let prod = |labels: &[Fr], w: &[Fr]| {
            w.iter()
                .zip(labels)
                .map(|(w, l)| *w + beta * l + gamma)
                .product::<Fr>()
        };
        assert_eq!(prod(&id, &w), prod(&perm, &w));

        // break one copy: gate 1 is `x*y = xy`, gate 2 uses xy again
        let mut bad = w.clone();
        bad[2 * n + 1] += Fr::from(1u64);
        assert_ne!(prod(&id, &bad), prod(&perm, &bad));
    }
}
