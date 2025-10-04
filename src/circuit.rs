//! Circuit builder for the vanilla PLONK gate
//!
//! ```text
//! q_L * a + q_R * b + q_O * c + q_M * a * b + q_C = 0
//! ```
//!
//! Every gate has three wire slots (`a`, `b`, `c`) which each point at a
//! variable. Two slots pointing at the same variable is a copy constraint,
//! enforced later by the permutation argument.

use ark_ff::Field;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Variable(pub(crate) usize);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gate<F: Field> {
    pub a: Variable,
    pub b: Variable,
    pub c: Variable,
    pub q_l: F,
    pub q_r: F,
    pub q_o: F,
    pub q_m: F,
    pub q_c: F,
}

#[derive(Clone, Debug)]
pub struct Circuit<F: Field> {
    gates: Vec<Gate<F>>,
    /// Witness assignment, indexed by `Variable`.
    values: Vec<F>,
}

impl<F: Field> Circuit<F> {
    /// A fresh circuit. Variable 0 is reserved as a constant zero and is used
    /// to fill wire slots a gate doesn't use.
    pub fn new() -> Self {
        let mut c = Circuit {
            gates: Vec::new(),
            values: vec![F::zero()],
        };
        // 1 * zero + 0 = 0
        c.gate(Self::ZERO, Self::ZERO, Self::ZERO, F::one(), F::zero(), F::zero(), F::zero(), F::zero());
        c
    }

    pub const ZERO: Variable = Variable(0);

    pub fn num_gates(&self) -> usize {
        self.gates.len()
    }

    pub fn num_variables(&self) -> usize {
        self.values.len()
    }

    pub fn gates(&self) -> &[Gate<F>] {
        &self.gates
    }

    pub fn value(&self, v: Variable) -> F {
        self.values[v.0]
    }

    /// Allocate an unconstrained witness variable.
    pub fn alloc(&mut self, value: F) -> Variable {
        self.values.push(value);
        Variable(self.values.len() - 1)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn gate(&mut self, a: Variable, b: Variable, c: Variable, q_l: F, q_r: F, q_o: F, q_m: F, q_c: F) {
        for v in [a, b, c] {
            assert!(v.0 < self.values.len(), "unknown variable {:?}", v);
        }
        self.gates.push(Gate { a, b, c, q_l, q_r, q_o, q_m, q_c });
    }

    /// A variable fixed to `k`.
    pub fn constant(&mut self, k: F) -> Variable {
        let v = self.alloc(k);
        // v - k = 0
        self.gate(v, Self::ZERO, Self::ZERO, F::one(), F::zero(), F::zero(), F::zero(), -k);
        v
    }

    pub fn add(&mut self, x: Variable, y: Variable) -> Variable {
        let z = self.alloc(self.value(x) + self.value(y));
        // x + y - z = 0
        self.gate(x, y, z, F::one(), F::one(), -F::one(), F::zero(), F::zero());
        z
    }

    pub fn mul(&mut self, x: Variable, y: Variable) -> Variable {
        let z = self.alloc(self.value(x) * self.value(y));
        // x * y - z = 0
        self.gate(x, y, z, F::zero(), F::zero(), -F::one(), F::one(), F::zero());
        z
    }

    pub fn assert_equal(&mut self, x: Variable, y: Variable) {
        // x - y = 0
        self.gate(x, y, Self::ZERO, F::one(), -F::one(), F::zero(), F::zero(), F::zero());
    }

    /// Check every gate against the current assignment. Useful in tests; the
    /// prover doesn't rely on it.
    pub fn is_satisfied(&self) -> bool {
        self.gates.iter().all(|g| {
            let (a, b, c) = (self.value(g.a), self.value(g.b), self.value(g.c));
            (g.q_l * a + g.q_r * b + g.q_o * c + g.q_m * a * b + g.q_c).is_zero()
        })
    }
}

impl<F: Field> Default for Circuit<F> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;

    #[test]
    fn arithmetic() {
        let mut c = Circuit::<Fr>::new();
        let x = c.alloc(Fr::from(3u64));
        let y = c.alloc(Fr::from(4u64));
        let xy = c.mul(x, y);
        let s = c.add(xy, x);
        let fifteen = c.constant(Fr::from(15u64));
        c.assert_equal(s, fifteen);
        assert!(c.is_satisfied());
        assert_eq!(c.value(s), Fr::from(15u64));
    }

    #[test]
    fn bad_witness() {
        let mut c = Circuit::<Fr>::new();
        let x = c.alloc(Fr::from(3u64));
        let y = c.alloc(Fr::from(4u64));
        let xy = c.mul(x, y);
        let thirteen = c.constant(Fr::from(13u64));
        c.assert_equal(xy, thirteen);
        assert!(!c.is_satisfied());
    }
}
