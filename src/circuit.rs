//! Circuit builder for the vanilla PLONK gate
//!
//! ```text
//! q_L * a + q_R * b + q_O * c + q_M * a * b + q_C = 0
//! ```
//!
//! Every gate has three wire slots (`a`, `b`, `c`) which each point at a
//! variable. Two slots pointing at the same variable is a copy constraint,
//! enforced later by the permutation argument.
//!
//! Public inputs are the first `l` rows: each is a gate `1 * a + PI_i = 0`
//! where `PI_i = -x_i` lives in the public input polynomial rather than in
//! `q_C`, so the verifier can supply it.

use ark_ff::Field;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Variable(pub(crate) usize);

impl Variable {
    /// Every circuit's variable 0 is a constant zero, used to fill wire
    /// slots a gate doesn't use.
    pub const ZERO: Variable = Variable(0);
}

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
    /// Public input gates first, then everything else.
    gates: Vec<Gate<F>>,
    /// Witness assignment, indexed by `Variable`.
    values: Vec<F>,
    public_inputs: Vec<Variable>,
    /// Union-find over variables. `assert_equal` merges two variables so
    /// their wire slots end up in one permutation cycle, costing no gate.
    parent: Vec<usize>,
    constants: HashMap<F, Variable>,
}

impl<F: Field> Circuit<F> {
    /// A fresh circuit with `Variable::ZERO` allocated and constrained.
    pub fn new() -> Self {
        let mut c = Circuit {
            gates: Vec::new(),
            values: vec![F::zero()],
            public_inputs: Vec::new(),
            parent: vec![0],
            constants: HashMap::new(),
        };
        // 1 * zero + 0 = 0
        c.gate(
            Variable::ZERO,
            Variable::ZERO,
            Variable::ZERO,
            F::one(),
            F::zero(),
            F::zero(),
            F::zero(),
            F::zero(),
        );
        c
    }

    pub fn num_gates(&self) -> usize {
        self.gates.len()
    }

    pub fn num_variables(&self) -> usize {
        self.values.len()
    }

    pub fn gates(&self) -> &[Gate<F>] {
        &self.gates
    }

    pub fn num_public_inputs(&self) -> usize {
        self.public_inputs.len()
    }

    /// Public input values, in the order they were declared.
    pub fn public_inputs(&self) -> Vec<F> {
        self.public_inputs.iter().map(|v| self.value(*v)).collect()
    }

    pub fn value(&self, v: Variable) -> F {
        self.values[v.0]
    }

    /// The representative of `v`'s equivalence class under `assert_equal`.
    /// This is what the permutation argument sees.
    pub fn root(&self, v: Variable) -> Variable {
        let mut i = v.0;
        while self.parent[i] != i {
            i = self.parent[i];
        }
        Variable(i)
    }

    /// Allocate an unconstrained witness variable.
    pub fn alloc(&mut self, value: F) -> Variable {
        self.values.push(value);
        self.parent.push(self.values.len() - 1);
        Variable(self.values.len() - 1)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn gate(
        &mut self,
        a: Variable,
        b: Variable,
        c: Variable,
        q_l: F,
        q_r: F,
        q_o: F,
        q_m: F,
        q_c: F,
    ) {
        for v in [a, b, c] {
            assert!(v.0 < self.values.len(), "unknown variable {:?}", v);
        }
        self.gates.push(Gate {
            a,
            b,
            c,
            q_l,
            q_r,
            q_o,
            q_m,
            q_c,
        });
    }

    /// Declare a public input. Its gate is placed before all other gates so
    /// row `i` of the trace corresponds to public input `i`.
    pub fn public_input(&mut self, value: F) -> Variable {
        let v = self.alloc(value);
        let row = self.public_inputs.len();
        self.gates.insert(
            row,
            Gate {
                a: v,
                b: Variable::ZERO,
                c: Variable::ZERO,
                q_l: F::one(),
                q_r: F::zero(),
                q_o: F::zero(),
                q_m: F::zero(),
                q_c: F::zero(),
            },
        );
        self.public_inputs.push(v);
        v
    }

    /// A variable fixed to `k`. Repeated constants share one variable.
    pub fn constant(&mut self, k: F) -> Variable {
        if let Some(v) = self.constants.get(&k) {
            return *v;
        }
        let v = self.alloc(k);
        self.constants.insert(k, v);
        // v - k = 0
        self.gate(
            v,
            Variable::ZERO,
            Variable::ZERO,
            F::one(),
            F::zero(),
            F::zero(),
            F::zero(),
            -k,
        );
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
        self.gate(
            x,
            y,
            z,
            F::zero(),
            F::zero(),
            -F::one(),
            F::one(),
            F::zero(),
        );
        z
    }

    pub fn sub(&mut self, x: Variable, y: Variable) -> Variable {
        let z = self.alloc(self.value(x) - self.value(y));
        // x - y - z = 0
        self.gate(
            x,
            y,
            z,
            F::one(),
            -F::one(),
            -F::one(),
            F::zero(),
            F::zero(),
        );
        z
    }

    pub fn add_const(&mut self, x: Variable, k: F) -> Variable {
        let z = self.alloc(self.value(x) + k);
        // x + k - z = 0
        self.gate(
            x,
            Variable::ZERO,
            z,
            F::one(),
            F::zero(),
            -F::one(),
            F::zero(),
            k,
        );
        z
    }

    pub fn mul_const(&mut self, x: Variable, k: F) -> Variable {
        let z = self.alloc(self.value(x) * k);
        // k * x - z = 0
        self.gate(
            x,
            Variable::ZERO,
            z,
            k,
            F::zero(),
            -F::one(),
            F::zero(),
            F::zero(),
        );
        z
    }

    /// `x * y + z`, in one gate.
    pub fn mul_add(&mut self, x: Variable, y: Variable, z: Variable) -> Variable {
        let out = self.alloc(self.value(x) * self.value(y) + self.value(z));
        // x*y + z - out = 0 ... but that needs four wires. Use two gates.
        // TODO: a wider gate would make this one row.
        let xy = self.mul(x, y);
        self.gate(
            xy,
            z,
            out,
            F::one(),
            F::one(),
            -F::one(),
            F::zero(),
            F::zero(),
        );
        out
    }

    /// Constrain `x` to be 0 or 1: `x * x - x = 0`.
    pub fn assert_bool(&mut self, x: Variable) {
        self.gate(
            x,
            x,
            Variable::ZERO,
            -F::one(),
            F::zero(),
            F::zero(),
            F::one(),
            F::zero(),
        );
    }

    pub fn assert_const(&mut self, x: Variable, k: F) {
        // x - k = 0
        self.gate(
            x,
            Variable::ZERO,
            Variable::ZERO,
            F::one(),
            F::zero(),
            F::zero(),
            F::zero(),
            -k,
        );
    }

    /// Split `x` into `bits` little-endian bits, each constrained boolean,
    /// and constrain the recomposition. Fails the circuit if `x` doesn't fit.
    pub fn to_bits(&mut self, x: Variable, bits: usize) -> Vec<Variable>
    where
        F: ark_ff::PrimeField,
    {
        use ark_ff::BigInteger;
        let value = self.value(x).into_bigint();
        let mut out = Vec::with_capacity(bits);
        let mut acc = Variable::ZERO;
        let mut pow = F::one();
        for i in 0..bits {
            let bit = self.alloc(if value.get_bit(i) {
                F::one()
            } else {
                F::zero()
            });
            self.assert_bool(bit);
            // acc' = acc + 2^i * bit
            let next = self.alloc(self.value(acc) + pow * self.value(bit));
            self.gate(
                acc,
                bit,
                next,
                F::one(),
                pow,
                -F::one(),
                F::zero(),
                F::zero(),
            );
            acc = next;
            out.push(bit);
            pow.double_in_place();
        }
        self.assert_equal(acc, x);
        out
    }

    /// Constrain `x == y`. Free: the two variables are merged, so every
    /// wire slot referring to either lands in the same copy cycle.
    pub fn assert_equal(&mut self, x: Variable, y: Variable) {
        let (rx, ry) = (self.root(x), self.root(y));
        if rx != ry {
            self.parent[ry.0] = rx.0;
        }
    }

    /// Check every gate against the current assignment. Useful in tests; the
    /// prover doesn't rely on it.
    pub fn is_satisfied(&self) -> bool {
        let merged_agree = (0..self.values.len()).all(|i| {
            let v = Variable(i);
            self.value(v) == self.value(self.root(v))
        });
        let pi = self.public_inputs();
        merged_agree
            && self.gates.iter().enumerate().all(|(i, g)| {
                let (a, b, c) = (self.value(g.a), self.value(g.b), self.value(g.c));
                let pi_i = pi.get(i).map_or(F::zero(), |x| -*x);
                (g.q_l * a + g.q_r * b + g.q_o * c + g.q_m * a * b + g.q_c + pi_i).is_zero()
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
        assert_eq!(c.root(s), c.root(fifteen));
        assert_eq!(c.constant(Fr::from(15u64)), fifteen);
    }

    #[test]
    fn merged_variables_must_agree() {
        let mut c = Circuit::<Fr>::new();
        let x = c.alloc(Fr::from(3u64));
        let y = c.alloc(Fr::from(4u64));
        assert!(c.is_satisfied());
        c.assert_equal(x, y);
        assert!(!c.is_satisfied());
        // chains resolve to one root
        let mut c = Circuit::<Fr>::new();
        let vs: Vec<_> = (0..5).map(|_| c.alloc(Fr::from(9u64))).collect();
        for w in vs.windows(2) {
            c.assert_equal(w[1], w[0]);
        }
        assert!(vs.iter().all(|v| c.root(*v) == c.root(vs[0])));
        assert!(c.is_satisfied());
    }

    #[test]
    fn helpers() {
        let mut c = Circuit::<Fr>::new();
        let x = c.alloc(Fr::from(10u64));
        let y = c.alloc(Fr::from(3u64));
        let d = c.sub(x, y);
        c.assert_const(d, Fr::from(7u64));
        let e = c.add_const(d, Fr::from(5u64));
        c.assert_const(e, Fr::from(12u64));
        let f = c.mul_const(e, Fr::from(2u64));
        c.assert_const(f, Fr::from(24u64));
        let g = c.mul_add(x, y, f);
        c.assert_const(g, Fr::from(54u64));
        assert!(c.is_satisfied());
    }

    #[test]
    fn booleans_and_bits() {
        let mut c = Circuit::<Fr>::new();
        let one = c.alloc(Fr::from(1u64));
        c.assert_bool(one);
        let two = c.alloc(Fr::from(2u64));
        c.assert_bool(two);
        assert!(!c.is_satisfied());

        let mut c = Circuit::<Fr>::new();
        let x = c.alloc(Fr::from(0b1011u64));
        let bits = c.to_bits(x, 4);
        assert!(c.is_satisfied());
        assert_eq!(
            bits.iter().map(|b| c.value(*b)).collect::<Vec<_>>(),
            [1, 1, 0, 1].map(Fr::from)
        );
        // doesn't fit in 3 bits
        let mut c = Circuit::<Fr>::new();
        let x = c.alloc(Fr::from(0b1011u64));
        c.to_bits(x, 3);
        assert!(!c.is_satisfied());
    }

    #[test]
    fn public_inputs_come_first() {
        let mut c = Circuit::<Fr>::new();
        let x = c.alloc(Fr::from(3u64));
        let y = c.public_input(Fr::from(4u64));
        let xy = c.mul(x, y);
        let out = c.public_input(Fr::from(12u64));
        c.assert_equal(xy, out);
        assert!(c.is_satisfied());
        assert_eq!(c.num_public_inputs(), 2);
        assert_eq!(c.public_inputs(), vec![Fr::from(4u64), Fr::from(12u64)]);
        assert_eq!(c.gates()[0].a, y);
        assert_eq!(c.gates()[1].a, out);
        assert_eq!(c.gates()[2].a, Variable::ZERO);
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
