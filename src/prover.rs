//! The prover, following section 8 of the paper.
//!
//! No blinding yet, so proofs leak information about the witness. That's
//! fine while getting the arithmetic right.

use crate::circuit::Circuit;
use crate::preprocess::ProverKey;
use ark_ec::pairing::Pairing;
use ark_ff::{FftField, Field, One, Zero};
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Polynomial,
    Radix2EvaluationDomain,
};

/// Wire values laid out column by column, padded to the domain size.
pub struct Witness<F> {
    pub a: Vec<F>,
    pub b: Vec<F>,
    pub c: Vec<F>,
}

impl<F: Field> Witness<F> {
    pub fn from_circuit(circuit: &Circuit<F>, n: usize) -> Self {
        let mut w = Witness {
            a: vec![F::zero(); n],
            b: vec![F::zero(); n],
            c: vec![F::zero(); n],
        };
        for (i, g) in circuit.gates().iter().enumerate() {
            w.a[i] = circuit.value(g.a);
            w.b[i] = circuit.value(g.b);
            w.c[i] = circuit.value(g.c);
        }
        w
    }
}

/// Interpolate evaluations over the domain.
pub fn interpolate<F: FftField>(domain: &Radix2EvaluationDomain<F>, evals: &[F]) -> DensePolynomial<F> {
    DensePolynomial::from_coefficients_vec(domain.ifft(evals))
}

/// `p(X * omega)`
pub fn shift<F: FftField>(domain: &Radix2EvaluationDomain<F>, p: &DensePolynomial<F>) -> DensePolynomial<F> {
    let omega = domain.group_gen();
    let mut pow = F::one();
    let coeffs = p
        .coeffs
        .iter()
        .map(|c| {
            let r = *c * pow;
            pow *= omega;
            r
        })
        .collect();
    DensePolynomial::from_coefficients_vec(coeffs)
}

/// `L_1(X)`: 1 at `omega^0`, 0 elsewhere on the domain.
pub fn lagrange_first<F: FftField>(domain: &Radix2EvaluationDomain<F>) -> DensePolynomial<F> {
    let mut evals = vec![F::zero(); domain.size()];
    evals[0] = F::one();
    interpolate(domain, &evals)
}

/// `PI(X) = -sum_i x_i L_i(X)`
pub fn public_input_poly<F: FftField>(domain: &Radix2EvaluationDomain<F>, inputs: &[F]) -> DensePolynomial<F> {
    let mut evals = vec![F::zero(); domain.size()];
    for (e, x) in evals.iter_mut().zip(inputs) {
        *e = -*x;
    }
    interpolate(domain, &evals)
}

/// Round 1: wire polynomials.
pub fn wire_polys<E: Pairing>(pk: &ProverKey<E>, w: &Witness<E::ScalarField>) -> [DensePolynomial<E::ScalarField>; 3] {
    [
        interpolate(&pk.domain, &w.a),
        interpolate(&pk.domain, &w.b),
        interpolate(&pk.domain, &w.c),
    ]
}

/// Round 2: the permutation accumulator `z(X)`.
///
/// `z(omega^0) = 1` and `z(omega^{i+1}) = z(omega^i) * f_i / g_i` where
/// `f_i` uses the identity labels and `g_i` the permuted ones. If the wires
/// respect the copy constraints the two products agree overall, so the
/// accumulator returns to 1 after a full lap.
pub fn accumulator<E: Pairing>(
    pk: &ProverKey<E>,
    w: &Witness<E::ScalarField>,
    beta: E::ScalarField,
    gamma: E::ScalarField,
) -> DensePolynomial<E::ScalarField> {
    let n = pk.domain.size();
    let (id, perm) = pk.permutation.labels(&pk.domain, pk.k1, pk.k2);

    let mut evals = Vec::with_capacity(n);
    let mut acc = E::ScalarField::one();
    for i in 0..n {
        evals.push(acc);
        let num = (w.a[i] + beta * id[i] + gamma)
            * (w.b[i] + beta * id[n + i] + gamma)
            * (w.c[i] + beta * id[2 * n + i] + gamma);
        let den = (w.a[i] + beta * perm[i] + gamma)
            * (w.b[i] + beta * perm[n + i] + gamma)
            * (w.c[i] + beta * perm[2 * n + i] + gamma);
        acc *= num * den.inverse().expect("gamma collided with a wire value");
    }
    debug_assert!(acc.is_one(), "copy constraints not satisfied");
    interpolate(&pk.domain, &evals)
}

/// Round 3: the quotient `t(X)`, split into three pieces of degree < n.
///
/// ```text
/// t * Z_H = gate(X) + PI(X)
///         + alpha   * (f(X) z(X) - g(X) z(X omega))
///         + alpha^2 * (z(X) - 1) L_1(X)
/// ```
pub fn quotient<E: Pairing>(
    pk: &ProverKey<E>,
    wires: &[DensePolynomial<E::ScalarField>; 3],
    z: &DensePolynomial<E::ScalarField>,
    pi: &DensePolynomial<E::ScalarField>,
    beta: E::ScalarField,
    gamma: E::ScalarField,
    alpha: E::ScalarField,
) -> [DensePolynomial<E::ScalarField>; 3] {
    type P<E> = DensePolynomial<<E as Pairing>::ScalarField>;
    let n = pk.domain.size();
    let [a, b, c] = wires;
    // wire(X) + beta * k * X + gamma
    let lin = |k: E::ScalarField, wire: &P<E>| -> P<E> {
        wire + &DensePolynomial::from_coefficients_vec(vec![gamma, beta * k])
    };
    // wire(X) + beta * s(X) + gamma
    let lin_sigma = |s: &P<E>, wire: &P<E>| -> P<E> {
        &(wire + &(s * beta)) + &DensePolynomial::from_coefficients_vec(vec![gamma])
    };

    let gate = &(&(a * b) * &pk.q_m)
        + &(a * &pk.q_l)
        + (b * &pk.q_r)
        + (c * &pk.q_o)
        + pk.q_c.clone()
        + pi.clone();

    let f = &(&lin(E::ScalarField::one(), a) * &lin(pk.k1, b)) * &lin(pk.k2, c);
    let g = &(&lin_sigma(&pk.s_sigma[0], a) * &lin_sigma(&pk.s_sigma[1], b)) * &lin_sigma(&pk.s_sigma[2], c);
    let z_w = shift(&pk.domain, z);
    let perm = &(&f * z) - &(&g * &z_w);

    let l1 = lagrange_first(&pk.domain);
    let z_minus_one = z - &DensePolynomial::from_coefficients_vec(vec![E::ScalarField::one()]);
    let start = &z_minus_one * &l1;

    let numerator = &(&gate + &(&perm * alpha)) + &(&start * (alpha * alpha));
    let (t, rem) = numerator.divide_by_vanishing_poly(pk.domain);
    assert!(rem.is_zero(), "constraints not satisfied: quotient has a remainder");
    assert!(t.degree() < 3 * n, "quotient degree {} too large", t.degree());

    let mut coeffs = t.coeffs;
    coeffs.resize(3 * n, E::ScalarField::zero());
    let hi = coeffs.split_off(2 * n);
    let mid = coeffs.split_off(n);
    [
        DensePolynomial::from_coefficients_vec(coeffs),
        DensePolynomial::from_coefficients_vec(mid),
        DensePolynomial::from_coefficients_vec(hi),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kzg::Srs;
    use crate::preprocess::preprocess;
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::UniformRand;
    use ark_std::test_rng;

    fn circuit() -> Circuit<Fr> {
        let mut c = Circuit::<Fr>::new();
        let x = c.alloc(Fr::from(3u64));
        let y = c.public_input(Fr::from(4u64));
        let xy = c.mul(x, y);
        let s = c.add(xy, x);
        let k = c.constant(Fr::from(15u64));
        c.assert_equal(s, k);
        let y2 = c.mul(y, y);
        let _ = c.add(y2, s);
        c
    }

    #[test]
    fn accumulator_closes() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(32, &mut rng);
        let c = circuit();
        let pk = preprocess(&c, &srs);
        let w = Witness::from_circuit(&c, pk.domain.size());
        let (beta, gamma) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
        let z = accumulator(&pk, &w, beta, gamma);
        assert_eq!(z.evaluate(&Fr::one()), Fr::one());
        // z(omega^n) = z(1) = 1 is the wrap-around; check the recurrence too
        let n = pk.domain.size();
        let (id, perm) = pk.permutation.labels(&pk.domain, pk.k1, pk.k2);
        for i in 0..n {
            let x = pk.domain.element(i);
            let num = (w.a[i] + beta * id[i] + gamma)
                * (w.b[i] + beta * id[n + i] + gamma)
                * (w.c[i] + beta * id[2 * n + i] + gamma);
            let den = (w.a[i] + beta * perm[i] + gamma)
                * (w.b[i] + beta * perm[n + i] + gamma)
                * (w.c[i] + beta * perm[2 * n + i] + gamma);
            assert_eq!(z.evaluate(&(x * pk.domain.group_gen())) * den, z.evaluate(&x) * num);
        }
    }

    #[test]
    fn shift_evaluates_at_omega_x() {
        let mut rng = test_rng();
        let domain = Radix2EvaluationDomain::<Fr>::new(16).unwrap();
        let p = DensePolynomial::<Fr>::rand(20, &mut rng);
        let x = Fr::rand(&mut rng);
        assert_eq!(shift(&domain, &p).evaluate(&x), p.evaluate(&(x * domain.group_gen())));
    }

    #[test]
    fn quotient_divides_exactly() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(32, &mut rng);
        let c = circuit();
        let pk = preprocess(&c, &srs);
        let n = pk.domain.size();
        let w = Witness::from_circuit(&c, n);
        let (beta, gamma, alpha) = (Fr::rand(&mut rng), Fr::rand(&mut rng), Fr::rand(&mut rng));
        let wires = wire_polys(&pk, &w);
        let z = accumulator(&pk, &w, beta, gamma);
        let pi = public_input_poly(&pk.domain, &c.public_inputs());
        let [t_lo, t_mid, t_hi] = quotient(&pk, &wires, &z, &pi, beta, gamma, alpha);
        assert!(t_lo.degree() < n && t_mid.degree() < n && t_hi.degree() < n);

        // reassemble and spot-check the identity at a random point
        let zeta = Fr::rand(&mut rng);
        let zn = zeta.pow([n as u64]);
        let t = t_lo.evaluate(&zeta) + zn * t_mid.evaluate(&zeta) + zn * zn * t_hi.evaluate(&zeta);
        let zh = pk.domain.evaluate_vanishing_polynomial(zeta);
        let [a, b, c] = wires.map(|p| p.evaluate(&zeta));
        let [s1, s2, s3] = [0, 1, 2].map(|i| pk.s_sigma[i].evaluate(&zeta));
        let gate = a * b * pk.q_m.evaluate(&zeta)
            + a * pk.q_l.evaluate(&zeta)
            + b * pk.q_r.evaluate(&zeta)
            + c * pk.q_o.evaluate(&zeta)
            + pk.q_c.evaluate(&zeta)
            + pi.evaluate(&zeta);
        let f = (a + beta * zeta + gamma) * (b + beta * pk.k1 * zeta + gamma) * (c + beta * pk.k2 * zeta + gamma);
        let g = (a + beta * s1 + gamma) * (b + beta * s2 + gamma) * (c + beta * s3 + gamma);
        let zz = z.evaluate(&zeta);
        let zw = z.evaluate(&(zeta * pk.domain.group_gen()));
        let l1 = lagrange_first(&pk.domain).evaluate(&zeta);
        let lhs = gate + alpha * (f * zz - g * zw) + alpha * alpha * (zz - Fr::one()) * l1;
        assert_eq!(lhs, t * zh);
    }

    #[test]
    #[should_panic(expected = "remainder")]
    fn bad_witness_has_remainder() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(32, &mut rng);
        let mut c = Circuit::<Fr>::new();
        let x = c.alloc(Fr::from(3u64));
        let y = c.alloc(Fr::from(4u64));
        let xy = c.mul(x, y);
        let k = c.constant(Fr::from(13u64));
        c.assert_equal(xy, k);
        let pk = preprocess(&c, &srs);
        let w = Witness::from_circuit(&c, pk.domain.size());
        let (beta, gamma, alpha) = (Fr::rand(&mut rng), Fr::rand(&mut rng), Fr::rand(&mut rng));
        let wires = wire_polys(&pk, &w);
        let z = accumulator(&pk, &w, beta, gamma);
        let pi = public_input_poly(&pk.domain, &[]);
        quotient(&pk, &wires, &z, &pi, beta, gamma, alpha);
    }
}
