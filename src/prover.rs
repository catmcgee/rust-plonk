//! The prover, following section 8 of the paper.

use crate::circuit::Circuit;
use crate::kzg::Srs;
use crate::poly::{interpolate, vanishing_at};
use crate::preprocess::ProverKey;
use crate::proof::{Evaluations, Proof};
use crate::rounds::Rounds;
use ark_ec::pairing::Pairing;
use ark_ff::{FftField, Field, One, UniformRand, Zero};
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Polynomial,
    Radix2EvaluationDomain,
};
use ark_std::rand::RngCore;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProveError {
    /// The witness doesn't satisfy the circuit.
    Unsatisfied,
    /// The circuit declares a different number of public inputs than the key.
    PublicInputCount { expected: usize, got: usize },
    /// More gates than the key's domain has rows.
    TooManyGates { max: usize, got: usize },
}

impl fmt::Display for ProveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProveError::Unsatisfied => write!(f, "witness does not satisfy the circuit"),
            ProveError::PublicInputCount { expected, got } => {
                write!(f, "circuit has {got} public inputs, key expects {expected}")
            }
            ProveError::TooManyGates { max, got } => {
                write!(f, "circuit has {got} gates, key supports at most {max}")
            }
        }
    }
}

impl std::error::Error for ProveError {}

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

/// `PI(X) = -sum_i x_i L_i(X)`
pub fn public_input_poly<F: FftField>(
    domain: &Radix2EvaluationDomain<F>,
    inputs: &[F],
) -> DensePolynomial<F> {
    let mut evals = vec![F::zero(); domain.size()];
    for (e, x) in evals.iter_mut().zip(inputs) {
        *e = -*x;
    }
    interpolate(domain, &evals)
}

/// Add `(b_k X^k + ... + b_0) * Z_H(X)` with random `b_i`. Leaves the values
/// on the domain alone but hides the polynomial at the opening point.
pub fn blind<F: FftField, R: RngCore>(
    domain: &Radix2EvaluationDomain<F>,
    p: DensePolynomial<F>,
    degree: usize,
    rng: &mut R,
) -> DensePolynomial<F> {
    let mask = DensePolynomial::from_coefficients_vec((0..=degree).map(|_| F::rand(rng)).collect());
    p + mask.mul_by_vanishing_poly(*domain)
}

/// Round 1: wire polynomials, each blinded with a degree-1 mask because they
/// are opened at one point. Degree n+1.
pub fn wire_polys<E: Pairing, R: RngCore>(
    pk: &ProverKey<E>,
    w: &Witness<E::ScalarField>,
    rng: &mut R,
) -> [DensePolynomial<E::ScalarField>; 3] {
    [&w.a, &w.b, &w.c].map(|col| blind(&pk.domain, interpolate(&pk.domain, col), 1, rng))
}

/// Round 2: the permutation accumulator `z(X)`.
///
/// `z(omega^0) = 1` and `z(omega^{i+1}) = z(omega^i) * f_i / g_i` where
/// `f_i` uses the identity labels and `g_i` the permuted ones. If the wires
/// respect the copy constraints the two products agree overall, so the
/// accumulator returns to 1 after a full lap.
///
/// Opened at two points, so blinded with a degree-2 mask. Degree n+2.
pub fn accumulator<E: Pairing, R: RngCore>(
    pk: &ProverKey<E>,
    w: &Witness<E::ScalarField>,
    beta: E::ScalarField,
    gamma: E::ScalarField,
    rng: &mut R,
) -> Result<DensePolynomial<E::ScalarField>, ProveError> {
    let n = pk.domain.size();
    let id = &pk.id_labels;
    let [s1, s2, s3] = &pk.s_sigma;

    let mut nums = Vec::with_capacity(n);
    let mut dens = Vec::with_capacity(n);
    for i in 0..n {
        nums.push(
            (w.a[i] + beta * id[i] + gamma)
                * (w.b[i] + beta * id[n + i] + gamma)
                * (w.c[i] + beta * id[2 * n + i] + gamma),
        );
        dens.push(
            (w.a[i] + beta * s1.on_h[i] + gamma)
                * (w.b[i] + beta * s2.on_h[i] + gamma)
                * (w.c[i] + beta * s3.on_h[i] + gamma),
        );
    }
    if dens.iter().any(|d| d.is_zero()) {
        // gamma happened to cancel a wire value; astronomically unlikely
        return Err(ProveError::Unsatisfied);
    }
    ark_ff::batch_inversion(&mut dens);

    let mut evals = Vec::with_capacity(n);
    let mut acc = E::ScalarField::one();
    for (num, den_inv) in nums.iter().zip(&dens) {
        evals.push(acc);
        acc *= *num * den_inv;
    }
    // The product over all rows is 1 exactly when the wires respect the
    // copy constraints (up to a gamma collision).
    if !acc.is_one() {
        return Err(ProveError::Unsatisfied);
    }
    Ok(blind(&pk.domain, interpolate(&pk.domain, &evals), 2, rng))
}

/// Round 3: the quotient `t(X)`, split into three pieces of degree < n.
///
/// ```text
/// t * Z_H = gate(X) + PI(X)
///         + alpha   * (f(X) z(X) - g(X) z(X omega))
///         + alpha^2 * (z(X) - 1) L_1(X)
/// ```
///
/// Everything is evaluated on a coset of a domain of size 4n, multiplied
/// pointwise and divided by `Z_H` there (which never vanishes off `H`), then
/// interpolated back. With the blinding, `f z` has degree 4n+5 so `t` has
/// degree 3n+5; 4n points pin it down as long as n >= 8. The last chunk
/// therefore has degree up to n+5, not n-1.
///
/// The chunks are then blinded against each other: `b X^n` added to one and
/// `b` subtracted from the next leaves `t_lo + X^n t_mid + X^2n t_hi`
/// unchanged, but the individual commitments no longer determine `t`'s
/// coefficients.
#[allow(clippy::too_many_arguments)]
pub fn quotient<E: Pairing, R: RngCore>(
    pk: &ProverKey<E>,
    wires: &[DensePolynomial<E::ScalarField>; 3],
    z: &DensePolynomial<E::ScalarField>,
    pi: &DensePolynomial<E::ScalarField>,
    beta: E::ScalarField,
    gamma: E::ScalarField,
    alpha: E::ScalarField,
    rng: &mut R,
) -> Result<[DensePolynomial<E::ScalarField>; 3], ProveError> {
    let n = pk.domain.size();
    assert!(n >= crate::preprocess::MIN_DOMAIN_SIZE);
    let coset = &pk.coset;
    let m = coset.size();
    let ev = |p: &DensePolynomial<E::ScalarField>| coset.fft(&p.coeffs);

    let [a, b, c] = [ev(&wires[0]), ev(&wires[1]), ev(&wires[2])];
    let [q_l, q_r, q_o, q_m, q_c] = pk.selectors.each_ref().map(|q| &q.on_coset);
    let [s1, s2, s3] = pk.s_sigma.each_ref().map(|s| &s.on_coset);
    let pi = ev(pi);
    let l1 = &pk.l1.on_coset;
    let zz = ev(z);
    let xs = &pk.coset_points;

    // The 4n-th root of unity to the 4th is omega, so z(X omega) on the
    // coset is z(X) rotated by four positions.
    let z_w = |i: usize| zz[(i + 4) % m];

    let one = E::ScalarField::one();
    let alpha2 = alpha * alpha;
    let mut t = Vec::with_capacity(m);
    for i in 0..m {
        let x = xs[i];
        let gate =
            a[i] * b[i] * q_m[i] + a[i] * q_l[i] + b[i] * q_r[i] + c[i] * q_o[i] + q_c[i] + pi[i];
        let f = (a[i] + beta * x + gamma)
            * (b[i] + beta * pk.k1 * x + gamma)
            * (c[i] + beta * pk.k2 * x + gamma);
        let g = (a[i] + beta * s1[i] + gamma)
            * (b[i] + beta * s2[i] + gamma)
            * (c[i] + beta * s3[i] + gamma);
        let perm = f * zz[i] - g * z_w(i);
        let start = (zz[i] - one) * l1[i];
        t.push((gate + alpha * perm + alpha2 * start) * pk.z_h_inv_coset[i % 4]);
    }
    let mut coeffs = coset.ifft(&t);
    // If the constraints hold the numerator is divisible by Z_H and t has
    // degree at most 3n+5. If they don't, the pointwise division gives some
    // other polynomial of degree < 4n, which usually shows up as nonzero high
    // coefficients. Not always though: on the coset 1/Z_H is
    // (1 + X^n + X^2n + X^3n)/(g^4n - 1), so a remainder R of degree < 6
    // hides entirely under t's top coefficients. That's why `prove` checks
    // satisfiability up front; this is just a backstop.
    let tail = coeffs.split_off(3 * n + 6);
    if !tail.iter().all(|c| c.is_zero()) {
        return Err(ProveError::Unsatisfied);
    }

    let mut hi = coeffs.split_off(2 * n);
    let mut mid = coeffs.split_off(n);
    let mut lo = coeffs;

    let b10 = E::ScalarField::rand(rng);
    let b11 = E::ScalarField::rand(rng);
    lo.push(b10);
    mid[0] -= b10;
    mid.push(b11);
    hi[0] -= b11;
    Ok([
        DensePolynomial::from_coefficients_vec(lo),
        DensePolynomial::from_coefficients_vec(mid),
        DensePolynomial::from_coefficients_vec(hi),
    ])
}

/// The linearisation polynomial `r(X)`.
///
/// Take the identity `t Z_H = gate + alpha perm + alpha^2 start`, fix the
/// evaluations of `a, b, c, S_sigma1, S_sigma2` at `zeta` and of `z` at
/// `zeta omega`, and what's left is linear in the remaining polynomials.
/// The verifier can build its commitment from the proof and the verifier key
/// without knowing the polynomials, and for an honest prover `r(zeta) = 0`.
#[allow(clippy::too_many_arguments)]
pub fn linearisation<E: Pairing>(
    pk: &ProverKey<E>,
    z: &DensePolynomial<E::ScalarField>,
    t: &[DensePolynomial<E::ScalarField>; 3],
    ev: &Evaluations<E::ScalarField>,
    pi_at_zeta: E::ScalarField,
    beta: E::ScalarField,
    gamma: E::ScalarField,
    alpha: E::ScalarField,
    zeta: E::ScalarField,
) -> DensePolynomial<E::ScalarField> {
    let one = E::ScalarField::one();
    let (zeta_n, z_h, l1) = vanishing_at(pk.domain.size(), zeta);
    let konst = |k: E::ScalarField| DensePolynomial::from_coefficients_vec(vec![k]);

    let [q_l, q_r, q_o, q_m, q_c] = pk.selectors.each_ref().map(|q| &q.poly);
    let gate = &(&(&(&(q_m * (ev.a * ev.b)) + &(q_l * ev.a)) + &(q_r * ev.b)) + &(q_o * ev.c))
        + &(q_c + &konst(pi_at_zeta));

    let (f, g_partial) = ev.permutation_factors(beta, gamma, zeta, pk.k1, pk.k2);
    // g = g_partial * (c + beta S_sigma3(X) + gamma)
    let g = &(&pk.s_sigma[2].poly * (g_partial * beta)) + &konst(g_partial * (ev.c + gamma));
    let perm = &(z * f) - &(&g * ev.z_omega);

    let start = &(z - &konst(one)) * l1;

    let quotient = &(&t[0] + &(&t[1] * zeta_n)) + &(&t[2] * (zeta_n * zeta_n));

    &(&(&gate + &(&perm * alpha)) + &(&start * (alpha * alpha))) - &(&quotient * z_h)
}

/// Run all five rounds and produce a proof.
pub fn prove<E: Pairing, R: RngCore>(
    srs: &Srs<E>,
    pk: &ProverKey<E>,
    circuit: &Circuit<E::ScalarField>,
    rng: &mut R,
) -> Result<Proof<E>, ProveError> {
    let n = pk.domain.size();
    let omega = pk.domain.group_gen();
    if circuit.num_public_inputs() != pk.vk.num_public_inputs {
        return Err(ProveError::PublicInputCount {
            expected: pk.vk.num_public_inputs,
            got: circuit.num_public_inputs(),
        });
    }
    if circuit.num_gates() > n {
        return Err(ProveError::TooManyGates {
            max: n,
            got: circuit.num_gates(),
        });
    }
    // Gate by gate check now; the copy constraints are checked when the
    // accumulator is built. Cheaper and more reliable than trying to infer
    // it from the quotient computation.
    if !circuit.is_satisfied() {
        return Err(ProveError::Unsatisfied);
    }
    let public_inputs = circuit.public_inputs();

    let mut rounds = Rounds::start(&pk.vk, &public_inputs);

    // round 1
    let w = Witness::from_circuit(circuit, n);
    let wires = wire_polys(pk, &w, rng);
    let [ca, cb, cc] = wires.each_ref().map(|p| srs.commit(p));

    // round 2
    let (beta, gamma) = rounds.wires([&ca, &cb, &cc]);
    let z = accumulator(pk, &w, beta, gamma, rng)?;
    let cz = srs.commit(&z);

    // round 3
    let alpha = rounds.accumulator(&cz);
    let pi = public_input_poly(&pk.domain, &public_inputs);
    let t = quotient(pk, &wires, &z, &pi, beta, gamma, alpha, rng)?;
    let [ct_lo, ct_mid, ct_hi] = t.each_ref().map(|p| srs.commit(p));

    // round 4
    let zeta = rounds.quotient([&ct_lo, &ct_mid, &ct_hi]);
    let [a, b, c] = &wires;
    let evals = Evaluations {
        a: a.evaluate(&zeta),
        b: b.evaluate(&zeta),
        c: c.evaluate(&zeta),
        s_sigma1: pk.s_sigma[0].poly.evaluate(&zeta),
        s_sigma2: pk.s_sigma[1].poly.evaluate(&zeta),
        z_omega: z.evaluate(&(zeta * omega)),
    };

    // round 5
    let v = rounds.evaluations(&evals);
    let r = linearisation(
        pk,
        &z,
        &t,
        &evals,
        pi.evaluate(&zeta),
        beta,
        gamma,
        alpha,
        zeta,
    );
    if !r.evaluate(&zeta).is_zero() {
        // Can't happen if the checks above passed; refuse to emit garbage.
        return Err(ProveError::Unsatisfied);
    }
    let w_zeta = srs.open_batch(
        &[&r, a, b, c, &pk.s_sigma[0].poly, &pk.s_sigma[1].poly],
        zeta,
        v,
    );
    let w_zeta_omega = srs.open_at(&z, zeta * omega);

    Ok(Proof {
        a: ca,
        b: cb,
        c: cc,
        z: cz,
        t_lo: ct_lo,
        t_mid: ct_mid,
        t_hi: ct_hi,
        evals,
        w_zeta,
        w_zeta_omega,
    })
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
        let pk = preprocess(&c, &srs).unwrap();
        let w = Witness::from_circuit(&c, pk.domain.size());
        let (beta, gamma) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
        let z = accumulator(&pk, &w, beta, gamma, &mut rng).unwrap();
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
            assert_eq!(
                z.evaluate(&(x * pk.domain.group_gen())) * den,
                z.evaluate(&x) * num
            );
        }
    }

    #[test]
    fn blinding_keeps_domain_values() {
        let mut rng = test_rng();
        let domain = Radix2EvaluationDomain::<Fr>::new(8).unwrap();
        let evals: Vec<Fr> = (0..8).map(|_| Fr::rand(&mut rng)).collect();
        let p = interpolate(&domain, &evals);
        let q = blind(&domain, p.clone(), 2, &mut rng);
        assert_ne!(p, q);
        assert_eq!(q.degree(), 10);
        for (i, e) in evals.iter().enumerate() {
            assert_eq!(q.evaluate(&domain.element(i)), *e);
        }
    }

    #[test]
    fn quotient_divides_exactly() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(32, &mut rng);
        let c = circuit();
        let pk = preprocess(&c, &srs).unwrap();
        let n = pk.domain.size();
        let w = Witness::from_circuit(&c, n);
        let (beta, gamma, alpha) = (Fr::rand(&mut rng), Fr::rand(&mut rng), Fr::rand(&mut rng));
        let wires = wire_polys(&pk, &w, &mut rng);
        let z = accumulator(&pk, &w, beta, gamma, &mut rng).unwrap();
        let pi = public_input_poly(&pk.domain, &c.public_inputs());
        let [t_lo, t_mid, t_hi] =
            quotient(&pk, &wires, &z, &pi, beta, gamma, alpha, &mut rng).unwrap();
        assert!(t_lo.degree() <= n && t_mid.degree() <= n && t_hi.degree() < n + 6);

        // reassemble and spot-check the identity at a random point
        let zeta = Fr::rand(&mut rng);
        let zn = zeta.pow([n as u64]);
        let t = t_lo.evaluate(&zeta) + zn * t_mid.evaluate(&zeta) + zn * zn * t_hi.evaluate(&zeta);
        let zh = pk.domain.evaluate_vanishing_polynomial(zeta);
        let [a, b, c] = wires.map(|p| p.evaluate(&zeta));
        let [s1, s2, s3] = pk.s_sigma.each_ref().map(|s| s.poly.evaluate(&zeta));
        let [q_l, q_r, q_o, q_m, q_c] = pk.selectors.each_ref().map(|q| q.poly.evaluate(&zeta));
        let gate = a * b * q_m + a * q_l + b * q_r + c * q_o + q_c + pi.evaluate(&zeta);
        let f = (a + beta * zeta + gamma)
            * (b + beta * pk.k1 * zeta + gamma)
            * (c + beta * pk.k2 * zeta + gamma);
        let g = (a + beta * s1 + gamma) * (b + beta * s2 + gamma) * (c + beta * s3 + gamma);
        let zz = z.evaluate(&zeta);
        let zw = z.evaluate(&(zeta * pk.domain.group_gen()));
        let l1 = pk.l1.poly.evaluate(&zeta);
        let lhs = gate + alpha * (f * zz - g * zw) + alpha * alpha * (zz - Fr::one()) * l1;
        assert_eq!(lhs, t * zh);
    }

    #[test]
    fn bad_witness_has_remainder() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(32, &mut rng);
        let mut c = Circuit::<Fr>::new();
        let x = c.alloc(Fr::from(3u64));
        let y = c.alloc(Fr::from(4u64));
        let xy = c.mul(x, y);
        let k = c.constant(Fr::from(13u64));
        c.assert_equal(xy, k);
        let pk = preprocess(&c, &srs).unwrap();
        let w = Witness::from_circuit(&c, pk.domain.size());
        let (beta, gamma, alpha) = (Fr::rand(&mut rng), Fr::rand(&mut rng), Fr::rand(&mut rng));
        let wires = wire_polys(&pk, &w, &mut rng);
        let z = accumulator(&pk, &w, beta, gamma, &mut rng).unwrap();
        let pi = public_input_poly(&pk.domain, &[]);
        assert_eq!(
            quotient(&pk, &wires, &z, &pi, beta, gamma, alpha, &mut rng).err(),
            Some(ProveError::Unsatisfied)
        );
    }
}
