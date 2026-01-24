//! The verifier, following section 8.4 of the paper.

use crate::kzg::Commitment;
use crate::preprocess::VerifierKey;
use crate::proof::Proof;
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::{Field, One, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

pub fn verify<E: Pairing>(vk: &VerifierKey<E>, public_inputs: &[E::ScalarField], proof: &Proof<E>) -> bool {
    if public_inputs.len() != vk.num_public_inputs {
        return false;
    }
    let n = vk.n;
    let Some(domain) = Radix2EvaluationDomain::<E::ScalarField>::new(n) else {
        return false;
    };
    let omega = domain.group_gen();
    let ev = &proof.evals;
    let one = E::ScalarField::one();

    // replay the transcript
    let mut transcript = vk.transcript(public_inputs);
    transcript.absorb(b"a", &proof.a.0);
    transcript.absorb(b"b", &proof.b.0);
    transcript.absorb(b"c", &proof.c.0);
    let beta: E::ScalarField = transcript.challenge(b"beta");
    let gamma: E::ScalarField = transcript.challenge(b"gamma");
    transcript.absorb(b"z", &proof.z.0);
    let alpha: E::ScalarField = transcript.challenge(b"alpha");
    transcript.absorb(b"t_lo", &proof.t_lo.0);
    transcript.absorb(b"t_mid", &proof.t_mid.0);
    transcript.absorb(b"t_hi", &proof.t_hi.0);
    let zeta: E::ScalarField = transcript.challenge(b"zeta");
    transcript.absorb(b"a(zeta)", &ev.a);
    transcript.absorb(b"b(zeta)", &ev.b);
    transcript.absorb(b"c(zeta)", &ev.c);
    transcript.absorb(b"s_sigma1(zeta)", &ev.s_sigma1);
    transcript.absorb(b"s_sigma2(zeta)", &ev.s_sigma2);
    transcript.absorb(b"z(zeta omega)", &ev.z_omega);
    let v: E::ScalarField = transcript.challenge(b"v");
    transcript.absorb(b"w_zeta", &proof.w_zeta.0);
    transcript.absorb(b"w_zeta_omega", &proof.w_zeta_omega.0);
    let u: E::ScalarField = transcript.challenge(b"u");

    // zeta in H would make Z_H(zeta) = 0 and the identity vacuous
    let zeta_n = zeta.pow([n as u64]);
    let z_h = zeta_n - one;
    if z_h.is_zero() {
        return false;
    }
    // L_1(zeta) = (zeta^n - 1) / (n (zeta - 1))
    let l1 = z_h / (E::ScalarField::from(n as u64) * (zeta - one));
    // PI(zeta) = -sum x_i L_i(zeta)
    let lagrange = domain.evaluate_all_lagrange_coefficients(zeta);
    let pi: E::ScalarField = -public_inputs
        .iter()
        .zip(&lagrange)
        .map(|(x, l)| *x * l)
        .sum::<E::ScalarField>();

    // r(X) = r_0 + (linear combination of committed polynomials). The
    // constant part is computed here, the rest as a commitment [D].
    let f = (ev.a + beta * zeta + gamma) * (ev.b + beta * vk.k1 * zeta + gamma) * (ev.c + beta * vk.k2 * zeta + gamma);
    let g_partial = (ev.a + beta * ev.s_sigma1 + gamma) * (ev.b + beta * ev.s_sigma2 + gamma);
    let r0 = pi - l1 * alpha * alpha - alpha * g_partial * (ev.c + gamma) * ev.z_omega;

    let alpha2 = alpha * alpha;
    let d = vk.q_m.0 * (ev.a * ev.b)
        + vk.q_l.0 * ev.a
        + vk.q_r.0 * ev.b
        + vk.q_o.0 * ev.c
        + vk.q_c.0
        + proof.z.0 * (alpha * f + alpha2 * l1)
        - vk.s_sigma[2].0 * (alpha * g_partial * beta * ev.z_omega)
        - (proof.t_lo.0 + proof.t_mid.0 * zeta_n + proof.t_hi.0 * (zeta_n * zeta_n)) * z_h;

    // fold [D], [a], [b], [c], [S_sigma1], [S_sigma2] with v, same order as the prover
    let v2 = v * v;
    let v3 = v2 * v;
    let v4 = v3 * v;
    let v5 = v4 * v;
    let folded_comm = d + proof.a.0 * v + proof.b.0 * v2 + proof.c.0 * v3 + vk.s_sigma[0].0 * v4 + vk.s_sigma[1].0 * v5;
    // r(zeta) = 0, i.e. D(zeta) = -r_0
    let folded_value = -r0 + v * ev.a + v2 * ev.b + v3 * ev.c + v4 * ev.s_sigma1 + v5 * ev.s_sigma2;

    vk.kzg.verify_multi_point(
        &[
            (Commitment(folded_comm.into_affine()), zeta, folded_value, proof.w_zeta),
            (proof.z, zeta * omega, ev.z_omega, proof.w_zeta_omega),
        ],
        u,
    )
}
