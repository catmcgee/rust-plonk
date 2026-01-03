//! The verifier.
//!
//! First version: the prover opens every polynomial at `zeta`, and the
//! verifier checks the polynomial identity in the field, then checks the
//! openings against the commitments. Simple, but the proof is bigger than it
//! needs to be.

use crate::preprocess::VerifierKey;
use crate::proof::Proof;
use ark_ec::pairing::Pairing;
use ark_ff::{Field, One, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

pub fn verify<E: Pairing>(vk: &VerifierKey<E>, public_inputs: &[E::ScalarField], proof: &Proof<E>) -> bool {
    if public_inputs.len() != vk.num_public_inputs {
        return false;
    }
    let n = vk.n;
    let domain = Radix2EvaluationDomain::<E::ScalarField>::new(n).unwrap();
    let omega = domain.group_gen();
    let ev = &proof.evals;

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
    let at_zeta = [
        ev.a, ev.b, ev.c, ev.z, ev.t_lo, ev.t_mid, ev.t_hi,
        ev.q_l, ev.q_r, ev.q_o, ev.q_m, ev.q_c,
        ev.s_sigma[0], ev.s_sigma[1], ev.s_sigma[2],
    ];
    for v in &at_zeta {
        transcript.absorb(b"eval", v);
    }
    transcript.absorb(b"eval", &ev.z_omega);
    let v: E::ScalarField = transcript.challenge(b"v");

    // zeta in H would make Z_H(zeta) = 0 and the identity vacuous
    let zeta_n = zeta.pow([n as u64]);
    let z_h = zeta_n - E::ScalarField::one();
    if z_h.is_zero() {
        return false;
    }
    // L_1(zeta) = (zeta^n - 1) / (n (zeta - 1))
    let l1 = z_h / (E::ScalarField::from(n as u64) * (zeta - E::ScalarField::one()));
    // PI(zeta) = -sum x_i L_i(zeta), with L_i(zeta) = omega^i (zeta^n - 1) / (n (zeta - omega^i))
    let lagrange = domain.evaluate_all_lagrange_coefficients(zeta);
    let pi: E::ScalarField = -public_inputs
        .iter()
        .zip(&lagrange)
        .map(|(x, l)| *x * l)
        .sum::<E::ScalarField>();

    // the identity at zeta
    let gate = ev.a * ev.b * ev.q_m + ev.a * ev.q_l + ev.b * ev.q_r + ev.c * ev.q_o + ev.q_c + pi;
    let f = (ev.a + beta * zeta + gamma)
        * (ev.b + beta * vk.k1 * zeta + gamma)
        * (ev.c + beta * vk.k2 * zeta + gamma);
    let g = (ev.a + beta * ev.s_sigma[0] + gamma)
        * (ev.b + beta * ev.s_sigma[1] + gamma)
        * (ev.c + beta * ev.s_sigma[2] + gamma);
    let lhs = gate + alpha * (f * ev.z - g * ev.z_omega) + alpha * alpha * (ev.z - E::ScalarField::one()) * l1;
    let t = ev.t_lo + zeta_n * ev.t_mid + zeta_n * zeta_n * ev.t_hi;
    if lhs != t * z_h {
        return false;
    }

    // the openings
    let comms = [
        proof.a, proof.b, proof.c, proof.z, proof.t_lo, proof.t_mid, proof.t_hi,
        vk.q_l, vk.q_r, vk.q_o, vk.q_m, vk.q_c,
        vk.s_sigma[0], vk.s_sigma[1], vk.s_sigma[2],
    ];
    vk.kzg.verify_batch(&comms, zeta, &at_zeta, v, &proof.w_zeta)
        && vk.kzg.verify(&proof.z, zeta * omega, ev.z_omega, &proof.w_zeta_omega)
}
