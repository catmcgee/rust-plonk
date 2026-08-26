//! The verifier, following section 8.4 of the paper.

use crate::kzg::{Commitment, Opening};
use crate::poly::{lagrange_at, vanishing_at};
use crate::preprocess::VerifierKey;
use crate::proof::Proof;
use crate::rounds::Rounds;
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::Zero;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    PublicInputCount {
        expected: usize,
        got: usize,
    },
    /// The key's domain size isn't one the field supports.
    BadDomain {
        size: usize,
    },
    /// The evaluation point landed in the domain, which makes the identity
    /// vacuous. Probability n / |F| for an honest prover.
    ZetaInDomain,
    /// The pairing equation didn't hold. This is where a wrong witness, a
    /// tampered proof or wrong public inputs all end up.
    PairingCheckFailed,
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerifyError::PublicInputCount { expected, got } => {
                write!(f, "got {got} public inputs, key expects {expected}")
            }
            VerifyError::BadDomain { size } => write!(f, "no evaluation domain of size {size}"),
            VerifyError::ZetaInDomain => write!(f, "evaluation point is in the domain"),
            VerifyError::PairingCheckFailed => write!(f, "pairing check failed"),
        }
    }
}

impl std::error::Error for VerifyError {}

/// Check a proof against the key and public inputs.
pub fn verify<E: Pairing>(
    vk: &VerifierKey<E>,
    public_inputs: &[E::ScalarField],
    proof: &Proof<E>,
) -> Result<(), VerifyError> {
    if public_inputs.len() != vk.num_public_inputs {
        return Err(VerifyError::PublicInputCount {
            expected: vk.num_public_inputs,
            got: public_inputs.len(),
        });
    }
    let n = vk.n;
    let domain = Radix2EvaluationDomain::<E::ScalarField>::new(n)
        .ok_or(VerifyError::BadDomain { size: n })?;
    let omega = domain.group_gen();
    let ev = &proof.evals;

    // replay the transcript
    let mut rounds = Rounds::start(vk, public_inputs);
    let (beta, gamma) = rounds.wires([&proof.a, &proof.b, &proof.c]);
    let alpha = rounds.accumulator(&proof.z);
    let zeta = rounds.quotient([&proof.t_lo, &proof.t_mid, &proof.t_hi]);
    let v = rounds.evaluations(ev);
    let u = rounds.openings(&proof.w_zeta, &proof.w_zeta_omega);

    // zeta in H would make Z_H(zeta) = 0 and the identity vacuous
    let (zeta_n, z_h, l1) = vanishing_at(n, zeta);
    if z_h.is_zero() {
        return Err(VerifyError::ZetaInDomain);
    }
    // L_i(zeta) only for the first l rows, so the verifier stays O(l).
    let lagrange = lagrange_at(&domain, zeta, public_inputs.len());
    // PI(zeta) = -sum x_i L_i(zeta)
    let pi: E::ScalarField = -public_inputs
        .iter()
        .zip(&lagrange)
        .map(|(x, l)| *x * l)
        .sum::<E::ScalarField>();

    // r(X) = r_0 + (linear combination of committed polynomials). The
    // constant part is computed here, the rest as a commitment [D].
    let (f, g_partial) = ev.permutation_factors(beta, gamma, zeta, vk.k1, vk.k2);
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
    let folded_comm = d
        + proof.a.0 * v
        + proof.b.0 * v2
        + proof.c.0 * v3
        + vk.s_sigma[0].0 * v4
        + vk.s_sigma[1].0 * v5;
    // r(zeta) = 0, i.e. D(zeta) = -r_0
    let folded_value = -r0 + v * ev.a + v2 * ev.b + v3 * ev.c + v4 * ev.s_sigma1 + v5 * ev.s_sigma2;

    let ok = vk.kzg.verify_multi_point(
        &[
            Opening {
                comm: Commitment(folded_comm.into_affine()),
                point: zeta,
                value: folded_value,
                proof: proof.w_zeta,
            },
            Opening {
                comm: proof.z,
                point: zeta * omega,
                value: ev.z_omega,
                proof: proof.w_zeta_omega,
            },
        ],
        u,
    );
    if ok {
        Ok(())
    } else {
        Err(VerifyError::PairingCheckFailed)
    }
}
