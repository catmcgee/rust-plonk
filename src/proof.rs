use crate::kzg::{self, Commitment};
use ark_ec::pairing::Pairing;

/// Openings at `zeta` (and `z` at `zeta * omega`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Evaluations<F> {
    pub a: F,
    pub b: F,
    pub c: F,
    pub z: F,
    pub z_omega: F,
    pub t_lo: F,
    pub t_mid: F,
    pub t_hi: F,
    pub q_l: F,
    pub q_r: F,
    pub q_o: F,
    pub q_m: F,
    pub q_c: F,
    pub s_sigma: [F; 3],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof<E: Pairing> {
    pub a: Commitment<E>,
    pub b: Commitment<E>,
    pub c: Commitment<E>,
    pub z: Commitment<E>,
    pub t_lo: Commitment<E>,
    pub t_mid: Commitment<E>,
    pub t_hi: Commitment<E>,
    pub evals: Evaluations<E::ScalarField>,
    /// Batched opening of everything at `zeta`.
    pub w_zeta: kzg::Proof<E>,
    /// Opening of `z` at `zeta * omega`.
    pub w_zeta_omega: kzg::Proof<E>,
}
