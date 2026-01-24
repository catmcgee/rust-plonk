use crate::kzg::{self, Commitment};
use ark_ec::pairing::Pairing;

/// The evaluations the verifier needs. Everything else is folded into the
/// linearisation polynomial `r(X)`, which the verifier reconstructs as a
/// commitment and checks opens to zero at `zeta`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Evaluations<F> {
    pub a: F,
    pub b: F,
    pub c: F,
    pub s_sigma1: F,
    pub s_sigma2: F,
    pub z_omega: F,
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
    /// Batched opening of `r, a, b, c, S_sigma1, S_sigma2` at `zeta`.
    pub w_zeta: kzg::Proof<E>,
    /// Opening of `z` at `zeta * omega`.
    pub w_zeta_omega: kzg::Proof<E>,
}
