//! Proof struct and its wire format.
//!
//! Serialisation is arkworks' compressed canonical encoding. Deserialising
//! validates that every point is on the curve and in the prime-order
//! subgroup, which the pairing check relies on; never use the `_unchecked`
//! variants on data from the network.

use crate::kzg::{self, Commitment};
use ark_ec::pairing::Pairing;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Validate,
};

/// The evaluations the verifier needs. Everything else is folded into the
/// linearisation polynomial `r(X)`, which the verifier reconstructs as a
/// commitment and checks opens to zero at `zeta`.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Evaluations<F: ark_ff::Field> {
    pub a: F,
    pub b: F,
    pub c: F,
    pub s_sigma1: F,
    pub s_sigma2: F,
    pub z_omega: F,
}

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
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

impl<E: Pairing> Proof<E> {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size(Compress::Yes));
        self.serialize_compressed(&mut buf)
            .expect("writing to a Vec");
        buf
    }

    /// Parse and validate. Fails on malformed input, points off the curve
    /// or outside the subgroup, and non-canonical field elements.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, SerializationError> {
        Self::deserialize_with_mode(bytes, Compress::Yes, Validate::Yes)
    }
}
