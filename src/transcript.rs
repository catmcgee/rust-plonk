//! Fiat-Shamir transcript.
//!
//! Every message the prover would send gets absorbed; challenges are derived by
//! hashing the running state. Absorbing the challenge label back in keeps the
//! state moving so two challenges in a row are different.
//!
//! Challenges are reduced from 64 bytes, not 32: reducing a 256-bit digest
//! modulo the ~255-bit scalar field would leave a bias of a few percent.

use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use sha2::{Digest, Sha256, Sha512};

pub struct Transcript {
    state: [u8; 32],
}

impl Transcript {
    pub fn new(label: &[u8]) -> Self {
        let mut t = Transcript { state: [0u8; 32] };
        t.absorb_bytes(b"init", label);
        t
    }

    pub fn absorb_bytes(&mut self, label: &[u8], bytes: &[u8]) {
        let mut h = Sha256::new();
        h.update(self.state);
        h.update((label.len() as u64).to_le_bytes());
        h.update(label);
        h.update((bytes.len() as u64).to_le_bytes());
        h.update(bytes);
        self.state = h.finalize().into();
    }

    pub fn absorb<T: CanonicalSerialize + ?Sized>(&mut self, label: &[u8], item: &T) {
        let mut buf = Vec::with_capacity(item.compressed_size());
        item.serialize_compressed(&mut buf)
            .expect("serialization into a Vec cannot fail");
        self.absorb_bytes(label, &buf);
    }

    pub fn challenge<F: PrimeField>(&mut self, label: &[u8]) -> F {
        self.absorb_bytes(b"challenge", label);
        let wide = Sha512::new()
            .chain_update(b"squeeze")
            .chain_update(self.state)
            .finalize();
        F::from_le_bytes_mod_order(&wide)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;

    #[test]
    fn deterministic() {
        let mut a = Transcript::new(b"test");
        let mut b = Transcript::new(b"test");
        a.absorb(b"x", &Fr::from(5u64));
        b.absorb(b"x", &Fr::from(5u64));
        assert_eq!(a.challenge::<Fr>(b"c"), b.challenge::<Fr>(b"c"));
    }

    #[test]
    fn different_inputs_different_challenges() {
        let mut a = Transcript::new(b"test");
        let mut b = Transcript::new(b"test");
        a.absorb(b"x", &Fr::from(5u64));
        b.absorb(b"x", &Fr::from(6u64));
        assert_ne!(a.challenge::<Fr>(b"c"), b.challenge::<Fr>(b"c"));

        let mut c = Transcript::new(b"test");
        c.absorb(b"y", &Fr::from(5u64));
        let mut a2 = Transcript::new(b"test");
        a2.absorb(b"x", &Fr::from(5u64));
        assert_ne!(a2.challenge::<Fr>(b"c"), c.challenge::<Fr>(b"c"));
    }

    #[test]
    fn consecutive_challenges_differ() {
        let mut t = Transcript::new(b"test");
        let c1: Fr = t.challenge(b"c");
        let c2: Fr = t.challenge(b"c");
        assert_ne!(c1, c2);
    }
}
