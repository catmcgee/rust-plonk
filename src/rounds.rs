//! The Fiat-Shamir schedule, written once so the prover and verifier can't
//! drift apart. Each method absorbs what the prover sends in that round and
//! returns the challenge(s) the next round needs.

use crate::kzg::{self, Commitment};
use crate::preprocess::VerifierKey;
use crate::proof::Evaluations;
use crate::transcript::Transcript;
use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;

pub struct Rounds {
    t: Transcript,
}

impl Rounds {
    pub fn start<E: Pairing>(vk: &VerifierKey<E>, public_inputs: &[E::ScalarField]) -> Self {
        Rounds {
            t: vk.transcript(public_inputs),
        }
    }

    /// Round 1 -> `(beta, gamma)`
    pub fn wires<E: Pairing>(
        &mut self,
        wires: [&Commitment<E>; 3],
    ) -> (E::ScalarField, E::ScalarField) {
        self.t.absorb(b"a", &wires[0].0);
        self.t.absorb(b"b", &wires[1].0);
        self.t.absorb(b"c", &wires[2].0);
        (self.t.challenge(b"beta"), self.t.challenge(b"gamma"))
    }

    /// Round 2 -> `alpha`
    pub fn accumulator<E: Pairing>(&mut self, z: &Commitment<E>) -> E::ScalarField {
        self.t.absorb(b"z", &z.0);
        self.t.challenge(b"alpha")
    }

    /// Round 3 -> `zeta`
    pub fn quotient<E: Pairing>(&mut self, t: [&Commitment<E>; 3]) -> E::ScalarField {
        self.t.absorb(b"t_lo", &t[0].0);
        self.t.absorb(b"t_mid", &t[1].0);
        self.t.absorb(b"t_hi", &t[2].0);
        self.t.challenge(b"zeta")
    }

    /// Round 4 -> `v`
    pub fn evaluations<F: PrimeField>(&mut self, ev: &Evaluations<F>) -> F {
        self.t.absorb(b"evaluations", ev);
        self.t.challenge(b"v")
    }

    /// Round 5 -> `u`, only the verifier needs it
    pub fn openings<E: Pairing>(
        &mut self,
        w_zeta: &kzg::Proof<E>,
        w_zeta_omega: &kzg::Proof<E>,
    ) -> E::ScalarField {
        self.t.absorb(b"w_zeta", &w_zeta.0);
        self.t.absorb(b"w_zeta_omega", &w_zeta_omega.0);
        self.t.challenge(b"u")
    }
}
