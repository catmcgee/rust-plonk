//! Prove knowledge of p, q with p * q = n, p, q < 2^32, without revealing them.
//!
//! The range checks matter: without them p = n, q = 1 works, and so does any
//! p with q = n / p in the field.

use ark_bls12_381::{Bls12_381, Fr};
use ark_ff::Field;
use plonk::{preprocess, prove, verify, Circuit, Srs};
use std::time::Instant;

fn factors(p: u64, q: u64) -> Circuit<Fr> {
    let mut c = Circuit::<Fr>::new();
    let n = c.public_input(Fr::from(p * q));
    let p = c.alloc(Fr::from(p));
    let q = c.alloc(Fr::from(q));
    c.to_bits(p, 32);
    c.to_bits(q, 32);
    let one = c.constant(Fr::from(1u64));
    let p_minus_one = c.sub(p, one);
    let q_minus_one = c.sub(q, one);
    // neither factor is 1: (p-1)(q-1) has an inverse
    let prod = c.mul(p_minus_one, q_minus_one);
    let inv = c.alloc(c.value(prod).inverse().unwrap_or_default());
    let should_be_one = c.mul(prod, inv);
    c.assert_equal(should_be_one, one);
    let pq = c.mul(p, q);
    c.assert_equal(pq, n);
    c
}

fn main() {
    let mut rng = rand::thread_rng();
    let circuit = factors(3_331_129, 1_000_003);
    println!(
        "{} gates, satisfied: {}",
        circuit.num_gates(),
        circuit.is_satisfied()
    );

    // With TRUSTED_SETUP pointing at c-kzg's trusted_setup.txt the proof is
    // made against the Ethereum ceremony rather than a locally sampled tau.
    let srs = match std::env::var("TRUSTED_SETUP") {
        Ok(path) => {
            let text = std::fs::read_to_string(path).expect("read trusted setup");
            let srs = Srs::<Bls12_381>::from_ceremony_text(&text).expect("parse");
            println!("using ceremony srs, degree {}", srs.max_degree());
            srs
        }
        Err(_) => Srs::<Bls12_381>::setup(512, &mut rng),
    };
    let pk = preprocess(&circuit, &srs).unwrap();

    let t = Instant::now();
    let proof = prove(&srs, &pk, &circuit, &mut rng).expect("witness is valid");
    println!(
        "proved in {:?}, {} bytes",
        t.elapsed(),
        proof.to_bytes().len()
    );

    let t = Instant::now();
    let ok = verify(&pk.vk, &circuit.public_inputs(), &proof).is_ok();
    println!("verified in {:?}: {ok}", t.elapsed());

    let bad = factors(3_331_129 * 1_000_003, 1);
    println!(
        "trivial factorisation satisfies circuit: {}",
        bad.is_satisfied()
    );
}
