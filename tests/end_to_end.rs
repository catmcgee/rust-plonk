use ark_bls12_381::{Bls12_381, Fr};
use ark_std::test_rng;
use plonk::{preprocess, prove, verify, Circuit, Srs};

/// x^3 + x + 5 = y, with y public. The classic.
fn cubic(x: u64, y: u64) -> Circuit<Fr> {
    let mut c = Circuit::<Fr>::new();
    let y = c.public_input(Fr::from(y));
    let x = c.alloc(Fr::from(x));
    let x2 = c.mul(x, x);
    let x3 = c.mul(x2, x);
    let five = c.constant(Fr::from(5u64));
    let s = c.add(x3, x);
    let s = c.add(s, five);
    c.assert_equal(s, y);
    c
}

#[test]
fn cubic_proves_and_verifies() {
    let mut rng = test_rng();
    let srs = Srs::<Bls12_381>::setup(64, &mut rng);
    let circuit = cubic(3, 35);
    assert!(circuit.is_satisfied());
    let pk = preprocess(&circuit, &srs);
    let proof = prove(&srs, &pk, &circuit);
    assert!(verify(&pk.vk, &circuit.public_inputs(), &proof));
}

#[test]
fn wrong_public_input_rejected() {
    let mut rng = test_rng();
    let srs = Srs::<Bls12_381>::setup(64, &mut rng);
    let circuit = cubic(3, 35);
    let pk = preprocess(&circuit, &srs);
    let proof = prove(&srs, &pk, &circuit);
    assert!(!verify(&pk.vk, &[Fr::from(36u64)], &proof));
    assert!(!verify(&pk.vk, &[], &proof));
}

#[test]
#[should_panic]
fn unsatisfied_circuit_cannot_prove() {
    let mut rng = test_rng();
    let srs = Srs::<Bls12_381>::setup(64, &mut rng);
    let circuit = cubic(3, 36);
    assert!(!circuit.is_satisfied());
    let pk = preprocess(&circuit, &srs);
    let _ = prove(&srs, &pk, &circuit);
}
