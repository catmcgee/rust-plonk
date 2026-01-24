use ark_bls12_381::{Bls12_381, Fr};
use ark_std::test_rng;
use plonk::{preprocess, prove, verify, Circuit, ProveError, Srs};

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
    let proof = prove(&srs, &pk, &circuit, &mut rng).unwrap();
    assert!(verify(&pk.vk, &circuit.public_inputs(), &proof));
}

#[test]
fn wrong_public_input_rejected() {
    let mut rng = test_rng();
    let srs = Srs::<Bls12_381>::setup(64, &mut rng);
    let circuit = cubic(3, 35);
    let pk = preprocess(&circuit, &srs);
    let proof = prove(&srs, &pk, &circuit, &mut rng).unwrap();
    assert!(!verify(&pk.vk, &[Fr::from(36u64)], &proof));
    assert!(!verify(&pk.vk, &[], &proof));
}

#[test]
fn unsatisfied_circuit_cannot_prove() {
    let mut rng = test_rng();
    let srs = Srs::<Bls12_381>::setup(64, &mut rng);
    let circuit = cubic(3, 36);
    assert!(!circuit.is_satisfied());
    let pk = preprocess(&circuit, &srs);
    assert_eq!(prove(&srs, &pk, &circuit, &mut rng).err(), Some(ProveError::Unsatisfied));
}

#[test]
fn tampered_proof_rejected() {
    use ark_ec::AffineRepr;
    let mut rng = test_rng();
    let srs = Srs::<Bls12_381>::setup(64, &mut rng);
    let circuit = cubic(3, 35);
    let pk = preprocess(&circuit, &srs);
    let proof = prove(&srs, &pk, &circuit, &mut rng).unwrap();
    let pi = circuit.public_inputs();

    let mut p = proof.clone();
    p.evals.a += Fr::from(1u64);
    assert!(!verify(&pk.vk, &pi, &p));

    let mut p = proof.clone();
    p.evals.z_omega += Fr::from(1u64);
    assert!(!verify(&pk.vk, &pi, &p));

    let mut p = proof.clone();
    p.evals.s_sigma1 = p.evals.s_sigma2;
    assert!(!verify(&pk.vk, &pi, &p));

    let mut p = proof.clone();
    p.z = plonk::kzg::Commitment((p.z.0 + p.a.0).into());
    assert!(!verify(&pk.vk, &pi, &p));

    let mut p = proof.clone();
    p.w_zeta = plonk::kzg::Proof(p.w_zeta_omega.0);
    assert!(!verify(&pk.vk, &pi, &p));

    let mut p = proof.clone();
    p.t_hi = plonk::kzg::Commitment(<Bls12_381 as ark_ec::pairing::Pairing>::G1Affine::zero());
    assert!(!verify(&pk.vk, &pi, &p));
}

#[test]
fn proof_for_one_circuit_does_not_verify_for_another() {
    let mut rng = test_rng();
    let srs = Srs::<Bls12_381>::setup(64, &mut rng);
    let circuit = cubic(3, 35);
    let pk = preprocess(&circuit, &srs);
    let proof = prove(&srs, &pk, &circuit, &mut rng).unwrap();

    // same shape, different constant
    let mut other = Circuit::<Fr>::new();
    let y = other.public_input(Fr::from(35u64));
    let x = other.alloc(Fr::from(3u64));
    let x2 = other.mul(x, x);
    let x3 = other.mul(x2, x);
    let six = other.constant(Fr::from(6u64));
    let s = other.add(x3, x);
    let s = other.add(s, six);
    other.assert_equal(s, y);
    let other_pk = preprocess(&other, &srs);
    assert!(!verify(&other_pk.vk, &[Fr::from(35u64)], &proof));
}

/// Two circuits with the same shape but different selectors must not share
/// challenges, otherwise a proof for one could be replayed against the other.
#[test]
fn challenges_depend_on_the_circuit() {
    use plonk::transcript::Transcript;
    let mut rng = test_rng();
    let srs = Srs::<Bls12_381>::setup(64, &mut rng);
    let a = preprocess(&cubic(3, 35), &srs);
    let mut other = Circuit::<Fr>::new();
    let y = other.public_input(Fr::from(35u64));
    let x = other.alloc(Fr::from(3u64));
    let x2 = other.mul(x, x);
    let x3 = other.mul(x2, x);
    let six = other.constant(Fr::from(6u64));
    let s = other.add(x3, x);
    let s = other.add(s, six);
    other.assert_equal(s, y);
    let b = preprocess(&other, &srs);
    let pi = [Fr::from(35u64)];
    let mut ta: Transcript = a.vk.transcript(&pi);
    let mut tb: Transcript = b.vk.transcript(&pi);
    assert_ne!(ta.challenge::<Fr>(b"x"), tb.challenge::<Fr>(b"x"));
}

#[test]
fn a_few_hundred_gates() {
    let mut rng = test_rng();
    let srs = Srs::<Bls12_381>::setup(1024 + 5, &mut rng);
    // fibonacci-ish chain with a public output
    let mut c = Circuit::<Fr>::new();
    let mut a = c.constant(Fr::from(1u64));
    let mut b = c.constant(Fr::from(1u64));
    for _ in 0..300 {
        let s = c.add(a, b);
        let p = c.mul(s, a);
        a = b;
        b = p;
    }
    let out = c.public_input(c.value(b));
    c.assert_equal(out, b);
    assert!(c.is_satisfied());
    let pk = preprocess(&c, &srs);
    assert_eq!(pk.vk.n, 1024);
    let proof = prove(&srs, &pk, &c, &mut rng).unwrap();
    assert!(verify(&pk.vk, &c.public_inputs(), &proof));
    assert!(!verify(&pk.vk, &[Fr::from(1u64)], &proof));
}
