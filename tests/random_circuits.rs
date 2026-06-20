use ark_bls12_381::{Bls12_381, Fr};
use ark_ff::UniformRand;
use plonk::kzg::Commitment;
use plonk::{preprocess, prove, required_srs_degree, verify, Circuit, ProveError, Srs};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

/// A random DAG of add/mul/const gates over `inputs` allocated values, with
/// `outputs` of the results exposed as public inputs.
fn random_circuit(
    rng: &mut ChaCha20Rng,
    gates: usize,
    inputs: usize,
    outputs: usize,
) -> Circuit<Fr> {
    let mut c = Circuit::<Fr>::new();
    let mut vars: Vec<_> = (0..inputs).map(|_| c.alloc(Fr::rand(rng))).collect();
    for _ in 0..gates {
        let x = vars[rng.gen_range(0..vars.len())];
        let y = vars[rng.gen_range(0..vars.len())];
        let v = match rng.gen_range(0..5) {
            0 => c.add(x, y),
            1 => c.mul(x, y),
            2 => c.sub(x, y),
            3 => c.add_const(x, Fr::rand(rng)),
            _ => c.mul_const(x, Fr::rand(rng)),
        };
        vars.push(v);
    }
    for _ in 0..outputs {
        let v = vars[rng.gen_range(0..vars.len())];
        let out = c.public_input(c.value(v));
        c.assert_equal(v, out);
    }
    c
}

#[test]
fn random_circuits_prove_and_verify() {
    let mut rng = ChaCha20Rng::seed_from_u64(1);
    let srs = Srs::<Bls12_381>::setup(required_srs_degree(256), &mut rng);
    for i in 0..40 {
        let gates = rng.gen_range(0..200);
        let outputs = rng.gen_range(0..6);
        let c = random_circuit(&mut rng, gates, 3, outputs);
        assert!(c.is_satisfied(), "iteration {i}");
        let pk = preprocess(&c, &srs).unwrap();
        let proof = prove(&srs, &pk, &c, &mut rng).unwrap();
        let pi = c.public_inputs();
        assert!(verify(&pk.vk, &pi, &proof), "iteration {i}");
        if !pi.is_empty() {
            let mut wrong = pi.clone();
            wrong[0] += Fr::from(1u64);
            assert!(!verify(&pk.vk, &wrong, &proof), "iteration {i}");
        }
    }
}

#[test]
fn no_public_inputs() {
    let mut rng = ChaCha20Rng::seed_from_u64(2);
    let srs = Srs::<Bls12_381>::setup(required_srs_degree(64), &mut rng);
    let c = random_circuit(&mut rng, 30, 2, 0);
    let pk = preprocess(&c, &srs).unwrap();
    assert_eq!(pk.vk.num_public_inputs, 0);
    let proof = prove(&srs, &pk, &c, &mut rng).unwrap();
    assert!(verify(&pk.vk, &[], &proof));
    assert!(!verify(&pk.vk, &[Fr::from(0u64)], &proof));
}

#[test]
fn exactly_a_power_of_two_gates() {
    let mut rng = ChaCha20Rng::seed_from_u64(3);
    let srs = Srs::<Bls12_381>::setup(required_srs_degree(64), &mut rng);
    for n in [8usize, 16, 64] {
        // Circuit::new adds one gate; each public input adds a gate and an
        // assert_equal adds another.
        let mut c = Circuit::<Fr>::new();
        let x = c.alloc(Fr::from(7u64));
        let mut acc = x;
        for _ in 0..n - 3 {
            acc = c.mul(acc, x);
        }
        let out = c.public_input(c.value(acc));
        c.assert_equal(acc, out);
        assert_eq!(c.num_gates(), n);
        let pk = preprocess(&c, &srs).unwrap();
        assert_eq!(pk.vk.n, n);
        let proof = prove(&srs, &pk, &c, &mut rng).unwrap();
        assert!(verify(&pk.vk, &c.public_inputs(), &proof));
    }
}

#[test]
fn every_proof_field_matters() {
    let mut rng = ChaCha20Rng::seed_from_u64(4);
    let srs = Srs::<Bls12_381>::setup(required_srs_degree(64), &mut rng);
    let c = random_circuit(&mut rng, 40, 3, 2);
    let pk = preprocess(&c, &srs).unwrap();
    let proof = prove(&srs, &pk, &c, &mut rng).unwrap();
    let pi = c.public_inputs();
    assert!(verify(&pk.vk, &pi, &proof));

    let other = prove(&srs, &pk, &c, &mut rng).unwrap();
    let swap_point = |p: &mut Commitment<Bls12_381>| *p = Commitment((p.0 + other.a.0).into());
    let bump = |x: &mut Fr| *x += Fr::from(1u64);

    type Mutation<'a> = (&'a str, Box<dyn Fn(&mut plonk::Proof<Bls12_381>) + 'a>);
    let mutations: Vec<Mutation> = vec![
        ("a", Box::new(|p| swap_point(&mut p.a))),
        ("b", Box::new(|p| swap_point(&mut p.b))),
        ("c", Box::new(|p| swap_point(&mut p.c))),
        ("z", Box::new(|p| swap_point(&mut p.z))),
        ("t_lo", Box::new(|p| swap_point(&mut p.t_lo))),
        ("t_mid", Box::new(|p| swap_point(&mut p.t_mid))),
        ("t_hi", Box::new(|p| swap_point(&mut p.t_hi))),
        ("a(zeta)", Box::new(|p| bump(&mut p.evals.a))),
        ("b(zeta)", Box::new(|p| bump(&mut p.evals.b))),
        ("c(zeta)", Box::new(|p| bump(&mut p.evals.c))),
        ("s_sigma1(zeta)", Box::new(|p| bump(&mut p.evals.s_sigma1))),
        ("s_sigma2(zeta)", Box::new(|p| bump(&mut p.evals.s_sigma2))),
        ("z(zeta omega)", Box::new(|p| bump(&mut p.evals.z_omega))),
        ("w_zeta", Box::new(|p| p.w_zeta = other.w_zeta)),
        (
            "w_zeta_omega",
            Box::new(|p| p.w_zeta_omega = other.w_zeta_omega),
        ),
    ];
    for (name, mutate) in mutations {
        let mut p = proof.clone();
        mutate(&mut p);
        assert_ne!(p, proof, "{name} mutation was a no-op");
        assert!(!verify(&pk.vk, &pi, &p), "{name}");
    }
}

#[test]
fn proofs_are_randomised() {
    let mut rng = ChaCha20Rng::seed_from_u64(5);
    let srs = Srs::<Bls12_381>::setup(required_srs_degree(64), &mut rng);
    let c = random_circuit(&mut rng, 20, 2, 1);
    let pk = preprocess(&c, &srs).unwrap();
    let p1 = prove(&srs, &pk, &c, &mut ChaCha20Rng::seed_from_u64(10)).unwrap();
    let p2 = prove(&srs, &pk, &c, &mut ChaCha20Rng::seed_from_u64(10)).unwrap();
    let p3 = prove(&srs, &pk, &c, &mut ChaCha20Rng::seed_from_u64(11)).unwrap();
    assert_eq!(p1, p2);
    assert_ne!(p1.a, p3.a);
    assert_ne!(p1.z, p3.z);
    assert_ne!(p1.evals.a, p3.evals.a);
    assert!(verify(&pk.vk, &c.public_inputs(), &p3));
}

#[test]
fn key_mismatch_is_an_error() {
    let mut rng = ChaCha20Rng::seed_from_u64(6);
    let srs = Srs::<Bls12_381>::setup(required_srs_degree(64), &mut rng);
    let small = random_circuit(&mut rng, 4, 2, 1);
    let big = random_circuit(&mut rng, 40, 2, 1);
    let pk = preprocess(&small, &srs).unwrap();
    assert_eq!(
        prove(&srs, &pk, &big, &mut rng).err(),
        Some(ProveError::TooManyGates {
            max: 8,
            got: big.num_gates()
        })
    );
    let two_outputs = random_circuit(&mut rng, 4, 2, 2);
    assert!(matches!(
        prove(&srs, &pk, &two_outputs, &mut rng),
        Err(ProveError::PublicInputCount {
            expected: 1,
            got: 2
        })
    ));
}
