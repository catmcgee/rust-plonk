use ark_bls12_381::{Bls12_381, Fr};
use ark_std::test_rng;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use plonk::{preprocess, prove, verify, Circuit, Srs};

/// A chain of `gates` multiply-adds with one public output.
fn chain(gates: usize) -> Circuit<Fr> {
    let mut c = Circuit::<Fr>::new();
    let mut a = c.constant(Fr::from(2u64));
    let mut b = c.constant(Fr::from(3u64));
    for _ in 0..gates / 2 {
        let s = c.add(a, b);
        let p = c.mul(s, a);
        a = b;
        b = p;
    }
    let out = c.public_input(c.value(b));
    c.assert_equal(out, b);
    c
}

fn bench(c: &mut Criterion) {
    let mut rng = test_rng();
    let mut group = c.benchmark_group("plonk");
    group.sample_size(10);
    for log in [8, 10, 12] {
        let n = 1usize << log;
        let circuit = chain(n - 8);
        let srs = Srs::<Bls12_381>::setup(n + 5, &mut rng);
        let pk = preprocess(&circuit, &srs);
        assert_eq!(pk.vk.n, n);
        let pi = circuit.public_inputs();

        group.bench_with_input(BenchmarkId::new("prove", n), &n, |b, _| {
            b.iter(|| prove(&srs, &pk, &circuit, &mut rng).unwrap())
        });
        let proof = prove(&srs, &pk, &circuit, &mut rng).unwrap();
        group.bench_with_input(BenchmarkId::new("verify", n), &n, |b, _| {
            b.iter(|| assert!(verify(&pk.vk, &pi, &proof)))
        });
    }
    group.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
