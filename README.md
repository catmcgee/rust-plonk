# plonk

A from-scratch implementation of the PLONK proving system in Rust, mostly to understand it properly.
Uses arkworks for field/curve arithmetic and FFTs; everything else is written here.

What's here: the vanilla three-wire gate, copy constraints via the permutation
argument, KZG commitments on BLS12-381, zero-knowledge blinding, the
linearisation trick, and a Fiat-Shamir transcript. Proofs are 624 bytes.

```
cargo test
cargo run --release --example factors
cargo bench
```

Not done, and not planned unless I get curious:

- custom gates and lookups; everything has to be expressed as `q_L a + q_R b + q_O c + q_M ab + q_C`
- the SRS is generated locally, there's no loader for a real ceremony
- `Circuit` holds the witness alongside the constraints, so the verifier side
  builds a circuit it doesn't need the values for
- `verify` returns a bool, not why it failed
- no multithreading

Not audited. Don't use this for anything real.
