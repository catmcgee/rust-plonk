# plonk

A from-scratch implementation of the PLONK proving system in Rust, mostly to understand it properly.
Uses arkworks for field/curve arithmetic and FFTs; everything else is written here.

What's here: the vanilla three-wire gate, copy constraints via the permutation
argument, KZG commitments on BLS12-381, zero-knowledge blinding, the
linearisation trick, and a Fiat-Shamir transcript. Proofs are 624 bytes.
The SRS can be sampled locally for tests or read from the Ethereum KZG
ceremony's `trusted_setup.txt`, which caps circuits at 4096 gates.

```
cargo test
cargo run --release --example factors
TRUSTED_SETUP=path/to/trusted_setup.txt cargo run --release --example factors
cargo bench
```

Not done, and not planned unless I get curious:

- custom gates and lookups; everything has to be expressed as `q_L a + q_R b + q_O c + q_M ab + q_C`
- `Circuit` holds the witness alongside the constraints, so the verifier side
  builds a circuit it doesn't need the values for

Not audited. Don't use this for anything real.
