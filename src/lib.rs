//! PLONK, written to learn it.

pub mod circuit;
pub mod kzg;
pub mod permutation;
pub mod preprocess;
pub mod proof;
pub mod prover;
pub mod transcript;
pub mod verifier;

pub use circuit::{Circuit, Variable};
pub use kzg::Srs;
pub use preprocess::{preprocess, required_srs_degree, PreprocessError, ProverKey, VerifierKey};
pub use proof::Proof;
pub use prover::{prove, ProveError};
pub use verifier::verify;
