//! KZG polynomial commitments over a pairing-friendly curve.
//!
//! `Srs::setup` is a plain powers-of-tau with the secret sampled locally,
//! which is only fine for tests. `Srs::from_ceremony_text` reads the output
//! of the Ethereum KZG ceremony instead, in the text format c-kzg ships.

use ark_ec::{
    pairing::Pairing, scalar_mul::variable_base::VariableBaseMSM, AffineRepr, CurveGroup,
    PrimeGroup,
};
use ark_ff::{Field, One, UniformRand, Zero};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::RngCore;

/// Structured reference string: `[1, tau, tau^2, ..., tau^d]` in G1 and `[1, tau]` in G2.
#[derive(Clone, Debug)]
pub struct Srs<E: Pairing> {
    pub powers_of_g: Vec<E::G1Affine>,
    pub h: E::G2Affine,
    pub tau_h: E::G2Affine,
}

/// Everything the verifier needs from the SRS.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierKey<E: Pairing> {
    pub g: E::G1Affine,
    pub h: E::G2Affine,
    pub tau_h: E::G2Affine,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Commitment<E: Pairing>(pub E::G1Affine);

/// Witness `[(p(X) - p(z)) / (X - z)]_1` for an evaluation at `z`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct OpeningProof<E: Pairing>(pub E::G1Affine);

/// A claimed opening: commitment, point, value, proof.
pub struct Opening<E: Pairing> {
    pub comm: Commitment<E>,
    pub point: E::ScalarField,
    pub value: E::ScalarField,
    pub proof: OpeningProof<E>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SrsError {
    Parse(String),
    /// The powers aren't consecutive powers of the same `tau` as `tau_h`.
    Inconsistent,
}

impl std::fmt::Display for SrsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SrsError::Parse(m) => write!(f, "parse error: {m}"),
            SrsError::Inconsistent => write!(f, "srs powers are inconsistent"),
        }
    }
}

impl std::error::Error for SrsError {}

impl<E: Pairing> Srs<E> {
    /// Build from points produced elsewhere, checking they are consistent:
    /// `e(sum r_i g_i, tau h) == e(sum r_i g_{i+1}, h)` for random `r_i`
    /// says every `g_{i+1} = tau g_i`, and `h, tau_h` match.
    pub fn from_powers<R: RngCore>(
        powers_of_g: Vec<E::G1Affine>,
        h: E::G2Affine,
        tau_h: E::G2Affine,
        rng: &mut R,
    ) -> Result<Self, SrsError> {
        if powers_of_g.len() < 2 {
            return Err(SrsError::Parse("need at least two G1 powers".into()));
        }
        let rs: Vec<E::ScalarField> = (1..powers_of_g.len())
            .map(|_| E::ScalarField::rand(rng))
            .collect();
        let lo = E::G1::msm_unchecked(&powers_of_g[..rs.len()], &rs);
        let hi = E::G1::msm_unchecked(&powers_of_g[1..], &rs);
        if !E::multi_pairing([lo, -hi], [tau_h, h]).0.is_one() {
            return Err(SrsError::Inconsistent);
        }
        Ok(Srs {
            powers_of_g,
            h,
            tau_h,
        })
    }

    /// Parse the trusted setup file shipped with c-kzg-4844 (the Ethereum
    /// KZG ceremony output). Format: a line with the number of G1 points,
    /// a line with the number of G2 points, the G1 points in Lagrange form,
    /// the G2 powers, then the G1 points in monomial form, one compressed
    /// point in hex per line. Older files stop after the G2 section; then
    /// the first section is taken as monomial and the consistency check in
    /// [`Srs::from_powers`] decides whether that was right.
    pub fn from_ceremony_text<R: RngCore>(text: &str, rng: &mut R) -> Result<Self, SrsError> {
        let lines: Vec<&str> = text
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .collect();
        let count = |i: usize, what: &str| -> Result<usize, SrsError> {
            lines
                .get(i)
                .ok_or_else(|| SrsError::Parse(format!("missing {what} count")))?
                .parse::<usize>()
                .map_err(|e| SrsError::Parse(format!("bad {what} count: {e}")))
        };
        let n_g1 = count(0, "g1")?;
        let n_g2 = count(1, "g2")?;
        if n_g2 < 2 {
            return Err(SrsError::Parse("need [1]_2 and [tau]_2".into()));
        }
        let bytes = |i: usize, what: &str| -> Result<Vec<u8>, SrsError> {
            let line = lines
                .get(i)
                .ok_or_else(|| SrsError::Parse(format!("file ends inside {what}")))?;
            decode_hex(line).ok_or_else(|| SrsError::Parse(format!("bad hex in {what}")))
        };
        let g1_section = |start: usize, what: &str| {
            (start..start + n_g1)
                .map(|i| {
                    E::G1Affine::deserialize_compressed(&bytes(i, what)?[..])
                        .map_err(|e| SrsError::Parse(format!("bad g1 point: {e}")))
                })
                .collect::<Result<Vec<_>, _>>()
        };
        let lagrange = g1_section(2, "g1 lagrange")?;
        let g2 = (2 + n_g1..2 + n_g1 + n_g2)
            .map(|i| {
                E::G2Affine::deserialize_compressed(&bytes(i, "g2")?[..])
                    .map_err(|e| SrsError::Parse(format!("bad g2 point: {e}")))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let g1 = if lines.len() > 2 + n_g1 + n_g2 {
            g1_section(2 + n_g1 + n_g2, "g1 monomial")?
        } else {
            lagrange
        };
        Self::from_powers(g1, g2[0], g2[1], rng)
    }

    /// Inverse of [`Srs::from_ceremony_text`], in the short layout: the
    /// monomial G1 powers in the first section, then the two G2 points.
    pub fn to_ceremony_text(&self) -> String {
        fn line<T: CanonicalSerialize>(p: &T) -> String {
            let mut bytes = Vec::new();
            p.serialize_compressed(&mut bytes)
                .expect("writing to a Vec");
            encode_hex(&bytes) + "\n"
        }
        let mut out = format!("{}\n2\n", self.powers_of_g.len());
        for g in &self.powers_of_g {
            out += &line(g);
        }
        out += &line(&self.h);
        out += &line(&self.tau_h);
        out
    }

    /// Sample a fresh `tau` and compute powers up to `max_degree`, over the
    /// curve's standard generators so the result looks like a real ceremony's.
    pub fn setup<R: RngCore>(max_degree: usize, rng: &mut R) -> Self {
        let tau = E::ScalarField::rand(rng);
        let g = E::G1::generator();
        let h = E::G2::generator();

        let mut powers = Vec::with_capacity(max_degree + 1);
        let mut cur = E::ScalarField::one();
        for _ in 0..=max_degree {
            powers.push(cur);
            cur *= tau;
        }
        let powers_of_g: Vec<E::G1> = powers.iter().map(|p| g * p).collect();

        Srs {
            powers_of_g: E::G1::normalize_batch(&powers_of_g),
            h: h.into_affine(),
            tau_h: (h * tau).into_affine(),
        }
    }

    pub fn max_degree(&self) -> usize {
        self.powers_of_g.len() - 1
    }

    pub fn verifier_key(&self) -> VerifierKey<E> {
        VerifierKey {
            g: self.powers_of_g[0],
            h: self.h,
            tau_h: self.tau_h,
        }
    }

    pub fn commit(&self, p: &DensePolynomial<E::ScalarField>) -> Commitment<E> {
        assert!(
            p.degree() <= self.max_degree(),
            "polynomial degree {} exceeds srs degree {}",
            p.degree(),
            self.max_degree()
        );
        let c = E::G1::msm_unchecked(&self.powers_of_g[..p.coeffs.len()], &p.coeffs);
        Commitment(c.into_affine())
    }

    /// Evaluate `p` at `z` and produce the opening proof.
    pub fn open(
        &self,
        p: &DensePolynomial<E::ScalarField>,
        z: E::ScalarField,
    ) -> (E::ScalarField, OpeningProof<E>) {
        let (q, value) = divide_by_linear(p, z);
        (value, OpeningProof(self.commit(&q).0))
    }

    /// Just the proof, when the caller already knows `p(z)`.
    pub fn open_at(
        &self,
        p: &DensePolynomial<E::ScalarField>,
        z: E::ScalarField,
    ) -> OpeningProof<E> {
        self.open(p, z).1
    }

    /// Open several polynomials at the same point with one proof.
    ///
    /// The verifier supplies a random `gamma`; the polynomials are folded into
    /// `sum_i gamma^i p_i` and that is opened once. The caller is expected to
    /// know (and send) the individual `p_i(z)`.
    pub fn open_batch(
        &self,
        polys: &[&DensePolynomial<E::ScalarField>],
        z: E::ScalarField,
        gamma: E::ScalarField,
    ) -> OpeningProof<E> {
        self.open_at(&fold(polys, gamma), z)
    }
}

/// `sum_i gamma^i p_i`
pub fn fold<F: Field>(polys: &[&DensePolynomial<F>], gamma: F) -> DensePolynomial<F> {
    let mut acc = DensePolynomial::zero();
    let mut coeff = F::one();
    for p in polys {
        acc += (coeff, *p);
        coeff *= gamma;
    }
    acc
}

impl<E: Pairing> VerifierKey<E> {
    /// Check `e(C - [v]_1, [1]_2) == e(W, [tau - z]_2)`.
    pub fn verify(
        &self,
        comm: &Commitment<E>,
        z: E::ScalarField,
        value: E::ScalarField,
        proof: &OpeningProof<E>,
    ) -> bool {
        // e(C - v*G + z*W, H) * e(-W, tau*H) == 1
        let lhs = comm.0.into_group() - self.g * value + proof.0 * z;
        let rhs = -proof.0.into_group();
        E::multi_pairing([lhs, rhs], [self.h, self.tau_h])
            .0
            .is_one()
    }

    /// Counterpart of [`Srs::open_batch`]: fold commitments and values with
    /// the same `gamma` and check the single proof.
    pub fn verify_batch(
        &self,
        comms: &[Commitment<E>],
        z: E::ScalarField,
        values: &[E::ScalarField],
        gamma: E::ScalarField,
        proof: &OpeningProof<E>,
    ) -> bool {
        if comms.len() != values.len() {
            return false;
        }
        let mut folded_comm = E::G1::zero();
        let mut folded_value = E::ScalarField::zero();
        let mut coeff = E::ScalarField::one();
        for (c, v) in comms.iter().zip(values) {
            folded_comm += c.0 * coeff;
            folded_value += *v * coeff;
            coeff *= gamma;
        }
        self.verify(
            &Commitment(folded_comm.into_affine()),
            z,
            folded_value,
            proof,
        )
    }

    /// Check several openings, possibly at different points, with one pairing
    /// equation. Each `(C_i, z_i, v_i, W_i)` satisfies
    /// `e(C_i - v_i G + z_i W_i, H) = e(W_i, tau H)`; a random `u` from the
    /// verifier combines them:
    ///
    /// ```text
    /// e(sum u^i (C_i - v_i G + z_i W_i), H) = e(sum u^i W_i, tau H)
    /// ```
    pub fn verify_multi_point(&self, openings: &[Opening<E>], u: E::ScalarField) -> bool {
        let mut lhs = E::G1::zero();
        let mut ws = E::G1::zero();
        let mut coeff = E::ScalarField::one();
        for o in openings {
            lhs += (o.comm.0.into_group() - self.g * o.value + o.proof.0 * o.point) * coeff;
            ws += o.proof.0 * coeff;
            coeff *= u;
        }
        E::multi_pairing([lhs, -ws], [self.h, self.tau_h])
            .0
            .is_one()
    }
}

fn decode_hex(s: &str) -> Option<Vec<u8>> {
    let s = s.strip_prefix("0x").unwrap_or(s);
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}

fn encode_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Divide `p` by `(X - z)`. Returns `(quotient, remainder)`; the remainder is `p(z)`.
pub fn divide_by_linear<F: Field>(p: &DensePolynomial<F>, z: F) -> (DensePolynomial<F>, F) {
    if p.is_zero() {
        return (DensePolynomial::zero(), F::zero());
    }
    // Synthetic division, highest coefficient first.
    let mut q = vec![F::zero(); p.coeffs.len() - 1];
    let mut carry = F::zero();
    for (i, c) in p.coeffs.iter().enumerate().rev() {
        let v = *c + carry;
        if i == 0 {
            return (DensePolynomial::from_coefficients_vec(q), v);
        }
        q[i - 1] = v;
        carry = v * z;
    }
    unreachable!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_std::test_rng;

    #[test]
    fn linear_division() {
        let mut rng = test_rng();
        let p = DensePolynomial::<Fr>::rand(17, &mut rng);
        let z = Fr::rand(&mut rng);
        let (q, r) = divide_by_linear(&p, z);
        assert_eq!(r, p.evaluate(&z));
        let x_minus_z = DensePolynomial::from_coefficients_vec(vec![-z, Fr::one()]);
        let back = &q * &x_minus_z + DensePolynomial::from_coefficients_vec(vec![r]);
        assert_eq!(back, p);
    }

    #[test]
    fn commit_open_verify() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(32, &mut rng);
        let vk = srs.verifier_key();

        let p = DensePolynomial::<Fr>::rand(20, &mut rng);
        let c = srs.commit(&p);
        let z = Fr::rand(&mut rng);
        let (v, proof) = srs.open(&p, z);
        assert_eq!(v, p.evaluate(&z));
        assert!(vk.verify(&c, z, v, &proof));

        // wrong value
        assert!(!vk.verify(&c, z, v + Fr::one(), &proof));
        // wrong point
        assert!(!vk.verify(&c, z + Fr::one(), v, &proof));
        // wrong commitment
        let c2 = srs.commit(&DensePolynomial::rand(20, &mut rng));
        assert!(!vk.verify(&c2, z, v, &proof));
    }

    #[test]
    fn batch_open() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(32, &mut rng);
        let vk = srs.verifier_key();

        let polys: Vec<DensePolynomial<Fr>> = (0..4)
            .map(|i| DensePolynomial::rand(10 + i, &mut rng))
            .collect();
        let refs: Vec<&DensePolynomial<Fr>> = polys.iter().collect();
        let comms: Vec<_> = polys.iter().map(|p| srs.commit(p)).collect();

        let z = Fr::rand(&mut rng);
        let gamma = Fr::rand(&mut rng);
        let proof = srs.open_batch(&refs, z, gamma);
        let values: Vec<Fr> = polys.iter().map(|p| p.evaluate(&z)).collect();
        assert!(vk.verify_batch(&comms, z, &values, gamma, &proof));

        let mut bad = values.clone();
        bad[2] += Fr::one();
        assert!(!vk.verify_batch(&comms, z, &bad, gamma, &proof));
        assert!(!vk.verify_batch(&comms, z, &values, gamma + Fr::one(), &proof));
    }

    #[test]
    fn multi_point() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(32, &mut rng);
        let vk = srs.verifier_key();
        let p = DensePolynomial::<Fr>::rand(12, &mut rng);
        let q = DensePolynomial::<Fr>::rand(12, &mut rng);
        let (cp, cq) = (srs.commit(&p), srs.commit(&q));
        let (z1, z2) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
        let (vp, wp) = srs.open(&p, z1);
        let (vq, wq) = srs.open(&q, z2);
        let u = Fr::rand(&mut rng);
        let op = |comm, point, value, proof| Opening {
            comm,
            point,
            value,
            proof,
        };
        assert!(vk.verify_multi_point(&[op(cp, z1, vp, wp), op(cq, z2, vq, wq)], u));
        assert!(!vk.verify_multi_point(&[op(cp, z1, vp, wp), op(cq, z2, vq + Fr::one(), wq)], u));
        assert!(!vk.verify_multi_point(&[op(cp, z1, vp, wq), op(cq, z2, vq, wp)], u));
        assert!(!vk.verify_multi_point(&[op(cp, z2, vp, wp), op(cq, z1, vq, wq)], u));
    }

    #[test]
    fn ceremony_text_round_trip() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(20, &mut rng);
        let text = srs.to_ceremony_text();
        assert!(text.starts_with("21\n2\n"));
        let back = Srs::<Bls12_381>::from_ceremony_text(&text, &mut rng).unwrap();
        assert_eq!(back.powers_of_g, srs.powers_of_g);
        assert_eq!((back.h, back.tau_h), (srs.h, srs.tau_h));

        // a power from a different tau is caught
        let other = Srs::<Bls12_381>::setup(20, &mut rng);
        let mut powers = srs.powers_of_g.clone();
        powers[7] = other.powers_of_g[7];
        assert_eq!(
            Srs::<Bls12_381>::from_powers(powers, srs.h, srs.tau_h, &mut rng).err(),
            Some(SrsError::Inconsistent)
        );
        assert_eq!(
            Srs::<Bls12_381>::from_powers(srs.powers_of_g.clone(), srs.h, other.tau_h, &mut rng)
                .err(),
            Some(SrsError::Inconsistent)
        );

        // garbage
        assert!(matches!(
            Srs::<Bls12_381>::from_ceremony_text("2\n2\nzz\n", &mut rng),
            Err(SrsError::Parse(_))
        ));
        assert!(matches!(
            Srs::<Bls12_381>::from_ceremony_text(&text[..text.len() - 10], &mut rng),
            Err(SrsError::Parse(_))
        ));
    }

    /// Run with the real file: `TRUSTED_SETUP=path cargo test ceremony_file`
    #[test]
    fn ceremony_file() {
        let Ok(path) = std::env::var("TRUSTED_SETUP") else {
            return;
        };
        let text = std::fs::read_to_string(path).unwrap();
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::from_ceremony_text(&text, &mut rng).unwrap();
        assert_eq!(srs.max_degree(), 4095);
        let p = DensePolynomial::<Fr>::rand(4000, &mut rng);
        let c = srs.commit(&p);
        let z = Fr::rand(&mut rng);
        let (v, proof) = srs.open(&p, z);
        assert!(srs.verifier_key().verify(&c, z, v, &proof));
    }

    #[test]
    fn constant_and_zero_polys() {
        let mut rng = test_rng();
        let srs = Srs::<Bls12_381>::setup(4, &mut rng);
        let vk = srs.verifier_key();
        let z = Fr::rand(&mut rng);

        let zero = DensePolynomial::<Fr>::zero();
        let c = srs.commit(&zero);
        let (v, pi) = srs.open(&zero, z);
        assert!(v.is_zero());
        assert!(vk.verify(&c, z, v, &pi));

        let k = DensePolynomial::from_coefficients_vec(vec![Fr::from(7u64)]);
        let c = srs.commit(&k);
        let (v, pi) = srs.open(&k, z);
        assert_eq!(v, Fr::from(7u64));
        assert!(vk.verify(&c, z, v, &pi));
    }
}
