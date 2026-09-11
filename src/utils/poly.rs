//! Polynomial kernels on the prover's critical path that ark-poly either
//! runs sequentially or does redundant work for.
//!
//! Everything here is a plain function over coefficient slices; the prover
//! wraps the results back into `DensePolynomial` where it needs them.

use ark_ff::{FftField, Field};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_std::{cfg_chunks, cfg_chunks_mut, cfg_iter, cfg_iter_mut};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Smallest chunk a thread is handed in the parallel scans below; below
/// this the rayon overhead dominates the field arithmetic.
const MIN_CHUNK: usize = 1 << 12;

fn chunk_size(len: usize) -> usize {
    #[cfg(feature = "parallel")]
    let threads = rayon::current_num_threads();
    #[cfg(not(feature = "parallel"))]
    let threads = 1;
    len.div_ceil(threads).max(MIN_CHUNK)
}

/// Quotient of `(p(X) - p(zeta)) / (X - zeta)`.
///
/// Synthetic division: with `p = sum_i p_i X^i` of degree `n`, the quotient
/// `q` has degree `n - 1` and satisfies `q_{n-1} = p_n`,
/// `q_i = p_{i+1} + zeta * q_{i+1}`. The constant term `p_0` never enters,
/// so the caller need not subtract `p(zeta)` first. The result is trimmed of
/// leading zeros like `DensePolynomial::from_coefficients_vec` would.
///
/// The recurrence is a linear scan, so it parallelizes as a three-pass
/// prefix computation: (1) every chunk runs the recurrence locally with a
/// zero carry-in from above, (2) a short sequential pass over the chunk
/// boundaries propagates the true carries (`q` at each chunk's top is
/// `local + zeta^len * carry`), (3) every chunk adds `zeta^{b - i} * carry`
/// to its local values. Two passes over the data instead of one, but each
/// pass is embarrassingly parallel.
pub fn divide_by_linear<F: Field>(p: &[F], zeta: F) -> Vec<F> {
    if p.len() <= 1 {
        return Vec::new();
    }
    let src = &p[1..];
    let len = src.len();
    let chunk = chunk_size(len);
    let mut q = vec![F::zero(); len];

    // (1) Local recurrence per chunk, top-down.
    cfg_chunks_mut!(q, chunk)
        .zip(cfg_chunks!(src, chunk))
        .for_each(|(qc, pc)| {
            let mut acc = F::zero();
            for (qi, pi) in qc.iter_mut().zip(pc).rev() {
                acc = *pi + zeta * acc;
                *qi = acc;
            }
        });

    // (2) Carries into each chunk, from the top chunk (carry 0) downwards.
    let num_chunks = len.div_ceil(chunk);
    let mut carries = vec![F::zero(); num_chunks];
    let mut carry = F::zero();
    for k in (0..num_chunks).rev() {
        carries[k] = carry;
        let a = k * chunk;
        let b = (a + chunk).min(len);
        carry = q[a] + zeta.pow([(b - a) as u64]) * carry;
    }

    // (3) Fix-up: q_i += zeta^{b - i} * carry for i in [a, b).
    cfg_chunks_mut!(q, chunk)
        .zip(cfg_iter!(carries))
        .for_each(|(qc, c)| {
            if c.is_zero() {
                return;
            }
            let mut factor = zeta;
            for qi in qc.iter_mut().rev() {
                *qi += factor * c;
                factor *= zeta;
            }
        });

    while q.last().is_some_and(|c| c.is_zero()) {
        q.pop();
    }
    q
}

/// `(a(X)^2 - b(X)) / v_H(X)` for `deg a, deg b < m = |H|`, returning
/// `None` if the division is not exact.
///
/// `a^2` has degree at most `2m - 2`, so it is computed with a single FFT of
/// size `2m` (evaluate `a`, square pointwise, interpolate) rather than
/// ark-poly's generic `a * a`, which transforms both operands. Division by
/// `X^m - 1` then needs no long division: with `n = a^2 - b` of degree
/// `< 2m`, the quotient is `n[m..]` and the remainder is `n[..m] + n[m..]`
/// coefficient-wise, so exactness is `n[i] + n[m + i] == 0` for all `i`.
pub fn square_minus_over_vanishing<F: FftField>(
    a: &[F],
    b: &[F],
    domain: Radix2EvaluationDomain<F>,
) -> Option<Vec<F>> {
    let m = domain.size();
    debug_assert!(a.len() <= m && b.len() <= m);
    let domain2 =
        Radix2EvaluationDomain::<F>::new(2 * m).expect("2m must be a supported FFT size when m is");

    let mut n = domain2.fft(a);
    cfg_iter_mut!(n).for_each(|e| {
        e.square_in_place();
    });
    domain2.ifft_in_place(&mut n);
    debug_assert_eq!(n.len(), 2 * m);
    cfg_iter_mut!(n[..b.len()])
        .zip(b)
        .for_each(|(n_i, b_i)| *n_i -= b_i);

    let (low, high) = n.split_at(m);
    let exact = cfg_iter!(low)
        .zip(high)
        .all(|(lo, hi)| (*lo + hi).is_zero());
    if !exact {
        return None;
    }
    let mut q = high.to_vec();
    while q.last().is_some_and(|c| c.is_zero()) {
        q.pop();
    }
    Some(q)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ff::Zero;
    use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
    use ark_std::{test_rng, UniformRand};

    #[test]
    fn linear_division_matches_long_division() {
        let rng = &mut test_rng();
        // Cover the single-chunk path, exact chunk multiples, and a ragged
        // top chunk.
        for len in [1usize, 2, 7, MIN_CHUNK, 2 * MIN_CHUNK, 3 * MIN_CHUNK + 17] {
            let p = DensePolynomial::<Fr>::rand(len - 1, rng);
            let zeta = Fr::rand(rng);
            let v = p.evaluate(&zeta);
            let expected = &(&p - &DensePolynomial::from_coefficients_vec(vec![v]))
                / &DensePolynomial::from_coefficients_vec(vec![-zeta, Fr::from(1u64)]);
            let got = DensePolynomial::from_coefficients_vec(divide_by_linear(&p.coeffs, zeta));
            assert_eq!(got, expected, "len {len}");
        }
    }

    #[test]
    fn linear_division_trims_leading_zeros() {
        let mut coeffs = vec![Fr::from(3u64), Fr::from(5u64)];
        coeffs.extend(std::iter::repeat_n(Fr::zero(), 10));
        let q = divide_by_linear(&coeffs, Fr::from(7u64));
        assert_eq!(q, vec![Fr::from(5u64)]);
    }

    #[test]
    fn square_minus_over_vanishing_matches_ark_poly() {
        let rng = &mut test_rng();
        let domain = Radix2EvaluationDomain::<Fr>::new(1 << 10).unwrap();
        let m = domain.size();
        let a = DensePolynomial::<Fr>::rand(m - 1, rng);
        // Exact case: b = a^2 mod v_H, i.e. the evaluations of a^2 on H.
        let a_sq = &a * &a;
        let (expected_q, b) = a_sq.divide_by_vanishing_poly(domain);
        let got = square_minus_over_vanishing(&a.coeffs, &b.coeffs, domain).unwrap();
        assert_eq!(DensePolynomial::from_coefficients_vec(got), expected_q);

        // Inexact case must be detected.
        let mut bad = b.coeffs.clone();
        bad[3] += Fr::from(1u64);
        assert!(square_minus_over_vanishing(&a.coeffs, &bad, domain).is_none());

        // Short operands (degree well below m) are zero-padded correctly.
        let a_short = DensePolynomial::<Fr>::rand(5, rng);
        let (expected_q, b_short) = (&a_short * &a_short).divide_by_vanishing_poly(domain);
        let got = square_minus_over_vanishing(&a_short.coeffs, &b_short.coeffs, domain).unwrap();
        assert_eq!(DensePolynomial::from_coefficients_vec(got), expected_q);
    }
}
