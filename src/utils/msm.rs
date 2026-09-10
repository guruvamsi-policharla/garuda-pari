//! A multi-scalar multiplication that runs inside the caller's thread pool.
//!
//! `ark-ec` 0.6's `msm_unchecked` splits the input into `threads / 2` chunks
//! and processes each in a *freshly built* two-thread pool, parallel only
//! across bucket windows within a chunk. That has two costs for the prover:
//!
//! - A lone MSM at `T` threads keeps `2 * (T / 2)` inner threads busy on
//!   `~17` windows each, so with heterogeneous cores (e.g. Apple P/E) the
//!   slowest chunk sets the pace and cores idle at the end of every window
//!   round.
//! - `install` into a foreign pool makes the blocked outer worker steal
//!   other pending work, so the effective thread count is uncontrolled: a
//!   "1-thread" pool running two joined MSMs uses two threads.
//!
//! This is Pippenger with signed digits over `ark-ec`'s `Bucket`
//! coordinates (same per-addition cost as the library), parallelised over
//! `(window, chunk)` tasks on the current pool with a per-window bucket
//! merge, so all `T` threads stay busy and nothing escapes the pool. Digits
//! are stored window-major so each task streams a contiguous `i32` row.
//! Single-threaded it uses the library's window size and is the same
//! algorithm; in parallel it trades ~15% more bucket additions (smaller
//! windows, more tasks) for balance and bucket arrays that fit in L2.

use ark_ec::VariableBaseMSM;
use ark_ff::{BigInteger, PrimeField};
use ark_std::{cfg_chunks, cfg_into_iter};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Number of threads the MSM may use.
fn threads() -> usize {
    #[cfg(feature = "parallel")]
    {
        rayon::current_num_threads()
    }
    #[cfg(not(feature = "parallel"))]
    {
        1
    }
}

/// Largest window size (bits); bucket arrays are `2^(c-1)` entries.
const MAX_WINDOW: usize = 16;

/// `log2(n) * ln(2)`, as in `ark-ec`.
fn ln_without_floats(n: usize) -> usize {
    (ark_std::log2(n) * 69 / 100) as usize
}

/// Window size (bits) and number of scalar chunks for an MSM of `n` terms
/// on `threads` threads.
///
/// Single-threaded: the library's window `ln(n) + 2` and one chunk, which
/// minimises bucket additions. In parallel: two bits less (`~15%` more
/// additions; `8x` smaller bucket arrays) and enough chunks that the
/// `(window, chunk)` task count is at least `4 * threads`, keeping the pool
/// balanced across cores of unequal speed.
fn params(n: usize, threads: usize) -> (usize, usize) {
    // `log2` rounds up, so 2^21 + 1 terms would ask for 17 bits; cap at
    // the largest supported window.
    let c_serial = if n < 32 {
        3
    } else {
        (ln_without_floats(n) + 2).min(MAX_WINDOW)
    };
    if threads <= 1 || n < 1 << 10 {
        return (c_serial, 1);
    }
    let c = c_serial.saturating_sub(2).max(3);
    let windows = 256usize.div_ceil(c);
    // Chunks of at least 2^12 terms; below that the merges dominate.
    let k = (4 * threads).div_ceil(windows).clamp(1, (n >> 12).max(1));
    (c, k)
}

/// `sum_i scalars[i] * bases[i]`, truncating to the shorter slice.
pub fn msm<G: VariableBaseMSM>(bases: &[G::MulBase], scalars: &[G::ScalarField]) -> G {
    let n = bases.len().min(scalars.len());
    let (c, k) = params(n, threads());
    msm_with::<G>(&bases[..n], &scalars[..n], c, k)
}

/// [`msm`] with an explicit window size `c` (bits, `3..=MAX_WINDOW`) and chunk count
/// `k`; exposed for tuning.
pub fn msm_with<G: VariableBaseMSM>(
    bases: &[G::MulBase],
    scalars: &[G::ScalarField],
    c: usize,
    k: usize,
) -> G {
    let n = bases.len().min(scalars.len());
    if n == 0 {
        return G::zero();
    }
    assert!(
        (3..=MAX_WINDOW).contains(&c),
        "window size {c} out of range"
    );
    let bases = &bases[..n];
    let scalars = &scalars[..n];
    let num_bits = G::ScalarField::MODULUS_BIT_SIZE as usize;
    let windows = num_bits.div_ceil(c);
    let digits = window_major_digits(scalars, c, windows);

    let chunk = n.div_ceil(k.max(1)).max(1);
    let half = 1usize << (c - 1);
    let window_sums: Vec<G> = cfg_into_iter!(0..windows)
        .map(|w| {
            // Recentred digits lie in [-2^(c-1), 2^(c-1)); the top window
            // keeps its carry and lies in [0, 2^c].
            let num_buckets = if w + 1 == windows { (1 << c) + 1 } else { half };
            let buckets = accumulate::<G>(&digits[w], bases, chunk, num_buckets);
            let mut running = G::ZERO_BUCKET;
            let mut sum = G::ZERO_BUCKET;
            for b in buckets.iter().rev() {
                running += b;
                sum += &running;
            }
            sum.into()
        })
        .collect();

    // Horner over windows, high to low.
    let mut total = G::zero();
    for sum in window_sums.iter().rev() {
        for _ in 0..c {
            total.double_in_place();
        }
        total += sum;
    }
    total
}

/// Bucket accumulation for one window over `k` scalar chunks, merged.
fn accumulate<G: VariableBaseMSM>(
    digits: &[i32],
    bases: &[G::MulBase],
    chunk: usize,
    num_buckets: usize,
) -> Vec<G::Bucket> {
    let partials = cfg_chunks!(digits, chunk)
        .zip(cfg_chunks!(bases, chunk))
        .map(|(digits, bases)| {
            let mut buckets = vec![G::ZERO_BUCKET; num_buckets];
            for (&d, base) in digits.iter().zip(bases) {
                if d > 0 {
                    buckets[(d - 1) as usize] += base;
                } else if d < 0 {
                    buckets[(-d - 1) as usize] -= base;
                }
            }
            buckets
        });
    let merge = |mut acc: Vec<G::Bucket>, part: Vec<G::Bucket>| {
        for (a, p) in acc.iter_mut().zip(&part) {
            *a += p;
        }
        acc
    };
    #[cfg(feature = "parallel")]
    {
        partials.reduce_with(merge).unwrap()
    }
    #[cfg(not(feature = "parallel"))]
    {
        partials.reduce(merge).unwrap()
    }
}

/// Signed `c`-bit digits of every scalar, `digits[w][i]` for window `w`
/// and scalar `i`. Same recoding as `ark-ec`'s `make_digits`.
fn window_major_digits<F: PrimeField>(scalars: &[F], c: usize, windows: usize) -> Vec<Vec<i32>> {
    let n = scalars.len();
    let mut rows = vec![vec![0i32; n]; windows];
    // Transpose the row chunks so each piece of scalars writes its own
    // contiguous span of every row.
    let piece = n.div_ceil(threads().max(1)).max(1 << 12);
    let mut pieces: Vec<Vec<&mut [i32]>> = (0..n.div_ceil(piece))
        .map(|_| Vec::with_capacity(windows))
        .collect();
    for row in rows.iter_mut() {
        for (p, span) in row.chunks_mut(piece).enumerate() {
            pieces[p].push(span);
        }
    }
    cfg_into_iter!(pieces)
        .zip(cfg_chunks!(scalars, piece))
        .for_each(|(mut cols, scalars)| {
            for (i, s) in scalars.iter().enumerate() {
                recode(&s.into_bigint(), c, windows, |w, d| cols[w][i] = d);
            }
        });
    rows
}

/// Recentre the base-`2^c` digits of `a` to `[-2^(c-1), 2^(c-1))`, carrying
/// upward; the top window absorbs the final carry.
#[inline]
fn recode(a: &impl BigInteger, c: usize, windows: usize, mut emit: impl FnMut(usize, i32)) {
    let limbs = a.as_ref();
    let radix = 1u64 << c;
    let mask = radix - 1;
    let mut carry = 0u64;
    for w in 0..windows {
        let bit_offset = w * c;
        let (u, b) = (bit_offset / 64, bit_offset % 64);
        let bits = if b < 64 - c || u + 1 == limbs.len() {
            limbs[u] >> b
        } else {
            (limbs[u] >> b) | (limbs[u + 1] << (64 - b))
        };
        let coef = carry + (bits & mask);
        carry = (coef + radix / 2) >> c;
        let mut digit = coef as i64 - (carry << c) as i64;
        if w + 1 == windows {
            digit += (carry << c) as i64;
        }
        emit(w, digit as i32);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Fr, G1Affine, G1Projective};
    use ark_ec::{CurveGroup, PrimeGroup};
    use ark_ff::{AdditiveGroup, Field, UniformRand, Zero};
    use ark_std::rand::{rngs::StdRng, SeedableRng};

    fn inputs(n: usize, rng: &mut StdRng) -> (Vec<G1Affine>, Vec<Fr>) {
        let bases: Vec<G1Affine> = (0..n)
            .map(|_| (G1Projective::generator() * Fr::rand(rng)).into_affine())
            .collect();
        let mut scalars: Vec<Fr> = (0..n).map(|_| Fr::rand(rng)).collect();
        // Mix in the prover's small scalars: bits, zeros, and the maximum.
        for (i, s) in scalars.iter_mut().enumerate() {
            match i % 7 {
                0 => *s = Fr::ZERO,
                1 => *s = Fr::ONE,
                2 => *s = -Fr::ONE,
                _ => {}
            }
        }
        (bases, scalars)
    }

    #[test]
    fn matches_library_msm() {
        let mut rng = StdRng::seed_from_u64(3);
        for n in [1usize, 2, 31, 32, 1000, 5000, (1 << 13) + 3, (1 << 14) + 1] {
            let (bases, scalars) = inputs(n, &mut rng);
            let expected = G1Projective::msm_unchecked(&bases, &scalars);
            assert_eq!(msm::<G1Projective>(&bases, &scalars), expected, "n = {n}");
            for c in [3usize, 8, 13, 16] {
                for k in [1usize, 3, 8] {
                    assert_eq!(
                        msm_with::<G1Projective>(&bases, &scalars, c, k),
                        expected,
                        "n = {n}, c = {c}, k = {k}"
                    );
                }
            }
        }
    }

    #[test]
    fn truncates_to_shorter_slice() {
        let mut rng = StdRng::seed_from_u64(4);
        let (bases, scalars) = inputs(100, &mut rng);
        let expected = G1Projective::msm_unchecked(&bases[..60], &scalars[..60]);
        assert_eq!(msm::<G1Projective>(&bases[..60], &scalars), expected);
        assert_eq!(msm::<G1Projective>(&bases, &scalars[..60]), expected);
        assert!(msm::<G1Projective>(&bases[..0], &scalars).is_zero());
    }
}
