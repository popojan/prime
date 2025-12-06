# Prime DNA - Technical Review

**Date:** 2025-12-05
**Reviewer:** Claude (with Jan Popelka)

## Summary

This tool generates large probable primes using "Prime DNA" - a sequence of `(p_{n+1} - p_n)/2 mod 2` as binary digits. The README claims 15-25x speedup over random search.

## Findings

### Code Analysis

**Test counting is correct** - every `is_prime()` call is properly counted (main.rs:260-261).

**Trial division is free** - candidates eliminated by small prime divisibility (main.rs:257-259) don't count as primality tests. This is appropriate since trial division is O(small) vs O(n³ log log n) for primality.

**Expected tests formula** (main.rs:432-433):
```rust
let average_tests = (binary_digits as f64 * f64::ln(2.0)).ceil() as usize;
```
Uses `n·ln(2)` per PNT, summed across all primes found.

### Speedup Decomposition

To isolate DNA effect, compare with `-d 0` (no trial division):

| Mode | Speedup | Source |
|------|---------|--------|
| `-d 0` (DNA only) | ~2x | Testing only odd numbers (standard) |
| `-d 100` | ~10-15x | Trial division + odd-only |
| `-d 1000` | ~15-25x | More aggressive trial division |

**DNA-specific contribution: ~1.0x (none)**

### Statistical Test

Compared DNA sequence to random bits (5000 samples, 150-bit numbers):

```
DNA:    95/5000 = 1.9%
Random: 105/5000 = 2.1%
Ratio:  0.90x (DNA slightly WORSE)
p-value > 0.05
```

**Conclusion:** DNA sequence provides NO statistical advantage for primality.

### What the Tool Actually Does Well

1. **Reproducible generation** - same parameters always produce same primes
2. **Efficient implementation** - uses standard sieve optimizations effectively

### Naming Scheme Limitation

The `p(from, to, power)` notation has a hidden cost:

| Component | Size |
|-----------|------|
| `p(2284,2616,3321)` description | ~40 bits |
| Described prime | ~3322 bits |
| **Required lookup table** (primes 1..2616) | **~35,000 bits** |

The lookup table is **10x larger** than the described prime!

**When useful:**
- Amortized over many primes (shared lookup table)
- Communication where both parties have prime tables

**When not useful:**
- Single prime storage
- General prime representation

**Coverage:** Not all primes can be described this way - only those matching DNA fragments. Estimated ~0.2 DNA-primes per 100-bit window.

### Amortization Analysis

**Question:** When does shared lookup table become worthwhile?

**Notation breakdown:**
| Component | Bits | Formula |
|-----------|------|---------|
| `from` index | ~12 | ⌈log₂(2616)⌉ |
| `to` index | ~12 | ⌈log₂(2616)⌉ |
| `power` | ~12 | ⌈log₂(3321)⌉ |
| **Total notation** | **~36** | |

**Table size:** First 2616 primes require ~35,043 bits (~4.4 KB).

**Break-even analysis for N primes of b bits:**
```
Storage without table: N × b bits
Storage with table:    35043 + N × 36 bits
Break-even: N = 35043 / (b - 36)
```

| Prime size (bits) | Break-even N | Asymptotic compression |
|-------------------|--------------|------------------------|
| 100 | 548 | 2.8× |
| 500 | 76 | 14× |
| 1000 | 36 | 28× |
| 3000 | 12 | 83× |

**The 83× compression ratio is geometric, but prime density affects table efficiency.**

The raw ratio `3000 bits / 36 bits ≈ 83×` is geometric. However, prime sparsification affects the **lookup table efficiency**:

| N primes | Table bits | DNA bits | DNA/Table | Avg bits/prime |
|----------|------------|----------|-----------|----------------|
| 100 | 776 | 99 | 0.128 | 7.8 |
| 1000 | 11,731 | 999 | 0.085 | 11.7 |
| 2616 | 35,043 | 2,615 | 0.075 | 13.4 |
| 10000 | 155,749 | 9,999 | 0.064 | 15.6 |

**DNA per table bit ≈ 1/log₂(N)** — efficiency DROPS as primes get sparser.

This means: to search deeper into DNA (for larger primes), the table grows faster than the searchable window. Prime density affects how much "searchable DNA" you get per bit of table storage.

**Position-dependent notation cost:**

The notation `p(from, to, power)` has position-dependent efficiency:

| Position | Notation bits | 3000-bit compression |
|----------|---------------|---------------------|
| 10 | 28 | 107× |
| 100 | 31 | 97× |
| 1000 | 34 | 88× |
| 10000 | 40 | 75× |
| 50000 | 44 | 68× |

**The tradeoff:** Larger tables give more searchable DNA (higher probability of finding ANY prime), but primes found at larger positions have worse compression.

Asymptotic compression for table of N primes:
```
compression ≈ power / (2·log₂(N) + log₂(power))
```

This degrades as O(1/log N) — prime sparsification forces larger tables, which logarithmically erodes the notation advantage.

**Coverage with Chebyshev bias:**

DNA sequence has bias: P(1) ≈ 0.586, P(0) ≈ 0.414 (Chebyshev).

For a b-bit prime from DNA position `from` to `to`:
- Window length: `to - from = b - 1` bits
- Valid endpoints: must start and end with 1
- P(valid) = P(1)² ≈ 0.343

Expected DNA-primes per L DNA bits (for b-bit primes):
```
≈ (L - b + 1) × P(valid) × (1 / (b · ln 2))
```

For 3000-bit primes and L = 5000 DNA bits: **~0.33 DNA-primes**.

**Conclusion:** DNA naming is efficient for **large prime collections** (>12 primes at 3000 bits), but the lookup table overhead dominates for small sets.

### No "Self-Sustaining" Threshold

**Question:** Is there a table size N* after which you can find ALL subsequent primes?

**Answer: NO.** Coverage actually DECREASES as the table grows:

```
Coverage ≈ 0.343 / ln(N)
```

| N primes | Coverage of N-bit primes |
|----------|-------------------------|
| 100 | ~7.4% |
| 10,000 | ~3.7% |
| 1,000,000 | ~2.5% |

**The fundamental mismatch:**
- DNA grows **linearly**: O(N) bits for N primes
- b-bit primes grow **exponentially**: O(2^b / b)

Since prime gaps generate only 1 DNA bit each, while prime sizes grow logarithmically, the DNA sequence can never "catch up" to the exponential growth of primes. The naming scheme captures a **vanishing fraction** of all primes as N → ∞.

**Fraction of nameable primes as function of p:**

For primes near p, the fraction that can be DNA-named:
```
f(p) ≈ 0.343 / ln(p) ≈ 0.5 / log₂(p)
```

| Prime size p | Bits | Nameable fraction |
|--------------|------|-------------------|
| 10³ | 10 | 5.0% |
| 10⁶ | 20 | 2.5% |
| 10⁹ | 30 | 1.7% |
| 10¹² | 40 | 1.25% |
| 2¹⁰⁰⁰ | 1000 | 0.05% |

**Derivation:** For b-bit primes near p ≈ 2^b:
- Natural table size: N ≈ p/ln(p) primes (PNT inverse)
- DNA bits available: ~p/ln(p)
- DNA-describable count: ~0.343 × (p/ln p) / (b·ln 2)
- Total b-bit primes: ~p / (b·ln 2)
- Ratio: 0.343/ln(p)

### Branch: precomputed-diffs

Contains a valid optimization: precompute DNA sequence once instead of computing `(p-last)/2 mod 2` repeatedly.

**Benchmark:**
- main: 6.1ms
- precomputed-diffs: 2.5ms
- Speedup: **2.4x** (real, verified)

Results are identical - pure performance optimization.

**Recommendation:** Merge to main.

## Honest README Would Say

```
Generates large probable primes efficiently using:
- Standard trial division sieve
- Parallel search over many candidates
- Deterministic bit sequence derived from prime gaps

The bit sequence has no special primality properties vs random bits,
but provides reproducible, compact descriptions of found primes.
```

## Verification Commands

```bash
# Without trial division - shows true DNA effect
./prime -d 0 100 100
# Speedup: ~2x (parallel search only)

# With trial division - shows combined effect
./prime -d 100 100 100
# Speedup: ~10x (trial division + parallel)
```
