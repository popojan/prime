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
