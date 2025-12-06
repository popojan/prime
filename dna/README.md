# Prime DNA - Compact Prime Encoding

Gap-based encoding for prime sequences. Stores `gap/2` values (all gaps after p=2 are even), achieving ~8x compression with O(n) decode time.

## Performance

| Primes | Storage | Decode | vs Sieve |
|--------|---------|--------|----------|
| 78k (to 10⁶) | 78 KB | 0.3 ms | 15x faster |
| 665k (to 10⁷) | 665 KB | 2.6 ms | 18x faster |
| 5.8M (to 10⁸) | 5.8 MB | 22 ms | 37x faster |

## Files

- `prime_dna.hpp` - C++ header-only library (universal, auto type selection)
- `prime_dna.js` - JavaScript implementation with Base64 serialization
- `exploration/` - Wolfram Language analysis scripts

## Usage

### C++
```cpp
#include "prime_dna.hpp"

std::vector<uint64_t> primes = sieve(1000000);
prime_dna::PrimeDNAUniversal dna;
dna.encode(primes);
dna.save("primes.dna");

// Later...
dna.load("primes.dna");
auto decoded = dna.decode();  // 37x faster than re-sieving!
```

### JavaScript
```javascript
const dna = new PrimeDNA();
dna.encode(primes);
const b64 = dna.toBase64();  // Embed in HTML/JSON

// Later...
new PrimeDNA().fromBase64(b64).decode();
```

## Theory

### Why gap/2?

All prime gaps (after 2→3) are even, so `gap/2` saves 1 bit per gap:
- Max gap to 10⁸: 220 → half-gap 110 → fits in uint8
- Max gap to 10¹⁸: ~1500 → half-gap ~750 → fits in uint16

### Compression Limits

From information theory, the entropy of prime gaps is ~3.9 bits/prime. Our fixed-width encoding uses 8 bits/prime (uint8), giving 2x overhead vs theoretical minimum. Variable-length encoding could approach the entropy bound.

### Why not delta encoding?

We tested second differences (delta of gaps) but they have **higher entropy** (~4.8 bits) than raw gaps. Prime gaps are not autocorrelated - each gap is essentially independent.

## Maximum Prime Gaps

The encoding type depends on maximum gap size. Known bounds:

| Bound | Result | Source |
|-------|--------|--------|
| Cramér conjecture | gap ~ O(log² p) | Heuristic (1936) |
| RH implies | gap ~ O(√p log p) | [Cramér 1936](https://en.wikipedia.org/wiki/Prime_gap) |
| Unconditional | gap < O(p^0.525) | [Baker-Harman-Pintz 2001](https://mathscinet.ams.org/mathscinet-getitem?mr=1826193) |
| Largest known | 1676 after 2.07×10¹⁹ | [Kehrig 2023](https://t5k.org/notes/gaps.html) |

### Practical Type Selection

| Prime range | Max gap | Max half-gap | Type |
|-------------|---------|--------------|------|
| < 10¹² | ~500 | ~250 | uint8 |
| < 10¹⁸ | ~1500 | ~750 | uint16 |
| > 10¹⁸ | ~5000+ | ~2500+ | uint32 |

## References

- [Prime gap - Wikipedia](https://en.wikipedia.org/wiki/Prime_gap)
- [The Gaps Between Primes](https://t5k.org/notes/gaps.html) - Comprehensive gap tables
- [Terry Tao - Large prime gaps](https://terrytao.wordpress.com/2019/08/26/large-prime-gaps-and-probabilistic-models/)
- [OEIS A001223](https://oeis.org/A001223) - Prime gap sequence
- [Cramér's conjecture](https://en.wikipedia.org/wiki/Cram%C3%A9r%27s_conjecture)
- [Baker-Harman-Pintz (2001)](https://arxiv.org/abs/math/0009129) - Gap upper bound O(p^0.525)

## Exploration

The `exploration/` folder contains Wolfram Language scripts documenting our analysis:

1. `blockchain_dna*.wl` - Self-referential encoding experiments
2. `compression_theory.wl` - Information-theoretic bounds
3. `test_prediction.wl` - Prediction strategies (all worse than raw gaps!)

**Conclusion:** Simple gap/2 encoding is near-optimal. More complex schemes (prediction, delta encoding) don't improve compression because prime gaps lack exploitable autocorrelation.
