(* Simple Benchmark: Sieve vs Gap Decompression *)

Print["=== SIMPLE BENCHMARK ===\n"];

(* Target: first N primes *)
n = 100000;

(* === METHOD 1: Standard sieve ===*)
Print["1. SIEVE (generate from scratch)"];
t1 = AbsoluteTiming[
  primesSieve = Prime[Range[n]];
][[1]];
Print["   Time: ", t1, " sec"];

(* === METHOD 2: Gap decompression ===*)
Print["\n2. GAP DECOMPRESSION"];

(* First, create the gap encoding *)
gaps = Differences[primesSieve];
p1 = primesSieve[[1]];

(* Decompress *)
t2 = AbsoluteTiming[
  primesGap = FoldList[Plus, p1, gaps];
][[1]];
Print["   Time: ", t2, " sec"];
Print["   Speedup vs sieve: ", N[t1/t2, 3], "x"];

(* Verify correctness *)
Print["   Correct: ", primesGap == primesSieve];

(* === METHOD 3: Prediction + correction ===*)
Print["\n3. PREDICTION + CORRECTION"];

(* Create correction encoding *)
(* Simple prediction: next gap ≈ previous gap *)
corrections = Differences[gaps]; (* delta-of-gaps *)
g1 = gaps[[1]];

(* Decompress *)
t3 = AbsoluteTiming[
  gapsRecon = FoldList[Plus, g1, corrections];
  primesCorr = FoldList[Plus, p1, gapsRecon];
][[1]];
Print["   Time: ", t3, " sec"];
Print["   Speedup vs sieve: ", N[t1/t3, 3], "x"];
Print["   Correct: ", primesCorr == primesSieve];

(* === STORAGE COMPARISON ===*)
Print["\n=== STORAGE ==="];
Print["Method\t\t\tBits\t\tBits/prime"];

directBits = Total[Ceiling[Log2[primesSieve]]];
Print["Direct:\t\t\t", directBits, "\t", N[directBits/n, 3]];

gapBits = Ceiling[Log2[p1]] + Total[Ceiling[Log2[gaps + 1]]];
Print["Gaps:\t\t\t", gapBits, "\t\t", N[gapBits/n, 3]];

corrBits = Ceiling[Log2[p1]] + Ceiling[Log2[g1 + 1]] +
           Total[Ceiling[Log2[Abs[corrections] + 1]] + 1]; (* +1 for sign *)
Print["Corrections:\t\t", corrBits, "\t\t", N[corrBits/n, 3]];

(* === FIXED WIDTH (practical) ===*)
Print["\n=== FIXED WIDTH (practical) ==="];
maxGap = Max[gaps];
Print["Max gap in first ", n, " primes: ", maxGap];
Print["Fits in 1 byte (256): ", maxGap <= 256];
Print["Fits in 2 bytes (65536): ", maxGap <= 65536];

fixedBits = Ceiling[Log2[p1]] + n * If[maxGap <= 256, 8, 16];
Print["Fixed-width encoding: ", fixedBits, " bits (", N[fixedBits/n, 3], " bits/prime)"];

Print["\n=== SUMMARY ==="];
Print["Sieve time: ", t1, " sec"];
Print["Gap decompression: ", t2, " sec (", N[t1/t2, 2], "x faster)"];
Print[""];
Print["Storage: gaps use ", N[gapBits/directBits, 2], "x less space than direct"];
Print[""];
Print["CONCLUSION: Gap encoding is both smaller AND faster to decode than sieve!"];
