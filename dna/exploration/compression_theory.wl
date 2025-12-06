(* Compression Theory Analysis for Prime Sequences *)

Print["=== INFORMATION-THEORETIC BOUNDS ===\n"];

(* First N primes *)
n = 10000;
primes = Prime[Range[n]];
pMax = primes[[-1]]; (* largest prime *)

Print["Analyzing first ", n, " primes (up to ", pMax, ")"];

(* === NAIVE BOUND ===*)
Print["\n=== 1. NAIVE: Store each prime directly ==="];
directBits = Total[Ceiling[Log2[primes]]];
Print["Bits: ", directBits];
Print["Bits/prime: ", N[directBits/n, 4]];

(* === GAP ENCODING ===*)
Print["\n=== 2. GAP ENCODING: Store p1 + gaps ==="];
gaps = Differences[primes];
gapBits = Ceiling[Log2[primes[[1]]]] + Total[Ceiling[Log2[gaps + 1]]];
Print["Bits: ", gapBits];
Print["Bits/prime: ", N[gapBits/n, 4]];
Print["Compression vs naive: ", N[directBits/gapBits, 3], "x"];

(* === ENTROPY OF GAPS ===*)
Print["\n=== 3. ENTROPY BOUND ==="];
gapCounts = Counts[gaps];
gapProbs = N[Values[gapCounts]/Length[gaps]];
gapEntropy = -Total[gapProbs * Log2[gapProbs]];
entropyBits = Ceiling[gapEntropy * n] + Ceiling[Log2[primes[[1]]]];
Print["Gap entropy: ", N[gapEntropy, 4], " bits/gap"];
Print["Theoretical minimum: ", entropyBits, " bits"];
Print["Compression vs naive: ", N[directBits/entropyBits, 3], "x"];

(* === WHAT'S THE ACTUAL LIMIT? ===*)
Print["\n=== 4. FUNDAMENTAL LIMIT ==="];
Print["The primes up to ", pMax, " can be described by:"];
Print["  - A bitmask of length ", pMax, " (but only ", n, " ones)"];
Print["  - Entropy of this: C(", pMax, ", ", n, ") ≈ ", N[n * Log2[pMax/n], 0], " bits"];

(* Binomial entropy *)
p = N[n/pMax]; (* density of primes *)
binaryEntropy = If[p > 0 && p < 1, -p*Log2[p] - (1-p)*Log2[1-p], 0];
maskEntropy = pMax * binaryEntropy;
Print["  - Binary entropy per position: ", N[binaryEntropy, 4], " bits"];
Print["  - Total mask entropy: ~", Round[maskEntropy], " bits"];

(* === THE KEY INSIGHT ===*)
Print["\n=== KEY INSIGHT ==="];
Print["We CANNOT beat: log2(C(n, π(n))) ≈ π(n) × log2(n/π(n))"];
Print["For n = ", pMax, ", π(n) = ", n];
Print[""];
Print["Limit: ~", N[n * Log2[pMax/n], 0], " bits = ",
  N[Log2[pMax/n], 3], " bits/prime"];
Print[""];
Print["Our gap encoding: ", N[gapBits/n, 3], " bits/prime"];
Print["Entropy encoding: ", N[entropyBits/n, 3], " bits/prime"];
Print[""];
Print["Gap between achieved and limit: ",
  N[(entropyBits - n * Log2[pMax/n])/(n * Log2[pMax/n]) * 100, 2], "%"];

(* === PRIME NUMBER THEOREM VIEW ===*)
Print["\n=== PNT PERSPECTIVE ==="];
Print["π(x) ≈ x/ln(x)"];
Print["So average prime ≈ p × ln(p) / p = ln(p)"];
Print["This means gaps scale as O(ln p)"];
Print[""];
Print["For primes near ", pMax, ":"];
Print["  Expected gap: ", N[Log[pMax], 3]];
Print["  Actual mean gap: ", N[Mean[gaps], 3]];
Print["  Bits per gap: ", N[Log2[Mean[gaps]], 3]];

(* === PRACTICAL QUESTION ===*)
Print["\n=== PRACTICAL QUESTION ==="];
Print["What are we REALLY trying to do?"];
Print[""];
Print["1. COMPRESS primes? → We can do ~3-4x better than naive"];
Print["2. GENERATE primes? → Different question!"];
Print[""];
Print["For GENERATION, the question is:"];
Print["  Given DNA, how quickly can we find the next prime?"];
Print["  DNA doesn't need to compress - it needs to PREDICT."];
