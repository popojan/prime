(* Prime DNA Blockchain v3 - Prediction + Correction encoding *)

(* === CORE IDEA ===
   If we can PREDICT p_n from p_1...p_{n-1} with small error,
   we only need to store the CORRECTION.

   This IS compression: correction bits << full prime bits
*)

Print["=== PREDICTION-BASED COMPRESSION ===\n"];

primes = Prime[Range[1000]];
gaps = Differences[primes];

(* Prediction: next prime ≈ current + average recent gap *)
PredictNext[primes_, n_, k_] := Module[{recentGaps},
  If[n <= k + 1,
    Return[primes[[n-1]] + 2]  (* Simple fallback *)
  ];
  recentGaps = Differences[primes[[n-k-1 ;; n-1]]];
  primes[[n-1]] + Round[Mean[recentGaps]]
]

(* Compute corrections *)
corrections = Table[
  Prime[n] - PredictNext[primes, n, 5],
  {n, 2, 1000}
];

Print["Correction statistics (primes 2-1000):"];
Print["  Mean: ", N[Mean[corrections], 3]];
Print["  StdDev: ", N[StandardDeviation[corrections], 3]];
Print["  Min: ", Min[corrections]];
Print["  Max: ", Max[corrections]];
Print["  Range: ", Max[corrections] - Min[corrections]];

(* Bits needed *)
correctionBits = Ceiling[Log2[Max[Abs[corrections]] + 1]] + 1; (* +1 for sign *)
Print["\nBits per correction: ", correctionBits];

directBits = Total[Ceiling[Log2[primes[[2;;]]]]];
compressedBits = Length[corrections] * correctionBits + Ceiling[Log2[primes[[1]]]];
Print["\nCompression for 1000 primes:"];
Print["  Direct encoding: ", directBits, " bits"];
Print["  Correction encoding: ", compressedBits, " bits"];
Print["  Compression ratio: ", N[directBits/compressedBits, 3], "x"];

(* === DISTRIBUTION OF CORRECTIONS ===*)
Print["\n=== CORRECTION DISTRIBUTION ==="];
Print["Value\tCount"];
corrCounts = Tally[corrections];
corrCounts = SortBy[corrCounts, First];
Do[
  If[Abs[c[[1]]] <= 20,
    Print[c[[1]], "\t", c[[2]]]
  ];
, {c, corrCounts}];

(* === ENTROPY ANALYSIS ===*)
Print["\n=== ENTROPY ANALYSIS ==="];
freqs = N[#[[2]]/Length[corrections]] & /@ corrCounts;
entropy = -Total[freqs * Log2[freqs]];
Print["Entropy of corrections: ", N[entropy, 4], " bits"];
Print["Theoretical minimum: ", N[entropy * Length[corrections], 0], " bits"];
Print["vs Direct: ", directBits, " bits"];
Print["Potential compression: ", N[directBits / (entropy * Length[corrections]), 3], "x"];

(* === WHAT IF WE USE HUFFMAN/ARITHMETIC CODING? ===*)
Print["\n=== OPTIMAL CODING ==="];
Print["With optimal (Huffman/arithmetic) coding:"];
optimalBits = Ceiling[entropy * Length[corrections]];
Print["  Bits needed: ~", optimalBits];
Print["  Compression: ", N[directBits/optimalBits, 3], "x"];

(* === THE BLOCKCHAIN ASPECT ===
   Each correction depends on the PREDICTION, which uses previous primes.
   So to decode prime N, you need primes 1..N-1.
   This IS a blockchain: each block verifies the chain.
*)

Print["\n=== BLOCKCHAIN STRUCTURE ==="];
Print["Encoding: [p1] [corr2] [corr3] ... [corrN]"];
Print[""];
Print["To decode:"];
Print["  p1 = stored directly"];
Print["  p2 = predict(p1) + corr2"];
Print["  p3 = predict(p1,p2) + corr3"];
Print["  ..."];
Print["Each prime depends on ALL previous - it's a chain!"];

(* Verify reconstruction works *)
Print["\n=== RECONSTRUCTION TEST ==="];
reconstructed = {primes[[1]]};
Do[
  pred = PredictNext[reconstructed, n, 5];
  AppendTo[reconstructed, pred + corrections[[n-1]]];
, {n, 2, 100}];

Print["First 20 reconstructed: ", reconstructed[[1;;20]]];
Print["First 20 actual:        ", primes[[1;;20]]];
Print["Perfect match: ", reconstructed == primes[[1;;100]]];

(* === FOR PRIME GENERATION ===
   Given the correction sequence, we can GENERATE primes!
   Corrections form a compact "DNA" of the prime sequence.
*)

Print["\n=== DNA FOR PRIME GENERATION ==="];
Print["The correction sequence IS the 'DNA':"];
Print["  - Compact (", N[entropy, 3], " bits/prime vs ", N[Mean[Ceiling[Log2[primes[[2;;1000]]]]], 3], " bits/prime)"];
Print["  - Deterministic (corrections are exact)"];
Print["  - Self-referential (each uses previous primes)"];
Print[""];
Print["To find if candidate C is prime:"];
Print["  1. Compute expected = predict(known primes)"];
Print["  2. Compute correction = C - expected"];
Print["  3. Check if correction matches DNA"];
Print["  4. If match → C is the next prime!"];
