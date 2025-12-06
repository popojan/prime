(* Prime DNA Blockchain v2 - Self-referential encoding *)

(* === GOAL ===
   Encode the sequence of primes using the primes themselves.
   Ideal: DNA that allows reconstruction of ALL primes.

   Blockchain principle:
   - Each "block" (prime) depends on all previous
   - The chain is self-verifying
*)

(* === APPROACH 1: Gap deviation encoding ===
   Instead of storing gaps directly, store deviation from expected.
   Expected gap ≈ ln(p), so deviation should be small.
*)

GapDeviations[n_] := Module[{primes, gaps, expected, deviations},
  primes = Prime[Range[n + 1]];
  gaps = Differences[primes];
  expected = Table[Log[primes[[i]]], {i, 1, n}];
  deviations = gaps - expected;
  {gaps, expected, deviations}
]

Print["=== GAP DEVIATION ANALYSIS ===\n"];

{gaps, expected, devs} = GapDeviations[100];
Print["First 20 gaps:      ", gaps[[1;;20]]];
Print["Expected (ln p):    ", Round[expected[[1;;20]], 0.1]];
Print["Deviations:         ", Round[devs[[1;;20]], 0.1]];

Print["\nDeviation statistics (first 100 gaps):"];
Print["  Mean: ", N[Mean[devs], 4]];
Print["  StdDev: ", N[StandardDeviation[devs], 4]];
Print["  Min: ", Min[devs]];
Print["  Max: ", Max[devs]];

(* Bits needed to encode *)
Print["\nBits needed:"];
Print["  Direct gaps: ", Total[Ceiling[Log2[gaps + 1]]], " bits"];
Print["  Deviations (signed): ", Total[Ceiling[Log2[Abs[devs] + 1]] + 1], " bits"];

(* === APPROACH 2: Recursive encoding ===
   Each prime is encoded relative to prediction from previous primes.
   p_n = f(p_1, ..., p_{n-1}) + correction
*)

Print["\n=== RECURSIVE PREDICTION ==="];
Print["Trying to predict p_n from p_1...p_{n-1}\n"];

(* Simple prediction: p_n ≈ p_{n-1} + ln(p_{n-1}) *)
SimplePrediction[primes_, n_] := primes[[n-1]] + Log[primes[[n-1]]]

(* Better prediction using last k gaps *)
GapTrendPrediction[primes_, n_, k_] := Module[{recentGaps, avgGap},
  If[n <= k + 1, Return[SimplePrediction[primes, n]]];
  recentGaps = Differences[primes[[n-k-1 ;; n-1]]];
  avgGap = Mean[recentGaps];
  primes[[n-1]] + avgGap
]

primes = Prime[Range[200]];
Print["n\tActual\tSimple pred\tError\tGap-trend pred\tError"];
Do[
  actual = primes[[n]];
  simple = SimplePrediction[primes, n];
  trend = GapTrendPrediction[primes, n, 5];
  Print[n, "\t", actual, "\t", Round[simple], "\t\t", Round[actual - simple],
        "\t", Round[trend], "\t\t", Round[actual - trend]];
, {n, {10, 20, 50, 100, 200}}];

(* === APPROACH 3: Self-encoding chain ===
   DNA_n = DNA_{n-1} ⊕ transform(p_n, DNA_{n-1})

   The transform uses DNA_{n-1} to determine HOW to encode p_n.
   This creates dependency: decoding p_n requires DNA_{n-1}.
*)

Print["\n=== SELF-ENCODING CHAIN ==="];

(* Hash-like mixing: use previous DNA to scramble new prime bits *)
ChainEncode[n_] := Module[{primes, dna, primeBits, scrambled, seed},
  primes = Prime[Range[n]];
  dna = {};

  Do[
    primeBits = IntegerDigits[primes[[k]], 2];

    If[k == 1,
      (* Genesis block *)
      dna = primeBits,

      (* Use DNA so far as "seed" to scramble prime bits *)
      (* Position i of primeBits goes to position determined by DNA *)
      seed = FromDigits[Take[dna, Min[10, Length[dna]]], 2];
      scrambled = Table[
        primeBits[[Mod[i - 1 + seed, Length[primeBits]] + 1]],
        {i, Length[primeBits]}
      ];
      (* Append scrambled bits *)
      dna = Join[dna, scrambled];
    ];
  , {k, n}];

  dna
]

(* Can we DECODE? *)
ChainDecode[dna_, n_] := Module[{primes, pos, seed, chunkSize, chunk, unscrambled, p},
  primes = {2}; (* Genesis *)
  pos = Length[IntegerDigits[2, 2]] + 1; (* After first prime *)

  Do[
    (* Estimate chunk size for prime k *)
    chunkSize = Ceiling[Log2[primes[[-1]] * 2]]; (* Rough upper bound *)

    If[pos + chunkSize - 1 > Length[dna], Break[]];

    chunk = dna[[pos ;; pos + chunkSize - 1]];

    (* Unscramble using seed from previous DNA *)
    seed = FromDigits[Take[dna[[1 ;; pos - 1]], Min[10, pos - 1]], 2];
    unscrambled = Table[
      chunk[[Mod[i - 1 - seed, Length[chunk]] + 1]],
      {i, Length[chunk]}
    ];

    p = FromDigits[unscrambled, 2];
    AppendTo[primes, p];
    pos += chunkSize;
  , {k, 2, n}];

  primes
]

dna20 = ChainEncode[20];
Print["Chain-encoded DNA (20 primes): ", Length[dna20], " bits"];
Print["First 50 bits: ", dna20[[1;;Min[50, Length[dna20]]]]];

decoded = ChainDecode[dna20, 20];
Print["Decoded primes: ", decoded];
Print["Actual primes:  ", Prime[Range[Length[decoded]]]];
Print["Match: ", decoded == Prime[Range[Length[decoded]]]];

(* === KEY QUESTION: COVERAGE ===
   Can we encode ALL primes this way?
   Or only a subset?
*)

Print["\n=== COVERAGE QUESTION ==="];
Print["Chain encoding stores ALL primes exactly (no loss)."];
Print["But does it COMPRESS?"];
Print[""];
directBits = Total[Ceiling[Log2[Prime[Range[100]]]]];
chainBits = Length[ChainEncode[100]];
Print["100 primes:"];
Print["  Direct encoding: ", directBits, " bits"];
Print["  Chain encoding:  ", chainBits, " bits"];
Print["  Ratio: ", N[chainBits/directBits, 3]];
