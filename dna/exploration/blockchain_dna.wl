(* Prime DNA Blockchain Exploration *)
(* Each prime contributes ALL its bits, interleaved deterministically *)

(* === CORE CONCEPT ===
   Current DNA: 1 bit per gap → O(N) bits for N primes
   New DNA: all bits of each prime → O(N log p_N) bits

   Interleave rule: bit i of prime p_n goes to position (p_i mod currentLength)
   This makes encoding of p_n depend on ALL previous primes.
*)

(* Deterministic interleave: insert bits at positions determined by small primes *)
InsertAtPosition[list_, elem_, pos_] := Module[{p = Mod[pos, Length[list] + 1]},
  Insert[list, elem, p + 1]
]

(* Build DNA blockchain from first N primes *)
BuildDNABlockchain[n_] := Module[
  {primes, dna, primeBits, positions, p},

  primes = Prime[Range[n]];
  dna = {};

  Do[
    p = primes[[k]];
    primeBits = IntegerDigits[p, 2];

    (* Each bit goes to position determined by small primes *)
    Do[
      positions = If[i <= k,
        primes[[i]],  (* Use p_i for position *)
        primes[[Mod[i - 1, k] + 1]]  (* Wrap around if needed *)
      ];
      dna = InsertAtPosition[dna, primeBits[[i]], positions];
    , {i, Length[primeBits]}];
  , {k, n}];

  dna
]

(* Alternative: XOR-based mixing (preserves length, for comparison) *)
BuildDNAXOR[n_] := Module[
  {primes, dna, primeBits, padded},

  primes = Prime[Range[n]];
  dna = {};

  Do[
    primeBits = IntegerDigits[primes[[k]], 2];

    If[Length[dna] == 0,
      dna = primeBits,
      (* Pad shorter to match longer *)
      If[Length[primeBits] > Length[dna],
        dna = Join[Table[0, Length[primeBits] - Length[dna]], dna]
      ];
      If[Length[dna] > Length[primeBits],
        primeBits = Join[Table[0, Length[dna] - Length[primeBits]], primeBits]
      ];
      dna = Mod[dna + primeBits, 2]  (* XOR *)
    ];
  , {k, n}];

  dna
]

(* Original DNA (1 bit per gap) *)
BuildOriginalDNA[n_] := Module[{primes, gaps},
  primes = Prime[Range[n + 1]];
  gaps = Differences[primes];
  Mod[gaps/2, 2]
]

Print["=== PRIME DNA BLOCKCHAIN ===\n"];

(* Test small cases *)
Print["First 10 primes blockchain:"];
dna10 = BuildDNABlockchain[10];
Print["  Length: ", Length[dna10], " bits"];
Print["  DNA: ", dna10];
Print["  1s: ", Count[dna10, 1], " (", N[100 Count[dna10, 1]/Length[dna10], 3], "%)"];

Print["\nOriginal DNA (10 gaps):"];
orig10 = BuildOriginalDNA[10];
Print["  Length: ", Length[orig10], " bits"];
Print["  DNA: ", orig10];

Print["\n=== GROWTH COMPARISON ==="];
Print["N\tOriginal\tBlockchain\tRatio"];
Do[
  orig = BuildOriginalDNA[n];
  block = BuildDNABlockchain[n];
  Print[n, "\t", Length[orig], "\t\t", Length[block], "\t\t",
    N[Length[block]/Length[orig], 3]];
, {n, {10, 50, 100, 200, 500}}];

Print["\n=== COVERAGE ANALYSIS ==="];
Print["For N-th prime p_N, what fraction of p_N's bits are 'covered' by DNA?"];
Print["N\tp_N\tlog2(p_N)\tDNA bits\tCoverage"];
Do[
  pN = Prime[n];
  bitsPN = Ceiling[Log2[pN]];
  block = BuildDNABlockchain[n];
  coverage = N[Length[block] / bitsPN, 3];
  Print[n, "\t", pN, "\t", bitsPN, "\t\t", Length[block], "\t\t", coverage];
, {n, {10, 50, 100, 200}}];

Print["\n=== BIT DISTRIBUTION ==="];
block100 = BuildDNABlockchain[100];
ones = Count[block100, 1];
zeros = Count[block100, 0];
Print["Blockchain (100 primes): ", ones, " ones (", N[100 ones/Length[block100], 3], "%)"];
Print["                         ", zeros, " zeros (", N[100 zeros/Length[block100], 3], "%)"];

orig100 = BuildOriginalDNA[100];
ones = Count[orig100, 1];
zeros = Count[orig100, 0];
Print["Original (100 gaps):     ", ones, " ones (", N[100 ones/Length[orig100], 3], "%)"];
Print["                         ", zeros, " zeros (", N[100 zeros/Length[orig100], 3], "%)"];
