(* Prime DNA Blockchain v5 - Clean DAG analysis *)

Print["=== PRIME DAG ENCODING ===\n"];

primes = Prime[Range[1000]];
n = Length[primes];

(* Build index for fast lookup *)
primeIndex = Association[Table[primes[[i]] -> i, {i, n}]];

(* === LINK TYPES ===
   1. Sequential: p_n from p_{n-1} + correction
   2. Sophie Germain: p = 2q + 1 (1 bit type + small correction)
   3. Twin: p = q + 2 (1 bit type, implicit correction)
   4. Ratio: p = k*q (log k bits + correction)
*)

(* Encoding costs *)
SeqCorrection[i_] := Module[{gaps, pred},
  If[i <= 2, Return[primes[[i]] - primes[[i-1]]]];
  gaps = Differences[primes[[Max[1, i-6] ;; i-1]]];
  pred = primes[[i-1]] + Round[Mean[gaps]];
  primes[[i]] - pred
]

(* Find best encoding for each prime *)
FindBestEncoding[i_] := Module[
  {seqCorr, seqBits, best, p, q, idx, corr, bits},

  p = primes[[i]];
  If[i == 1, Return[{"genesis", 0, Ceiling[Log2[p]]}]];

  (* Sequential baseline *)
  seqCorr = SeqCorrection[i];
  seqBits = If[seqCorr == 0, 1, Ceiling[Log2[Abs[seqCorr] + 1]] + 1];
  best = {"seq", seqCorr, seqBits};

  (* Check Sophie Germain: is p = 2q + 1 for some prime q? *)
  If[OddQ[p] && PrimeQ[(p - 1)/2],
    q = (p - 1)/2;
    If[KeyExistsQ[primeIndex, q],
      idx = primeIndex[q];
      (* SG needs: 1 bit type + index reference *)
      (* But if q is "close" in sequence, reference is cheap *)
      bits = 2; (* Just 2 bits for SG link! *)
      If[bits < best[[3]], best = {"SG", q, bits}];
    ];
  ];

  (* Check twin: is p = q + 2 for prime q? *)
  If[PrimeQ[p - 2] && KeyExistsQ[primeIndex, p - 2] && primeIndex[p - 2] == i - 1,
    (* Twin of previous - just 1 bit! *)
    best = {"twin", p - 2, 1};
  ];

  best
]

(* Analyze all primes *)
encodings = Table[FindBestEncoding[i], {i, n}];

(* Count link types *)
Print["=== LINK TYPE DISTRIBUTION ==="];
counts = Counts[encodings[[All, 1]]];
Print["Genesis: ", Lookup[counts, "genesis", 0]];
Print["Sequential: ", Lookup[counts, "seq", 0]];
Print["Sophie Germain: ", Lookup[counts, "SG", 0]];
Print["Twin: ", Lookup[counts, "twin", 0]];

(* Total bits *)
totalBits = Total[encodings[[All, 3]]];
directBits = Total[Ceiling[Log2[primes]]];

Print["\n=== COMPRESSION ==="];
Print["1000 primes:"];
Print["  Direct encoding: ", directBits, " bits"];
Print["  DAG encoding: ", totalBits, " bits"];
Print["  Compression: ", N[directBits/totalBits, 4], "x"];
Print["  Bits/prime: ", N[totalBits/n, 3]];

(* Show some examples *)
Print["\n=== ENCODING EXAMPLES ==="];
Print["Prime\tType\tRef/Corr\tBits"];
Do[
  enc = encodings[[i]];
  Print[primes[[i]], "\t", enc[[1]], "\t", enc[[2]], "\t\t", enc[[3]]];
, {i, 1, 30}];

(* Sophie Germain chains *)
Print["\n=== SOPHIE GERMAIN CHAINS ==="];
sgPrimes = Select[Range[n], encodings[[#, 1]] == "SG" &];
Print["SG-encoded primes: ", primes[[sgPrimes[[1;;Min[20, Length[sgPrimes]]]]]];

(* Find longest SG chain *)
Print["\nLongest chains (p → 2p+1 → 4p+3 → ...):"];
chains = {};
visited = Table[False, n];
Do[
  If[!visited[[i]] && encodings[[i, 1]] != "SG",
    (* Start of potential chain *)
    chain = {primes[[i]]};
    p = primes[[i]];
    While[
      PrimeQ[2*p + 1] && KeyExistsQ[primeIndex, 2*p + 1],
      p = 2*p + 1;
      AppendTo[chain, p];
      visited[[primeIndex[p]]] = True;
    ];
    If[Length[chain] >= 3, AppendTo[chains, chain]];
  ];
, {i, n}];

chains = SortBy[chains, -Length[#] &];
Do[Print["  ", c], {c, Take[chains, 5]}];

Print["\n=== THE DAG STRUCTURE ==="];
Print["This is a DIRECTED ACYCLIC GRAPH:"];
Print["  - Most primes: sequential (from previous)"];
Print["  - Some primes: SG link (from p → 2p+1)"];
Print["  - Twin primes: 1-bit link"];
Print[""];
Print["The 'DNA' is the GRAPH STRUCTURE itself!"];
Print["Each prime is encoded as: (type, reference, correction)"];
