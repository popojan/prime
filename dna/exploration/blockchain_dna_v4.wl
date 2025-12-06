(* Prime DNA Blockchain v4 - Non-sequential "graph" structure *)

(* === IDEA ===
   Primes don't have to be encoded in order!
   Some primes might be better predicted from non-adjacent primes.
   Structure: directed graph where each prime points to its "predictors"
*)

Print["=== NON-SEQUENTIAL PRIME GRAPH ===\n"];

primes = Prime[Range[500]];
n = Length[primes];

(* For each prime, find which OTHER prime predicts it best *)
(* Prediction: p_target ≈ k * p_source for some small k *)

Print["=== RATIO-BASED PREDICTION ==="];
Print["Looking for primes where p_j / p_i ≈ small integer..."];

(* Find near-integer ratios *)
nearIntegerRatios = {};
Do[
  Do[
    ratio = primes[[j]] / primes[[i]];
    nearestInt = Round[ratio];
    error = Abs[ratio - nearestInt];
    If[nearestInt >= 2 && error < 0.01,
      AppendTo[nearIntegerRatios, {i, j, nearestInt, error, primes[[i]], primes[[j]]}]
    ];
  , {j, i + 1, Min[i + 100, n]}];
, {i, 1, n - 1}];

Print["Found ", Length[nearIntegerRatios], " near-integer ratios"];
Print["\nBest examples (error < 0.005):"];
best = Select[nearIntegerRatios, #[[4]] < 0.005 &];
Print["p_i\tp_j\tratio\terror"];
Do[
  Print[r[[5]], "\t", r[[6]], "\t", r[[3]], "\t", N[r[[4]], 4]];
, {r, Take[SortBy[best, #[[4]]&], 20]}];

(* === TWIN PRIMES as natural links ===*)
Print["\n=== TWIN PRIMES ==="];
twins = Select[Range[n - 1], primes[[# + 1]] - primes[[#]] == 2 &];
Print["Twin prime pairs in first 500 primes: ", Length[twins]];
Print["Examples: ", Take[Table[{primes[[i]], primes[[i+1]]}, {i, twins}], 10]];

(* === PRIME CHAINS ===
   Some primes form chains: p, 2p+1, 2(2p+1)+1, ...
   These are Cunningham chains!
*)

Print["\n=== CUNNINGHAM CHAINS ==="];
Print["Chains where p_{i+1} = 2*p_i + 1 (Sophie Germain)"];

cunningham = {};
Do[
  If[MemberQ[primes, 2*primes[[i]] + 1],
    j = Position[primes, 2*primes[[i]] + 1][[1, 1]];
    AppendTo[cunningham, {i, j, primes[[i]], primes[[j]]}]
  ];
, {i, 1, n - 1}];

Print["Found ", Length[cunningham], " Sophie Germain links"];
Print["Examples: ", Take[cunningham, 10]];

(* === BUILD THE GRAPH ===*)
Print["\n=== PRIME DEPENDENCY GRAPH ==="];
Print["Each prime can be encoded via:"];
Print["  1. Sequential (correction from previous)"];
Print["  2. Ratio link (p_j = k * p_i, store k and correction)"];
Print["  3. Sophie Germain link (p_j = 2*p_i + 1 + correction)"];

(* Cost function: bits needed to encode each link type *)
SequentialCost[i_] := Module[{pred, corr},
  If[i == 1, Return[Ceiling[Log2[primes[[1]]]]]]; (* Genesis *)
  pred = primes[[i-1]] + Round[Mean[Differences[primes[[Max[1,i-6];;i-1]]]]];
  corr = primes[[i]] - pred;
  Ceiling[Log2[Abs[corr] + 1]] + 1 (* correction + sign *)
]

RatioCost[i_, j_, k_] := Module[{pred, corr},
  pred = k * primes[[i]];
  corr = primes[[j]] - pred;
  Ceiling[Log2[k]] + Ceiling[Log2[Abs[corr] + 1]] + 1 (* ratio + correction + sign *)
]

SGCost[i_, j_] := Module[{pred, corr},
  pred = 2 * primes[[i]] + 1;
  corr = primes[[j]] - pred;
  Ceiling[Log2[Abs[corr] + 1]] + 1 (* just correction + sign, SG link is implicit *)
]

Print["\n=== COST COMPARISON (first 50 primes) ==="];
Print["Prime\tSeq cost\tBest alt\tSavings"];
totalSeq = 0;
totalBest = 0;
Do[
  seqCost = SequentialCost[i];
  totalSeq += seqCost;

  (* Check for ratio links *)
  bestAlt = seqCost;
  bestType = "seq";

  Do[
    If[j < i,
      ratio = primes[[i]] / primes[[j]];
      k = Round[ratio];
      If[k >= 2 && k <= 8,
        cost = RatioCost[j, i, k];
        If[cost < bestAlt, bestAlt = cost; bestType = "ratio " <> ToString[k] <> "×p" <> ToString[j]];
      ];
      (* Sophie Germain check *)
      If[2*primes[[j]] + 1 == primes[[i]] || Abs[2*primes[[j]] + 1 - primes[[i]]] <= 4,
        cost = SGCost[j, i];
        If[cost < bestAlt, bestAlt = cost; bestType = "SG(" <> ToString[primes[[j]]] <> ")"];
      ];
    ];
  , {j, 1, i - 1}];

  totalBest += bestAlt;

  If[i <= 20 || bestAlt < seqCost,
    Print[primes[[i]], "\t", seqCost, "\t\t", bestType, " (", bestAlt, ")\t",
      If[bestAlt < seqCost, seqCost - bestAlt, "-"]];
  ];
, {i, 1, 50}];

Print["\nTotal (50 primes):"];
Print["  Sequential: ", totalSeq, " bits"];
Print["  Optimal graph: ", totalBest, " bits"];
Print["  Improvement: ", N[(totalSeq - totalBest)/totalSeq * 100, 3], "%"];

(* === THE KEY INSIGHT ===*)
Print["\n=== KEY INSIGHT ==="];
Print["The 'DNA' doesn't have to be linear!"];
Print["It can be a GRAPH where primes reference optimal predecessors."];
Print[""];
Print["Structure:"];
Print["  [p1] [link_type_2, ref_2, corr_2] [link_type_3, ref_3, corr_3] ..."];
Print[""];
Print["Link types: sequential(1 bit), ratio(+log k bits), SG(1 bit), etc."];
Print["This is a generalized 'blockchain' - a DAG of primes!"];
