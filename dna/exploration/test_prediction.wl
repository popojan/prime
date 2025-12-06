(* Test different prediction strategies *)

Print["=== PREDICTION STRATEGIES ===\n"];

primes = Prime[Range[100000]];
gaps = Differences[primes];

(* Strategy 1: ln(p) *)
pred1 = Table[Round[Log[primes[[i]]]], {i, 1, Length[gaps]}];
off1 = gaps - pred1;

(* Strategy 2: Previous gap *)
pred2 = Prepend[Most[gaps], 1];
off2 = gaps - pred2;

(* Strategy 3: Average of last 3 gaps *)
pred3 = Table[
  If[i <= 3, Round[Mean[gaps[[1;;i]]]], Round[Mean[gaps[[i-3;;i-1]]]]],
  {i, 1, Length[gaps]}
];
off3 = gaps - pred3;

(* Strategy 4: Median of last 5 gaps *)
pred4 = Table[
  If[i <= 5, Round[Median[gaps[[1;;i]]]], Round[Median[gaps[[i-5;;i-1]]]]],
  {i, 1, Length[gaps]}
];
off4 = gaps - pred4;

(* Compare *)
Print["Strategy\t\tMin\tMax\tRange\tBits/offset"];
Do[
  {name, offs} = strat;
  bits = Total[If[# == 0, 1, Ceiling[Log2[Abs[#] + 1]] + 1] & /@ offs];
  Print[name, "\t", Min[offs], "\t", Max[offs], "\t", Max[offs]-Min[offs],
    "\t", N[bits/Length[offs], 3]];
, {strat, {
  {"ln(p)", off1},
  {"prev gap", off2},
  {"avg(3)", off3},
  {"med(5)", off4}
}}];

(* Raw gaps baseline *)
gapBits = Total[Ceiling[Log2[gaps + 1]]];
Print["\nRaw gaps:\t1\t", Max[gaps], "\t", Max[gaps]-1, "\t", N[gapBits/Length[gaps], 3]];

(* Best strategy? *)
Print["\n=== HISTOGRAM: avg(3) offsets ==="];
counts = Counts[off3];
Print["Offset\tCount"];
Do[
  If[KeyExistsQ[counts, i] && counts[i] > Length[gaps]/100,
    Print[i, "\t", counts[i]]
  ];
, {i, -30, 30}];

(* Entropy *)
Print["\n=== ENTROPY ==="];
entropy3 = -Total[(#/Length[off3]) * Log2[#/Length[off3]] & /@ Values[Counts[off3]]];
entropyGap = -Total[(#/Length[gaps]) * Log2[#/Length[gaps]] & /@ Values[Counts[gaps]]];
Print["avg(3) offset entropy: ", N[entropy3, 4], " bits"];
Print["Raw gap entropy:       ", N[entropyGap, 4], " bits"];
Print["Savings: ", N[100*(1 - entropy3/entropyGap), 2], "%"];
