# prime
Probably gives some probable primes quite fast.

## Method

Program generates big (strongly probable) primes fast.

## Usage
```
Program to generate big (strongly probable) primes fast

Usage: prime [OPTIONS] [NESTING_LEVEL] [BASE_FROM] [BASE_TO]

Arguments:
  [NESTING_LEVEL]  Nesting level (default: 3)
  [BASE_FROM]      Nesting initial number - lower bound (default: 1)
  [BASE_TO]        Nesting initial number - upper bound (default: 100)

Options:
  -f, --from <FROM>          Order of the lowest precalculated prime [default: 2]
  -t, --to <TO>              Can override order of the highest precalculated prime
  -d, --divisors <DIVISORS>  Order of the highest precalculated divisor prime [default: 1000]
      --descending           Start generating from bigger primes to smaller
      --sort-by-fragment     Sorts resulting primes by underlying DNA fragment
  -e, --extra-tests          Perform extra tests (k-tuples, Cunningham)
      --verbose              Immediately output probable primes to stderr, possibly duplicated
      --debug                Print debug information related to each tested span to stderr
      --final-strict         Perform final strict probable primality test on deduplicated primes
      --duplicates           Do not deduplicate resulting primes
      --allow-divided        Allow testing candidates divided by small precalculated divisors
  -h, --help                 Print help
  -V, --version              Print version
```

Timing on a personal laptop:
```
$ time ./prime 7 100 200
1006    303     |prime|n(115,7) 347769611807825674539085949181139152371599461793101740952318328609297623662367571886029733443964578893627363046320741979312780192235435758012299226404996986368837766237056973225731757234493118064451550238958034157626171504377547928487562277794425815682981219426797645308398814948596444383872029779082239        []
1036    312     |prime|n(136,7) 673089671133593883160810749508062370777531596625450377940570746404512139105344100298708993405107718797343016071179101291085045240467919069697370161666838580640602044648188541870600420964439582770900101136470274420261913099122829135148554889253064426183186696582084931590825432225042776055985183982808993052182527       []
1044    315     |prime|n(142,7) 165751580032335844096748613107814594862210698253690282011340273311470763577875329707592722030370654224514777282228110383011484691668440742531878720824365024687561414942308790426142319357334621229431116529692049338277989449217228881380311212573872346050953921324901936053066833577541186548806190162228203034278230527    []
1062    320     |prime|n(156,7) 26860109325588132477177038476435818950859018856999691227546290711878234536197232062181979175115046863803302338276946035685813555061143096297361779713615178138900393073950454357065648533312239790233597876074684987707908207968074106072672262658621735355114749352290516986385354047912832558918169116396837744279678433184767       []
Found 4 probable primes using 100 tests compared to 2878 expected tests. Speed-up 28.8×.

real    0m0.115s
user    0m0.372s
sys     0m0.059s
```

It's deterministic, you can always find the same primes later using the same command-line arguments or even faster thanks
to the descriptions given, e.g. first of the three primes above given `n(115,7)`: 
```
$ time ./prime 7 115 116
1006    303     |prime|n(115,7) 347769611807825674539085949181139152371599461793101740952318328609297623662367571886029733443964578893627363046320741979312780192235435758012299226404996986368837766237056973225731757234493118064451550238958034157626171504377547928487562277794425815682981219426797645308398814948596444383872029779082239        []
Found 1 probable primes using 1 tests compared to 698 expected tests. Speed-up 698.0×.

real    0m0.049s
user    0m0.022s
sys     0m0.036s
```