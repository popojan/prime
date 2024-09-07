# prime

Search for big (strongly probable) twin primes

## Usage

```
Usage: prime [OPTIONS] [FROM] [TO]

Arguments:
  [FROM]  Power from
  [TO]    Power to

Options:
  -m, --max-steps <MAX_STEPS>  Maximum steps for each power [default: 3]
      --verbose                Immediately output probable primes to stdout, possibly duplicated
  -h, --help                   Print help
  -V, --version                Print version
```

## Default

Default usage without any parameters is equivalent to calling:
```
prime --max-steps 3 2 100
```

```
$ ./prime
decimal_digits  steps   third   step_diff       primality       0       power   twin_prime
1       1       false   1       true_true       0       2       5
1       1       true    0       true_true       0       2       5
2       1       false   3       true_true       0       3       11
2       1       true    1       true_true       0       3       11
2       1       false   1       true_true       0       4       17
2       -1      true    2       true_true       0       4       19
2       -1      false   1       true_true       0       5       31
2       -3      true    11      true_true       0       5       31
2       -1      false   3       true_true       0       6       61
3       3       true    16      true_true       0       6       101
3       2       false   9       true_true       0       7       137
3       2       true    9       true_true       0       7       179
3       -2      false   15      true_true       0       8       241
3       1       true    6       true_true       0       8       347
3       1       false   9       true_true       0       9       521
3       -3      true    21      true_true       0       9       661
4       1       false   7       true_true       0       10      1031
4       -2      false   19      true_true       0       11      2029
4       -3      true    17      true_true       0       11      2713
4       -1      false   3       true_true       0       12      4093
4       2       true    16      true_true       0       12      5477
4       2       false   27      true_true       0       13      8219
5       1       true    15      true_true       0       13      10937
5       -1      true    4       true_true       0       14      21841
5       1       false   1       true_true       0       16      65537
6       2       false   7       true_true       0       18      262151
7       -1      false   3       true_true       0       20      1048573
7       -2      false   19      true_true       0       21      2097133
7       1       false   9       true_true       0       23      8388617
8       1       true    40      true_true       0       24      22369661
9       2       true    65      true_true       0       29      715827947
10      1       true    21      true_true       0       31      2863311551
14      -2      false   117     true_true       0       44      17592186044299
16      1       true    8       true_true       0       52      6004799503160669
20      -1      true    12      true_true       0       66      98382635059784275273
```

