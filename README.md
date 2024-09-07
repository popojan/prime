# prime
Probably gives some probable primes quite fast.

## Method

Program generates big (strongly probable) primes fast. It uses fragments of so-called **prime DNA**,
sequence of *half the difference between two successor primes modulo 2*, as binary digits
of a big prime candidate being tested for primality.

## Usage
```
Usage: prime [OPTIONS] [MIN_BINARY_DIGITS] [MAX_BINARY_DIGITS]

Arguments:
  [MIN_BINARY_DIGITS]  Minimum successive primes used (DNA fragment length, binary digits plus one)
  [MAX_BINARY_DIGITS]  Maximum successive primes used (DNA fragment length, binary digits plus one) [default: same as minimum]

Options:
  -f, --from <FROM>          Order of the lowest precalculated prime [default: 2]
  -t, --to <TO>              Can override order of the highest precalculated prime
  -d, --divisors <DIVISORS>  Order of the highest precalculated divisor prime [default: 1000]
      --descending           Start generating from bigger primes to smaller
      --sort-by-fragment     Sorts resulting primes by underlying DNA fragment
  -p, --power-2 <POWER_2>    Add an extra power of two [default: -1]
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
$ time  ./prime 332 333
binary_digits   decimal_digits  description     probable_prime  divisors_used
331     100     |prime|p(1995,2327,-1)  2422869083934692479697045230277340847807057386770959270917524861565955936481887645455978493444353163    []
331     100     |prime|p(2437,2769,-1)  2423932902271937113060898257795617159394161747280120403101168841435111563108985766417129571131137341    []
331     100     |prime|p(1029,1361,-1)  2494073167469322385003700286402406000652114573552907449820865579590519798760164507716055449453933911    []
331     100     |prime|p(745,1077,-1)   2978530528181116750045266614864823840782763278906623064735937422473265044636494106055714124012572263    []
331     100     |prime|p(401,733,-1)    3067100013533246378431395149339760981137291441434444879981594229036803151012815429672318387139073371    []
331     100     |prime|p(2313,2645,-1)  3690813149025004511496261256027454610201081548677468989676275627882971834082151025801763786265686457    []
331     100     |prime|p(719,1051,-1)   3719470522442927140766600197911461128050914289316146208510357135788196867165922252482558325637150319    []
331     100     |prime|p(164,496,-1)    3773266524435410325194116415957021668660217578587971638236712481085307405354511281714144149270888421    []
331     100     |prime|p(395,727,-1)    3816337085222718874829093571394022641707742333201777913354217294279537735275106255359217198871959247    []
331     100     |prime|p(1891,2223,-1)  4090408214021789856449672967695310701804888974035280999927653662909920970398831120196919178446027631    []
331     100     |prime|p(1328,1660,-1)  4235490182036489488943377160198224462485305812552696990245092228623268937040381918142417192841682537    []
332     100     |prime|p(2337,2670,-1)  4818004751212267383202297272819108662744844380180722416317489244999062987988932568495263977040861749    []
332     100     |prime|p(2772,3105,-1)  4825160646308346156108673838182661167612894900011660864305183247533356753959750771991709744973032381    []
332     100     |prime|p(1077,1410,-1)  5126529378634190470679398311200809848590449405888548626811750720905054741750781801295600064396309921    []
332     100     |prime|p(2010,2343,-1)  5817835129996389404203437687876828622506693979345012832436164307810676558232290301634534224287987351    []
332     100     |prime|p(413,746,-1)    5899277003409834707762961668918599942058654010031215580478282156404633211012529117030419646431589749    []
332     100     |prime|p(1713,2046,-1)  7067304649027675290811477371134790885078470640759341489588678513482135894770672593378006858904139091    []
332     100     |prime|p(1457,1790,-1)  7644672523312437101476400892717596967234800051230223483087448459443254478228237081968424455055794673    []
332     100     |prime|p(2630,2963,-1)  8697565033467958685721555263190985313353369197498583515014021492579617144399569432510143972676613631    []
Found 19 probable primes using 279 tests compared to 4378 expected tests. Speed-up 15.7×.

real    0m0.215s
user    0m1.617s
sys     0m0.006s
```

or e.g. with extra power of 2 added to the candidate primes to get titanic sized primes

```
$ time ./prime -p 3321 332 333
3322    1000    |prime|p(2284,2616,3321)        5255518873824416903687982113990223422500609656068207278985959860701674376140948952727868959731367711773472091268331032352076981803914759707845432510527148579017492248480427610016653843412003372271186798041175697541335432489827420263435608995587192950500013093267360192849106442263110378600880351884182032222445257200283144706505515692338227794115908612542540824186460695779484745234811992358935185750392699459427601991495454356668874186092852211813885161170963358852476989176854882069055149418495714927697767252274601940022528984667478034485958659850797126957592650317449509974542270245372291309786143923729921135636901473773573945910846621505737402572124910098843260164663698281661944877778802780126407973006501645256151418593929600952588492997056668247846037517779683839815201459112083552571094637574755369406240446203876462459153457250236443416958777437515790231249932453272479736352242246951860788214568746953392632844148464273742951094311666459138999065402004807232354170529472590364093018912197    []
3322    1000    |prime|p(389,721,3321)  5255518873824416903687982113990223422500609656068207278985959860701674376140948952727868959731367711773472091268331032352076981803914759707845432510527148579017492248480427610016653843412003372271186798041175697541335432489827420263435608995587192950500013093267360192849106442263110378600880351884182032222445257200283144706505515692338227794115908612542540824186460695779484745234811992358935185750392699459427601991495454356668874186092852211813885161170963358852476989176854882069055149418495714927697767252274601940022528984667478034485958659850797126957592650317449509974542270245372291309786143923729921135636901473773573945910846621505737402572124910098843260164663698281661944877778802780126407973006501645256151418593929600952588492997056668247846037517779683839815201459112083552571094637574755369406240446203876462459153457250236443416958777437515790231249932453272479736352242246951860788416158113321967241338896224871419428095723604007179620156170447398815160291715784427148393001104357    []
3322    1000    |prime|p(2432,2765,3321)        5255518873824416903687982113990223422500609656068207278985959860701674376140948952727868959731367711773472091268331032352076981803914759707845432510527148579017492248480427610016653843412003372271186798041175697541335432489827420263435608995587192950500013093267360192849106442263110378600880351884182032222445257200283144706505515692338227794115908612542540824186460695779484745234811992358935185750392699459427601991495454356668874186092852211813885161170963358852476989176854882069055149418495714927697767252274601940022528984667478034485958659850797126957592650317449509974542270245372291309786143923729921135636901473773573945910846621505737402572124910098843260164663698281661944877778802780126407973006501645256151418593929600952588492997056668247846037517779683839815201459112083552571094637574755369406240446203876462459153457250236443416958777437515790231249932453272479736352242246951860792341994064844876971280825620288185956960605801727816105933773839408304059723781978219421749190305723    []
Found 3 probable primes using 269 tests compared to 6909 expected tests. Speed-up 25.7×.

real    0m3.306s
user    0m23.744s
sys     0m0.015s
```

It's deterministic, you can always find the same primes later using the same command-line arguments or even faster thanks
to the descriptions given, e.g. first of the three primes above given `p(2284,2616,3321)`: 
```
./prime -f 2284 -t 2616 -p 3321
```

## A big one

```
 time ./prime -d2 -f 54356 -t 62548 -p 65536 --allow-divided    # ~ 17 minutes
```