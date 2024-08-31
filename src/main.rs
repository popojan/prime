extern crate core;

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use std::ops::{Add, AddAssign, Div, DivAssign, Mul, Rem, Shl, Shr, Sub};
use num_bigint::{BigUint, BigInt, ToBigUint};
use num_traits::identities::One;
use num_traits::identities::Zero;
use num_traits::Signed;
use rayon::prelude::*;

use num_prime::nt_funcs::{is_prime, primes, nth_prime};

use clap::Parser;
use num_prime::PrimalityTestConfig;

/// Program to generate big (strongly probable) primes fast. Uses fragments of prime DNA,
/// sequence of half the difference between two successor primes mod 2 as binary digits
/// of a big prime candidate being tested for primality. Somehow it works much better
/// than random or sequential search.

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Order of the lowest precalculated prime
    #[clap(short, long, value_parser, default_value_t = 2)]
    from: usize,

    /// Can override order of the highest precalculated prime
    #[clap(short, long, value_parser)]
    to: Option<usize>,

    /// Order of the highest precalculated divisor prime
    #[clap(short, long, value_parser, default_value_t = 1000)]
    divisors: usize,

    /// Start generating from bigger primes to smaller
    #[clap(long, value_parser, default_value_t = false)]
    descending: bool,

    /// Sorts resulting primes by underlying DNA fragment
    #[clap(long, value_parser, default_value_t = false)]
    sort_by_fragment: bool,

    /// Add an extra power of two
    #[clap(short, long, value_parser, default_value_t = -1)]
    power_2: i64,

    /// Perform extra tests (k-tuples, Cunningham)
    #[clap(short, long, value_parser, default_value_t = false)]
    extra_tests: bool,

    /// Immediately output probable primes to stderr, possibly duplicated
    #[clap(long, value_parser, default_value_t = false)]
    verbose: bool,

    /// Print debug information related to each tested span to stderr
    #[clap(long, value_parser, default_value_t = false)]
    debug: bool,

    /// Perform final strict probable primality test on deduplicated primes
    #[clap(long, value_parser, default_value_t = false)]
    final_strict: bool,

    /// Do not deduplicate resulting primes
    #[clap(long, value_parser, default_value_t = false)]
    duplicates: bool,

    /// Nesting level (default: 3)
    #[clap()]
    nesting_level: Option<u64>,

    /// Nesting initial number - lower bound (default: 1)
    #[clap()]
    base_from: Option<usize>,

    /// Nesting initial number - upper bound (default: 100)
    #[clap()]
    base_to: Option<usize>,

    /// Allow testing candidates divided by small precalculated divisors
    #[clap(long, value_parser, default_value_t = false)]
    allow_divided: bool,

}

fn myreduce(n:usize, ap:&BigUint, a: &[BigUint]) -> (BigUint, Vec<BigUint>) {
    let mut accum = ap.clone();
    let mut divisors = vec![];
    for p in a[0..usize::min(n+1,a.len())].iter() {
        while p.lt(&accum) && accum.clone().rem(p).is_zero() {
            accum.div_assign(p);
            divisors.push(p.clone());
        }
        if p > &accum || divisors.len() > 10 {
            break;
        }
    }
    return (accum, divisors);
}

fn cunningham_1st(exact: &BigUint) -> (usize, usize) {
    let zero= BigUint::zero();
    let one= BigUint::one();
    let two = BigUint::from(2_u64);
    let mut seq = 1;
    let mut dnext = exact.clone();
    let mut tests = 0;
    loop {
        let mut cnextnext = dnext.clone().sub(&one);
        if cnextnext.clone().rem(&two) == zero {
            cnextnext = cnextnext.div(&two);
            tests += 1;
            if is_prime(&cnextnext, None).probably() {
                seq += 1;
            } else {
                break;
            }
        } else {
            break;
        }
        dnext = cnextnext.clone();
    }
    return (tests, seq);
}

fn cunningham_2nd(exact: &BigUint) -> (usize, usize) {
    let one= BigUint::one();
    let two = BigUint::from(2_u64);
    let mut seq = 1;
    let mut dnext = exact.clone();
    let mut tests = 0;
    loop {
        let mut cnextnext = dnext.clone().add(&one);
        if cnextnext.clone().rem(&two).is_zero() {
            cnextnext = cnextnext.div(&two);
            tests += 1;
            if is_prime(&cnextnext, None).probably() {
                seq += 1;
            } else {
                break;
            }
        } else {
            break;
        }
        dnext = cnextnext.clone();
    }
    return (tests, seq);
}

fn k_tuple(exact: &BigUint) -> (usize, usize) {
    let two = BigUint::from(2_u64);
    let six = BigUint::from(6_u64);
    let eight =  BigUint::from(8_u64);
    let four = BigUint::from(4_u64);
    let twelve = BigUint::from(12_u64);
    let mut seq = 1;
    let mut tests = 0;
    tests += 1;
    if is_prime(&exact.clone().add(&two), None).probably() {
        seq += 1;
        if is_prime(&exact.clone().add(&six), None).probably() {
            seq += 1;
            if is_prime(&exact.clone().add(&eight), None).probably() {
                seq += 1;
                if is_prime(&exact.clone().sub(&four), None).probably() {
                    seq += 1;
                    if is_prime(&exact.clone().add(&twelve), None).probably() {
                        seq += 1;
                    }
                }
            }
        }
    }
    return (tests, seq);
}

fn bigprime(a: &Vec<BigUint>, i:usize,j:usize,k:i64, b: &mut Vec<(usize, String, BigUint, Vec<BigUint>)>, args: &Args, extra_tests: bool) -> usize {
    if !bigprime_dry(&a, i, j) {
        return 0;
    }
    let zero= BigUint::zero();
    let one= BigUint::one();
    let two = BigUint::from(2_u64);
    let mut last = &a[i];
    let mut accum = if k < 0 {zero.clone()} else {two.pow(k as u32)};
    let mut digit = BigUint::from(1_u64);
    for  p in &a[i+1..j] {
        let add = p.sub(last).to_biguint().unwrap().div(two.clone()).rem(two.clone());
        accum = accum.add(digit.clone().mul(add));
        digit = digit.mul(&two);
        last = p;
    }
    let mut tests = 0;
    if accum.gt(&two) {
        if  accum > zero && accum != one {
            if accum.clone().rem(&two).is_zero() {
                accum.add_assign(&one);
            }
            let (exact, divisors) = myreduce(args.divisors, &accum, &a);
            //let exact = accum;
            if args.allow_divided || divisors.is_empty() {
                tests = 1;
                if is_prime(&exact, None).probably() {
                    let mut description = vec!["prime".to_string()];

                    if extra_tests {
                        let (_tests, arity_1st) = cunningham_1st(&exact);
                        tests += _tests;
                        let (_tests, arity_2nd) = cunningham_2nd(&exact);
                        tests += _tests;
                        let (_tests, arity_k_tuple) = k_tuple(&exact);
                        tests += _tests;

                        if arity_1st > 1 {
                            description.push(format!("cunn:1st_{}", arity_1st));
                        }
                        if arity_2nd > 1 {
                            description.push(format!("cunn:2nd_{}", arity_2nd));
                        }
                        if arity_k_tuple > 1 {
                            description.push(format!("ktuple_{}", arity_k_tuple));
                        }
                    }
                    b.push((tests, description.join("|"), exact.clone(), divisors));
                    tests = 0;
                }
            }
        }
    }
    return tests;
}

fn bigprime_dry(a: &Vec<BigUint>, i:usize, j:usize) -> bool {
    let zero= BigUint::zero();
    let two = BigUint::from(2_u64);
    let mut last = &a[i];
    let mut leading = true;
    let mut first_zero = false;
    let mut trailing_zeros = 0;
    let mut _leading_zeros = 0;
    let mut first = true;
    for  p in &a[i+1..j] {
        let add = p.sub(last).to_biguint().unwrap().div(two.clone()).rem(two.clone());
        if !first {
            if add == zero {
                if leading {
                    _leading_zeros += 1;
                }
                trailing_zeros += 1;
            } else {
                trailing_zeros = 0;
                leading = false;
            }
        } else {
            first = false;
            first_zero = add == zero;
        }
        last = p;
    }
    if first_zero || trailing_zeros > 0 {
        return false;
    }
    return true;
}

fn nested_prime(aa: &Vec<BigUint>, n: &BigInt, k: usize, ret: &mut Vec<(usize, String, BigUint, Vec<BigUint>)>, args: &Args) -> usize {
    let mut a: BigInt = n.sub(&BigInt::one()).shr(1);
    let mut b: BigInt = n.add(&BigInt::one()).shr(1);
    for i in 0..k {
        let na = a.clone().mul(&b).shl(1) - a.clone().sub(&b).abs();
        let nb = (a.clone().mul(&a).add(b.clone().mul(&b)).sub(&BigInt::one())).div(a.clone().sub(&b).abs());
        a = na;
        b = nb;
    }
    let pp: BigUint = a.add(&b).to_biguint().unwrap();
    let (exact, divisors) = myreduce(args.divisors, &pp, &aa);
    //let exact = accum;

    let mut tests = 0;
    if args.allow_divided || divisors.is_empty() {
        tests = 1;
        if is_prime(&exact, None).probably() {
            let mut description = vec!["prime".to_string()];

            if args.extra_tests {
                let (_tests, arity_1st) = cunningham_1st(&exact);
                tests += _tests;
                let (_tests, arity_2nd) = cunningham_2nd(&exact);
                tests += _tests;
                let (_tests, arity_k_tuple) = k_tuple(&exact);
                tests += _tests;

                if arity_1st > 1 {
                    description.push(format!("cunn:1st_{}", arity_1st));
                }
                if arity_2nd > 1 {
                    description.push(format!("cunn:2nd_{}", arity_2nd));
                }
                if arity_k_tuple > 1 {
                    description.push(format!("ktuple_{}", arity_k_tuple));
                }
            }
            ret.push((tests, description.join("|"), exact.clone(), divisors));
            tests = 0;
        }
    }
    return tests;
}

fn main() {
    let args = Args::parse();


    let kk: u64 = args.nesting_level.unwrap_or(3_u64);
    let min_kn = args.base_from.unwrap_or(1);
    let max_kn = args.base_to.unwrap_or(100) ;
    let lo = args.from;
    let hi = args.to.unwrap_or(max_kn * 10 + lo);
    let asc = !args.descending;
    let extra_tests = args.extra_tests;

    let mut a = Vec::<BigUint>::new();
    for p in primes(nth_prime(usize::max(args.divisors, hi+1) as u64)+1_u64).iter() {
        a.push(BigUint::from(*p));
    }
    let mut indices = Vec::<(usize, usize, u64, bool)>::new();

    for kn in min_kn..max_kn  {
        indices.push((kn, kn, kk, extra_tests));
    }
    if asc {
        indices.sort_by(|b, a| (b.0, b.1 - b.0).partial_cmp(&(a.0, a.1 - a.0)).unwrap());
    } else {
        indices.sort_by(|a, b| (b.0, b.1 - b.0).partial_cmp(&(a.0, a.1 - a.0)).unwrap());
    };

    let running = Arc::new(AtomicBool::new(true));
    let r = running.clone();

    ctrlc::set_handler(move || {
        r.store(false, Ordering::SeqCst);
        eprintln!("Ctrl+C handler called!");
    }).expect("Error setting Ctrl-C handler");

    let mut probable_primes = indices.into_par_iter()
    .inspect(|(i, j, k,_extra)| {
        if args.debug {
            eprintln!("Testing span p({},{},{})... ", i, j, k);
        }
    })
        .map(|(i, j, k, extra)| {
        let mut b = vec![];
        let tests0  = if running.load(Ordering::SeqCst) {
            nested_prime(&a,
                         &BigInt::from(i).shl(1_u32).add(&BigInt::one()),
                         kk as usize,
                         &mut b,
                         &args)
        } else {
            0
        };
        if b.len() > 0 {
            let tup = b.first().unwrap();
            (i, j, k, tests0 + tup.0, tup.1.clone(), tup.2.clone(), tup.3.clone())
        } else {
            (i, j, k, tests0, "".to_string(), BigUint::zero(), Vec::<BigUint>::new())
        }
    })
    .inspect(|(i, j, k, _tests, description, p, divisors)| {
        if p > &BigUint::zero() && args.verbose {
            let binary_digits = p.to_str_radix(2).len();
            let decimal_digits = p.to_str_radix(10).len();
            eprintln!("{}\t{}\t|{}|n({},{})\t{}\t{:?}",
                     binary_digits, decimal_digits, description, i, k, p, divisors);
        } else if args.debug {
            if _tests > &0 {
                eprintln!("Nested prime p({},{},{}) is composite", i, j, k);
            }  else {
            }
        }
    })
    .collect::<Vec<(usize, usize, u64, usize, String, BigUint, Vec<BigUint>)>>();

    let mut prime_count = 0;
    let mut total_tests = 0;
    let mut expected_tests = 0;

    let mut seen = HashMap::<BigUint, bool>::new();
    for (i, j, k, tests, description, p, divisors) in probable_primes {
        if p > BigUint::zero() && (!args.final_strict
            || is_prime(&p, Some(PrimalityTestConfig::strict())).probably()) {
            //numbers_tested_total += tests;
            let binary_digits = p.to_str_radix(2).len();
            let average_tests = (binary_digits as f64 * f64::ln(2.0)).ceil() as usize;
            if !seen.contains_key(&p) || args.duplicates {
                let decimal_digits = p.to_str_radix(10).len();
                println!("{}\t{}\t|{}|n({},{})\t{}\t{:?}", binary_digits, decimal_digits, description, i, k, p, divisors);
                if !args.duplicates {
                    seen.insert(p, true);
                }
            }
            prime_count += 1;
            expected_tests += average_tests;
        }
        total_tests += tests;
    }
    eprintln!("Found {} probable primes using {} tests compared to {} expected tests. Speed-up {:.1}×.",
              prime_count, total_tests, expected_tests, (expected_tests as f64)/(total_tests as f64));
    return;
}
