extern crate core;

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use std::ops::{Add, AddAssign, Div, DivAssign, Mul, Rem, Sub};
use std::time::{SystemTime, UNIX_EPOCH};
use num_bigint::{BigUint, BigInt, ToBigInt, ToBigUint};
use num_traits::identities::One;
use num_traits::identities::Zero;
use indicatif::ParallelProgressIterator;
use indicatif::{ProgressBar, ProgressStyle};

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

    /// Minimum successive primes used (DNA fragment length, binary digits plus one)
    #[clap()]
    min_binary_digits: Option<usize>,

    /// Maximum successive primes used (DNA fragment length, binary digits plus one) [default: same as minimum]
    #[clap()]
    max_binary_digits: Option<usize>,

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

fn cunningham_1st(exact: &BigUint) -> (usize, usize, usize) {
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
    let el = seq;
    dnext = exact.clone();
    loop {
        let cnextnext = dnext.clone().mul(&two).add(&one);
        tests += 1;
        if is_prime(&cnextnext, None).probably() {
            seq += 1;
        } else {
            break;
        }
        dnext = cnextnext.clone();
    }
    return (tests, seq, el);
}

fn cunningham_2nd(exact: &BigUint) -> (usize, usize, usize) {
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
    let el = seq;
    dnext = exact.clone();
    loop {
        let cnextnext = dnext.clone().mul(&two).sub(&one);
        tests += 1;
        if is_prime(&cnextnext, None).probably() {
            seq += 1;
        } else {
            break;
        }
        dnext = cnextnext.clone();
    }
    return (tests, seq, el);
}

fn k_tuple(exact: &BigUint) -> (usize, usize, usize) {
    let two = BigInt::from(2_u64);
    let four = BigInt::from(4_u64);

    let diffs = [four.clone(), two.clone(), four.clone(), two.clone(), four.clone()];
    let mut seq = 1;
    let mut el = 1_usize;
    let mut tests = 0;
    for i in 1..diffs.len()+1 {
        let mut off = BigInt::zero();
        let mut minj = i;
        for j in (0..i).rev() {
            tests += 1;
            off.add_assign(&diffs[j]);
            if off.lt(&exact.to_bigint().unwrap()) && is_prime(
                &exact.to_bigint().unwrap().sub(&off).to_biguint().unwrap(),None).probably() {
                minj = j;
            } else {
                break;
            }
        }
        off = BigInt::zero();
        let mut maxj = i;
        for j in i..diffs.len() {
            tests += 1;
            off.add_assign(&diffs[j]);
            if is_prime(&exact.to_bigint().unwrap().add(&off).to_biguint().unwrap(),None).probably() {
                maxj = j;
            } else {
                break;
            }
        }
        if maxj - minj + 1 > seq {
            if maxj >= 1 && maxj < 3 && minj <= 1 {
                seq = maxj;
                el = i;
            } else if maxj >= 3 && minj <= 1 {
                seq = maxj - minj + 1;
                el = i - minj + 1;
            }
        }
    }
    return (tests, seq, el);
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
                        let (_tests, arity_1st, cunn_1st_el) = cunningham_1st(&exact);
                        tests += _tests;
                        let (_tests, arity_2nd, cunn_2nd_el) = cunningham_2nd(&exact);
                        tests += _tests;
                        let (_tests, arity_k_tuple, k_tuple_el) = k_tuple(&exact);
                        tests += _tests;

                        if arity_1st > 1 {
                            description.push(format!("cunn:1st_{}({})", arity_1st, cunn_1st_el));
                        }
                        if arity_2nd > 1 {
                            description.push(format!("cunn:2nd_{}({})", arity_2nd, cunn_2nd_el));
                        }
                        if arity_k_tuple > 1 {
                            description.push(format!("ktuple_{}({})", arity_k_tuple, k_tuple_el));
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
    if first_zero  || trailing_zeros > 0 {
        return false;
    }
    return true;
}

fn main() {
    let args = Args::parse();

    let start = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();

    let min_kn = args.min_binary_digits.unwrap_or(args.to.unwrap_or(args.from + 100) - args.from );
    let max_kn = args.max_binary_digits.unwrap_or(min_kn);
    let lo = args.from;
    let hi = args.to.unwrap_or(max_kn * 10 + lo);
    let asc = !args.descending;
    let kk = args.power_2;
    let extra_tests = args.extra_tests;

    let mut a = Vec::<BigUint>::new();
    for p in primes(nth_prime(usize::max(args.divisors, hi+1) as u64)+1_u64).iter() {
        a.push(BigUint::from(*p));
    }
    let mut indices = Vec::<(usize, usize, i64, bool)>::new();

    for kn in min_kn..usize::min(max_kn, hi-lo)+1  {
        for i in lo..hi-kn+1 {
            indices.push((i, i + kn, kk, extra_tests));
        }
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

    let pbr = ProgressBar::new(indices.len().try_into().unwrap()).with_style(
        ProgressStyle::with_template(
            "{msg} {wide_bar} {pos}/{len} {elapsed}/{duration} [{binary_bytes_per_sec}]",
        )
        .unwrap(),
    );

    let mut probable_primes = indices.into_par_iter()
    .inspect(|(i, j, k,_extra)| {
        if args.debug {
            println!("Testing span p({},{},{})... ", i, j, k);
        }
    })
        .map(|(i, j, k, extra)| {
        let mut b = Vec::<(usize, String, BigUint, Vec<BigUint>)>::new();
        let tests0 = if running.load(Ordering::SeqCst) {
            bigprime(&a, i, j, k, &mut b, &args, extra)
        } else {
            0
        };
        if b.len() > 0 {
            let tup = b.first().unwrap();
            pbr.set_message(format!("Found p({},{},{})!", i, j, k));
            (i, j, k, tests0 + tup.0, tup.1.clone(), tup.2.clone(), tup.3.clone())
        } else {
            (i, j, k, tests0, "".to_string(), BigUint::zero(), Vec::<BigUint>::new())
        }
    })
    .progress_with(pbr.clone())
    .inspect(|(i, j, k, _tests, description, p, divisors)| {
        if p > &BigUint::zero() && args.verbose {
            let binary_digits = p.to_str_radix(2).len();
            let decimal_digits = p.to_str_radix(10).len();
            println!("{}\t{}\t|{}|p({},{},{})\t{}\t{:?}",
                     binary_digits, decimal_digits, description, i,j, k, p, divisors);
        } else if args.debug {
            if _tests > &0 {
                println!("Span prime p({},{},{}) is composite", i, j, k);
            }  else {
                println!("Span p({},{},{}) span starts or ends with zero", i, j, k);
            }
        }
    })
    .collect::<Vec<(usize, usize, i64, usize, String, BigUint, Vec<BigUint>)>>();

    probable_primes.sort_by(|a,b|  {
        let ordering = if args.sort_by_fragment {
            (a.1-a.0, a.0, a.1).partial_cmp(&(b.1-b.0, b.0, b.1)).unwrap()
        } else {
            (&a.5.clone(), a.0, a.1).partial_cmp(&(&b.5, b.0, b.1)).unwrap()
        };
        if !asc {
            ordering.reverse()
        } else {
            ordering
        }
    });
    let mut prime_count = 0;
    let mut total_tests = 0;
    let mut expected_tests = 0;
    let mut total_score = 0.0;

    pbr.finish_and_clear();

    println!("binary_digits\tdecimal_digits\tdescription\tprobable_prime\tdivisors_used");
    let mut seen = HashMap::<BigUint, bool>::new();
    for (i, j, k, tests, description, p, divisors) in probable_primes {
        if p > BigUint::zero() && (!args.final_strict
            || is_prime(&p, Some(PrimalityTestConfig::strict())).probably()) {
            //numbers_tested_total += tests;
            let binary_digits = p.to_str_radix(2).len();
            let average_tests = (binary_digits as f64 * f64::ln(2.0)).ceil() as usize;
            if !seen.contains_key(&p) || args.duplicates {
                let decimal_digits = p.to_str_radix(10).len();
                println!("{}\t{}\t|{}|p({},{},{})\t{}\t{:?}", binary_digits, decimal_digits, description, i, j, k, p, divisors);
                if !args.duplicates {
                    seen.insert(p, true);
                }
                total_score += (average_tests as f64).powf(3.0) * (average_tests as f64).ln();
                prime_count += 1;
                expected_tests += average_tests;
            }
        }
        total_tests += tests;
    }
    eprintln!("Found {} probable primes using {} tests compared to {} expected tests. Speed-up {:.1}×.",
              prime_count, total_tests, expected_tests, (expected_tests as f64)/(total_tests as f64));

    let end = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();

    eprintln!("Time: {:?}  Log Score: {:.4}  Log Score per sec: {:.4}", end - start, total_score.ln(), (total_score / (end -start).as_secs_f64()).ln());

    return;
}
