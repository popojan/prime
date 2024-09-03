mod rpn;

extern crate core;

use crate::rpn::_parse_rpn;

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use indicatif::ParallelProgressIterator;
use indicatif::{ProgressBar, ProgressStyle};

use std::ops::{Add, AddAssign, Div, DivAssign, Mul, Rem, Shl, Shr, Sub};
use std::time::{SystemTime, UNIX_EPOCH};
use num_bigint::{BigUint, BigInt, ToBigUint};
use num_traits::identities::One;
use num_traits::identities::Zero;
use num_traits::{Signed, ToPrimitive};
use num_traits::Num;
use rayon::prelude::*;

use num_prime::nt_funcs::{is_prime, primes, nth_prime};

use clap::Parser;
use num_prime::PrimalityTestConfig;

/// Program to generate big (strongly probable) primes fast.

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {

    /// Order of the highest precalculated divisor prime
    #[clap(short, long, value_parser, default_value_t = 1000)]
    divisors: usize,

    /// Start generating from bigger primes to smaller
    #[clap(long, value_parser, default_value_t = false)]
    descending: bool,

    /// Sorts resulting primes by underlying DNA fragment
    #[clap(long, value_parser, default_value_t = false)]
    sort_by_fragment: bool,

    /// Perform extra tests (k-tuples, Cunningham)
    #[clap(short, long, value_parser, default_value_t = false)]
    extra_tests: bool,

    /// Immediately output probable primes to stderr
    #[clap(long, value_parser, default_value_t = false)]
    verbose: bool,

    /// Print debug information related to each tested span to stderr
    #[clap(long, value_parser, default_value_t = false)]
    debug: bool,

    /// Perform final strict probable primality test
    #[clap(long, value_parser, default_value_t = false)]
    final_strict: bool,

    /// Nesting level (default: 3)
    #[clap()]
    nesting_level: Option<u64>,

    /// Nesting initial number (default: 1)
    #[clap()]
    base_from: Option<String>,

    /// Number of consecutive numbers to test (default: 100)
    #[clap()]
    base_count: Option<String>,

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
    let two = BigUint::from(2_u64);
    let six = BigUint::from(6_u64);
    let eight =  BigUint::from(8_u64);
    let four = BigUint::from(4_u64);
    let twelve = BigUint::from(12_u64);
    let diffs = [two, six, eight, four, twelve];
    let mut seq = 1;
    let mut el = 1;
    let mut tests = 0;
    'outer: for i in 0..diffs.len() {
        let mut nseq = 1;
        let nel = i+1;
        let mut off = BigUint::zero();
        for j in (0..i).rev() {
            tests += 1;
            off.add_assign(&diffs[j]);
            if off.lt(exact) && is_prime(&exact.clone().sub(&off),None).probably() {
                nseq += 1;
            } else {
                continue 'outer;
            }
        }
        off = BigUint::zero();
        'inner: for j in i..diffs.len() {
            tests += 1;
            off.add_assign(&diffs[j]);
            if is_prime(&exact.clone().add(&off),None).probably() {
                nseq += 1;
            } else {
                break 'inner;
            }
        }
        if nseq > seq && nseq >= nel {
            seq = nseq;
            el = nel;
        }
    }
    return (tests, seq, el);
}

fn _bigprime(a: &Vec<BigUint>, i:usize,j:usize,k:i64, b: &mut Vec<(usize, String, BigUint, Vec<BigUint>)>, args: &Args, extra_tests: bool) -> usize {
    if !_bigprime_dry(&a, i, j) {
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

fn _bigprime_dry(a: &Vec<BigUint>, i:usize, j:usize) -> bool {
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
    for _i in 0..k {
        let na: BigInt = a.clone().mul(&b).shl(1) - a.clone().sub(&b).abs();
        let nb = na.clone().add(&BigInt::one());
        //let nb = (a.clone().mul(&a).add(b.clone().mul(&b)).sub(&BigInt::one())).div(a.clone().sub(&b).abs());
        a = na;
        b = nb;
    }
    let pp: BigUint = a.add(&b).abs().to_biguint().unwrap();
    let (exact, divisors) = if args.allow_divided {
        myreduce(args.divisors, &pp, &aa)
    } else {
        (pp, vec![])
    };
    //let exact = accum;

    let mut tests;
    tests = 1;
    if is_prime(&exact, None).probably() {
        let mut description = vec!["prime".to_string()];

        if args.extra_tests {
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
        ret.push((tests, description.join("|"), exact.clone(), divisors));
        tests = 0;
    }
    return tests;
}

fn main() {
    let args = Args::parse();

    let start = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();

    let kk: u64 = args.nesting_level.unwrap_or(3_u64);
    let base_from = args.base_from.clone().unwrap_or("1".to_string());
    let base_count = args.base_count.clone().unwrap_or("100".to_string());
    let min_kn = if base_from.contains(" ") {
        _parse_rpn(&base_from)
    } else {
        BigInt::from_str_radix(&base_from, 10).unwrap()
    };
    let max_kn = if base_count.contains(" ") {
        _parse_rpn(&base_count)
    } else {
        BigInt::from_str_radix(&base_count, 10).unwrap()
    };
    let asc = !args.descending;

    let mut a = Vec::<BigUint>::new();
    for p in primes(nth_prime(args.divisors as u64)+1_u64).iter() {
        a.push(BigUint::from(*p));
    }
    let mut indices = Vec::<(BigInt, BigInt, u64)>::new();

    let mut bi = min_kn.clone();
    let lim = min_kn.add(&max_kn);
    while bi.lt(&lim) {
        indices.push((bi.clone(), bi.clone(), kk));
        bi.add_assign(&BigInt::one());
    }
    if asc {
        indices.sort_by(|b, a| (
            b.0.clone(), b.1.clone() - b.0.clone()).partial_cmp(&(a.0.clone(), a.1.clone() - a.0.clone())
        ).unwrap());
    } else {
        indices.sort_by(|a, b| (
            b.0.clone(), b.1.clone() - b.0.clone()).partial_cmp(&(a.0.clone(), a.1.clone() - a.0.clone())
        ).unwrap());
    };

    let running = Arc::new(AtomicBool::new(true));
    let r = running.clone();

    ctrlc_async::set_handler(move || {
        r.store(false, Ordering::SeqCst);
        eprintln!("Ctrl+C handler called!");
    }).expect("Error setting Ctrl-C handler");

    let pbr = ProgressBar::new(max_kn.to_u64().unwrap()).with_style(
        ProgressStyle::with_template(
            "{msg} {wide_bar} {pos}/{len} {elapsed}/{duration} [{binary_bytes_per_sec}]",
        )
        .unwrap(),
    );

    let probable_primes = indices.into_par_iter()
    .progress_with(pbr.clone())
    .inspect(|(i, _j, k)| {
        if args.debug {
            println!("Testing nested number n({},{})... ", i, k);
        }
    })
        .map(|(i, j, k)| {
        let mut b = vec![];
        let tests0  = if running.load(Ordering::SeqCst) {
            nested_prime(&a,
                         &BigInt::from(i.clone()).shl(1_u32).add(&BigInt::one()),
                         kk as usize,
                         &mut b,
                         &args)
        } else {
            0
        };
        if b.len() > 0 {
            let tup = b.first().unwrap();
            pbr.set_message(format!("Found n({}, {})!", i, k));
            (i, j, k, tests0 + tup.0, tup.1.clone(), tup.2.clone(), tup.3.clone())
        } else {
            (i, j, k, tests0, "".to_string(), BigUint::zero(), Vec::<BigUint>::new())
        }
    })
    .inspect(|(i, _j, k, _tests, description, p, divisors)| {
        if p > &BigUint::zero() && args.verbose {
            let binary_digits = p.to_str_radix(2).len();
            let decimal_digits = p.to_str_radix(10).len();
            println!("{}\t{}\t|{}|n({},{})\t{}\t{:?}",
                     binary_digits, decimal_digits, description, i, k, p, divisors);
        } else if args.debug {
            if _tests > &0 {
                println!("Nested number n({},{}) is composite", i, k);
            }  else {
            }
        }
    })
    .collect::<Vec<(BigInt, BigInt, u64, usize, String, BigUint, Vec<BigUint>)>>();

    let mut prime_count = 0;
    let mut total_tests = 0;
    let mut expected_tests = 0;
    let mut total_score = 0.0;

    println!("binary_digits\tdecimal_digits\tdescription\tprobable_prime\tdivisors_used");
    for (i, _j, k, tests, description, p, divisors) in probable_primes {
        if p > BigUint::zero() && (!args.final_strict || !running.load(Ordering::SeqCst)
            || is_prime(&p, Some(PrimalityTestConfig::strict())).probably()) {
            //numbers_tested_total += tests;
            let binary_digits = p.to_str_radix(2).len();
            let average_tests = (binary_digits as f64 * f64::ln(2.0)).ceil() as usize;
            let decimal_digits = p.to_str_radix(10).len();
            println!("{}\t{}\t|{}|n({},{})\t{}\t{:?}", binary_digits, decimal_digits, description, i, k, p, divisors);
            prime_count += 1;
            expected_tests += average_tests;
            total_score += (average_tests as f64).powf(3.0) * (average_tests as f64).ln();
        }
        total_tests += tests;
    }

    eprintln!("Found {} probable primes using {} tests compared to {} expected tests. Speed-up {:.1}×.",
              prime_count, total_tests, expected_tests, (expected_tests as f64)/(total_tests as f64));

    let end = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();

    eprintln!("Time: {:?}  Log Score: {:.4}  Log Score per sec: {:.4}", end - start, total_score.ln(), (total_score / (end -start).as_secs_f64()).ln());

    return;
}
