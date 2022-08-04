extern crate core;

use std::ops::{Add, Div, Mul, Rem, Sub};
use num_bigint::{BigUint, ToBigUint};
use num_traits::identities::One;
use num_traits::identities::Zero;
use std::collections::HashSet;

use std::env;

use num_prime::nt_funcs::{is_prime, primes, nth_prime};
use num_traits::ToPrimitive;

fn myreduce(n:usize, ap:&BigUint, a: &Vec<BigUint>) -> BigUint{
    let mut accum = ap.clone();
    for p in a[0..n].iter().chain(vec![BigUint::from(2_u64)].iter()) {
        while p < &accum && accum.clone().rem(p) == BigUint::zero() {
            accum = accum.div(p);
        }
        if p > &accum {
            break;
        }
    }
    return accum;
}

fn _bigprime(a: &Vec<BigUint>, i:usize,j:usize,k:i64, b: &mut Vec<BigUint>) -> (usize, usize, usize){
    let mut last = &a[i];
    let zero= BigUint::zero();
    let one= BigUint::one();
    let two = BigUint::from(2_u64);
    let mut accum = if k < 0 {zero.clone()} else {two.pow(k as u32)};
    let mut digit = BigUint::from(1_u64);
    let mut leading = true;
    let mut first_zero = false;
    let mut trailing_zeros = 0;
    let mut leading_zeros = 0;
    let mut first = true;
    for  p in &a[i+1..j] {
        let add = one.clone()-p.sub(last).to_biguint().unwrap().div(two.clone()).rem(two.clone());
        if !first {
            if add == zero {
                if leading {
                    leading_zeros += 1;
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
        accum = accum.add(digit.clone().mul(add));
        digit = digit.mul(&two);
        last = p;
    }
    let mut tests = 0;
    if first_zero || trailing_zeros > 0 {
        return (tests, leading_zeros, trailing_zeros);
    }
    if accum > two {
        if  accum > zero && accum != one {
            if accum.clone().rem(&two) == zero {
                accum = accum.add(&one);
            }
            let exact = myreduce(j, &accum, &a);
            //let exact = accum;
            if is_prime(&exact, None).probably() {
                b.push(exact);
            }
            tests = 1;
        }
    }
    return (tests, leading_zeros, trailing_zeros);
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
    let zero= BigUint::zero();
    let one= BigUint::one();
    let two = BigUint::from(2_u64);
    let mut seq = 1;
    let mut dnext = exact.clone();
    let mut tests = 0;
    loop {
        let mut cnextnext = dnext.clone().add(&one);
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

fn popojan(a: &Vec<BigUint>, i:usize,j:usize,k:i64, b: &mut Vec<(usize, String, BigUint)>, extra_tests: bool) -> (usize, usize, usize){
    let zero= BigUint::zero();
    let one= BigUint::one();
    let two = BigUint::from(2_u64);
    let mut last = &a[i];
    let mut accum = if k < 0 {zero.clone()} else {two.pow(k as u32)};
    let mut digit = BigUint::from(1_u64);
    let mut leading = true;
    let mut first_zero = false;
    let mut trailing_zeros = 0;
    let mut leading_zeros = 0;
    let mut first = true;
    for  p in &a[i+1..j] {
        let add = p.sub(last).to_biguint().unwrap().div(two.clone()).rem(two.clone());
        if !first {
            if add == zero {
                if leading {
                    leading_zeros += 1;
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
        accum = accum.add(digit.clone().mul(add));
        digit = digit.mul(&two);
        last = p;
    }
    let mut tests = 0;
    if first_zero || trailing_zeros > 0 {
        return (tests, leading_zeros, trailing_zeros);
    }
    if accum > two {
        if  accum > zero && accum != one {
            if accum.clone().rem(&two) == zero {
                accum = accum.add(&one);
            }
            let exact = myreduce(j, &accum, &a);
            //let exact = accum;
            tests = 1;
            //eprintln!("new {} {},{},{}", p0s.len(), i,j,k);
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
                b.push((tests, description.join("|"), exact.clone()));
                tests = 0;
            }
        }
    }
    return (tests, leading_zeros, trailing_zeros);
}

fn magic(i:usize) ->usize {
    (BigUint::from(1827175083751_u64).div(BigUint::from(207256360584_u64))
        +BigUint::from(622226202419_u64).mul(BigUint::from(i)).div(BigUint::from(621769081752_u64))).to_usize().unwrap()+1
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 {
        let arg1 = args.get(1).unwrap();
        if arg1 == "--help" || arg1 == "-h" {
            println!("Usage: {} <count> [<lo> <hi> <kk> <ascending> <minkn> <duplicates> <extra_tests> <min_steps>]", args.get(0).unwrap());
            return;
        }
    }
    let cnt = usize::from_str_radix(&args.get(1).unwrap_or(&"1000000".to_string()),10).unwrap();
    let lo = usize::from_str_radix(&args.get(2).unwrap_or(&"1000".to_string()),10).unwrap();
    let hi = usize::from_str_radix(&args.get(3).unwrap_or(&"2000".to_string()),10).unwrap();
    let kk = i64::from_str_radix(&args.get(4).unwrap_or(&"-1".to_string()),10).unwrap();
    let _ascending = usize::from_str_radix(&args.get(5).unwrap_or(&"0".to_string()),10).unwrap();
    let _minkn = usize::from_str_radix(&args.get(6).unwrap_or(&"3".to_string()),10).unwrap();
    let duplicates = usize::from_str_radix(&args.get(7).unwrap_or(&"0".to_string()),10).unwrap();
    let extra_tests = usize::from_str_radix(&args.get(8).unwrap_or(&"0".to_string()),10).unwrap();
    let min_steps = usize::from_str_radix(&args.get(9).unwrap_or(&"0".to_string()),10).unwrap();

    let mut a = Vec::<BigUint>::new();
    for p in primes(nth_prime((magic(hi)+1) as u64)+1 as u64).iter() {
        a.push(BigUint::from(*p));
    }
    let mut lastcnt = 0;
    let mut set = HashSet::<BigUint>::new();
    let mut numbers_tested_total = 0;
    let mut numbers_tested_total_last;
    let mut numbers_tested_average = 0;
    let mut numbers_found = 0;
    //let mut kn = if ascending > 0 {minkn } else {hi - lo};
    let mut i = magic(lo);
    let limit = magic(hi);
    let mut total_steps = 1;
    let mut kn;
    eprintln!("{}",vec!["total_steps", "numbers_found", "binary_digits", "decimal_digits", "numbers_tested_total", "numbers_tested_average", "speedup"].join(", "));
    numbers_tested_total_last = numbers_tested_total;
    while lastcnt < cnt  {
        //let mut i = lo;
        kn = magic(i);
        if kn > limit {
            break;
        }
        if total_steps < min_steps {
            i = kn;
            //eprintln!("step {} {}", total_steps, kn);
            total_steps += 1;
            continue;
        }
        //while i < hi - kn {
        let mut b = Vec::<(usize, String, BigUint)>::new();
        let (tests, _skipl, _skipr) = popojan(&a, i, i+kn, kk, &mut b, extra_tests>0);
        numbers_tested_total += tests;
        eprint!("\r{} tests", numbers_tested_total - numbers_tested_total_last);
        let mut binary_digits=0;
        let mut decimal_digits=0;
        if b.len() > 0 {
            for (tests, description, p) in b.iter() {
                numbers_tested_total += tests;
                if duplicates > 0 || !set.contains(p) {
                    binary_digits = p.to_str_radix(2).len();
                    decimal_digits = p.to_str_radix(10).len();
                    let average_tests = (binary_digits as f64 * f64::ln(2.0)).ceil() as usize;
                    println!("{}/{}\t{}\t{}\t|{}|p({},{},{})\t{}",
                             numbers_tested_total - numbers_tested_total_last, average_tests,
                             binary_digits, decimal_digits, description, i, i+kn, kk, p);
                    numbers_found += 1;
                    set.insert(p.clone());
                    lastcnt += 1;
                    numbers_tested_average += average_tests;
                    if lastcnt >= cnt {
                        break;
                    }
                }
            }
            b.clear();
            eprintln!("\r{{{}, {}, {}, {}, {}, {}, {:.2}}},",
                      total_steps, numbers_found, binary_digits, decimal_digits, numbers_tested_total, numbers_tested_average, numbers_tested_average as f64 / numbers_tested_total as f64);
            numbers_tested_total_last = numbers_tested_total;
        }
        /*if lastcnt >= cnt {
            break;
        }*/
        i = kn;//skipl;//usize::max(skipl, skipr + 1);
        total_steps += 1;
        //}
        //kn = if ascending > 0 { kn + 1 } else { kn - 1 };
        if lastcnt >= cnt {
            break;
        }
    }
    eprintln!("Found {} primes. Total tests {} / average tests {} = {:.2} speedup",
              numbers_found, numbers_tested_total, numbers_tested_average, numbers_tested_average as f64 /numbers_tested_total as f64);
    return;
}
