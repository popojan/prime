use std::ops::{Add, Div, Mul, Rem, Sub};
use num_bigint::{BigUint, ToBigUint};
use num_traits::identities::One;
use num_traits::identities::Zero;
use std::collections::HashSet;

use std::env;

use num_prime::nt_funcs::{is_prime, primes, nth_prime};

fn myreduce(n:usize, ap:&BigUint, a: &Vec<BigUint>) -> BigUint{
    let mut accum = ap.clone();
    for p in a[0..n].iter().chain(vec![BigUint::from(2_u64)].iter()) {
        while &accum > p && accum.clone().rem(p) == BigUint::zero() {
            accum = accum.div(p);
        }
    }
    return accum;

}
fn bigprime(a: &Vec<BigUint>, i:usize,j:usize,k:usize, b: &mut Vec<BigUint>) -> (usize, usize){
    let mut last = &a[i];
    let zero= BigUint::zero();
    let one= BigUint::one();
    let two = BigUint::from(2_u64);
    let mut accum = two.pow(k as u32);
    let mut digit = BigUint::from(1_u64);
    //let mut it = 0_usize;
    let mut leading = true;
    let mut trailing_zeros = 0;
    let mut leading_zeros = 0;
    for  p in &a[i+1..j] {
        let add = digit.clone().mul(one.clone()-p.sub(last).to_biguint().unwrap().div(two.clone()).rem(two.clone()));
        if add == zero {
            if leading {
                leading_zeros += 1;
            }
            trailing_zeros += 1;
        }
        else {
            leading = false;
            trailing_zeros = 0;
        }
        accum = accum.add(&add);
        digit = digit.mul(&two);
        last = p;
        //it += 1;
    }
    if accum > two {
        if accum.clone().rem(two) == zero {
            let below = myreduce(j / 2, &accum.clone().sub(one.clone()).to_biguint().unwrap(), &a);
            let above = myreduce(j / 2, &accum.clone().add(one.clone()), &a);
            if is_prime(&below, None).probably() {
                b.push(below);
            }
            if is_prime(&above, None).probably() {
                b.push(above);
            }
        }
        else if  accum > zero && accum != one {
            let exact = myreduce(j / 2, &accum, &a);
            if is_prime(&exact, None).probably() {
                b.push(exact);
            }
        }
    }
    return (leading_zeros, trailing_zeros);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("Usage: {} <count> <lo> <hi> <kk>", args.get(0).unwrap());
        return;
    }
    let cnt = usize::from_str_radix(&args.get(1).unwrap_or(&"1".to_string()),10).unwrap();
    let lo = usize::from_str_radix(&args.get(2).unwrap_or(&"100".to_string()),10).unwrap();
    let hi = usize::from_str_radix(&args.get(3).unwrap_or(&"200".to_string()),10).unwrap();
    let kk = usize::from_str_radix(&args.get(4).unwrap_or(&"1".to_string()),10).unwrap();

    let mut a = Vec::<BigUint>::new();
    for p in primes(nth_prime((hi+1) as u64)+1 as u64).iter() {
        a.push(BigUint::from(*p));
    }
    let mut b = Vec::<BigUint>::new();
    //let rng = rand::thread_rng();
    let mut lastcnt = 0;
    let mut set = HashSet::<BigUint>::new();
    let mut _hi = hi;// + rng.gen::<usize>() % (hi-lo) as usize;
    let mut numbers_tested = 0;
    let mut numbers_tested_total = 0;
    let mut numbers_tested_average = 0;
    while lastcnt < cnt {
        let mut  _lo = lo;//(hi as f64).sqrt().ceil() as usize;
        //_lo = rng.gen::<usize>() % _lo as usize;
        //let h =  (hi as f64).sqrt().sqrt().ceil() as usize;
        _hi-=1;
        if _hi < lo || _hi > hi {
            break;
        }
        let mut skip_start = 0;
        let mut skip_end = 0;
        for i in _lo .. _hi {
            if skip_start > 0 || i > _hi - skip_end {
                skip_start -= 1;
                continue;
            }
            //println!("{},{},{}",b.len(),i,_hi);
            let (skipl, skipr) = bigprime(&a, i, _hi,kk, &mut b);
            skip_end += skipr;
            skip_start += skipl;
            numbers_tested += 1;
            if b.len() > 0 {
                for p in b.iter() {
                    if !set.contains(p) {
                        let binary_digits = p.to_str_radix(2).len();
                        let decimal_digits = p.to_str_radix(10).len();
                        let average_tests = binary_digits*f64::ln(2.0).ceil() as usize;
                        println!("{}/{}\t{}\t{}\t{}\tbigprime({}, {}, {})",
                                 numbers_tested, average_tests,
                                 binary_digits, decimal_digits, p, i, _hi, kk);
                        set.insert(p.clone());
                        lastcnt += 1;
                        numbers_tested_total += numbers_tested;
                        numbers_tested_average += average_tests;
                        numbers_tested = 0;
                        if lastcnt >= cnt {
                            break;
                        }
                    }
                }
                b.clear();
            }
            if lastcnt >= cnt {
                break;
            }
        }
    }
    println!("Total tests {} / average tests {}", numbers_tested_total, numbers_tested_average);
    return;
}