extern crate core;


use astro_float::BigFloat;
use std::fmt::format;
//use std::intrinsics::powf64;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign};
use std::thread::Builder;
use std::time::Instant;
use clap::ArgAction::SetTrue;
use num_bigint::{BigInt, BigUint, ToBigInt};
use num_traits::identities::One;
use num_traits::identities::Zero;
use rayon::prelude::*;

use num_prime::nt_funcs::{is_prime, primes, nth_prime, next_prime, prev_prime, nth_prime_est, prime_pi_est};
use num_traits::{Pow, pow, ToPrimitive, Signed};

use clap::Parser;
use num_complex::ComplexFloat;
use num_prime::PrimalityTestConfig;
use num_modular::{ModularCoreOps, ModularInteger, MontgomeryInt};

use number_theory::NumberTheory;
use number_theory::Mpz;

/// Program to generate big (strongly probable) primes fast. Uses fragments of prime DNA,
/// sequence of half the difference between two successor primes mod 2 as binary digits
/// of a big prime candidate being tested for primality. Somehow it works much better
/// than random or sequential search.

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Order of the lowest precalculated prime
    #[clap(short, long, value_parser, default_value_t = 1)]
    from: usize,

    /// Order of the highest precalculated prime
    #[clap(short, long, value_parser, default_value_t = 1000)]
    to: usize,

    /// Order of the highest precalculated divisor prime
    #[clap(short, long, value_parser, default_value_t = 100000)]
    divisors: usize,

    /// Start generating from bigger primes to smaller
    #[clap(long, value_parser, default_value_t = false)]
    descending: bool,

    /// Sorts resulting primes by underlying DNA fragment
    #[clap(long, value_parser, default_value_t = false)]
    sort_by_fragment: bool,

    /// Add extra power of two
    #[clap(short, long, value_parser, default_value_t = -1)]
    power_2: i64,

    /// Perform extra tests (k-tuples, Cunningham)
    #[clap(short, long, value_parser, default_value_t = false)]
    extra_tests: bool,

    /// Minimal DNA fragment length
    #[clap(long, value_parser, default_value_t = 255)]
    min_span: usize,

    /// Exact DNA fragment length
    #[clap(long, value_parser, default_value_t = 0)]
    span: usize,

    /// undocumented speedup, finds less primes
    #[clap(long, value_parser, default_value_t = false)]
    diagonal: bool,

    /// Maximal DNA fragment length
    #[clap(long, value_parser, default_value_t = 255)]
    max_span: usize,

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
    duplicates: bool
}

fn myreduce(n:usize, ap:&BigUint, a: &Vec<BigUint>) -> (BigUint, Vec<BigUint>) {
    let mut accum = ap.clone();
    let mut divisors = vec![];
    for p in a[0..n].iter().chain(vec![BigUint::from(2_u64)].iter()) {
        while p < &accum && accum.clone().rem(p) == BigUint::zero() {
            accum = accum.div(p);
            divisors.push(p.clone());
        }
        if p > &accum {
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

fn mersenne_plus_2_third(a: &Vec<BigUint>, dna: &Vec<u8>, i:usize,j:usize,k:i64, b: &mut Vec<(usize, String, BigUint, Vec<BigUint>)>, extra_tests: bool) -> usize {
    let zero= BigUint::zero();
    let one= BigUint::one();
    let two = BigUint::from(2_u64);
    let three = BigUint::from(3_u64);
    let p = two.pow(a[i].to_u32().unwrap()).add(&one);
    if p.clone().rem(&three) == zero {
        //let (q, divisors) = myreduce(a.len(), &p.div(&three), &a);
        let q = p.div(&three);
        let divisors = vec![];
        if is_prime(&q, None).probably() {
            b.push((1, format!("1/3(2^{} + 1)", a[i]).to_string(), q, divisors));
            return 0;
        }
        return 1;
    } else {
        b.push((0, format!("1/3(2^{} - 1 mod 3 > 0", a[i]).to_string(), p, vec![]));
        return 0;
    }
    return 0;
}

fn total_eg(digits: &Vec<u8>, mul: &BigUint) -> (BigUint,BigUint) {
    let mut b = BigUint::from(1_u64);
    let mut num = BigUint::zero();
    let two = BigUint::from(2_u64);
    let max = two.clone().pow(digits.len()-1);
    for digit in digits.iter() {
        num += max.clone().div(&b).mul(digit);
        b = b.mul(&two);
    }
    (num.mul(mul), max)
}

fn isq(power:&BigUint, i: (&BigUint,&BigUint), j: (&BigUint,&BigUint)) -> (BigUint,BigUint){
    let p = BigUint::from(2_u64).pow(power.to_u64().unwrap());
    (p.clone().mul(i.0.add(i.1)).div(i.1),p.clone().mul(j.0.add(j.1)).div(j.1))
}

fn rev3(prime:&BigUint, power:&BigUint, i: (&BigUint, &BigUint), j: (&BigUint, &BigUint)) -> BigUint {
    let (a,b)= isq(power, i, j);
    let ta = total_eg(&a.to_radix_le(2), prime);
    let tb = total_eg(&b.to_radix_le(2), &BigUint::one());
    let den =  ta.1.clone()*tb.1.clone();
    let num = ta.0.mul(&tb.1).add(tb.0.mul(&ta.1));
    if num.clone().rem(&den)==BigUint::zero() {
        prime.clone().add(num.div(&den))
    } else {
        BigUint::zero()
    }
}

fn next(prime:&BigUint, a: &BigUint, b: &BigUint) -> BigUint {
    let ta = total_eg(&a.to_radix_le(2), prime);
    let tb = total_eg(&b.to_radix_le(2), &BigUint::one());
    let den =  ta.1.clone()*tb.1.clone();
    let num = ta.0.mul(&tb.1).add(tb.0.mul(&ta.1));
    if num.clone().rem(&den)==BigUint::zero() {
        prime.clone().add(num.div(&den))
    } else {
        BigUint::zero()
    }
}
fn bigprime(a: &Vec<BigUint>, dna: &Vec<u8>, i:usize,j:usize,k:i64, b: &mut Vec<(usize, String, BigUint, Vec<BigUint>)>, extra_tests: bool) -> usize {
    let zero= BigUint::zero();
    let one= BigUint::one();
    let two = BigUint::from(2_u64);
    //let mut last = &dna[i];
    let mut accum = if k < 0 {zero.clone()} else {two.clone().pow(k as u32)};
    let mut digit = BigUint::from(1_u64);
    for (k, gene) in dna[i..j].iter().enumerate() {
        accum = accum.add(&a[k+i].clone().mul(gene).mul(&digit));
        digit = digit.mul(&two);
    }
    let mut tests = 0;
    if accum > two {
        if  accum > zero && accum != one {
            if accum.clone().rem(&two) == zero {
                accum = accum.add(&one);
            }
            let (exact, divisors) = myreduce(j-i, &accum, &a); //(accum, vec![]);//
            //let exact = accum;
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
    return tests;
}

fn magic(i:usize) ->usize {

    (BigUint::from(1827175083751_u64).div(BigUint::from(207256360584_u64))
        +BigUint::from(622226202419_u64).mul(BigUint::from(i)).div(BigUint::from(621769081752_u64))).to_usize().unwrap()+1
}

/*fn identity(i:usize) -> usize {
    i
}
*/
fn big_two_twins(k: usize, ii:usize,max: usize) -> (usize, (bool, BigUint), (bool, BigUint)) {
    //2^(k + 1) - 2^(k - Floor[k/2])
    /*let mut binary_a = vec![0_u8; k + 2];
    let mut binary_b = vec![0_u8; k - k/2 + 1];
    binary_a[0] = 1;
    binary_b[0] = 1;*/
    let mut p = BigUint::from(2_usize).pow(k+1_usize);//BigUint::from_radix_be(&binary_b, 2).unwrap();
    for i in ii..(k+1) {
        let mut a = BigUint::from(2_usize).pow(k-i);//_radix_be(&binary_a, 2).unwrap();
        p.sub_assign(a);
    }
    let mut steps = 0;
    let mut q = p.clone();
    let mut pq = false;
    let cfg = None;
    if !is_prime(&p, cfg).probably()
    {
        p = next_prime(&p, cfg).unwrap();
    }
    loop {
        q = p.clone().add(BigUint::from(2_usize));
        steps += 1;
        pq = is_prime(&q, cfg).probably();
        if pq || steps >= max { break; }
        p = next_prime(&p, cfg).unwrap();
    }
    (steps, (true, p), (pq, q))
}

fn big_zero_twins(odd_w: BigUint, zero_count: usize) -> ((bool, BigUint), (bool, BigUint)) {
    let mut decimal = vec![0_u8; zero_count+1-odd_w.to_str_radix(10).len()];
    decimal[0] = 1;
    let mut p = BigUint::from_radix_be(&decimal ,10).unwrap();
    p.mul_assign(&odd_w);
    p.add_assign(&odd_w);
    p.add_assign(BigUint::from(2_usize));
    let prime2 = is_prime(&p, None).probably();
    let q = p.clone().add(BigUint::from(4_usize));
    let prime4 = is_prime(&q, None).probably();
    ((prime2, p), (prime4, q))
}

fn big_fast_twins(k: usize, third: bool, max_steps: usize) -> (isize, (bool, BigUint), (bool, BigUint), BigUint) {
    let a = BigUint::from(2_usize).pow(k);
    let b = BigUint::from(2_usize).pow(k+1);
    let p00 = (a.clone().add(
         if third {
            b.sub(&a)
            .div(BigUint::from(3_usize))
        } else {
        BigUint::zero()}));
    //let a= 2.51368;
    //let b = 3.20683;
    //let c = 0.0605536;
    //let diff = BigUint::from(f64::floor(((b-a)*(k as f64)/(b+c*(k as f64))).exp()) as usize);
    let pl0 = p00.clone();//.sub(&diff);//add(BigUint::from((k as f64 / 2.0.ln()*f64::exp(7.0))as usize));
    let pr0 = p00.clone();//add(&diff);//sub(BigUint::from((k as f64 / 2.0.ln()*f64::exp(7.0))as usize));
    let mut steps = 0;
    let mut pl = pl0.clone();
    let mut pr = pr0.clone();
    let mut ql: BigUint = pl0.clone();
    let mut qr: BigUint = pr0.clone();
    let mut prime4l = false;
    let mut prime4r = false;
    //let base: f64 = 2.0;
    if !is_prime(&pl, None).probably() {
        pl = prev_prime(&pl, None).unwrap();
    }
    if !is_prime(&pr, None).probably() {
        pr = next_prime(&pr, None).unwrap();
    }
    /*let aa = -0.505638;//496082;
    let bb = 13.1404;//9.03497;
    let mult0 = (bb + aa*(2.0*k as f64));
    let prec = 5_u32;
    let scale = f64::floor(-mult0)+prec as f64;
    let mult = BigUint::from(2_usize).pow(scale as usize);
    let diff = pl.clone().div(BigUint::from(2_usize).pow(BigUint::from(prec))).mul(&mult);
    //println!("{:?}, i={}, scale={}, mult0={} mult={:?}, diff = {:?}",p0, k, scale, mult0, mult,diff);

    if(diff < pl) {    pl.sub_assign(&diff); }
    if(diff < pr) {pr.add_assign(&diff);}

    if pl > BigUint::one() && !is_prime(&pl, None).probably() {
        pl = prev_prime(&pl, None).unwrap();
    }
    if !is_prime(&pr, None).probably() {
        pr = next_prime(&pr, None).unwrap();
    }

*/
    let pl0 = pl.clone();
    let pr0 = pr.clone();

    //if(pl > BigUint::from(2_usize)) {
        while steps < max_steps  {
            ql = pl.clone().sub(BigUint::from(2_usize));
            qr = pr.clone().add(BigUint::from(2_usize));
            prime4l = is_prime(&ql, None).probably();
            prime4r = is_prime(&qr, None).probably();
            steps += 1;
            if prime4l || prime4r { break }
            if pr.clone().sub(&p00).gt(&BigUint::from(max_steps * 6)) { break }
            if p00.clone().sub(&pl).gt(&BigUint::from(max_steps * 6)) { break }
            pl = prev_prime(&pl, None).unwrap();
            pr = next_prime(&pr, None).unwrap();
        }
    //}
    if prime4r {
        return (steps as isize, (true, pr.clone()), (prime4r, qr), pr.sub(&p00));
    }
    return (-(steps as isize), (true, pl.clone()), (prime4l, ql), p00.sub(&pl));
}

fn big_fastest_twins(k: usize, third: bool, max_steps: usize) -> (isize, (bool, BigUint), (bool, BigUint), BigUint) {
    let a = BigUint::from(2_usize).pow(k);
    let b = BigUint::from(2_usize).pow(k+1);
    let p00 = (a.clone().add(
        if third {
            b.sub(&a)
                .div(BigUint::from(3_usize))
        } else {
            BigUint::zero()}));
    let pl0 = p00.clone();
    let mut steps = 0;
    let mut pl = pl0.clone();//.add(BigUint::one());
    let mut ql: BigUint = pl0.clone();
    let mut prime4l = false;
    if is_prime(&pl, None).probably() {
        ql = pl.clone().add(BigUint::from(2_usize));
        prime4l = is_prime(&ql, None).probably();
    }
    return (-(steps as isize), (true, pl.clone()), (prime4l, ql), pl.sub(&pl0));
}

fn is_mersenne_exponent(p: u128) -> bool {
    let four = BigUint::from(4_usize);
    let two = BigUint::from(2_usize);
    let M = two.clone().pow(p).sub(BigUint::one());
    let mut s = four.clone();
    for i in 1..p-1 {
        s = s.pow(&two).sub(&two);
        if s > M  {
            s.rem_assign(&M);
        }
    }
    //println!("{:?}",next_prime( &M, None).unwrap());
    return s == BigUint::zero();
}

fn log_integral(x: &BigFloat, prec: usize) -> BigFloat {
    const nr: astro_float::RoundingMode = astro_float::RoundingMode::None;
    let mut cc = astro_float::Consts::new().unwrap();
    let gamma = BigFloat::from_f64(0.5772156649015328606065120900824024310421593359399235988057672348848677267776646709369470632917467495, prec);
    let mut ret: BigFloat = gamma;
    ret = ret.add(&x.ln(prec, nr, &mut cc).ln(prec, nr, & mut cc), prec, nr);

    let sqx:BigFloat = x.sqrt(prec, nr);
    let mut add: BigFloat = BigFloat::from_f64(0.0, prec);
    let mut n = 1_u64;
    let mut nfact : BigFloat = BigFloat::from_u64(1_u64, prec);
    let lnx = x.ln(prec, nr, &mut cc);
    loop {
        let mut sum: BigFloat = BigFloat::from_f64(0.0, prec);
        for k in 0..((n-1)/2)+1 {
            sum = sum.add(&BigFloat::from_f64(1.0/(2.0*(k as f64) +1.0), prec), prec, nr);
        }
        let one = if (n-1) % 2 == 0 {1} else {-1};
        let lnxn = lnx.pow(&BigFloat::from_u64(n as u64,prec), prec, nr, &mut cc);
        nfact = nfact.mul(&BigFloat::from_u64(n, prec), prec, nr);
        let pow2 = BigFloat::from_f64(2.0, prec).pow(&BigFloat::from_u64(n-1, prec), prec, nr, &mut cc);
        sum = sum.mul( &BigFloat::from_i32(one, prec), prec, nr).mul(&lnxn, prec, nr).div(&nfact, prec, nr).div(&pow2, prec, nr);
        add = add.add(&sum, prec, nr);
        //println!("{:?}",sum.convert_to_radix(astro_float::Radix::Dec, astro_float::RoundingMode::None).ok());
        if sum.abs() < BigFloat::from_f64(1e-3, prec) {break}
        n += 1;
    }
    add = add.mul(&sqx, prec, nr);
    ret = ret.add(&add, prec, nr);
    return ret;
}

fn main_mersenne() {
    let args = Args::parse();

    let lo = args.from;
    let hi = args.to;
    let mut min_kn = args.min_span;
    let mut max_kn = args.max_span;
    let asc = !args.descending;
    let kk = args.power_2;
    let extra_tests = args.extra_tests;

    if args.span > 0 {
        min_kn = args.span;
        max_kn = args.span;
    }

    //let fmagic = if args.magic { magic} else {identity};
    let mpe51: Vec<u64> = vec![2,3,5,7,13,17,19,31,61,89,107,127,521,607,1279,2203,2281,3217,4253,4423,9689,9941,
                               11213,19937,21701,23209,44497,86243,110503,132049,216091,756839,859433,1257787,1398269,2976221,
                               3021377,6972593,13466917,20996011,24036583,25964951,30402457,32582657,37156667,
                               42643801,43112609,57885161,74207281,77232917,82589933];


    //let fmagic = if args.magic { magic} else {identity};
    let mut tests = 0;
    let mut prime_count = 0;
    let mut expected_tests = 0;
    for mi in args.from..args.to {
        for exp in
        (f64::floor(1.0 / 3.0 * mpe51[mi] as f64).to_u64().unwrap())..(f64::ceil(2.0 / 3.0 * mpe51[mi] as f64).to_u64().unwrap()) {
            let p = next(
                &BigUint::from(2_u64).pow(mpe51[mi]).sub(&BigUint::one()),
                &BigUint::from(exp),
                &BigUint::from(exp)
            );
            tests += 1;
            let is = is_prime(&p, None).probably();
            if is {
                let binary_digits = p.to_str_radix(2).len();
                let average_tests = (binary_digits as f64 * f64::ln(2.0)).ceil() as usize;
                prime_count += 1;
                expected_tests += average_tests;
                println!("i = {} e = {} {:?} {}", mi, exp, p, is);
                break;
            }
        }
    }
    eprintln!("Found {} primes using {} tests compared to {} expected tests. Speed-up {:.1}×.",
              prime_count, tests, expected_tests, (expected_tests as f64) / (tests as f64));
    return;
}
use num_traits::Float;

fn main() {
    let args = Args::parse();

    let lo = args.from;
    let hi = args.to;
    let mut min_kn = args.min_span;
    let mut max_kn = args.max_span;
    let asc = !args.descending;
    let kk = args.power_2;
    let extra_tests = args.extra_tests;

    if args.span > 0 {
        min_kn = args.span;
        max_kn = args.span;
    }
    let mut mods = vec![1_u64];

    let _lo = (lo + 1 - (lo %2)) as u64;
    let _hi = hi as u64;
    println!("{},{}",_lo,_hi);
    for k in (_lo.._hi) {
        mods.push(1_u64);
    }
    let bar = indicatif::ProgressBar::new((hi-2_usize) as u64);

    for k in (2_u64.._hi) {
        bar.inc(1);
        if k >= _lo && k%2 == 1{
            if mods[k as usize- _lo as usize] == k - 1 {
                println!("{} is prime", k);
            } else {
                //println!("{} is not prime", k);
            }
        }
        let mut i = 0;
        for p in (_lo.. _hi).step_by(2) {
            if mods[i] > 0 {
                mods[i] = mods[i].mulm(k, &p);
            }
            i+=2;
        }
    }
    bar.finish();
    return;
    //let nom = log_integral(&BigFloat::from_f64(2.0, 100)); //.convert_to_radix(astro_float::Radix::Dec, astro_float::RoundingMode::None).ok();
    let two = BigFloat::from_f64(2.0, 100);//BigUint::from(2_u64);
    let mut cc = astro_float::Consts::new().unwrap();
    const prec:usize = 80;
    for n in 1..30 {
        let dec = astro_float::Radix::Dec;
        let nr = astro_float::RoundingMode::None;
        let x = two.pow(&two.pow(&BigFloat::from_u64(n,prec), prec, nr, &mut cc), prec, nr, &mut cc);
        let numerator = log_integral(&x, prec).log2(prec, nr, &mut cc).log2(prec, nr, &mut cc);
        let (pos, digits, exp) = x.log2(prec, nr, &mut cc).convert_to_radix(dec, nr).unwrap();
        let prime = nth_prime_est(&BigUint::from_radix_be(&digits[0..(exp as usize+1)],10).unwrap()).unwrap().to_u64().unwrap();
        let denominator = BigFloat::from_u64(prime,prec).log2(prec, nr, &mut cc);
        let result = numerator.div(&denominator, prec, nr);
        println!("{}\t{:?}", n, result.convert_to_radix(dec, nr).ok());
    }
    return;

//let fmagic = if args.magic { magic} else {identity};
    let mpe51: Vec<u128> = vec![2,3,5,7,13,17,19,31,61,89,107,127,521,607,1279,2203,2281,3217,4253,4423,9689,9941,
                               11213,19937,21701,23209,44497,86243,110503,132049,216091,756839,859433,1257787,1398269,2976221,
                               3021377,6972593,13466917,20996011,24036583,25964951,30402457,32582657,37156667,
                               42643801,43112609,57885161,74207281,77232917,82589933];

    //let fmagic = if args.magic { magic} else {identity};
    let mut tests = 0;
    let mut prime_count = 0;
    let mut expected_tests = 0;
    for mi in args.from..args.to {
        let p = mpe51[mi];
        println!("{}\t{}\t{}", mi, p, is_mersenne_exponent(p));
    }
    return;
}

fn main_cosi() {
    let args = Args::parse();

    let lo = args.from;
    let hi = args.to;

    let mut now = Instant::now();
    for x in lo..hi {
        let mut a = BigUint::from(2_u64).pow(BigUint::from(nth_prime(x as u64))).sub(&BigUint::one());;
        a.mul_assign(&a.clone());
        a = next_prime(&a,None).unwrap();
        let mut q;
        let mut b = a.clone();
        let mut j = 0;
        loop {
            let mut got_prime = false;
            let mut k = 0;
            loop {
                b = next_prime(&b, None).unwrap();
                q = b.clone().mul(&b).add(a.clone().mul(&a)).div(BigUint::from(2_usize));
                k += 1;
                if !is_prime(&q, None).probably() {
                    q = next_prime(&q,None).unwrap();
                }
                //
                if is_prime(&q, None).probably()
                && is_prime(&q.clone().add(BigUint::from(2_usize)), None).probably(){
                    got_prime = true;
                    let decimal_digits = q.to_str_radix(10).len();
                    let mut score = (decimal_digits as f64) * (decimal_digits as f64).ln();
                    score *= score.ln();
                    let spm  = 60.0 * score / now.elapsed().as_secs_f64();
                    println!("{}\t{}\t{}\t{}\t{:0.2}\t{}\t{}\t{}", decimal_digits, x, j, k, spm.ln(), a, b, q);
                    now = Instant::now();
                    break;
                }
                if k >= args.power_2 {
                    break;
                }
            }
            if !got_prime {
                break;
            }
            j += 1;
            break;
            a = q.clone();
            b = a.clone();
        }
    }
    return;


    for x in lo..hi {
        let n = BigUint::from(x);
        let a = prev_prime(&n.sqrt(),None).unwrap();
        let b = n.sqrt();
        let c = n.clone();
        let d = n.clone().sqrt().add(BigUint::one());
        let e = next_prime(&n.sqrt(), None).unwrap();
        let t = a.clone().mul(&a).add(e.clone().mul(&e)).to_bigint().unwrap().sub(c.clone().to_bigint().unwrap().mul(BigInt::from(2_usize)));
        println!("{}, {}, sqrt({}), {}, {} => {}", a,b,c,d,e, t);
    }
    return;
    let mut min_kn = args.min_span;
    let mut max_kn = args.max_span;
    let asc = !args.descending;
    let kk = args.power_2;
    let extra_tests = args.extra_tests;

    if args.span > 0 {
        min_kn = args.span;
        max_kn = args.span;
    }

    let mut tests = 0;
    let mut prime_count = 0;
    let mut expected_tests = 0;
    let mut total_score = 0.0;
    let mut now = Instant::now();
    for k in args.from..args.to {
        for third in vec![false, true] {
        //for ii in (k/2_usize)..(k/2_usize+k/10_usize) {
            //eprintln!("{}",ii);
            //let res = big_two_twins(k, ii, (args.power_2 + 2) as usize);
            let res = big_fast_twins( k, third, (args.power_2 + 2) as usize);
            if res.1.0 && res.2.0 {
                let decimal_digits = res.1.1.to_str_radix(10).len();
                let mut score = (decimal_digits as f64) * (decimal_digits as f64).ln();
                score *= score.ln();
                let spm  = 60.0 * score / now.elapsed().as_secs_f64();
                let dpm = now.elapsed();
                total_score += score;
                prime_count += 1;
                println!("{:0.3}\t{:0.3}\t{:0.0?}\t{}\t{}\t{}\t{}\t{}_{}\t{}\t{}\t{}", score.ln(), spm.ln(), dpm, decimal_digits, res.0, third, res.3, res.1.0, res.2.0, 0/*ii*/, k, res.1.1);
                //break;
            }
        }
    }
    eprintln!("Found {} primes using {} tests compared to {} expected tests. Speed-up {:.1}×.",
              prime_count, tests, expected_tests, (expected_tests as f64)/(tests as f64));
    return;
    /*let mut indices = Vec::<(usize, BigUint)>::new(); // mi, power, den


    let mut a = Vec::<BigUint>::new();
    for p in primes(nth_prime(usize::max(args.divisors, hi+1) as u64)+1 as u64).iter() {
        a.push(BigUint::from(*p));
    }

    let mut tests = 0;
    let mut expected_tests = 0;

    let mut i = args.from;
    loop {
            let candidate_a:BigUint = a[i].clone();
            //let ei = candidate_a.to_bigint().unwrap().mul(216883_u64).add(403611441_u64).div(2088811_u64).add(1_u64);
            //if ei.clone().sub(i).abs() < BigInt::from(2_i64) {
                //eprintln!("fine err {:?}",ei.sub(i));
                indices.push((i, candidate_a));
            //} else {
                //eprintln!("bad err {:?}",ei.sub(i));
            //}
            i+=1;
        if i >= args.to {
            break;
        }
    }

    let mut probable_primes = indices.into_par_iter()
        .inspect(|(i, a)| {
            if args.debug {
                eprintln!("Testing p({})={}, 1/3 * (2^p({})+1).. ", i,a,i);
            }
        })
        .map(|(i, a)| {
            let mut mp = BigUint::from(2_u64).pow(&a).add(&BigUint::one()).div(BigUint::from(3_u64));
            if is_prime(&mp, None).probably() {
                let expected_tests = (mp.to_radix_le(2).len().to_f64().unwrap() * f64::ln(2.0)).ceil() as usize;
                (1, expected_tests, i, a.clone(), mp)//prime = np.clone();
            } else {
                (1, 0, i, a.clone(), BigUint::zero())
            }
        })
        .inspect(|(_tests, _expected, i, a,  p)| {
            if p > &BigUint::zero() && args.verbose {
                let binary_digits = p.to_str_radix(2).len();
                let decimal_digits = p.to_str_radix(10).len();
                eprintln!("{}\t{}\tp({})={}\t1/3 * (2^p({})+1)\t{:?}",
                          binary_digits, decimal_digits, i, a, i, p);
            } else if args.debug {
                if _tests > &0 {
                    eprintln!("Prime p({})={} =>  1/3 * (2^p({})+1) is composite", i,a,i,);
                }
            }
        })
        .collect::<Vec<(usize, usize, usize, BigUint, BigUint)>>();

    probable_primes.sort_by(|a,b|  {
        let ordering = a.4.partial_cmp(&b.4).unwrap();
        if !asc {
            ordering.reverse()
        } else {
            ordering
        }
    });

    let mut last_p = BigUint::from(1_usize);
    let mut prime_count = 0;
    let mut total_tests = 0;
    let mut expected_tests = 0;
    for (tests, _expected, i, a, p) in probable_primes {
        if p > BigUint::zero() && (!args.final_strict
            || is_prime(&p, Some(PrimalityTestConfig::strict())).probably()) {
            let binary_digits = p.to_str_radix(2).len();
            let average_tests = (binary_digits as f64 * f64::ln(2.0)).ceil() as usize;
            if p != last_p || args.duplicates {
                let decimal_digits = p.to_str_radix(10).len();
                println!("{}\t{}\t{}\t{}\t{}", binary_digits, decimal_digits, i, a, p);
                last_p = p.clone();
            }
            prime_count += 1;
            expected_tests += average_tests;
        }
        total_tests += tests;
    }
    eprintln!("Found {} primes using {} tests compared to {} expected tests. Speed-up {:.1}×.",
              prime_count, total_tests, expected_tests, (expected_tests as f64)/(total_tests as f64));
    return;
    return;

     */
    /*let mut tests = 0;
    let mut expected_tests = 0;
    let aa = vec![(1,2),(3,4),(7,8),(5,8),(1,8),(15,16),(3,8),(13,16),(9,16),(31,32),(25,32),(63,64),(17,32), (25,64)];
    let bb = vec![
        vec![(2,7),(3,11)],
        vec![(6,7)],
        vec![(8,9),(10,11),(14,15)],
        vec![(7,11)],
        vec![(2,15)],
        vec![(18,19), (24,25)],
        vec![(8,21)],
        vec![(22,27)],
        vec![(18,31)],
        vec![(32,33),(34,35),(73,75)],
        vec![(51,65)],
        vec![(74,75),(78,79),(98,99)],
        vec![(41,77)],
        vec![(32,81),(46,117),(56,143),(64,163)]
    ];
    for me in mpe51 {
        let mut candidatesVec<BigUint> = vec![];
        for (ia, &(a1, a2) in aa.iter().enumerate() {
            if
            let i =
            if is_prime(&a, None).probably() {
                for &b in bb[ia].iter() {
                    if is_prime(&b, None).probably() {
                        candidate = true;
                        ca = Some(b.clone());
                        //break;
                    }
                }
            }
            if candidate { break; }
        }
        if let Some(candidate_a) = ca {
            let mut mp = BigUint::from(2_u64).pow(candidate_a).sub(&BigUint::one());
            tests += 1;
            if is_prime(&mp, None).probably() {
                expected_tests += (mp.to_radix_le(2).len().to_f64().unwrap() * f64::ln(2.0)).ceil() as usize;
                println!("a =\t{}\tdigits =\t{}\tprime =\t{:?} ", candidate_a, mp.to_radix_le(10).len(), mp);
                //prime = np.clone();
            }
        }
    }

    eprintln!("{}/{} == {} speedup", expected_tests, tests, (expected_tests as f64)/(tests as f64));

    /*let mut tests = 0;
    let mut expected_tests = 0;
    for i in 0..args.to {
        let aa = vec![1+2*i,3+4*i,7+8*i,5+8*i,1+8*i,15+16*i,3+8*i,13+16*i,9+16*i,31+32*i,25+32*i,63+64*i, 17+32*i, 25+64*i];
        let bb = vec![
            vec![2+7*i,3+11*i],
            vec![6+7*i],
            vec![8+9*i, 10+11*i,14+15*i],
            vec![7+11*i],
            vec![2+15*i],
            vec![18+19*i, 24+25*i],
            vec![8+21*i],
            vec![22+27*i],
            vec![18+31*i],
            vec![32+33*i,34+35*i,73+75*i],
            vec![51+65*i],
            vec![74+75*i,78+79*i,98+99*i],
            vec![41+77*i],
            vec![32+81*i,46+117*i,56+143*i,64+163*i]
        ];
        let mut candidate = false;
        let mut ca = None;
        for (ia,&a) in aa.iter().enumerate() {
            if is_prime(&a, None).probably() {
                for &b in bb[ia].iter() {
                    if is_prime(&b, None).probably() {
                        candidate = true;
                        ca = Some(b.clone());
                        //break;
                    }
                }
            }
            if candidate { break; }
        }
        if let Some(candidate_a) = ca {
            let mut mp = BigUint::from(2_u64).pow(candidate_a).sub(&BigUint::one());
            tests += 1;
            if is_prime(&mp, None).probably() {
                expected_tests += (mp.to_radix_le(2).len().to_f64().unwrap() * f64::ln(2.0)).ceil() as usize;
                println!("a =\t{}\tdigits =\t{}\tprime =\t{:?} ", candidate_a, mp.to_radix_le(10).len(), mp);
                //prime = np.clone();
            }
        }
    }

    eprintln!("{}/{} == {} speedup", expected_tests, tests, (expected_tests as f64)/(tests as f64));*/
    return;
    */

    /*
    println!("{:?}", rev3(
        &BigUint::from(2_u64).pow(mpe51[17-1]).sub(&BigUint::one()),
        &BigUint::from(50_u64),
        (&BigUint::from(1_u64),&BigUint::from(32768_u64)),
        (&BigUint::from(1_u64),&BigUint::from(32768_u64))
    ));
    println!("{:?}", rev3(
        &BigUint::from(17_u64),
        &BigUint::from(4_u64),
        (&BigUint::from(3_u64),&BigUint::from(8_u64)),
        (&BigUint::from(1_u64),&BigUint::from(2_u64))
    ));
    return;
*/
    /*let mut a = Vec::<BigUint>::new();
    for p in primes(nth_prime(usize::max(args.divisors, hi+1) as u64)+1 as u64).iter() {
        a.push(BigUint::from(*p));
    }
    let mut dna = Vec::<u8>::new();
    let mut last_p = &BigUint::one();
    let two = BigUint::from(2_u64);
    for p in &a {
        let diff = p.sub(last_p);
        let arity = diff.div(&two).rem(&two).to_u8().unwrap();
        //dna.push(rand::random::<bool>());
        dna.push(arity);
        last_p = p;
    }
    let mut indices = Vec::<(usize, usize, i64, bool)>::new();

    if args.diagonal {
        let mut ii = magic(lo);
        let mut jj = magic(ii);
        loop  {
            while ii < hi && dna[ii]>0 { ii+=1};
            while jj < hi && dna[jj]>0 { jj+=1};
            if jj >= hi {
                break;
            }
            if jj - ii >= min_kn {
                indices.push((ii, jj, kk, extra_tests));
            }
            ii += 1;
            jj = magic(ii);

        }
    } else {
        /*for kn in min_kn..usize::min(max_kn, hi - lo) + 1 {
            for i in lo..hi - kn + 1 {
                let ii = i;
                let jj = i + kn;
                if dna[ii]>0 && dna[jj]>0 {
                    indices.push((ii, jj, kk, extra_tests));
                }
            }
        }*/
        for i in lo..hi {
            indices.push((i, 0, kk, extra_tests));
        }
    }
    if asc {
        indices.sort_by(|b, a| (b.0, b.1 - b.0).partial_cmp(&(a.0, a.1 - a.0)).unwrap());
    } else {
        indices.sort_by(|a, b| (b.0, b.1 - b.0).partial_cmp(&(a.0, a.1 - a.0)).unwrap());
    };

    eprintln!("number of decimal digits bounds = ({}, {})",
              ((usize::min(min_kn, hi-lo)) as f64 * f64::log10(2.0)).ceil(),
              ((usize::min(max_kn, hi-lo)) as f64 * f64::log10(2.0)).ceil());

    let mut probable_primes = indices.into_par_iter()
    .inspect(|(i, j, k,_extra)| {
        if args.debug {
            eprintln!("Testing span p({},{},{})... ", i, j, k);
        }
    })
        .map(|(i, j, k, extra)| {
        let mut b = Vec::<(usize, String, BigUint, Vec<BigUint>)>::new();
        //let tests0 = bigprime(&a, &dna, i, j, k, &mut b, extra);
        let tests0 = mersenne_plus_2_third(&a, &dna, i, j, k, &mut b, extra);
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
            eprintln!("{}\t{}\t|{}|p({},{},{})\t{}\t{:?}",
                     binary_digits, decimal_digits, description, i,j, k, p, divisors);
        } else if args.debug {
            if _tests > &0 {
                eprintln!("Span prime p({},{},{}) is composite", i, j, k);
            }  else {
                eprintln!("Span p({},{},{}) span starts or ends with zero", i, j, k);
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
    let mut last_p = BigUint::from(1_usize);
    let mut prime_count = 0;
    let mut total_tests = 0;
    let mut expected_tests = 0;
    for (i, j, k, tests, description, p, divisors) in probable_primes {
        if p > BigUint::zero() && (!args.final_strict
            || is_prime(&p, Some(PrimalityTestConfig::strict())).probably()) {
            //numbers_tested_total += tests;
            let binary_digits = p.to_str_radix(2).len();
            let average_tests = (binary_digits as f64 * f64::ln(2.0)).ceil() as usize;
            if p != last_p || args.duplicates {
                let decimal_digits = p.to_str_radix(10).len();
                println!("{}\t{}\t|{}|p({},{},{})\t{}\t{:?}", binary_digits, decimal_digits, description, i, j, k, p, divisors);
                last_p = p.clone();
            }
            prime_count += 1;
            expected_tests += average_tests;
        }
        total_tests += tests;
    }
    eprintln!("Found {} primes using {} tests compared to {} expected tests. Speed-up {:.1}×.",
              prime_count, total_tests, expected_tests, (expected_tests as f64)/(total_tests as f64));
    return;

 */
}
