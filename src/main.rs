extern crate core;


use std::ops::{Add, AddAssign, Div, MulAssign, Shl, Sub, SubAssign};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};
use num_bigint::BigUint;
use num_traits::identities::Zero;

use num_prime::nt_funcs::{is_prime, next_prime, prev_prime};
use num_traits::{Pow, ToPrimitive};
use rayon::prelude::*;

use clap::Parser;
use indicatif::{ParallelProgressIterator, ProgressBar, ProgressStyle};

/// Program to generate big (strongly probable) twin primes fast.

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Maximum steps for each power
    #[clap(short, long, value_parser, default_value_t = 3)]
    max_steps: usize,

    /// Immediately output probable primes to stdout, possibly duplicated
    #[clap(long, value_parser, default_value_t = false)]
    verbose: bool,

    /// Power from
    #[clap()]
    from: Option<usize>,

    /// Power to
    #[clap()]
    to: Option<usize>,
}

fn _big_two_twins(k: usize, ii:usize,max: usize) -> (usize, (bool, BigUint), (bool, BigUint)) {
     let mut p = BigUint::from(2_usize).pow(k+1_usize);//BigUint::from_radix_be(&binary_b, 2).unwrap();
    for i in ii..(k+1) {
        let a = BigUint::from(2_usize).pow(k-i);//_radix_be(&binary_a, 2).unwrap();
        p.sub_assign(a);
    }
    let mut steps = 0;
    let mut q;
    let mut pq;
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

fn _big_zero_twins(odd_w: BigUint, zero_count: usize) -> ((bool, BigUint), (bool, BigUint)) {
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

fn big_fast_twins(k: usize, third: bool, max_steps: usize) -> (isize, (bool, BigUint), (bool, BigUint), BigUint, usize) {
    let a = BigUint::from(1_usize).shl(k);
    let b = BigUint::from(1_usize).shl(k+1);
    let p00 = a.clone().add(
         if third {
            b.sub(&a)
            .div(BigUint::from(3_usize))
        } else {
        BigUint::zero()});
    let pl0 = p00.clone();
    let pr0 = p00.clone();
    let mut steps = 0;
    let mut pl = pl0.clone();
    let mut pr = pr0.clone();
    let mut ql: BigUint = pl0.clone();
    let mut qr: BigUint = pr0.clone();
    let mut prime4l = false;
    let mut prime4r = false;

    let mut tests = 2;
    if !is_prime(&pl, None).probably() {
        pl = prev_prime(&pl, None).unwrap();
    }
    if !is_prime(&pr, None).probably() {
        pr = next_prime(&pr, None).unwrap();
    }

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
        tests += 2;
    }

    if prime4r {
        return (steps as isize, (true, pr.clone()), (prime4r, qr), pr.sub(&p00), tests);
    }
    return (-(steps as isize), (true, pl.clone()), (prime4l, ql), p00.sub(&pl), tests);
}

fn _big_fastest_twins(k: usize, third: bool) -> (isize, (bool, BigUint), (bool, BigUint), BigUint) {
    let a = BigUint::from(2_usize).pow(k);
    let b = BigUint::from(2_usize).pow(k+1);
    let p00 = a.clone().add(
        if third {
            b.sub(&a)
                .div(BigUint::from(3_usize))
        } else {
            BigUint::zero()});
    let pl0 = p00.clone();
    let steps = 0;
    let pl = pl0.clone();//.add(BigUint::one());
    let mut ql: BigUint = pl0.clone();
    let mut prime4l = false;
    if is_prime(&pl, None).probably() {
        ql = pl.clone().add(BigUint::from(2_usize));
        prime4l = is_prime(&ql, None).probably();
    }
    return (-(steps as isize), (true, pl.clone()), (prime4l, ql), pl.sub(&pl0));
}

fn main() {
    let args = Args::parse();

    let base_from = args.from.unwrap_or(2).max(2);
    let base_to = args.to.unwrap_or(100);

    let start = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();

    let mut prime_count = 0;
    let mut expected_tests = 0;
    let mut total_score = 0.0;
    let mut tests = 0;
    let mut indices = vec![];

    for k in base_from..base_to {
        for third in vec![false, true] {
            indices.push((k, third));
        }
    }

    let pbr = ProgressBar::new((2*(base_to-base_from)).to_u64().unwrap()).with_style(
        ProgressStyle::with_template(
            "{msg} {wide_bar} {pos}/{len} {elapsed}/{duration} [{binary_bytes_per_sec}]",
        ).unwrap(),
    );

    let running = Arc::new(AtomicBool::new(true));
    let r = running.clone();

    ctrlc::set_handler(move || {
        r.store(false, Ordering::SeqCst);
        eprintln!("Ctrl+C handler called!");
    }).expect("Error setting Ctrl-C handler");

    let mut ret = indices.into_par_iter()
    .progress_with(pbr.clone())
    .flat_map(|(k, third)| {
        if running.load(Ordering::SeqCst) {
            vec![(k, third, big_fast_twins(k, third, args.max_steps.max(1)))]
        } else {
            vec![]
        }
    })
    .inspect(|(k, third, res)| {
        let decimal_digits = res.1.1.to_str_radix(10).len();
        if args.verbose && res.1.0 && res.2.0 {
            println!("{}\t{}\t{}\t{}\t{}_{}\t{}\t{}\t{}", decimal_digits, res.0, third, res.3, res.1.0, res.2.0, 0, k, res.1.1);
            pbr.set_message(format!("Found twins! {} digits", decimal_digits));
        }
    }).collect::<Vec<(usize, bool, (isize, (bool, BigUint), (bool, BigUint), BigUint, usize))>>();

    pbr.finish_and_clear();

    ret.sort_by(|(_k1, _t1, a), (_k2, _t2, b) | a.1.1.partial_cmp(&b.1.1).unwrap());

    println!("decimal_digits\tsteps\tthird\tstep_diff\tprimality\t0\tpower\ttwin_prime");
    for (k, third, res) in ret {
        if res.1.0 && res.2.0 {
            let decimal_digits = res.1.1.to_str_radix(10).len();
            let binary_digits = res.1.1.to_str_radix(2).len();
            let average_tests = (binary_digits as f64 * f64::ln(2.0)).ceil() as usize;
            prime_count += 2;
            expected_tests += 2 * average_tests;
            total_score += 2.0 * (average_tests as f64).powf(3.0) * (average_tests as f64).ln();
            println!("{}\t{}\t{}\t{}\t{}_{}\t{}\t{}\t{}", decimal_digits, res.0, third, res.3, res.1.0, res.2.0, 0, k, res.1.1);
        }
        tests += res.4;
    }
    eprintln!("Found {} primes using {} tests compared to {} expected tests. Speed-up {:.1}×.",
              prime_count, tests, expected_tests, (expected_tests as f64)/(tests as f64));

    let end = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();

    eprintln!("Time: {:?}  Log Score: {:.4}  Log Score per sec: {:.4}", end - start, total_score.ln(), (total_score / (end -start).as_secs_f64()).ln());

}
