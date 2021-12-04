use std::cmp::Ordering;
use std::io;
use std::io::prelude::*;

fn parse_binary(s: &str) -> i32 {
    i32::from_str_radix(s, 2).expect("valid input")
}

// The instructions number bits starting from the left.  That is, the
// most significant bit.
fn mask(bitwidth: i32, bitpos: i32) -> i32 {
    1 << (bitwidth - bitpos - 1)
}

fn most_popular(bitwidth: i32, bitpos: i32, readings: &[i32]) -> Option<bool> {
    let mask: i32 = mask(bitwidth, bitpos);
    let mut count1: usize = 0;
    for n in readings {
        if (n & mask) == mask {
            count1 += 1
        }
    }
    let count0 = readings.len() - count1;
    match count1.cmp(&count0) {
        Ordering::Greater => Some(true), // 1 is more popular than 0
        Ordering::Less => Some(false),   // 0 is more popular than 1
        Ordering::Equal => None,         // equally popular
    }
}

fn part1(bitwidth: i32, readings: &[i32]) {
    let mut gamma = 0;
    for bitpos in 0..bitwidth {
        if most_popular(bitwidth, bitpos, readings) == Some(true) {
            gamma |= mask(bitwidth, bitpos);
        }
    }
    let all_bits: i32 = (1 << bitwidth) - 1;
    let epsilon = (!gamma) & all_bits;
    println!("Part 1: {}*{} = {}", gamma, epsilon, gamma * epsilon);
}

fn filter(bitwidth: i32, readings: &[i32], retain_most_popular: bool) -> i32 {
    let mut remaining = Vec::from(readings);

    for bitpos in 0..bitwidth {
        let most_popular = most_popular(bitwidth, bitpos, &remaining);
        let expected = if retain_most_popular {
            match most_popular {
                Some(b) => b,
                None => retain_most_popular,
            }
        } else {
            match most_popular {
                Some(b) => !b,
                None => retain_most_popular,
            }
        };
        let mask = mask(bitwidth, bitpos);
        let want = |x: &i32| {
            let got = x & mask == mask;
            expected == got
        };
        remaining.retain(want);
        if remaining.len() == 1 {
            break;
        }
    }
    remaining[0]
}

fn part2(bitwidth: i32, readings: &[i32]) {
    let oxygen_generator_reading = filter(bitwidth, readings, true);
    let co2_scrubber_reading = filter(bitwidth, readings, false);
    println!(
        "Day 3 part 2: {}*{} = {}",
        oxygen_generator_reading,
        co2_scrubber_reading,
        oxygen_generator_reading * co2_scrubber_reading,
    );
}

fn main() {
    let lines: Vec<String> = io::BufReader::new(io::stdin())
        .lines()
        .map(|line| line.unwrap())
        .collect();
    let bitwidth = lines[0].len() as i32;
    let readings: Vec<i32> = lines.iter().map(|line| parse_binary(line)).collect();
    part1(bitwidth, &readings);
    part2(bitwidth, &readings);
}
