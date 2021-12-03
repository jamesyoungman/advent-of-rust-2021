use std::cmp::Ordering;
use std::io;
use std::io::prelude::*;

fn parse_binary(s: &str) -> i32 {
    i32::from_str_radix(s, 2).expect("valid input")
}

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
    let result: Option<bool> = match count1.cmp(&count0) {
        Ordering::Greater => Some(true),
        Ordering::Less => Some(false),
        Ordering::Equal => None,
    };
    //println!(
    //	"most_popular: bit position {}: count of 1s: {}, count of 0s: {}, most popular: {:?}",
    //	bitpos,
    //	count1,
    //	count0,
    //	result
    //);
    result
}

fn part1(bitwidth: i32, readings: &[i32]) {
    let mut gamma = 0;
    for bitpos in 0..bitwidth {
        if most_popular(bitwidth, bitpos, readings) == Some(true) {
            gamma |= mask(bitwidth, bitpos);
        }
    }
    //println!("Part 1: gamma={:b}={}", gamma, gamma);
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
        //println!("filter: bit pos {}: retaining readings with value {}",
        //	 bitpos, if expected { 1 } else { 0 });
        let want = |x: &i32| {
            let mask = mask(bitwidth, bitpos);
            let got = x & mask == mask;
            expected == got
        };
        //for n in &remaining {
        //    println!("before filtering: {:05b}", n);
        //}
        remaining.retain(want);
        //for n in &remaining {
        //    println!("after filtering: retained: {:05b}", n);
        //}
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
