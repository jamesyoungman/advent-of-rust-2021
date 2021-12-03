use std::collections::BTreeMap;
use std::io;
use std::io::prelude::*;

fn parse_binary(s: &str) -> i32 {
    i32::from_str_radix(s, 2).expect("valid input")
}

fn count_bit_occupants(
    bitwidth: i32,
    mut h: BTreeMap<i32, usize>,
    n: &i32
) -> BTreeMap<i32, usize> {
    for bitpos in 0..bitwidth {
	let mask: i32 = 1 << bitpos;
	let value = n & mask == mask;
	if value {
	    *h.entry(bitpos as i32).or_insert(0) += 1
	}
    }
    h
}

fn part1(
    bitwidth: i32,
    readings: &Vec<i32>
) {
    let counts: BTreeMap<i32, usize> = readings.iter()
	.fold(BTreeMap::new(),
	      |acc, n| count_bit_occupants(bitwidth, acc, n));
    let mut gamma = 0;
    for bitpos in 0..bitwidth {
	let count1 = counts[&bitpos];
	//println!("part1: readings.len()={}, counts[{}]={}", readings.len(), bitpos, count1);
	let count0 = readings.len() - count1;
	if count1 > count0 {
	    println!("bit pos {}: most common: 1", bitpos);
	    gamma |= 1 << bitpos;
	} else {
	    println!("bit pos {}: most common: 0", bitpos);
	}
    }
    println!("Part 1: gamma={:b}={}", gamma, gamma);
    let mask: i32 = (1 << bitwidth) - 1;
    let epsilon = (!gamma) & mask;
    println!("Part 1: epsilon={:b}={}", epsilon, epsilon);
    println!("Part 1: gamma*epsilon={}", gamma*epsilon);

}


fn main() {
    let lines: Vec<String> = io::BufReader::new(io::stdin())
        .lines()
	.map(|line| line.unwrap())
	.collect();
    println!("[{}]", lines[0]);
    let bitwidth = lines[0].len() as i32;
    let readings: Vec<i32> =
	lines.iter()
        .map(|line| parse_binary(&line))
        .collect();
    part1(bitwidth, &readings);
}
