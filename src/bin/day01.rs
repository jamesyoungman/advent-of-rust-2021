use std::io;
use std::io::prelude::*;

fn main() {
    let depths: Vec<u64> = io::BufReader::new(io::stdin()).lines()
    	.map(|s| s.unwrap().parse::<u64>().unwrap())
	.collect();
    let increases = depths.windows(2)
	.filter(|w| w[1] > w[0])
	.count();
    println!("Day 01 part 1: {}", increases);

    let sums: Vec<u64> = depths.windows(3)
	.map(|w| w.iter().sum())
	.collect();
    let increases = sums.windows(2)
	.filter(|w| w[1] > w[0])
	.count();
    println!("Day 01 part 2: {}", increases);
}
