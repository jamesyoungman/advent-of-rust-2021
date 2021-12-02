use std::io;
use std::io::prelude::*;

fn count_increases(values: &[u64]) -> usize {
    values.windows(2).filter(|w| w[1] > w[0]).count()
}

fn main() {
    let depths: Vec<u64> = io::BufReader::new(io::stdin())
        .lines()
        .map(|s| s.unwrap().parse::<u64>().unwrap())
        .collect();
    println!("Day 01 part 1: {}", count_increases(&depths));

    let sums: Vec<u64> = depths.windows(3).map(|w| w.iter().sum()).collect();
    println!("Day 01 part 2: {}", count_increases(&sums));
}
