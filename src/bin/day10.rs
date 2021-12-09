use std::io;
use std::io::prelude::*;


fn part1(_lines: &[String]) {
}

fn part2(_lines: &[String]) {
}

fn main() {
    let lines: Vec<String> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .collect();

    part1(&lines);
    part2(&lines);
}
