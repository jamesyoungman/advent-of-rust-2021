use std::io;
use std::io::prelude::*;


fn generation(current: Vec<u32>) -> Vec<u32> {
    let births = current.iter().filter(|&n| *n == 0).count();
    let nextlen = current.len() + births;
    let mut next: Vec<u32> = Vec::with_capacity(nextlen);
    for n in current {
	next.push(match n {
	    0 => 6,
	    _ => n - 1,
	});
    }
    next.resize(nextlen, 8);
    next
}

fn show(day: usize, population: &[u32]) {
    println!(
	"After {:2} {}: {} (total {} fish)",
	day,
	if day == 1 { "day" } else { "days" },
	population.iter()
	    .map(u32::to_string)
	    .collect::<Vec<String>>()
	    .join(","),
	population.iter().count(),
    );
}

fn compute(mut population: Vec<u32>,
	   days: usize) -> usize {
    for day in 1..=days {
	population = generation(population);
	if day < 19 {
	    show(day, &population);
	}
    }
    population.len()
}

fn part1(population: Vec<u32>) {
    const DAYS: usize = 80;
    println!(
	"Day 6 part 1: after {} days, total population is {}",
	DAYS,
	compute(population, DAYS),
    );
}

fn main() {
    let first_line = match io::BufReader::new(io::stdin())
        .lines()
	.next()
        .map(|thing| thing.unwrap()) {
	    Some(line) => line,
	    None => {
		panic!("empty input");
	    }
	};
    let population: Vec<u32> = match first_line.split(',')
	.map(|s| s.parse::<u32>())
	.collect() {
	    Err(e) => {
		panic!("failed to parse integer in {}: {}", first_line, e);
	    }
	    Ok(items) => items,
	};
    part1(population.clone());
}
