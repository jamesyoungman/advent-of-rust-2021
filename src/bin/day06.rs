use std::io;
use std::io::prelude::*;

#[derive(Debug)]
struct School {
    population_by_days: [usize; 9]
}

impl School {
    fn new(counters: &[u8]) -> School {
	let mut pop: [usize; 9] = [0; 9];
	for counter in counters {
	    pop[*counter as usize] += 1;
	}
	School {
	    population_by_days: pop,
	}
    }

    fn a_day_passes(&mut self) {
	let births = self.population_by_days[0];
	self.population_by_days[0] = self.population_by_days[1];
	self.population_by_days[1] = self.population_by_days[2];
	self.population_by_days[2] = self.population_by_days[3];
	self.population_by_days[3] = self.population_by_days[4];
	self.population_by_days[4] = self.population_by_days[5];
	self.population_by_days[5] = self.population_by_days[6];
	self.population_by_days[6] = self.population_by_days[7] + births;
	self.population_by_days[7] = self.population_by_days[8];
	self.population_by_days[8] = births;
    }

    fn compute(&mut self, days: usize) -> usize {
	for _day in 1..=days {
	    self.a_day_passes();
	}
	self.fish_count()
    }

    fn fish_count(&self) -> usize {
	self.population_by_days.iter().sum()
    }
}

fn part1(population: &[u8]) {
    const DAYS: usize = 80;
    let mut school = School::new(population);
    println!(
	"Day 6 part 1: after {} days, total population is {}",
	DAYS,
	school.compute(DAYS),
    );
}

fn part2(population: &[u8]) {
    const DAYS: usize = 256;
    let mut school = School::new(population);
    println!(
	"Day 6 part 2: after {} days, total population is {}",
	DAYS,
	school.compute(DAYS),
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
    let population: Vec<u8> = match first_line.split(',')
	.map(|s| s.parse::<u8>())
	.collect() {
	    Err(e) => {
		panic!("failed to parse integer in {}: {}", first_line, e);
	    }
	    Ok(items) => items,
	};
    part1(&population);
    part2(&population);
}
