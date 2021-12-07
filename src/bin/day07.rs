use std::io;
use std::io::prelude::*;

fn cost_of_move(from: usize, to: usize) -> usize {
    if from > to {
	from - to
    } else {
	to - from
    }
}

fn cost_of_dest(
    dest: usize,
    positions: &[usize]
) -> usize {
    positions.iter()
	.map(|pos| cost_of_move(*pos, dest))
	.sum()
}

fn min_dest(
    positions: &[usize]
) -> Option<(usize, usize)> {
    let min_pos = *positions.iter().min().unwrap();
    let max_pos = *positions.iter().max().unwrap();

    let mut best: Option<(usize, usize)> = None;
    for pos in min_pos..=max_pos {
	let cost = cost_of_dest(pos, positions);
	best = match best {
	    None => Some((pos, cost)),
	    Some((_, best_cost)) => if best_cost > cost {
		Some((pos, cost))
	    } else {
		best
	    }
	};
    }
    best
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
    let positions: Vec<usize> = match first_line.split(',')
	.map(|s| s.parse::<usize>())
	.collect() {
	    Err(e) => {
		panic!("failed to parse integer in {}: {}", first_line, e);
	    }
	    Ok(items) => items,
	};
    if let Some((best_pos, cost)) = min_dest(&positions) {
	println!("Day 7 part 1: dest {} costs {}", best_pos, cost);
    } else {
	println!("No submarines.  Nothing to do.");
    }
}
