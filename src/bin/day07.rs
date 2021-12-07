use std::io;
use std::io::prelude::*;

fn inorder(from: usize, to: usize) -> (usize, usize) {
    if from > to {
        (to, from)
    } else {
        (from, to)
    }
}

fn cost_of_move_part1(from: usize, to: usize) -> usize {
    let (from, to) = inorder(from, to);
    to - from
}

fn sum_of_values(first: usize, last: usize) -> usize {
    let n = last - first + 1;
    (n * (first + last)) / 2
}

fn cost_of_move_part2(from: usize, to: usize) -> usize {
    let (from, to) = inorder(from, to);
    sum_of_values(0, to - from)
}

#[test]
fn test_cost_of_move_part2() {
    assert_eq!(cost_of_move_part2(1, 1), 0);
    assert_eq!(cost_of_move_part2(2, 2), 0);
    assert_eq!(cost_of_move_part2(1, 2), 1);
    assert_eq!(cost_of_move_part2(2, 3), 1);
    assert_eq!(cost_of_move_part2(1, 3), 1 + 2);
    assert_eq!(cost_of_move_part2(1, 4), 1 + 2 + 3);
}

fn cost_of_dest(
    dest: usize,
    positions: &[usize],
    cost_of_move: fn(usize, usize) -> usize,
) -> usize {
    positions.iter().map(|pos| cost_of_move(*pos, dest)).sum()
}

fn min_dest(
    positions: &[usize],
    cost_of_move: fn(usize, usize) -> usize,
) -> Option<(usize, usize)> {
    let min_pos = *positions.iter().min().unwrap();
    let max_pos = *positions.iter().max().unwrap();

    let mut best: Option<(usize, usize)> = None;
    for pos in min_pos..=max_pos {
        let cost = cost_of_dest(pos, positions, cost_of_move);
        best = match best {
            None => Some((pos, cost)),
            Some((_, best_cost)) => {
                if best_cost > cost {
                    Some((pos, cost))
                } else {
                    best
                }
            }
        };
    }
    best
}

fn main() {
    let first_line = match io::BufReader::new(io::stdin())
        .lines()
        .next()
        .map(|thing| thing.unwrap())
    {
        Some(line) => line,
        None => {
            panic!("empty input");
        }
    };
    let positions: Vec<usize> = match first_line.split(',').map(|s| s.parse::<usize>()).collect() {
        Err(e) => {
            panic!("failed to parse integer in {}: {}", first_line, e);
        }
        Ok(items) => items,
    };
    if let Some((best_pos, cost)) = min_dest(&positions, cost_of_move_part1) {
        println!("Day 7 part 1: dest {} costs {}", best_pos, cost);
    } else {
        println!("No submarines.  Nothing to do.");
    }
    if let Some((best_pos, cost)) = min_dest(&positions, cost_of_move_part2) {
        println!("Day 7 part 2: dest {} costs {}", best_pos, cost);
    } else {
        println!("No submarines.  Nothing to do.");
    }
}
