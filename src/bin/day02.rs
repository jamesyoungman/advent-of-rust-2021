use std::io;
use std::io::prelude::*;

enum Move {
    Down(i32),
    Up(i32),
    Forward(i32)
}

fn parse_move(s: &str) -> Result<Move, String> {
    let words: Vec<_> = s.split(" ").collect();
    if words.len() != 2 {
	Err(format!("expected 2 words, got {}: {}", words.len(), s))
    } else {
	match words[1].parse::<i32>() {
	    Err(e) => Err(format!("expected a number, got {}: {}", words[1], e)),
	    Ok(n) => {
		match words[0] {
		    "down" => Ok(Move::Down(n)),
		    "up" => Ok(Move::Up(n)),
		    "forward" => Ok(Move::Forward(n)),
		    _ => Err(format!("expected up/down/forward, got {}", words[0])),
		}
	    }
	}
    }
}

fn move_sub(pos: (i32, i32), m: &Move) -> (i32, i32) {
    let (h, v) = pos;
    match m {
	Move::Down(n) => (h, v + n),
	Move::Up(n) => (h, v - n),
	Move::Forward(n) => (h + n, v),
    }
}

fn main() {
    let moves: Vec<Move> = io::BufReader::new(io::stdin()).lines()
    	.map(|s| parse_move(&s.unwrap()).expect("valid input"))
	.collect();

    let start = (0_i32, 0_i32);
    let finish = moves.iter().fold(start, |acc, this_move| move_sub(acc, this_move));
    println!("Day 02 part 1: {}", finish.0 * finish.1);
}
