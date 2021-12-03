use std::io;
use std::io::prelude::*;

enum Move {
    Down(i64),
    Up(i64),
    Forward(i64),
}

fn parse_move(s: &str) -> Result<Move, String> {
    let words: Vec<_> = s.split(' ').collect();
    if words.len() != 2 {
        Err(format!("expected 2 words, got {}: {}", words.len(), s))
    } else {
        match words[1].parse::<i64>() {
            Err(e) => Err(format!("expected a number, got {}: {}", words[1], e)),
            Ok(n) => match words[0] {
                "down" => Ok(Move::Down(n)),
                "up" => Ok(Move::Up(n)),
                "forward" => Ok(Move::Forward(n)),
                _ => Err(format!("expected up/down/forward, got {}", words[0])),
            },
        }
    }
}

fn part1(moves: &[Move]) {
    fn move_sub(pos: (i64, i64), m: &Move) -> (i64, i64) {
        let (h, v) = pos;
        match m {
            Move::Down(x) => (h, v + x),
            Move::Up(x) => (h, v - x),
            Move::Forward(x) => (h + x, v),
        }
    }

    println!("Day 02 part 1: {}", {
        let (h, v) = moves.iter().fold((0, 0), move_sub);
        h * v
    });
}

fn part2(moves: &[Move]) {
    struct Pos {
        aim: i64,
        h: i64,
        v: i64,
    }
    fn move_sub(pos: Pos, m: &Move) -> Pos {
        match m {
            Move::Down(x) => Pos {
                aim: pos.aim + x,
                ..pos
            },
            Move::Up(x) => Pos {
                aim: pos.aim - x,
                ..pos
            },
            Move::Forward(x) => Pos {
                h: pos.h + x,
                v: pos.v + pos.aim * x,
                ..pos
            },
        }
    }

    println!("Day 02 part 2: {}", {
        let end = moves.iter().fold(Pos { aim: 0, h: 0, v: 0 }, move_sub);
        end.h * end.v
    });
}

fn main() {
    let moves: Vec<Move> = io::BufReader::new(io::stdin())
        .lines()
        .map(|s| parse_move(&s.unwrap()).expect("valid input"))
        .collect();
    part1(&moves);
    part2(&moves);
}
