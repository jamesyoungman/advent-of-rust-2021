use std::io;
use std::io::prelude::*;

fn find_nonmatching_helper(mut s: String) -> String {
    loop {
        let mut changed = false;
        for pair in ["()", "[]", "{}", "<>"] {
            let snext = s.replace(pair, "");
            //println!("replacing {} in {} -> {}", pair, s, snext);
            if snext.len() < s.len() {
                changed = true;
                s = snext;
            }
        }
        if !changed {
            break;
        }
    }
    s
}

fn find_nonmatching(s: &str) -> Option<char> {
    let not_matched = find_nonmatching_helper(s.to_string());
    for ch in not_matched.chars() {
        match ch {
            ')' | ']' | '}' | '>' => {
                return Some(ch);
            }
            _ => (),
        }
    }
    None
}

fn syntax_error_score(s: &str) -> u32 {
    if let Some(bad) = find_nonmatching(s) {
        match bad {
            ')' => 3,
            ']' => 57,
            '}' => 1197,
            '>' => 25137,
            _ => 0,
        }
    } else {
        0
    }
}

#[test]
fn test_find_nonmatching() {
    assert_eq!(None, find_nonmatching(""));
    assert_eq!(None, find_nonmatching("()"));
    assert_eq!(None, find_nonmatching("[]"));
    assert_eq!(None, find_nonmatching("{}"));
    assert_eq!(None, find_nonmatching("<>"));
    assert_eq!(None, find_nonmatching("(())"));
    assert_eq!(None, find_nonmatching("(<>)"));
    assert_eq!(None, find_nonmatching("<([])>"));
    assert_eq!(Some(']'), find_nonmatching("(]"));
    assert_eq!(Some('}'), find_nonmatching("<<}"));
}

fn part1(lines: &[String]) {
    let total_score: u32 = lines.iter().map(|line| syntax_error_score(&line)).sum();
    println!("Day 10 part 1: {}", total_score);
}

fn part2(_lines: &[String]) {}

fn main() {
    let lines: Vec<String> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .collect();

    part1(&lines);
    part2(&lines);
}
