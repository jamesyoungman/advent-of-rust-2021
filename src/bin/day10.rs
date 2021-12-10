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

fn completing_chars_helper(mut s: String) -> Result<String, ()> {
    let mut result: String = String::new();
    loop {
        //println!("completing_chars_helper: top of loop: s={}", s);
        let not_matched = find_nonmatching_helper(s.clone());
        if not_matched.is_empty() {
            break;
        }
        let mut changed = false;
        for (open, close) in [('(', ')'), ('[', ']'), ('{', '}'), ('<', '>')] {
            if let Some(_) = not_matched.strip_suffix(close) {
                return Err(()); // Syntax error
            }
            if let Some(head) = not_matched.strip_suffix(open) {
                result.push(close);
                s = head.to_string();
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    Ok(result)
}

fn completing_chars(s: &str) -> Result<String, ()> {
    completing_chars_helper(s.to_string())
}

#[test]
fn test_completing_chars() {
    assert_eq!(Ok("".to_string()), completing_chars(""));
    assert_eq!(Ok("".to_string()), completing_chars("()"));
    assert_eq!(Ok("".to_string()), completing_chars("[{}]"));
    assert_eq!(Ok("]".to_string()), completing_chars("[{}"));
    assert_eq!(Ok("]".to_string()), completing_chars("["));
    assert_eq!(Ok("]]".to_string()), completing_chars("[["));

    // syntax error cannot be completed
    assert_eq!(Err(()), completing_chars("[)"));
}

fn autocomplete_score(s: &str) -> Option<u64> {
    if let Ok(needed) = completing_chars(s) {
        let mut score: u64 = 0;
        for ch in needed.chars() {
            let n = match ch {
                ')' => 1,
                ']' => 2,
                '}' => 3,
                '>' => 4,
                _ => 0,
            };
            score = score * 5 + n;
        }
        println!(
            "completing string for {} is {} with score {}",
            s, needed, score
        );
        Some(score)
    } else {
        None
    }
}

fn part1(lines: &[String]) {
    let total_score: u32 = lines.iter().map(|line| syntax_error_score(&line)).sum();
    println!("Day 10 part 1: {}", total_score);
}

fn part2(lines: &[String]) {
    let mut scores: Vec<u64> = lines
        .iter()
        .filter_map(|line| autocomplete_score(line))
        .collect();
    scores.sort();
    let middle_score = scores[scores.len() / 2];
    println!("Day 10 part 2: {}", middle_score);
}

fn main() {
    let lines: Vec<String> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .collect();

    part1(&lines);
    part2(&lines);
}
