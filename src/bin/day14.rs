use std::collections::BTreeMap;
use std::collections::HashMap;
use std::io;
use std::io::prelude::*;

type Pair = (char, char);
type Rules = HashMap<Pair, char>;

fn apply_rules_once(
    input: &HashMap<Pair, usize>,
    rules: &HashMap<Pair, char>,
) -> HashMap<Pair, usize> {
    let mut output: HashMap<Pair, usize> = HashMap::new();

    for (pair, count) in input {
        match rules.get(pair) {
            Some(insertion) => {
                let (left, right) = pair;
                *output.entry((*left, *insertion)).or_insert(0) += *count;
                *output.entry((*insertion, *right)).or_insert(0) += *count;
                //println!(
                //    "apply_rules_once: using rule {}{}->{}, {}{}({}) -> {}{}({}) {}{}({})",
                //    left, right, insertion,
                //    left, right, count,
                //    left, insertion, output.get(&(*left, *insertion)).unwrap(),
                //    insertion, right, output.get(&(*insertion, *right)).unwrap(),
                //);
            }
            None => {
                println!("apply_rules_once: passthrough: {}{}", pair.0, pair.1);
                output.insert(*pair, *count);
            }
        }
    }
    output
}

fn str_to_hash(input: &str) -> HashMap<Pair, usize> {
    let mut result = HashMap::new();
    let v: Vec<char> = input.chars().collect();
    for w in v.windows(2) {
        let pair = (w[0], w[1]);
        *result.entry(pair).or_insert(0) += 1;
    }
    result
}

#[test]
fn test_str_to_hash() {
    let h = str_to_hash("NNCB");
    assert_eq!(h.get(&('N', 'N')), Some(&1));
    assert_eq!(h.get(&('N', 'C')), Some(&1));
    assert_eq!(h.get(&('C', 'B')), Some(&1));
    assert_eq!(h.len(), 3);
}

fn apply_rules(s: &str, count: usize, rules: &Rules) -> HashMap<Pair, usize> {
    let mut input = str_to_hash(s);
    for _iter in 0..count {
        input = apply_rules_once(&input, rules)
    }
    input
}

#[cfg(test)]
fn hash_to_vec(input: &HashMap<Pair, usize>) -> Vec<(Pair, usize)> {
    let mut result: Vec<(Pair, usize)> = Vec::with_capacity(input.len());
    for (pair, count) in input {
        result.push((*pair, *count));
    }
    result.sort();
    result
}

#[cfg(test)]
fn str_apply_rules_once(s: &str, rules: &Rules) -> Vec<(Pair, usize)> {
    println!("apply_rules_once: input={}", s);
    let mut v = hash_to_vec(&apply_rules_once(&str_to_hash(s), rules));
    v.sort();
    v
}

#[cfg(test)]
const SAMPLE_RULES: &str = concat!(
    "CH -> B\n",
    "HH -> N\n",
    "CB -> H\n",
    "NH -> C\n",
    "HB -> C\n",
    "HC -> B\n",
    "HN -> C\n",
    "NN -> C\n",
    "BH -> H\n",
    "NC -> B\n",
    "NB -> B\n",
    "BN -> B\n",
    "BB -> N\n",
    "BC -> B\n",
    "CC -> N\n",
    "CN -> C\n"
);

#[test]
fn test_apply_rule() {
    let rules: Rules = parse_rules(SAMPLE_RULES).expect("example should be valid");

    let expected = |s: &str| -> Vec<((char, char), usize)> { hash_to_vec(&str_to_hash(s)) };
    assert_eq!(str_apply_rules_once("NNCB", &rules), expected("NCNBCHB"));
    assert_eq!(
        str_apply_rules_once("NCNBCHB", &rules),
        expected("NBCCNBBBCBHCB")
    );
    assert_eq!(
        str_apply_rules_once("NBCCNBBBCBHCB", &rules),
        expected("NBBBCNCCNBBNBNBBCHBHHBCHB")
    );
    assert_eq!(
        str_apply_rules_once("NBBBCNCCNBBNBNBBCHBHHBCHB", &rules),
        expected("NBBNBNBBCCNBCNCCNBBNBBNBBBNBBNBBCBHCBHHNHCBBCBHCB")
    );
}

fn parse_rule(input: &str) -> Result<((char, char), char), String> {
    if let Some((left, right)) = input.split_once(" -> ") {
        let pair: Vec<char> = left.chars().collect();
        let insertion: Vec<char> = right.chars().collect();
        if let (&[first, second], &[insertion]) = (pair.as_slice(), insertion.as_slice()) {
            let input = (first, second);
            let rule = (input, insertion);
            return Ok(rule);
        }
    }
    Err(format!("unexpected input rule: {}", input))
}

#[test]
fn test_parse_rule() {
    assert_eq!(parse_rule("AB -> C"), Ok((('A', 'B'), 'C')));
    assert!(parse_rule("AB ->C").is_err());
    assert!(parse_rule("A B -> C").is_err());
    assert!(parse_rule("AB-> C").is_err());
    assert!(parse_rule("AB->C").is_err());
    assert!(parse_rule("AB C").is_err());
    assert!(parse_rule("A->C").is_err());
    assert!(parse_rule("AB -> ").is_err());
    assert!(parse_rule("-> C").is_err());
}

fn parse_rules(input: &str) -> Result<Rules, String> {
    let mut result: Rules = HashMap::new();
    for line in input.split_terminator('\n') {
        let (input, output) = parse_rule(line)?;
        result.insert(input, output);
    }
    Ok(result)
}

fn parse_input(input: &str) -> Result<(String, Rules), String> {
    match input.split_once("\n\n") {
        Some((template, tail)) => match parse_rules(tail) {
            Err(e) => Err(e),
            Ok(rules) => Ok((template.to_string(), rules)),
        },
        None => Err("missing blank line".to_string()),
    }
}

fn count_if_right_is_b(item: (&(char, char), &usize)) -> Option<usize> {
    match item {
        ((_, 'B'), count) => Some(*count),
        _ => None,
    }
}

fn count_frequencies(input: &HashMap<Pair, usize>) -> HashMap<char, usize> {
    let mut frequency_counts = HashMap::new();
    for ((left, _), count) in input.iter() {
        *frequency_counts.entry(*left).or_insert(0) += count;
    }
    frequency_counts.insert('B', input.iter().filter_map(count_if_right_is_b).sum());
    frequency_counts
}

fn chars_by_frequency(input: &HashMap<Pair, usize>) -> BTreeMap<usize, Vec<char>> {
    let mut result: BTreeMap<usize, Vec<char>> = BTreeMap::new();
    let histogram: HashMap<char, usize> = count_frequencies(input);
    for (ch, freq) in histogram {
        result.entry(freq).or_insert_with(Vec::new).push(ch);
    }
    result
}

fn highest_and_lowest_freq_after_n_iterations(
    template: &str,
    iterations: usize,
    rules: &Rules,
) -> (usize, usize) {
    let result: HashMap<Pair, usize> = apply_rules(template, iterations, rules);
    let chars_by_frequency: BTreeMap<usize, Vec<char>> = chars_by_frequency(&result);
    match (
        chars_by_frequency.iter().next(),
        chars_by_frequency.iter().rev().next(),
    ) {
        (Some((lowest_freq, _least_common)), Some((highest_freq, _most_common))) => {
            (*lowest_freq, *highest_freq)
        }
        _ => {
            panic!("not enough chars");
        }
    }
}

#[test]
fn test_highest_and_lowest_freq_after_n_iterations() {
    fn hl(input: &str, count: usize) -> (usize, usize) {
        let rules: Rules = parse_rules(SAMPLE_RULES).expect("example should be valid");
        highest_and_lowest_freq_after_n_iterations(input, count, &rules)
    }

    assert_eq!(hl("NNCB", 1), (1, 2));
    assert_eq!(hl("NNCB", 10), (161, 1749));
}

fn solve(template: &str, rules: &Rules, iterations: usize) -> usize {
    let (lowest_freq, highest_freq) =
        highest_and_lowest_freq_after_n_iterations(template, iterations, rules);
    highest_freq - lowest_freq
}

fn part1(template: &str, rules: &Rules) {
    println!("Day 14 part 1: {}", solve(template, rules, 10));
}

fn part2(template: &str, rules: &Rules) {
    println!("Day 14 part 2: {}", solve(template, rules, 40));
}

fn main() {
    let mut input = String::new();
    match io::stdin().read_to_string(&mut input) {
        Ok(_) => (),
        Err(e) => {
            panic!("failed to read input: {}", e);
        }
    }
    match parse_input(input.as_str()) {
        Ok((template, rules)) => {
            part1(template.as_str(), &rules);
            part2(template.as_str(), &rules);
        }
        Err(e) => {
            eprintln!("{}", e);
        }
    }
}
