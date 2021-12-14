use std::collections::BTreeMap;
use std::collections::HashMap;
use std::io;
use std::io::prelude::*;

fn apply_rules_once(
    input: &HashMap<usize, char>,
    rules: &HashMap<(char, char), char>,
) -> HashMap<usize, char> {
    let mut offset: usize = 0;
    let mut prev: Option<char> = None;
    let mut output: HashMap<usize, char> = HashMap::new();
    println!("apply_rules: input = {:?}", &input);
    for pos in 0..input.len() {
	let ch = *input.get(&pos).unwrap();
	if let Some(prev_ch) = prev {
	    println!("pos={}, prev_ch={}, ch={}", pos, prev_ch, ch);
	    assert!(pos > 0);
	    println!("checking for rule for {}{}", prev_ch, ch);
	    match rules.get(&(prev_ch, ch)) {
		Some(insertion) => {
		    println!(
			"applying rule {}{} -> {} at input position {}",
			prev_ch,
			ch,
			insertion,
			pos,
		    );
		    output.insert(pos+offset, *insertion);
		    offset += 1;
		}
		None => {
		    println!("no rule for {}{}", prev_ch, ch);
		},
	    }
	} else {
	    println!("initial iteration: pos={}, ch={}", pos, ch);
	}
	output.insert(pos+offset, ch);
	prev = Some(ch);
    }
    println!("apply_rules: output = {:?}", &output);
    output
}

fn str_to_hash(input: &str) -> HashMap<usize, char> {
    let mut result = HashMap::new();
    for (i, ch) in input.chars().enumerate() {
	result.insert(i, ch);
    }
    result
}

fn apply_rules(
    s: &str,
    count: usize,
    rules: &HashMap<(char, char), char>,
) -> HashMap<usize, char> {
    let mut input = str_to_hash(s);
    for _iter in 0..count {
	input = apply_rules_once(&input, rules)
    }
    input
}

#[cfg(test)]
fn str_apply_rules_once(
    s: &str,
    rules: &HashMap<(char, char), char>,
) -> String {
    println!("apply_rules_once: input={}", s);
    let out = apply_rules_once(&str_to_hash(s), rules);
    let mut result = String::with_capacity(out.len());
    for i in 0..out.len() {
	match out.get(&i) {
	    Some(ch) => {
		result.push(*ch);
	    }
	    None => {
		panic!("expected an output character at position {}: {:?}",
		       i, &out);
	    }
	}
    }
    println!("apply_rules_once: result={}", &result);
    result
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
    let rules: HashMap<(char, char), char> = parse_rules(SAMPLE_RULES)
	.expect("example should be valid");
    assert_eq!(str_apply_rules_once("NNCB", &rules), "NCNBCHB".to_string());
    assert_eq!(str_apply_rules_once("NCNBCHB", &rules), "NBCCNBBBCBHCB".to_string());
    assert_eq!(str_apply_rules_once("NBCCNBBBCBHCB", &rules),
	       "NBBBCNCCNBBNBNBBCHBHHBCHB".to_string());
    assert_eq!(str_apply_rules_once("NBBBCNCCNBBNBNBBCHBHHBCHB", &rules),
	       "NBBNBNBBCCNBCNCCNBBNBBNBBBNBBNBBCBHCBHHNHCBBCBHCB".to_string());
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

fn parse_rules(input: &str) -> Result<HashMap<(char, char), char>, String> {
    let mut result: HashMap<(char, char), char> = HashMap::new();
    for line in input.split_terminator('\n') {
	let (input, output) = parse_rule(line)?;
	result.insert(input, output);
    }
    Ok(result)
}

fn parse_input(input: &str) -> Result<(String, HashMap<(char, char), char>), String> {
    match input.split_once("\n\n") {
	Some((template, tail)) => {
	    match parse_rules(tail) {
		Err(e) => Err(e),
		Ok(rules) => Ok((template.to_string(), rules)),
	    }
	}
	None => Err("missing blank line".to_string()),
    }
}

fn count_frequencies(input: &HashMap<usize, char>) -> HashMap<char, usize> {
    let mut frequency_counts = HashMap::new();
    for ch in input.values() {
	*frequency_counts.entry(*ch).or_insert(0) += 1;
    }
    frequency_counts
}

fn chars_by_frequency(input: &HashMap<usize, char>) -> BTreeMap<usize, Vec<char>> {
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
    rules: &HashMap<(char, char), char>) -> (usize, usize) {
    let result: HashMap<usize, char> = apply_rules(template, iterations, rules);
    let chars_by_frequency: BTreeMap<usize, Vec<char>> = chars_by_frequency(&result);
    match (chars_by_frequency.iter().next(), chars_by_frequency.iter().rev().next()) {
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
	let rules: HashMap<(char, char), char> = parse_rules(SAMPLE_RULES)
	    .expect("example should be valid");
	highest_and_lowest_freq_after_n_iterations(input, count, &rules)
    }

    assert_eq!(hl("NNCB", 1),
	       (1, 2)		// NCNBCHB
    );
}

fn part1(template: &str, rules: &HashMap<(char, char), char>) {
    let (lowest_freq, highest_freq) = highest_and_lowest_freq_after_n_iterations(
	template, 10, rules);
    println!(
	"Day 14 part 1: {} - {} = {}",
	highest_freq,
	lowest_freq,
	highest_freq - lowest_freq
    );
}

fn part2(_template: &str, _rules: &HashMap<(char, char), char>) {
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
