use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;

use regex::{Captures, Regex};
use tracing_subscriber::prelude::*;

#[derive(Debug, PartialEq, Eq, Clone)]
struct SnailNum(String);

impl From<&str> for SnailNum {
    fn from(s: &str) -> SnailNum {
        SnailNum(s.to_string())
    }
}

impl Display for SnailNum {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(self.0.as_str())
    }
}

fn parse_snail_number(s: &str) -> Result<SnailNum, String> {
    Ok(SnailNum(s.to_string()))
}

fn find_explode_point(n: &SnailNum) -> Option<(usize, usize)> {
    const EXPLODE_DEPTH: i32 = 4;
    let mut depth: i32 = -1;
    let mut explode_start: Option<usize> = None;
    for (pos, ch) in n.0.chars().enumerate() {
        //println!("find_explode_point: at {}, depth={}, explode_start={:?}, ch={}",
        //	 pos, depth, explode_start, ch);
        match ch {
            '[' => {
                if let Some(_) = explode_start {
                    panic!("more than {} levels of nesting", EXPLODE_DEPTH);
                } else {
                    depth = match depth.checked_add(1) {
                        None => {
                            panic!("too many '['");
                        }
                        Some(d) => d,
                    }
                }
            }
            ']' => {
                if let Some(start) = explode_start {
                    return Some((start, pos));
                } else {
                    depth = depth - 1;
		    if depth < -1 {
			panic!("number has more ']' than '['");
		    }
                }
            }
            d if d.is_ascii_digit() => {
		assert!(depth >= 0);
                if depth == EXPLODE_DEPTH && explode_start.is_none() {
                    explode_start = Some(pos);
                }
            }
            ',' => (),
            _ => {
                panic!("unexpected character '{}'", ch);
            }
        }
    }
    None
}

#[test]
fn test_find_explode_point() {
    fn find_explode_substr(n: &SnailNum) -> Option<&str> {
        match find_explode_point(n) {
            Some((begin, end)) => n.0.get(begin..end),
            None => None,
        }
    }

    assert_eq!(find_explode_substr(&SnailNum::from("[1,2]")), None);
    assert_eq!(find_explode_substr(&SnailNum::from("[[1,2],[3,4]]")), None);
    assert_eq!(
        find_explode_substr(&SnailNum::from("[[[[[9,8],1],2],3],4]")),
        Some("9,8")
    );
}

fn add_stringly_typed_number(s: &str, to_add: &str) -> String {
    match to_add.parse::<i32>() {
        Ok(to_add) => match s.parse::<i32>() {
            Ok(n) => {
		let result = (n + to_add).to_string();
		println!("add_stringly_typed_number: {} + {} -> {}",
			n, to_add, result);
		result
	    }
            Err(e) => {
                panic!("'{}' is not a number: {}", s, e);
            }
        },
        Err(e) => {
            panic!("'{}' is not a number: {}", to_add, e);
        }
    }
}

fn explode_lhs(s: &str, left_number: &str) -> String {
    println!("explode_lhs:  input={}", s);
    let rx = Regex::new(r"^(.*\D)(\d+)(\D*)").unwrap();
    let add = |caps: &Captures| -> String {
	let left = &caps[1];
	let middle = add_stringly_typed_number(&caps[2], left_number);
	let right = &caps[3];
	println!("explode_lhs:   left={}", left);
	println!("explode_lhs:caps[2]={}", &caps[2]);
	println!("explode_lhs: middle={}", middle);
	println!("explode_lhs:  right={}", right);
        format!("{}{}{}", left, middle, right)
    };
    rx.replace(s, add).to_string()
}

#[test]
fn test_explode_lhs() {
    assert_eq!(explode_lhs("[[[[", "9"), "[[[[".to_string());
    assert_eq!(explode_lhs("[1,2],[", "4"), "[1,6],[");
}

fn explode_rhs(s: &str, right_number: &str) -> String {
    let rx = Regex::new(r"^(\D*)(\d+)(.*)$").unwrap();
    let add = |caps: &Captures| -> String {
        format!(
            "{}{}{}",
            &caps[1],
            &add_stringly_typed_number(&caps[2], right_number),
            &caps[3]
        )
    };
    rx.replace(s, add).to_string()
}

fn extract_pair(s: &str) -> (String, String) {
    let rx = Regex::new(r"^\[(\d+),(\d+)\]").unwrap();
    match rx.captures(s) {
        Some(caps) => (caps[1].to_string(), caps[2].to_string()),
        None => {
            panic!("expected [...], got {}", s);
        }
    }
}

fn explode(n: SnailNum) -> (SnailNum, bool) {
    match find_explode_point(&n) {
        Some((mut begin, mut end)) => {
            // n.0[begin..end] is the actual pair (e.g. "8,2").  but
            // we actually want to replace "[8,2]" with 0.  So we
            // widen our window by 1 in each direction.
            begin -= 1;
            end += 1;
            //println!("begin is {}", begin);
            //println!("end is {}", end);
            match n.0.get(begin..end) {
                Some(s) => {
                    println!("    exploding pair {}", s);
                    let (left_number, right_number) = extract_pair(s);
                    let lhs = n.0.get(0..begin).unwrap();
                    let rhs = n.0.get(end..).unwrap();
                    let output = format!(
                        "{}0{}",
                        explode_lhs(lhs, &left_number),
                        explode_rhs(rhs, &right_number)
                    );
                    println!("    exploding {}\n    result is {}", &n, &output);
                    (SnailNum(output), true)
                }
                None => {
                    panic!("find_explode_point returned invalid indexes");
                }
            }
        }
        None => (n, false), // no need to explode.
    }
}

#[test]
fn test_explode() {
    assert_eq!(
        explode(SnailNum::from("[1,2]")),
        (SnailNum::from("[1,2]"), false)
    );
    assert_eq!(
        explode(SnailNum::from("[[[[[9,8],1],2],3],4]")),
        (SnailNum::from("[[[[0,9],2],3],4]"), true)
    );
    assert_eq!(
        explode(SnailNum::from("[7,[6,[5,[4,[3,2]]]]]")),
        (SnailNum::from("[7,[6,[5,[7,0]]]]"), true)
    );
    assert_eq!(
        explode(SnailNum::from("[[6,[5,[4,[3,2]]]],1]")),
        (SnailNum::from("[[6,[5,[7,0]]],3]"), true)
    );
    assert_eq!(
        explode(SnailNum::from("[[3,[2,[1,[7,3]]]],[6,[5,[4,[3,2]]]]]")),
        (SnailNum::from("[[3,[2,[8,0]]],[9,[5,[4,[3,2]]]]]"), true)
    );
    assert_eq!(
        explode(SnailNum::from("[[3,[2,[8,0]]],[9,[5,[4,[3,2]]]]]")),
        (SnailNum::from("[[3,[2,[8,0]]],[9,[5,[7,0]]]]"), true)
    );
}

fn split(n: SnailNum) -> (SnailNum, bool) {
    let rx = Regex::new(r"^(.*?\D)(\d\d+)(\D.*)$").unwrap();
    match rx.captures(&n.0) {
        None => (n, false),
        Some(caps) => match caps[2].parse::<i32>() {
            Ok(big) => {
                let left = big / 2;
                let right = left + big % 2;
                let newval: String = format!("{}[{},{}]{}", &caps[1], left, right, &caps[3]);
                println!("    splitting {}\n    result is {}", &n, &newval);
                (SnailNum::from(newval.as_str()), true)
            }
            Err(e) => {
                panic!("expected number, got {} ({})", &caps[2], e);
            }
        },
    }
}

#[test]
fn test_split() {
    assert_eq!(
        split(SnailNum::from("[10,6]")),
        (SnailNum::from("[[5,5],6]"), true)
    );
    assert_eq!(
        split(SnailNum::from("[11,6]")),
        (SnailNum::from("[[5,6],6]"), true)
    );
    assert_eq!(
        split(SnailNum::from("[12,6]")),
        (SnailNum::from("[[6,6],6]"), true)
    );
    // Verify that we pass through stuff on the left that doesn't need
    // splitting.
    assert_eq!(
        split(SnailNum::from("[[1,2],[10,6]]")),
        (SnailNum::from("[[1,2],[[5,5],6]]"), true)
    );
    // Verify that we always split the leftmost number.
    assert_eq!(
        split(SnailNum::from("[12,16]")),
        (SnailNum::from("[[6,6],16]"), true)
    );
}

fn reduce(mut n: SnailNum) -> SnailNum {
    loop {
        println!("  reducing {}", &n);
        let (exploded_number, did_explode) = explode(n);
        n = exploded_number;
        if !did_explode {
            let (split_number, changed) = split(n);
            n = split_number;
            if !changed {
                break;
            }
        }
    }
    n
}

#[test]
fn test_reduce() {
    assert_eq!(
        reduce(SnailNum::from("[[[[[4,3],4],4],[7,[[8,4],9]]],[1,1]]")),
        SnailNum::from("[[[[0,7],4],[[7,8],[6,0]]],[8,1]]")
    );
}

fn add(left: SnailNum, right: SnailNum) -> SnailNum {
    let tmp = format!("[{},{}]", left, right);
    println!("adding {} to {} by reducing {}", &left.0, &right.0, &tmp);
    reduce(SnailNum::from(tmp.as_str()))
}

#[test]
fn test_add() {
    let left = SnailNum::from("[[[[4,3],4],4],[7,[[8,4],9]]]");
    let right = SnailNum::from("[1,1]");
    assert_eq!(
        add(left, right),
        SnailNum::from("[[[[0,7],4],[[7,8],[6,0]]],[8,1]]")
    );
}

#[test]
fn test_add_larger_example() {
    assert_eq!(
        add(
            SnailNum::from("[[[0,[4,5]],[0,0]],[[[4,5],[2,6]],[9,5]]]"),
            SnailNum::from("[7,[[[3,7],[4,3]],[[6,3],[8,8]]]]")
        ),
        SnailNum::from("[[[[4,0],[5,4]],[[7,7],[6,0]]],[[8,[7,7]],[[7,9],[5,0]]]]")
    );
}

#[test]
fn test_add_larger_example_failing_step_a() {
    // This test is takng from the falling step within the calculation
    // for test_add_larger_example.
    assert_eq!(
	add(
	    SnailNum::from("[[[[6,6],[6,6]],[[6,0],[6,7]]],[[[7,7],[8,9]],[8,[8,1]]]]"),
	    SnailNum::from("[2,9]")
	),
	SnailNum::from("[[[[6,6],[7,7]],[[0,7],[7,7]]],[[[5,5],[5,6]],9]]"));
}

#[test]
fn test_add_larger_example_failing_step_b() {
    // This test is takng from the falling step within the calculation
    // for test_add_larger_example.
    assert_eq!(
	explode(SnailNum::from("[[[[12,12],[6,14]],[[15,0],[17,[8,1]]]],[2,9]]")),
	(SnailNum::from("[[[[12,12],[6,14]],[[15,0],[25,0]]],[3,9]]"), true));
}

fn add_snail_numbers<I, S>(items: I) -> SnailNum
where
    I: IntoIterator<Item = S>,
    S: Into<SnailNum>,
{
    let mut it = items.into_iter().map(|item| item.into());
    match it.next() {
        Some(first) => it.fold(first.into(), |acc, item| {
            println!("Adding {} and {}", &acc, &item);
            add(acc, item)
        }),
        None => {
            panic!("There were no input items and I don't know what the Snalfish zero is");
        }
    }
}

#[test]
fn test_add_snail_numbers_sample() {
    assert_eq!(
        add_snail_numbers(["[1,1]", "[2,2]", "[3,3]", "[4,4]"]),
        SnailNum::from("[[[[1,1],[2,2]],[3,3]],[4,4]]")
    );

    assert_eq!(
        add_snail_numbers(["[1,1]", "[2,2]", "[3,3]", "[4,4]", "[5,5]"]),
        SnailNum::from("[[[[3,0],[5,3]],[4,4]],[5,5]]")
    );

    assert_eq!(
        add_snail_numbers(["[1,1]", "[2,2]", "[3,3]", "[4,4]", "[5,5]", "[6,6]"]),
        SnailNum::from("[[[[5,0],[7,4]],[5,5]],[6,6]]")
    );
}

#[test]
fn test_add_snail_numbers_large_example() {
    assert_eq!(add_snail_numbers(["[[[0,[4,5]],[0,0]],[[[4,5],[2,6]],[9,5]]]",
				  "[7,[[[3,7],[4,3]],[[6,3],[8,8]]]]",
				  "[[2,[[0,8],[3,4]]],[[[6,7],1],[7,[1,6]]]]",
				  "[[[[2,4],7],[6,[0,5]]],[[[6,8],[2,8]],[[2,1],[4,5]]]]",
				  "[7,[5,[[3,8],[1,4]]]]",
				  "[[2,[2,2]],[8,[8,1]]]",
				  "[2,9]",
				  "[1,[[[9,3],9],[[9,0],[0,7]]]]",
				  "[[[5,[7,4]],7],1]",
				  "[[[[4,2],2],6],[8,7]]"]),
	       SnailNum::from("[[[[8,7],[7,7]],[[8,6],[7,7]]],[[[0,7],[6,6]],[8,7]]]"));
}

#[test]
fn test_display_roundtrips() {
    for s in &[
        "[5,3]",
        "[5,[1,2]]",
        "[[1,2],5]",
        "[[1,2],[3,4]]",
        "[[1,2],[[8,9],4]]",
    ] {
        match parse_snail_number(s) {
            Ok(num) => {
                let formatted = num.to_string();
                assert_eq!(s, &formatted, "failed to round-trip parse/print");
            }
            Err(e) => {
                panic!("failed to parse '{}': {}", s, e);
            }
        }
    }
}

fn part1(_nums: &[SnailNum]) {
}

fn run() -> Result<(), String> {
    let fmt_layer = tracing_subscriber::fmt::layer().with_target(true);
    let filter_layer = match tracing_subscriber::EnvFilter::try_from_default_env()
        .or_else(|_| tracing_subscriber::EnvFilter::try_new("debug"))
    {
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        }
        Ok(layer) => layer,
    };

    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .init();

    let lines: Vec<String> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .collect();
    let parsed: Result<Vec<SnailNum>, String> = lines
        .iter()
        .map(|line| -> Result<SnailNum, String> { parse_snail_number(line) })
        .collect();
    match parsed {
        Ok(snail_numbers) => {
            println!(
                "There are {} snail numbers in the input.",
                snail_numbers.len()
            );
            part1(&snail_numbers);
            Ok(())
        }
        Err(e) => Err(e),
    }
}

fn main() {
    if let Err(e) = run() {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}
