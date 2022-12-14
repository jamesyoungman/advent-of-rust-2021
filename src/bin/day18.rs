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
                    depth -= 1;
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
		(n + to_add).to_string()
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

#[test]
fn test_explode_lhs() {
    let evaluator = Evaluator::new();
    assert_eq!(evaluator.explode_lhs("[[[[", "9"), "[[[[".to_string());
    assert_eq!(evaluator.explode_lhs("[1,2],[", "4"), "[1,6],[");
}

#[test]
fn test_explode() {
    let evaluator = Evaluator::new();
    assert_eq!(
        evaluator.explode(SnailNum::from("[1,2]")),
        (SnailNum::from("[1,2]"), false)
    );
    assert_eq!(
        evaluator.explode(SnailNum::from("[[[[[9,8],1],2],3],4]")),
        (SnailNum::from("[[[[0,9],2],3],4]"), true)
    );
    assert_eq!(
        evaluator.explode(SnailNum::from("[7,[6,[5,[4,[3,2]]]]]")),
        (SnailNum::from("[7,[6,[5,[7,0]]]]"), true)
    );
    assert_eq!(
        evaluator.explode(SnailNum::from("[[6,[5,[4,[3,2]]]],1]")),
        (SnailNum::from("[[6,[5,[7,0]]],3]"), true)
    );
    assert_eq!(
        evaluator.explode(SnailNum::from("[[3,[2,[1,[7,3]]]],[6,[5,[4,[3,2]]]]]")),
        (SnailNum::from("[[3,[2,[8,0]]],[9,[5,[4,[3,2]]]]]"), true)
    );
    assert_eq!(
        evaluator.explode(SnailNum::from("[[3,[2,[8,0]]],[9,[5,[4,[3,2]]]]]")),
        (SnailNum::from("[[3,[2,[8,0]]],[9,[5,[7,0]]]]"), true)
    );
}

#[test]
fn test_split() {
    let evaluator = Evaluator::new();
    assert_eq!(
        evaluator.split(SnailNum::from("[10,6]")),
        (SnailNum::from("[[5,5],6]"), true)
    );
    assert_eq!(
        evaluator.split(SnailNum::from("[11,6]")),
        (SnailNum::from("[[5,6],6]"), true)
    );
    assert_eq!(
        evaluator.split(SnailNum::from("[12,6]")),
        (SnailNum::from("[[6,6],6]"), true)
    );
    // Verify that we pass through stuff on the left that doesn't need
    // splitting.
    assert_eq!(
        evaluator.split(SnailNum::from("[[1,2],[10,6]]")),
        (SnailNum::from("[[1,2],[[5,5],6]]"), true)
    );
    // Verify that we always split the leftmost number.
    assert_eq!(
        evaluator.split(SnailNum::from("[12,16]")),
        (SnailNum::from("[[6,6],16]"), true)
    );
}

#[test]
fn test_reduce() {
    let evaluator = Evaluator::new();
    assert_eq!(
        evaluator.reduce(SnailNum::from("[[[[[4,3],4],4],[7,[[8,4],9]]],[1,1]]")),
        SnailNum::from("[[[[0,7],4],[[7,8],[6,0]]],[8,1]]")
    );
}

#[test]
fn test_add() {
    let evaluator = Evaluator::new();
    let left = SnailNum::from("[[[[4,3],4],4],[7,[[8,4],9]]]");
    let right = SnailNum::from("[1,1]");
    assert_eq!(
        evaluator.add(left, right),
        SnailNum::from("[[[[0,7],4],[[7,8],[6,0]]],[8,1]]")
    );
}

#[test]
fn test_add_larger_example() {
    let evaluator = Evaluator::new();
    assert_eq!(
        evaluator.add(
            SnailNum::from("[[[0,[4,5]],[0,0]],[[[4,5],[2,6]],[9,5]]]"),
            SnailNum::from("[7,[[[3,7],[4,3]],[[6,3],[8,8]]]]")
        ),
        SnailNum::from("[[[[4,0],[5,4]],[[7,7],[6,0]]],[[8,[7,7]],[[7,9],[5,0]]]]")
    );
}

#[test]
fn test_add_larger_example_failing_step_a() {
    let evaluator = Evaluator::new();
    // This test is takng from the falling step within the calculation
    // for test_add_larger_example.
    assert_eq!(
	evaluator.add(
	    SnailNum::from("[[[[6,6],[6,6]],[[6,0],[6,7]]],[[[7,7],[8,9]],[8,[8,1]]]]"),
	    SnailNum::from("[2,9]")
	),
	SnailNum::from("[[[[6,6],[7,7]],[[0,7],[7,7]]],[[[5,5],[5,6]],9]]"));
}

#[test]
fn test_add_larger_example_failing_step_b() {
    let evaluator = Evaluator::new();
    // This test is takng from the falling step within the calculation
    // for test_add_larger_example.
    assert_eq!(
	evaluator.explode(SnailNum::from("[[[[12,12],[6,14]],[[15,0],[17,[8,1]]]],[2,9]]")),
	(SnailNum::from("[[[[12,12],[6,14]],[[15,0],[25,0]]],[3,9]]"), true));
}

#[test]
fn test_add_snail_numbers_sample() {
    let evaluator = Evaluator::new();
    assert_eq!(
	evaluator.add_snail_numbers(["[1,1]", "[2,2]", "[3,3]", "[4,4]"]),
        SnailNum::from("[[[[1,1],[2,2]],[3,3]],[4,4]]")
    );

    assert_eq!(
	evaluator.add_snail_numbers(["[1,1]", "[2,2]", "[3,3]", "[4,4]", "[5,5]"]),
        SnailNum::from("[[[[3,0],[5,3]],[4,4]],[5,5]]")
    );

    assert_eq!(
	evaluator.add_snail_numbers(["[1,1]", "[2,2]", "[3,3]", "[4,4]", "[5,5]", "[6,6]"]),
        SnailNum::from("[[[[5,0],[7,4]],[5,5]],[6,6]]")
    );
}

#[test]
fn test_add_snail_numbers_large_example() {
    let evaluator = Evaluator::new();
    assert_eq!(evaluator.add_snail_numbers([
	"[[[0,[4,5]],[0,0]],[[[4,5],[2,6]],[9,5]]]",
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


struct Evaluator {
    magnitude_step_rx: Regex,
    magnitude_final_rx: Regex,
    split_rx: Regex,
    explode_lhs_rx: Regex,
    explode_rhs_rx: Regex,
    extract_pair_rx: Regex,
}

impl Evaluator {
    fn new() -> Evaluator {
	Evaluator {
	    magnitude_step_rx: Regex::new(r"\[(\d+),(\d+)]").unwrap(),
	    magnitude_final_rx: Regex::new(r"\[(\d+)]").unwrap(),
	    split_rx: Regex::new(r"^(.*?\D)(\d\d+)(\D.*)$").unwrap(),
	    explode_lhs_rx: Regex::new(r"^(.*\D)(\d+)(\D*)").unwrap(),
	    explode_rhs_rx: Regex::new(r"^(\D*)(\d+)(.*)$").unwrap(),
	    extract_pair_rx: Regex::new(r"^\[(\d+),(\d+)\]").unwrap(),
	}
    }

    fn explode(&self, n: SnailNum) -> (SnailNum, bool) {
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
			//println!("    exploding pair {}", s);
			let (left_number, right_number) = self.extract_pair(s);
			let lhs = n.0.get(0..begin).unwrap();
			let rhs = n.0.get(end..).unwrap();
			let output = format!(
                            "{}0{}",
                            self.explode_lhs(lhs, &left_number),
                            self.explode_rhs(rhs, &right_number)
			);
			//println!("    exploding {}\n    result is {}", &n, &output);
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

    fn split(&self, n: SnailNum) -> (SnailNum, bool) {
	match self.split_rx.captures(&n.0) {
            None => (n, false),
            Some(caps) => match caps[2].parse::<i32>() {
		Ok(big) => {
                    let left = big / 2;
                    let right = left + big % 2;
                    let newval: String = format!("{}[{},{}]{}", &caps[1], left, right, &caps[3]);
                    //println!("    splitting {}\n    result is {}", &n, &newval);
                    (SnailNum::from(newval.as_str()), true)
		}
		Err(e) => {
                    panic!("expected number, got {} ({})", &caps[2], e);
		}
            },
	}
    }

    fn magnitude(&self, n: SnailNum) -> u64 {
	let mut digits = n.0;
	let mag_step = |caps: &Captures| -> String {
	    let left = &caps[1];
	    let right = &caps[2];
	    //println!("mag_step: left={}, right={}", left, right);
	    match (left.parse::<u64>().map(|l| l.checked_mul(3)),
		   right.parse::<u64>().map(|r| r.checked_mul(2))) {
		(Ok(None), _) => {
		    panic!("magnitude: overflow in {}*3", &left)
		}
		(_, Ok(None)) => {
		    panic!("magnitude: overflow in {}*2", &right)
		}
		(Ok(Some(l)), Ok(Some(r))) => match l.checked_add(r) {
		    Some(result) => {
			//println!("mag_step; [{},{}] -> {}",
			//	     left, right, result);
			format!("{}", result)
		    }
		    None => {
			panic!("magnitude: overflow in final addition {} + {}", &l, &r);
		    }
		}
		(Err(e), _) => {
		    panic!("magnitude: cannot convert number '{}': {}", left, e)
		}
		(_, Err(e)) => {
		    panic!("magnitude: cannot convert number '{}': {}", right, e)
		}
	    }
	};
	loop {
	    //dbg!(&digits);
	    let updated = self.magnitude_step_rx.replace(digits.as_str(), mag_step).to_string();
	    if updated == digits {
		let result_as_str = self.magnitude_final_rx.replace(digits.as_str(), "$1");
		match result_as_str.parse() {
		    Ok(n) => {
			return n;
		    }
		    Err(e) => {
			panic!("magnitude: cannot convert final result {}: {}", &result_as_str, e);
		    }
		}
	    }
	    digits = updated;
	}
    }

    pub fn reduce(&self, mut n: SnailNum) -> SnailNum {
	loop {
            //println!("  reducing {}", &n);
            let (exploded_number, did_explode) = self.explode(n);
            n = exploded_number;
            if !did_explode {
		let (split_number, changed) = self.split(n);
		n = split_number;
		if !changed {
                    break;
		}
            }
	}
	n
    }

    pub fn add(&self, left: SnailNum, right: SnailNum) -> SnailNum {
	let tmp = format!("[{},{}]", left, right);
	//println!("adding {} to {} by reducing {}", &left.0, &right.0, &tmp);
	self.reduce(SnailNum::from(tmp.as_str()))
    }

    fn add_snail_numbers<I, S>(&self, items: I) -> SnailNum
    where
	I: IntoIterator<Item = S>,
	S: Into<SnailNum>,
    {
	let mut it = items.into_iter().map(|item| item.into());
	match it.next() {
            Some(first) => it.fold(first.into(), |acc, item| {
		//println!("Adding {} and {}", &acc, &item);
		self.add(acc, item)
            }),
            None => {
		panic!("There were no input items and I don't know what the Snailfish zero is");
            }
	}
    }

    fn explode_lhs(&self, s: &str, left_number: &str) -> String {
	//println!("explode_lhs:  input={}", s);
	let add = |caps: &Captures| -> String {
	    let left = &caps[1];
	    let middle = add_stringly_typed_number(&caps[2], left_number);
	    let right = &caps[3];
	    //println!("explode_lhs:   left={}", left);
	    //println!("explode_lhs:caps[2]={}", &caps[2]);
	    //println!("explode_lhs: middle={}", middle);
	    //println!("explode_lhs:  right={}", right);
            format!("{}{}{}", left, middle, right)
	};
	self.explode_lhs_rx.replace(s, add).to_string()
    }

    fn explode_rhs(&self, s: &str, right_number: &str) -> String {
	let add = |caps: &Captures| -> String {
            format!(
		"{}{}{}",
		&caps[1],
		&add_stringly_typed_number(&caps[2], right_number),
		&caps[3]
            )
	};
	self.explode_rhs_rx.replace(s, add).to_string()
    }

fn extract_pair(&self, s: &str) -> (String, String) {
	match self.extract_pair_rx.captures(s) {
            Some(caps) => (caps[1].to_string(), caps[2].to_string()),
            None => {
		panic!("expected [...], got {}", s);
            }
	}
    }
}

#[test]
fn test_magnitude() {
    let evaluator = Evaluator::new();
    assert_eq!(evaluator.magnitude(SnailNum::from("[9,1]")), 29);
    assert_eq!(evaluator.magnitude(SnailNum::from("[1,9]")), 21);
    assert_eq!(evaluator.magnitude(SnailNum::from("[[9,1],[1,9]]")), 129);
    assert_eq!(evaluator.magnitude(SnailNum::from("[[1,2],[[3,4],5]]")), 143);
    assert_eq!(evaluator.magnitude(SnailNum::from("[[[[8,7],[7,7]],[[8,6],[7,7]]],[[[0,7],[6,6]],[8,7]]]")), 3488);
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

#[test]
fn test_final_part1_example() {
    let evaluator = Evaluator::new();
    let sum = evaluator.add_snail_numbers([
	"[[[0,[5,8]],[[1,7],[9,6]]],[[4,[1,2]],[[1,4],2]]]",
	"[[[5,[2,8]],4],[5,[[9,9],0]]]",
	"[6,[[[6,2],[5,6]],[[7,6],[4,7]]]]",
	"[[[6,[0,7]],[0,9]],[4,[9,[9,0]]]]",
	"[[[7,[6,4]],[3,[1,3]]],[[[5,5],1],9]]",
	"[[6,[[7,3],[3,2]]],[[[3,8],[5,7]],4]]",
	"[[[[5,4],[7,7]],8],[[8,3],8]]",
	"[[9,3],[[9,9],[6,[4,9]]]]",
	"[[2,[[7,7],7]],[[5,8],[[9,3],[0,2]]]]",
	"[[[[5,2],5],[8,[3,7]]],[[5,[7,5]],[4,4]]]"]);
    assert_eq!(sum, SnailNum::from("[[[[6,6],[7,6]],[[7,7],[7,0]]],[[[7,7],[7,7]],[[7,8],[9,9]]]]"));
    assert_eq!(evaluator.magnitude(sum), 4140);
}

fn part1(nums: &[SnailNum]) {
    let eval = Evaluator::new();
    println!("Day 18 part 1: {}", eval.magnitude(eval.add_snail_numbers(nums.iter().map(|n| n.to_owned()))));

}

fn part2(nums: &[SnailNum]) {
    let mut magnitudes: Vec<u64> = Vec::with_capacity(nums.len() * nums.len());
    let eval = Evaluator::new();
    for (i, left) in nums.iter().enumerate() {
	for (j, right) in nums.iter().enumerate() {
	    if i != j {
		magnitudes.push(eval.magnitude(eval.add(left.clone(), right.clone())));
	    }
	}
    }
    magnitudes.sort();
    println!("Day 18 part 2: {}", magnitudes.pop().unwrap());
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
            part2(&snail_numbers);
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
