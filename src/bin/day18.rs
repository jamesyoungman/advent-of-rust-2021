use std::cmp::max;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;
use std::str::FromStr;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, digit1},
    combinator::{map, map_res, opt, recognize},
    sequence::{preceded, separated_pair, terminated, tuple},
    IResult,
};
use tracing_subscriber::prelude::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum SnailDigit {
    Empty,
    Internal,
    Literal(i8),
}

impl From<i8> for SnailDigit {
    fn from(n: i8) -> SnailDigit {
	SnailDigit::Literal(n)
    }
}

impl Default for SnailDigit {
    fn default() -> SnailDigit {
	SnailDigit::Empty
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct SnailNum {
    digits: Vec<SnailDigit>,
}

impl From<(i8, i8)> for SnailNum {
    fn from(pair: (i8, i8)) -> SnailNum {
	SnailNum {
	    digits: vec![SnailDigit::from(pair.0),
			 SnailDigit::Internal, // the root
			 SnailDigit::from(pair.1),
			 SnailDigit::Empty],
	}
    }
}

#[test]
fn test_from_pair() {
    assert_eq!(&SnailNum::from((5,3)),
	       &SnailNum {
		   digits: vec![
		       SnailDigit::Literal(5),
		       SnailDigit::Internal,
		       SnailDigit::Literal(3),
		       SnailDigit::Empty,
		   ]
	       });
}


fn fix_tail(
    mut v: Vec<SnailDigit>,
    fill: SnailDigit,
) -> Vec<SnailDigit> {
    let orig_size: usize = v.len();
    loop {
	match v.pop() {
	    Some(SnailDigit::Literal(n)) => {
		v.push(SnailDigit::Literal(n));
		break;
	    }
	    None => {
		break;
	    }
	    Some(SnailDigit::Internal | SnailDigit::Empty) => (),
	}
    }
    v.resize(orig_size, fill);
    v
}


fn stretch(v: &[SnailDigit],
	   want_len: usize,
	   fill: SnailDigit,
) -> Vec<SnailDigit> {
    let mut result = Vec::with_capacity(want_len);
    let old_len = v.len();
    let margin = (want_len - old_len) / 2;
    result.resize(margin, SnailDigit::Empty);
    result.extend(v);
    result.resize(want_len, SnailDigit::Empty);
    fix_tail(result, fill)
}

impl From<(&SnailNum, &SnailNum)> for SnailNum {
    fn from(pair: (&SnailNum, &SnailNum)) -> SnailNum {
	let (left, right) = pair;

	let want_len = max(left.digits.len(), right.digits.len());
	let left_result = stretch(&left.digits, want_len, SnailDigit::Internal);
	assert_eq!(left_result.len(), want_len);

	let right_result = stretch(&right.digits, want_len, SnailDigit::Empty);
	assert_eq!(right_result.len(), want_len);

	let mut v: Vec<SnailDigit> = Vec::with_capacity(want_len * 2);
	assert_eq!(left_result.len(), right_result.len());
	v.extend(left_result);
	v.extend(right_result);
	SnailNum {
	    digits: v,
	}
    }
}

#[test]
fn test_from_snailnum_pair() {
    let a = SnailNum::from((1, 2));
    let b = SnailNum::from((6, 8));
    let c = SnailNum::from((&a, &b));
    assert_eq!(&c.digits,
	       &vec![SnailDigit::Literal(1),
		     SnailDigit::Internal,
		     SnailDigit::Literal(2),
		     SnailDigit::Internal, // root
		     SnailDigit::Literal(6),
		     SnailDigit::Internal,
		     SnailDigit::Literal(8),
		     SnailDigit::Empty]);
}

fn fmt_subtree(
    f: &mut Formatter<'_>,
    from: usize,
    to: usize,
    num: &[SnailDigit]
) -> fmt::Result {
    dbg!(&from);
    dbg!(&to);
    dbg!(&num[from..to]);
    let w = to - from;
    dbg!(&w);
    if w == 0 {
	eprintln!("printing zero items");
	return Ok(());
    }
    let r = from + (to - from)/2;
    match dbg!(num[dbg!(r)]) {
	SnailDigit::Empty => Ok(()),
	SnailDigit::Internal => {
	    println!("recursing into {:?} and then {:?}", from..r, r..to);
	    f.write_str("[")
		.and_then(|_| if r > from { fmt_subtree(f, from, r, num) } else { Ok(()) })
		.and_then(|_| f.write_str(","))
		.and_then(|_| if to > r { fmt_subtree(f, r, to, num) } else { Ok(()) })
		.and_then(|_| f.write_str("]"))
	}
	SnailDigit::Literal(n) => {
	    write!(f, "{}", n)
	}
    }
}

impl Display for SnailNum {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
	fmt_subtree(f, 0, self.digits.len()-1, self.digits.as_slice())
    }
}

#[test]
fn test_snailnum_display() {
    assert_eq!(
	&SnailNum {
	    digits: vec![
		SnailDigit::Literal(4),
		SnailDigit::Internal,
		SnailDigit::Literal(7),
		SnailDigit::Empty,
	    ]
	}.to_string(),
	"[4,7]");
    assert_eq!(
	&SnailNum {
	    digits: vec![
		SnailDigit::Literal(6),
		SnailDigit::Internal,
		SnailDigit::Literal(7),
		SnailDigit::Internal,
		SnailDigit::Empty,
		SnailDigit::Literal(2),
		SnailDigit::Empty,
		SnailDigit::Empty,
	    ]
	}.to_string(),
	"[[6,7],2]");
}

fn i8_parser(input: &str) -> IResult<&str, i8> {
    map_res(
        recognize(tuple((opt(char('-')), digit1))),
        FromStr::from_str)
	(input)
}

#[test]
fn test_i8_parser() {
    assert_eq!(i8_parser("5"), Ok(("", 5_i8)));
    assert_eq!(i8_parser("54"), Ok(("", 54_i8)));
    assert_eq!(i8_parser("-20"), Ok(("", -20_i8)));
}

fn naked_pair_parser(input: &str) -> IResult<&str, (SnailNum, SnailNum) > {
    separated_pair(preceded(tag("["), snailnum_parser),
		   char(','),
		   terminated(snailnum_parser, tag("]")))
	(input)
}

#[test]
fn test_naked_pair_parser() {
    assert_eq!(naked_pair_parser("[5,3]"),
	       Ok(("",
		   (
		       SnailNum {
			   digits: vec![
			       SnailDigit::Literal(5),
			       SnailDigit::Empty,
			   ]
		       },
		       SnailNum {
			   digits: vec![
			       SnailDigit::Literal(3),
			       SnailDigit::Empty,
			   ]
		       }
		   ))));
}


fn pair_parser(input: &str) -> IResult<&str, SnailNum > {
    map(naked_pair_parser,
	|(left, right): (SnailNum, SnailNum)| SnailNum::from((&left, &right)))
	(input)
}

fn snailnum_parser(input: &str)-> IResult<&str, SnailNum > {
    alt((
	map(i8_parser, |n| SnailNum { digits: vec![SnailDigit::Literal(n),
						   SnailDigit::Empty] }),
	pair_parser
    ))(input)
}

#[test]
fn test_snailnum_parser() {
    assert_eq!(snailnum_parser("[5,3]"),
	       Ok(("",
		   (
		       SnailNum {
			   digits: vec![
			       SnailDigit::Literal(5),
			       SnailDigit::Internal,
			       SnailDigit::Literal(3),
			       SnailDigit::Empty,
			   ]
		       }
		   ))));
}


fn parse_snail_number(s: &str) -> Result<SnailNum, String> {
    match snailnum_parser(s) {
	Ok((unparsed, n)) => {
	    if unparsed.is_empty() {
		Ok(n)
	    } else {
		Err(format!("unexpected junk after number: '{}'", unparsed))
	    }
	}
	Err(e) => Err(e.to_string()),
    }
}

#[test]
fn test_parse_snail_number() {
    assert_eq!(parse_snail_number("[4,7]"),
	       Ok(SnailNum {
		   digits: vec![
		       SnailDigit::Literal(4),
		       SnailDigit::Internal,
		       SnailDigit::Literal(7),
		       SnailDigit::Empty,
		   ]
	       }));

    assert_eq!(parse_snail_number("[[6,7],2]"),
	       Ok(SnailNum {
		   digits: vec![
		       SnailDigit::Literal(6),
		       SnailDigit::Internal,
		       SnailDigit::Literal(7),
		       SnailDigit::Internal, // root
		       SnailDigit::Empty,
		       SnailDigit::Literal(2),
		       SnailDigit::Empty,
		       SnailDigit::Empty
		   ]
	       }));
}


#[test]
fn test_display_roundtrips() {
    for s in &[
	//"[5,3]",
	//"[5,[1,2]]",
	//"[[1,2],5]",
	//"[[1,2],[3,4]]",
	"[[1,2],[[8,9],4]]",
    ] {
	match parse_snail_number(s) {
	    Ok(num) => {
		dbg!(s);
		dbg!(&num);
		let formatted = num.to_string();
		dbg!(&formatted);
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
        .or_else(|_| tracing_subscriber::EnvFilter::try_new("info"))
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
    let parsed: Result<Vec<SnailNum>, String> = lines.iter()
	.map(|line| -> Result<SnailNum, String> { parse_snail_number(line) })
	.collect();
    match parsed {
	Ok(snail_numbers) => {
	    println!("There are {} snail numbers in the input.", snail_numbers.len());
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
