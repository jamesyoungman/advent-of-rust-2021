use std::ops::Range;
use std::io;
use std::io::prelude::*;
use std::str::FromStr;

use nom::{
    bytes::complete::tag,
    character::complete::{char, digit1},
    combinator::{map_res, opt, recognize},
    sequence::{preceded, tuple},
    IResult,
};
use tracing_subscriber::prelude::*;

#[derive(Debug, Eq, PartialEq)]
struct Target {
    x: Range<i32>,
    y: Range<i32>
}

impl Target {
    fn contains(&self, x: i32, y: i32) -> bool {
	self.x.contains(&x) && self.y.contains(&y)
    }
}

fn i32_parser(input: &str) -> IResult<&str, i32> {
    map_res(
        recognize(tuple((opt(char('-')), digit1))),
        FromStr::from_str)
	(input)
}


fn parse_range(input: &str) -> IResult<&str, (i32, i32)> {
    tuple((
	i32_parser,
	preceded(tag(".."),
		 i32_parser)))(input)
}

fn parse_target(input: &str) -> IResult<&str, ((i32, i32), (i32, i32))> {
    preceded(tag("target area: x="),
	     tuple((parse_range,
		    preceded(tag(", y="),
			     parse_range))))(input)
}

fn maybe_swap(lesser: i32, greater: i32) -> (i32, i32) {
    if lesser <= greater {
	(lesser, greater)
    } else {
	(greater, lesser)
    }
}

impl TryFrom<&str> for Target {
    type Error = String;
    fn try_from(s: &str) -> Result<Target, String> {
	match parse_target(s) {
	    Ok((unparsed, ((xmin, xmax), (ymin, ymax)))) => {
		if unparsed.is_empty() {
		    let (xmin, xmax) = maybe_swap(xmin, xmax);
		    let (ymin, ymax) = maybe_swap(ymin, ymax);
		    Ok(Target {
			x: xmin..xmax+1,
			y: ymin..ymax+1,
		    })
		} else {
		    Err(format!("unexpected trailing junk: '{}'", unparsed))
		}
	    }
	    Err(e) => {
		Err(format!("failed to parse '{}': {}", s, e))
	    }
	}
    }
}

#[test]
fn test_parse_target() {
    assert_eq!(Ok(Target {
	x: 70..126,
	y: -121..160,
    }), Target::try_from("target area: x=70..125, y=159..-121"));
}

fn simulate(_name: &str, mut xv: i32, mut yv: i32, target: &Target) -> Vec<(i32, i32)> {
    let highpoint = (yv * yv + yv) / 2;
    //dbg!(&highpoint);
    let mut result = Vec::new();
    let mut x = 0;
    let mut y = 0;
    for _iter in 0.. {
	x += xv;
	y += yv;
	if xv > 0 {
	    xv -= 1;
	} else if xv < 0 {
	    xv += 1;
	}
	yv -= 1;
	result.push((x, y));
	if y < target.y.start {
	    break;
	}
    }
    //dbg!(&result);
    assert_eq!(*result.iter().map(|(_x, y)| y).max().unwrap(), highpoint);
    result
}

fn sim(name: &str, xv: i32, yv: i32, target: &Target) -> (bool, i32) {
    let points = simulate(name, xv, yv, target);
    let hit = points.iter().find(|(x, y)| target.contains(*x, *y)).is_some();
    let high = points.iter().map(|(_x, y)| y).max().unwrap();
    (hit, *high)
}

#[test]
fn test_sim() {
    let target = Target {
	x: 20..31,
	y: -10..-4
    };

    fn tri(n: i32) -> i32 {
	(n * n + n) / 2
    }

    assert_eq!(sim("example1", 7, 2, &target), (true, tri(2)));
    assert_eq!(sim("example1", 6, 9, &target), (true, 45));
    assert_eq!(sim("wrong-way-1", -7, 2, &target), (false, tri(2)));
    assert_eq!(sim("overshoot-x", 1000, 2, &target), (false, tri(2)));
}

fn solve(target: &Target) -> Option<i32> {
    (1..target.x.end)
	.flat_map(|xv: i32| (1..500).map(move |yv: i32| (xv, yv)))
	.filter_map(|(xv, yv)| {
	    let (hit, high) = sim("solve", xv, yv, target);
	    if hit {
		Some(high)
	    } else {
		None
	    }
	})
	.max()
}

#[test]
fn test_solve() {
    let target = Target {
	x: 20..31,
	y: -10..-4
    };
    assert_eq!(solve(&target), Some(45));
}

fn part1(target: &Target) {
    println!("Day 17 part 1: {}", solve(target).unwrap());
}

fn part2(_t: &Target) {
    println!("Day 17 part 2: ");
}

fn main() {
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

    let mut input = String::new();
    match io::stdin().read_to_string(&mut input) {
        Ok(_) => (),
        Err(e) => {
            panic!("failed to read input: {}", e);
        }
    }
    let no_newline: &str = input.strip_suffix("\n").unwrap_or(input.as_str());
    match Target::try_from(no_newline) {
	Ok(t) => {
	    part1(&t);
	    part2(&t);
	}
	Err(e) => {
	    eprintln!("fail: {}", e);
	}
    }
}
