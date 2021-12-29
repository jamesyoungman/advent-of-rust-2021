use std::cmp::Ordering;
use std::io;
use std::io::prelude::*;
use std::ops::Range;
use std::str::FromStr;

use nom::{
    bytes::complete::tag,
    character::complete::{char, digit1},
    combinator::{map_res, opt, recognize},
    sequence::{preceded, tuple},
    IResult,
};
use tracing_subscriber::prelude::*;

type Pair = (i32, i32);

#[derive(Debug, Eq, PartialEq)]
struct Target {
    x: Range<i32>,
    y: Range<i32>,
}

impl Target {
    fn contains(&self, x: i32, y: i32) -> bool {
        self.x.contains(&x) && self.y.contains(&y)
    }
}

fn i32_parser(input: &str) -> IResult<&str, i32> {
    map_res(
        recognize(tuple((opt(char('-')), digit1))),
        FromStr::from_str,
    )(input)
}

fn parse_range(input: &str) -> IResult<&str, Pair> {
    tuple((i32_parser, preceded(tag(".."), i32_parser)))(input)
}

fn parse_target(input: &str) -> IResult<&str, (Pair, Pair)> {
    preceded(
        tag("target area: x="),
        tuple((parse_range, preceded(tag(", y="), parse_range))),
    )(input)
}

fn maybe_swap(lesser: i32, greater: i32) -> Pair {
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
                        x: xmin..xmax + 1,
                        y: ymin..ymax + 1,
                    })
                } else {
                    Err(format!("unexpected trailing junk: '{}'", unparsed))
                }
            }
            Err(e) => Err(format!("failed to parse '{}': {}", s, e)),
        }
    }
}

#[test]
fn test_parse_target() {
    assert_eq!(
        Ok(Target {
            x: 70..126,
            y: -121..160,
        }),
        Target::try_from("target area: x=70..125, y=159..-121")
    );
}

fn simulate(_name: &str, mut xv: i32, mut yv: i32, target: &Target) -> Vec<Pair> {
    let mut result = Vec::new();
    let mut x = 0;
    let mut y = 0;
    for _iter in 0.. {
        x += xv;
        y += yv;
	match xv.cmp(&0) {
	    Ordering::Greater => { xv -= 1; }
	    Ordering::Equal => (),
	    Ordering::Less => { xv += 1; }
	}
        yv -= 1;
        result.push((x, y));
        if y < target.y.start {
            break;
        }
    }
    result
}

fn sim(name: &str, xv: i32, yv: i32, target: &Target) -> (bool, i32) {
    let points = simulate(name, xv, yv, target);
    let hit = points.iter()
        .any(|(x, y)| target.contains(*x, *y));
    let high = points.iter().map(|(_x, y)| y).max().unwrap();
    (hit, *high)
}

#[test]
fn test_sim() {
    let target = Target {
        x: 20..31,
        y: -10..-4,
    };

    fn tri(n: i32) -> i32 {
        (n * n + n) / 2
    }

    assert_eq!(sim("example1", 7, 2, &target), (true, tri(2)));
    assert_eq!(sim("example1", 6, 9, &target), (true, 45));
    assert_eq!(sim("wrong-way-1", -7, 2, &target), (false, tri(2)));
    assert_eq!(sim("overshoot-x", 1000, 2, &target), (false, tri(2)));
}

fn on_target_velocities(target: &Target) -> Vec<(i32, i32, i32)> {
    let d = -(target.y.start - 1);
    (1..target.x.end)
        .flat_map(|xv: i32| ((-d)..d).map(move |yv: i32| (xv, yv)))
        .filter_map(|(xv, yv)| {
            let (hit, high) = sim("solve", xv, yv, target);
            if hit {
                Some((xv, yv, high))
            } else {
                None
            }
        })
        .collect()
}

#[test]
fn test_on_target_velocities() {
    let target = Target {
        x: 20..31,
        y: -10..-4,
    };
    assert_eq!(on_target_velocities(&target).len(), 112);
}

fn solve(target: &Target) -> Option<i32> {
    on_target_velocities(target)
        .iter()
        .map(|(_xv, _yv, high)| *high)
        .max()
}

#[test]
fn test_solve() {
    let target = Target {
        x: 20..31,
        y: -10..-4,
    };
    assert_eq!(solve(&target), Some(45));
}

fn part1(target: &Target) {
    println!("Day 17 part 1: {}", solve(target).unwrap());
}

fn part2(target: &Target) {
    let n = on_target_velocities(target).len();
    println!("Day 17 part 2: {}", n);
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
    let no_newline: &str = input.strip_suffix('\n').unwrap_or_else(|| input.as_str());
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
