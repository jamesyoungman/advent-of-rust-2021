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
use tracing::{event, span, Level};
use tracing_subscriber::prelude::*;

#[derive(Debug, Eq, PartialEq)]
struct Target {
    x: Range<i32>,
    y: Range<i32>
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

//#[derive(Debug)]
//struct Probe {
//    name: String,
//    x: i32,
//    y: i32,
//    xv: i32,
//    yv: i32
//}
//
//impl Probe {
//    fn step(&mut self) {
//	self.x += self.xv;
//	self.y += self.yv;
//	match self.xv.cmp(&0) {
//	    Ordering::Equal => (),
//	    Ordering::Less => { self.xv += 1; }
//	    Ordering::Greater => { self.xv -= 1; }
//	}
//	self.yv -= 1;
//	dbg!(self);
//    }
//
//    fn is_in(&self, xrange: &Range<i32>, yrange: &Range<i32>) -> bool {
//	xrange.contains(&self.x) && yrange.contains(&self.y)
//    }
//}

fn simulate_x(name: &str, mut xv: i32, target: &Range<i32>) -> Option<Range<usize>> {
    let mut x = 0;

    let mut first_step_inside: Option<usize> = None;
    let mut last_step_inside: Option<usize> = None;
    for iter in 0.. {
	let ontarget = target.contains(&x);
	event!(
	    Level::TRACE,
	    "{}: simulate_x: x={:>3}, xv={:>3}: ontarget={}",
	    name, x, xv, ontarget,
	);
	if target.contains(&x) {
	    if first_step_inside.is_none() {
		first_step_inside = Some(iter);
	    }
	    last_step_inside = Some(iter);
	}
	x += xv;
	if xv > 0 {
	    xv -= 1;
	} else if xv < 0 {
	    xv += 1;
	}
	if xv == 0 {
	    match (first_step_inside, last_step_inside) {
		(None, _) => return None,
		(Some(first), Some(last)) => {
		    if target.contains(&x) {
			return Some(first..usize::MAX);
		    } else {
			return Some(first..(last+1));
		    }
		}
		(Some(_), None) => unreachable!(),
	    }
	}
    }
    None
}

fn simulate_y<F: FnMut(usize, i32, i32, bool)>(
    _name: &str,
    mut yv: i32,
    target: &Range<i32>,
    mut observer: F,
) -> (i32, Option<Range<usize>>) {
    let initial_yv = yv;
    let mut y = 0;
    let mut first_step_inside: Option<usize> = None;
    let mut last_step_inside: Option<usize> = None;
    let mut highpoint = 0;
    for iter in 0.. {
	if y > highpoint {
	    highpoint = y;
	}
	let ontarget = target.contains(&y);
	event!(
	    Level::TRACE,
	    "simulate_y: iteration {:>3} initial_yv={}, y={}, yv={}, ontarget={}",
	    iter, initial_yv, y, yv, ontarget,
	);
	if y < target.start && yv < 0 {
	    // Below target and falling.
	    event!(
		Level::TRACE,
		"simulate_y: fell below target",
	    );
	    break;
	}
	observer(iter, y, yv, ontarget);
	if ontarget {
	    if first_step_inside.is_none() {
		first_step_inside = Some(iter);
	    }
	    last_step_inside = Some(iter);
	}
	y += yv;
	yv -= 1;
    }
    match (first_step_inside, last_step_inside) {
	(None, _) => (highpoint, None),
	(Some(first), Some(last)) => (highpoint, Some(first..(last+1))),
	_ => unreachable!(),
    }
}

fn ranges_intersect(a: &Range<usize>, b: &Range<usize>) -> bool {
    for i in a.clone() {
	if b.contains(&i) {	// this is very low-tech.
	    return true;
	}
    }
    false
}

fn simulate(name: &str, xv: i32, yv: i32, target: &Target) -> (bool, i32) {
    let x_wins = simulate_x(name, xv, &target.x);
    let mut hit_target = false;
    let observer = |step: usize, _y: i32, _yv: i32, ontarget: bool| {
	if let Some(wins) = x_wins.as_ref() {
	    if wins.contains(&step) && ontarget {
		hit_target = true;
	    }
	}
    };
    let (highpoint, _y_wins) = simulate_y(name, yv, &target.y, observer);
    (hit_target, highpoint)
}

#[test]
fn test_simulate() {
    let target = Target {
	x: 20..31,
	y: -10..-4
    };
    assert!(matches!(simulate("example1", 7, 2, &target),
		     (true, _)));
    assert!(matches!(simulate("example1", 6, 9, &target),
		     (true, 45)));
    assert!(matches!(simulate("wrong-way-1", -7, 2, &target),
		     (false, _)));
    assert!(matches!(simulate("overshoot-x", 1000, 2, &target),
		     (false, _)));
}


fn smallest_viable_x_velocity(target: &Target) -> Option<(i32, Range<usize>)> {
    for xv in 1.. {
	let name: String = format!("orig_xv={:>3}", xv);
	let x_wins = simulate_x(name.as_str(), xv, &target.x);
	match x_wins {
	    None => { continue; }
	    Some(r) if r.is_empty() => { continue; }
	    Some(r) => {
		return Some((xv, r));
	    }
	}
    }
    None
}

fn solve(target: &Target) -> Option<i32> {
    let span = span!(Level::ERROR, "solve for xv", target=?target);
    let _enter = span.enter();
    let (xv, x_wins): (i32, Range<usize>) = match smallest_viable_x_velocity(target) {
	None => {
	    return None;
	}
	Some((v, w)) => (v, w),
    };
    println!("minimum viable x velocity is {}", xv);

    let mut was_ever_on_target: bool = false;
    let mut highest: Option<i32> = None;
    for yv in 1.. {
        let span = span!(Level::ERROR, "solve for yv", trial_yv=%yv, target=?target);
        let _enter = span.enter();

	let orig_yv = yv;
	let observer = |step: usize, y: i32, _yv: i32, y_ontarget: bool| {
	    if y_ontarget && x_wins.contains(&step) {
		event!(
		    Level::DEBUG,
		    "for xv={}, yv={}, on-target at step {}",
		    xv,
		    orig_yv,
		    step,
		);
		was_ever_on_target = true;
	    }
	};
	match simulate_y("solve", yv, &target.y, observer) {
	    (highpoint, Some(y_wins)) => {
		if ranges_intersect(&x_wins, &y_wins) {
		    // We hit the target.  Because yv increases
		    // monotonically, so does
		    // highest_for_this_velocity.
		    event!(
			Level::DEBUG,
			"solve: for yv={}, x_wins={:?}, updating highest from {:?} to {}",
			yv,
			x_wins,
			highest,
			highpoint,
		    );
		    highest = Some(highpoint);
		}
	    }
	    (_, None) => {
		if was_ever_on_target {
		    event!(
			Level::INFO,
			"At initial y velocity {}, we never hit the target, so we're done (yv is too high)",
			orig_yv,
		    );
		    assert!(matches!(simulate("sanity-check", xv, orig_yv, target),
				     (false, _)));
		    break;
		}
	    }
	}
    }
    highest
}

#[test]
fn test_solve() {
    let target = Target {
	x: 20..31,
	y: -10..-4
    };
    assert_eq!(solve(&target), Some(45));
}

fn part1(t: &Target) {
    println!("Day 17 part 1: {:?}", solve(t));
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
