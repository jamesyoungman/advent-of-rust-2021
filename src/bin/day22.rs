use core::ops::RangeInclusive;
use std::cmp::{max, min};
use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;
use std::iter::Extend;
use std::str::FromStr;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, digit1},
    combinator::{map, map_res, opt, recognize},
    sequence::{delimited, preceded, separated_pair, terminated, tuple},
    IResult,
};

#[derive(Debug, PartialEq, Eq, Hash)]
struct Point(i32, i32, i32);

#[derive(Debug, PartialEq, Eq)]
struct Range3D {
    x: RangeInclusive<i32>,
    y: RangeInclusive<i32>,
    z: RangeInclusive<i32>,
}

fn crop_range(r: &RangeInclusive<i32>) -> Option<RangeInclusive<i32>> {
    let result = (max(-50, *r.start()))..=(min(50, *r.end()));
    if result.is_empty() {
        None
    } else {
        Some(result)
    }
}

impl Range3D {
    fn is_empty(&self) -> bool {
        self.x.is_empty() || self.y.is_empty() || self.z.is_empty()
    }

    fn crop(&self) -> Option<Range3D> {
        if let Some(x) = crop_range(&self.x) {
            if let Some(y) = crop_range(&self.y) {
                if let Some(z) = crop_range(&self.z) {
                    return Some(Range3D { x, y, z });
                }
            }
        }
        None
    }

    fn contains(&self, p: &Point) -> bool {
        self.x.contains(&p.0) && self.y.contains(&p.1) && self.z.contains(&p.2)
    }

    fn all(&self) -> HashSet<Point> {
        let mut result = HashSet::new();
        for x in self.x.clone() {
            for y in self.y.clone() {
                for z in self.z.clone() {
                    result.insert(Point(x, y, z));
                }
            }
        }
        result
    }
}

#[test]
fn test_crop3d() {
    assert_eq!(
        Range3D {
            x: -54112..=-39298,
            y: -85059..=-49293,
            z: -27449..=7877
        }
        .crop(),
        None
    );
    assert_eq!(
        Range3D {
            x: -54112..=39298,
            y: -85059..=-19,
            z: 20..=200
        }
        .crop(),
        Some(Range3D {
            x: -50..=50,
            y: -50..=-19,
            z: 20..=50
        })
    );
}

#[derive(Debug, PartialEq, Eq)]
enum Instruction {
    On(Range3D),
    Off(Range3D),
}

impl Instruction {
    fn affects(&self) -> HashSet<Point> {
        match self {
            Instruction::On(r) | Instruction::Off(r) => r.all(),
        }
    }

    fn crop(&self) -> Option<Instruction> {
        match self {
            Instruction::On(r) => match r.crop() {
                None => None,
                Some(range) => Some(Instruction::On(range)),
            },
            Instruction::Off(r) => match r.crop() {
                None => None,
                Some(range) => Some(Instruction::Off(range)),
            },
        }
    }
}

fn i32_parser(input: &str) -> IResult<&str, i32> {
    map_res(
        recognize(tuple((opt(char('-')), digit1))),
        FromStr::from_str,
    )(input)
}

fn convert_to_range(pair: (i32, i32)) -> Result<RangeInclusive<i32>, String> {
    if pair.0 <= pair.1 {
        Ok((pair.0)..=(pair.1))
    } else {
        Err(format!("inverted range {:?}", pair))
    }
}

fn parse_range(input: &str) -> IResult<&str, RangeInclusive<i32>> {
    map_res(
        separated_pair(i32_parser, tag(".."), i32_parser),
        convert_to_range,
    )(input)
}

fn make_ranges(
    ranges: (
        RangeInclusive<i32>,
        RangeInclusive<i32>,
        RangeInclusive<i32>,
    ),
) -> Range3D {
    let (x, y, z) = ranges;
    Range3D { x, y, z }
}

fn parse_ranges(input: &str) -> IResult<&str, Range3D> {
    map(
        tuple((
            delimited(tag("x="), parse_range, tag(",")),
            delimited(tag("y="), parse_range, tag(",")),
            preceded(tag("z="), parse_range),
        )),
        make_ranges,
    )(input)
}

fn make_instruction(parts: (bool, Range3D)) -> Instruction {
    let (on, ranges) = parts;
    if on {
        Instruction::On(ranges)
    } else {
        Instruction::Off(ranges)
    }
}

fn parse_on(input: &str) -> IResult<&str, bool> {
    map(tag("on"), |_| true)(input)
}

fn parse_off(input: &str) -> IResult<&str, bool> {
    map(tag("off"), |_| false)(input)
}

fn parse_on_off(input: &str) -> IResult<&str, bool> {
    alt((parse_on, parse_off))(input)
}

fn parse_instruction(input: &str) -> IResult<&str, Instruction> {
    map(
        separated_pair(parse_on_off, tag(" "), parse_ranges),
        make_instruction,
    )(input)
}

#[test]
fn test_parse_instruction() {
    assert_eq!(
        parse_instruction("on x=-54112..-39298,y=-85059..-49293,z=-27449..7877"),
        Ok((
            "",
            Instruction::On(Range3D {
                x: -54112..=-39298,
                y: -85059..=-49293,
                z: -27449..=7877
            })
        ))
    );
}

fn line_to_instruction(line: &str) -> Instruction {
    match parse_instruction(line) {
        Ok(("", instruction)) => instruction,
        Ok((tail, _)) => {
            panic!("not matched: '{}'", tail);
        }
        Err(e) => {
            panic!("failed: {}", e);
        }
    }
}

struct Reactor {
    on: HashSet<Point>,
}

impl Reactor {
    fn new() -> Reactor {
        Reactor {
            on: HashSet::with_capacity(101 * 101 * 101),
        }
    }

    fn count_cubes_on(&self) -> usize {
        self.on.len()
    }

    fn obey(&mut self, instruction: &Instruction) {
        match instruction {
            Instruction::On(range) => {
                self.on.extend(instruction.affects());
            }
            Instruction::Off(range) => self.on.retain(|p| !range.contains(p)),
        }
    }
}

fn part1(instructions: &[Instruction]) {
    let cropped: Vec<Instruction> = instructions.iter().filter_map(|inst| inst.crop()).collect();
    let mut reactor = Reactor::new();
    for instruction in &cropped {
        reactor.obey(instruction);
    }
    println!("Day 22 part 1: {} cubes are on", reactor.count_cubes_on());
}

fn run() -> Result<(), String> {
    let instructions: Vec<Instruction> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .map(|line| line_to_instruction(line.as_str()))
        .collect();
    for instruction in &instructions {
        println!("{:?}", instruction);
    }
    part1(&instructions);
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}
