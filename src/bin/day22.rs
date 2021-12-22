use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;
use std::iter::Extend;

mod base {
    use core::ops::RangeInclusive;
    use std::cmp::{max, min};
    use std::str::FromStr;

    use nom::{
        branch::alt,
        bytes::complete::tag,
        character::complete::{char, digit1},
        combinator::{map, map_res, opt, recognize},
        sequence::{delimited, preceded, separated_pair, tuple},
        IResult,
    };

    #[derive(Debug, PartialEq, Eq, Hash)]
    pub struct Point(i32, i32, i32);

    impl Point {
        pub fn new(x: i32, y: i32, z: i32) -> Point {
            Point(x, y, z)
        }
    }

    #[derive(Debug, PartialEq, Eq)]
    pub struct Range3D {
        pub x: RangeInclusive<i32>,
        pub y: RangeInclusive<i32>,
        pub z: RangeInclusive<i32>,
    }

    pub fn crop_range(r: &RangeInclusive<i32>) -> Option<RangeInclusive<i32>> {
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

        pub fn crop(&self) -> Option<Range3D> {
            if let Some(x) = crop_range(&self.x) {
                if let Some(y) = crop_range(&self.y) {
                    if let Some(z) = crop_range(&self.z) {
                        return Some(Range3D { x, y, z });
                    }
                }
            }
            None
        }

        pub fn contains(&self, p: &Point) -> bool {
            self.x.contains(&p.0) && self.y.contains(&p.1) && self.z.contains(&p.2)
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
    pub enum Instruction {
        On(Range3D),
        Off(Range3D),
    }

    impl Instruction {
        pub fn new_state(&self) -> bool {
            match self {
                Instruction::On(_) => true,
                Instruction::Off(_) => false,
            }
        }

        pub fn affects(&self) -> &Range3D {
            match self {
                Instruction::On(r) | Instruction::Off(r) => r,
            }
        }

        pub fn crop(&self) -> Option<Instruction> {
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

    pub fn parse_instruction(input: &str) -> IResult<&str, Instruction> {
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

    impl From<&str> for Instruction {
        fn from(s: &str) -> Instruction {
            match parse_instruction(s) {
                Ok(("", instruction)) => instruction,
                Ok((tail, _)) => {
                    panic!("not matched: '{}'", tail);
                }
                Err(e) => {
                    panic!("failed: {}", e);
                }
            }
        }
    }
}

mod part1 {
    use std::collections::HashSet;

    use super::base::*;

    struct Reactor {
        on: HashSet<Point>,
    }

    fn all(range: &Range3D) -> HashSet<Point> {
        let mut result = HashSet::new();
        for x in range.x.clone() {
            for y in range.y.clone() {
                for z in range.z.clone() {
                    result.insert(Point::new(x, y, z));
                }
            }
        }
        result
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
                    self.on.extend(all(instruction.affects()));
                }
                Instruction::Off(range) => self.on.retain(|p| !range.contains(p)),
            }
        }
    }

    pub fn run(instructions: &[Instruction]) {
        let cropped: Vec<Instruction> =
            instructions.iter().filter_map(|inst| inst.crop()).collect();
        let mut reactor = Reactor::new();
        for instruction in &cropped {
            reactor.obey(instruction);
        }
        println!("Day 22 part 1: {} cubes are on", reactor.count_cubes_on());
    }
}

use base::Instruction;

fn run() -> Result<(), String> {
    let instructions: Vec<Instruction> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .map(|line| Instruction::from(line.as_str()))
        .collect();
    for instruction in &instructions {
        println!("{:?}", instruction);
    }
    part1::run(&instructions);
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}
