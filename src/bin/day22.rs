use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;

mod base {
    use core::ops::Range;
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

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct Range3D {
        pub x: Range<i32>,
        pub y: Range<i32>,
        pub z: Range<i32>,
    }

    pub fn crop_range(r: &Range<i32>) -> Option<Range<i32>> {
        let result = (max(-50, r.start))..(min(50, r.end));
        if result.is_empty() {
            None
        } else {
            Some(result)
        }
    }

    impl Range3D {
        pub fn intersect(&self, other: &Range3D) -> Range3D {
            Range3D {
                x: max(self.x.start, other.x.start)..min(self.x.end, other.x.end),
                y: max(self.y.start, other.y.start)..min(self.y.end, other.y.end),
                z: max(self.z.start, other.z.start)..min(self.z.end, other.z.end),
            }
        }
    }

    #[derive(Debug)]
    pub enum PointLineRelation {
        Before,
        Within,
        Beyond,
    }

    fn relation_of_point_to_range(val: i32, range: &Range<i32>) -> PointLineRelation {
        if range.start > val {
            PointLineRelation::Before
        } else if range.end <= val {
            PointLineRelation::Beyond
        } else {
            PointLineRelation::Within
        }
    }

    impl Range3D {
        fn is_empty(&self) -> bool {
            self.x.is_empty() || self.y.is_empty() || self.z.is_empty()
        }

	pub fn xlen(&self) -> u64 {
            (self.x.end - self.x.start)
                .try_into()
                .expect("x range should have a positive number of entries")
	}

	pub fn ylen(&self) -> u64 {
            (self.y.end - self.y.start)
                .try_into()
                .expect("y range should have a positive number of entries")
	}

	pub fn zlen(&self) -> u64 {
            (self.z.end - self.z.start)
                .try_into()
                .expect("z range should have a positive number of entries")
	}

	pub fn xy_cross_sectional_area(&self) -> u64 {
	    if self.is_empty() {
		0
	    } else {
		self.xlen() * self.ylen()
	    }
	}

        pub fn count_points(&self) -> u64 {
            if self.is_empty() {
                0
            } else {
                self.xy_cross_sectional_area() * self.zlen()
            }
        }

        /// Split a Range3D into (a, b) by x coordinate (i.e. cut it with a plane
        /// parallel to the y,z axes).
        /// a is the points having x <= xboundary
        /// b is the points having x > xboundary
        pub fn split_x(self, xboundary: i32) -> (Option<Range3D>, Option<Range3D>) {
            match relation_of_point_to_range(xboundary, &self.x) {
                PointLineRelation::Before => (None, Some(self)),
                PointLineRelation::Beyond => (Some(self), None),
                PointLineRelation::Within => (
                    Some(Range3D {
                        x: self.x.start..xboundary,
                        y: self.y.clone(),
                        z: self.z.clone(),
                    }),
                    Some(Range3D {
                        x: xboundary..self.x.end,
                        y: self.y,
                        z: self.z,
                    }),
                ),
            }
        }

        pub fn split_y(self, yboundary: i32) -> (Option<Range3D>, Option<Range3D>) {
            match relation_of_point_to_range(yboundary, &self.y) {
                PointLineRelation::Before => (None, Some(self)),
                PointLineRelation::Beyond => (Some(self), None),
                PointLineRelation::Within => (
                    Some(Range3D {
                        x: self.x.clone(),
                        y: self.y.start..yboundary,
                        z: self.z.clone(),
                    }),
                    Some(Range3D {
                        x: self.x,
                        y: yboundary..self.y.end,
                        z: self.z,
                    }),
                ),
            }
        }

        pub fn split_z(self, zboundary: i32) -> (Option<Range3D>, Option<Range3D>) {
            match relation_of_point_to_range(zboundary, &self.z) {
                PointLineRelation::Before => (None, Some(self)),
                PointLineRelation::Beyond => (Some(self), None),
                PointLineRelation::Within => (
                    Some(Range3D {
                        x: self.x.clone(),
                        y: self.y.clone(),
                        z: self.z.start..zboundary,
                    }),
                    Some(Range3D {
                        x: self.x,
                        y: self.y,
                        z: zboundary..self.z.end,
                    }),
                ),
            }
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
    fn test_range3d_split_x() {
        let r = Range3D {
            x: 5..10,
            y: 20..30,
            z: 50..90,
        };
        assert_eq!(r.clone().split_x(1000000), (Some(r), None));

        let r = Range3D {
            x: 5..10,
            y: 20..30,
            z: 50..90,
        };
        assert_eq!(r.clone().split_x(-1000000), (None, Some(r)));

        let r = Range3D {
            x: 5..10,
            y: 20..30,
            z: 50..90,
        };
        assert_eq!(
            r.clone().split_x(8),
            (
                Some(Range3D {
                    x: 5..8,
                    y: 20..30,
                    z: 50..90,
                }),
                Some(Range3D {
                    x: 8..10,
                    y: 20..30,
                    z: 50..90,
                })
            )
        );
    }

    #[test]
    fn test_range3d_split_y() {
        let r = Range3D {
            x: 20..30,
            y: 5..10,
            z: 50..90,
        };
        assert_eq!(r.clone().split_y(1000000), (Some(r), None));

        let r = Range3D {
            x: 20..30,
            y: 5..10,
            z: 50..90,
        };
        assert_eq!(r.clone().split_y(-1000000), (None, Some(r)));

        let r = Range3D {
            x: 20..30,
            y: 5..10,
            z: 50..90,
        };
        assert_eq!(
            r.clone().split_y(8),
            (
                Some(Range3D {
                    x: 20..30,
                    y: 5..8,
                    z: 50..90,
                }),
                Some(Range3D {
                    x: 20..30,
                    y: 8..10,
                    z: 50..90,
                })
            )
        );
    }

    #[test]
    fn test_range3d_split_z() {
        let r = Range3D {
            x: 20..30,
            y: 50..90,
            z: 5..10,
        };
        assert_eq!(r.clone().split_z(1000000), (Some(r), None));

        let r = Range3D {
            x: 20..30,
            y: 50..90,
            z: 5..10,
        };
        assert_eq!(r.clone().split_z(-1000000), (None, Some(r)));

        let r = Range3D {
            x: 20..30,
            y: 50..90,
            z: 5..10,
        };
        assert_eq!(
            r.clone().split_z(8),
            (
                Some(Range3D {
                    x: 20..30,
                    y: 50..90,
                    z: 5..8,
                }),
                Some(Range3D {
                    x: 20..30,
                    y: 50..90,
                    z: 8..10,
                })
            )
        );
    }

    #[test]
    fn test_crop3d() {
        assert_eq!(
            Range3D {
                x: -54112..-39298,
                y: -85059..-49293,
                z: -27449..7877
            }
            .crop(),
            None
        );
        assert_eq!(
            Range3D {
                x: -54112..39298,
                y: -85059..-19,
                z: 20..200
            }
            .crop(),
            Some(Range3D {
                x: -50..50,
                y: -50..-19,
                z: 20..50
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

    fn convert_to_range(pair: (i32, i32)) -> Result<Range<i32>, String> {
        if pair.0 <= pair.1 {
	    // The ranges in the input are inclusive (i.e. a..=b) but
	    // we use Range<i32> (i.e. a..(b+1)) to represent them.
            Ok((pair.0)..(pair.1 + 1))
        } else {
            Err(format!("inverted range {:?}", pair))
        }
    }

    fn parse_range(input: &str) -> IResult<&str, Range<i32>> {
        map_res(
            separated_pair(i32_parser, tag(".."), i32_parser),
            convert_to_range,
        )(input)
    }

    fn make_ranges(
        ranges: (
            Range<i32>,
            Range<i32>,
            Range<i32>,
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
                    x: -54112..-39297,
                    y: -85059..-49292,
                    z: -27449..7878
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

    pub trait CubeFlipper {
        fn count_cubes_on(&self) -> u64;
        fn obey(&mut self, instruction: &Instruction);
    }
}

mod part1 {
    use std::collections::HashSet;

    use super::base::*;

    pub struct Reactor {
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
        pub fn new() -> Reactor {
            Reactor {
                on: HashSet::with_capacity(101 * 101 * 101),
            }
        }
    }

    impl CubeFlipper for Reactor {
        fn count_cubes_on(&self) -> u64 {
            self.on.len() as u64
        }

        fn obey(&mut self, instruction: &Instruction) {
            match instruction {
                Instruction::On(range) => {
                    self.on.extend(all(range));
                }
                Instruction::Off(range) => self.on.retain(|p| !range.contains(p)),
            }
        }
    }
}

mod part2 {
    use core::ops::Range;

    use super::base::*;

    fn zrange(instructions: &[Instruction]) -> Option<Range<i32>> {
	let zmin: Option<i32> = instructions.iter().map(|inst| inst.affects().z.start).min();
	let zmax: Option<i32> = instructions.iter().map(|inst| inst.affects().z.end).max();
	match (zmin, zmax) {
	    (Some(zmin), Some(zmax)) => Some(zmin..zmax),
	    _ => None,
	}
    }

    fn run(instructions: &[Instruction]) -> u64 {
        let mut lit: Vec<Range3D> = Vec::new();
        let mut count: u64 = 0;
	todo!()
    }

    pub fn part2(instructions: &[Instruction]) {
        let count = run(instructions);
        // 272176456701857 is too low.
	//
        println!("Day 22 part 2: cubes lit: {}", count);
    }
}

use base::CubeFlipper;
use base::Instruction;

pub fn run_part<T: CubeFlipper>(part: i32, instructions: &[Instruction], reactor: &mut T) {
    let cropped: Vec<Instruction> = instructions.iter().filter_map(|inst| inst.crop()).collect();
    for instruction in &cropped {
        reactor.obey(instruction);
    }
    println!(
        "Day 22 part {}: {} cubes are on",
        part,
        reactor.count_cubes_on()
    );
}

fn run() -> Result<(), String> {
    let instructions: Vec<Instruction> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .map(|line| Instruction::from(line.as_str()))
        .collect();
    for instruction in &instructions {
        println!("{:?}", instruction);
    }
    let mut reactor1 = part1::Reactor::new();
    run_part(1, &instructions, &mut reactor1);

    part2::part2(&instructions);
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}
