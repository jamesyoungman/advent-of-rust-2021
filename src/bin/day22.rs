
use std::io;
use std::io::prelude::*;

mod base {
    use core::ops::Range;
    use std::cmp::{max, min, Ordering};
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

    #[derive(Debug, PartialEq, Eq, Clone, Hash)]
    pub struct Range3D {
        pub x: Range<i32>,
        pub y: Range<i32>,
        pub z: Range<i32>,
    }

    #[cfg(test)]
    impl Ord for Range3D {
	fn cmp(&self, other: &Range3D) -> Ordering {
	    fn rangecmp(left: &Range<i32>, right: &Range<i32>) -> Ordering {
		match left.start.cmp(&right.start) {
		    Ordering::Equal => left.end.cmp(&right.end),
		    unequal => unequal,
		}
	    }
	    match rangecmp(&self.x, &other.x) {
		Ordering::Equal => match rangecmp(&self.y, &other.y) {
		    Ordering::Equal => rangecmp(&self.z, &other.z),
		    unequal => unequal,
		},
		unequal => unequal,
	    }
	}
    }

    #[cfg(test)]
    impl PartialOrd for Range3D {
	fn partial_cmp(&self, other: &Range3D) -> Option<Ordering> {
	    Some(self.cmp(other))
	}
    }

    pub fn crop_range(r: &Range<i32>) -> Option<Range<i32>> {
        let result = (max(-50, r.start))..(min(50, r.end));
        if result.is_empty() {
            None
        } else {
            Some(result)
        }
    }

    pub fn range_intersects(a: &Range<i32>, b: &Range<i32>) -> bool {
	if a.end <= a.start {
	    false
	} else if a.start >= b.end {
	    false
	} else {
	    true
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

	pub fn intersects(&self, other: &Range3D) -> bool {
	    !self.intersect(other).is_empty()
	}

	pub fn contains_range(&self, other: &Range3D) -> bool {
	    self.x.contains(&other.x.start) &&
		self.x.contains(&(other.x.end - 1)) &&
		self.y.contains(&other.y.start) &&
		self.y.contains(&(other.y.end - 1)) &&
		self.z.contains(&other.z.start) &&
		self.z.contains(&(other.z.end - 1))
	}

	/// Compute self - other.
	pub fn subtract(&self, other: &Range3D) -> Vec<Range3D> {
	    let result = if !self.intersects(other) {
		vec![self.clone()]
	    } else {
		vec![
		    // The part of self which is wholly to the left (-X) of other
		    Range3D { x: self.x.start..other.x.start, y: self.y.clone(), z: self.z.clone(), },
		    // The part of self which is wholly to the right (+X) of other
		    Range3D { x: other.x.end..self.x.end, y: self.y.clone(), z: self.z.clone(), },

		    // Similarly for Y
		    Range3D { x: self.x.clone(), y: self.y.start..other.y.start, z: self.z.clone(), },
		    Range3D { x: self.x.clone(), y: other.y.end..self.y.end, z: self.z.clone(), },

		    // And for Y
		    Range3D { x: self.x.clone(), y: self.y.clone(), z: self.z.start..other.z.start, },
		    Range3D { x: self.x.clone(), y: self.y.clone(), z: other.z.end..self.z.end, },
		].into_iter()
		    .enumerate()
		    .filter(|(_, r)| !r.is_empty())
		    .inspect(|(i, r)| {
			// Postconditions:
			// 1. no output Range3D can overlap with any part of `other`.
			// 2. no output Range3D object can contain any cube not
			//    contained in `self`.
			assert!(!r.intersects(other),
				"postcondition failed ({}) for ({:?}-{:?}): expected {:?} to be disjoint from {:?}",
				i, self, other, r, other);
			assert!(self.contains_range(r),
				"postcondition failed ({}) for ({:?}0{:?}): expected {:?} to contain {:?}",
				i, self, other, self, r);
		    })
		    .map(|(_, r)| r)
		    .collect()
	    };
	    result
	}
    }

    #[test]
    fn test_subtract_a_within_b() {
	let a = Range3D {
	    x: 10..12,
	    y: 10..12,
	    z: 10..12,
	};
	let b = Range3D {
	    x: 0..20,
	    y: 0..20,
	    z: 0..20,
	};
	assert_eq!(a.subtract(&b), vec![]);
    }

    #[test]
    fn test_subtract_x_only() {
	let a = Range3D {
	    x: 10..20,
	    y: 10..20,
	    z: 10..20,
	};
	// remainder on the -X side only
	assert_eq!(a.subtract(&Range3D {
	    x: 11..100,
	    y: -100..100,
	    z: -100..100,
	}), vec![
	    Range3D {
		x: 10..11,
		y: 10..20,
		z: 10..20,
	    }]);
	// remainder on the +X side only
	assert_eq!(a.subtract(&Range3D {
	    x: -100..11,
	    y: -100..100,
	    z: -100..100,
	}), vec![
	    Range3D {
		x: 11..20,
		y: 10..20,
		z: 10..20,
	    }]);

	// remainder on both -X and +X sides.
	fn sorted(mut input: Vec<Range3D>) -> Vec<Range3D> {
	    input.sort();
	    input
	}
	assert_eq!(
	    sorted(a.subtract(&Range3D {
		x: 12..16,
		y: -100..100,
		z: -100..100,
	    })),
	    sorted(
		vec![
		    Range3D {
			x: 10..12,
			y: 10..20,
			z: 10..20,
		    },
		    Range3D {
			x: 16..20,
			y: 10..20,
			z: 10..20,
		    }
		]
	    ));
    }

    #[derive(Debug)]
    pub enum PointLineRelation {
        Before,
        Within,
        Beyond,
    }

    pub fn relation_of_point_to_range(val: i32, range: &Range<i32>) -> PointLineRelation {
        if range.start > val {
            PointLineRelation::Before
        } else if range.end <= val {
            PointLineRelation::Beyond
        } else {
            PointLineRelation::Within
        }
    }

    /// CrossSection represents an axis-aligned rectangle.  That is, a
    /// rectangle in the X-Y plane, the Y-Z plane, or the X-Z plane.
    #[derive(Debug, Clone, Eq)]
    pub struct CrossSection {
	first: Range<i32>,
	second: Range<i32>,
    }

    impl CrossSection {
	fn new(first: Range<i32>, second: Range<i32>) -> CrossSection {
	    CrossSection {
		first,
		second,
	    }
	}

	pub fn intersects(&self, other: &CrossSection) -> bool {
	    range_intersects(&self.first, &other.first) || range_intersects(&self.second, &other.second)
	}
    }

    impl PartialEq for CrossSection {
	fn eq(&self, other: &CrossSection) -> bool {
	    fn range_eq(a: &Range<i32>, b: &Range<i32>) -> bool {
		a.start == b.start && a.end == b.end
	    }
	    range_eq(&self.first, &other.first) && range_eq(&self.second, &other.second)
	}
    }

    // A SplitPoint is an axis-aligned rectangle at a specific
    // position on an axis.  The first tuple member specifies the
    // axis position and the second tuple member specifies the
    // rectangle.
    #[derive(Debug, Clone, Eq)]
    pub struct SplitPoint {
	pub at: i32,
	pub cross_section: CrossSection,
    }

    /// We want to maintain a binary heap of SplitPoint values ordered
    /// by axis position.  We don't need them to be ordered by their
    /// cross_section attribute.
    impl Ord for SplitPoint {
	fn cmp(&self, other: &SplitPoint) -> Ordering {
	    self.at.cmp(&other.at)
	}
    }

    impl PartialOrd for SplitPoint {
	fn partial_cmp(&self, other: &SplitPoint) -> Option<Ordering> {
	    Some(self.cmp(other))
	}
    }

    impl PartialEq for SplitPoint {
	fn eq(&self, other: &SplitPoint) -> bool {
	    self.cmp(other) == Ordering::Equal
	}
    }

    impl Range3D {
        fn is_empty(&self) -> bool {
            self.x.is_empty() || self.y.is_empty() || self.z.is_empty()
        }

	pub fn range(&self, axis: &Axis) -> &Range<i32> {
	    match axis {
		Axis::X => &self.x,
		Axis::Y => &self.y,
		Axis::Z => &self.z,
	    }
	}

	pub fn cross_section(&self, axis: &Axis) -> CrossSection {
	    let axis_range = |ax: Axis| -> Range<i32> {
		self.range(&ax).clone()
	    };
	    match axis {
		Axis::X => CrossSection::new(axis_range(Axis::Y), axis_range(Axis::Z)),
		Axis::Y => CrossSection::new(axis_range(Axis::X), axis_range(Axis::Z)),
		Axis::Z => CrossSection::new(axis_range(Axis::X), axis_range(Axis::Y)),
	    }
	}

	pub fn on_axis_at(&self, axis: &Axis, value: i32) -> Option<CrossSection> {
	    let r = self.range(axis);
	    if !r.contains(&value) {
		None
	    } else {
		Some(self.cross_section(axis))
	    }
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

	pub fn split_on_axis(self, axis: &Axis, boundary: i32) -> (Option<Range3D>, Option<Range3D>) {
	    fn kill_if_empty(r: Option<Range3D>) -> Option<Range3D> {
		match r {
		    None => None,
		    Some(range) if !range.is_empty() => Some(range),
		    Some(_) => None,
		}
	    }
	    fn kill_empty_pair_items(pair: (Option<Range3D>, Option<Range3D>)) -> (Option<Range3D>, Option<Range3D>) {
		(kill_if_empty(pair.0), kill_if_empty(pair.1))
	    }
	    kill_empty_pair_items(
		match axis {
		    Axis::X => self.split_x(boundary),
		    Axis::Y => self.split_y(boundary),
		    Axis::Z => self.split_z(boundary),
		}
	    )
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

        pub fn contains_point(&self, p: &Point) -> bool {
            self.x.contains(&p.0) && self.y.contains(&p.1) && self.z.contains(&p.2)
        }
    }

    #[test]
    fn count_points() {
        let r = Range3D {
            x: 5..10,
            y: 20..30,
            z: 50..90,
        };
	assert_eq!(r.count_points(), 5*10*40);
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

    #[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
    pub enum Axis { X, Y, Z }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct Instruction {
	pub on: bool,		// otherwise off
	pub range: Range3D,
    }

    fn ranges_overlap(a: &Range<i32>, b: &Range<i32>) -> bool {
	a.contains(&b.start) || a.contains(&b.end) || b.contains(&a.start) || b.contains(&a.end)
    }

    impl Instruction {
        pub fn new_state(&self) -> bool {
	    self.on
        }

        pub fn affects(&self) -> &Range3D {
	    &self.range
        }

	pub fn is_empty(&self) -> bool {
	    self.range.is_empty()
	}

	pub fn count_points(&self) -> u64 {
	    self.range.count_points()
	}

	pub fn subtract(&self, other: &Instruction) -> Vec<Instruction> {
	    self.range.subtract(&other.range)
		.into_iter()
		.map(|r| Instruction {
		    on: self.on,
		    range: r,
		})
		.collect()
	}

        pub fn crop(&self) -> Option<Instruction> {
	    match self.range.crop() {
		None => None,
		Some(range) => Some(Instruction {
		    on: self.on,
		    range,
		}),
	    }
	}

	pub fn split(self, axis: &Axis, v: i32) -> (Option<Instruction>, Option<Instruction>) {
	    let make_instruction = |r: Range3D| -> Instruction {
		Instruction {
		    on: self.on,
		    range: r,
		}
	    };
	    let (before, after) = self.range.split_on_axis(axis, v);
	    (before.map(make_instruction), after.map(make_instruction))
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
        let (on, range) = parts;
	Instruction {
	    on,
	    range,
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
                Instruction {
		    on: true,
		    range: Range3D {
			x: -54112..-39297,
			y: -85059..-49292,
			z: -27449..7878
                    },
		}
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

    pub fn parse_instructions(input: &str) -> Vec<Instruction> {
	input.split_terminator('\n')
	    .map(|line| Instruction::from(line))
	    .collect()
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
	    if instruction.on {
                self.on.extend(all(&instruction.range));
	    } else {
		self.on.retain(|p| !instruction.range.contains_point(p));
	    }
	}
    }

    pub fn part1(instructions: &[Instruction]) -> u64 {
	let cropped: Vec<Instruction> = instructions.iter().filter_map(|inst| inst.crop()).collect();
	let mut reactor = Reactor::new();
	for instruction in &cropped {
            reactor.obey(instruction);
	}
        reactor.count_cubes_on()
    }
}

mod part2 {
    use core::ops::Range;
    use std::cmp::Ordering;

    use super::base::*;

    fn compute_cutoff<F>(
	instructions: &[Instruction],
	pred: F
    ) -> usize
    where
	F: FnMut(&Instruction) -> bool
    {
	let result = instructions.partition_point(pred);
	#[cfg(debug)]
	for (i, inst) in instructions.iter().enumerate() {
	    if i < result {
		assert!(pred(inst));
	    } else {
		assert!(!pred(inst));
	    }
	}
	result
    }

    fn val_range(instructions: &[Instruction], axis: &Axis) -> Option<Range<i32>> {
	let min_val: Option<i32> = instructions.iter().map(|inst| inst.affects().range(axis).start).min();
	let max_val: Option<i32> = instructions.iter().map(|inst| inst.affects().range(axis).end).max();
	match (min_val, max_val) {
	    (Some(the_min), Some(the_max)) => Some(the_min..the_max),
	    _ => None,
	}
    }

    fn axis_values(instructions: &[Instruction], axis: &Axis) -> Vec<i32> {
	let mut result: Vec<i32> = Vec::with_capacity(instructions.len().checked_mul(2).expect("no overflow"));
	for r in instructions.iter().map(|inst| inst.affects().range(axis)) {
	    result.push(r.start);
	    result.push(r.end);
	}
	result.sort_unstable();
	result
    }

    fn order_by_start(a: &Instruction, b: &Instruction, axis: &Axis) -> Ordering {
	let a_front = a.affects().range(axis).start;
	let b_front = b.affects().range(axis).start;
	a_front.cmp(&b_front)
    }

    #[cfg(test)]
    fn order_instructions_fully(a: &Instruction, b: &Instruction) -> Ordering {
	match order_by_start(a, b, &Axis::X) {
	    Ordering::Equal => match order_by_start(a, b, &Axis::Y) {
		Ordering::Equal => order_by_start(a, b, &Axis::Z),
		unequal => unequal,
	    }
	    unequal => unequal,
	}
    }

    fn split_into_nonoverlapping_instructions(instructions: &[Instruction]) -> Vec<Instruction> {
	// Invariant: active_instructions contains no pair of
	// instructions with overlapping ranges.
	let mut active_instructions = Vec::with_capacity(instructions.len());
	let mut new_active = Vec::with_capacity(instructions.len());

	// At the beginning of the loop, the invariant holds because
	// active_instructions is empty.
	for inst in instructions {
	    new_active.clear();
	    // To preserve the invariant on `active_instructions` we
	    // have to establish it on `new_active`.
	    //
	    // The output of Instruction::subtract() must cover no
	    // cube beyond those covered by `self`.
	    new_active.extend(
		active_instructions.drain(0..)
		    .flat_map(|active: Instruction| active.subtract(&inst)));
	    // If that property of subtract() holds, the invariant is
	    // upheld for `new_active`.
	    if inst.on {
		// If we also require that none of the values returned
		// by a.subtract(b) overlaps b, then this modification
		// to `new_active` upholds its invariant.
		new_active.push(inst.clone());
	    }
	    // Now we replace the content of `active_instructions`
	    // with the content of `new_active`: if the invariant held
	    // in `new_active` it will then hold in
	    // `active_instructions`.
	    active_instructions.clear();
	    active_instructions.extend(new_active.drain(0..));
	}
	active_instructions
    }

    fn count_on_cubes(instructions: &[Instruction]) -> u64 {
	let active = split_into_nonoverlapping_instructions(instructions);
	println!("There are {} non-overlapping instructions to light cubes", active.len());
	active.iter()
	    .inspect(|inst| { assert!(inst.on); })
	    .map(|inst| inst.count_points())
	    .sum()
    }

    pub fn part2(instructions: &[Instruction]) -> u64 {
        let count = count_on_cubes(&instructions);
        //     272176456701857 is too low.
	//    2454065225612984 is too high.
	//    8442461386225739 is too high
	// 4496341296119187436 is also too high.
	count
    }
}

use base::Instruction;

fn run() -> Result<(), String> {
    let input: String = {
	let mut input: String = String::new();
	match io::stdin().read_to_string(&mut input) {
            Ok(_) => input,
            Err(e) => { return Err(e.to_string()); }
	}
    };
    let instructions: Vec<Instruction> = base::parse_instructions(input.as_str());

    let count1 = part1::part1(&instructions);
    println!("Day 22 part 1: {}", count1);

    let count2 = part2::part2(&instructions);
    println!("Day 22 part 2: {}", count2);
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_input(input: &str) -> Vec<Instruction> {
	base::parse_instructions(input)
    }

    static TEST_INPUT: &str = r"on x=10..12,y=10..12,z=10..12
on x=11..13,y=11..13,z=11..13
off x=9..11,y=9..11,z=9..11
on x=10..10,y=10..10,z=10..10";

    static LARGER_TEST_INPUT: &str = r"on x=-20..26,y=-36..17,z=-47..7
on x=-20..33,y=-21..23,z=-26..28
on x=-22..28,y=-29..23,z=-38..16
on x=-46..7,y=-6..46,z=-50..-1
on x=-49..1,y=-3..46,z=-24..28
on x=2..47,y=-22..22,z=-23..27
on x=-27..23,y=-28..26,z=-21..29
on x=-39..5,y=-6..47,z=-3..44
on x=-30..21,y=-8..43,z=-13..34
on x=-22..26,y=-27..20,z=-29..19
off x=-48..-32,y=26..41,z=-47..-37
on x=-12..35,y=6..50,z=-50..-2
off x=-48..-32,y=-32..-16,z=-15..-5
on x=-18..26,y=-33..15,z=-7..46
off x=-40..-22,y=-38..-28,z=23..41
on x=-16..35,y=-41..10,z=-47..6
off x=-32..-23,y=11..30,z=-14..3
on x=-49..-5,y=-3..45,z=-29..18
off x=18..30,y=-20..-8,z=-3..13
on x=-41..9,y=-7..43,z=-33..15
on x=-54112..-39298,y=-85059..-49293,z=-27449..7877
on x=967..23432,y=45373..81175,z=27513..53682";

    static VERY_LARGE_TEST_INPUT: &str = r"on x=-5..47,y=-31..22,z=-19..33
on x=-44..5,y=-27..21,z=-14..35
on x=-49..-1,y=-11..42,z=-10..38
on x=-20..34,y=-40..6,z=-44..1
off x=26..39,y=40..50,z=-2..11
on x=-41..5,y=-41..6,z=-36..8
off x=-43..-33,y=-45..-28,z=7..25
on x=-33..15,y=-32..19,z=-34..11
off x=35..47,y=-46..-34,z=-11..5
on x=-14..36,y=-6..44,z=-16..29
on x=-57795..-6158,y=29564..72030,z=20435..90618
on x=36731..105352,y=-21140..28532,z=16094..90401
on x=30999..107136,y=-53464..15513,z=8553..71215
on x=13528..83982,y=-99403..-27377,z=-24141..23996
on x=-72682..-12347,y=18159..111354,z=7391..80950
on x=-1060..80757,y=-65301..-20884,z=-103788..-16709
on x=-83015..-9461,y=-72160..-8347,z=-81239..-26856
on x=-52752..22273,y=-49450..9096,z=54442..119054
on x=-29982..40483,y=-108474..-28371,z=-24328..38471
on x=-4958..62750,y=40422..118853,z=-7672..65583
on x=55694..108686,y=-43367..46958,z=-26781..48729
on x=-98497..-18186,y=-63569..3412,z=1232..88485
on x=-726..56291,y=-62629..13224,z=18033..85226
on x=-110886..-34664,y=-81338..-8658,z=8914..63723
on x=-55829..24974,y=-16897..54165,z=-121762..-28058
on x=-65152..-11147,y=22489..91432,z=-58782..1780
on x=-120100..-32970,y=-46592..27473,z=-11695..61039
on x=-18631..37533,y=-124565..-50804,z=-35667..28308
on x=-57817..18248,y=49321..117703,z=5745..55881
on x=14781..98692,y=-1341..70827,z=15753..70151
on x=-34419..55919,y=-19626..40991,z=39015..114138
on x=-60785..11593,y=-56135..2999,z=-95368..-26915
on x=-32178..58085,y=17647..101866,z=-91405..-8878
on x=-53655..12091,y=50097..105568,z=-75335..-4862
on x=-111166..-40997,y=-71714..2688,z=5609..50954
on x=-16602..70118,y=-98693..-44401,z=5197..76897
on x=16383..101554,y=4615..83635,z=-44907..18747
off x=-95822..-15171,y=-19987..48940,z=10804..104439
on x=-89813..-14614,y=16069..88491,z=-3297..45228
on x=41075..99376,y=-20427..49978,z=-52012..13762
on x=-21330..50085,y=-17944..62733,z=-112280..-30197
on x=-16478..35915,y=36008..118594,z=-7885..47086
off x=-98156..-27851,y=-49952..43171,z=-99005..-8456
off x=2032..69770,y=-71013..4824,z=7471..94418
on x=43670..120875,y=-42068..12382,z=-24787..38892
off x=37514..111226,y=-45862..25743,z=-16714..54663
off x=25699..97951,y=-30668..59918,z=-15349..69697
off x=-44271..17935,y=-9516..60759,z=49131..112598
on x=-61695..-5813,y=40978..94975,z=8655..80240
off x=-101086..-9439,y=-7088..67543,z=33935..83858
off x=18020..114017,y=-48931..32606,z=21474..89843
off x=-77139..10506,y=-89994..-18797,z=-80..59318
off x=8476..79288,y=-75520..11602,z=-96624..-24783
on x=-47488..-1262,y=24338..100707,z=16292..72967
off x=-84341..13987,y=2429..92914,z=-90671..-1318
off x=-37810..49457,y=-71013..-7894,z=-105357..-13188
off x=-27365..46395,y=31009..98017,z=15428..76570
off x=-70369..-16548,y=22648..78696,z=-1892..86821
on x=-53470..21291,y=-120233..-33476,z=-44150..38147
off x=-93533..-4276,y=-16170..68771,z=-104985..-24507";

    #[test]
    fn part1_example() {
        assert_eq!(part1::part1(&parse_input(TEST_INPUT)), 39);
        assert_eq!(part1::part1(&parse_input(LARGER_TEST_INPUT)), 590_784);
        assert_eq!(part1::part1(&parse_input(VERY_LARGE_TEST_INPUT)), 474_140);
    }

    #[test]
    fn part2_example() {
        assert_eq!(part2::part2(&parse_input(TEST_INPUT)), 39);
        assert_eq!(
	    part2::part2(&parse_input(VERY_LARGE_TEST_INPUT)),
	    2_758_514_936_282_235
        );
    }
}
