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

    impl SplitPoint {
	pub fn from_front_face(r: &Range3D, axis: &Axis) -> SplitPoint {
	    let axis_range: &Range<i32> = r.range(axis);
	    let cross_section: CrossSection = r.cross_section(axis);
	    SplitPoint {
		at: axis_range.start,
		cross_section,
	    }
	}

	pub fn from_back_face(r: &Range3D, axis: &Axis) -> SplitPoint {
	    let axis_range: &Range<i32> = r.range(axis);
	    let cross_section: CrossSection = r.cross_section(axis);
	    SplitPoint {
		at: axis_range.end,
		cross_section,
	    }
	}
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

    #[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
    pub enum Axis { X, Y, Z }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum Instruction {
        On(Range3D),
        Off(Range3D),
    }

    fn ranges_overlap(a: &Range<i32>, b: &Range<i32>) -> bool {
	a.contains(&b.start) || a.contains(&b.end) || b.contains(&a.start) || b.contains(&a.end)
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

	pub fn is_empty(&self) -> bool {
	    self.affects().is_empty()
	}

	pub fn count_points(&self) -> u64 {
	    self.affects().count_points()
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

	pub fn split(self, axis: &Axis, v: i32) -> (Option<Instruction>, Option<Instruction>) {
	    let on: bool = matches!(self, Instruction::On(_));
	    let make_instruction = |r: Range3D| -> Instruction {
		assert!(!r.is_empty(), "{:?} is empty", &r);
		if on {
		    Instruction::On(r)
		} else {
		    Instruction::Off(r)
		}
	    };
	    let (before, after) = match self {
		Instruction::On(r) | Instruction::Off(r) => r.split_on_axis(axis, v),
	    };
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
    use std::cmp::{min, Ordering};

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

    fn split_instructions_on_axis(
	mut instructions: Vec<Instruction>,
	axis: &Axis,
    ) -> Vec<Instruction> {
	println!("split_instructions_on_axis: axis {:?}, current instruction count {}", axis, instructions.len());
	for inst in &instructions {
	    assert!(!inst.is_empty());
	}

	// The basic idea behind creating split_points is that it
	// means we don't have to have a readonly borrow of
	// `instructions` which overlaps the loop below.
	let mut split_points: Vec<SplitPoint> = {
	    let capacity: usize = instructions.len().checked_mul(2).expect("no overflow");
	    let mut values: Vec<SplitPoint> = Vec::with_capacity(capacity);
	    values.extend(
		instructions.iter()
		    .flat_map(|inst| {
			let cuboid: &Range3D = inst.affects();
			// We generate two split points, being the front
			// and back faces (with respect to `axis`) of the
			// range of `inst`.
			let result = [
			    SplitPoint::from_front_face(cuboid, axis),
			    SplitPoint::from_back_face(cuboid, axis),
			];
			//println!("From range {:?} generated split points {:?}",
			//	 &cuboid, &result);
			result
		    })
	    );
	    values.sort_unstable();
	    values
	};


	let order_instructions_by_start = |a: &Instruction, b: &Instruction| -> Ordering {
	    order_by_start(a, b, axis)
	};
	let mut done: Vec<Instruction> = Vec::with_capacity(instructions.len());
	let mut disorder_from: usize = 0;
	while !instructions.is_empty() {
	    println!("split_instructions_on_axis: axis {:?}, remaining instructions {} ({} done), remaining split points {}",
		     axis, instructions.len(), done.len(), split_points.len());
	    if disorder_from < instructions.len() {
		// instructions are ordered by increasing `start` value.
		if let Some(slice) = instructions.get_mut(disorder_from..) {
		    //println!("Sorting instructions from posistion {}", disorder_from);
		    slice.sort_by(order_instructions_by_start);
		}
		disorder_from = instructions.len();
	    }
	    if let Some(split) = split_points.pop() {
		// Find the location of the first instruction whose
		// start is less than this split point.
		// partition_point assumes that all elements for which
		// the predicate is true are at the start of the
		// slice.
		//println!("Current spit point is {:?}\nThe top 20 instructions:", split);
		//for inst in instructions.iter().rev().take(20) {
		//    println!("{:?}", &inst);
		//}
		//println!("The bottom 5 instructions:");
		//for inst in instructions.iter().take(5) {
		//    println!("{:?}", &inst);
		//}
		let possible_intersections = compute_cutoff(
		    &instructions, |inst| inst.affects().range(axis).end < split.at);
		println!("Of {} total instructions, {} cannot intersect the split point {}",
			 instructions.len(), possible_intersections, split.at);
		if possible_intersections == instructions.len() {
		    // All instructions have a start which is less
		    // than this split point.  All remaining split
		    // points are at locations which are less than or
		    // equal to this split point.  Thus we just
		    // discard the current split point.
		} else {
		    let mut todo: Vec<Instruction> = instructions.drain(possible_intersections..).collect();
		    while let Some(inst) = todo.pop() {
			assert!(!inst.is_empty());

			let inst_points = inst.count_points();
			let inst_affected_cuboid = inst.affects();
			match relation_of_point_to_range(split.at, inst_affected_cuboid.range(axis)) {
			    PointLineRelation::Before => {
				// this instruction is wholly beyond
				// (ordinate values all higher or
				// equal) the plane of the split
				// rectangle.
				assert!(!inst.is_empty());
				done.push(inst);
			    }
			    PointLineRelation::Beyond => {
				// This instruction is closer to the origin than the split point,
				// so we will re-visit this instruction when we handle a split point
				// closer to the origin than the current one.
				// We are still making progress because we're going to discard this
				// split point.
				assert!(!inst.is_empty());
				disorder_from = min(instructions.len(), disorder_from); // instructions is now disordered.
				instructions.push(inst);
			    }
			    PointLineRelation::Within => {
				match inst_affected_cuboid.on_axis_at(axis, split.at) {
				    None => unreachable!(),
				    Some(cross_section) => {
					if cross_section.intersects(&split.cross_section) {
					    // We need to split this instruction.
					    // We know there must be a split because `split.at`
					    // is within the affected cuboid.
					    assert!(!inst.is_empty(),
						    "{:?} is empty", &inst);
					    match inst.split(axis, split.at) {
						// Result is (before, after).
						(None, None) => unreachable!(),
						(Some(_), None) => unreachable!(),
						(None, Some(after)) => {
						    assert!(!after.is_empty());
						    done.push(after);
						}
						(Some(before), Some(after)) => {
						    // The current split point is not smaller than all remaining
						    // split points.   So we know that `after` will not need to
						    // be further split.
						    assert!(!after.is_empty());
						    done.push(after);
						    // `before` may need to be further split by a later
						    // (smaller ordinate value) split.
						    assert!(!before.is_empty());
						    let new_point_count = before.count_points();
						    // Assert that we're making progress.
						    assert!(new_point_count < inst_points);
						    disorder_from = min(instructions.len(), disorder_from); // instructions is now disordered.
						    instructions.push(before);
						}
					    }
					} else {
					    // The plane of the split
					    // rectangle intersects this
					    // instruction, but the
					    // rectangle itself doesn't
					    // intersect the cuboid
					    // affected by this
					    // instruction.
					    //
					    // However, later splits may
					    // intersect this instruction,
					    // so we can't add it to
					    // `done`.
					    assert!(!inst.is_empty());
					    disorder_from = min(instructions.len(), disorder_from); // instructions is now disordered.
					    instructions.push(inst);
					}
				    }
				}
			    }
			}
		    }
		}
	    } else {
		if !instructions.is_empty() {
		    println!("surprisingly, no more split points left, but {} instructions.", instructions.len());
		}
		done.extend(instructions.drain(0..));
	    }
	}
	println!("No instructions remain to be processed, {} are done", done.len());
	done
    }

    #[test]
    fn test_split_instructions_on_axis() {
	let instructions: Vec<Instruction> = vec![
	    Instruction::On(Range3D { x: 64..96, y: -23166..1189, z: -25001..2694 }), // A
	    Instruction::On(Range3D { x: 54..93, y: -44801..-25805, z: -7741..7070 }) // B
	];
	let mut split = split_instructions_on_axis(instructions, &Axis::X);
	split.sort_by(order_instructions_fully);
	assert_eq!(
	    split,
	    vec![
		Instruction::On(Range3D { x: 54..64, y: -44801..-25805, z: -7741..7070 }), // part of B (low X)
		Instruction::On(Range3D { x: 64..93, y: -44801..-25805, z: -7741..7070 }), // part of B (high X)
		Instruction::On(Range3D { x: 64..93, y: -23166..1189, z: -25001..2694 }), // part of A (low X)
		Instruction::On(Range3D { x: 93..96, y: -23166..1189, z: -25001..2694 }), // part of A (high X)
	    ]
	);
    }

    fn split_into_nonoverlapping_instructions(mut instructions: Vec<Instruction>) -> Vec<Instruction> {
	for axis in &[Axis::X, Axis::Y, Axis::Z] {
	    instructions = split_instructions_on_axis(instructions, axis);
	    //println!("After splitting on axis {:?}:", &axis);
	    //for inst in instructions.iter() {
	    //	println!("{:?}", &inst);
	    //}
	}
	instructions
    }

    fn run(orig_instructions: &[Instruction]) -> u64 {
	let non_overlapping = split_into_nonoverlapping_instructions(orig_instructions.to_vec());
	println!("There are {} non-overlapping instructions", non_overlapping.len());
	0
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
