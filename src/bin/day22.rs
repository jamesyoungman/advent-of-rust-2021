use core::ops::Range;

use std::cmp::{max, min};
#[cfg(test)]
use std::cmp::Ordering;
use std::io;
use std::io::prelude::*;
use std::str::FromStr;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, digit1},
    combinator::{map, map_res, opt, recognize},
    sequence::{delimited, preceded, separated_pair, tuple},
    IResult,
};

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
struct Range3D {
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

impl Range3D {
    /// Compute self - other.
    fn subtract(&self, other: &Range3D) -> Vec<Range3D> {
	let intersection = Range3D {
	    x: max(self.x.start, other.x.start)..min(self.x.end, other.x.end),
	    y: max(self.y.start, other.y.start)..min(self.y.end, other.y.end),
	    z: max(self.z.start, other.z.start)..min(self.z.end, other.z.end),
	};

	if intersection.is_empty() {
	    vec![self.clone()]
	} else {
	    [
		// Slice at right-angles to the X-axis first.
		// The part of self which is wholly to the left (-X) of other
		Range3D { x: self.x.start..intersection.x.start, y: self.y.clone(), z: self.z.clone() },
		// The part of self which is wholly to the right (+X) of other
		Range3D { x: intersection.x.end..self.x.end, y: self.y.clone(), z: self.z.clone() },

		// Slice at right-angles to the Y-axis second.
		Range3D { x: intersection.x.clone(), y: self.y.start..intersection.y.start, z: self.z.clone() },
		Range3D { x: intersection.x.clone(), y: intersection.y.end..self.y.end, z: self.z.clone() },

		// Slice at right-angles to the Z-axis last.
		Range3D { x: intersection.x.clone(), y: intersection.y.clone(), z: self.z.start..intersection.z.start, },
		Range3D { x: intersection.x.clone(), y: intersection.y.clone(), z: intersection.z.end..self.z.end, },
	    ].into_iter()
		.filter(|r| !r.is_empty())
		.collect()
	}
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

impl Range3D {
    fn is_empty(&self) -> bool {
        self.x.is_empty() || self.y.is_empty() || self.z.is_empty()
    }

    fn xlen(&self) -> u64 {
        (self.x.end - self.x.start)
            .try_into()
            .expect("x range should have a non-negative number of entries")
    }

    fn ylen(&self) -> u64 {
        (self.y.end - self.y.start)
            .try_into()
            .expect("y range should have a non-negative number of entries")
    }

    fn zlen(&self) -> u64 {
        (self.z.end - self.z.start)
            .try_into()
            .expect("z range should have a non-negative number of entries")
    }

    fn count_points(&self) -> u64 {
        if self.is_empty() {
            0
        } else {
	    self.xlen() * self.ylen() * self.zlen()
        }
    }

    fn crop(&self) -> Option<Range3D> {
	fn crop_range(r: &Range<i32>) -> Option<Range<i32>> {
	    let result = (max(-50, r.start))..(min(51, r.end));
	    if result.is_empty() {
		None
	    } else {
		Some(result)
	    }
	}

        if let Some(x) = crop_range(&self.x) {
            if let Some(y) = crop_range(&self.y) {
                if let Some(z) = crop_range(&self.z) {
                    return Some(Range3D { x, y, z });
                }
            }
        }
        None
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
            x: -50..51,
            y: -50..-19,
            z: 20..51
        })
    );
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Instruction {
    pub on: bool,		// otherwise off
    pub range: Range3D,
}

impl Instruction {
    fn count_points(&self) -> u64 {
	self.range.count_points()
    }

    fn subtract(&self, other: &Instruction) -> Vec<Instruction> {
	self.range.subtract(&other.range)
	    .into_iter()
	    .map(|r| Instruction {
		on: self.on,
		range: r,
	    })
	    .collect()
    }

    fn crop(&self) -> Option<Instruction> {
	self.range.crop().map(|range| Instruction {
	    on: self.on,
	    range,
	})
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

fn parse_instructions(input: &str) -> Vec<Instruction> {
    input.split_terminator('\n')
	.map(Instruction::from)
	.collect()
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
		.flat_map(|active: Instruction| active.subtract(inst)));
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
    split_into_nonoverlapping_instructions(instructions).iter()
	.map(Instruction::count_points)
	.sum()
}

fn part1(instructions: &[Instruction]) -> u64 {
    let cropped: Vec<Instruction> = instructions.iter().filter_map(|inst| inst.crop()).collect();
    count_on_cubes(&cropped)
}

fn part2(instructions: &[Instruction]) -> u64 {
    count_on_cubes(instructions)
}


fn run() -> Result<(), String> {
    let input: String = {
	let mut input: String = String::new();
	match io::stdin().read_to_string(&mut input) {
            Ok(_) => input,
            Err(e) => { return Err(e.to_string()); }
	}
    };
    let instructions: Vec<Instruction> = parse_instructions(input.as_str());

    let count1 = part1(&instructions);
    println!("Day 22 part 1: {}", count1);

    let count2 = part2(&instructions);
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
        assert_eq!(part1(&parse_instructions(TEST_INPUT)), 39);
        assert_eq!(part1(&parse_instructions(LARGER_TEST_INPUT)), 590_784);
        assert_eq!(part1(&parse_instructions(VERY_LARGE_TEST_INPUT)), 474_140);
    }

    #[test]
    fn part2_example() {
        assert_eq!(part2(&parse_instructions(TEST_INPUT)), 39);
        assert_eq!(
	    part2(&parse_instructions(VERY_LARGE_TEST_INPUT)),
	    2_758_514_936_282_235
        );
    }

    #[test]
    fn simple_counts() {
	let instructions = parse_instructions("on x=0..1,y=0..0,z=0..0");
	assert_eq!(&instructions,
		   &vec![
		       Instruction {
			   on: true,
			   range: Range3D {
			       x: 0..2,
			       y: 0..1,
			       z: 0..1,
			   }
		       }
		   ]);
	assert_eq!(instructions[0].count_points(), 2,
		   "{:?} should contain 2 cubes", &instructions[0]);
	assert_eq!(part2(&instructions), 2);
    }

    #[test]
    fn simple_examples() {
	assert_eq!(part2(&parse_instructions(r"on x=0..1,y=0..0,z=0..0
off x=0..0,y=-0..0,z=0..0")), 1);

	assert_eq!(part2(&parse_instructions(r"on x=0..1,y=0..1,z=0..1
off x=0..0,y=-0..0,z=0..0")), 7);
    }
}
