use std::collections::HashMap;
use std::collections::HashSet;
use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;
use std::num::ParseIntError;
use std::str::FromStr;

use ndarray::prelude::*;
use regex::Regex;
use tracing_subscriber::prelude::*;

const SAMPLE: &[&str] = &[
    "--- scanner 0 ---",
    "404,-588,-901",
    "528,-643,409",
    "-838,591,734",
    "390,-675,-793",
    "-537,-823,-458",
    "-485,-357,347",
    "-345,-311,381",
    "-661,-816,-575",
    "-876,649,763",
    "-618,-824,-621",
    "553,345,-567",
    "474,580,667",
    "-447,-329,318",
    "-584,868,-557",
    "544,-627,-890",
    "564,392,-477",
    "455,729,728",
    "-892,524,684",
    "-689,845,-530",
    "423,-701,434",
    "7,-33,-71",
    "630,319,-379",
    "443,580,662",
    "-789,900,-551",
    "459,-707,401",
    "",
    "--- scanner 1 ---",
    "686,422,578",
    "605,423,415",
    "515,917,-361",
    "-336,658,858",
    "95,138,22",
    "-476,619,847",
    "-340,-569,-846",
    "567,-361,727",
    "-460,603,-452",
    "669,-402,600",
    "729,430,532",
    "-500,-761,534",
    "-322,571,750",
    "-466,-666,-811",
    "-429,-592,574",
    "-355,545,-477",
    "703,-491,-529",
    "-328,-685,520",
    "413,935,-424",
    "-391,539,-444",
    "586,-435,557",
    "-364,-763,-893",
    "807,-499,-711",
    "755,-354,-619",
    "553,889,-390",
    "",
    "--- scanner 2 ---",
    "649,640,665",
    "682,-795,504",
    "-784,533,-524",
    "-644,584,-595",
    "-588,-843,648",
    "-30,6,44",
    "-674,560,763",
    "500,723,-460",
    "609,671,-379",
    "-555,-800,653",
    "-675,-892,-343",
    "697,-426,-610",
    "578,704,681",
    "493,664,-388",
    "-671,-858,530",
    "-667,343,800",
    "571,-461,-707",
    "-138,-166,112",
    "-889,563,-600",
    "646,-828,498",
    "640,759,510",
    "-630,509,768",
    "-681,-892,-333",
    "673,-379,-804",
    "-742,-814,-386",
    "577,-820,562",
    "",
    "--- scanner 3 ---",
    "-589,542,597",
    "605,-692,669",
    "-500,565,-823",
    "-660,373,557",
    "-458,-679,-417",
    "-488,449,543",
    "-626,468,-788",
    "338,-750,-386",
    "528,-832,-391",
    "562,-778,733",
    "-938,-730,414",
    "543,643,-506",
    "-524,371,-870",
    "407,773,750",
    "-104,29,83",
    "378,-903,-323",
    "-778,-728,485",
    "426,699,580",
    "-438,-605,-362",
    "-469,-447,-387",
    "509,732,623",
    "647,635,-688",
    "-868,-804,481",
    "614,-800,639",
    "595,780,-596",
    "",
    "--- scanner 4 ---",
    "727,592,562",
    "-293,-554,779",
    "441,611,-461",
    "-714,465,-776",
    "-743,427,-804",
    "-660,-479,-426",
    "832,-632,460",
    "927,-485,-438",
    "408,393,-506",
    "466,436,-512",
    "110,16,151",
    "-258,-428,682",
    "-393,719,612",
    "-211,-452,876",
    "808,-476,-593",
    "-575,615,604",
    "-485,667,467",
    "-680,325,-822",
    "-627,-443,-432",
    "872,-547,-609",
    "833,512,582",
    "807,604,487",
    "839,-516,451",
    "891,-625,532",
    "-652,-548,-490",
    "30,-46,-14",
    "",
];

/// All rotation transforms are an integer number of 90-degree
/// rotations about the origin (about some combination of axes).  All
/// rotations are 0 degrees, 90 degrees, 180 degrees or 270 degrees.
#[derive(Debug, PartialEq, Eq)]
struct Transform {
    matrix: Array2<i32>,	// column-major order.
}

#[derive(Debug)]
struct BadTransform(String);

///
/// The transform matrix looks like this:
///
/// | col 0  | col 1 | col 2 | col 3 |
/// | ------ | ----- | ----- | ----- |
/// |    r00 |   r01 |   r02 |    t0 |
/// |    r10 |   r11 |   r12 |    t1 |
/// |    r20 |   r21 |   r22 |    t2 |
/// |      0 |     0 |     0 |     1 |
///
/// For a pure rotation, t0==t1==t2==0.
impl Transform {
    const VALID_ROTATIONS: [u8; 4] = [0, 1, 2, 3];

    fn c_and_s(r: u8) -> Result<(i32, i32), BadTransform> {
	match r {
	    0 => Ok((1, 0)), // 0 degrees
	    1 => Ok((0, 1)), // 90 degrees
	    2 => Ok((-1, 0)), // 180 degrees
	    3 => Ok((0, -1)), // 270 degrees
	    _ => Err(BadTransform(format!("rotation values should be 0,1,2,3: {}", r))),
	}
    }

    fn try_from_rotations_translations(
	rotate: &[u8; 3],
	translate: &[i32; 3],
    ) -> Result<Transform, BadTransform> {
	// Using the mnemonics from
	// https://www.euclideanspace.com/maths/algebra/matrix/transforms/examples/index.htm
	let (cb, sb) = Transform::c_and_s(rotate[0])?;
	let (ch, sh) = Transform::c_and_s(rotate[1])?;
	let (ca, sa) = Transform::c_and_s(rotate[2])?;

	// The top-left portion of the transformation matrix is a 3x3
	// submatrix representing the rotation.  The right column
	// represents the translation and the bottom row is fixed.
	let matrix = array![
	    [ ch*ca, -ch*sa*cb+sh*sb,  ch*sa*sb+sh*cb, translate[0]],
	    [    sa,           ca*cb,          -ca*sb, translate[1]],
	    [-sh*ca,  sh*sa*cb+ch*sb, -sh*sa*sb+ch*cb, translate[2]],
	    [     0,               0,               0,            1]
	];
	Ok(Transform {
	    matrix,
	})
    }

    fn try_from_rotations(rotate: &[u8; 3]) -> Result<Transform, BadTransform> {
	Self::try_from_rotations_translations(rotate, &[0, 0, 0])
    }

    fn all_rotations() -> Vec<Transform> {
	let mut result = Vec::new();
	for rx in Self::VALID_ROTATIONS {
	    for ry in Self::VALID_ROTATIONS {
		for rz in Self::VALID_ROTATIONS {
		    result.push(Transform::try_from_rotations(&[rx, ry, rz])
				.expect("VALID_ROTATIONS should be valid"));
		}
	    }
	}
	result
    }
}

#[derive(Debug)]
struct TransformBuilder {
    rotations: Option<[u8; 3]>,
    translations: Option<[i32; 3]>,
}

impl TransformBuilder {
    fn new() -> TransformBuilder {
	TransformBuilder {
	    rotations: None,
	    translations: None,
	}
    }

    fn translate(&mut self, amounts: [i32; 3]) {
	self.translations = Some(amounts)
    }

    fn rotate(&mut self, amounts: [u8; 3]) -> Result<(), BadTransform> {
	if let Some(e) = amounts.iter()
	    .filter_map(|r| Transform::c_and_s(*r).err())
	    .next() {
		Err(e)
	    } else {
		self.rotations = Some(amounts);
		Ok(())
	    }
    }

    fn build(&self) -> Transform {
	const NO_ROTATIONS: [u8; 3] = [0, 0, 0];
	const NO_TRANSLATIONS: [i32; 3] = [0, 0, 0];
	let rotations: &[u8; 3] = self.rotations.as_ref().unwrap_or(&NO_ROTATIONS);
	let translations: &[i32; 3] = self.translations.as_ref().unwrap_or(&NO_TRANSLATIONS);
	match Transform::try_from_rotations_translations(rotations, translations) {
	    Ok(t) => t,
	    Err(e) => {
		panic!(
		    "unexpected error '{}' should have been prevented by TransformBuilder::rotate()",
		    e);
	    }
	}
    }
}

impl Display for BadTransform {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
	self.0.fmt(f)
    }
}

impl Error for BadTransform {}

impl Default for Transform {
    fn default() -> Transform {
	Transform {
	    matrix: Array2::zeros((4,4)),
	}
    }
}

/// We represent a point as a 4-vector whose last element is 1 in
/// order to make it convenient to apply a rotation and translation to
/// it by multiplication with a 4x4 matrix.  See explanation at
/// https://www.euclideanspace.com/maths/geometry/affine/matrix4x4/index.htm
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct Point {
    // coorrdinates is a column vector.  It has shape (1, 4).
    coordinates: Array2<i32>,
}

impl From<[i32; 3]> for Point {
    fn from(v: [i32; 3]) -> Point {
	let coordinates = array![
	    v[0], v[1], v[2], 1
	].insert_axis(Axis(1));
	Point {
	    coordinates,
	}
    }
}

#[test]
fn test_point_from() {
    let p = Point::from([6, 7, 8]);
    assert_eq!(p.coordinates[(0,0)], 6);
    assert_eq!(p.coordinates[(1,0)], 7);
    assert_eq!(p.coordinates[(2,0)], 8);
    assert_eq!(p.coordinates[(3,0)], 1); // fixed
}

impl Display for Point {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
	for (i, n) in self.coordinates.iter().take(3).enumerate() {
	    if i > 0 {
		f.write_str(",")?;
	    }
	    write!(f, "{}", n)?;
	}
	Ok(())
    }
}

#[test]
fn test_point_display() {
    let p = Point::from([1, 2, 3]);
    assert_eq!(&p.to_string(), "1,2,3");
}

impl Point {
    fn transform(&self, t: &Transform) -> Point {
	println!("{} * {} =", t.matrix, self.coordinates);
	let product: Array2<i32> = t.matrix.dot(&self.coordinates);
	println!("{}", product);
	Point {
	    coordinates: product,
	}
    }

    fn xyz(&self) -> Array1<i32> {
	let slice = s![0..3, 0..1]; // drops the extra `1`.
	self.coordinates.slice(slice).index_axis(Axis(1), 0).to_owned()
    }
}

#[test]
fn test_example() {
    let m = array![
	[1, 0, 0, 0],
	[0, 1, 0, 0],
	[0, 0, 1, 0],
	[0, 0, 0, 1]];
    let v1 = array![
	[4],
	[5],
	[6],
	[1]];
    let product1 = m.dot(&v1);
    println!("{} *\n{} =\n{}\n", m, v1, product1);
    let v2 = array![4, 5, 6, 1];
    let product2 = m.dot(&v2);
    println!("{} *\n{} =\n{}\n", m, v2, product2);

    assert_eq!(product1[(0,0)], 4);
    assert_eq!(product1[(1,0)], 5);
    assert_eq!(product1[(2,0)], 6);
    assert_eq!(product1[(3,0)], 1);
}



#[test]
fn test_point_transform() {
    let p = Point::from([-2, -3, 1]);
    let expected = Point::from([2, -1, 3]);
    let mut found: bool = false;
    for rx in 0..3 {
	for ry in 0..3 {
	    for rz in 0..3 {
		let t = Transform::try_from_rotations(&[rx, ry, rz])
		    .expect("test case should be valid");
		let p2 = p.transform(&t);
		println!("{}\n", &p2);
		if p2 == expected {
		    found = true;
		}
		println!("found={}\n", &found);
	    }
	}
    }
    assert!(found);
}

#[derive(Debug, PartialEq, Eq)]
enum PointConversionError {
    Int(String, ParseIntError),
    Fmt(String, String),
}

impl Display for PointConversionError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            PointConversionError::Int(s, e) => {
                write!(f, "failed to convert number '{}': {}", s, e)
            }
            PointConversionError::Fmt(line, msg) => {
                write!(f, "line '{}' has unexpected format: {}", line, msg)
            }
        }
    }
}

impl Error for PointConversionError {}

impl FromStr for Point {
    type Err = PointConversionError;
    fn from_str(s: &str) -> Result<Point, PointConversionError> {
        let mut values: Vec<Result<i32, ParseIntError>> = s.split(',')
	    .map(|s| s.parse())
	    .collect();
        let first_err: Option<&ParseIntError> = values
            .iter()
            .filter_map(|x: &Result<_, ParseIntError>| -> Option<&ParseIntError> {
                x.as_ref().err()
            })
                    .next();
        match (first_err, values.len()) {
            (None, 3) => {
		let getval = |r: &Result<i32, ParseIntError>| -> i32 {
		    *r.as_ref().unwrap()
		};
		values.push(Ok(1));
		Ok(Point {
                    coordinates: Array::from_iter(
			values.iter()
			    .map(getval))
			.insert_axis(Axis(1)),
		})
	    }
	    (Some(e), _) => Err(PointConversionError::Int(s.to_string(), e.clone())),
	    (None, n) if n > 3 => Err(PointConversionError::Fmt(
		s.to_string(), "too many ','".to_string())),
            (None, _) => Err(PointConversionError::Fmt(
		s.to_string(), "not enough ','".to_string())),
        }
    }
}

impl TryFrom<&str> for Point {
    type Error = PointConversionError;
    fn try_from(s: &str) -> Result<Point, PointConversionError> {
        Point::from_str(s)
    }
}

#[test]
fn test_parse_point() {
    assert_eq!(
        Ok(Point::from([1, 2, 3])),
        Point::from_str("1,2,3")
    );
    assert_eq!(
        Ok(Point::from([1, 2, 3])),
        Point::try_from("1,2,3")
    );
    assert_eq!(
        Ok(Point::from([1, -2, 3])),
        Point::try_from("1,-2,3")
    );

    assert!(Point::from_str("1,2,").is_err()); // missing value
    assert!(Point::from_str("1,2").is_err()); // missing field
    assert!(Point::from_str(",1,2,3").is_err()); // too many fields
    assert!(Point::from_str("1,antelope,3").is_err()); // not a number
    assert!(Point::from_str("1,2,3.3").is_err()); // floaing point not allowed
}

#[test]
fn test_point_xyz() {
    let p = Point::from([99, -200, 6]);
    let xyz = p.xyz();
    assert_eq!(xyz[0], 99);
    assert_eq!(xyz[1], -200);
    assert_eq!(xyz[2], 6);
}

struct ScannerReport {
    points: HashSet<Point>,
}


impl ScannerReport {
    fn compute_overlaps(&self, other: &ScannerReport) -> Vec<(Transform, HashSet<Point>)> {
	vec![
	    (Transform::default(), HashSet::new())
	]
    }
}

fn get_sample_scanner_reports() -> HashMap<i32, ScannerReport> {
    parse_input(SAMPLE).expect("valid sample input")
}


#[test]
fn test_computer_overlaps() {
    let sample = get_sample_scanner_reports();
    let report0 = sample.get(&0).expect("test input should have scanner 0");
    let report1 = sample.get(&1).expect("test input should have scanner 1");
    let overlaps = report0.compute_overlaps(&report1);
    match overlaps.as_slice() {
	[(_t, points)] => {
	    assert_eq!(points.len(), 12);
	}
	[] => {
	    panic!("expected one overlap, got none");
	}
	_ => {
	    panic!("expected one overlap, got {}", overlaps.len());
	}
    }
}



#[derive(Debug)]
struct BadInput(String);

impl Display for BadInput {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
	self.0.fmt(f)
    }
}

fn add_scanner_report(
    current_scanner_id: &mut Option<i32>,
    current_points: &mut HashSet<Point>,
    result: &mut HashMap<i32, ScannerReport>,
) -> Result<(), BadInput> {
    match (current_scanner_id.as_mut(), current_points.is_empty()) {
	(None, true) => Ok(()),	// nothing to do
	(None, false) => Err(BadInput(
	    "saw line containing a point before any scanner id header".to_string())),
	(Some(id), _) => {
	    result.insert(*id, ScannerReport {
		points: current_points.clone(),
	    });
	    *current_scanner_id = None;
	    current_points.clear();
	    Ok(())
	}
    }
}

fn parse_input(lines: &[&str]) -> Result<HashMap<i32, ScannerReport>, BadInput> {
    let mut result = HashMap::new();
    let mut current_points: HashSet<Point> = HashSet::new();
    let mut current_scanner_id: Option<i32> = None;
    const SEP_PATTERN: &str = r"^--- scanner (\d+) ---$";
    let sep_re = Regex::new(SEP_PATTERN).unwrap();

    for line in lines {
	if line.is_empty() {
	    continue;
	} else if let Some(cap) = sep_re.captures(line) {
	    if let Some(id_string) = cap.get(1) {
		match id_string.as_str().parse() {
		    Ok(n) => {
			add_scanner_report(
			    &mut current_scanner_id,
			    &mut current_points,
			    &mut result
			)?;
			current_scanner_id = Some(n);
			continue;
		    }
		    Err(e) => {
			return Err(BadInput(format!(
			    "non-decimal scanner id in line '{}': {}",
			    line,
			    e,
			)));
		    }
		}
	    } else {
		return Err(BadInput(format!(
		    "regex '{}' should have captured an id from '{}'",
		    SEP_PATTERN,
		    line,
		)));
	    }
	} else {
	    match Point::from_str(line) {
		Ok(point) => {
		    current_points.insert(point);
		}
		Err(e) => {
		    return Err(BadInput(format!("invalid point '{}': {}", line, e)));
		}
	    }
	}
    }
    if current_scanner_id.is_some() {
	add_scanner_report(
	    &mut current_scanner_id,
	    &mut current_points,
	    &mut result
	)?;
    }
    Ok(result)
}

fn solve1(_reports: &HashMap<i32, ScannerReport>) -> HashSet<Point> {
    HashSet::new()
}

//#[test]
//fn test_solve1() {
//    const EXPECTED_BEACONS: &[&str] = &[
//	"-892,524,684",
//	"-876,649,763",
//	"-838,591,734",
//	"-789,900,-551",
//	"-739,-1745,668",
//	"-706,-3180,-659",
//	"-697,-3072,-689",
//	"-689,845,-530",
//	"-687,-1600,576",
//	"-661,-816,-575",
//	"-654,-3158,-753",
//	"-635,-1737,486",
//	"-631,-672,1502",
//	"-624,-1620,1868",
//	"-620,-3212,371",
//	"-618,-824,-621",
//	"-612,-1695,1788",
//	"-601,-1648,-643",
//	"-584,868,-557",
//	"-537,-823,-458",
//	"-532,-1715,1894",
//	"-518,-1681,-600",
//	"-499,-1607,-770",
//	"-485,-357,347",
//	"-470,-3283,303",
//	"-456,-621,1527",
//	"-447,-329,318",
//	"-430,-3130,366",
//	"-413,-627,1469",
//	"-345,-311,381",
//	"-36,-1284,1171",
//	"-27,-1108,-65",
//	"7,-33,-71",
//	"12,-2351,-103",
//	"26,-1119,1091",
//	"346,-2985,342",
//	"366,-3059,397",
//	"377,-2827,367",
//	"390,-675,-793",
//	"396,-1931,-563",
//	"404,-588,-901",
//	"408,-1815,803",
//	"423,-701,434",
//	"432,-2009,850",
//	"443,580,662",
//	"455,729,728",
//	"456,-540,1869",
//	"459,-707,401",
//	"465,-695,1988",
//	"474,580,667",
//	"496,-1584,1900",
//	"497,-1838,-617",
//	"527,-524,1933",
//	"528,-643,409",
//	"534,-1912,768",
//	"544,-627,-890",
//	"553,345,-567",
//	"564,392,-477",
//	"568,-2007,-577",
//	"605,-1665,1952",
//	"612,-1593,1893",
//	"630,319,-379",
//	"686,-3108,-505",
//	"776,-3184,-501",
//	"846,-3110,-434",
//	"1135,-1161,1235",
//	"1243,-1093,1063",
//	"1660,-552,429",
//	"1693,-557,386",
//	"1735,-437,1738",
//	"1749,-1800,1813",
//	"1772,-405,1572",
//	"1776,-675,371",
//	"1779,-442,1789",
//	"1780,-1548,337",
//	"1786,-1538,337",
//	"1847,-1591,415",
//	"1889,-1729,1762",
//	"1994,-1805,1792",
//    ];
//
//    let reports = get_sample_scanner_reports();
//
//    let expected_beacons: HashSet<Point> = {
//	let mut result: HashSet<Point> = HashSet::new();
//	for bl in EXPECTED_BEACONS {
//	    result.insert(Point::from_str(bl).expect("valid expected test result"));
//	}
//	result
//    };
//    let got_beacons: HashSet<Point> = solve1(&reports);
//    assert_eq!(expected_beacons, got_beacons);
//}

fn part1(reports: &HashMap<i32, ScannerReport>) {
    let beacons = solve1(reports);
    println!("Day 19 part 1: {}", beacons.len());
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
    let ls: Vec<&str> = lines.iter().map(|s| s.as_str()).collect();
    match parse_input(&ls) {
	Err(e) => Err(e.to_string()),
	Ok(reports) => {
	    part1(&reports);
	    Ok(())
	}
    }
}

fn main() {
    if let Err(e) = run() {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}
