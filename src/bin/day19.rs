use std::cmp::{max, min};
use std::collections::HashMap;
use std::collections::HashSet;
use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;
use std::num::ParseIntError;
use std::ops::Sub;
use std::str::FromStr;

use ndarray::prelude::*;
use regex::Regex;
use tracing_subscriber::prelude::*;

const MIN_OVERLAPS: usize = 12;

#[cfg(test)]
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

trait Transform {
    fn transform(&self, p: &Point) -> Point;
    fn then(&self, t: &AffineTransform) -> TransformChain;
}

/// All rotation transforms are an integer number of 90-degree
/// rotations about the origin (about some combination of axes).  All
/// rotations are 0 degrees, 90 degrees, 180 degrees or 270 degrees.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
struct AffineTransform {
    matrix: Array2<i32>, // column-major order.

    rotation: [u8; 3],
    translation: [i32; 3],
}

#[derive(Debug)]
struct BadAffineTransform(String);

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
impl AffineTransform {
    //pub const ROTATION_MODULUS: u8 = 4;
    pub const VALID_ROTATIONS: [u8; 4] = [0, 1, 2, 3];

    fn c_and_s(r: u8) -> Result<(i32, i32), BadAffineTransform> {
        match r {
            0 => Ok((1, 0)),  // 0 degrees
            1 => Ok((0, 1)),  // 90 degrees
            2 => Ok((-1, 0)), // 180 degrees
            3 => Ok((0, -1)), // 270 degrees
            _ => Err(BadAffineTransform(format!(
                "rotation values should be 0,1,2,3: {}",
                r
            ))),
        }
    }

    fn try_from_rotations_translations(
        rotate: &[u8; 3],
        translate: &[i32; 3],
    ) -> Result<AffineTransform, BadAffineTransform> {
        // Using the mnemonics from
        // https://www.euclideanspace.com/maths/algebra/matrix/transforms/examples/index.htm
        let (cb, sb) = AffineTransform::c_and_s(rotate[0])?;
        let (ch, sh) = AffineTransform::c_and_s(rotate[1])?;
        let (ca, sa) = AffineTransform::c_and_s(rotate[2])?;

        // The top-left portion of the transformation matrix is a 3x3
        // submatrix representing the rotation.  The right column
        // represents the translation and the bottom row is fixed.
        let matrix = array![
            [
                ch * ca,
                -ch * sa * cb + sh * sb,
                ch * sa * sb + sh * cb,
                translate[0]
            ],
            [sa, ca * cb, -ca * sb, translate[1]],
            [
                -sh * ca,
                sh * sa * cb + ch * sb,
                -sh * sa * sb + ch * cb,
                translate[2]
            ],
            [0, 0, 0, 1]
        ];
        Ok(AffineTransform {
            matrix,
            rotation: rotate.to_owned(),
            translation: translate.to_owned(),
        })
    }

    fn rotation(&self) -> &[u8; 3] {
        &self.rotation
    }

    fn try_from_rotations(rotate: &[u8; 3]) -> Result<AffineTransform, BadAffineTransform> {
        Self::try_from_rotations_translations(rotate, &[0, 0, 0])
    }

    fn all_rotations() -> Vec<AffineTransform> {
        let mut result = Vec::new();
        for rx in Self::VALID_ROTATIONS {
            for ry in Self::VALID_ROTATIONS {
                for rz in Self::VALID_ROTATIONS {
                    result.push(
                        AffineTransform::try_from_rotations(&[rx, ry, rz])
                            .expect("VALID_ROTATIONS should be valid"),
                    );
                }
            }
        }
        result
    }
}

#[derive(Debug, Clone)]
struct TransformChain {
    transforms: Vec<AffineTransform>,
}

impl Transform for TransformChain {
    fn transform(&self, p: &Point) -> Point {
	self.transforms.iter().fold(p.clone(), |p, t| t.transform(&p))
    }
    fn then(&self, t: &AffineTransform) -> TransformChain {
	let mut transforms: Vec<AffineTransform> = Vec::with_capacity(
	    1 + self.transforms.len());
	transforms.push(t.clone());
	transforms.extend(self.transforms.clone());
	TransformChain {
	    transforms
	}
    }
}

#[derive(Debug)]
struct AffineTransformBuilder {
    rotations: Option<[u8; 3]>,
    translations: Option<[i32; 3]>,
}

impl AffineTransformBuilder {
    fn new() -> AffineTransformBuilder {
        AffineTransformBuilder {
            rotations: None,
            translations: None,
        }
    }

    fn translate(mut self, amounts: [i32; 3]) -> Self {
        self.translations = Some(amounts);
	self
    }

    fn rotate(mut self, amounts: &[u8; 3]) -> Result<Self, BadAffineTransform> {
        if let Some(e) = amounts
            .iter()
            .filter_map(|r| AffineTransform::c_and_s(*r).err())
            .next()
        {
            Err(e)
        } else {
            self.rotations = Some(amounts.clone());
            Ok(self)
        }
    }

    fn build(&self) -> AffineTransform {
        const NO_ROTATIONS: [u8; 3] = [0, 0, 0];
        const NO_TRANSLATIONS: [i32; 3] = [0, 0, 0];
        let rotations: &[u8; 3] = self.rotations.as_ref().unwrap_or(&NO_ROTATIONS);
        let translations: &[i32; 3] = self.translations.as_ref().unwrap_or(&NO_TRANSLATIONS);
        match AffineTransform::try_from_rotations_translations(rotations, translations) {
            Ok(t) => t,
            Err(e) => {
                panic!(
		    "unexpected error '{}' should have been prevented by AffineTransformBuilder::rotate()",
		    e);
            }
        }
    }
}

impl Display for BadAffineTransform {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Error for BadAffineTransform {}

impl Default for AffineTransform {
    fn default() -> AffineTransform {
        AffineTransform::try_from_rotations_translations(&[0, 0, 0], &[0, 0, 0]).unwrap()
    }
}

/// We represent a point as a 4-vector whose last element is 1 in
/// order to make it convenient to apply a rotation and translation to
/// it by multiplication with a 4x4 matrix.  See explanation at
/// https://www.euclideanspace.com/maths/geometry/affine/matrix4x4/index.htm
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Point {
    // coorrdinates is a column vector.  It has shape (1, 4).
    coordinates: Array2<i32>,
}

impl From<[i32; 3]> for Point {
    fn from(v: [i32; 3]) -> Point {
        let coordinates = array![v[0], v[1], v[2], 1].insert_axis(Axis(1));
        Point { coordinates }
    }
}

#[test]
fn test_point_from() {
    let p = Point::from([6, 7, 8]);
    assert_eq!(p.coordinates[(0, 0)], 6);
    assert_eq!(p.coordinates[(1, 0)], 7);
    assert_eq!(p.coordinates[(2, 0)], 8);
    assert_eq!(p.coordinates[(3, 0)], 1); // fixed
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
    fn origin() -> Point {
	Point::from([0, 0, 0])
    }

    fn translate(&self, translation: &Array2<i32>) -> Point {
	let mut result = &self.coordinates + translation;
	result[(3, 0)] = 1;
	Point {
	    coordinates: result
	}
    }

    fn xyz(&self) -> Array1<i32> {
        let slice = s![0..3, 0..1]; // drops the extra `1`.
        self.coordinates
            .slice(slice)
            .index_axis(Axis(1), 0)
            .to_owned()
    }
}

impl Transform for AffineTransform {
    fn transform(&self, p: &Point) -> Point {
	//println!("Applying transform {:?} to {}", self, &p);
	Point {
	    coordinates: self.matrix.dot(&p.coordinates),
	}
    }

    /// This is probably unnecessary since we could compute a matrix
    /// which combines two affine transformations.  But I don't want
    /// to take the time right now to debug that.
    fn then(&self, next: &AffineTransform) -> TransformChain {
	TransformChain {
	    transforms: vec![next.clone(), self.clone()],
	}
    }
}

#[test]
fn test_translate() {
    let origin = Point::from([0, 0, 0]);
    let a = origin.translate(&array![0, 0, 0, 0].insert_axis(Axis(1)));
    assert_eq!(a, origin);
}


impl Sub for &Point {
    type Output = Array2<i32>;
    fn sub(self, other: Self) -> Array2<i32> {
        &self.coordinates - &other.coordinates
    }
}

impl Sub for Point {
    type Output = Array2<i32>;
    fn sub(self, other: Self) -> Array2<i32> {
        (&self).sub(&other)
    }
}

//#[derive(Debug)]
//pub struct AxisAlignedBoundingBox {
//    pub min: Point,
//    pub max: Point,
//}
//
//impl AxisAlignedBoundingBox {
//    fn new(min: Point, max: Point) -> AxisAlignedBoundingBox {
//        AxisAlignedBoundingBox { min, max }
//    }
//
//    fn insert(&mut self, p: &Point) {
//        Zip::from(&mut self.min.coordinates)
//            .and(&p.coordinates)
//            .for_each(|curr_min, point| *curr_min = min(*curr_min, *point));
//        Zip::from(&mut self.max.coordinates)
//            .and(&p.coordinates)
//            .for_each(|curr_max, point| *curr_max = max(*curr_max, *point));
//    }
//
//    fn transform(&self, t: &AffineTransform) -> AxisAlignedBoundingBox {
//        let tmin = self.min.transform(t);
//        let mut result = AxisAlignedBoundingBox {
//            min: tmin.clone(),
//            max: tmin.clone(),
//        };
//        result.insert(&self.max.transform(t));
//        result
//    }
//}
//
//fn aabb_of_points<'a, I>(input: I) -> Option<AxisAlignedBoundingBox>
//where
//    I: IntoIterator<Item = &'a Point>,
//{
//    let mut it = input.into_iter();
//    let p = it.next()?;
//    let mut bb = AxisAlignedBoundingBox::new(p.clone(), p.clone());
//    for item in it {
//        bb.insert(&item);
//    }
//    Some(bb)
//}
//
//impl<'a> FromIterator<&'a Point> for Option<AxisAlignedBoundingBox> {
//    fn from_iter<I>(items: I) -> Option<AxisAlignedBoundingBox>
//    where
//        I: IntoIterator<Item = &'a Point>,
//    {
//        aabb_of_points(items)
//    }
//}

#[test]
fn test_example() {
    let m = array![[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]];
    let v1 = array![[4], [5], [6], [1]];
    let product1 = m.dot(&v1);
    println!("{} *\n{} =\n{}\n", m, v1, product1);
    let v2 = array![4, 5, 6, 1];
    let product2 = m.dot(&v2);
    println!("{} *\n{} =\n{}\n", m, v2, product2);

    assert_eq!(product1[(0, 0)], 4);
    assert_eq!(product1[(1, 0)], 5);
    assert_eq!(product1[(2, 0)], 6);
    assert_eq!(product1[(3, 0)], 1);
}

#[test]
fn test_point_transform() {
    let p = Point::from([-2, -3, 1]);
    let expected = Point::from([2, -1, 3]);
    let mut found: bool = false;
    for rx in 0..3 {
        for ry in 0..3 {
            for rz in 0..3 {
                let t = AffineTransform::try_from_rotations(&[rx, ry, rz])
                    .expect("test case should be valid");
                let p2 = t.transform(&p);
                if p2 == expected {
                    found = true;
                }
            }
        }
    }
    assert!(found);
}

#[derive(Debug, PartialEq, Eq)]
pub enum PointConversionError {
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
        let mut values: Vec<Result<i32, ParseIntError>> = s.split(',').map(|s| s.parse()).collect();
        let first_err: Option<&ParseIntError> = values
            .iter()
            .filter_map(|x: &Result<_, ParseIntError>| -> Option<&ParseIntError> {
                x.as_ref().err()
            })
            .next();
        match (first_err, values.len()) {
            (None, 3) => {
                let getval = |r: &Result<i32, ParseIntError>| -> i32 { *r.as_ref().unwrap() };
                values.push(Ok(1));
                Ok(Point {
                    coordinates: Array::from_iter(values.iter().map(getval)).insert_axis(Axis(1)),
                })
            }
            (Some(e), _) => Err(PointConversionError::Int(s.to_string(), e.clone())),
            (None, n) if n > 3 => Err(PointConversionError::Fmt(
                s.to_string(),
                "too many ','".to_string(),
            )),
            (None, _) => Err(PointConversionError::Fmt(
                s.to_string(),
                "not enough ','".to_string(),
            )),
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
    assert_eq!(Ok(Point::from([1, 2, 3])), Point::from_str("1,2,3"));
    assert_eq!(Ok(Point::from([1, 2, 3])), Point::try_from("1,2,3"));
    assert_eq!(Ok(Point::from([1, -2, 3])), Point::try_from("1,-2,3"));

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

#[derive(Debug)]
struct ScannerReport {
    points: Vec<Point>,
    //bb: Option<AxisAlignedBoundingBox>,
}

impl From<&[Point]> for ScannerReport {
    fn from(points: &[Point]) -> ScannerReport {
        //let bb: Option<AxisAlignedBoundingBox> = aabb_of_points(points.iter());
        ScannerReport {
	    points: points.to_vec(),
	    // bb
	}
    }
}

#[inline]
fn manhattan1(a: i32, b: i32) -> i64 {
    (max(a, b) - min(a, b)).into()
}

fn manhattan3(a: &Array1<i32>, b: &Array1<i32>) -> i64 {
    (0..3).map(|axis| manhattan1(a[axis], b[axis])).sum()
}


/// Find one or more transforms which transforms a into b.  In general
/// there will be more than one.  For example, where both points are
/// coincident at the origin, any rotation (or none) will do.
fn find_rotation(
    a: &Array2<i32>,
    b: &Array2<i32>
) -> Vec<AffineTransform> {
    let mut result = Vec::new();
    for t in AffineTransform::all_rotations() {
	let rotated = t.matrix.dot(b);
	if rotated == a {
	    result.push(t);
	}
    }
    result
}

fn compute_diff(a: &Point, b: &Point) -> Array2<i32> {
    let mut result = (&a.coordinates - &b.coordinates).to_owned();
    result[(3, 0)] = 1;
    result
}

impl ScannerReport {
    fn len(&self) -> usize {
	self.points.len()
    }

    fn point_set(&self) -> HashSet<Point> {
	self.points.iter().fold(
	    HashSet::new(),
	    |mut acc, p| {
		acc.insert(p.clone());
		acc
	    })
    }

    fn transform<T: Transform>(&self, t: &T) -> Vec<Point> {
        self.points
            .iter()
	    .map(|p| t.transform(p))
	    .collect()
    }

    //fn bounding_box(&self) -> Option<&AxisAlignedBoundingBox> {
    //    self.bb.as_ref()
    //}

    fn fingerprint_permutation(&self) -> Vec<(i64, usize, usize)> {
        let slice = s![0..3, 0..1]; // drops the extra `1`.
	let raw_values: Vec<Array1<i32>> = self.points.iter()
	    .map(|point| point.coordinates.slice(slice).index_axis(Axis(1), 0).to_owned())
	    .collect();
	let mut distances: Vec<(i64, usize, usize)> = Vec::new();
	for (i, a) in raw_values.iter().enumerate() {
	    for j in 0..i {
		let dist: i64 = manhattan3(a, &raw_values[j]);
		distances.push((dist, i, j))
	    }
	}
	distances.sort_unstable();
	distances
    }

    /// Convert a rotation which we believe maps diffs between
    /// locations in self and points into a full transform (rotation +
    /// translation) which actually does.  Or, if we cannot find one,
    /// return None.
    ///
    /// Because we accept a subset (of size >= `min_size`) of matching
    /// points as being sufficient, more than one translation may be
    /// accepted.  For example, if min_size is 1 and both sets of
    /// points have 2 members, there are two possible translations
    /// which map just one of the points onto another.
    ///
    /// The coordinates in `point` do not necessarily appear the same
    /// order as they appear in `self`.
    fn deduce_translation(
	&self,
	other: &ScannerReport,
	rotation: &AffineTransform,
	likely_equivalences: &[(usize, usize)],
	min_size: usize
    ) -> Vec<(AffineTransform, Vec<Point>)> {
	let rotated_points = other.transform(rotation);
	let mut diffs: HashMap<Array2<i32>, usize> = HashMap::new();
	for (my_index, their_index) in likely_equivalences {
	    let diff: Array2<i32> = compute_diff(
		&self.points[*my_index],
		&rotated_points[*their_index]
	    );
	    *diffs.entry(diff).or_insert(0) += 1;
	}

	diffs.into_iter()
	    .filter_map(|(diff, votes)| {
		//println!("{:>2} votes: {:?}", votes, diff);
		if votes >= min_size { Some(diff) } else { None }
	    })
	    .map(|diff| {
		AffineTransformBuilder::new()
		    .translate([diff[(0, 0)], diff[(1, 0)], diff[(2, 0)]])
		    .rotate(rotation.rotation()).expect("rotation should already be valid")
		    .build()
	    })
	    .map(|t| {
		let transformed: Vec<Point> = other.transform(&t);
		(t, transformed)
	    })
	    .collect()
    }

    fn compute_overlaps(
        &self,
        other: &ScannerReport,
        min_size: usize,
    ) -> Vec<(AffineTransform, Vec<Point>, Vec<Point>)> {
	assert!(self.len() > 1);
	assert!(other.len() > 1);
	let my_fingerprint = self.fingerprint_permutation();
	let their_fingerprint = other.fingerprint_permutation();

	fn pairs_by_distance(distances: &[(i64, usize, usize)]) -> HashMap<i64, Vec<(usize, usize)>> {
	    distances.iter()
		.fold(HashMap::new(),
		      |mut map, (d, i, j)| {
			  map.entry(*d).or_insert_with(Vec::new).push((*i, *j));
			  map
		      })
	}

	let mut my_distance = pairs_by_distance(my_fingerprint.as_slice());
	let mut their_distance = pairs_by_distance(their_fingerprint.as_slice());
	let mut distance_matches: HashMap<i64, (Vec<(usize, usize)>, Vec<(usize, usize)>)> = HashMap::new();
	for (d, my_pairs) in my_distance.drain() {
	    if let Some(their_pairs) = their_distance.remove(&d) {
		distance_matches.insert(d, (my_pairs,  their_pairs));
	    }
	}
	let mut transform_votes: HashMap<AffineTransform, usize> = HashMap::new();
	let mut likely_equivalences: Vec<(usize, usize)> = Vec::new();

	for (_d, (my_pairs, their_pairs)) in distance_matches.iter() {
	    if their_pairs.len() == 0 {
		continue;
	    }
	    for (my_i, my_j) in my_pairs {
		let my_diff = compute_diff(&self.points[*my_i], &self.points[*my_j]);

		for (their_i, their_j) in their_pairs {
		    let their_diff = compute_diff(&other.points[*their_i], &other.points[*their_j]);
		    let rotations = find_rotation(&my_diff, &their_diff);

		    if !rotations.is_empty() {
			likely_equivalences.push((*my_i, *their_i));
			likely_equivalences.push((*my_j, *their_j));
			for t in rotations {
			    *transform_votes.entry(t.clone()).or_insert(0) += 1;
			}
		    }
		}
	    }
	}

	let sufficient_diff_overlaps = |(t, votes): (AffineTransform, usize)| -> Option<AffineTransform> {
	    if votes >= min_size {
		Some(t)
	    } else {
		None
	    }
	};

	let overlaps: Vec<(AffineTransform, Vec<Point>)> = transform_votes.into_iter()
	    //.inspect(|(t, votes)| { println!("{:>2} votes: {:?}", votes, &t);})
	    .filter_map(sufficient_diff_overlaps)
	    .flat_map(|r| self.deduce_translation(other, &r, &likely_equivalences, min_size))
	    .collect();
	let mut result: Vec<(AffineTransform, Vec<Point>, Vec<Point>)> = Vec::with_capacity(
	    overlaps.len());
	for (transform, transformed_points) in overlaps {
	    let mut maybe_overlapping: HashMap<bool, Vec<Point>> = HashMap::with_capacity(2);
	    maybe_overlapping.insert(true, vec![]);
	    maybe_overlapping.insert(false, vec![]);
	    let my_points = self.point_set();
	    for p in transformed_points {
		let overlaps: bool = my_points.contains(&p);
		match maybe_overlapping.get_mut(&overlaps) {
		    Some(v) => { v.push(p); }
		    None => unreachable!(),
		}
	    }
	    let item: (AffineTransform, Vec<Point>, Vec<Point>) = (
		transform,
		maybe_overlapping.remove(&true).unwrap(),
		maybe_overlapping.remove(&false).unwrap(),
	    );
	    result.push(item);
	}
	result
    }
}

fn noop_transform() -> AffineTransform {
    AffineTransformBuilder::new().build()
}

/// Take a number of scanner reports.  Combine them.
fn combine_overlapping_reports(
    reports: &HashMap<i32, ScannerReport>,
    min_overlap_points: usize,
) -> HashMap<(i32, i32), AffineTransform> {
    let mut result: HashMap<(i32, i32), AffineTransform> = HashMap::new();
    let mut todo: Vec<(i32, &ScannerReport)> = reports.iter().map(|(id, rep)| (*id, rep)).collect();
    let seed_id: i32 = {
	if let Some(min_key) = todo.iter().map(|(id, _rep)| id).min() {
	    *min_key
	} else {
	    // No input at all.
	    return HashMap::new();
	}
    };
    let seed_pos = todo.iter()
	.enumerate()
	.filter_map(|(pos, (id, _))| {
	    if *id == seed_id {
		Some(pos)
	    } else {
		None
	    }
	})
	.next()
	.unwrap();
    let seed_report: &ScannerReport = todo.swap_remove(seed_pos).1;
    result.insert((seed_id, seed_id), noop_transform());
    let mut combined = ScannerReport {
	points: seed_report.points.clone(),
    };
    let mut already_combined: HashSet<Point> = HashSet::with_capacity(
	reports.values().map(|report| report.points.len()).sum());
    while !todo.is_empty() {
	println!("{} reports joined so far; {} to do; combined result has {} points so far",
		 result.len(), todo.len(), combined.points.len());
	let mut made_progress = false;
	let mut next_todo: Vec<(i32, &ScannerReport)> = Vec::with_capacity(todo.len());
	for (id, report) in todo.drain(0..) {
	    let mut overlaps = combined.compute_overlaps(report, min_overlap_points);
	    println!("There are {} overlap candidates with report {}", overlaps.len(), id);
	    for (i, (_t, over, other)) in overlaps.iter().enumerate() {
		println!("Candidate {} has {} overlaps and {} non-overlaps",
			 i, over.len(), other.len());
	    }
	    if let Some((transform, _overlapping_points, _non_overlapping_points)) = overlaps.pop() {
		println!("Joining report {} (which has {} points)", id, report.points.len());
		println!("Scanner {} is at position {} relative to scanner {}",
			 id, transform.transform(&Point::origin()), seed_id);
		for point in report.points.iter() {
		    let transformed = transform.transform(point);
		    if !already_combined.contains(&transformed) {
			already_combined.insert(transformed.clone());
			combined.points.push(transformed);
		    }
		}
		result.insert((seed_id, id), transform);
		made_progress = true;
	    } else {
		// We did not find an overlap yet, so try the next report;
		// add this one back into the to-do list.
		println!("Not yet able to join report {}", id);
		next_todo.push((id, report));
	    }
	}
	todo.extend(next_todo);
	if !made_progress {
	    let unjoinable_keys: Vec<_> = todo.iter().map(|(id, _)| *id).collect();
	    panic!("unable to join some reports: {:?}", unjoinable_keys);
	}
    }
    assert!(todo.is_empty());
    return result;
}

#[test]
fn test_combine_overlapping_reports() {
    let sample_reports: HashMap<i32, ScannerReport> = get_sample_scanner_reports();
    let combined = combine_overlapping_reports(&sample_reports, 12);
    println!("sample input: there are {} non-overlapping groups of reports", combined.len());
    for ((leader, follower), transform) in &combined {
	println!("Transform {}->{} is {:?}", leader, follower, &transform);
	println!("Scanner {} is at position {} relative to scanner {}",
		 follower, transform.transform(&Point::origin()), leader);
    }
    let expected_beacons: Vec<Point> = [
	"-892,524,684",
	"-876,649,763",
	"-838,591,734",
	"-789,900,-551",
	"-739,-1745,668",
	"-706,-3180,-659",
	"-697,-3072,-689",
	"-689,845,-530",
	"-687,-1600,576",
	"-661,-816,-575",
	"-654,-3158,-753",
	"-635,-1737,486",
	"-631,-672,1502",
	"-624,-1620,1868",
	"-620,-3212,371",
	"-618,-824,-621",
	"-612,-1695,1788",
	"-601,-1648,-643",
	"-584,868,-557",
	"-537,-823,-458",
	"-532,-1715,1894",
	"-518,-1681,-600",
	"-499,-1607,-770",
	"-485,-357,347",
	"-470,-3283,303",
	"-456,-621,1527",
	"-447,-329,318",
	"-430,-3130,366",
	"-413,-627,1469",
	"-345,-311,381",
	"-36,-1284,1171",
	"-27,-1108,-65",
	"7,-33,-71",
	"12,-2351,-103",
	"26,-1119,1091",
	"346,-2985,342",
	"366,-3059,397",
	"377,-2827,367",
	"390,-675,-793",
	"396,-1931,-563",
	"404,-588,-901",
	"408,-1815,803",
	"423,-701,434",
	"432,-2009,850",
	"443,580,662",
	"455,729,728",
	"456,-540,1869",
	"459,-707,401",
	"465,-695,1988",
	"474,580,667",
	"496,-1584,1900",
	"497,-1838,-617",
	"527,-524,1933",
	"528,-643,409",
	"534,-1912,768",
	"544,-627,-890",
	"553,345,-567",
	"564,392,-477",
	"568,-2007,-577",
	"605,-1665,1952",
	"612,-1593,1893",
	"630,319,-379",
	"686,-3108,-505",
	"776,-3184,-501",
	"846,-3110,-434",
	"1135,-1161,1235",
	"1243,-1093,1063",
	"1660,-552,429",
	"1693,-557,386",
	"1735,-437,1738",
	"1749,-1800,1813",
	"1772,-405,1572",
	"1776,-675,371",
	"1779,-442,1789",
	"1780,-1548,337",
	"1786,-1538,337",
	"1847,-1591,415",
	"1889,-1729,1762",
	"1994,-1805,1792",
    ].iter()
	.map(|s| Point::from_str(s).expect("valid input"))
	.collect();

    let mut all_points: HashSet<Point> = HashSet::new();
    for ((leader, follower), transform) in &combined {
	match sample_reports.get(follower) {
	    Some(report) => {
		for p in report.transform(transform) {
		    all_points.insert(p);
		}
	    }
	    None => {
		// This case is supposedly unreachable.
		panic!("bug: report {} overlaps {} but {} is not present in sample_reports", follower, leader, follower);
	    }
	}
    }
    println!("There are {} distinct points:", all_points.len());
    for p in all_points.iter() {
	println!("{}", p);
    }


    let same = same_points(&expected_beacons,
			   all_points.iter().cloned().collect::<Vec<_>>().as_slice());
    match same {
	Ok(()) => (),
	Err((only_left, common, only_right)) => {
	    println!("points only in expected_beacons: {}", only_left.len());
	    println!("points common to both: {}", common.len());
	    println!("points only in all_points: {}", only_right.len());

	    for x in only_left {
		println!("Expected but not found: {}", x);
	    }
	    for x in common {
		println!("Found, as expected: {}", x);
	    }
	    for x in only_right {
		println!("Unexpected: {}", x);
	    }
	    panic!("incorrect set of beacons");
	}
    }

}

fn unique_points(reports: &HashMap<i32, ScannerReport>) -> HashSet<Point> {
    let mut all_points: HashSet<Point> = HashSet::new();
    let mut combined = combine_overlapping_reports(&reports, MIN_OVERLAPS);
    for ((_, follower), transform) in combined.drain() {
	if let Some(report) = reports.get(&follower) {
	    for p in report.transform(&transform) {
		all_points.insert(p);
	    }
	} else {
	    // This case is supposedly unreachable.
	    panic!("bug: report {} is not present in the input", follower);
	}
    }
    all_points
}


#[test]
fn test_unique_points() {
    let sample_reports: HashMap<i32, ScannerReport> = get_sample_scanner_reports();
    let uniques = unique_points(&sample_reports);
    assert_eq!(uniques.len(), 79);
}

#[cfg(test)]
fn get_sample_scanner_reports() -> HashMap<i32, ScannerReport> {
    parse_input(SAMPLE).expect("valid sample input")
}

#[test]
fn test_compute_overlaps_trivial() {
    let report = parse_input(&[
        "--- scanner 0 ---",
        "1,2,3",
        "15,17,91",
        "--- scanner 1 ---",	// same points as scanner 0
        "1,2,3",
        "15,17,91",
    ])
    .expect("valid test data");
    let overlaps = report[&0].compute_overlaps(&report[&1], 1);
    assert!(overlaps.len() >= 1);
    for (_t, overlap_points, others) in overlaps.iter() {
        assert_eq!(overlap_points, &report[&0].points);
        assert_eq!(overlap_points, &report[&1].points);
	assert!(others.is_empty());
    }
}

#[cfg(test)]
fn show_overlaps(
    from: i32,
    to: i32,
    overlaps: &[(AffineTransform, Vec<Point>, Vec<Point>)]
) {
    for (i, (transform, _, _)) in overlaps.iter().enumerate() {
	let scanner1_origin = transform.transform(&Point::origin());
	println!(
	    "Overlap {0}: scanner {2} must be at {3} (relative to scanner {1})",
	    i,
	    from,
	    to,
	    scanner1_origin,
	);
    }
}

#[cfg(test)]
fn point_set(points: &[Point]) -> HashSet<Point> {
    points.iter()
	.fold(HashSet::with_capacity(points.len()),
	      |mut result, item| {
		  result.insert(item.clone());
		  result
	      })
}

#[cfg(test)]
fn same_points(
    left: &[Point],
    right: &[Point],
) -> Result<(), (Vec<Point>, Vec<Point>, Vec<Point>)> {
    let left_set = point_set(left);
    let right_set = point_set(right);
    let only_right: Vec<Point> = right.iter().filter(|r| !left_set.contains(r)).cloned().collect();
    let only_left: Vec<Point> = left.iter().filter(|l| !right_set.contains(l)).cloned().collect();
    let common: Vec<Point> = left.iter().filter(|l| right_set.contains(l)).cloned().collect();
    if only_left.is_empty() && only_right.is_empty() {
	Ok(())
    } else {
	Err((only_left, common, only_right))
    }
}

#[cfg(test)]
fn str_slice_to_points(s: &[&str]) -> Vec<Point> {
    s.iter()
	.map(|s| Point::from_str(s).expect("valid input"))
	.collect()
}

#[cfg(test)]
fn assert_same_points(
    label: &str,
    left: &[Point],
    right: &[Point],
) {
    let same = same_points(left, right);
    match same {
	Ok(()) => {
	    println!("assert_same_points: success: match for {}", label);
	}
	Err((only_left, common, only_right)) => {
	    println!("assert_same_points: failure: mismatch for {}", label);
	    for x in only_left {
		println!("Expected but not found: {}", x);
	    }
	    for x in common {
		println!("Common to both (as epected): {}", x);
	    }
	    for x in only_right {
		println!("Unexpected: {}", x);
	    }
	    panic!("incorrect set of points");
	}
    }
}

#[test]
fn test_compute_overlaps() {
    let sample = get_sample_scanner_reports();
    let report0 = sample.get(&0).expect("test input should have scanner 0");
    let report1 = sample.get(&1).expect("test input should have scanner 1");
    let report2 = sample.get(&2).expect("test input should have scanner 2");
    let report3 = sample.get(&3).expect("test input should have scanner 3");
    let report4 = sample.get(&4).expect("test input should have scanner 4");
    let overlaps = report0.compute_overlaps(&report1, MIN_OVERLAPS);
    // There are two rotations which map report1 onto report0.  One is
    // a half-turn around axis 1, the other is a half-turn around both
    // axis 0 and axis 2.  These are always equivalent.
    assert!(!overlaps.is_empty());
    show_overlaps(0, 1, &overlaps);
    let t01 = match overlaps.as_slice() {
	[(t,
	  scanner1_overlap_points_relative_to_0,
	  _scanner1_other_points_relative_to_0,
	), ..] => {
	    let scanner1_origin = t.transform(&Point::origin());
	    println!("test_compute_overlaps: scanner 1 is at {}", scanner1_origin);
	    assert_eq!(scanner1_origin, Point::from([68, -1246, -43]));
	    let expected_scanner1_overlap_points: Vec<Point> =
		str_slice_to_points(&[
		    "-618,-824,-621",
		    "-537,-823,-458",
		    "-447,-329,318",
		    "404,-588,-901",
		    "544,-627,-890",
		    "528,-643,409",
		    "-661,-816,-575",
		    "390,-675,-793",
		    "423,-701,434",
		    "-345,-311,381",
		    "459,-707,401",
		    "-485,-357,347",
		]);
	    assert_same_points("scanner 1",
			       &expected_scanner1_overlap_points,
			       scanner1_overlap_points_relative_to_0);
	    t
	}
	[] => {
	    panic!("there should be an overlap between 0 and 1");
	}
    };

    let overlaps = report1.compute_overlaps(&report4, MIN_OVERLAPS);
    assert!(!overlaps.is_empty());
    show_overlaps(1, 4, &overlaps);
    let (t04, t14) = match overlaps.as_slice() {
	[(t14, scanner4_overlap_points_relative_to_1, _nonoverlap_points), ..] => {
	    let expected_scanner4_origin_as_seen_from_0 = Point::from([-20, -1133, 1061]);
	    println!("Computing scanner 4 origin with respect to 0, MANUALLY...");
	    let scanner4_origin = // from 0's point of view.
		t01.transform(
		    &t14.transform(
			&Point::origin()
		    )
		);
	    assert_eq!(scanner4_origin,
		       expected_scanner4_origin_as_seen_from_0,
		       "manual transform stack 4->0 is wrong");
	    println!("Computing scanner 4 origin with respect to 0, with THEN...");
	    let t04 = t01.then(&t14);
	    let scanner4_origin = t04.transform(&Point::origin());
	    assert_eq!(scanner4_origin, Point::from([-20, -1133, 1061]),
		       "transform stack using then() for 4->0 is wrong");
	    println!("test_compute_overlaps: scanner 4 is at {}", scanner4_origin);

	    let scanner4_overlap_points_relative_to_0: Vec<Point> =
		scanner4_overlap_points_relative_to_1.iter()
		.map(|p| t01.transform(&p))
		.collect();
	    let expected_scanner4_overlap_points: Vec<Point> = str_slice_to_points(&[
		"459,-707,401",
		"-739,-1745,668",
		"-485,-357,347",
		"432,-2009,850",
		"528,-643,409",
		"423,-701,434",
		"-345,-311,381",
		"408,-1815,803",
		"534,-1912,768",
		"-687,-1600,576",
		"-447,-329,318",
		"-635,-1737,486"]);
	    assert_same_points("scanner 4",
			       &expected_scanner4_overlap_points,
			       &scanner4_overlap_points_relative_to_0);
	    (t04, t14)
	}
	[] => {
	    panic!("there should be an overlap between 1 and 4");
	}
    };

    let overlaps = report4.compute_overlaps(&report2, MIN_OVERLAPS);
    assert!(!overlaps.is_empty());
    show_overlaps(4, 2, &overlaps);
    let (_t02, _t42) = match overlaps.as_slice() {
	[(t42, _overlap_points, _nonoverlap_points), ..] => {
	    let expected_scanner2_origin_as_seen_from_0 = Point::from([1105, -1205, 1229]);
	    println!("Computing scanner 4 origin with respect to 0, MANUALLY...");
	    let scanner2_origin = // from 0's point of view
		t01.transform(
		    &t14.transform(
			&t42.transform(
			    &Point::origin())));
	    assert_eq!(scanner2_origin,
		       expected_scanner2_origin_as_seen_from_0,
		       "manual transform stack 2->0 is wrong");
	    println!("Computing scanner 4 origin with respect to 0, with THEN...");
	    let t02 = t04.then(&t42);
	    let scanner2_origin = t02.transform(&Point::origin());
	    assert_eq!(scanner2_origin,
		       expected_scanner2_origin_as_seen_from_0,
		       "transform stack using then for 2->0 is wrong");
	    println!("test_compute_overlaps: scanner 2 is at {}", scanner2_origin);
	    (t02, t42)
	}
	[] => {
	    panic!("there should be an overlap between 4 and 2");
	}
    };

    let overlaps = report1.compute_overlaps(&report3, MIN_OVERLAPS);
    assert!(!overlaps.is_empty());
    show_overlaps(1, 3, &overlaps);
    match overlaps.as_slice() {
	[(t13, _overlap_points, _nonoverlap_points), ..] => {
	    let expected_scanner3_origin_as_seen_from_0 = Point::from([-92, -2380, -20]);
	    println!("Computing scanner 3 origin with respect to 0, MANUALLY...");
	    let scanner3_origin = // from 0's point of view
		t01.transform(
		    &t13.transform(
			&Point::origin()));
	    assert_eq!(scanner3_origin,
		       expected_scanner3_origin_as_seen_from_0,
		       "manual transform stack 3->0 is wrong");
	    println!("Computing scanner 3 origin with respect to 0, with THEN...");
	    let t03 = t01.then(&t13);
	    let scanner3_origin = t03.transform(&Point::origin());
	    assert_eq!(scanner3_origin,
		       expected_scanner3_origin_as_seen_from_0,
		       "transform stack using then 3->0 is wrong");
	    println!("test_compute_overlaps: scanner 3 is at {}", scanner3_origin);
	}
	[] => {
	    panic!("there should be an overlap between 1 and 3");
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
    current_points: &mut Vec<Point>,
    result: &mut HashMap<i32, ScannerReport>,
) -> Result<(), BadInput> {
    match (current_scanner_id.as_mut(), current_points.is_empty()) {
        (None, true) => Ok(()), // nothing to do
        (None, false) => Err(BadInput(
            "saw line containing a point before any scanner id header".to_string(),
        )),
        (Some(id), _) => {
            result.insert(*id, ScannerReport::from(current_points.as_slice()));
            *current_scanner_id = None;
            current_points.clear();
            Ok(())
        }
    }
}

fn parse_input(lines: &[&str]) -> Result<HashMap<i32, ScannerReport>, BadInput> {
    let mut result = HashMap::new();
    let mut current_points: Vec<Point> = Vec::new();
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
                            &mut result,
                        )?;
                        current_scanner_id = Some(n);
                        continue;
                    }
                    Err(e) => {
                        return Err(BadInput(format!(
                            "non-decimal scanner id in line '{}': {}",
                            line, e,
                        )));
                    }
                }
            } else {
                return Err(BadInput(format!(
                    "regex '{}' should have captured an id from '{}'",
                    SEP_PATTERN, line,
                )));
            }
        } else {
            match Point::from_str(line) {
                Ok(point) => {
                    current_points.push(point);
                }
                Err(e) => {
                    return Err(BadInput(format!("invalid point '{}': {}", line, e)));
                }
            }
        }
    }
    if current_scanner_id.is_some() {
        add_scanner_report(&mut current_scanner_id, &mut current_points, &mut result)?;
    }
    Ok(result)
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
    let beacons = unique_points(reports);
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
