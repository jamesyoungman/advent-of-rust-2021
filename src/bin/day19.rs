use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;
use std::num::ParseIntError;
use std::str::FromStr;

use ndarray::prelude::*;
use tracing_subscriber::prelude::*;

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
    fn try_from_rotations_translations(
	rotate: &[u8; 3],
	translate: &[i32; 3],
    ) -> Result<Transform, BadTransform> {
	// Using the mnemonics from
	// https://www.euclideanspace.com/maths/algebra/matrix/transforms/examples/index.htm
	fn c_and_s(r: u8) -> Result<(i32, i32), BadTransform> {
	    match r {
		0 => Ok((1, 0)), // 0 degrees
		1 => Ok((0, 1)), // 90 degrees
		2 => Ok((-1, 0)), // 180 degrees
		3 => Ok((0, -1)), // 270 degrees
		_ => Err(BadTransform(format!("rotation values should be 0,1,2,3: {}", r))),
	    }
	}
	let (cb, sb) = c_and_s(rotate[0])?;
	let (ch, sh) = c_and_s(rotate[1])?;
	let (ca, sa) = c_and_s(rotate[2])?;

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
#[derive(Debug, PartialEq, Eq)]
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

    let _lines: Vec<String> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .collect();
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}
