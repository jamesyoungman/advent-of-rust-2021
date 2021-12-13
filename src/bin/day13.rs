use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;
use std::num::ParseIntError;

#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Hash, Clone)]
struct Point {
    x: i32,
    y: i32,
}

impl Point {
    fn transform(&self, fold: &Fold) -> Point {
        match fold {
            Fold::X(x) => {
                if self.x < *x {
                    self.clone()
                } else {
                    Point {
                        x: 2 * x - self.x,
                        y: self.y,
                    }
                }
            }
            Fold::Y(y) => {
                if self.y < *y {
                    self.clone()
                } else {
                    Point {
                        x: self.x,
                        y: 2 * y - self.y,
                    }
                }
            }
        }
    }
}

#[test]
fn test_transform() {
    assert_eq!(
        Point { x: 10, y: 6 }.transform(&Fold::Y(5)),
        Point { x: 10, y: 4 }
    );
    assert_eq!(
        Point { x: 6, y: 10 }.transform(&Fold::X(5)),
        Point { x: 4, y: 10 }
    );
}

impl Display for Point {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({},{})", self.x, self.y)
    }
}

fn show_points<'a, I>(points: I)
where
    I: Iterator<Item = &'a Point>,
{
    for point in points {
        println!("{}", point);
    }
}

impl TryFrom<(&str, &str)> for Point {
    type Error = ParseIntError;
    fn try_from(xy: (&str, &str)) -> Result<Point, ParseIntError> {
        match (xy.0.parse(), xy.1.parse()) {
            (Err(e), _) | (_, Err(e)) => Err(e),
            (Ok(x), Ok(y)) => Ok(Point { x, y }),
        }
    }
}

enum Fold {
    X(i32),
    Y(i32),
}

impl Display for Fold {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (indicator, value) = match self {
            Fold::X(x) => ('x', x),
            Fold::Y(y) => ('y', y),
        };
        write!(f, "Fold along {}={}", indicator, value)
    }
}

enum ParseFoldError {
    BadInt(String, ParseIntError),
    Unrecognised(String),
}

impl Display for ParseFoldError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ParseFoldError::BadInt(s, e) => {
                write!(f, "failed to parse {} as an integer: {}", s, e)
            }
            ParseFoldError::Unrecognised(s) => {
                write!(f, "does not look like a fold instruction: {}", s)
            }
        }
    }
}

impl TryFrom<&str> for Fold {
    type Error = ParseFoldError;
    fn try_from(s: &str) -> Result<Fold, ParseFoldError> {
        match s.strip_prefix("fold along y=") {
            Some(tail) => match tail.parse() {
                Ok(y) => Ok(Fold::Y(y)),
                Err(e) => Err(ParseFoldError::BadInt(tail.to_string(), e)),
            },
            None => match s.strip_prefix("fold along x=") {
                Some(tail) => match tail.parse() {
                    Ok(x) => Ok(Fold::X(x)),
                    Err(e) => Err(ParseFoldError::BadInt(tail.to_string(), e)),
                },
                None => Err(ParseFoldError::Unrecognised(s.to_string())),
            },
        }
    }
}

fn single_fold(dots: &HashSet<Point>, fold: &Fold) -> HashSet<Point> {
    HashSet::from_iter(dots.iter().map(|dot| dot.transform(fold)))
}

fn part1(dots: &HashSet<Point>, folds: &[Fold]) {
    match folds.first() {
        Some(first_fold) => {
            println!("before fold there are {} dots", dots.len());
            let folded = single_fold(dots, first_fold);
            println!("after fold there are {} dots", folded.len());
            show_points(folded.iter());
            println!("Day 13 part 1: number of dots: {}", folded.len());
        }
        None => {
            panic!("no fold instructions!");
        }
    }
}

fn part2(_dots: &HashSet<Point>, _folds: &[Fold]) {}

fn parse_dots(input: &str) -> HashSet<Point> {
    input
        .split_terminator('\n')
        .map(|line| match line.split_once(',') {
            None => {
                panic!("unexpected dots line: {}", line);
            }
            Some((x, y)) => match Point::try_from((x, y)) {
                Ok(point) => point,
                Err(e) => {
                    panic!("{}", e);
                }
            },
        })
        .collect()
}

fn parse_folds(input: &str) -> Vec<Fold> {
    input
        .split_terminator('\n')
        .map(|line| match Fold::try_from(line) {
            Ok(fold) => fold,
            Err(e) => {
                panic!("bad fold {}: {}", line, e);
            }
        })
        .collect()
}

fn parse_input(input: &str) -> (HashSet<Point>, Vec<Fold>) {
    match input.split_once("\n\n") {
        Some((lines_giving_dots, lines_giving_folds)) => (
            parse_dots(lines_giving_dots),
            parse_folds(lines_giving_folds),
        ),
        None => {
            panic!("input does not contain a blank line");
        }
    }
}

fn main() {
    let mut input = String::new();
    match io::stdin().read_to_string(&mut input) {
        Ok(_) => (),
        Err(e) => {
            panic!("failed to read input: {}", e);
        }
    }
    let (dots, folds) = parse_input(input.as_str());
    for dot in dots.iter() {
        println!("{}", dot);
    }
    for fold in &folds {
        println!("{}", fold);
    }

    part1(&dots, &folds);
    part2(&dots, &folds);
}
