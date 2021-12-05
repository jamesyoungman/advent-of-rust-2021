use std::cmp::{max, min, Ordering};
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;
use std::num::ParseIntError;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
struct Point {
    pub x: i32,
    pub y: i32,
}

impl Display for Point {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({},{})", self.x, self.y)
    }
}

fn str_to_i32(s: &str) -> Result<i32, String> {
    s.parse().map_err(|e: ParseIntError| e.to_string())
}

impl TryFrom<&str> for Point {
    type Error = String;
    fn try_from(s: &str) -> Result<Point, String> {
        let parts = s.split(',').collect::<Vec<_>>();
        match parts.as_slice() {
            [x, y] => Ok(Point {
                x: str_to_i32(x)?,
                y: str_to_i32(y)?,
            }),
            _ => Err("expected x,y".to_string()),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum LineType {
    Horizontal,
    Vertical,
    Other,
}

#[derive(Copy, Clone)]
struct Line {
    pub from: Point,
    pub to: Point,
}

impl Line {
    pub fn category(&self) -> LineType {
        if self.from.x == self.to.x {
            LineType::Vertical
        } else if self.from.y == self.to.y {
            LineType::Horizontal
        } else {
            LineType::Other
        }
    }

    pub fn draw(&self) -> Vec<Point> {
        fn delta(start: i32, end: i32) -> i32 {
            match start.cmp(&end) {
                Ordering::Equal => 0,
                Ordering::Less => 1,
                Ordering::Greater => -1,
            }
        }
        let xdelta = delta(self.from.x, self.to.x);
        let ydelta = delta(self.from.y, self.to.y);
        // sep is the distance between the endpoints, in either the
        // horizontal or vertical direction, as opposed to the actual
        // length of the line.
        let sep = max(
            (self.from.x - self.to.x).abs(),
            (self.from.y - self.to.y).abs(),
        );
        (0..=sep)
            .map(|t| Point {
                x: self.from.x + t as i32 * xdelta,
                y: self.from.y + t as i32 * ydelta,
            })
            .collect()
    }
}

impl Display for Line {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.from, self.to)
    }
}

impl TryFrom<&str> for Line {
    type Error = String;
    fn try_from(s: &str) -> Result<Line, String> {
        let parts: Vec<&str> = s.split(" -> ").collect();
        match parts.as_slice() {
            [from, to] => Ok(Line {
                from: Point::try_from(*from)?,
                to: Point::try_from(*to)?,
            }),
            _ => Err("expected from -> to".to_string()),
        }
    }
}

#[derive(Debug)]
struct Grid {
    top_left: Point,
    bot_right: Point,
    points: HashMap<Point, usize>,
}

impl Grid {
    fn update_corners(&mut self, p: &Point) {
        self.top_left.x = min(p.x, self.top_left.x);
        self.top_left.y = min(p.y, self.top_left.y);
        self.bot_right.x = max(p.x, self.bot_right.x);
        self.bot_right.y = max(p.y, self.bot_right.y);
    }

    fn draw(&mut self, p: &Point) {
        *self.points.entry(*p).or_insert(0) += 1;
    }
}

impl Display for Grid {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for y in self.top_left.y..=self.bot_right.y {
            for x in self.top_left.x..=self.bot_right.x {
                let p: Point = Point { x, y };
                match self.points.get(&p) {
                    Some(n) => {
                        assert!(*n < 10);
                        write!(f, "{}", n)?;
                    }
                    None => {
                        f.write_str(".")?;
                    }
                }
            }
            f.write_str("\n")?;
        }
        Ok(())
    }
}

impl From<&Vec<Line>> for Grid {
    fn from(lines: &Vec<Line>) -> Grid {
        let mut grid = Grid {
            top_left: Point { x: 0, y: 0 },
            bot_right: Point { x: 0, y: 0 },
            points: HashMap::new(),
        };
        for line in lines {
            for point in line.draw() {
                grid.update_corners(&point);
                grid.draw(&point);
            }
        }
        grid
    }
}

fn count_overlaps(part_num: i32, lines: &[Line]) {
    let kept_lines: Vec<Line> = match part_num {
        1 => lines
            .iter()
            .filter(|line| line.category() != LineType::Other)
            .cloned()
            .collect(),
        2 => lines.to_vec(),
        _ => {
            panic!("part {}?", part_num);
        }
    };
    let grid = Grid::from(&kept_lines);
    println!("Part {}:\n{}", part_num, &grid);
    let total = grid.points.values().filter(|count| **count > 1).count();
    println!("Day 5 part {}: {}", part_num, total);
}

#[test]
fn test_diagonal() {
    let line1 = Line {
        from: Point { x: 1, y: 1 },
        to: Point { x: 3, y: 3 },
    };
    let points = line1.draw();
    assert_eq!(Point { x: 1, y: 1 }, points[0]);
    assert_eq!(Point { x: 2, y: 2 }, points[1]);
    assert_eq!(Point { x: 3, y: 3 }, points[2]);

    let line2 = Line {
        from: Point { x: 9, y: 7 },
        to: Point { x: 7, y: 9 },
    };
    let points = line2.draw();
    assert_eq!(Point { x: 9, y: 7 }, points[0]);
    assert_eq!(Point { x: 8, y: 8 }, points[1]);
    assert_eq!(Point { x: 7, y: 9 }, points[2]);
}

fn main() {
    let lines: Vec<Line> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .map(|line| match Line::try_from(line.as_str()) {
            Ok(line) => line,
            Err(e) => {
                panic!("expected valid lines: {}", e)
            }
        })
        .collect();

    count_overlaps(1, &lines);
    count_overlaps(2, &lines);
}
