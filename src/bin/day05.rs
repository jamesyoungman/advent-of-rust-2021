use std::cmp::{max, min};
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

#[derive(Copy, Clone, Debug)]
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
        match self.category() {
            LineType::Vertical => {
                let ymin = min(self.from.y, self.to.y);
                let ymax = max(self.from.y, self.to.y);
                (ymin..=ymax).map(|y| Point { x: self.from.x, y }).collect()
            }
            LineType::Horizontal => {
                let xmin = min(self.from.x, self.to.x);
                let xmax = max(self.from.x, self.to.x);
                (xmin..=xmax).map(|x| Point { x, y: self.from.y }).collect()
            }
            LineType::Other => {
                // In part 1, we only consider horizontal and vertical lines
                vec![]
            }
        }
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
            //println!("after drawing {}:\n{}", line, grid);
        }
        grid
    }
}

fn part1(g: &Grid) {
    let mut total: usize = 0;
    for (_p, count) in g.points.iter() {
        if *count > 1 {
            total += 1;
        }
    }
    println!("Day 5 part 1: {}", total);
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

    let grid = Grid::from(&lines);
    println!("{}", &grid);
    part1(&grid);
}
