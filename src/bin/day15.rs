use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;

use ndarray::prelude::*;

use pathfinding::directed::astar::astar;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Clone, Copy)]
struct Point {
    x: usize,
    y: usize,
}

impl Point {
    pub fn new(x: usize, y: usize) -> Point {
        Point { x, y }
    }
}

impl Display for Point {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({},{})", self.x, self.y)
    }
}

#[derive(Debug)]
struct Grid {
    risk: Array2<usize>,
}

impl Grid {
    pub fn get(&self, p: &Point) -> usize {
        self.risk[(p.x, p.y)]
    }

    pub fn height(&self) -> usize {
        self.risk.nrows()
    }

    pub fn width(&self) -> usize {
        self.risk.ncols()
    }

    pub fn neighbours(&self, p: &Point) -> Vec<Point> {
        neighbours(p, self.height(), self.width())
    }

    pub fn top_left(&self) -> Point {
        Point::new(0, 0)
    }

    pub fn bottom_right(&self) -> Point {
        Point::new(self.width() - 1, self.height() - 1)
    }
}

impl Display for Grid {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "Grid; {}x{}", self.height(), self.width())?;
        for row in 0..self.height() {
            for col in 0..self.width() {
                let p = Point { x: col, y: row };
                write!(f, "{}", self.get(&p))?;
            }
            f.write_str("\n")?;
        }
        Ok(())
    }
}

fn decode_cell(cell: char) -> usize {
    let mut s: String = String::with_capacity(1);
    s.push(cell);
    match s.parse() {
        Ok(n) => {
            assert!(n <= 9);
            n
        }
        Err(e) => {
            panic!("invalid (non-numeric) cell '{}': {}", cell, e);
        }
    }
}

impl TryFrom<&[String]> for Grid {
    type Error = String;
    fn try_from(lines: &[String]) -> Result<Grid, String> {
        let cells: Vec<Vec<char>> = lines
            .iter()
            .map(|line| -> Vec<char> { line.chars().collect() })
            .collect();
        if lines.is_empty() {
            Err("no data".to_string())
        } else {
            let height = lines.len();
            let width = lines[0].len();
            for line in lines {
                assert_eq!(line.len(), width);
            }
            let risk = Array::from_shape_fn((height, width), |(c, r)| decode_cell(cells[r][c]));
            //println!("risk:\n{:?}", &risk);
            let result = Grid { risk };
            //println!("grid:\n{}", &result);
            Ok(result)
        }
    }
}

fn clamp_range(val: usize, limit: usize) -> Option<usize> {
    if val < limit {
        Some(val)
    } else {
        None
    }
}

fn neighbours(p: &Point, rows: usize, cols: usize) -> Vec<Point> {
    let (r, c) = (p.y, p.x);
    let mut result: Vec<Point> = Vec::with_capacity(4);
    let prev_col: Option<usize> = c.checked_sub(1);
    let next_col: Option<usize> = c.checked_add(1).map(|val| clamp_range(val, cols)).flatten();
    let prev_row: Option<usize> = r.checked_sub(1);
    let next_row: Option<usize> = r.checked_add(1).map(|val| clamp_range(val, rows)).flatten();

    // Neighbours are N, E, S, W.
    // We do not include NE, SE, SW, NW.
    if let Some(pr) = prev_row {
        result.push(Point::new(c, pr)); // N
    }
    if let Some(pc) = prev_col {
        result.push(Point::new(pc, r)); // West
    }
    // miss out myself
    if let Some(nc) = next_col {
        result.push(Point::new(nc, r)); // East
    }
    if let Some(next_row) = next_row {
        result.push(Point::new(c, next_row)); // South
    }
    assert!(result.len() == 4 || result.len() == 3 || result.len() == 2);
    result
}

fn abs_diff(a: usize, b: usize) -> usize {
    if a > b {
        a - b
    } else {
        b - a
    }
}

/// Manhattan distance between two points
fn manhattan(a: &Point, b: &Point) -> usize {
    abs_diff(a.x, b.x) + abs_diff(a.y, b.y)
}

fn lowest_risk_path(start: &Point, end: &Point, costs: &Grid) -> usize {
    let successors = |pos: &Point| -> Vec<(Point, usize)> {
        costs
            .neighbours(pos)
            .iter()
            .map(|pos| (*pos, costs.get(pos)))
            .collect()
    };
    let heuristic = |pos: &Point| -> usize { manhattan(pos, end) };
    let success = |pos: &Point| -> bool { pos == end };
    match astar(start, successors, heuristic, success) {
        Some((_path, cost)) => cost,
        None => {
            panic!("no solution found");
        }
    }
}

#[test]
fn test_lowest_risk_path() {
    fn runtest(numbers: &[&str]) -> usize {
        let ns: Vec<String> = numbers.iter().map(|line| line.to_string()).collect();
        let grid = Grid::try_from(ns.as_slice()).expect("valid test data");
        //println!("{}", &grid);
        lowest_risk_path(&grid.top_left(), &grid.bottom_right(), &grid)
    }

    let lowest = runtest(&["116", "138", "213"]);
    assert_eq!(lowest, 7);

    let lowest = runtest(&[
        "1163751742",
        "1381373672",
        "2136511328",
        "3694931569",
        "7463417111",
        "1319128137",
        "1359912421",
        "3125421639",
        "1293138521",
        "2311944581",
    ]);
    assert_eq!(lowest, 40);
    // There are multiple paths of cost 40 (e.g. pass through
    // (7,5) or (8,4) so we don't check that the chosen path
    // is identical.
}

fn enlarge_grid(small: &Grid) -> Grid {
    let sw: usize = small.width();
    let sh: usize = small.height();
    Grid {
        risk: Array::from_shape_fn((sh * 5, sw * 5), |(x, y)| {
            let base_cost = small.get(&Point {
                x: x % sw,
                y: y % sh,
            });
            let manhattan = x / sw + y / sh;
            let cost = base_cost + manhattan;
            1 + (cost - 1) % 9
        }),
    }
}

#[test]
fn test_enlarge_grid() {
    let example = &[
        "1163751742",
        "1381373672",
        "2136511328",
        "3694931569",
        "7463417111",
        "1319128137",
        "1359912421",
        "3125421639",
        "1293138521",
        "2311944581",
    ];
    let ns: Vec<String> = example.iter().map(|line| line.to_string()).collect();
    let grid = Grid::try_from(ns.as_slice()).expect("valid test data");
    let big = enlarge_grid(&grid);
    assert_eq!(
        lowest_risk_path(&big.top_left(), &big.bottom_right(), &big),
        315
    );
}

fn part1(grid: &Grid) {
    println!(
        "Day 15 part 1: {}",
        lowest_risk_path(&grid.top_left(), &grid.bottom_right(), grid)
    );
}

fn part2(grid: &Grid) {
    let big_grid = enlarge_grid(grid);
    println!(
        "Day 15 part 2: {}",
        lowest_risk_path(&big_grid.top_left(), &big_grid.bottom_right(), &big_grid)
    );
}

fn main() {
    let lines: Vec<String> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .collect();
    let grid = Grid::try_from(lines.as_slice()).expect("valid input");
    part1(&grid);
    part2(&grid);
}
