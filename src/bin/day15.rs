use std::cmp::Ordering;
use std::collections::HashSet;
use std::io;
use std::io::prelude::*;

use ndarray::prelude::*;

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

#[derive(Debug)]
struct Grid {
    risk: Array2<usize>,
}

impl Grid {
    pub fn get(&self, p: &Point) -> usize {
        self.risk[(p.x, p.y)]
    }

    pub fn height(&self) -> usize {
        self.risk.ncols()
    }

    pub fn width(&self) -> usize {
        self.risk.nrows()
    }

    pub fn neighbours(&self, p: &Point) -> Vec<Point> {
        neighbours(p, self.height(), self.width())
    }

    pub fn top_left(&self) -> Point {
	Point::new(0, 0)
    }

    pub fn bottom_right(&self) -> Point {
	Point::new(self.width()-1, self.height()-1)
    }
}

fn decode_cell(cell: char) -> usize {
    let mut s: String = String::with_capacity(1);
    s.push(cell);
    match s.parse() {
        Ok(n) => {
            assert!(n >= 0);
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
            let risk = Array::from_shape_fn((height, width), |(r, c)| decode_cell(cells[r][c]));
            Ok(Grid { risk })
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
        result.push(Point::new(pr, c));
    }
    if let Some(pc) = prev_col {
        result.push(Point::new(r, pc)); // West
    }
    // miss out myself
    if let Some(nc) = next_col {
        result.push(Point::new(r, nc)); // East
    }
    if let Some(next_row) = next_row {
        result.push(Point::new(next_row, c)); // South
    }
    assert!(result.len() == 4 || result.len() == 3 || result.len() == 2);
    result
}

#[derive(Debug, Clone, Eq)]
struct Path {
    inorder: Vec<Point>,
    visited: HashSet<Point>,
}

impl Path {
    pub fn new() -> Path {
	Path {
	    inorder: Vec::new(),
	    visited: HashSet::new(),
	}
    }

    pub fn contains(&self, p: &Point) -> bool {
	self.visited.contains(p)
    }

    pub fn push(&mut self, p: Point) {
	self.visited.insert(p.clone());
	self.inorder.push(p);
    }

    pub fn visiting(&self, p: Point) -> Path {
	let mut result = self.clone();
	result.push(p);
	result

    }

    pub fn pop(&mut self) -> Option<Point> {
	if let Some(p) = self.inorder.pop() {
	    self.visited.remove(&p);
	    Some(p)
	} else {
	    None
	}
    }
}

impl Ord for Path {
    fn cmp(&self, other: &Path) -> Ordering {
	for (mine, theirs) in self.inorder.iter().zip(other.inorder.iter()) {
	    let comparison = mine.cmp(theirs);
	    if comparison != Ordering::Equal {
		return comparison;
	    }
	}
	// All elements in the common prefix match.  Hence the longer
	// sequence is the greater.
	self.inorder.len().cmp(&other.inorder.len())
    }
}

impl PartialOrd for Path {
    fn partial_cmp(&self, other: &Path) -> Option<Ordering> {
	Some(self.cmp(other))
    }
}

impl PartialEq for Path {
    fn eq(&self, other: &Path) -> bool {
	self.cmp(other) == Ordering::Equal
    }
}


impl From<Vec<Point>> for Path {
    fn from(points: Vec<Point>) -> Path {
	let mut result = Path::new();
	for p in points {
	    result.push(p);
	}
	result
    }
}

fn risk_search(
    start: &Point,
    end: &Point,
    grid: &Grid,
    current: usize,
    best: &mut usize,
    path: Path,
) -> Option<(usize, Path)> {
    if start == end {
	if current < *best {
	    *best = current;
	}
	Some((current, path))
    } else {
	let best_neighbour: Option<(usize, Path)> = grid.neighbours(&start).iter()
	    .filter(|n| !path.contains(n))
	    .filter_map(|n| -> Option<(usize, Path)> {
		let next_path: Path = path.visiting(*n);
		let next_risk: usize = current + grid.get(n);
		if next_risk < *best {
		    assert_eq!(next_risk,
			       next_path.inorder.iter().map(|pos| grid.get(pos)).sum());
		    risk_search(n, end, grid, next_risk, best, next_path)
		} else {
		    // Bound the search here, we cannot beat `best`.
		    None
		}
	    })
	    .min();
	best_neighbour
    }
}

fn lowest_risk_path(start: &Point, end: &Point, grid: &Grid) -> Option<(usize, Path)> {
    let mut path = Path::new();
    let mut best = usize::MAX;
    let mut visited: HashSet<Point> = HashSet::new();
    visited.insert(*start);
    risk_search(start, end, grid, 0, &mut best, path)
}

#[test]
fn test_lowest_risk_path() {

    fn runtest(numbers: &[&str]) -> (usize, Path) {
	let ns: Vec<String> = numbers.iter().map(|line| line.to_string()).collect();
	let grid = Grid::try_from(ns.as_slice()).expect("valid test data");
	match lowest_risk_path(&grid.top_left(), &grid.bottom_right(), &grid) {
	    Some((lowest, path)) => {
		println!("tuntest: lowest={}", lowest);
		println!("runtest: path={:?}", path);
		(lowest, path)
	    }
	    None => {
		panic!("runtest: no path found");
	    }
	}
    }

    let (lowest, _path) = runtest(&[
        "116",
        "138",
        "213",
    ]);
    assert_eq!(lowest, 7);

    let (lowest, path) = runtest(&[
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
    assert_eq!(
        path,
	Path::from(vec![
            Point::new(0, 1),
            Point::new(0, 2),
            Point::new(1, 2),
            Point::new(2, 2),
            Point::new(3, 2),
            Point::new(4, 2),
            Point::new(5, 2),
            Point::new(6, 2),
            Point::new(6, 3),
            Point::new(7, 3),
            Point::new(7, 4),
            Point::new(7, 5),
            Point::new(8, 5),
            Point::new(8, 6),
            Point::new(8, 7),
            Point::new(8, 8),
            Point::new(9, 8),
            Point::new(9, 9)
        ]),
    );
}

fn part1() {
    println!("Day 15 part 1: ");
}

fn part2() {
    println!("Day 15 part 2: ");
}

fn main() {
    let lines: Vec<String> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .collect();
    let grid = Grid::try_from(lines.as_slice()).expect("valid input");
}
