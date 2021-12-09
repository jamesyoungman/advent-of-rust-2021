use std::io;
use std::io::prelude::*;

use ndarray::prelude::*;
//use ndarray::s;
//use ndarray::Zip;

struct HeightMap {
    heights: Array2<i32>
}

fn clamp_range(val: usize, limit: usize) -> Option<usize> {
    if val < limit {
	Some(val)
    } else {
	None
    }
}

fn neighbours(r: usize, c: usize, rows: usize, cols: usize) -> Vec<(usize, usize)> {
    let mut result: Vec<(usize, usize)> = Vec::with_capacity(8);
    let prev_col: Option<usize> = c.checked_sub(1);
    let next_col: Option<usize> = c.checked_add(1).map(|val| clamp_range(val, cols)).flatten();
    let prev_row: Option<usize> = r.checked_sub(1);
    let next_row: Option<usize> = r.checked_add(1).map(|val| clamp_range(val, rows)).flatten();

    // Neighbours are N, E, S, W.
    // We do not include NE, SE, SW, NW.
    if let Some(pr) = prev_row {
	//if let Some(pc) = prev_col {
	//    result.push((pr, pc));
	//}
	//
	result.push((pr, c));	// North
	//if let Some(nc) = next_col {
	//    result.push((pr, nc));
	//}
    }

    if let Some(pc) = prev_col {
	result.push((r, pc));	// West
    }
    // miss out myself
    if let Some(nc) = next_col {
	result.push((r, nc));	// East
    }

    if let Some(next_row) = next_row {
	//if let Some(pc) = prev_col {
	//    result.push((next_row, pc));
	//}
	result.push((next_row, c)); // South
	//if let Some(nc) = next_col {
	//    result.push((next_row, nc));
	//}
    }
    assert!(result.len() == 4 || result.len() == 3 || result.len() == 2);
    result
}

impl HeightMap {
    fn is_low_point(&self, r: usize, c: usize) -> bool {
	let nrows: usize = self.heights.nrows();
	let ncols: usize = self.heights.ncols();
	let h = self.heights[(r, c)];
	for neighbour in neighbours(r, c, nrows, ncols) {
	    let neighbour_height: i32 = self.heights[neighbour];
	    if neighbour_height < h {
		return false;
	    }
	}
	true
    }

    fn low_points(&self) -> Array2<i32> {
	Array::from_shape_fn(
	    (self.heights.nrows(), self.heights.ncols()),
	    |(r, c)| {
		if self.is_low_point(r, c) {
		    self.heights[(r, c)]
		} else {
		    -1
		}
	    })
    }
}

fn decode_cell(cell: char) -> i32 {
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



impl TryFrom<&[String]> for HeightMap {
    type Error = String;
    fn try_from(lines: &[String]) -> Result<HeightMap, String> {
	let cells: Vec<Vec<char>> = lines.iter()
	    .map(|line| -> Vec<char> {
		line.chars().collect()
	    })
	    .collect();
	if lines.len() == 0 {
	    Err("no data".to_string())
	} else {
	    let height = lines.len();
	    let width = lines[0].len();
	    for line in lines {
		assert_eq!(line.len(), width);
	    }
	    let heights = Array::from_shape_fn(
		(height, width), |(r, c)| decode_cell(cells[r][c]));
	    Ok(HeightMap {
		heights,
	    })
	}
    }
}

fn part1(hm: &HeightMap) {
    let lows = hm.low_points();
    println!("lows:\n{}", lows);
    let risk_levels = lows.map(|val| val + 1);
    println!("risk levels:\n{}", risk_levels);
    let total_risk = risk_levels.sum();
    println!("Day 9 part 1: {}", total_risk);
}

fn part2(_hm: &HeightMap) {
}

fn main() {
    let lines: Vec<String> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .collect();
    let hm = HeightMap::try_from(lines.as_slice()).expect("valid input");

    part1(&hm);
    part2(&hm);
}
