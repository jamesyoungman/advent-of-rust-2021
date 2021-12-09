use std::collections::HashMap;
use std::io;
use std::io::prelude::*;

use ndarray::prelude::*;
//use ndarray::s;
//use ndarray::Zip;

struct HeightMap {
    heights: Array2<i32>,
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
        result.push((pr, c)); // North
                              //if let Some(nc) = next_col {
                              //    result.push((pr, nc));
                              //}
    }

    if let Some(pc) = prev_col {
        result.push((r, pc)); // West
    }
    // miss out myself
    if let Some(nc) = next_col {
        result.push((r, nc)); // East
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

#[derive(Clone, Copy, Debug)]
enum BasinCell {
    HighPoint,
    LowPoint,
    DrainsTo((usize, usize)),
}

impl HeightMap {
    fn is_low_point(&self, r: usize, c: usize) -> bool {
        let nrows: usize = self.heights.nrows();
        let ncols: usize = self.heights.ncols();
        let h = self.heights[(r, c)];
        for neighbour in neighbours(r, c, nrows, ncols) {
            let neighbour_height: i32 = self.heights[neighbour];
            if neighbour_height <= h {
                return false;
            }
        }
        true
    }

    fn low_points(&self) -> Array2<i32> {
        Array::from_shape_fn((self.heights.nrows(), self.heights.ncols()), |(r, c)| {
            if self.is_low_point(r, c) {
                self.heights[(r, c)]
            } else {
                -1
            }
        })
    }

    fn assign_low_point(
        &self,
        r: usize,
        c: usize,
        nrows: usize,
        ncols: usize,
        basins: &mut Array2<Option<BasinCell>>,
        low_points: &Array2<i32>,
    ) {
        let pos = (r, c);
        match basins[pos] {
            Some(_) => (),
            None => {
                if low_points[pos] != -1 {
                    // pos is a low point.
                    basins[pos] = Some(BasinCell::LowPoint);
                    return;
                }
                let height = self.heights[pos];
                let mut lowest_neighbour: Option<(usize, usize)> = None;
                let mut height_of_lowest_neighbour: Option<i32> = None;
                for neighbour in neighbours(r, c, nrows, ncols) {
                    let this_neighbour_height = self.heights[neighbour];
                    match height_of_lowest_neighbour {
                        None => {
                            lowest_neighbour = Some(neighbour);
                            height_of_lowest_neighbour = Some(this_neighbour_height);
                        }
                        Some(lowest_so_far) if this_neighbour_height < lowest_so_far => {
                            lowest_neighbour = Some(neighbour);
                            height_of_lowest_neighbour = Some(this_neighbour_height);
                        }
                        _ => (),
                    }
                }
                match lowest_neighbour {
                    Some(lowest_pos) => {
                        if let Some(h) = height_of_lowest_neighbour {
                            assert!(h < height);
                        }
                        match &basins[lowest_pos] {
                            Some(BasinCell::HighPoint) => unreachable!(),
                            Some(BasinCell::LowPoint) => {
                                basins[pos] = Some(BasinCell::DrainsTo(lowest_pos));
                            }
                            // This is basically the UNION-FIND algorithm.
                            Some(known) => {
                                basins[pos] = Some(*known);
                            }
                            None => {
                                let (r, c) = lowest_pos;
                                self.assign_low_point(r, c, nrows, ncols, basins, low_points);
                                basins[pos] = basins[lowest_pos];
                                assert!(matches!(basins[pos], Some(BasinCell::DrainsTo(_))));
                            }
                        }
                    }
                    None => unreachable!(),
                }
            }
        }
    }

    fn basins(&self) -> Array2<BasinCell> {
        let nrows = self.heights.nrows();
        let ncols = self.heights.ncols();
        let low_points = self.low_points();
        let is_a_low_point = |r: usize, c: usize| -> bool { low_points[(r, c)] != -1 };
        let mut maybe_result: Array2<Option<BasinCell>> =
            Array2::from_shape_fn((nrows, ncols), |(r, c)| {
                if self.heights[(r, c)] == 9 {
                    Some(BasinCell::HighPoint)
                } else if is_a_low_point(r, c) {
                    Some(BasinCell::LowPoint)
                } else {
                    None
                }
            });
        for r in 0..nrows {
            for c in 0..ncols {
                self.assign_low_point(r, c, nrows, ncols, &mut maybe_result, &low_points);
            }
        }
        let result: Array2<BasinCell> =
            Array2::from_shape_fn((nrows, ncols), |pos| match maybe_result[pos] {
                None => {
                    panic!("basins() did not assign {:?}", pos);
                }
                Some(x) => x,
            });
        result
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
            let heights = Array::from_shape_fn((height, width), |(r, c)| decode_cell(cells[r][c]));
            Ok(HeightMap { heights })
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

fn part2(hm: &HeightMap) {
    let mut basin_size: HashMap<(usize, usize), usize> = HashMap::new();
    let basins: Array2<BasinCell> = hm.basins();

    println!("basins:\n{:?}", basins);

    let nrows: usize = hm.heights.nrows();
    let ncols: usize = hm.heights.ncols();

    for r in 0..nrows {
        for c in 0..ncols {
            let pos = (r, c);
            match basins[pos] {
                BasinCell::HighPoint => (),
                BasinCell::LowPoint => {
                    *basin_size.entry(pos).or_insert(0) += 1;
                }
                BasinCell::DrainsTo(dest) => {
                    *basin_size.entry(dest).or_insert(0) += 1;
                }
            }
        }
    }

    for (basin, size) in basin_size.iter() {
        println!("There is a basin of size {} at {:?}", size, basin);
    }

    let mut basin_sizes: Vec<usize> = basin_size.values().copied().collect();
    basin_sizes.sort_unstable();
    let product: usize = basin_sizes
        .iter()
        .rev()
        .take(3)
        .inspect(|size| {
            println!("a top-3 basin has size {}", size);
        })
        .product();
    println!("Day 9 part 2: product = {}", product);
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
