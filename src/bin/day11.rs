use std::io;
use std::io::prelude::*;

use ndarray::prelude::*;

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

    // Neighbours are N, E, S, W + NE, SE, SW, NW.
    if let Some(pr) = prev_row {
        if let Some(pc) = prev_col {
            result.push((pr, pc));
        }

        result.push((pr, c)); // North
        if let Some(nc) = next_col {
            result.push((pr, nc));
        }
    }

    if let Some(pc) = prev_col {
        result.push((r, pc)); // West
    }
    // miss out myself
    if let Some(nc) = next_col {
        result.push((r, nc)); // East
    }

    if let Some(next_row) = next_row {
        if let Some(pc) = prev_col {
            result.push((next_row, pc));
        }
        result.push((next_row, c)); // South
        if let Some(nc) = next_col {
            result.push((next_row, nc));
        }
    }
    assert!(result.len() >= 3 && result.len() <= 8);
    result
}

fn flash(
    grid: &mut Array2<u8>,
    r: usize,
    c: usize,
    nrows: usize,
    ncols: usize,
    flashed: &mut Array2<u8>,
) {
    assert_eq!(flashed[(r, c)], 0);
    //println!("The octopus at ({},{}) flashes.", r, c);
    flashed[(r, c)] = 1;
    for n in neighbours(r, c, nrows, ncols) {
        if flashed[n] == 0 {
            //println!("Bumping energy of the octopus at {:?} ({} to {}).",
            //	     n, grid[n], grid[n]+1);
            grid[n] += 1;
            if grid[n] > 9 {
                flash(grid, n.0, n.1, nrows, ncols, flashed);
            }
        }
    }
}

fn cycle(grid: &mut Array2<u8>, all_grid_positions: &[(usize, usize)]) -> usize {
    let nrows: usize = grid.nrows();
    let ncols: usize = grid.ncols();

    grid.map_mut(|element| *element += 1);
    let mut flashed: Array2<u8> = Array2::zeros((nrows, ncols));
    for pos in all_grid_positions {
        if grid[*pos] > 9 && flashed[*pos] == 0 {
            flash(grid, pos.0, pos.1, nrows, ncols, &mut flashed);
        }
    }
    let mut flash_count: usize = 0;
    for pos in all_grid_positions {
        if grid[*pos] > 9 {
            flash_count += 1;
            grid[*pos] = 0;
        }
    }
    flash_count
}

fn all_grid_positions(nrows: usize, ncols: usize) -> Vec<(usize, usize)> {
    let mut result = Vec::with_capacity(nrows * ncols);
    for r in 0..nrows {
        for c in 0..ncols {
            let pos = (r, c);
            result.push(pos);
        }
    }
    result
}

fn iterate(
    grid: &mut Array2<u8>,
    iterations: usize,
    stop_on_sync_flash: bool,
) -> (usize, Option<usize>) {
    let nrows: usize = grid.nrows();
    let ncols: usize = grid.ncols();
    let cells = nrows * ncols;
    let every_cell = all_grid_positions(nrows, ncols);
    let mut flashes: usize = 0;
    let mut first_synchronized_flash: Option<usize> = None;
    println!("Before any steps:\n{}", &grid);
    for iteration in 1..=iterations {
        let flashes_this_cycle = cycle(grid, &every_cell);
        flashes += flashes_this_cycle;
        println!(
            "After {} step(s):\n{}\n({} flashes)",
            iteration, &grid, flashes_this_cycle
        );
	if flashes_this_cycle == cells && first_synchronized_flash.is_none() {
	    first_synchronized_flash = Some(iteration);
	    if stop_on_sync_flash {
		break;
	    }
	}
    }
    (flashes, first_synchronized_flash)
}

fn part1(grid: &Array2<u8>) {
    const ITERATIONS: usize = 100;
    let (flashes, _) = iterate(&mut grid.clone(), ITERATIONS, false);
    println!(
        "Day 11 part 1: after {} iterations there were {} flashes",
        ITERATIONS, flashes
    );
}

fn part2(grid: &Array2<u8>) {
    let (_, first_sync) = iterate(&mut grid.clone(), usize::MAX, true);
    if let Some(iter) = first_sync {
	println!(
            "Day 11 part 1: first synchronized flash at iteration {}",
            iter
	);
    } else {
	println!("Day 11 part 1: there was no synchronized flash.");
    }
}

fn decode_cell(cell: char) -> u8 {
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

fn make_grid(lines: &[String]) -> Result<Array2<u8>, String> {
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
        Ok(heights)
    }
}

fn main() {
    let lines: Vec<String> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .collect();
    let grid = make_grid(&lines).expect("valid input");

    part1(&grid);
    part2(&grid);
}
