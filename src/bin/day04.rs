use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;
use std::num::ParseIntError;

#[derive(Debug, Clone)]
struct Grid {
    won: bool,
    rows: Vec<Vec<i32>>,
    got: Vec<Vec<bool>>,
}

impl Grid {
    pub fn new() -> Grid {
        Grid {
            won: false,
            rows: Vec::new(),
            got: Vec::new(),
        }
    }

    pub fn sum_unmarked(&self) -> i32 {
        let mut result: i32 = 0;
        for (numrow, gotrow) in self.rows.iter().zip(self.got.iter()) {
            for (num, got) in numrow.iter().zip(gotrow.iter()) {
                if !*got {
                    result += num;
                }
            }
        }
        result
    }

    pub fn add_row(&mut self, numbers: Vec<i32>) {
        assert!(numbers.len() == 5);
        self.got.push([false].repeat(numbers.len()));
        self.rows.push(numbers);
    }

    pub fn is_full_size(&self) -> bool {
        self.rows.len() == 5
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn already_won(&self) -> bool {
        self.won
    }

    fn won_row(&self, rownum: usize) -> bool {
        self.got[rownum].iter().all(|got: &bool| *got)
    }

    fn won_column(&self, colnum: usize) -> bool {
        for row in self.got.iter() {
            if !row[colnum] {
                return false;
            }
        }
        true
    }

    fn won(&self, rownum: usize, colnum: usize) -> bool {
        self.won_row(rownum) || self.won_column(colnum)
    }

    pub fn call_number(&mut self, n: &i32) -> bool {
        for (r, row) in self.rows.iter().enumerate() {
            for (c, value) in row.iter().enumerate() {
                if value == n {
                    self.got[r][c] = true;
                    if self.won(r, c) {
                        self.won = true;
                        return true;
                    }
                }
            }
        }
        false
    }
}

impl Display for Grid {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for row in self.rows.iter() {
            for num in row.iter() {
                write!(f, "{:>2} ", num)?;
            }
            f.write_str("\n")?;
        }
        Ok(())
    }
}

fn get_numbers(s: &str) -> Result<Vec<i32>, ParseIntError> {
    s.split(',').map(|item: &str| item.parse::<i32>()).collect()
}

fn get_grid<I>(iter: &mut I) -> Result<Option<Grid>, std::io::Error>
where
    I: Iterator<Item = Result<String, std::io::Error>>,
{
    let mut grid = Grid::new();
    loop {
        match iter.next() {
            Some(Err(e)) => {
                return Err(e);
            }
            Some(Ok(line)) if line.is_empty() => {
                if !grid.is_empty() {
                    // Blank line between grids.
                    break;
                } else {
                    // Skip the initial blank line
                }
            }
            Some(Ok(line)) => {
                let numbers: Vec<i32> = match line
                    .split_ascii_whitespace()
                    .map(|item: &str| item.parse::<i32>())
                    .collect()
                {
                    Err(e) => {
                        panic!("bad number: {}", e);
                    }
                    Ok(nums) => nums,
                };
                assert!(!numbers.is_empty());
                grid.add_row(numbers);
            }
            None => {
                // End of input.
                break;
            }
        }
    }
    if grid.is_empty() {
        Ok(None)
    } else {
        assert!(grid.is_full_size());
        Ok(Some(grid))
    }
}

fn get_grids<I>(mut iter: I) -> Result<Vec<Grid>, std::io::Error>
where
    I: Iterator<Item = Result<String, std::io::Error>>,
{
    let mut result: Vec<Grid> = Vec::new();
    loop {
        match get_grid(&mut iter) {
            Ok(Some(grid)) => {
                result.push(grid);
            }
            Ok(None) => {
                break;
            }
            Err(e) => {
                return Err(e);
            }
        }
    }
    Ok(result)
}

fn play(grids: &mut Vec<Grid>, numbers: &[i32]) -> Vec<(Grid, i32)> {
    let num_grids = grids.len();
    let mut win_order: Vec<(Grid, i32)> = Vec::new();
    for number in numbers {
        for grid in grids.iter_mut() {
            if grid.already_won() {
                continue; // a grid can only win once.
            }
            if grid.call_number(number) {
                win_order.push((grid.clone(), *number));
                if win_order.len() == num_grids {
                    println!("win order: ");
                    for (g, n) in &win_order {
                        println!("winning on {}:\n{}", n, g);
                    }
                    return win_order;
                }
            }
        }
    }
    panic!("Day 4: some grid has not won yet!");
}

fn part1(grids: &mut Vec<Grid>, numbers: &[i32]) {
    let winners = play(grids, numbers);
    let (grid, number) = &winners[0];
    let sum = grid.sum_unmarked();
    println!(
        "Day 4 part 1: score = {} * {} = {}",
        sum,
        number,
        sum * number,
    );
}

fn part2(mut grids: Vec<Grid>, numbers: &[i32]) {
    let mut winners = play(&mut grids, numbers);
    winners.reverse();
    let (grid, number) = &winners[0]; // actually the last to win
    let sum = grid.sum_unmarked();
    println!(
        "Day 4 part 2: score = {} * {} = {}",
        sum,
        number,
        sum * number,
    );
}

fn main() {
    let mut line_iter = io::BufReader::new(io::stdin()).lines();

    let numbers: Vec<i32> =
        get_numbers(&line_iter.next().unwrap().unwrap()).expect("valid number list");
    let grids: Vec<Grid> = get_grids(line_iter).expect("valid grids");
    for grid in &grids {
        println!("{}", grid);
    }
    part1(&mut grids.clone(), &numbers);
    part2(grids, &numbers);
}
