use std::collections::HashSet;
use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;

use tracing_subscriber::prelude::*;

#[derive(Debug)]
struct BadInput(String);

impl Display for BadInput {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Error for BadInput {}

fn get_pixel(ch: char) -> Result<bool, BadInput> {
    match ch {
        '.' | '#' => Ok(ch == '#'),
        _ => Err(BadInput(format!("unexpected character '{}'", ch))),
    }
}

struct Image {
    side: usize,

    // The set of lit (#) pixels.
    pixels: HashSet<(usize, usize)>,
}

impl Display for Image {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for y in 0..self.side {
            for x in 0..self.side {
                f.write_str(match self.pixels.contains(&(x, y)) {
                    true => "#",
                    false => ".",
                })?;
            }
            f.write_str("\n")?;
        }
        Ok(())
    }
}

impl Image {
    fn new(side: usize) -> Image {
        Image {
            side,
            pixels: HashSet::new(),
        }
    }

    fn side(&self) -> usize {
        self.side
    }

    fn get_pixel(&self, x: usize, y: usize) -> bool {
        self.pixels.contains(&(x, y))
    }

    fn set_pixel(&mut self, x: usize, y: usize, lit: bool) {
        if lit {
            self.pixels.insert((x, y));
        } else {
            // assume not already lit.
            assert_eq!(self.pixels.contains(&(x, y)), false);
        }
    }
}

fn parse_image(lines: &[&str]) -> Result<Image, BadInput> {
    fn convert_line(s: &str, y: usize, w: usize, img: &mut Image) -> Result<(), BadInput> {
        let mut count = 0;
        for (x, ch) in s.chars().enumerate() {
            count = x + 1;
            match get_pixel(ch) {
                Ok(lit) => {
                    img.set_pixel(x, y, lit);
                }
                Err(e) => {
                    panic!("Image::set_pixel: bad argument: {}", e);
                }
            }
        }
        if count != w {
            Err(BadInput(format!(
                "expected {} pixels on line {}, got {}",
                w, y, count
            )))
        } else {
            Ok(())
        }
    }

    let height = lines.len();
    let width = height;
    if lines.is_empty() {
        return Err(BadInput("image is missing".to_string()));
    }
    let mut image = Image::new(height);
    for (y, line) in lines.iter().enumerate() {
        convert_line(line, y, width, &mut image)?;
    }
    Ok(image)
}

fn parse_program(s: &str) -> Result<Vec<bool>, BadInput> {
    s.chars().map(get_pixel).collect()
}

fn parse_input(lines: &[&str]) -> Result<(Vec<bool>, Image), BadInput> {
    let mut it = lines.iter();
    let program: Vec<bool> = match it.next() {
        Some(s) => parse_program(s)?,
        None => {
            return Err(BadInput("input is empty".to_string()));
        }
    };
    const PROG_LEN: usize = 512;
    if program.len() != PROG_LEN {
        return Err(BadInput(format!(
            "expected program to have length {} , it has length {}",
            PROG_LEN,
            program.len()
        )));
    }

    match it.next() {
        Some(s) if s.is_empty() => (),
        Some(_) => {
            return Err(BadInput("expected empty line".to_string()));
        }
        None => {
            return Err(BadInput("image is missing".to_string()));
        }
    }
    let mut lines: Vec<&str> = Vec::new();
    for line in it {
        lines.push(line);
    }
    let image: Image = parse_image(&lines)?;
    Ok((program, image))
}

fn get_input_num(image: &Image, x: usize, y: usize) -> u32 {
    let getpixel = |dx: i8, dy: i8| -> bool {
        match (x, dx, y, dy) {
            (0, -1, _, _) | (_, _, 0, -1) => false,
            (x, -1, y, -1) => image.get_pixel(x - 1, y - 1),
            (x, dx, y, -1) => image.get_pixel(x + dx as usize, y - 1),
            (x, -1, y, dy) => image.get_pixel(x - 1, y + dy as usize),
            (x, dx, y, dy) => image.get_pixel(x + dx as usize, y + dy as usize),
        }
    };
    let mut result: u32 = 0;
    for dy in -1..=1 {
	for dx in -1..=1 {
            result <<= 1;
            if getpixel(dx, dy) {
                result |= 1;
            }
        }
    }
    result
}

const SAMPLE_PROGRAM: &str = concat!(
    "..#.#..#####.#.#.#.###.##.....###.##.#..###.####..#####..#....#..#..##..##",
    "#..######.###...####..#..#####..##..#.#####...##.#.#..#.##..#.#......#.###",
    ".######.###.####...#.##.##..#..#..#####.....#.#....###..#.##......#.....#.",
    ".#..#..##..#...##.######.####.####.#.#...#.......#..#.#.#...####.##.#.....",
    ".#..#...##.#.##..#...##.#.##..###.#......#.#.......#.#.#.####.###.##...#..",
    "...####.#..#..#.##.#....##..#.####....##...##..#...#......#.#.......#.....",
    "..##..####..#...#.#.#...##..#.#..###..#####........#..####......#..#");

const SAMPLE_IMAGE: &str = concat!("#..#.\n",
				   "#....\n",
				   "##..#\n",
				   "..#..\n",
				   "..###\n");

#[test]
fn test_get_input_num() {
    let image_lines: Vec<&str> = SAMPLE_IMAGE.split_terminator('\n').collect();
    let img: Image = parse_image(&image_lines).expect("valid sample image");
    assert_eq!(get_input_num(&img, 2, 2), 34);
}


fn compute_enhanced_pixel(num: u32, program: &[bool]) -> bool {
    match program.get(num as usize) {
        Some(v) => *v,
        None => {
            panic!("pixel lookup error: index {} is out of range", num);
        }
    }
}

#[test]
fn test_compute_enhanced_pixel() {
    let program: Vec<bool> = parse_program(SAMPLE_PROGRAM)
	.expect("valid test input");
    assert_eq!(compute_enhanced_pixel(34, &program),
	       true);
}

fn enhance(program: &[bool], input: &Image) -> Image {
    let in_width = input.side();
    let out_width = in_width * 3;
    let mut output = Image::new(out_width);
    for x in 0..out_width {
        for y in 0..out_width {
            let input_num: u32 = get_input_num(input, x / 3, y / 3);
            output.set_pixel(x, y, compute_enhanced_pixel(input_num, program));
        }
    }
    output
}

fn part1(_program: &[bool], _image: &Image) {}

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

    let lines: Vec<String> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .collect();
    let ls: Vec<&str> = lines.iter().map(|s| s.as_str()).collect();
    match parse_input(&ls) {
        Err(e) => Err(e.to_string()),
        Ok((program, image)) => {
            part1(&program, &image);
            Ok(())
        }
    }
}

fn main() {
    if let Err(e) = run() {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}
