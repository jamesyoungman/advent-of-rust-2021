use std::collections::HashSet;
use std::cmp::{max, min};
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

#[derive(Debug)]
struct Bounds<T: Ord + Copy> {
    min: T,
    max: T,
}

impl<T: Copy + Ord> Bounds<T> {
    fn new(min: T, max: T) -> Bounds<T> {
        Bounds {
            min,
            max
        }
    }

    fn update(&mut self, val: T) {
        self.min = min(self.min, val);
        self.max = max(self.max, val);
    }
}

#[derive(Debug)]
struct ImageBoundingBox {
    x: Bounds<i64>,
    y: Bounds<i64>
}

impl ImageBoundingBox {
    fn new(
        xmin: i64,
        xmax: i64,
        ymin: i64,
        ymax: i64,
    ) -> ImageBoundingBox {
        ImageBoundingBox {
            x: Bounds::new(xmin, xmax),
            y: Bounds::new(ymin, ymax),
        }
    }

    fn update(&mut self, x: i64, y: i64) {
        self.x.update(x);
        self.y.update(y);
    }

    fn get(&self) -> ((i64, i64), (i64, i64)) {
        ((self.x.min, self.y.min),
         (self.x.max, self.y.max))
    }
}


type Ordinate = i64;
type Point = (Ordinate, Ordinate);

#[derive(Debug)]
struct Image {
    bounds: Option<ImageBoundingBox>,
    pixels: HashSet<Point>,     // The set of non-default pixels.
    default: bool,              // default pixel state
}

impl Display for Image {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.bounds.as_ref() {
            Some(b) => {
                let ((left, top), (right, bottom)) = b.get();
                for y in top..=bottom { // we're actually rendering upside down
                    for x in left..=right {
                        let lit = match self.pixels.contains(&(x, y)) {
                            true => !self.default,
                            false => self.default,
                        };
                        f.write_str(if lit { "#" } else { "." })?;
                    }
                    f.write_str("\n")?;
                }
                Ok(())
            }
            None => {
                write!(f, "(no image bounds, {} non-default pixels)", self.pixels.len())
            }
        }
    }
}

impl Image {
    fn new(default: bool) -> Image {
        Image {
            bounds: None,
            pixels: HashSet::new(),
            default,
        }
    }

    //fn all_default<'a, I>(&self, mut it: I) -> bool
    //where
    //	I: Iterator<Item=&'a Point>
    //{
    //	!it.any(|p| self.pixels.contains(p))
    //}

    fn get_pixel(&self, x: Ordinate, y: Ordinate) -> bool {
        if self.pixels.contains(&(x, y)) {
            !self.default
        } else {
            self.default
        }
    }

    fn bounds(&self) -> Option<&ImageBoundingBox> {
        self.bounds.as_ref()
    }

    fn set_pixel(&mut self, x: Ordinate, y: Ordinate, lit: bool) {
        let pos = (x, y);
        if lit == self.default {
            self.pixels.remove(&pos);
        } else {
            match &mut self.bounds {
		None => {
                    self.bounds = Some(ImageBoundingBox::new(x, x, y, y));
		}
		Some(b) => {
                    b.update(x, y);
		}
            }
            self.pixels.insert(pos);
        }
    }

    fn count_lit_pixels(&self) -> Option<usize> {
        if self.default {
            None		// an infinite number are lit
        } else {
            Some(self.pixels.len())
        }
    }

    fn count_unlit_pixels(&self) -> Option<usize> {
        if self.default {
            Some(self.pixels.len())
        } else {
            None		// an infinite number are unlit
        }
    }

    //fn maybe_remove_left_and_top_margin(&mut self) {
    //	match self.bounds.clone() {
    //	    None => (),
    //	    Some(b) => {
    //		let ((left, top), (right, bottom)) = b.get();
    //		let top_row_blank: bool = Self::all_default((left..=right).map(|x| (x, top)));
    //		let left_col_blank: bool = Self::all_default((top..=bottom).map(|y| (left, y)));
    //		if top_row_blank {
    //		    top -= 1;
    //		}
    //		if left_col_blank {
    //		    left += 1;
    //		}
    //		let newbounds = Some(ImageBoundingBox::new(left, right, bottom, top));
    //		self.bounds = newbounds;
    //		dbg!(b);
    //		dbg!(newbounds);
    //	    }
    //	}
    //}
}

fn parse_image(lines: &[&str]) -> Result<Image, BadInput> {
    fn convert_line(
        s: &str,
        y: Ordinate,
        w: Ordinate,
        img: &mut Image
    ) -> Result<(), BadInput> {
        let mut count: Ordinate = 0;
        for (x, ch) in s.chars().enumerate() {
            let x = x as Ordinate;
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

    let mut image = Image::new(false);
    let height = lines.len() as Ordinate;
    let width = height;
    if lines.is_empty() {
        return Err(BadInput("image is missing".to_string()));
    }
    for (y, line) in lines.iter().enumerate() {
        convert_line(line, y as Ordinate, width, &mut image)?;
    }
    println!("parse_image: input\n{:?}\ntranslated to image\n{}\n",
             lines, image);
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

fn get_input_num(image: &Image, x: Ordinate, y: Ordinate) -> u32 {
    let getpixel = |dx: i64, dy: i64| -> bool {
	image.get_pixel(x + dx, y + dy)
    };
    let mut result: u32 = 0;
    for dy in -1..=1 {
        for dx in -1..=1 {
            result <<= 1;
            let lit  = getpixel(dx, dy);
            if lit {
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

const SMALL_SAMPLE_IMAGE: &str = concat!(
    "#..#.\n",
    "#....\n",
    "##..#\n",
    "..#..\n",
    "..###\n"
);

/// LARGE_SAMPLE_IMAGE has the same pixels lit as SMALL_SAMPLE_IMAGE, but with
/// an offset in both the x and y directions.
const LARGE_SAMPLE_IMAGE: &str = concat!(
    "...............\n",
    "...............\n",
    "...............\n",
    "...............\n",
    "...............\n",
    ".....#..#......\n",
    ".....#.........\n",
    ".....##..#.....\n",
    ".......#.......\n",
    ".......###.....\n",
    "...............\n",
    "...............\n",
    "...............\n",
    "...............\n",
    "...............\n",
);

#[test]
fn test_get_input_num() {
    let image_lines: Vec<&str> = SMALL_SAMPLE_IMAGE.split_terminator('\n').collect();
    let img: Image = parse_image(&image_lines).expect("valid sample image");
    println!("Image is:\n{}", img);
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
    let new_default = if input.default {
	// Pixels not recorded in input.pixels are lit.  In the next
	// generation their state will be set to program[511] because
	// their neighbours are lit.
        program[511]
    } else {
        program[0]
    };
    let mut output = Image::new(new_default);
    match input.bounds() {
        None => (),
        Some(b) => {
            let ((left, top), (right, bottom)) = dbg!(b.get());
            for y in (top-1)..=(bottom+1) {
                for x in (left-1)..=(right+1) {
                    let input_num: u32 = get_input_num(input, x, y);
                    output.set_pixel(x, y, compute_enhanced_pixel(input_num, program));
                }
            }
        }
    }
    output
}

#[test]
fn test_bounding_box() {
    let small_image_lines: Vec<&str> = SMALL_SAMPLE_IMAGE.split_terminator('\n').collect();
    let small_image: Image = parse_image(&small_image_lines).expect("valid sample image");

    let large_image_lines: Vec<&str> = LARGE_SAMPLE_IMAGE.split_terminator('\n').collect();
    let large_image: Image = parse_image(&large_image_lines).expect("valid sample image");

    assert_eq!(small_image.to_string(), large_image.to_string());
}


#[test]
fn test_enhance() {
    let program: Vec<bool> =  parse_program(SAMPLE_PROGRAM)
        .expect("valid test input");
    let image_lines: Vec<&str> = LARGE_SAMPLE_IMAGE.split_terminator('\n').collect();
    let gen0: Image = parse_image(&image_lines).expect("valid sample image");
    let gen1: Image = enhance(&program, &gen0);
    println!("gen0:\n{}\ngen1:\n{}\n", &gen0, &gen1);
    assert_eq!(gen1.to_string(),
               concat!(
                   ".##.##.\n",
                   "#..#.#.\n",
                   "##.#..#\n",
                   "####..#\n",
                   ".#..##.\n",
                   "..##..#\n",
                   "...#.#.\n",
               ));
    let gen2: Image = enhance(&program, &gen1);
    println!("gen2:\n{}\n", &gen2);
    assert_eq!(gen2.to_string(),
               concat!(
		   ".......#.\n",
		   ".#..#.#..\n",
		   "#.#...###\n",
		   "#...##.#.\n",
		   "#.....#.#\n",
		   ".#.#####.\n",
		   "..#.#####\n",
		   "...##.##.\n",
		   "....###..\n",
	       ));
}


fn part1(program: &[bool], image: &Image) {
    let doubly_enhanced = enhance(program, &enhance(program, image));
    // 5547 is too high
    println!("Day 20 part 1: pixels lit: {:?}", doubly_enhanced.count_lit_pixels());
}

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
