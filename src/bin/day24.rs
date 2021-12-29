use std::cmp::max;
use std::collections::HashMap;
use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;
use std::str::FromStr;

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, digit1, multispace1},
    combinator::{map, map_res, opt, recognize, value},
    sequence::{pair, preceded, tuple},
    IResult,
};
use tracing_subscriber::prelude::*;

type Word = i64;

#[derive(Debug, Eq, PartialEq, Clone, Copy, Hash)]
pub enum Reg {
    W,
    X,
    Y,
    Z,
}

impl Display for Reg {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Reg::W => "w",
            Reg::X => "x",
            Reg::Y => "y",
            Reg::Z => "z",
        })
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum Operand {
    Register(Reg),
    Literal(Word),
}

impl Display for Operand {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Register(r) => r.fmt(f),
            Operand::Literal(value) => write!(f, "{}", value),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy, PartialOrd, Ord)]
pub enum BinaryOpcode {
    Add,
    Mul,
    Div,
    Mod,
    Eql,
}

impl BinaryOpcode {
    fn execute(&self, dest: Word, src: Word) -> Result<Word, BadProgram> {
        match self {
            BinaryOpcode::Add => match dest.checked_add(src) {
                Some(n) => Ok(n),
                None => Err(BadProgram(format!(
                    "addition overflow for {} + {}",
                    dest, src,
                ))),
            },
            BinaryOpcode::Mul => match dest.checked_mul(src) {
                Some(n) => Ok(n),
                None => Err(BadProgram(format!(
                    "multiplication overflow for {} * {}",
                    dest, src,
                ))),
            },
            BinaryOpcode::Eql => Ok(if dest == src { 1 } else { 0 }),
            BinaryOpcode::Mod => match dest.checked_rem(src) {
                Some(n) => Ok(n),
                None => Err(BadProgram(format!(
                    "cannot compute {} modulo {}",
                    dest, src
                ))),
            },
            BinaryOpcode::Div => match dest.checked_div(src) {
                Some(n) => Ok(n),
                None => Err(BadProgram(format!("cannot compute {} / {}", dest, src))),
            },
        }
    }
}

impl Display for BinaryOpcode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            BinaryOpcode::Add => "add",
            BinaryOpcode::Mul => "mul",
            BinaryOpcode::Div => "div",
            BinaryOpcode::Mod => "mod",
            BinaryOpcode::Eql => "eql",
        })
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum Instruction {
    Binary {
        op: BinaryOpcode,
        dest: Reg,
        src: Operand,
    },
    Inp {
        dest: Reg,
    },
}

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::Binary { op, dest, src } => write!(f, "{} {} {}", op, dest, src),
            Instruction::Inp { dest } => write!(f, "inp {}", dest),
        }
    }
}

#[derive(Debug)]
pub struct BadInstruction {
    input: String,
    message: String,
}

impl Display for BadInstruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "bad instruction '{}': {}", self.input, self.message)
    }
}

impl Error for BadInstruction {}

fn parse_literal(input: &str) -> IResult<&str, Word> {
    map_res(
        recognize(tuple((opt(char('-')), digit1))),
        FromStr::from_str,
    )(input)
}

fn parse_reg(input: &str) -> IResult<&str, Reg> {
    alt((
        value(Reg::W, char('w')),
        value(Reg::X, char('x')),
        value(Reg::Y, char('y')),
        value(Reg::Z, char('z')),
    ))(input)
}

fn parse_operand(input: &str) -> IResult<&str, Operand> {
    alt((
        map(parse_reg, Operand::Register),
        map(parse_literal, Operand::Literal),
    ))(input)
}

fn parse_binary_opcode(input: &str) -> IResult<&str, BinaryOpcode> {
    alt((
        value(BinaryOpcode::Add, tag("add")),
        value(BinaryOpcode::Mul, tag("mul")),
        value(BinaryOpcode::Div, tag("div")),
        value(BinaryOpcode::Mod, tag("mod")),
        value(BinaryOpcode::Eql, tag("eql")),
    ))(input)
}

fn parse_binary(input: &str) -> IResult<&str, Instruction> {
    map(
        tuple((
            parse_binary_opcode,
            preceded(multispace1, parse_reg),
            preceded(multispace1, parse_operand),
        )),
        |(op, dest, src)| Instruction::Binary { op, dest, src },
    )(input)
}

fn parse_inp(input: &str) -> IResult<&str, Instruction> {
    map(preceded(pair(tag("inp"), multispace1), parse_reg), |dest| {
        Instruction::Inp { dest }
    })(input)
}

fn parse_instruction(input: &str) -> IResult<&str, Instruction> {
    alt((parse_inp, parse_binary))(input)
}

impl TryFrom<&str> for Instruction {
    type Error = BadInstruction;
    fn try_from(s: &str) -> Result<Instruction, BadInstruction> {
        match parse_instruction(s) {
            Ok((tail, instruction)) => {
                if tail.is_empty() {
                    Ok(instruction)
                } else {
                    Err(BadInstruction {
                        input: s.to_string(),
                        message: format!("unexpected trailing junk '{}'", tail),
                    })
                }
            }
            Err(e) => Err(BadInstruction {
                input: s.to_string(),
                message: e.to_string(),
            }),
        }
    }
}

fn parse_input(lines: &[&str]) -> Result<Vec<Instruction>, BadInstruction> {
    lines.iter().copied().map(Instruction::try_from).collect()
}

#[derive(Debug)]
struct ArithmeticUnit {
    registers: HashMap<Reg, Word>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct BadProgram(String);

impl Display for BadProgram {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "bad program: {}", self.0)
    }
}

impl Error for BadProgram {}

mod nfa {
    use super::*;

    #[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Hash, Clone)]
    struct State {
        w: Word,
        x: Word,
        y: Word,
        z: Word,
    }

    impl State {
        fn get(&self, r: &Reg) -> Word {
            match r {
                Reg::W => self.w,
                Reg::X => self.x,
                Reg::Y => self.y,
                Reg::Z => self.z,
            }
        }

        fn set(self, r: &Reg, value: Word) -> Self {
            match r {
                Reg::W => Self { w: value, ..self },
                Reg::X => Self { x: value, ..self },
                Reg::Y => Self { y: value, ..self },
                Reg::Z => Self { z: value, ..self },
            }
        }
    }

    fn eval_op(
        state: State,
        op: &BinaryOpcode,
        dest: &Reg,
        src: &Operand,
    ) -> Result<State, BadProgram> {
        let src_val: Word = match src {
            Operand::Register(r) => state.get(r),
            Operand::Literal(w) => *w,
        };
        let dst_val: Word = state.get(dest);
        let result: Word = op.execute(dst_val, src_val)?;
        Ok(state.set(dest, result))
    }

    pub fn execute(program: &[Instruction]) -> Result<Option<i64>, BadProgram> {
        const DIGITS: [i64; 9] = [1, 2, 3, 4, 5, 6, 7, 8, 9];
        let mut inputs_consumed: usize = 0;
        let mut largest_input_for_state: HashMap<State, i64> = HashMap::with_capacity(590490);
        largest_input_for_state.insert(
            State {
                w: 0,
                x: 0,
                y: 0,
                z: 0,
            },
            0,
        );
        for (i, instruction) in program.iter().enumerate() {
            println!(
                "Step {:>3} (consumed {:>2} inputs, tracking {:>9} states): {}",
                i,
                inputs_consumed,
                largest_input_for_state.len(),
                &instruction,
            );

            match instruction {
                Instruction::Inp { dest } => {
                    inputs_consumed += 1;
		    let mut next: HashMap<State, i64> = HashMap::with_capacity(largest_input_for_state.capacity());
                    for (curr_state, max_input) in largest_input_for_state.drain() {
                        for digit in DIGITS {
                            let n = max_input * 10 + digit;
                            let curr_max =
                                next.entry(curr_state.clone().set(dest, digit)).or_insert(0);
                            *curr_max = max(*curr_max, n);
                        }
                    }
		    largest_input_for_state = next;
                }
                Instruction::Binary { op, dest, src } => {
		    let mut next: HashMap<State, i64> = HashMap::with_capacity(largest_input_for_state.capacity());
                    for (curr_state, max_input) in largest_input_for_state.drain() {
                        let updated_state = eval_op(curr_state, op, dest, src)?;
                        let curr_max = next.entry(updated_state).or_insert(0);
                        *curr_max = max(*curr_max, max_input);
                    }
		    largest_input_for_state = next;
                }
            }
        }
        println!(
            "All steps executed.  There are {} remaining states",
            largest_input_for_state.len()
        );
        let largest: Option<i64> = largest_input_for_state
            .drain()
            .filter_map(|(state, n)| if state.z == 0 { Some(n) } else { None })
            .max();
        Ok(largest)
    }
}

fn part1(program: &[Instruction]) {
    match nfa::execute(program) {
        Ok(Some(largest)) => {
            println!("Day 24 part 1: solution is {}", largest);
        }
        Ok(None) => {
            println!("Day 24 part 1: there is no maximum");
        }
        Err(e) => {
            eprintln!("Day 24 part 1: failed: {}", e);
        }
    }
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
        Ok(program) => {
            part1(&program);
            //part2(&program);
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
