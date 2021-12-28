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
struct BadProgram(String);

impl Display for BadProgram {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "bad program: {}", self.0)
    }
}

impl Error for BadProgram {}

fn initial_registers() -> HashMap<Reg, Word> {
    let mut regs = HashMap::new();
    regs.insert(Reg::W, 0);
    regs.insert(Reg::X, 0);
    regs.insert(Reg::Y, 0);
    regs.insert(Reg::Z, 0);
    regs
}

impl ArithmeticUnit {
    fn new() -> ArithmeticUnit {
        ArithmeticUnit {
	    registers: initial_registers(),
	}
    }

    fn set_reg(&mut self, r: &Reg, value: Word) {
        self.registers.insert(*r, value);
    }

    fn get_reg(&self, r: &Reg) -> Word {
        match self.registers.get(r) {
            Some(&n) => n,
            None => {
                panic!("Register {} was unexpectedly deleted", r);
            }
        }
    }

    fn fetch(&self, operand: &Operand) -> Word {
        match operand {
            Operand::Register(r) => self.get_reg(r),
            Operand::Literal(n) => *n,
        }
    }

    /// Execute a sequence of instructions, returning the value in the z register
    fn execute(
        &mut self,
        program: &[Instruction],
        inputs: &mut Vec<Word>, // reversed: last element is first input, etc.
    ) -> Result<Word, BadProgram> {
	self.registers = initial_registers();

        for instruction in program {
            match instruction {
                Instruction::Binary { op, dest, src } => {
                    match op.execute(self.get_reg(dest), self.fetch(src)) {
                        Ok(result_val) => {
                            self.set_reg(dest, result_val);
                        }
                        Err(e) => {
                            return Err(BadProgram(format!(
                                "failed while executing instruction '{}': {}",
                                instruction, e,
                            )));
                        }
                    }
                }
                Instruction::Inp { dest } => match inputs.pop() {
                    None => {
                        return Err(BadProgram("ran out of input".to_string()));
                    }
                    Some(value) => {
                        self.registers.insert(*dest, value);
                    }
                },
            }
        }
        if !inputs.is_empty() {
            return Err(BadProgram("some input was not consumed".to_string()));
        }
        match self.registers.get(&Reg::Z) {
            Some(&z) => Ok(z),
            None => {
                panic!("Register Z was unexpectedly deleted");
            }
        }
    }
}

#[test]
fn test_execute_sample_1() {
    let program = vec![
        Instruction::Inp { dest: Reg::X },
        Instruction::Binary {
            op: BinaryOpcode::Mul,
            dest: Reg::X,
            src: Operand::Literal(-1),
        },
    ];
    let mut alu = ArithmeticUnit::new();
    assert_eq!(alu.execute(&program, &mut vec![4]), Ok(0));
    assert_eq!(alu.get_reg(&Reg::X), -4);
}

#[test]
fn test_execute_sample_2() {
    let program = vec![
        Instruction::Inp { dest: Reg::Z },
        Instruction::Inp { dest: Reg::X },
        Instruction::Binary {
            op: BinaryOpcode::Mul,
            dest: Reg::Z,
            src: Operand::Literal(3),
        },
        Instruction::Binary {
            op: BinaryOpcode::Eql,
            dest: Reg::Z,
            src: Operand::Register(Reg::X),
        },
    ];
    assert_eq!(
        ArithmeticUnit::new().execute(&program, &mut vec![9, 3]),
        Ok(1)
    );
    assert_eq!(
        ArithmeticUnit::new().execute(&program, &mut vec![3, 9]),
        Ok(0)
    );
    assert_eq!(
        ArithmeticUnit::new().execute(&program, &mut vec![10, 3]),
        Ok(0)
    );
}

#[test]
fn test_execute_sample_3() {
    fn check(
        input_val: Word,
        expected_w: Word,
        expected_x: Word,
        expected_y: Word,
        expected_z: Word,
    ) {
        let program_text: Vec<&str> = concat!(
            "inp w\n",
            "add z w\n",
            "mod z 2\n",
            "div w 2\n",
            "add y w\n",
            "mod y 2\n",
            "div w 2\n",
            "add x w\n",
            "mod x 2\n",
            "div w 2\n",
            "mod w 2\n",
        )
        .split_terminator('\n')
        .collect();
        let program = parse_input(&program_text).expect("test input is a valid program");

        let mut alu = ArithmeticUnit::new();
        assert_eq!(alu.execute(&program, &mut vec![input_val]), Ok(expected_z));
        assert_eq!(
            alu.get_reg(&Reg::Z),
            expected_z,
            "z wrong for input {}",
            input_val
        );
        assert_eq!(
            alu.get_reg(&Reg::Y),
            expected_y,
            "y wrong for input {}",
            input_val
        );
        assert_eq!(
            alu.get_reg(&Reg::X),
            expected_x,
            "y wrong for input {}",
            input_val
        );
        assert_eq!(
            alu.get_reg(&Reg::W),
            expected_w,
            "y wrong for input {}",
            input_val
        );
    }

    check(0, 0, 0, 0, 0);
    check(1, 0, 0, 0, 1);
    check(2, 0, 0, 1, 0);
    check(4, 0, 1, 0, 0);
    check(8, 1, 0, 0, 0);
    check(6, 0, 1, 1, 0);
    check(7, 0, 1, 1, 1);
    check(15, 1, 1, 1, 1);
}

fn make_input(val: i64) -> Option<Vec<Word>> {
    const DECIMAL: u32 = 10;
    let s = val.to_string();
    if s.contains('0') {
        None
    } else {
        let inputs = s
            .chars()
            .rev() // rightmost item should be first input.
            .map(|ch| match ch.to_digit(DECIMAL) {
                Some(n) => n.into(),
                None => {
                    panic!("non-digit {} in string value {} of {}", ch, s, val);
                }
            })
            .collect();
        Some(inputs)
    }
}


fn solve_worker<I: Iterator<Item=Word>>(
    program: &[Instruction],
    trials: I
) -> Result<Option<Word>, BadProgram> {
    let mut nonskipped: u64 = 0;
    for serial in trials {
	let verbose = (nonskipped < 10) || (serial % 1_000_000 == 111_111);
        let inputs = make_input(serial);
	if verbose {
	    println!("serial {}: inputs {:?}, unskipped {}", serial, &inputs, nonskipped);
	}
	match inputs {
            None => {
		if verbose {
		    println!("Skipping {}", serial);
		}
	    }
            Some(inputs) if inputs.len() != 14 => {
                panic!(
                    "incorrect size input {}; length is {}",
                    serial,
                    inputs.len()
                );
            }
            Some(mut inputs) => {
		nonskipped += 1;
		if verbose || nonskipped < 10 {
		    print!(
			"checking {:>14}: ",
			serial,
		    );
		}
                let mut alu = ArithmeticUnit::new();
		match alu.execute(program, &mut inputs) {
                    Err(e) => {
                        return Err(e);
                    }
		    Ok(z) => {
			if verbose {
			    println!(
				"result {}; ALU is {:?}",
				z,
				&alu
			    );
			}
			if z == 0 {
                            return Ok(Some(serial));
			}
		    }
                }
            }
        }
    }
    Ok(None)
}

fn solve1(program: &[Instruction]) -> Result<Option<Word>, BadProgram> {
    let range = 11_111_111_111_111..111_111_111_111_111;
    solve_worker(program, range.rev())
}


mod symbolic {
    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
    pub enum DeferredOperand {
	Literal(Word),
	Input(u8),
	BinaryOperation{
	    op: BinaryOpcode,
	    left: Box<DeferredOperand>,
	    right: Box<DeferredOperand>,
	},
    }


    fn simplify_input_equality(input_number: u8, other: DeferredOperand) -> DeferredOperand {
	match &other {
	    // No input is zero or greater than 9.
	    DeferredOperand::Literal(n) if *n == 0 || *n > 9 => DeferredOperand::Literal(0),
	    _ => DeferredOperand::BinaryOperation {
		op: BinaryOpcode::Eql,
		left: Box::new(DeferredOperand::Input(input_number)),
		right: Box::new(other),
	    }
	}
    }

    fn simplify_add(left: DeferredOperand, right: DeferredOperand) -> DeferredOperand {
	match commuting_pair(left, right) {
	    (x, DeferredOperand::Literal(0)) | (DeferredOperand::Literal(0), x) => x,
	    (l, r) if l == r => {
		DeferredOperand::BinaryOperation {
		    op: BinaryOpcode::Mul,
		    left: Box::new(l),
		    right: Box::new(DeferredOperand::Literal(2)),
		}
	    }
	    (DeferredOperand::Literal(a), DeferredOperand::Literal(b)) => {
		DeferredOperand::Literal(a + b)
	    }
	    (l, r) => {
		DeferredOperand::BinaryOperation {
		    op: BinaryOpcode::Add,
		    left: Box::new(l),
		    right: Box::new(r),
		}
	    }
	}
    }

    fn simplify_mul(left: DeferredOperand, right: DeferredOperand) -> DeferredOperand {
	match commuting_pair(left, right) {
	    (_, DeferredOperand::Literal(0)) | (DeferredOperand::Literal(0), _) => DeferredOperand::Literal(0),
	    (x, DeferredOperand::Literal(1)) | (DeferredOperand::Literal(1), x) => x,
	    (DeferredOperand::Literal(a), DeferredOperand::Literal(b)) => {
		DeferredOperand::Literal(a * b)
	    }

	    // Factorise (a+b)(a+d) to a(b+d).
	    (
		DeferredOperand::BinaryOperation { op: BinaryOpcode::Add, left: a, right: b, },
		DeferredOperand::BinaryOperation { op: BinaryOpcode::Add, left: c, right: d, }
	    ) if a == c => {
		DeferredOperand::BinaryOperation {
		    op: BinaryOpcode::Mul,
		    left: a,
		    right: Box::new(DeferredOperand::BinaryOperation {
			op: BinaryOpcode::Add,
			left: b,
			right: d,
		    }),
		}
	    }

	    // Factorise (a+b)(c+b) to b(a+c).
	    (
		DeferredOperand::BinaryOperation { op: BinaryOpcode::Add, left: a, right: b, },
		DeferredOperand::BinaryOperation { op: BinaryOpcode::Add, left: c, right: d, }
	    ) if b == d => {
		DeferredOperand::BinaryOperation {
		    op: BinaryOpcode::Mul,
		    left: b,
		    right: Box::new(DeferredOperand::BinaryOperation {
			op: BinaryOpcode::Add,
			left: a,
			right: c,
		    }),
		}
	    }

	    (l, r) => {
		DeferredOperand::BinaryOperation {
		    op: BinaryOpcode::Mul,
		    left: Box::new(l),
		    right: Box::new(r),
		}
	    }
	}
    }

    fn simplify_div(left: DeferredOperand, right: DeferredOperand) -> DeferredOperand {
	match (left, right) {
	    (x, DeferredOperand::Literal(1)) | (DeferredOperand::Literal(1), x) => x,
	    (DeferredOperand::Literal(a), DeferredOperand::Literal(b)) => {
		DeferredOperand::Literal(a / b)
	    }
	    (l, r) => {
		if l == r {
		    DeferredOperand::Literal(1)
		} else {
		    DeferredOperand::BinaryOperation {
			op: BinaryOpcode::Div,
			left: Box::new(l),
			right: Box::new(r),
		    }
		}
	    }
	}
    }

    fn simplify_mod(left: DeferredOperand, right: DeferredOperand) -> DeferredOperand {
	match (left, right) {
	    (DeferredOperand::Literal(a), DeferredOperand::Literal(b)) => {
		DeferredOperand::Literal(a % b)
	    }
	    (l, r) if l == r => {
		DeferredOperand::Literal(0)
	    }
	    (l, r) => {
		DeferredOperand::BinaryOperation {
		    op: BinaryOpcode::Mod,
		    left: Box::new(l),
		    right: Box::new(r),
		}
	    }
	}
    }

    /// Swap the operands of a commutative operation such that one kind of
    /// argument reproducibly goes on the left.  This should allow other
    /// rules to notice that two expressions are structurally identical.
    ///
    /// This is based on the idea that for any commutative operation @, (a
    /// @ b) = (b @ a) for any a, b.
    fn commuting_pair(left: DeferredOperand, right: DeferredOperand) -> (DeferredOperand, DeferredOperand) {
	if left < right {
	    (left, right)
	} else {
	    (right, left)
	}
    }

    /// Simplify (a @ b) = (c @ d)
    fn simplify_commutative_equality(
	the_op: BinaryOpcode,
	a: DeferredOperand,
	b: DeferredOperand,
	c: DeferredOperand,
	d: DeferredOperand,
    ) -> DeferredOperand {
	assert!(the_op == BinaryOpcode::Add || the_op == BinaryOpcode::Mul);

	if a == c {
	    simplify_eql(b, d)
	} else if a == d {
	    simplify_eql(b, c)
	} else if b == c {
	    simplify_eql(a, d)
	} else if b == d {
	    simplify_eql(a, c)
	} else {
	    DeferredOperand::BinaryOperation {
		op: BinaryOpcode::Eql,
		left: Box::new(DeferredOperand::BinaryOperation {
		    op: the_op,
		    left: Box::new(a),
		    right: Box::new(b),
		}),
		right: Box::new(DeferredOperand::BinaryOperation {
		    op: the_op,
		    left: Box::new(c),
		    right: Box::new(d),
		}),
	    }
	}
    }

    fn simplify_eql(left: DeferredOperand, right: DeferredOperand) -> DeferredOperand {
	match commuting_pair(left, right) {
	    (DeferredOperand::Literal(a), DeferredOperand::Literal(b)) => {
		if a == b {
		    DeferredOperand::Literal(1)
		} else {
		    DeferredOperand::Literal(0)
		}
	    }
	    (DeferredOperand::Input(a), DeferredOperand::Input(b)) if a == b => {
		DeferredOperand::Literal(1)
	    }
	    (DeferredOperand::Input(inp), other)  | (other, DeferredOperand::Input(inp))  => {
		simplify_input_equality(inp, other)
	    }

	    (l, r) if l == r => DeferredOperand::Literal(1),

	    // simplify (a @ b) = (c @ d) for any commutative operation @.
	    (
		// left is a @ b
		DeferredOperand::BinaryOperation {
		    op: left_op,
		    left: a,
		    right: b,
		},
		// right is c @ d.
		DeferredOperand::BinaryOperation {
		    op: right_op,
		    left: c,
		    right: d,
		},
	    ) if left_op == right_op => {
		simplify_commutative_equality(left_op, *a, *b, *c, *d)
	    }

	    (l, r) => {
		DeferredOperand::BinaryOperation {
		    op: BinaryOpcode::Eql,
		    left: Box::new(l),
		    right: Box::new(r),
		}
	    }
	}
    }


    fn simplify(input: DeferredOperand) -> DeferredOperand {
	match input {
	    DeferredOperand::Literal(_) | DeferredOperand::Input(_) => input,
	    DeferredOperand::BinaryOperation{ op, left, right } => {
		match (op, *left, *right) {
		    (BinaryOpcode::Add, l, r) => simplify_add(l, r),
		    (BinaryOpcode::Mul, l, r) => simplify_mul(l, r),
		    (BinaryOpcode::Div, l, r) => simplify_div(l, r),
		    (BinaryOpcode::Mod, l, r) => simplify_mod(l, r),
		    (BinaryOpcode::Eql, l, r) => simplify_eql(l, r),
		}
	    }
	}
    }


    pub fn symbolic_expression(program: &[Instruction]) -> DeferredOperand {
	let mut registers: HashMap<Reg, DeferredOperand> = {
	    let mut regs = HashMap::new();
	    for r in [Reg::W, Reg::X, Reg::Y, Reg::Z] {
		regs.insert(r, DeferredOperand::Literal(0));
	    }
	    regs
	};
	let mut inputs_consumed: u8 = 0;
	for (i, instruction) in program.iter().enumerate() {
	    println!("symbolic_expression: {:>03}: including {}", i, &instruction);
	    match instruction {
		Instruction::Inp{dest} => {
		    registers.insert(*dest, DeferredOperand::Input(inputs_consumed));
		    inputs_consumed += 1;
		}
		Instruction::Binary{op, dest, src} => {
		    let right: Box<DeferredOperand> = match src {
			Operand::Register(src) => match registers.get(src) {
			    Some(val) => Box::new(val.clone()),
			    None => {
				panic!("unknown source register {}", src);
			    }
			}
			Operand::Literal(n) => Box::new(DeferredOperand::Literal(*n)),
		    };
		    if let Some(lop) = registers.remove(dest) {
			let left: Box<DeferredOperand> = Box::new(lop);
			registers.insert(*dest, simplify(DeferredOperand::BinaryOperation {
			    op: *op,
			    left,
			    right,
			}));
		    } else {
			panic!("unknown destination register {}", dest);
		    }
		}
	    }
	}
	registers.get(&Reg::Z).unwrap().clone()
    }
}

fn part1(program: &[Instruction]) {
    match solve1(program) {
        Ok(None) => {
            println!("Day 24 part 1: did not find a solution");
        }
        Ok(Some(n)) => {
            println!("Day 24 part 1: solution is {}", n);
        }
        Err(e) => {
            eprintln!("Day 24 part 1: failed: {}", e);
        }
    }
}

fn part2(_program: &[Instruction]) {}

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
	    let sym = symbolic::symbolic_expression(&program);
	    println!("symbolic form of program is {:#?}", sym);
            //part1(&program);
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
