use std::collections::HashMap;
use std::cmp::{max, min, Ordering};
use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;
use std::ops::RangeInclusive;
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

    fn ranges_are_disjoint(left: &RangeInclusive<Word>,
			   right: &RangeInclusive<Word>) -> bool {
	    left.end() < right.start() ||  left.start() > right.end()
    }

    fn intersect_ranges(left: &RangeInclusive<Word>,
			right: &RangeInclusive<Word>) -> RangeInclusive<Word> {
	let begin = *max(left.start(), right.start());
	let end = *min(left.end(), right.end());
	begin..=end
    }

    #[derive(Debug, Clone, Eq)]
    pub enum Expression {
	Literal(Word),
	Input {
	    digit: u8,
	    range: RangeInclusive<Word>,
	},
	BinaryOp {
	    range: RangeInclusive<Word>,
	    op: BinaryOpcode,
	    left: Box<Expression>,
	    right: Box<Expression>,
	},
    }

    impl Display for Expression {
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
	    match self {
		Expression::Literal(w) => write!(f, "{}", w),
		Expression::Input{ digit, .. } => write!(f, "i{}", digit),
		Expression::BinaryOp { op, left, right, .. } => {
		    let operation_symbol: &str = match op {
			BinaryOpcode::Add => "+",
			BinaryOpcode::Mul => "*",
			BinaryOpcode::Div => "/",
			BinaryOpcode::Mod => "%",
			BinaryOpcode::Eql => "==",
		    };
		    write!(f, "({}{}{})", left, operation_symbol, right)
		}
	    }
	}
    }

    impl From<Word> for Expression {
	fn from(w: Word) -> Expression {
	    Expression::Literal(w)
	}
    }

    impl Ord for Expression {
	fn cmp(&self, other: &Self) -> Ordering {
	    match self {
		Expression::Literal(left) => match other {
		    Expression::Literal(right) => left.cmp(right),
		    _ => Ordering::Greater,
		}
		Expression::Input{ digit: left, .. } => match other {
		    Expression::Literal(_) => Ordering::Less,
		    Expression::Input{ digit: right, .. } => left.cmp(right),
		    _ => Ordering::Greater,
		}
		Expression::BinaryOp { range: _, op: self_op, left: self_left, right: self_right } => {
		    match other {
			Expression::Literal(_) | Expression::Input{..} => Ordering::Less,
			Expression::BinaryOp { range: _, op: other_op, left: other_left, right: other_right } => {
			    let result = self_op.cmp(other_op);
			    if result != Ordering::Equal {
				return result;
			    }
			    let result = self_left.cmp(other_left);
			    if result != Ordering::Equal {
				return result;
			    }
			    self_right.cmp(other_right)
			}
		    }
		}
	    }
	}
    }

    impl PartialOrd for Expression {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
	}
    }

    impl PartialEq for Expression {
	fn eq(&self, other: &Self) -> bool {
            self.cmp(other) == Ordering::Equal
	}
    }

    impl Expression {
	fn range(&self) -> RangeInclusive<Word> {
	    match self {
		Expression::Literal(n) => *n..=*n,
		Expression::Input{ range, .. } => range.clone(),
		Expression::BinaryOp { range, .. } => range.clone(),
	    }
	}

	fn has_disjoint_range(&self, other: &Self) -> bool {
	    ranges_are_disjoint(&self.range(), &other.range())
	}

	fn from_input(which: u8) -> Expression {
	    Expression::Input {
		digit: which,
		range: 1..=9,
	    }
	}

	fn known_to_be_zero(&self) -> bool {
	    match self {
		Expression::Literal(0) => true,
		_ => false,
	    }
	}

	fn deduce_eql_range(left: &Expression, right: &Expression) -> RangeInclusive<Word> {
	    if left == right {
		1..=1
	    } else {
		if left.has_disjoint_range(right) {
		    0..=0
		} else {
		    0..=1
		}
	    }
	}

	fn deduce_mul_range(left: &Expression, right: &Expression) -> RangeInclusive<Word> {
	    let vals = [*left.range().start(), *left.range().end(), *right.range().start(), *right.range().end()];
	    let endpoints = vals.iter().fold(
		(vals[0], vals[0]),
		|acc, val| (min(acc.0, *val), max(acc.1, *val)));
	    (endpoints.0)..=(endpoints.1)
	}

	fn deduce_add_range(left: &Expression, right: &Expression) -> RangeInclusive<Word> {
	    let begin = left.range().start() + right.range().start();
	    let end = left.range().end() + right.range().end();
	    begin..=end
	}

	fn deduce_div_range(left: &Expression, right: &Expression) -> RangeInclusive<Word> {
	    if left.range().start() >= &0 && right.range().start() >= &0 {
		(left.range().start()/right.range().end())..=(left.range().end()/right.range().start())
	    } else {
		todo!()
	    }
	}

	fn mul(a: Box<Expression>, b: Box<Expression>) -> Expression {
	    let range = Expression::deduce_mul_range(&a, &b);
	    Expression::BinaryOp {
		op: BinaryOpcode::Mul,
		left: a,
		right: b,
		range,
	    }
	}

	fn add(a: Box<Expression>, b: Box<Expression>) -> Expression {
	    let range = Expression::deduce_add_range(&a, &b);
	    Expression::BinaryOp {
		op: BinaryOpcode::Add,
		left: a,
		right: b,
		range,
	    }
	}

	fn eql(a: Box<Expression>, b: Box<Expression>) -> Expression {
	    Expression::BinaryOp {
		op: BinaryOpcode::Eql,
		left: a,
		right: b,
		range: 0..=1,
	    }
	}
    }


    fn simplify_input_equality(
	digit: u8,
	range: &RangeInclusive<Word>,
	other: Expression,
    ) -> Expression {
	match &other {
	    // No input is zero or greater than 9.
	    Expression::Literal(n) if *n == 0 || *n > 9 => Expression::from(0),
	    Expression::Input { digit: other_digit, .. } if digit == *other_digit => Expression::from(1),
	    Expression::BinaryOp { range: other_range, .. } if ranges_are_disjoint(range, other_range) =>
		Expression::from(0),
	    _ => {
		Expression::eql(
		    Box::new(Expression::Input {
			digit,
			range: range.clone(),
		    }),
		    Box::new(other))
	    }
	}
    }

    fn simplify_add(left: Expression, right: Expression) -> Expression {
	match commuting_pair(left, right) {
	    (x, expr) | (expr, x) if expr.known_to_be_zero() => x,
	    (l, r) if l == r => Expression::mul(
		Box::new(Expression::from(2)),
		Box::new(l)
	    ),
	    (Expression::Literal(a), Expression::Literal(b)) => {
		Expression::from(a + b)
	    }
	    (l, r) => Expression::add(
		Box::new(l),
		Box::new(r),
	    ),
	}
    }

    fn simplify_mul(left: Expression, right: Expression) -> Expression {
	match commuting_pair(left, right) {
	    (_, exp) | (exp, _) if exp.known_to_be_zero() => Expression::from(0),
	    (x, Expression::Literal(1)) | (Expression::Literal(1), x) => x,
	    (Expression::Literal(a), Expression::Literal(b)) => {
		Expression::from(a * b)
	    }

	    // Factorise (a+b)(a+d) to a(b+d).
	    (
		Expression::BinaryOp { op: BinaryOpcode::Add, left: a, right: b, range: _},
		Expression::BinaryOp { op: BinaryOpcode::Add, left: c, right: d, range: _},
	    ) if a == c => Expression::mul(a, Box::new(Expression::add(b, d))),

	    // Factorise (a+b)(c+b) to b(a+c).
	    (
		Expression::BinaryOp { op: BinaryOpcode::Add, left: a, right: b, range: _},
		Expression::BinaryOp { op: BinaryOpcode::Add, left: c, right: d, range: _},
	    ) if b == d => {
		// XXX: we may know the range of a+c already.
		Expression::mul(b, Box::new(Expression::add(a, c)))
	    }

	    // XXX: reorganise so we don't discard range information.
	    (l, r) => Expression::mul(Box::new(l), Box::new(r)),
	}
    }

    fn simplify_div(left: Expression, right: Expression) -> Expression {
	match (left, right) {
	    (x, Expression::Literal(1)) | (Expression::Literal(1), x) => x,
	    (Expression::Literal(a), Expression::Literal(b)) => Expression::from(a / b),
	    (l, r) => {
		if l == r {
		    Expression::from(1)
		} else {
		    let range = Expression::deduce_div_range(&l, &r);
		    Expression::BinaryOp {
			op: BinaryOpcode::Div,
			left: Box::new(l),
			right: Box::new(r),
			range,
		    }
		}
	    }
	}
    }

    fn simplify_mod(left: Expression, right: Expression) -> Expression {
	match (left, right) {
	    (Expression::Literal(a), Expression::Literal(b)) => Expression::from(a % b),
	    (l, r) if l == r => Expression::from(0),
	    (l, Expression::Literal(modulus)) => {
		Expression::BinaryOp {
		    op: BinaryOpcode::Mod,
		    left: Box::new(l),
		    right: Box::new(Expression::from(modulus)),
		    range: 0..=modulus,
		}
	    }
	    _ => todo!(),
	}
    }

    /// Swap the operands of a commutative operation such that one kind of
    /// argument reproducibly goes on the left.  This should allow other
    /// rules to notice that two expressions are structurally identical.
    ///
    /// This is based on the idea that for any commutative operation @, (a
    /// @ b) = (b @ a) for any a, b.
    fn commuting_pair(left: Expression, right: Expression) -> (Expression, Expression) {
	if left < right {
	    (left, right)
	} else {
	    (right, left)
	}
    }

    /// Simplify (a @ b) = (c @ d)
    fn simplify_commutative_equality(
	the_op: BinaryOpcode,
	a: Expression,
	b: Expression,
	left_range: RangeInclusive<Word>,
	c: Expression,
	d: Expression,
	right_range: RangeInclusive<Word>,
	expr_range: RangeInclusive<Word>,
    ) -> Expression {
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
	    let left = Expression::BinaryOp {
		op: the_op,
		left: Box::new(a),
		right: Box::new(b),
		range: left_range,
	    };
	    let right = Expression::BinaryOp {
		op: the_op,
		left: Box::new(c),
		right: Box::new(d),
		range: right_range,
	    };
	    Expression::BinaryOp {
		op: BinaryOpcode::Eql,
		left: Box::new(left),
		right: Box::new(right),
		range: expr_range,
	    }
	}
    }

    fn simplify_eql(
	left: Expression,
	right: Expression,
    ) -> Expression {
	match &commuting_pair(left, right) {
	    (Expression::Literal(a), Expression::Literal(b)) => {
		if a == b {
		    Expression::from(1)
		} else {
		    Expression::from(0)
		}
	    }
	    (Expression::Input{ digit, range }, other)  | (other, Expression::Input{ digit, range })  => {
		simplify_input_equality(*digit, range, other.clone())
	    }

	    (l, r) if l == r => Expression::from(1),

	    (l, r) if l.has_disjoint_range(r) => {
		Expression::from(0)
	    }

	    // simplify (a @ b) = (c @ d) for any commutative operation @.
	    (
		// left is a @ b
		Expression::BinaryOp {
		    op: left_op,
		    left: a,
		    right: b,
		    range: left_range,
		},
		// right is c @ d.
		Expression::BinaryOp {
		    op: right_op,
		    left: c,
		    right: d,
		    range: right_range,
		},
	    ) if left_op == right_op => {
		// XXX: when we have implemented deduced properties as
		// attributes of Expression, then this case may
		// discard things we know about left or right.
		simplify_commutative_equality(
		    *left_op,
		    *(*a).clone(), *(*b).clone(), left_range.clone(),
		    *(*c).clone(), *(*d).clone(), right_range.clone(),
		    0..=1)
	    }

	    (l, r) => {
		Expression::BinaryOp {
		    op: BinaryOpcode::Eql,
		    left: Box::new(l.clone()),
		    right: Box::new(r.clone()),
		    range: 0..=1,
		}
	    }
	}
    }

    fn collapse_degenerate_range(input: Expression) -> Expression {
	if let Expression::Literal(_) = &input {
	    input
	} else {
	    let range = input.range();
	    if range.start() == range.end() {
		println!("replacing {} with literal {}", &input, range.start());
		Expression::Literal(*range.start())
	    } else {
		input
	    }
	}
    }

    fn simplify(input: Expression) -> Expression {
	collapse_degenerate_range(
	    match input {
		Expression::Literal(_) => input,
		Expression::Input{..} => input,
		Expression::BinaryOp{ op, left, right, range: _range } => {
		    // XXX: preserve/use range value
		    match (op, *left, *right) {
			(BinaryOpcode::Add, l, r) => simplify_add(l, r),
			(BinaryOpcode::Mul, l, r) => simplify_mul(l, r),
			(BinaryOpcode::Div, l, r) => simplify_div(l, r),
			(BinaryOpcode::Mod, l, r) => simplify_mod(l, r),
			(BinaryOpcode::Eql, l, r) => simplify_eql(l, r),
		    }
		}
	    }
	)
    }

    pub fn symbolic_expression(program: &[Instruction]) -> Expression {
	let mut registers: HashMap<Reg, Expression> = {
	    let mut regs = HashMap::new();
	    for r in [Reg::W, Reg::X, Reg::Y, Reg::Z] {
		regs.insert(r, Expression::from(0));
	    }
	    regs
	};
	let mut inputs_consumed: u8 = 0;
	for (i, instruction) in program.iter().enumerate() {
	    println!("symbolic_expression: {:>03}: including {}", i, &instruction);
	    match instruction {
		Instruction::Inp{dest} => {
		    registers.insert(*dest, Expression::from_input(inputs_consumed));
		    inputs_consumed += 1;
		}
		Instruction::Binary{op, dest, src} => {
		    let right: Box<Expression> = match src {
			Operand::Register(src) => match registers.get(src) {
			    Some(val) => Box::new(val.clone()),
			    None => {
				panic!("unknown source register {}", src);
			    }
			}
			Operand::Literal(n) => Box::new(Expression::from(*n)),
		    };
		    if let Some(lop) = registers.remove(dest) {
			let range = lop.range().clone();
			let left: Box<Expression> = Box::new(lop);
			registers.insert(*dest,
					 simplify(
					     Expression::BinaryOp {
						 op: *op,
						 left,
						 right,
						 range,
					     }
					 )
			);
		    } else {
			panic!("unknown destination register {}", dest);
		    }
		}
	    }
	}
	registers.get(&Reg::Z).unwrap().clone()
    }

    fn constrain(
	input: Expression,
	range: &RangeInclusive<Word>
    ) -> Expression {
	match input {
	    Expression::Literal(n) => {
		if !range.contains(&n) {
		    panic!("constraining expression to range {:?} but the expression is {:?}", range, input);
		}
		Expression::Literal(n)
	    }
	    Expression::Input { digit, range: input_range, } => {
		if ranges_are_disjoint(&input_range, range) {
		    panic!("constraining expression to range {:?} but the expression has range {:?}", &range, &input_range);
		}
		Expression::Input { digit, range: intersect_ranges(range, &input_range) }
	    }
	    Expression::BinaryOp { range: bop_range, op, left, right } => {
		Expression::BinaryOp {
		    range: intersect_ranges(range, &bop_range),
		    op,
		    left,
		    right,
		}
	    }
	}
    }

    pub fn constrain_to_zero(input: Expression) -> Expression {
	let just_zero = 0..=0;
	constrain(input, &just_zero)
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
	    let constrained = symbolic::constrain_to_zero(sym);
	    println!("symbolic form of program is {}", constrained);
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
