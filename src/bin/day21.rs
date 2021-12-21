
struct Die {
    next_roll: usize,
    total_rolls: usize,
}

impl Die {
    pub fn new() -> Die {
	Die {
	    next_roll: 1,
	    total_rolls: 0,
	}
    }

    pub fn roll3(&mut self) -> Vec<usize> {
	vec![self.roll1(), self.roll1(),self.roll1()]
    }

    fn roll1(&mut self) -> usize {
	let result = self.next_roll;
	self.next_roll += 1;
	if self.next_roll > 100 {
	    self.next_roll = 1
	}
	self.total_rolls += 1;
	result
    }
}

struct Player {
    id: i8,
    pos: usize,
    score: usize,
}

fn next_pos(current: usize, rolled: usize) -> usize {
    (current + rolled - 1) % 10 + 1
}

#[test]
fn test_next_pos() {
    assert_eq!(next_pos(4, 3), 7);
    assert_eq!(next_pos(4, 6), 10);
    assert_eq!(next_pos(4, 7), 1);
}


impl Player {
    fn new(id: i8, initial_pos: usize) -> Player {
	Player {
	    id,
	    pos: initial_pos,
	    score: 0
	}
    }

    fn score(&self) -> usize {
	self.score
    }

    fn won(&self) -> bool {
	self.score() >= 1000
    }

    fn advance(&mut self, by: usize) {
	let next = next_pos(self.pos, by);
	println!(
	    "Player {} advances by {}, moving from space {} to space {}",
	    self.id, by, self.pos, next,
	);
	self.pos = next;
	self.score += self.pos
    }

    fn turn(&mut self, die: &mut Die) -> bool {
	let rolled = die.roll3();
	self.advance(rolled.iter().sum());
	println!(
	    "Player {} rolls {}+{}+{} and moves to space {} for a total score of {}.",
	    self.id,
	    rolled[0],
	    rolled[1],
	    rolled[2],
	    self.pos,
	    self.score()
	);
	self.won()
    }
}

fn simulate(
    p1pos: usize,
    p2pos: usize) -> (u8, usize, usize) {
    let mut die = Die::new();
    let mut p1 = Player::new(1, p1pos);
    let mut p2 = Player::new(2, p2pos);
    loop {
	if p1.turn(&mut die) { break; }
	if p2.turn(&mut die) { break; }
    }
    match (p1.won(), p2.won()) {
	(true, false) => (1, p2.score(), die.total_rolls),
	(false, true) => (2, p1.score(), die.total_rolls),
	_ => unreachable!(),
    }
}

fn part1(p1pos: usize, p2pos: usize) {
    let (winner, losing_score, total_rolls) = simulate(p1pos, p2pos);
    println!(
	"Day 21 part 1: winner is {}; {}*{} = {}",
	winner,
	losing_score,
	total_rolls,
	losing_score*total_rolls
    );
}


#[test]
fn test_simulate() {
    let (winner, losing_score, total_rolls) = simulate(4, 8);
    assert_eq!(winner, 1);
    assert_eq!(losing_score, 745);
    assert_eq!(total_rolls, 993);
}

fn main() {
    let p1pos = 3;
    let p2pos = 10;
    part1(p1pos, p2pos);
}
