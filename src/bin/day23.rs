use std::collections::HashSet;
use std::collections::HashMap;
use std::cmp::{max, min};
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::{Add, AddAssign, Mul};

use pathfinding::directed::astar::astar;
use pathfinding::num_traits::Zero;

//            1
//  01234567890
// #############
// #...........# 0 (hallway)
// ###B#C#B#D### 1 (room)
//   #A#D#C#A#   2 (room)
//   #########
//  01234567890
//            1

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
struct Cost(u64);

impl Zero for Cost {
    fn zero() -> Self {
	Cost(0)
    }
    fn is_zero(&self) -> bool {
	self.0 == 0
    }
}

impl Mul<u64> for Cost {
    type Output = Cost;
    fn mul(self, n: u64) -> <Self as Mul<u64>>::Output {
	Cost(self.0 * n)
    }
}

impl AddAssign<Cost> for Cost {
    fn add_assign(&mut self, rhs: Cost) {
	self.0 += rhs.0
    }
}

impl Add<Cost> for Cost {
    type Output = Cost;
    fn add(self, other: Cost) -> <Self as Add<Cost>>::Output {
	Cost(self.0 + other.0)
    }
}

impl Display for Cost {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
	std::fmt::Display::fmt(&self.0, f)
    }
}


#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
enum Amphipod {
    A, B, C, D
}

impl Amphipod {
    fn move_cost(&self) -> Cost {
	match self {
	    Amphipod::A => Cost(1),
	    Amphipod::B => Cost(10),
	    Amphipod::C => Cost(100),
	    Amphipod::D => Cost(1000),
	}
    }

    fn symbol(&self) -> char {
	match self {
	    Amphipod::A => 'A',
	    Amphipod::B => 'B',
	    Amphipod::C => 'C',
	    Amphipod::D => 'D',
	}
    }
}

impl TryFrom<char> for Amphipod {
    type Error = String;
    fn try_from(ch: char) -> Result<Amphipod, String> {
	match ch {
	    'A' => Ok(Amphipod::A),
	    'B' => Ok(Amphipod::B),
	    'C' => Ok(Amphipod::C),
	    'D' => Ok(Amphipod::D),
	    _ => Err(format!("unknown symbol {}, should be A, B, C or D", ch))
	}
    }
}

#[derive(Debug, PartialEq, Eq)]
enum LocationType {
    Hallway,
    Doormat(Amphipod),		// immediately outside room
    Room(Amphipod),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
struct Position {
    x: u8,
    y: u8,
}

impl Debug for Position {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
	write!(f, "({},{})", &self.x, &self.y)
    }
}

impl Position {
    fn manhattan(&self, other: &Position) -> u64 {
	let xdist: u64 = u64::from(max(self.x, other.x)) - u64::from(min(self.x, other.x));
	let ydist: u64 = u64::from(max(self.y, other.y)) - u64::from(min(self.y, other.y));
	xdist + ydist
    }

    fn neighbours(&self, other: &Position) -> bool {
	let dx: u8 = max(self.x, other.x) - min(self.x, other.x);
	let dy: u8 = max(self.y, other.y) - min(self.y, other.y);
	dx + dy == 1
    }

    fn north(&self, dist: u8) -> Option<Position> {
	if self.y >= dist {
	    Some(Position {
		x: self.x,
		y: self.y - dist,
	    })
	} else {
	    None
	}
    }

    fn south(&self, dist: u8) -> Option<Position> {
	let y = self.y + dist;
	if y <= 2 {
	    match self.x {
		2|4|6|8 => Some(Position {
		    x: self.x,
		    y,
		}),
		_ => None,
	    }
	} else {
	    None
	}
    }

    fn doormat_of(who: &Amphipod) -> Position {
	let x = match who {
	    Amphipod::A => 2,
	    Amphipod::B => 4,
	    Amphipod::C => 6,
	    Amphipod::D => 8,
	};
	Position {
	    x,
	    y: 0,
	}
    }

    fn is_column_for(x: u8) -> Option<Amphipod> {
	match x {
	    2 => Some(Amphipod::A),
	    4 => Some(Amphipod::B),
	    6 => Some(Amphipod::C),
	    8 => Some(Amphipod::D),
	    _ => None,
	}
    }

    fn get_type(&self) -> LocationType {
	match Self::is_column_for(self.x) {
	    None => LocationType::Hallway,
	    Some(family) => match self.y {
		0 => LocationType::Doormat(family),
		1|2 => LocationType::Room(family),
		_ => {
		    panic!("Unable to determine the type of location {:?}", &self);
		}
	    }
	}
    }

    fn is_doormat(&self) -> bool {
	matches!(self.get_type(), LocationType::Doormat(_))
    }
}

#[derive(Clone)]
struct Path {
    pub steps: Vec<Position>,
    checked: Option<Position>,
}

impl Debug for Path {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
	// We deliberately ignore the `alternate` flag to save space.
	write!(f, "Path{{ steps: {:?}, checked: {:?} }}", &self.steps, &self.checked)
    }
}

impl Path {
    fn from_step(pos: Position) -> Path {
	Path {
	    steps: vec![pos],
	    checked: None,
	}
    }

    fn from_steps(steps: Vec<Position>) -> Path {
	Path {
	    steps,
	    checked: None,
	}
    }

    fn then_move_to(mut self, pos: Position) -> Path {
	match self.steps.last() {
	    Some(last) => {
		if last.neighbours(&pos) {
		    self.steps.push(pos);
		} else {
		    panic!("new position {:?} is not adjacent to the end of the current path {:?}",
			   &pos, last);
		}
	    }
	    None => {
		panic!("then_move_to: existing path is empty");
	    }
	}
	self
    }

    fn join(&self, then: &Path) -> Path {
	assert!(self.checked.is_some());
	let last = self.steps.last().unwrap();
	match then.steps.first() {
	    None => { panic!("joining empty path"); }
	    Some(initial) => {
		if last.neighbours(initial) {
		    let mut steps = Vec::with_capacity(self.steps.len() + then.steps.len());
		    steps.extend(&self.steps);
		    steps.extend(&then.steps);
		    Path { steps, checked: self.checked }
		} else {
		    panic!("joining paths which don't meet");
		}
	    }
	}
    }

    fn sanity_check(&mut self, start: &Position) -> Result<(), String> {
	if let Some(checked_from) = &self.checked {
	    if checked_from == start {
		return Ok(());	// already done.
	    }
	}
	let mut prev: &Position = start;
	for (i, step) in self.steps.iter().enumerate() {
	    if !step.neighbours(prev) {
		return Err(format!(
		    "step {} from {:?} to {:?} is not a direct neighbour",
		    i, prev, step,
		));
	    }
	    prev = step;
	}
	self.checked = Some(*start);
	Ok(())
    }

    fn checked(mut self, start: &Position) -> Result<Self, String> {
	self.sanity_check(start).map(|()| self)
    }

    fn last(&self) -> Option<&Position> {
	self.steps.last()
    }

    fn total_cost(&self, unit_cost: Cost) -> Cost {
	unit_cost * (self.steps.len() as u64)
    }
}

fn sanity_check_paths<'a, I>(paths: I, start: &Position) -> Result<(), String>
where
    I: IntoIterator<Item = &'a mut Path>
{
    for path in paths.into_iter() {
	path.sanity_check(start)?;
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct State {
    location_contents: HashMap<Position, Amphipod>,
}

type SquishedState = Vec<(Amphipod,Position)>;


impl State {
    pub fn new() -> State {
	State {
	    location_contents: HashMap::with_capacity(8),
	}
    }

    pub fn is_complete(&self) -> bool {
	let mut counts: HashMap<Amphipod, usize> = HashMap::new();
	for who in self.location_contents.values() {
	    *counts.entry(*who).or_insert(0) += 1
	}
	counts.get(&Amphipod::A) == Some(&2) &&
	    counts.get(&Amphipod::B) == Some(&2) &&
	    counts.get(&Amphipod::C) == Some(&2) &&
	    counts.get(&Amphipod::D) == Some(&2)
    }

    pub fn squish(&self) -> Vec<(Amphipod, Position)> {
	let mut result: Vec<(Amphipod, Position)> = self.location_contents.iter()
	    .map(|(pos, who)| (*who, *pos))
	    .collect();
	// We sort the result so that equivalent states always have a
	// consistent representation.
	result.sort();
	result
    }

    fn set_pos(&mut self, who: &Amphipod, pos: &Position) {
	self.location_contents.insert(*pos, *who);
    }

    fn with_moved_amphipod(&self, who: &Amphipod, from: &Position, to: &Position) -> State {
	if from == to {
	    panic!("with_moved_amphipod: it did not actually move");
	}
	if let Some(existing) = self.location_contents.get(&to) {
	    panic!(
		"with_moved_amphipod: destination {:?} already contains {:?}",
		to,
		existing,
	    );
	}
	let mut next = State::new();
	for (pos, current_occupant) in self.location_contents.iter() {
	    if pos == from {
		assert_eq!(current_occupant, who);
	    } else {
		next.location_contents.insert(*pos, *current_occupant); // did not move
	    }
	}
	next.location_contents.insert(*to, *who);
	next
    }

    fn position_is_occupied(&self, pos: &Position) -> bool {
	self.location_contents.contains_key(pos)
    }

    fn is_path_blocked(&self, path: &Path) -> bool {
	path.steps.iter().any(|pos| self.position_is_occupied(pos))
    }

    fn path_to_exit_doormat(&self, current: &Position) -> Path {
	assert!(matches!(current.y, 1|2));     // must be in a room.
	assert!(matches!(current.x, 2|4|6|8)); // must be in a room.
	let north = current.north(1).unwrap();
	let path = match current.y {
	    2 => Path::from_steps(vec![north, current.north(2).unwrap()]),
	    1 => Path::from_step(north),
	    _ => unreachable!(),
	}.checked(current).expect("path_to_exit_doormat should produce valid paths");
	if let Some(last) = path.last() {
	    assert!(
		last.is_doormat(),
		"path_to_exit_doormat: last path position {:?} should be a doormat",
		&last
	    );
	    assert_eq!(last.x, current.x, "path_to_exit_doormat should not movbe horizontally");
	} else {
	    panic!("path_to_exit_doormat: emitted empty path");
	}
	path
    }

    fn paths_from_room_to_hallway(&self, current: &Position) -> Vec<Path> {
	assert!(matches!(current.y, 1|2));     // must be in a room.
	assert!(matches!(current.x, 2|4|6|8)); // must be in a room.
	let mut result = Vec::with_capacity(10);
	let steps_to_doormat: Vec<Position> = match current.y {
	    1 => {
		vec![Position {x: current.x, y: 0}]
	    }
	    2 => {
		vec![Position {x: current.x, y: 1},
		     Position {x: current.x, y: 0}]
	    }
	    _ => {
		panic!(
		    "paths_from_room_to_hallway: called for {:?} which is not actually a room",
		    &current
		);
	    }
	};
	let mut steps = Vec::with_capacity(10);
	steps.extend(&steps_to_doormat);
	for x in (current.x+1)..=10 {
	    let pos = Position { x, y: 0 };
	    let is_doormat = pos.is_doormat();
	    steps.push(pos);
	    if !is_doormat {
		let path: Path = Path::from_steps(steps.clone())
		    .checked(current)
		    .expect("paths_from_room_to_hallway should generate valid rightward paths");
		result.push(path);
	    }
	}
	steps.clear();
	steps.extend(&steps_to_doormat);
	for x in (0..current.x).rev() {
	    let pos = Position { x, y: 0 };
	    let is_doormat = pos.is_doormat();
	    steps.push(Position { x, y: 0 });
	    if !is_doormat {
		let path = Path::from_steps(steps.clone())
		    .checked(current)
		    .expect("paths_from_room_to_hallway should generate valid leftward paths");
		result.push(path);
	    }
	}
	sanity_check_paths(result.iter_mut(), current)
	    .expect("paths_from_room_to_hallway should generate valid paths");
	result
    }

    fn is_goal(&self) -> bool {
	true &&
	    self.location_contents.get(&Position{x: 2, y: 1}) == Some(&Amphipod::A) &&
	    self.location_contents.get(&Position{x: 2, y: 2}) == Some(&Amphipod::A) &&
	    self.location_contents.get(&Position{x: 4, y: 1}) == Some(&Amphipod::B) &&
	    self.location_contents.get(&Position{x: 4, y: 2}) == Some(&Amphipod::B) &&
	    self.location_contents.get(&Position{x: 6, y: 1}) == Some(&Amphipod::C) &&
	    self.location_contents.get(&Position{x: 6, y: 2}) == Some(&Amphipod::C) &&
	    self.location_contents.get(&Position{x: 8, y: 1}) == Some(&Amphipod::D) &&
	    self.location_contents.get(&Position{x: 8, y: 2}) == Some(&Amphipod::D)
    }

    fn heuristic(&self) -> Cost {
	let mut total_h: Cost = Cost(0);
	for (pos, who) in self.location_contents.iter() {
	    let moves: u64 = match pos.get_type() {
		LocationType::Room(owner) if &owner == who => {
		    // already home
		    0
		}
		_ => {
		    let doormat = Position::doormat_of(&who);
		    // manhattan distiance is an underestimate when
		    // the amphipod is in another family's room.  This
		    // does not violate the requirements on the
		    // heuristic.
		    //
		    // We add 1 because the amphipod has to at least
		    // step off the doormat into its room.  Since some
		    // amphipods have to move to the bottom of their
		    // room, this is another respect in which this
		    // heuristic is an underestimate.
		    Position::manhattan(&pos, &doormat) + 1
		}
	    };
	    total_h += who.move_cost() * moves;
	}
	total_h
    }

    fn next_possible_states(&self) -> Vec<(State, Cost)> {
	let mut result = Vec::new();
	for (pos, who) in self.location_contents.iter() {
	    let unit_cost: Cost = who.move_cost();
	    let paths = self.unblocked_moves_for(&pos);
	    for path in paths {
		if let Some(last) = path.last() {
		    let next_state = self.with_moved_amphipod(&who, &pos, &last);
		    result.push((next_state, path.total_cost(unit_cost)));
		} else {
		    panic!(
			"unblocked_moves_for({:?}) at {:?} suggested an empty path {:?}",
			&who,
			&pos,
			&path,
		    );
		}
	    }
	}
	result
    }

    fn unblocked_moves_for(&self, current: &Position) -> Vec<Path> {
	//println!("considering moves for occupant of {:?}", &current);
	let paths = self.possible_moves_for_no_collision(current);
	paths.into_iter()
	    .map(|mut path: Path| -> Path {
		path.sanity_check(&current)
		    .expect("possible_moves_for_no_collision should select a correct path");
		path
	    })
	    //.inspect(|path| { println!("considering a path {:?}", &path); })
	    .filter(|path| !self.is_path_blocked(&path))
	    //.inspect(|_| { println!("path is not blocked"); })
	    .collect()
    }

    /// Compute the possible moves for `who` without regard to collision.
    fn possible_moves_for_no_collision(&self, p: &Position) -> Vec<Path> {
	let who = match self.location_contents.get(p) {
	    Some(who) => who,
	    None => {
		panic!("possible_moves_for_no_collision: called for unoccupied position {:?}", p);
	    }
	};
	match p.get_type() {
	    //LocationType::Room(owning_family) if owning_family == who.family => {
	    //	// This amphipod is in its room.  Each room
	    //	// contains 2 locations (y=1, y=2).
	    //	match p.y {
	    //	    2 => {
	    //		// In theory the Amphipod could move up but
	    //		// that is never part of a least-energy
	    //		// solution.  Do nothing.
	    //		vec![]
	    //	    }
	    //	    1 => vec![Path::from_step(p.south(1).unwrap())],
	    //	    _ => unreachable!(),
	    //	}
	    //}
	    LocationType::Room(owner) => {
		// This amphipod is in someone else's room.  Legal
		// moves are out of the room (stopping in the hallway
		// or in its home) or to another location within the
		// room it is currently in.
		let mut result: Vec<Path> = vec![
		    match p.y {
			2 => {
			    Path::from_step(p.north(1).unwrap())
				.checked(&p)
				.expect("valid")
			}
			1 => {
			    // The Amphipod could move deeper into the
			    // room if it is unoccupied.
			    Path::from_step(p.south(1).unwrap())
				.checked(&p)
				.expect("valid")
			}
			_ => unreachable!(),
		    }
		];
		if owner != *who {
		    // This it not its own room, so it could step out onto the doormat and go home.
		    let path_to_exit_doormat = self.path_to_exit_doormat(&p)
			.checked(&p)
			.expect("path_to_exit_doormat should be valid");
		    let exit_doormat = Position { x: p.x, y: 0 };
		    for path_exit_doormat_to_home in self.paths_from_hallway_to_home(who, &exit_doormat) {
			let mut path = path_to_exit_doormat.join(&path_exit_doormat_to_home);
			path.sanity_check(&p).expect("path to exit doormat should be valid and start at current position");
			result.push(path);
		    }
		}

		// Or it could move out and park in the hallway instead.
		let mut hallway_paths = self.paths_from_room_to_hallway(&p);
		sanity_check_paths(hallway_paths.iter_mut(), &p).expect("hallway_paths should be valid");
		result.extend(hallway_paths);

		result.iter_mut()
		    .for_each(|path| {
			path.sanity_check(&p).expect("possible_moves_for_no_collision should create a valid path from a room");
		    });
		result
	    }
	    // No Amphipod should ever stop on a doormat.
	    LocationType::Doormat(_) => unreachable!(),
	    LocationType::Hallway => {
		// Amphipods which are currently in the hallway are
		// locked in place until they can move to their home.
		self.paths_from_hallway_to_home(who, &p)
	    }
	}
    }

    fn paths_from_own_doormat_to_home(&self, doormat: &Position) -> Vec<Path> {
	assert_eq!(doormat.y, 0);
	assert!(matches!(doormat.x, 2|4|6|8));
	let first: Position = doormat.south(1).unwrap();
	let second: Position = doormat.south(2).unwrap();
	let mut result = vec![Path::from_step(first),
			      Path::from_steps(vec![first, second])];
	sanity_check_paths(result.iter_mut(), doormat)
	    .expect("paths_from_own_doormat_to_home should generate correct paths");
	result
    }

    fn path_from_hallway_to_doormat(&self, who: &Amphipod, current: &Position) -> Path {
	assert_eq!(current.y, 0); // in hallway
	assert!((0..=10).contains(&current.x)); // in hallway
	let doormat = Position::doormat_of(&who);
	let mut result = if doormat.x > current.x {
	    Path {
		steps: ((current.x + 1)..=doormat.x)
		    .map(|x| Position { x, y: 0 })
		    .collect(),
		checked: None,
	    }
	} else {
	    Path {
		steps: (doormat.x..current.x).rev()
		    .map(|x| Position { x, y: 0 })
		    .collect(),
		checked: None,
	    }
	};
	result.sanity_check(&current).expect("valid path to doormat");
	assert_eq!(result.last().expect("non-empty path"), &doormat,
		   "path should end at doormat");
	result
    }

    /// Find all paths from a hallway location to an amphipod's home.
    /// `current` may be a doormat, because this method is called as
    /// part of route planning (i.e. `current` may just be a waypoint,
    /// not the actual current position of an amphipod).
    fn paths_from_hallway_to_home(&self, who: &Amphipod, current: &Position) -> Vec<Path> {
	assert_eq!(current.y, 0);
	assert!((0..=10).contains(&current.x)); // in hallway
	match current.get_type() {
	    LocationType::Hallway | LocationType::Doormat(_) => {
		// the amphipod is in the hallway or on someone else's
		// doormat.
		let home_doormat = Position::doormat_of(&who);
		if &home_doormat == current {
		    // The amphipod was already on its home doormat,
		    // and that is not allowed (since it is not
		    // allowed to stop there).
		    unreachable!()
		} else {
		    let path_to_own_doormat: Path = self.path_from_hallway_to_doormat(who, current)
			.checked(current).expect("valid path");
		    let first: Path = path_to_own_doormat.clone().then_move_to(home_doormat.south(1).unwrap())
			.checked(current).expect("valid path (first)");
		    let second: Path = first.clone().then_move_to(home_doormat.south(2).unwrap())
			.checked(current).expect("valid path (second)");
		    vec![first, second]
		}
	    }
	    LocationType::Room(_) => unreachable!(),
	}
    }
}

impl Display for State {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
	f.write_str("#############\n")?;
	for y in 0..3 {
	    if matches!(y, 0|1) {
		f.write_str("#")?;
	    } else {
		f.write_str(" ")?;
	    }
	    for x in 0..11 {
		let pos = Position { x, y };
		let symbol: char = if y == 0 || matches!(x, 2|4|6|8) {
		    match self.location_contents.get(&pos) {
			Some(a) => a.symbol(),
			None => '.',
		    }
		} else {
		    match x {
			1|3|5|7|9 => '#',
			_ => match y {
			    1 => '#',
			    _ => ' ',
			}
		    }
		};
		write!(f, "{}", symbol)?;
	    }
	    if matches!(y, 0|1) {
		f.write_str("#\n")?;
	    } else {
		f.write_str("\n")?;
	    }
	}
	f.write_str("  #########\n")?;
	Ok(())
    }
}


impl TryFrom<&Vec<(Amphipod, Position)>> for State {
    type Error = String;
    fn try_from(squished: &Vec<(Amphipod, Position)>) -> Result<State, String> {
	let mut result = State::new();
	for (who, pos) in squished.iter() {
	    if result.location_contents.contains_key(&pos) {
		return Err(format!("position {:?} has multiple occupants", &pos));
	    } else {
		result.location_contents.insert(*pos, *who);
	    }
	}
	if result.location_contents.len() != 8 {
	    Err(format!("expected 8 items in location_contents, got {}",
			result.location_contents.len()))
	} else {
	    Ok(result)
	}
    }
}

#[test]
fn test_unblocked_moves_for() {
    //            1
    //  01234567890
    // #############
    // #...........# 0 (hallway)
    // ###B#C#B#D### 1 (room)
    //   #A#D#C#A#   2 (room)
    //   #########
    //  01234567890
    //            1
    let current: State = {
	let mut s = State::new();
	s.location_contents.insert(Position { x: 2, y: 2 }, Amphipod::A);
	s.location_contents.insert(Position { x: 8, y: 2 }, Amphipod::A);
	s.location_contents.insert(Position { x: 2, y: 1 }, Amphipod::B);
	s.location_contents.insert(Position { x: 6, y: 1 }, Amphipod::B);
	s.location_contents.insert(Position { x: 4, y: 1 }, Amphipod::C);
	s.location_contents.insert(Position { x: 6, y: 2 }, Amphipod::C);
	s.location_contents.insert(Position { x: 4, y: 2 }, Amphipod::D);
	s.location_contents.insert(Position { x: 8, y: 1 }, Amphipod::D);
	s
    };
    assert_eq!(current.location_contents.get(&Position { x: 6, y: 1 }),
	       Some(&Amphipod::B));

    let paths = current.unblocked_moves_for(&Position {x: 6, y: 1 });
    dbg!(&paths);
    let mut destinations: HashSet<u8> = HashSet::with_capacity(10);
    for path in paths {
	match path.steps.first() {
	    Some(doormat) => {
		assert_eq!(doormat.x, 6);
		assert_eq!(doormat.y, 0);
	    }
	    None => {
		panic!("proposed an emtpy path");
	    }
	}
	match dbg!(path.steps.last()) {
	    Some(dest) => {
		assert_eq!(dest.y, 0);
		destinations.insert(dest.x);
	    }
	    None => unreachable!(),
	}
    }
    dbg!(&destinations);
    assert!(destinations.contains(&0));
    assert!(destinations.contains(&1));
    assert!(!destinations.contains(&2)); // it's a doormat
    assert!(destinations.contains(&3));
    assert!(!destinations.contains(&4)); // it's a doormat
    assert!(destinations.contains(&5));
    assert!(!destinations.contains(&6)); // it's a doormat
    assert!(destinations.contains(&7));
    assert!(!destinations.contains(&8)); // it's a doormat
    assert!(destinations.contains(&9));
    assert!(destinations.contains(&10));
    assert_eq!(destinations.len(), 7);

    // The C at (6,2) and cannot move because (6,1) is occupied by a B.
    let paths = current.unblocked_moves_for(&Position {x: 6, y: 2});
    assert!(paths.is_empty(), "unexpected paths {:#?}", paths);
}

fn squished_state_is_goal(s: &SquishedState) -> bool {
    let mut found: usize = 0;
    let mut seen: HashSet<Position> = HashSet::new();
    for (who, pos) in s.iter() {
	if seen.contains(pos) {
	    panic!("position {:?} occurs twice in squished state", pos);
	} else {
	    seen.insert(*pos);
	}
	match pos.get_type() {
	    LocationType::Room(owner) if owner == *who => { found += 1; }
	    _ => { return false; }
	}
    }
    found == 8
}

fn solve(start: &State) -> Cost {
    let heuristic = |s: &SquishedState| -> Cost {
	State::try_from(s).expect("valid state").heuristic()
    };
    let success = |s: &SquishedState| -> bool {
	squished_state_is_goal(s)
    };
    let successors = |s: &SquishedState| -> Vec<(SquishedState, Cost)> {
	let state = State::try_from(s).expect("valid state");
	let succ_states: Vec<(State, Cost)> = state.next_possible_states();
	println!("considering successors of state:\n{}\n... there are {} successors",
		 &state, succ_states.len());
	let result: Vec<(SquishedState, Cost)> = succ_states.into_iter()
	    .map(|(s, cost)| (s.squish(), cost))
	    .collect();
	result
    };
    let initial_squished_state = start.squish();
    match astar(&initial_squished_state, successors, heuristic, success) {
        Some((_path, cost)) => cost,
        None => {
            panic!("no solution found");
        }
    }
}

fn parse_board(board: &str) -> Result<State, String> {
    let mut result = State::new();
    for (y, line) in board.split_terminator('\n').skip(1).enumerate() {
	for (x, ch) in line.chars().skip(1).enumerate() {
	    let pos = Position{ x: x as u8, y: y as u8, };
	    match ch {
		'.'|' '|'#' => (),
		_ => match Amphipod::try_from(ch) {
		    Ok(who) => {
			result.set_pos(&who, &pos);
		    }
		    Err(e) => {
			return Err(format!("failed to parse line {} ('{}'): {}",
					   y+2, &line, e));
		    }
		}
	    }
	}
    }
    if result.is_complete() {
	Ok(result)
    } else {
	Err("some amphipods are missing".to_string())
    }
}

fn sample_input() -> State {
    //            1
    //  01234567890
    // #############
    // #...........# 0 (hallway)
    // ###B#C#B#D### 1 (room)
    //   #A#D#C#A#   2 (room)
    //   #########
    //  01234567890
    //            1
    let mut s = State::new();
    s.location_contents.insert(Position { x: 2, y: 2 }, Amphipod::A);
    s.location_contents.insert(Position { x: 8, y: 2 }, Amphipod::A);
    s.location_contents.insert(Position { x: 2, y: 1 }, Amphipod::B);
    s.location_contents.insert(Position { x: 6, y: 1 }, Amphipod::B);
    s.location_contents.insert(Position { x: 4, y: 1 }, Amphipod::C);
    s.location_contents.insert(Position { x: 6, y: 2 }, Amphipod::C);
    s.location_contents.insert(Position { x: 4, y: 2 }, Amphipod::D);
    s.location_contents.insert(Position { x: 8, y: 1 }, Amphipod::D);
    s
}

#[test]
fn test_parse_board() {
    let sample_handcoded = sample_input();
    let sample_parsed = parse_board(
	concat!(
	    "#############\n",
	    "#...........#\n",
	    "###B#C#B#D###\n",
	    "  #A#D#C#A#  \n",
	    "  #########  \n",
	)
    ).expect("test input should be valid");
    assert_eq!(sample_parsed, sample_handcoded);
}

fn real_input() -> State {
    //            1
    //  01234567890
    // ############# y
    // #...........# 0
    // ###B#B#D#D### 1
    //   #C#A#A#C#   2
    //   #########
    //  01234567890
    //            1
    let mut s = State::new();
    s.location_contents.insert(Position { x: 4, y: 2 }, Amphipod::A);
    s.location_contents.insert(Position { x: 6, y: 2 }, Amphipod::A);
    s.location_contents.insert(Position { x: 2, y: 1 }, Amphipod::B);
    s.location_contents.insert(Position { x: 4, y: 1 }, Amphipod::B);
    s.location_contents.insert(Position { x: 2, y: 2 }, Amphipod::C);
    s.location_contents.insert(Position { x: 8, y: 2 }, Amphipod::C);
    s.location_contents.insert(Position { x: 6, y: 1 }, Amphipod::D);
    s.location_contents.insert(Position { x: 8, y: 1 }, Amphipod::D);
    s
}

#[test]
fn test_successors() {
    //            1
    //  01234567890
    // ############# y
    // #.B.D.A.....# 0
    // ###.#B#.#D### 1
    //   #.#A#C#C#   2
    //   #########
    //            1
    //  01234567890

    let mut s = State::new();
    s.location_contents.insert(Position { x: 5, y: 0 }, Amphipod::A);
    s.location_contents.insert(Position { x: 4, y: 2 }, Amphipod::A);
    s.location_contents.insert(Position { x: 1, y: 0 }, Amphipod::B);
    s.location_contents.insert(Position { x: 4, y: 1 }, Amphipod::B);
    s.location_contents.insert(Position { x: 6, y: 2 }, Amphipod::C);
    s.location_contents.insert(Position { x: 8, y: 2 }, Amphipod::C);
    s.location_contents.insert(Position { x: 3, y: 0 }, Amphipod::D);
    s.location_contents.insert(Position { x: 8, y: 1 }, Amphipod::D);

    let succ_states: Vec<(State, Cost)> = s.next_possible_states();
    assert!(
	!succ_states.is_empty(),
	"State\n{}\nshould have at least one successor (moving the D at (8,1) to (9,0))",
	&s
    );
}

fn main() {
    let start = real_input();
    println!("Initial state:\n{}", start);
    let part1cost = solve(&start);
    println!("Day 23 part 1: cost is {}", part1cost);
}
