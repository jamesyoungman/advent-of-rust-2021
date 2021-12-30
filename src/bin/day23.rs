use std::collections::HashSet;
use std::cmp::{max, min};
use std::fmt::{self, Debug, Formatter};
use std::ops::{Add, Mul};

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

impl Mul<u64> for Cost {
    type Output = Cost;
    fn mul(self, n: u64) -> <Self as Mul<u64>>::Output {
	Cost(self.0 * n)
    }
}

impl Add<Cost> for Cost {
    type Output = Cost;
    fn add(self, other: Cost) -> <Self as Add<Cost>>::Output {
	Cost(self.0 + other.0)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Family {
    A, B, C, D
}

impl Family {
    fn move_cost(&self) -> Cost {
	match self {
	    Family::A => Cost(1),
	    Family::B => Cost(10),
	    Family::C => Cost(100),
	    Family::D => Cost(1000),
	}
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum MemberId {
    Zero,
    One,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct Amphipod {
    family: Family,
    id: MemberId,
}

impl Amphipod {
    fn family(&self) -> Family {
	self.family
    }

    fn index(&self) -> usize {
	match self.id {
	    MemberId::Zero => 0,
	    MemberId::One => 1,
	}
    }

    fn move_cost(&self) -> Cost {
	self.family.move_cost()
    }
}


#[derive(Debug, PartialEq, Eq)]
enum LocationType {
    Hallway,
    Doormat(Family),		// immediately outside room
    Room(Family),
}

#[derive(PartialEq, Eq, Clone, Copy)]
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

    fn east(&self, dist: u8) -> Option<Position> {
	if self.y > 0 {
	    None		// cannot move east/west in room.
	} else {
	    let x = self.x + dist;
	    if x <= 10 {
		Some(Position {
		    x,
		    y: 0,
		})
	    } else {
		None
	    }
	}
    }

    fn west(&self, dist: u8) -> Option<Position> {
	if self.y > 0 {
	    None		// cannot move east/west in room.
	} else {
	    if dist <= self.x {
		let x = self.x - dist;
		Some(Position {
		    x,
		    y: 0,
		})
	    } else {
		None
	    }
	}
    }

    fn doormat_of(family: &Family) -> Position {
	let x = match family {
	    Family::A => 2,
	    Family::B => 4,
	    Family::C => 6,
	    Family::D => 8,
	};
	Position {
	    x,
	    y: 0,
	}
    }

    fn is_column_for(x: u8) -> Option<Family> {
	match x {
	    2 => Some(Family::A),
	    4 => Some(Family::B),
	    6 => Some(Family::C),
	    8 => Some(Family::D),
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

    fn is_in_any_room(&self) -> bool {
	matches!(self.get_type(), LocationType::Room(_))
    }

    fn is_in_room(&self, whose: &Family) -> bool {
	match self.get_type() {
	    LocationType::Room(actual) if &actual == whose => true,
	    _ => false,
	}
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
    fn new() -> Path {
	Path {
	    steps: Vec::new(),
	    checked: None,
	}
    }

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
    a: [Position; 2],
    b: [Position; 2],
    c: [Position; 2],
    d: [Position; 2],
}

impl State {
    fn with_moved_amphipod(&self, who: &Amphipod, dest: &Position) -> State {
	let mut next: State = self.clone();
	match who.family {
	    Family::A => { next.a[who.index()] = *dest; }
	    Family::B => { next.b[who.index()] = *dest; }
	    Family::C => { next.c[who.index()] = *dest; }
	    Family::D => { next.d[who.index()] = *dest; }
	}
	next
    }

    fn position_is_occupied(&self, pos: &Position) -> bool {
	for i in 0..2 {
	    if &self.a[i] == pos || &self.b[i] == pos || &self.c[i] == pos || &self.d[i] == pos {
		return true;
	    }
	}
	false
    }

    fn position_of(&self, who: &Amphipod) -> Position {
	match who.family {
	    Family::A => self.a[who.index()],
	    Family::B => self.b[who.index()],
	    Family::C => self.c[who.index()],
	    Family::D => self.d[who.index()],
	}
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

    fn unblocked_moves_for(&self, who: &Amphipod) -> Vec<Path> {
	let current = self.position_of(who);
	let paths = self.possible_moves_for_no_collision(who);
	paths.into_iter()
	    .map(|mut path: Path| -> Path {
		path.sanity_check(&current)
		    .expect("possible_moves_for_no_collision should select a correct path");
		path
	    })
	    .filter(|path| !self.is_path_blocked(&path))
	    .collect()
    }

    /// Compute the possible moves for `who` without regard to collision.
    fn possible_moves_for_no_collision(&self, who: &Amphipod) -> Vec<Path> {
	let p = self.position_of(who);
	match p.get_type() {
	    LocationType::Room(owning_family) if owning_family == who.family => {
		// This amphipod is in its room.  Each room
		// contains 2 locations (y=1, y=2).
		match p.y {
		    2 => {
			// In theory the Amphipod could move up but
			// that is never part of a least-energy
			// solution.  Do nothing.
			vec![]
		    }
		    1 => vec![Path::from_step(p.south(1).unwrap())],
		    _ => unreachable!(),
		}
	    }
	    LocationType::Room(_) => {
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
		// In either case it could step out onto the doormat and go home.
		let path_to_exit_doormat = self.path_to_exit_doormat(&p)
		    .checked(&p)
		    .expect("path_to_exit_doormat should be valid");
		let exit_doormat = Position { x: p.x, y: 0 };
		for path_exit_doormat_to_home in self.paths_from_hallway_to_home(who, &exit_doormat) {
		    let mut path = path_to_exit_doormat.join(&path_exit_doormat_to_home);
		    path.sanity_check(&p).expect("path to exit doormat should be valid and start at current position");
		    result.push(path);
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
	sanity_check_paths(result.iter_mut(), doormat);
	result
    }

    fn path_from_hallway_to_doormat(&self, who: &Amphipod, current: &Position) -> Path {
	assert_eq!(current.y, 0); // in hallway
	assert!((0..=10).contains(&current.x)); // in hallway
	let doormat = Position::doormat_of(&who.family);
	let mut result = if doormat.x > current.x {
	    Path {
		steps: ((current.x + 1)..doormat.x)
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
		let home_doormat = Position::doormat_of(&who.family);
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
    let b1 = Amphipod {
	family: Family::B,
	id: MemberId::One,
    };
    let current = State {
	a: [Position { x: 2, y: 2 },
	    Position { x: 8, y: 2 }],
	b: [Position { x: 2, y: 1 },
	    Position { x: 6, y: 1 }], // this is b1
	c: [Position { x: 4, y: 1 },
	    Position { x: 6, y: 2 }], // this is c1
	d: [Position { x: 4, y: 2 },
	    Position { x: 8, y: 1 }],
    };
    assert_eq!(current.position_of(&b1), Position { x: 6, y: 1 });
    let paths = current.unblocked_moves_for(&b1);
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

    // c1 is at (6,2) and cannot move because (6,1) is occupied by b1.
    let c1 = Amphipod {
	family: Family::C,
	id: MemberId::One,
    };
    let paths = current.unblocked_moves_for(&c1);
    assert!(paths.is_empty());
}
