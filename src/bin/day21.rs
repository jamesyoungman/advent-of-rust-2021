fn next_pos(current: u8, rolled: u32) -> u8 {
    match rolled.checked_add(current.into()) {
        Some(n) => ((n - 1) % 10 + 1) as u8,
        None => {
            panic!("next_pos: failed to add {} and {}", current, rolled);
        }
    }
}

mod part1 {
    use super::next_pos;

    struct DeterministicDie {
        next_roll: u8,
        total_rolls: usize,
    }

    impl DeterministicDie {
        pub fn new() -> DeterministicDie {
            DeterministicDie {
                next_roll: 1,
                total_rolls: 0,
            }
        }

        pub fn roll3(&mut self) -> Vec<u8> {
            vec![self.roll1(), self.roll1(), self.roll1()]
        }

        fn roll1(&mut self) -> u8 {
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
        pos: u8,
        score: usize,
    }

    #[test]
    fn test_next_pos() {
        assert_eq!(next_pos(4, 3), 7);
        assert_eq!(next_pos(4, 6), 10);
        assert_eq!(next_pos(4, 7), 1);
    }

    impl Player {
        fn new(initial_pos: u8) -> Player {
            Player {
                pos: initial_pos,
                score: 0,
            }
        }

        fn score(&self) -> usize {
            self.score
        }

        fn won(&self) -> bool {
            self.score() >= 1000
        }

        fn advance(&mut self, by: u32) {
            let next = next_pos(self.pos, by);
            //println!(
            //    "Player {} advances by {}, moving from space {} to space {}",
            //    self.id, by, self.pos, next,
            //);
            self.pos = next;
            self.score += usize::from(self.pos);
        }

        fn turn(&mut self, die: &mut DeterministicDie) -> bool {
            let rolled: Vec<u8> = die.roll3();
            let total_roll: u32 = rolled.iter().copied().map(u32::from).sum();
            self.advance(total_roll);
            //println!(
            //    "Player {} rolls {}+{}+{} and moves to space {} for a total score of {}.",
            //    self.id,
            //    rolled[0],
            //    rolled[1],
            //    rolled[2],
            //    self.pos,
            //    self.score()
            //);
            self.won()
        }
    }

    fn simulate(p1pos: u8, p2pos: u8) -> (u8, usize, usize) {
        let mut die = DeterministicDie::new();
        let mut p1 = Player::new(p1pos);
        let mut p2 = Player::new(p2pos);
        loop {
            if p1.turn(&mut die) {
                break;
            }
            if p2.turn(&mut die) {
                break;
            }
        }
        match (p1.won(), p2.won()) {
            (true, false) => (1, p2.score(), die.total_rolls),
            (false, true) => (2, p1.score(), die.total_rolls),
            _ => unreachable!(),
        }
    }

    pub fn part1(p1pos: u8, p2pos: u8) {
        let (winner, losing_score, total_rolls) = simulate(p1pos, p2pos);
        println!(
            "Day 21 part 1: winner is {}; {}*{} = {}",
            winner,
            losing_score,
            total_rolls,
            losing_score * total_rolls
        );
    }

    #[test]
    fn test_simulate() {
        let (winner, losing_score, total_rolls) = simulate(4, 8);
        assert_eq!(winner, 1);
        assert_eq!(losing_score, 745);
        assert_eq!(total_rolls, 993);
    }
}

mod part2 {
    use std::collections::HashMap;

    use super::next_pos;

    const SCORE_TARGET: u8 = 21;
    const ROLLS_PER_TURN: u8 = 3;

    // Count the ways to roll a given total in some particular number of rolls.
    fn ways_to_roll_exactly(total_roll: u8, in_rolls: u8) -> usize {
        assert!(total_roll <= 30);
        if in_rolls == 0 || total_roll < 1 {
            0
        } else if in_rolls == 1 {
	    if (1..4).contains(&total_roll) {
                1
            } else {
                0
            }
        } else {
            let remaining = in_rolls - 1;
            [1, 2, 3]
                .iter()
                .map(|n| {
                    if total_roll < *n {
                        0
                    } else {
                        ways_to_roll_exactly(total_roll - *n, remaining)
                    }
                })
                .sum()
        }
    }

    #[test]
    fn test_ways_to_roll() {
        assert_eq!(ways_to_roll_exactly(4, 1), 0);
        assert_eq!(ways_to_roll_exactly(3, 1), 1);
        assert_eq!(ways_to_roll_exactly(2, 1), 1);
        assert_eq!(ways_to_roll_exactly(1, 1), 1);
        assert_eq!(ways_to_roll_exactly(0, 1), 0);

        // roll 7 in 2: not possible
        assert_eq!(ways_to_roll_exactly(7, 2), 0);
        // roll 6 in 2: 3+3
        assert_eq!(ways_to_roll_exactly(6, 2), 1);
        // roll 5 in 2: 2+3, 3+2.
        assert_eq!(ways_to_roll_exactly(5, 2), 2);
        // roll 4 in 2: 1+3, 3+1, 2+2
        assert_eq!(ways_to_roll_exactly(4, 2), 3);
        // roll 3 in 2: 1+2. 2+1
        assert_eq!(ways_to_roll_exactly(3, 2), 2);
        // roll 2 in 2: 1+1
        assert_eq!(ways_to_roll_exactly(2, 2), 1);
        // roll 1 in 2: not possible
        assert_eq!(ways_to_roll_exactly(1, 2), 0);
    }

    #[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Hash, Clone, Copy)]
    struct PlayerState {
        pos: u8,
        score: u8,
    }

    #[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Hash, Clone, Copy)]
    pub struct GameState(PlayerState, PlayerState);

    #[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone, Copy)]
    pub struct Outcome {
        win: usize,
        lose: usize,
    }

    pub struct Cache {
        entries: HashMap<GameState, Outcome>,
    }

    impl Cache {
        pub fn new() -> Cache {
            Cache {
                entries: HashMap::new(),
            }
        }

        pub fn get(&self, state: &GameState) -> Option<Outcome> {
            self.entries.get(state).copied()
        }

        pub fn set(&mut self, state: &GameState, outcome: Outcome) {
            self.entries.insert(*state, outcome);
        }
    }

    fn calculate_outcomes_slowly(
        current_player_state: &PlayerState,
        other_player_state: &PlayerState,
        cache: &mut Cache,
    ) -> Outcome {
        if current_player_state.score >= SCORE_TARGET {
            Outcome { win: 1, lose: 0 }
        } else if other_player_state.score >= SCORE_TARGET {
            Outcome { win: 0, lose: 1 }
        } else {
            let mut ways_for_current_player_to_win: usize = 0;
            let mut ways_for_current_player_to_lose: usize = 0;
            for roll in 3..=9 {
                let ways = ways_to_roll_exactly(roll, ROLLS_PER_TURN);
                let pos = next_pos(current_player_state.pos, roll.into());
                let next_outcome = calculate_outcomes_quickly(
                    other_player_state,
                    &PlayerState {
                        pos,
                        score: current_player_state.score + pos,
                    },
                    cache,
                );
                ways_for_current_player_to_win += ways * next_outcome.lose;
                ways_for_current_player_to_lose += ways * next_outcome.win;
            }
            Outcome {
                win: ways_for_current_player_to_win,
                lose: ways_for_current_player_to_lose,
            }
        }
    }

    fn calculate_outcomes_quickly(
        current_player_state: &PlayerState,
        other_player_state: &PlayerState,
        cache: &mut Cache,
    ) -> Outcome {
        let state: GameState = GameState(*current_player_state, *other_player_state);
        match cache.get(&state) {
            Some(outcome) => outcome,
            None => {
                let result =
                    calculate_outcomes_slowly(current_player_state, other_player_state, cache);
                cache.set(&state, result);
                result
            }
        }
    }

    pub fn part2(p1pos: u8, p2pos: u8) {
        let p1state = PlayerState {
            pos: p1pos,
            score: 0,
        };
        let p2state = PlayerState {
            pos: p2pos,
            score: 0,
        };
        let mut cache = Cache::new();
        let outcome = calculate_outcomes_quickly(&p1state, &p2state, &mut cache);
        println!(
            "Day 21 part 2:\np1 wins: {}\np2 wins: {}",
            outcome.win, outcome.lose
        );
    }
}

fn main() {
    let p1pos = 3_u8;
    let p2pos = 10_u8;
    part1::part1(p1pos, p2pos);
    part2::part2(p1pos, p2pos);
}
