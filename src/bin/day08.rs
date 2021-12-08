use std::collections::HashMap;
use std::io;
use std::io::prelude::*;

#[derive(Debug)]
struct PuzzleLine {
    samples: Vec<String>,
    output: Vec<String>,
}

impl TryFrom<String> for PuzzleLine {
    type Error = String;
    fn try_from(s: String) -> Result<PuzzleLine, String> {
        let mut it = s.split(" | ");
        if let Some(samp) = it.next().map(|s| s.split(' ')) {
            let samples: Vec<String> = samp.map(String::from).collect();
            if samples.len() > 10 {
                return Err(format!(
                    "expected 10 samples, got {}: {:?}",
                    samples.len(),
                    &samples,
                ));
            }
            if let Some(out) = it.next().map(|s| s.split(' ')) {
                let output: Vec<String> = out.map(String::from).collect();
                if output.len() > 4 {
                    return Err(format!(
                        "expected 4 outputs, got {}: {:?}",
                        output.len(),
                        output
                    ));
                }
                if None != it.next() {
                    return Err(format!("too many '|' in input line: {}", s));
                }
                Ok(PuzzleLine { samples, output })
            } else {
                Err("expected something on the right of a '|'".to_string())
            }
        } else {
            Err(format!("expected two fields separated by '|': {}", s,))
        }
    }
}

fn count1478(output: &[String]) -> usize {
    output
        .iter()
        .filter(|s| {
            matches!(
                s.len(),
                2|	 // it's a 1.
		4|	 // it's a 4.
		3|	 // it's a 7.
		7 // it's an 8.
            )
        })
        .count()
}

#[derive(Debug)]
struct Solution {
    /// Mapping from scrambled segment to true segment.
    forward: HashMap<char, char>,
    /// Mapping from true segment to scrambled segment.
    reverse: HashMap<char, char>,
}

impl Solution {
    pub fn new() -> Solution {
        Solution {
            forward: HashMap::new(),
            reverse: HashMap::new(),
        }
    }

    // True if we know the mappingn for all 7 segments.
    pub fn complete(&self) -> bool {
        self.forward.len() == 7
    }

    pub fn identify(&mut self, scrambled: &char, correct: &char) {
        if let Some(existing) = self.forward.get(scrambled) {
            panic!(
                "{} has been mapped to more than one unscrambled segment ({} and {})",
                scrambled, existing, correct,
            );
        }
        if let Some(existing) = self.reverse.get(correct) {
            panic!(
                "more than one scrambled segment ({} and {}) maps to {}",
                scrambled, existing, correct,
            );
        }
        //println!(
        //    "We have identified that scrambled segment {} maps to unscrambled segment {}",
        //    scrambled,
        //    correct
        //);
        self.forward.insert(*scrambled, *correct);
        self.reverse.insert(*correct, *scrambled);
        assert!(self.is_identified(scrambled));
    }

    pub fn is_identified(&self, scrambled: &char) -> bool {
        self.forward.contains_key(scrambled)
    }

    pub fn scramble(&self, unscrambled: &char) -> Option<char> {
        self.reverse.get(unscrambled).copied()
    }

    pub fn unscramble(&self, scrambled: &char) -> Option<char> {
        self.forward.get(scrambled).copied()
    }

    pub fn unscramble_segments(&self, segs: &str) -> Result<String, String> {
        let mut result: String = String::with_capacity(7);
        for scrambled in segs.chars() {
            if let Some(unscrambled) = self.unscramble(&scrambled) {
                result.push(unscrambled);
            } else {
                return Err(format!(
                    "Solution {:?} cannot unscramble {}",
                    &self, &scrambled
                ));
            }
        }
        Ok(result)
    }
}

fn string_contains<'a, S>(s: S, ch: &char) -> bool
where
    S: Into<&'a str>,
{
    let ss: &str = s.into();
    ss.contains(*ch)
}

#[test]
fn test_string_contains() {
    assert!(string_contains("hello", &'e'));
    assert!(string_contains("hello", &'l'));
    assert!(!string_contains("", &'x'));
    assert!(!string_contains("foo", &'g'));
}

fn count_digits_containing_segment(segment: &char, digits: &[String]) -> usize {
    digits
        .iter()
        .filter(|sample| string_contains(sample.as_str(), segment))
        .count()
}

/// | digit | segment count |
/// | ----- | ------------- |
/// | 0     | 6             |
/// | 1     | 2             |
/// | 2     | 5             |
/// | 3     | 5             |
/// | 4     | 4             |
/// | 5     | 5             |
/// | 6     | 6             |
/// | 7     | 3             |
/// | 8     | 7             |
/// | 9     | 6             |
///
/// # Identifying the digits 1, 4, 7 and 8
///
/// We can identify the digits 1, 4, 7, 8 by just counting the lit
/// segments.
///
/// | Segment count | Digits  | Segments  |
/// | ------------- | ------- | --------- |
/// | 2             | 1       | `  c  f`  |
/// | 4             | 4       | ` bcd f`  |
/// | 3             | 7       | `a c  f`  |
/// | 7             | 8       | `abcdefg` |
///
/// # Unscrambling segments e and g
///
/// Considering only the digits with unique segment counts, the segments e and g are used
/// only in the digit with 7 segments (i.e. 8).
///
/// Considering all digits, e is used in 4 digits (0, 2, 6, 8),
/// while g is used in 7 (0, 2, 3, 5, 6, 8, 9).
///
/// This allows us to distinguish both e and g.
///
/// # Unscrambling a
///
/// Segments c and f are used in all four digits (1478).  We can
/// immediately deduce a, since it is the only segment in a 3-count
/// digit which isn't c or f.
///
/// We now know a, e and g.
///
/// # Unscrambling segments b, c and f
///
/// Already we know the segments a, e and g.
///
/// We need to distinguish these cases with 5 lit segments.
///
/// | Segment count | Digit   | Segments  |
/// | ------------- | ------- | --------- |
/// | 5             | 2       | `a cde g` |
/// | 5             | 3       | `a cd fg` |
/// | 5             | 5       | `ab d fg` |
///
/// Segments b (in digit 5) and e (in digit 2) appear once each.  But
/// we know what e is, so we can deduce b.
///
/// We now know a, b, e and g.
///
/// Segment f appears in the 2-segment digit (i.e. 1=cf) but not in
/// the same 5-segment sigit as e.  This identifies f.
///
/// We deduce c, as it is the only other segment in the only 2-segment
/// digit (1).
///
/// Hence we now know segments a, b, c, e, f and g.
///
/// # Unscrambling segment d
///
/// We can distinguish these cases with 6 lit segments.
///
/// | Segment count | Digit   | Segments        |
/// | ------------- | ------- | --------------- |
/// | 6             | 0       | `abc efg`,      |
/// | 6             | 6       | `ab defg`       |
/// | 6             | 9       | `abcd fg`       |
///
///
/// | Frequency in 5-segment samples | Frequency in 6-segment samples | Segments |
/// | 1                              | 3                              | `bf`     |
/// | 2                              | 2                              | `ce`     |
/// | 3                              | 2                              | `d`      |
/// | 3                              | 3                              | `ag`     |
///
/// From this we can immediately identify d as being used in a unique
/// pattern, (3 times in 5-segment digits and 2 times in 6-segment
/// digits).
///
/// But in any case, since we already know the identities of all the
/// other segments, we could simply deduce d by elimination.

fn solve(samples: &[String]) -> Solution {
    //println!("Trying to solve {}", samples.join(" "));
    let mut solution = Solution::new();
    let mut digit_representation: HashMap<u8, String> = HashMap::new();
    const SEGMENTS: &str = "abcdefg";
    for segments in samples {
        match segments.len() {
            2 => {
                digit_representation.insert(1, segments.clone());
            }
            4 => {
                digit_representation.insert(4, segments.clone());
            }
            3 => {
                digit_representation.insert(7, segments.clone());
            }
            7 => {
                digit_representation.insert(8, segments.clone());
            }
            _ => (),
        }
    }

    // Considering only the digits with unique segment counts, the
    // segments e and g are used only in the digit with 7 segments
    // (i.e. 8).
    let mut e_and_g = String::new();
    for segment in SEGMENTS.chars() {
        let use_count: usize = digit_representation
            .values()
            .filter(|rep| rep.contains(segment))
            .count();
        if use_count == 1 {
            e_and_g.push(segment);
        }
    }
    // Considering all digits, e is used in 4 digits (0, 2, 6, 8),
    // while g is used in 7 (0, 2, 3, 5, 6, 8, 9).
    for e_or_g in e_and_g.chars() {
        match count_digits_containing_segment(&e_or_g, samples) {
            4 => {
                solution.identify(&e_or_g, &'e');
            }
            7 => {
                solution.identify(&e_or_g, &'g');
            }
            n => {
                panic!(
                    "did not expect to see {} segments used in a sample containing segment e or g",
                    n
                );
            }
        }
    }

    // We now know e and g.

    // Identify segment a.  It is the only segment in a 3-count digit
    // which isn't c or f.
    let mut c_or_f: Option<String> = None;
    for sample in samples.iter() {
        if sample.len() == 2 {
            // This is the digit 1.  Its segments are c and f.
            c_or_f = Some(sample.to_string());
            break;
        }
    }
    let c_or_f: String = c_or_f.unwrap();
    for sample in samples.iter().filter(|sample| sample.len() == 3) {
        if let Some(segment) = sample
            .chars()
            .find(|ch| !string_contains(c_or_f.as_str(), ch))
        {
            // Not c or f, so it must be a.
            solution.identify(&segment, &'a');
            break;
        }
    }

    // We now know segments a, e and g.

    // Segments b and e appear once each in 5-segment digits (5 and
    // 2).
    for scrambled_segment in SEGMENTS.chars() {
        let occurrences = samples
            .iter()
            .filter(|sample| sample.len() == 5)
            .filter(|sample| string_contains(sample.as_str(), &scrambled_segment))
            .count();
        if occurrences == 1 {
            // scrambled_segment unscrambles to either b or e.  But we
            // already identified e.
            if !solution.is_identified(&scrambled_segment) {
                solution.identify(&scrambled_segment, &'b');
            }
        }
    }

    // We now know segments a, b, e, g.
    //
    // Segment f appears in the 2-segment digit (i.e. 1=cf) but not in
    // the same 5-segment digit as e.  This identifies f.
    let e = solution.scramble(&'e').unwrap();
    let two_segment_sample: String = samples
        .iter()
        .filter(|s| s.len() == 2)
        .cloned()
        .next()
        .unwrap();
    let scrambled_segment_in_same_5segment_digit_as_e = |scrambled_segment: char| -> bool {
        for sample in samples.iter().filter(|sample| sample.len() == 5) {
            if string_contains(sample.as_str(), &e)
                && string_contains(sample.as_str(), &scrambled_segment)
            {
                return true;
            }
        }
        false
    };
    for f_candidate in two_segment_sample.chars() {
        if !scrambled_segment_in_same_5segment_digit_as_e(f_candidate) {
            solution.identify(&f_candidate, &'f');
        }
    }
    // We now know segments a, b, e, f, g.

    // We deduce c, as it is the only other segment in the only
    // 2-segment digit (1).
    for scrambled_segment in two_segment_sample.chars() {
        if !solution.is_identified(&scrambled_segment) {
            solution.identify(&scrambled_segment, &'c');
            break;
        }
    }

    // We now know segments a, b, c, e, f, g.  Deduce d by
    // elimination.
    for g_candidate in SEGMENTS.chars() {
        if !solution.is_identified(&g_candidate) {
            solution.identify(&g_candidate, &'d');
        }
    }

    assert!(solution.complete());
    solution
}

fn map_segments_to_digit(unscrambled_segments: &str) -> Option<u8> {
    let mut tmp: Vec<char> = unscrambled_segments.chars().collect();
    tmp.sort_unstable();
    let ordered: String = tmp.iter().collect();
    match ordered.as_str() {
        "abcefg" => Some(0),
        "cf" => Some(1),
        "acdeg" => Some(2),
        "acdfg" => Some(3),
        "bcdf" => Some(4),
        "abdfg" => Some(5),
        "abdefg" => Some(6),
        "acf" => Some(7),
        "abcdefg" => Some(8),
        "abcdfg" => Some(9),
        _ => None,
    }
}

fn part1(lines: &[PuzzleLine]) {
    let total: usize = lines.iter().map(|pline| count1478(&pline.output)).sum();
    println!("Day 8 part 1: {}", total);
}

fn find_output_value(pline: &PuzzleLine) -> Result<i32, String> {
    let solution = solve(&pline.samples);
    let mut number: i32 = 0;
    for output in pline.output.iter() {
        match solution.unscramble_segments(output) {
            Ok(unscrambled) => match map_segments_to_digit(unscrambled.as_str()) {
                Some(digit) => {
                    number = number * 10 + digit as i32;
                }
                None => {
                    return Err(format!("failed to map {}", unscrambled));
                }
            },
            Err(e) => {
                return Err(e);
            }
        }
    }
    Ok(number)
}

fn part2(lines: &[PuzzleLine]) {
    let mut total: i32 = 0;
    for pline in lines {
        //println!("Problem: {:?}", pline);
        match find_output_value(pline) {
            Ok(n) => {
                // println!(
                //     "Output {} -> {}",
                //     pline.output.join(" "),
                //     n
                // );
                total += n;
            }
            Err(e) => {
                panic!("{}", e);
            }
        }
    }
    println!("Day 8 part 2: {}", total);
}

fn main() {
    let plines: Vec<PuzzleLine> = match io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .map(PuzzleLine::try_from)
        .collect()
    {
        Ok(v) => v,
        Err(e) => {
            panic!("failed to parse puzzle input: {}", e);
        }
    };
    part1(&plines);
    part2(&plines);
}
