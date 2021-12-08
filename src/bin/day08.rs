use std::io;
use std::io::prelude::*;

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
fn count1478(output: &[String]) -> usize {
    output
        .iter()
        .filter(|s| {
            matches!(
                s.len(),
                2|	 // it's a 1.
			     4|	 // it's a 4.
			     3|	 // it's a 7.
			     7
            )
        }) // it's an 8.
        .count()
}

fn part1(lines: &[PuzzleLine]) {
    let total: usize = lines.iter().map(|pline| count1478(&pline.output)).sum();
    println!("Day 8 part 1: {}", total);
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
}
