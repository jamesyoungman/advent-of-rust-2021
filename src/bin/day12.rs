use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;

type Network = HashMap<String, HashSet<String>>;

fn part1(nodes: &Network) {
    println!("Day 12 part 1: {}", count_paths(nodes, &Part::One));
}

fn part2(nodes: &Network) {
    println!("Day 12 part 2: {}", count_paths(nodes, &Part::Two));
}

#[cfg(test)]
fn make_graph_from_strings(connections: &[&str]) -> Network {
    let c: Vec<(String, String)> = connections
        .iter()
        .map(|s: &&str| string_to_connection(s))
        .collect();
    make_graph(&c)
}

fn make_graph(connections: &[(String, String)]) -> Network {
    let mut result: HashMap<String, HashSet<String>> = HashMap::new();
    for (from, to) in connections {
        result
            .entry(from.to_string())
            .or_insert_with(HashSet::new)
            .insert(to.to_string());
        result
            .entry(to.to_string())
            .or_insert_with(HashSet::new)
            .insert(from.to_string());
    }
    result
}

fn neighbours<'a>(nodes: &'a Network, current: &str) -> Option<&'a HashSet<String>> {
    nodes.get(current)
}

trait Visited: Display {
    fn can_visit(&self, node: &str) -> bool;
    fn visit(&mut self, node: &str);
    fn unvisit(&mut self, node: &str);
}

struct BaseTracker {
    visit_count: HashMap<String, usize>,
    visits: Vec<String>,
}

impl BaseTracker {
    fn new() -> BaseTracker {
        BaseTracker {
            visit_count: HashMap::new(),
            visits: Vec::new(),
        }
    }

    fn visit(&mut self, node: &str) {
        *self.visit_count.entry(node.to_string()).or_insert(0) += 1;
        self.visits.push(node.to_string());
    }

    fn unvisit(&mut self, node: &str) {
        match self.visit_count.get(node) {
            None | Some(0) => {
                panic!("attempt to unvisit a node we never visited, {}", node);
            }
            Some(_) => (),
        }
        *self.visit_count.entry(node.to_string()).or_insert(0) -= 1;
        match self.visits.pop() {
            Some(last) => {
                assert_eq!(last, node, "out-of-order call to unvisit");
            }
            None => {
                panic!("attempt to unvisit a node {} while history is empty", node);
            }
        }
    }
}

impl Display for BaseTracker {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut first: bool = true;
        for node in &self.visits {
            if first {
                first = false;
            } else {
                f.write_str(",")?;
            }
            write!(f, "{}", node)?;
        }
        Ok(())
    }
}

struct Part1Tracker {
    inner: BaseTracker,
}

impl Part1Tracker {
    fn new() -> Part1Tracker {
        Part1Tracker {
            inner: BaseTracker::new(),
        }
    }
}

impl Visited for Part1Tracker {
    fn can_visit(&self, node: &str) -> bool {
        if is_big_cave(node) {
            true
        } else {
            let count = *self.inner.visit_count.get(node).unwrap_or(&0);
            count < 1
        }
    }

    fn visit(&mut self, node: &str) {
        self.inner.visit(node);
    }

    fn unvisit(&mut self, node: &str) {
        self.inner.unvisit(node);
    }
}

impl Display for Part1Tracker {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

struct Part2Tracker {
    inner: BaseTracker,
}

impl Part2Tracker {
    fn new() -> Part2Tracker {
        Part2Tracker {
            inner: BaseTracker::new(),
        }
    }
}

impl Display for Part2Tracker {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl Visited for Part2Tracker {
    fn can_visit(&self, node: &str) -> bool {
        let is_start_or_end = || -> bool { node == "start" || node == "end" };

        let too_many_visits = |inner: &BaseTracker| -> bool {
            inner
                .visit_count
                .iter()
                .any(|(node, visits)| !is_big_cave(node) && *visits > 1)
        };

        if is_big_cave(node) {
            true
        } else {
            match self.inner.visit_count.get(node) {
                Some(0) | None => true,
                Some(1) => !(is_start_or_end() || too_many_visits(&self.inner)),
                Some(2) => false,
                Some(n) => {
                    panic!("Part2Tracker: visited node {} {} times, max 2", node, n);
                }
            }
        }
    }

    fn visit(&mut self, node: &str) {
        self.inner.visit(node);
    }

    fn unvisit(&mut self, node: &str) {
        self.inner.unvisit(node);
    }
}

fn path_counter<V: Visited>(start: &str, end: &str, nodes: &Network, visited: &mut V) -> usize {
    visited.visit(start);
    let count = if start == end {
        println!("{}", visited);
        1
    } else {
        let mut n = 0;
        if let Some(neighbours) = neighbours(nodes, start) {
            for neighbour in neighbours {
                let can_visit = visited.can_visit(neighbour);
                if can_visit {
                    n += path_counter(neighbour, end, nodes, visited);
                }
            }
        }
        n
    };
    visited.unvisit(start);
    count
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Part {
    One,
    Two,
}

fn count_paths(nodes: &Network, pt: &Part) -> usize {
    match pt {
        Part::One => {
            let mut tracker = Part1Tracker::new();
            path_counter("start", "end", nodes, &mut tracker)
        }
        Part::Two => {
            let mut tracker = Part2Tracker::new();
            path_counter("start", "end", nodes, &mut tracker)
        }
    }
}

#[cfg(test)]
fn count_paths_in_connections(connections: &[&str], pt: &Part) -> usize {
    let net = make_graph_from_strings(connections);
    count_paths(&net, pt)
}

#[test]
fn test_count_paths_part1() {
    assert_eq!(
        count_paths_in_connections(
            &["start-A", "start-b", "A-c", "A-b", "b-d", "A-end", "b-end"],
            &Part::One
        ),
        10
    );
    assert_eq!(
        count_paths_in_connections(
            &[
                "dc-end", "HN-start", "start-kj", "dc-start", "dc-HN", "LN-dc", "HN-end", "kj-sa",
                "kj-HN", "kj-dc"
            ],
            &Part::One
        ),
        19
    );
    assert_eq!(
        count_paths_in_connections(
            &[
                "fs-end", "he-DX", "fs-he", "start-DX", "pj-DX", "end-zg", "zg-sl", "zg-pj",
                "pj-he", "RW-he", "fs-DX", "pj-RW", "zg-RW", "start-pj", "he-WI", "zg-he", "pj-fs",
                "start-RW",
            ],
            &Part::One
        ),
        226
    );
}

#[test]
fn test_count_paths_part2() {
    assert_eq!(
        count_paths_in_connections(
            &["start-A", "start-b", "A-c", "A-b", "b-d", "A-end", "b-end"],
            &Part::Two
        ),
        36
    );
    assert_eq!(
        count_paths_in_connections(
            &[
                "dc-end", "HN-start", "start-kj", "dc-start", "dc-HN", "LN-dc", "HN-end", "kj-sa",
                "kj-HN", "kj-dc"
            ],
            &Part::Two
        ),
        103
    );
    assert_eq!(
        count_paths_in_connections(
            &[
                "fs-end", "he-DX", "fs-he", "start-DX", "pj-DX", "end-zg", "zg-sl", "zg-pj",
                "pj-he", "RW-he", "fs-DX", "pj-RW", "zg-RW", "start-pj", "he-WI", "zg-he", "pj-fs",
                "start-RW",
            ],
            &Part::Two
        ),
        3509
    );
}

fn is_big_cave(node: &str) -> bool {
    node.chars().all(|ch| ch.is_ascii_uppercase())
}

#[test]
fn test_is_big_cave() {
    assert!(!is_big_cave("start"));
    assert!(is_big_cave("A"));
    assert!(!is_big_cave("b"));
    assert!(!is_big_cave("Mixed"));
}

fn string_to_connection(s: &str) -> (String, String) {
    let mut it = s.split('-');
    match it.next() {
        Some(from) => match it.next() {
            Some(to) => match it.next() {
                None => (from.to_string(), to.to_string()),
                Some(unwanted) => {
                    panic!("unwanted extra field {}", unwanted);
                }
            },
            None => {
                panic!("missing 'to' field");
            }
        },
        None => {
            panic!("missing 'from' field");
        }
    }
}

fn main() {
    let connections: Vec<(String, String)> = io::BufReader::new(io::stdin())
        .lines()
        .map(|thing| thing.unwrap())
        .map(|line| string_to_connection(line.as_str()))
        .collect();
    let graph = make_graph(&connections);

    part1(&graph);
    part2(&graph);
}
