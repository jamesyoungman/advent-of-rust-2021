use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::io::prelude::*;

type Node = usize;

#[derive(Clone)]
struct Network {
    nodes: HashMap<Node, HashSet<Node>>,
    name_to_node: HashMap<String, Node>,
    node_to_name: HashMap<Node, String>,
}

impl Network {
    pub fn new() -> Network {
        Network {
            nodes: HashMap::new(),
            name_to_node: HashMap::new(),
            node_to_name: HashMap::new(),
        }
    }

    pub fn assign_node_id(&mut self, name: &str) -> Node {
        match self.name_to_node.get(name) {
            Some(node) => *node,
            None => {
                let next = self.name_to_node.len();
                self.name_to_node.insert(name.to_string(), next);
                self.node_to_name.insert(next, name.to_string());
                next
            }
        }
    }

    pub fn name_to_node(&self, name: &str) -> Option<Node> {
	self.name_to_node.get(name).copied()
    }

    pub fn node_to_name(&self, node: &Node) -> Option<String> {
        self.node_to_name.get(node).map(String::from)
    }

    pub fn is_big_cave(&self, node: &Node) -> bool {
        match self.node_to_name(node) {
            Some(name) => is_big_cave(&name),
            None => false,
        }
    }

    pub fn add(&mut self, from: &str, to: &str) {
        let f: Node = self.assign_node_id(from);
        let t: Node = self.assign_node_id(to);
        self.nodes.entry(f).or_insert_with(HashSet::new).insert(t);
    }

    pub fn neighbours(&self, current: &Node) -> Option<&HashSet<Node>> {
        self.nodes.get(current)
    }
}

fn part1(nodes: &mut Network) {
    println!(
        "Day 12 part 1: {}",
        count_paths(nodes, can_visit_part1).unwrap()
    );
}

fn part2(nodes: &mut Network) {
    println!(
        "Day 12 part 2: {}",
        count_paths(nodes, can_visit_part2).unwrap()
    );
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
    let mut result = Network::new();
    for (from, to) in connections {
        result.add(from, to);
        result.add(to, from);
    }
    result
}

struct VisitTracker {
    visit_count: HashMap<Node, usize>,
    visits: Vec<Node>,
}

impl VisitTracker {
    fn new() -> VisitTracker {
        VisitTracker {
            visit_count: HashMap::new(),
            visits: Vec::new(),
        }
    }

    fn visit(&mut self, node: &Node) {
        *self.visit_count.entry(*node).or_insert(0) += 1;
        self.visits.push(*node);
    }

    fn unvisit(&mut self, node: &Node) {
        match self.visit_count.get(node) {
            None | Some(0) => {
                panic!("attempt to unvisit a node we never visited, {}", node);
            }
            Some(_) => (),
        }
        *self.visit_count.entry(*node).or_insert(0) -= 1;
        match self.visits.pop() {
            Some(last) => {
                assert_eq!(&last, node, "out-of-order call to unvisit");
            }
            None => {
                panic!("attempt to unvisit a node {} while history is empty", node);
            }
        }
    }
}

impl Display for VisitTracker {
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

fn can_visit_part1(network: &Network, tracker: &VisitTracker, node: &Node) -> bool {
    if network.is_big_cave(node) {
        true
    } else {
        let count = *tracker.visit_count.get(node).unwrap_or(&0);
        count < 1
    }
}

fn can_visit_part2(network: &Network, tracker: &VisitTracker, node: &Node) -> bool {
    let is_start_or_end = || -> bool {
        match network.node_to_name(node) {
            Some(s) => s == "start" || s == "end",
            None => false,
        }
    };

    let too_many_visits = || -> bool {
        tracker
            .visit_count
            .iter()
            .any(|(node, visits)| !network.is_big_cave(node) && *visits > 1)
    };

    if network.is_big_cave(node) {
        true
    } else {
        match tracker.visit_count.get(node) {
            Some(0) | None => true,
            Some(1) => !(is_start_or_end() || too_many_visits()),
            Some(2) => false,
            Some(n) => {
                panic!("can_visit_part2: visited node {} {} times, max 2", node, n);
            }
        }
    }
}

fn path_counter(
    start: &Node,
    end: &Node,
    nodes: &Network,
    visited: &mut VisitTracker,
    can_visit: fn(network: &Network, tracker: &VisitTracker, node: &Node) -> bool,
) -> usize {
    visited.visit(start);
    let count = if start == end {
        //println!("{}", visited);
        1
    } else {
        let mut n = 0;
        if let Some(neighbours) = nodes.neighbours(start) {
            for neighbour in neighbours {
                if can_visit(nodes, visited, neighbour) {
                    n += path_counter(neighbour, end, nodes, visited, can_visit);
                }
            }
        }
        n
    };
    visited.unvisit(start);
    count
}

fn count_paths(
    nodes: &mut Network,
    can_visit: fn(network: &Network, tracker: &VisitTracker, node: &Node) -> bool,
) -> Result<usize, String> {
    match nodes.name_to_node("start") {
        Some(start) => match nodes.name_to_node("end") {
            Some(end) => Ok(path_counter(
                &start,
                &end,
                nodes,
                &mut VisitTracker::new(),
                can_visit,
            )),
            None => Err("no end node".to_string()),
        },
        None => Err("no start node".to_string()),
    }
}

#[cfg(test)]
fn count_paths_in_connections(
    connections: &[&str],
    can_visit: fn(network: &Network, tracker: &VisitTracker, node: &Node) -> bool,
) -> Result<usize, String> {
    let mut graph = make_graph_from_strings(connections);
    count_paths(&mut graph, can_visit)
}

#[test]
fn test_count_paths_part1() {
    assert_eq!(
        count_paths_in_connections(
            &["start-A", "start-b", "A-c", "A-b", "b-d", "A-end", "b-end"],
            can_visit_part1,
        ),
        Ok(10)
    );
    assert_eq!(
        count_paths_in_connections(
            &[
                "dc-end", "HN-start", "start-kj", "dc-start", "dc-HN", "LN-dc", "HN-end", "kj-sa",
                "kj-HN", "kj-dc"
            ],
            can_visit_part1,
        ),
        Ok(19)
    );
    assert_eq!(
        count_paths_in_connections(
            &[
                "fs-end", "he-DX", "fs-he", "start-DX", "pj-DX", "end-zg", "zg-sl", "zg-pj",
                "pj-he", "RW-he", "fs-DX", "pj-RW", "zg-RW", "start-pj", "he-WI", "zg-he", "pj-fs",
                "start-RW",
            ],
            can_visit_part1,
        ),
        Ok(226)
    );
}

#[test]
fn test_count_paths_part2() {
    assert_eq!(
        count_paths_in_connections(
            &["start-A", "start-b", "A-c", "A-b", "b-d", "A-end", "b-end"],
            can_visit_part2,
        ),
        Ok(36)
    );
    assert_eq!(
        count_paths_in_connections(
            &[
                "dc-end", "HN-start", "start-kj", "dc-start", "dc-HN", "LN-dc", "HN-end", "kj-sa",
                "kj-HN", "kj-dc"
            ],
            can_visit_part2,
        ),
        Ok(103)
    );
    assert_eq!(
        count_paths_in_connections(
            &[
                "fs-end", "he-DX", "fs-he", "start-DX", "pj-DX", "end-zg", "zg-sl", "zg-pj",
                "pj-he", "RW-he", "fs-DX", "pj-RW", "zg-RW", "start-pj", "he-WI", "zg-he", "pj-fs",
                "start-RW",
            ],
            can_visit_part2,
        ),
        Ok(3509)
    );
}

fn is_big_cave(node_name: &str) -> bool {
    node_name.chars().all(|ch| ch.is_ascii_uppercase())
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
    let mut graph = make_graph(&connections);

    part1(&mut graph.clone());
    part2(&mut graph);
}
