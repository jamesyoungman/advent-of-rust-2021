use std::collections::HashMap;
use std::collections::HashSet;
use std::io;
use std::io::prelude::*;

type Network = HashMap<String, HashSet<String>>;

fn part1(nodes: &Network) {
    println!("Day 12 part 1: {}", count_paths(nodes));
}

fn part2(_nodes: &Network) {}

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

fn path_counter(
    start: &str,
    end: &str,
    nodes: &Network,
    visited: &mut HashSet<String>,
    visited_inorder: &mut Vec<String>,
) -> usize {
    visited.insert(start.to_string());
    visited_inorder.push(start.to_string());
    let count = if start == end {
        //print!("complete path:");
        //for node in visited_inorder.iter() {
        //    print!(" {}", node);
        //}
        //println!("");
        1
    } else {
        let mut n = 0;
        if let Some(neighbours) = neighbours(nodes, start) {
            for neighbour in neighbours {
                let can_visit = is_big_cave(neighbour) || !visited.contains(neighbour);
                //println!("can visit {} from {}? {}", neighbour, start, can_visit);
                if can_visit {
                    //println!("traversing {} -> {}", start, neighbour);
                    n += path_counter(neighbour, end, nodes, visited, visited_inorder);
                }
            }
        }
        n
    };
    visited.remove(start);
    visited_inorder.pop();
    count
}

fn count_paths(nodes: &Network) -> usize {
    let mut visited: HashSet<String> = HashSet::new();
    let mut visited_inorder: Vec<String> = Vec::new();
    path_counter("start", "end", nodes, &mut visited, &mut visited_inorder)
}

#[cfg(test)]
fn count_paths_in_connections(connections: &[&str]) -> usize {
    let net = make_graph_from_strings(connections);
    count_paths(&net)
}

#[test]
fn test_count_paths() {
    assert_eq!(
        count_paths_in_connections(&["start-A", "start-b", "A-c", "A-b", "b-d", "A-end", "b-end"]),
        10
    );
    assert_eq!(
        count_paths_in_connections(&[
            "dc-end", "HN-start", "start-kj", "dc-start", "dc-HN", "LN-dc", "HN-end", "kj-sa",
            "kj-HN", "kj-dc"
        ]),
        19
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
