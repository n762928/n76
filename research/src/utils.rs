use egg::*;
use libc::{rewind, CIBAUD, EPOLLRDHUP, GENL_UNS_ADMIN_PERM};
use core::num;
use std::collections::btree_map::Range;
use std::collections::{HashMap, HashSet, *};
use std::f64::consts;
use std::fmt::format;
use std::hash::Hash;
use std::io::{BufRead, BufReader, Seek, SeekFrom};
use std::ffi::CString;
use std::fs::{File, DirEntry};
use std::io::prelude::*;
use std::fs::OpenOptions;
use std::ops::Sub;
use std::{env, fs, i64, process, result, usize};
use std::cmp;
use bimap::{BiMap, BiHashMap};
use factorial::Factorial;
use std::collections::VecDeque;
use regex::{Match, Regex};
use lazy_static::lazy_static;
use std::sync::Mutex;
use std::time::Instant;
use std::cell::UnsafeCell;
use std::process::Command;
use std::str;
use std::time::Duration;

pub const DIRECTORY_PATH: &'static str       = "/tmp/gql/";
pub const SRC_GRAPH_BLISS_FILE: &'static str = "src_graph.txt";
pub const BLISS_PIPE_NAME: &'static str      = "my_pipe";
pub const MORPH_PIPE_NAME: &'static str      = "morph_pipe";
pub const RESULT_DIRECTORY: &'static str     = "result";
pub const COST_DIRECTORY: &'static str       = "cost/";
pub const SRC_DIRECTORY: &'static str        = "src/";
pub const USER_RULES_PATH: &'static str      = "user_rules/";
pub const DATA_GRAPH_PATH: &'static str      = "mico.lg";
pub const PEREGRINE_DIRECTORY: &'static str  = "peregrine/";

static NUM_PATTERNS: Mutex<usize> = Mutex::new(0);

fn simplify(s: &str, dynamic_rewrite_rules: Vec<Rewrite<SimpleLanguage, ()>>) -> (String, f64, EGraph<SimpleLanguage, ()>) {
    let expr: RecExpr<SimpleLanguage> = s.parse().unwrap();
    let mut rewrite_rules = get_static_rewrite_rules();
    rewrite_rules.extend(dynamic_rewrite_rules);
    let start = Instant::now();
    //default
    // let mut runner = Runner::default().with_iter_limit(40).with_node_limit(50_000).with_time_limit(Duration::from_secs(240)).with_expr(&expr).run(&rewrite_rules);
    let mut runner = Runner::default().with_iter_limit(40).with_node_limit(100_000).with_time_limit(Duration::from_secs(120)).with_expr(&expr).run(&rewrite_rules);
    find_patterns_costs();
    // custom_costs();
    let root = runner.roots[0];
    let end = Instant::now();
    let current_run_time = (end - start).as_secs();
    let extractor= Extractor::new(&runner.egraph, NaiveCostFunction);
    let (best_cost, best) = extractor.find_best(root);
    println!();
    // println!("best is {}", best);
    (best.to_string(), best_cost, runner.egraph)
}

// fn simplify(s: &str, dynamic_rewrite_rules: Vec<Rewrite<SimpleLanguage, ()>>) -> (String, f64, EGraph<SimpleLanguage, ()>) {
//     let expr: RecExpr<SimpleLanguage> = s.parse().unwrap();
//     let mut rewrite_rules = get_static_rewrite_rules();
//     rewrite_rules.extend(dynamic_rewrite_rules);

//     let start = Instant::now();
//     let mut runner = Runner::default()
//         .with_explanations_enabled()
//         .with_expr(&expr)
//         .run(&rewrite_rules);

//     let end = Instant::now();
//     let current_run_time = (end - start).as_secs();
//     find_patterns_costs();
//     let root = runner.roots[0];

//     // Clone the egraph to use in the separate thread
//     let egraph_clone = runner.egraph.clone();

//     // Timeout setup
//     let (tx, rx) = mpsc::channel();
//     let timeout = Duration::from_secs(1 - current_run_time);

//     // Run extractor in a separate thread with the cloned egraph
//     thread::spawn(move || {
//         let extractor = Extractor::new(&egraph_clone, NaiveCostFunction);
//         let result = extractor.find_best(root);
//         let _ = tx.send(result); // Send result back to main thread
//     });

//     // Initialize best_cost and best with default values
//     let mut best_cost = f64::INFINITY; // Assign default cost for timeout
//     let mut best = expr.clone(); // Default to the input expression if extraction times out

//     // Wait for the result with a timeout
//     match rx.recv_timeout(timeout) {
//         Ok(result) => {
//             best_cost = result.0;
//             best = result.1;
//         },
//         Err(_) => {
//             println!("Extractor timed out after 10 minutes.");
//         }
//     };


//     println!();
//     println!("best is {}", best);
//     (best.to_string(), best_cost, runner.egraph) // `runner.egraph` is still accessible here
// }

fn make_graph_file(graph_info: &GraphInfo, bliss_format: bool) -> Vec<String> {
    let mut bliss_graph = vec![];
    for i in 0..graph_info.graph.len() {
        for j in i+1..graph_info.graph.len() {
            if graph_info.graph[i][j] == 1 {
                bliss_graph.push((i + 1, j + 1));
            }
        }
    }
    let mut lines = vec![];
    if bliss_format {
        lines.push("p edge ".to_string() + &graph_info.graph.len().to_string() + " " + &bliss_graph.len().to_string());
    }
    for v in bliss_graph.iter() {
        let mut edge = v.0.to_string() + " " + &v.1.to_string();
        if bliss_format {
            edge = "e ".to_string() + &edge;
        }
        lines.push(edge);
    }
    lines
}

fn create_pipe(pipe_name: &str) {
    let path = DIRECTORY_PATH.to_string() + pipe_name;
    let filename = CString::new(path).unwrap();
    unsafe {
        libc::mkfifo(filename.as_ptr(), 0o777);
    }
}

fn write_to_pipe(pipe_name: &str, message: String) {
    let path = DIRECTORY_PATH.to_string() + pipe_name;
    let mut file: File = OpenOptions::new()
        .write(true)
        .append(true)
        .open(path)
        .unwrap();

    file.write_all(message.as_bytes()).expect("failed");

}

fn write_to_file(lines: Vec<String>, path: String) {
    let mut file = File::create(path).expect("error");
    let content = lines.join("\n");
    file.write_all(content.as_bytes()).expect("failed");
}

fn get_done_signal() {
    let pipe_path = DIRECTORY_PATH.to_string() + BLISS_PIPE_NAME;
    let file = File::open(pipe_path).unwrap();
    let reader = BufReader::new(file);
    reader.lines().next();
}

fn number_to_alphabet(mut num: usize) -> String {
    let mut result = String::new();
    while num > 0 {
        num -= 1;
        result.push((b'a' + (num % 26) as u8) as char);
        num /= 26;
    }
    result.chars().rev().collect()
}

fn alphabet_to_number(s: &str) -> usize {
    s.chars().fold(0, |acc, c| acc * 26 + (c as usize - 'a' as usize + 1))
}


fn get_edges_in_string_format(input: &str) -> Vec<(String, String)> {
    let result = input.replace("Match", "")
                      .replace("(", "")
                      .replace(")", "");

    let edges: Vec<&str> = result
        .split("--")
        .filter(|s| !s.trim().is_empty())
        .collect();

    let edge_tuples: Vec<(String, String)> = edges
        .iter()
        .map(|&edge| {
            let components: Vec<&str> = edge.trim().split_whitespace().collect();
            if components.len() == 2 {
                (components[0].to_string(), components[1].to_string())
            } else {
                eprintln!("Invalid edge: {}", edge);
                ("_".to_string(), "_".to_string())
            }
        })
        .collect();
    edge_tuples
}

fn build_graph_adjacency_matrix(edges_string: &Vec<(String, String)>, num_nodes: usize) -> GraphInfo {
    let mut num_edges = 0;
    let mut input_graph_matrix: Vec<Vec<usize>> = vec![vec![0; num_nodes]; num_nodes];
    for edge_string in edges_string.iter() {
        let node1 = alphabet_to_number(&edge_string.0) - 1;
        let node2 = alphabet_to_number(&edge_string.1) - 1;
        input_graph_matrix[node1][node2] = 1;
        input_graph_matrix[node2][node1] = 1;
        num_edges += 1;
    }
    let graph_info = GraphInfo {
        graph: input_graph_matrix,
        num_edges: num_edges,
    };
    graph_info
}

struct GraphInfo {
    graph: Vec<Vec<usize>>,
    num_edges: i32,
}

fn parse_input(input: &str, num_nodes: usize) -> GraphInfo {
    let edges_string = get_edges_in_string_format(&input);
    let input_graph = build_graph_adjacency_matrix(&edges_string, num_nodes);
    let input_graph_info = GraphInfo {
        graph : input_graph.graph,
        num_edges: input_graph.num_edges,
    };
    input_graph_info
}

// fn get_num_nodes(edges: &Vec<(String, String)>) -> usize {
//     let mut nodes = HashSet::new();
//     for edge in edges.iter() {
//         nodes.insert(edge.0.clone());
//         nodes.insert(edge.1.clone());
//     }
//     nodes.len()
// }

fn get_num_nodes(input: &str) -> usize {
    let cleaned = input.replace("(", "").replace(")", "");
    let components: Vec<&str> = cleaned.split_whitespace().collect();
    let mut nodes = HashSet::new();
    for component in components {
        if component.to_string() != "Match" && component.to_string() != "--" && component.to_string() != "!-" {
            nodes.insert(component);
        }
    }
    nodes.len()
}

fn clique(nodes: HashSet<String>) -> HashSet<(String, String)> {
    let mut all_edges = HashSet::new();
    for v1 in nodes.iter() {
        for v2 in nodes.iter() {
            if v1 == v2 {
                continue;
            }
            let edge = (v1.clone(), v2.clone());
            if !all_edges.contains(&edge) && !all_edges.contains(&(edge.1.clone(), edge.0.clone())) {
                all_edges.insert(edge);
            }
        }

    }
    all_edges
}

fn create_file_reader(entry: &DirEntry) -> BufReader<File> {
    let result_directory = DIRECTORY_PATH.to_string() + RESULT_DIRECTORY;
    let file_name = entry.file_name().to_string_lossy().into_owned();
    let file = File::open(result_directory.to_owned() + "/" + &file_name).unwrap();
    let reader = BufReader::new(file);
    reader
}

fn parse_graph_edges(reader: BufReader<File>) -> Vec<(i32, i32)> {
    let mut edges = Vec::new();
    for line_result in reader.lines() {
        let line = line_result.unwrap();
        if line.starts_with("e ") {
            let mut parts = line.split_whitespace();
            parts.next();
            if let (Some(first_num_str), Some(second_num_str)) = (parts.next(), parts.next()) {
                if let (Ok(first_num), Ok(second_num)) = (first_num_str.parse::<i32>(), second_num_str.parse::<i32>()) {
                    edges.push((first_num, second_num));
                }
            }
        }
     }
    edges
}

fn get_number_of_nodes_from_bliss_file(first_line: String) -> usize {
    let mut parts = first_line.split_whitespace();
    let p = parts.next().unwrap();
    let e = parts.next().unwrap();
    let nodes_num = parts.next().unwrap().parse::<usize>().unwrap();
    nodes_num
}

fn read_graph_from_bliss_file(reader: &mut BufReader<File>, coefficient: &mut i32) -> GraphInfo {
    let nodes_num = get_number_of_nodes_from_bliss_file(reader.lines().next().unwrap().unwrap());
    let mut num_edges = 0;
    let mut graph = vec![vec![0; nodes_num]; nodes_num];
    for line_result in reader.lines() {
        let line = line_result.unwrap();
        if line.starts_with("n ") {
            continue;
        }
        else if line.starts_with("e ") {
            let mut parts = line.split_whitespace();
            parts.next();
            let u = parts.next().unwrap().parse::<usize>().unwrap() - 1;
            let v = parts.next().unwrap().parse::<usize>().unwrap() - 1;
            graph[u][v] = 1;
            graph[v][u] = 1;
            num_edges += 1;
        }
        else {
            *coefficient = line.parse::<i32>().unwrap();
        }
     }
     let graph_info = GraphInfo {
        graph: graph,
        num_edges: num_edges,
     };
    graph_info
}

fn is_graph_complete(num_edges: i32, num_nodes: i32) -> bool {
    num_edges == (calculate_permutation(num_nodes as u64, 2) as i32)
}

fn generate_morph_rule_using_subtraction(pattern: &str, edge_induced_pattern: &str, provenance: &Id, egraph: &mut EGraph<SimpleLanguage, ()>) -> Id {
    let anti_edges_set = collect_anti_edges_numbers(pattern);
    let is_edge_induced_pattern = pattern == edge_induced_pattern;
    let num_nodes = get_num_nodes(pattern);
    let pattern_info: GraphInfo = parse_input(&edge_induced_pattern, num_nodes);
    call_bliss(&pattern_info, "vertex_induced");
    let result_directory = DIRECTORY_PATH.to_string() + RESULT_DIRECTORY;
    let peregrine_directory = DIRECTORY_PATH.to_string() + PEREGRINE_DIRECTORY;
    fs::create_dir(&peregrine_directory);
    let entries = fs::read_dir(result_directory).unwrap();
    let mut index = 0;
    let mut union_id = Id::from(0_usize); 
    let mut index = 0;
    let mut graph_infos = vec![];
    for entry in entries {
        index += 1;
        let dir_entry = entry.unwrap();
        let mut reader = create_file_reader(&dir_entry);
        let mut coefficient = 0;
        let new_graph_info  = read_graph_from_bliss_file(&mut reader, &mut coefficient); 
        make_peregrine_datagraph(&new_graph_info.graph, index);
        graph_infos.push(new_graph_info);
        fs::remove_file(&dir_entry.path());
    }
    write_pattern_to_peregrine(&pattern_info.graph, &anti_edges_set, false);
    let mut index = 1;
    let mut first_pattern = true;
    for graph_info in graph_infos {
        let mut coefficient = find_coefficient(index);
        index += 1;
        if coefficient == 0 {
            continue;
        }
        let mut should_write_anti_edges = true;
        if !is_edge_induced_pattern && pattern_info.num_edges != graph_info.num_edges {
            coefficient *= -1;
            
        }
        if !is_edge_induced_pattern && pattern_info.num_edges == graph_info.num_edges {
            should_write_anti_edges = false;
            
        }
        let graph_node = graph_to_egraph_node(&graph_info.graph, &pattern_info, should_write_anti_edges, provenance, egraph, &HashSet::new());
        let count_num = egraph.add(SimpleLanguage::Num(coefficient as i64));
        let count_node = egraph.add(SimpleLanguage::Count([count_num, graph_node]));
        if first_pattern {
            union_id = count_node;
        }
        else {
            union_id = egraph.add(SimpleLanguage::Union([count_node, union_id]));
        }
        first_pattern = false;
    }
    fs::remove_dir_all(&peregrine_directory);
    union_id
}

// fn generate_morph_rule_using_subtraction(pattern: &str, edge_induced_pattern: &str, provenance: &Id, egraph: &mut EGraph<SimpleLanguage, ()>) -> Id {
//     let is_edge_induced_pattern = pattern == edge_induced_pattern;
//     let num_nodes = get_num_nodes(pattern);
//     let pattern_info: GraphInfo = parse_input(&edge_induced_pattern, num_nodes);
//     call_bliss(&pattern_info, "vertex_induced");
//     let result_directory = DIRECTORY_PATH.to_string() + RESULT_DIRECTORY;
//     let entries = fs::read_dir(result_directory).unwrap();
//     let mut index = 0;
//     let mut union_id = Id::from(0_usize); 
//     for entry in entries {
//         let dir_entry = entry.unwrap();
//         let mut reader = create_file_reader(&dir_entry);
//         let mut coefficient = 0;
//         let new_graph_info = read_graph_from_bliss_file(&mut reader, &mut coefficient);
//         let mut should_write_anti_edges = true;
//         if !is_edge_induced_pattern && pattern_info.num_edges != new_graph_info.num_edges {
//             coefficient *= -1;
            
//         }
//         if !is_edge_induced_pattern && pattern_info.num_edges == new_graph_info.num_edges {
//             should_write_anti_edges = false;
            
//         }
//         let graph_node = graph_to_egraph_node(&new_graph_info.graph, &pattern_info, should_write_anti_edges, provenance, egraph, &HashSet::new());
//         let count_num = egraph.add(SimpleLanguage::Num(coefficient as i64));
//         let count_node = egraph.add(SimpleLanguage::Count([count_num, graph_node]));
//         if index == 0 {
//             union_id = count_node;
//         }
//         else {
//             union_id = egraph.add(SimpleLanguage::Union([count_node, union_id]));
//         }
//         index += 1; 
//         println!("read one");
//         fs::remove_file(&dir_entry.path());
//     }
//     union_id
// }

fn generate_morph_rule_using_peregrine(pattern: &str, edge_induced_pattern: &str, provenance: &Id, egraph: &mut EGraph<SimpleLanguage, ()>) -> Id {
    let anti_edges_set = collect_anti_edges_numbers(pattern);
    let num_nodes = get_num_nodes(pattern);
    let pattern_info: GraphInfo = parse_input(&edge_induced_pattern, num_nodes);
    call_bliss(&pattern_info, "edge_induced");
    let result_directory = DIRECTORY_PATH.to_string() + RESULT_DIRECTORY;
    let peregrine_directory = DIRECTORY_PATH.to_string() + PEREGRINE_DIRECTORY;
    fs::create_dir(&peregrine_directory);
    let entries = fs::read_dir(result_directory).unwrap();
    let mut union_id = Id::from(0_usize); 
    let mut index = 0;
    let mut graph_infos = vec![];
    for entry in entries {
        index += 1;
        let dir_entry = entry.unwrap();
        let mut reader = create_file_reader(&dir_entry);
        let mut coefficient = 0;
        let new_graph_info  = read_graph_from_bliss_file(&mut reader, &mut coefficient); 
        make_peregrine_datagraph(&new_graph_info.graph, index);
        graph_infos.push(new_graph_info);
        fs::remove_file(&dir_entry.path());
    }
    write_pattern_to_peregrine(&pattern_info.graph, &anti_edges_set, true);
    let mut index = 1;
    let mut first_pattern = true;
    for graph_info in graph_infos {
        let coefficient = find_coefficient(index);
        index += 1;
        if coefficient == 0 {
            continue;
        }
        let graph_node = graph_to_egraph_node(&graph_info.graph, &pattern_info, true, provenance, egraph, &HashSet::new());
        let count_num = egraph.add(SimpleLanguage::Num(coefficient as i64));
        let count_node = egraph.add(SimpleLanguage::Count([count_num, graph_node]));
        if first_pattern {
            union_id = count_node;
        }
        else {
            union_id = egraph.add(SimpleLanguage::Union([count_node, union_id]));
        }
        first_pattern = false;
    }
    fs::remove_dir_all(&peregrine_directory);
    union_id
}

fn find_coefficient(index: i32) -> i32 {
    let path = DIRECTORY_PATH.to_string() + PEREGRINE_DIRECTORY;
    let path_clone = path.clone();
    let output = Command::new("../peregrine-master/bin/count")
    .arg(path + "data" + &index.to_string())
    .arg(path_clone + "pattern.txt")
    .output()
    .expect("Failed to execute command");
    let stdout = str::from_utf8(&output.stdout).expect("Invalid UTF-8 sequence");
    stdout.lines().last().unwrap().parse().unwrap()
}

fn make_peregrine_datagraph(graph: &Vec<Vec<usize>>, index: i32) {
    let path = DIRECTORY_PATH.to_string() + PEREGRINE_DIRECTORY;
    let path_clone = path.clone();
    let file_path = path + &index.to_string() + ".txt";
    let mut output = OpenOptions::new().write(true).create(true).truncate(true).open(&file_path).unwrap();
    for i in 0..graph.len() {
        for j in i+1..graph.len() {
            if graph[i][j] == 1 {
                writeln!(output, "{} {}", i+1, j+1);
            }
        }
    }
    Command::new("../peregrine-master/bin/convert_data")
    .arg(file_path)
    .arg(path_clone + "data" + &index.to_string())
    .output();
}

fn write_pattern_to_peregrine(graph: &Vec<Vec<usize>>, anti_edges: &HashSet<(usize, usize)>, write_anti_edge: bool) {
    let path = DIRECTORY_PATH.to_string() + PEREGRINE_DIRECTORY;
    let mut output = OpenOptions::new().write(true).create(true).truncate(true).open(path + "pattern.txt").unwrap();
    for i in 0..graph.len() {
        for j in i+1..graph.len() {
            if graph[i][j] == 1 {
                writeln!(output, "{} {}", i+1, j+1);
            }
            else if write_anti_edge && anti_edges.contains(&(i+1, j+1)) || anti_edges.contains(&(j+1, i+1)) {
                writeln!(output, "{} {} {}", i+1, j+1, 1);
            }
        }
    }
}

// fn generate_morph_rule_using_super_pattern(pattern: &str, edge_induced_pattern: &str, provenance: &Id, egraph: &mut EGraph<SimpleLanguage, ()>) -> Id {
//     let anti_edges_set = collect_anti_edges_numbers(pattern);
//     call_bliss(&pattern_info, "permutation");
//     let result_directory = DIRECTORY_PATH.to_string() + RESULT_DIRECTORY;
//     let entries = fs::read_dir(result_directory).unwrap();
//     let mut index = 0;
//     let mut union_id = Id::from(0_usize); 
//     for entry in entries {
//         let anti_edges_set_clone = anti_edges_set.clone();
//         let dir_entry = entry.unwrap();
//         let mut reader = create_file_reader(&dir_entry);
//         let mut coefficient = 0;
//         let (new_graph_info, node_permutations) = read_graph_from_bliss_file(&mut reader, &mut coefficient);
//         let graph_node_string = create_permuted_pattern_for_moprh_rule(&(new_graph_info, anti_edges_set_clone), &node_permutations);
//         let graph_node_string_recexpr: RecExpr<SimpleLanguage> = graph_node_string.parse().unwrap(); 
//         push_to_global_patterns_vec(graph_node_string);
//         let graph_match_node = egraph.add_expr(&graph_node_string_recexpr);
//         let graph_node = egraph.add(SimpleLanguage::Morph([*provenance, graph_match_node]));
//         let count_num = egraph.add(SimpleLanguage::Num(coefficient));
//         let count_node = egraph.add(SimpleLanguage::Count([count_num, graph_node]));
//         if index == 0 {
//             union_id = count_node;
//         }
//         else {
//             union_id = egraph.add(SimpleLanguage::Union([count_node, union_id]));
//         }
//         index += 1; 
//         fs::remove_file(&dir_entry.path());
//     }
//     union_id
// }

fn generate_morph_rewrite_rule(pattern: &str, provenance: &Id, egraph: &mut EGraph<SimpleLanguage, ()>) -> Id {
    let super_pattern = convert_to_edge_induced_pattern(&pattern.to_string(), true);
    let num_nodes = get_num_nodes(pattern);
    let super_pattern_info = parse_input(&super_pattern, num_nodes);
    let edge_induced_pattern = convert_to_edge_induced_pattern(&pattern.to_string(), false);
    let is_edge_induced_pattern = pattern == edge_induced_pattern;
    if is_graph_complete(super_pattern_info.num_edges, super_pattern_info.graph.len() as i32) || is_edge_induced_pattern {
        generate_morph_rule_using_subtraction(pattern, &edge_induced_pattern, provenance, egraph)
    }
    else {
        generate_morph_rule_using_peregrine(pattern, &edge_induced_pattern, provenance, egraph)
    }
    
}

// fn generate_morph_rewrite_rule(pattern: &str, provenance: &Id, egraph: &mut EGraph<SimpleLanguage, ()>) -> Id {
//     let edge_induced_pattern = convert_to_edge_induced_pattern(&pattern.to_string(), false);
//     let is_edge_induced_pattern = pattern == edge_induced_pattern;
//     let pattern_info: GraphInfo = parse_input(&edge_induced_pattern);
//     call_bliss(&pattern_info);
//     let result_directory = DIRECTORY_PATH.to_string() + RESULT_DIRECTORY;
//     let entries = fs::read_dir(result_directory).unwrap();
//     let mut index = 0;
//     let mut union_id = Id::from(0_usize); 
//     for entry in entries {
//         let dir_entry = entry.unwrap();
//         let mut reader = create_file_reader(&dir_entry);
//         let mut coefficient = 0;
//         let new_graph_info = read_graph_from_bliss_file(&mut reader, &mut coefficient);
//         let graph_node = graph_to_egraph_node(&new_graph_info.graph, &pattern_info, is_edge_induced_pattern, provenance, egraph);
//         if !is_edge_induced_pattern && pattern_info.num_edges != new_graph_info.num_edges {
//             coefficient *= -1;
//         }
//         let count_num = egraph.add(SimpleLanguage::Num(coefficient));
//         let count_node = egraph.add(SimpleLanguage::Count([count_num, graph_node]));
//         if index == 0 {
//             union_id = count_node;
//         }
//         else {
//             union_id = egraph.add(SimpleLanguage::Union([count_node, union_id]));
//         }
//         index += 1; 
//         fs::remove_file(&dir_entry.path());
//     }
//     union_id
// }





fn graph_to_egraph_node(graph: &Vec<Vec<usize>>, original_pattern: &GraphInfo, should_write_anti_edges: bool, provenance: &Id, egraph: &mut EGraph<SimpleLanguage, ()>, anti_edges: &HashSet<(String, String)>) -> Id {
    let mut graph_enodes = vec![];
    for i in 0..graph.len() {
        for j in i+1..graph.len() {
            let u = number_to_alphabet(i + 1);
            let v = number_to_alphabet(j + 1);
            if anti_edges.contains(&(u.to_string(), v.to_string())) || anti_edges.contains(&(v.to_string(), u.to_string())) {
                let unode = egraph.add(SimpleLanguage::Symbol(Symbol::from(u)));
                let vnode = egraph.add(SimpleLanguage::Symbol(Symbol::from(v)));
                let anti_edge = egraph.add(SimpleLanguage::AntiEdge([unode, vnode]));
                graph_enodes.push(anti_edge);
            }
            else if graph[i][j] == 1 {
                let unode = egraph.add(SimpleLanguage::Symbol(Symbol::from(u)));
                let vnode = egraph.add(SimpleLanguage::Symbol(Symbol::from(v)));
                let edge = egraph.add(SimpleLanguage::Edge([unode, vnode]));
                graph_enodes.push(edge);
            }
            else if !should_write_anti_edges {
                continue;
            }
            else {
                let unode = egraph.add(SimpleLanguage::Symbol(Symbol::from(u)));
                let vnode = egraph.add(SimpleLanguage::Symbol(Symbol::from(v)));
                let anti_edge = egraph.add(SimpleLanguage::AntiEdge([unode, vnode]));
                graph_enodes.push(anti_edge);
            }
        }
    }
    let match_enode = SimpleLanguage::Match(graph_enodes.into_boxed_slice());
    let match_enode_clone = match_enode.clone();
    let graph_match_node = egraph.add(match_enode);
    let get_node = |id| egraph[id].nodes[0].clone();
    let pattern = match_enode_clone.build_recexpr(get_node); 
    let pattern_string = format!("{}", pattern);
    push_to_global_patterns_vec(pattern_string);
    egraph.add(SimpleLanguage::Morph([*provenance, graph_match_node]))
}


fn calculate_permutation(n: u64, i: u64) -> u64 {
    let result = n.factorial() / ((n - i).factorial() * i.factorial());
    result
}
 

fn get_node_degree(pattern: &Vec<Vec<usize>>, node: usize) -> usize {
    let mut degree = 0;
    for i in 0..pattern.len() {
        if pattern[node][i] == 1 {
            degree += 1;
        }
    }
    degree
}

fn count_fragments(graph: &Vec<Vec<usize>>, pattern: &Vec<Vec<usize>>) -> u64 {
    let cut_set = min_cut(pattern);
    let deg1 = get_node_degree(pattern, cut_set[0].0) - 1;
    let deg2 = get_node_degree(pattern, cut_set[0].1) - 1;
    let mut result = 0;
    for i in 0..graph.len() {
        for j in 0..graph.len() {
            if i == j {
                continue;
            }
            let deg_node = get_node_degree(graph, i) - 1;
            let deg_neighbor = get_node_degree(graph, j) - 1;
            if deg_node >= deg1 && deg_neighbor >= deg2 {
                result += calculate_permutation(deg_node as u64, deg1 as u64) * calculate_permutation(deg_neighbor as u64, deg2 as u64);
            }
        }
    }
    result
}

struct ShrinkageInfo {
    num: i32,
    pattern: String,
}


fn bfs(s: usize, t: usize, parent: &mut Vec<usize>, graph: &mut Vec<Vec<usize>>) -> bool {
    let mut visited = vec![false; graph.len()];
    let mut queue = VecDeque::new();
    queue.push_back(s);
    visited[s] = true;
    while queue.len() != 0 {
        let mut u = queue.pop_front().unwrap();
        for ind in 0..graph.len() {
            if !visited[ind] && graph[u][ind] > 0 {
                queue.push_back(ind);
                visited[ind] = true;
                parent[ind] = u;
            }
        }
    }
    visited[t]
}

fn dfs(graph: &mut Vec<Vec<usize>>, s: usize, visited: &mut Vec<bool>) {
    visited[s] = true;
    for i in 0..graph.len() {
        if graph[s][i] > 0 && !visited[i] {
            dfs(graph, i, visited);
        }
    }
}

fn min_cut(original_graph: &Vec<Vec<usize>>) -> Vec<(usize, usize)>{
    let mut graph = original_graph.clone();
    let mut src = 0;
    let mut sink = graph.len() - 1;
    let mut parent = vec![0; graph.len()];
    let mut max_flow = 0;
    let mut s = sink;
    while bfs(src, sink, &mut parent, &mut graph) {
        let mut path_flow = usize::MAX;
        s = sink;
        while s != src {
            path_flow = cmp::min(path_flow, graph[parent[s]][s]);
            s = parent[s];
        }
        max_flow += path_flow;
        let mut v = sink;
        while v != src {
            let mut u = parent[v];
            graph[u][v] -= path_flow;
            graph[v][u] += path_flow;
            v = parent[v];
        }
    }
    let mut visited = vec![false; graph.len()];
    let mut cut_set = vec![];
    dfs(&mut graph, s, &mut visited);
    for i in 0..graph.len() {
        for j in 0..graph.len() {
            if graph[i][j] == 0 && original_graph[i][j] > 0 && visited[i] {
                cut_set.push((i, j));
            }
        }
    }
    cut_set
}


fn call_bliss(pattern_info: &GraphInfo, message: &str) {
    let bliss_graph = make_graph_file(pattern_info, true);
    write_to_file(bliss_graph, DIRECTORY_PATH.to_string() + SRC_GRAPH_BLISS_FILE);
    write_to_pipe(BLISS_PIPE_NAME, message.to_string());
    get_done_signal();
}

fn build_escape_rewrite_rule_string(num_fragments: &u64, shrinkage_info: &ShrinkageInfo) -> String {
    let mut result = "(+ ".to_string();
    result += &num_fragments.to_string();
    result += " (Count ";
    result += &shrinkage_info.num.to_string();
    result += " ";
    result += &shrinkage_info.pattern;
    result += "))";
    result
}

fn escape_rewrite_rule(input_graph_info: &GraphInfo, input_pattern_info: &GraphInfo, shrinkage_info: &ShrinkageInfo) -> Pattern<SimpleLanguage> {
    let num_fragments = count_fragments(&input_graph_info.graph, &input_pattern_info.graph);
    let escape_rule = build_escape_rewrite_rule_string(&num_fragments, &shrinkage_info);
    println!();
    println!("Escape rule");
    println!("{}", escape_rule);
    escape_rule.parse().unwrap()
}

fn convert_to_edge_induced_pattern(pattern: &String, convert_anti_edge_to_edge: bool) -> String {
    if !convert_anti_edge_to_edge {
        let anti_edge_string_pattern = Regex::new(r" \(!- [a-zA-Z]+ [a-zA-Z]+\)").unwrap();
        anti_edge_string_pattern.replace_all(pattern, "").to_string()
    } else {
        pattern.replace("(!-", "(--")
    }
}

fn get_user_rules() -> HashMap<String, String> {
    let mut user_rules = HashMap::new();
    let rule1_lhs = "(Match (-- a b) (-- a d) (-- a c) (-- b c))".to_string();
    let rule1_rhs = "(Match (-- a b) (-- a d) (-- a c) (-- b c))".to_string();
    user_rules.insert(rule1_lhs, rule1_rhs);
    user_rules
}


// fn get_edges(pattern: &String) -> Vec<(String, String)> {
//     println!("{pattern}");
//     let edge_regex = Regex::new(r"--\s+(\w+)\s+(\w+)").unwrap();
//     let mut edges = Vec::new();
//     for cap in edge_regex.captures_iter(&pattern) {
//        edges.push((cap[1].to_string(), cap[2].to_string()));
//     }
//     edges
// }

fn parse_pattern(pattern: &String, edges: &mut Vec<(String, String)>, anti_edges: &mut Vec<(String, String)>) {
    let new_pattern: String = pattern.chars()
                                   .filter(|&c| c != '(' && c != ')')
                                   .collect();
    let parts: Vec<&str> = new_pattern.split_whitespace().collect();
    for i in 0..parts.len() {
        if parts[i] == "--" {
            edges.push((parts[i + 1].to_string(), parts[i + 2].to_string()));
        }
        if parts[i] == "!-" {
            anti_edges.push((parts[i + 1].to_string(), parts[i + 2].to_string()));
        }
    }
}

fn update_node_map(node_map: &mut HashMap<String, i32>, edge_number:i32, key: &String) -> i32 {
    let mut edge_number_cpy = edge_number.clone();
    if !node_map.contains_key(key) {
        node_map.insert(key.to_string(), edge_number);
        edge_number_cpy += 1;
    }
    edge_number_cpy
}



fn make_morph_graph_file(pattern: &String, file_number: i32) {
    let mut edges = vec![];
    let mut anti_edges = vec![];
    parse_pattern(pattern, &mut edges, &mut anti_edges);
    let mut node_map = HashMap::new();
    let mut file_lines = vec![];
    let mut node_number = 1;
    
    for edge in edges {
        node_number = update_node_map(&mut node_map, node_number, &edge.0);
        node_number = update_node_map(&mut node_map, node_number, &edge.1);
        let new_line = node_map.get(&edge.0).unwrap().to_string() + " " + &node_map.get(&edge.1).unwrap().to_string();
        file_lines.push(new_line);
    }

    for anti_edge in anti_edges {
        node_number = update_node_map(&mut node_map, node_number, &anti_edge.0);
        node_number = update_node_map(&mut node_map, node_number, &anti_edge.1);
        let new_line = node_map.get(&anti_edge.0).unwrap().to_string() + " " + &node_map.get(&anti_edge.1).unwrap().to_string() + " 1" ;
        file_lines.push(new_line);
    }
    let path = DIRECTORY_PATH.to_string() + COST_DIRECTORY + &file_number.to_string() + ".txt";
    write_to_file(file_lines, path);
}

fn find_patterns_costs() {
    let mut index = 0;
    let path = DIRECTORY_PATH.to_string() + COST_DIRECTORY;
    fs::create_dir(path);
    unsafe {
        let patterns = get_global_patterns_vec();
        for pattern in patterns {
            if (pattern.chars().next().unwrap() == 'F') {
                let mut new_pattern = "(Match (-- a b) (-- b c) (-- a c))";
                if *pattern == "F7".to_string() {
                    new_pattern = "(Match (-- a b) (-- b c) (-- c d) (-- a d))";
                }
                make_morph_graph_file(&new_pattern.to_string(), index); 
            }
            else {
                make_morph_graph_file(pattern, index);
            }
            index += 1;
        }
    }
    write_to_pipe(MORPH_PIPE_NAME, "start".to_string());
    read_from_pipe(MORPH_PIPE_NAME);
    get_costs();
}

fn get_costs() {
    let path = DIRECTORY_PATH.to_string() + COST_DIRECTORY + "result.txt";
    let file = File::open(path).unwrap();
    let reader = BufReader::new(file);
    unsafe {
        let map = get_global_map();
        let patterns = get_global_patterns_vec();
        let mut index = 0;
        for line in reader.lines() {
            let line = line.unwrap();
            let cost = line.trim().parse::<f64>().unwrap();
            let pattern = patterns[index].clone();
            map.insert(pattern, cost);
            index += 1;
        }
    }
}

fn create_pipes() {
    create_pipe(BLISS_PIPE_NAME);
    create_pipe(MORPH_PIPE_NAME);
}

fn read_from_pipe(pipe_name: &str) {
    let path = DIRECTORY_PATH.to_string() + pipe_name;
    let mut file = File::open(path).unwrap();
}

fn initialize_num_patterns(num: usize) {
    let mut num_patterns = NUM_PATTERNS.lock().unwrap();
    *num_patterns = num;
}

fn parse_alt_patterns_string(input: String) -> HashMap<String, i32> {
    let mut patterns = HashMap::new();
    let (key_word, rest) = input.split_once(' ').unwrap();
    match key_word {
        "(Union" => {
            let(left, right) = parse_union_string(rest.to_string());
            patterns = parse_alt_patterns_string(left);
            let second_set = parse_alt_patterns_string(right);
            for (pattern, num) in second_set {
                patterns.entry(pattern).and_modify(|value| *value += num).or_insert(num);
            }
        },
        "(Count" => {
            let (num, right) = parse_count_string(rest.to_string());
            patterns = parse_alt_patterns_string(right);
        },
        "(Morph" => {
            let (provenance, pattern) = parse_morph_string(rest.to_string());
            patterns.entry(pattern)
            .and_modify(|value| *value += 1) 
            .or_insert(1);
        },
        "(Const" => {
            let (provenance, formula) = parse_const_string(rest.to_string());
            patterns.entry(formula)
            .and_modify(|value| *value += 1) 
            .or_insert(1);
        }
        _ => {},

    };
    
    patterns
}

fn change_alt_patterns_cost(alt_patterns: &HashMap<String, i32>) {
    unsafe {
        let cost_map = get_global_map();
        for (pattern, num) in alt_patterns {
            cost_map.insert(pattern.to_string(), 0.0);
        }
    }
}

fn simplify_pattern_formula(input: String) -> (HashMap<String, i32>) {
    let mut patterns_count_map = HashMap::new();
    let mut constant:i64 = 0;
    let (key_word, rest) = input.split_once(' ').unwrap();
    match key_word {
        "(Union" => {
            let(left, right) = parse_union_string(rest.to_string());
            patterns_count_map = simplify_pattern_formula(left);
            let second_map = simplify_pattern_formula(right);
            for (pattern, count) in second_map {
                patterns_count_map.entry(pattern)
                .and_modify(|v| *v += count)
                .or_insert(count);
            }
        },
        "(Count" => {
            let (num, right) = parse_count_string(rest.to_string());
            patterns_count_map = simplify_pattern_formula(right);
            for (key, count) in patterns_count_map.iter_mut() {
                *count *= num;
            }
        },
        "(Morph" => {
            let (provenance, pattern) = parse_morph_string(rest.to_string());
            patterns_count_map.insert(pattern, 1);
        },
        "(Const" => {
            let (provenance, formula) = parse_const_string(rest.to_string());
            patterns_count_map.insert(formula, 1);
        },
        _ => {},

    };
    
    patterns_count_map
}

fn pattern_formula_to_string(pattens_map: &HashMap<String, i32>) -> String {
    let mut formula_string = String::new();
    let mut iteration = 0;
    for (pattern, count) in pattens_map {
        let pattern_string = "(Count ".to_string() + &count.to_string() + " " + pattern + ")";
        if iteration == 0 {
            formula_string = pattern_string;
        } 
        else {
            formula_string = "(Union ".to_string() + &formula_string + " " + &pattern_string + ")";
        }
        iteration += 1;
    }
    formula_string
}

fn get_patterns_formulas(alt_patterns: &HashMap<String, i32>, egraph: &mut EGraph<SimpleLanguage, ()>) {
    change_alt_patterns_cost(alt_patterns);
    let num_input_patterns = NUM_PATTERNS.lock().unwrap();
    unsafe {
        let patterns = get_global_patterns_vec();
        for i in 0..*num_input_patterns {
            let pattern = "(Morph (Pi ".to_string() + &i.to_string() + ") " + &patterns[i] + ")";
            let new_expr: RecExpr<SimpleLanguage> = pattern.parse().unwrap(); 
            let new_root = egraph.add_expr(&new_expr);
            let extractor = Extractor::new(&egraph, NaiveCostFunction);
            let (best_cost, best) = extractor.find_best(new_root);
            let best_string = format!("{}", best);
            let map = simplify_pattern_formula(best_string);
            let best_string = pattern_formula_to_string(&map);
            println!();
            println!("Simplified {} to {}", new_expr, best_string);
        }
    }
}

fn print_alt_patterns(patterns: &HashMap<String, i32>, cost: &f64) {
    let mut no_dup_cost = 0.0;
    println!();
    println!("Alternative Patterns Set with Cost {}:", cost);
    unsafe {
        let cost_map = get_global_map();
        for (pattern, count) in patterns {
            println!("{} with number {}", pattern, count);
            no_dup_cost += cost_map.get(pattern).unwrap_or(&0.0);
        }
    }
    println!();
    let formatted = format!("{:.5e}", no_dup_cost);
    print!("Correct Cost is {}", formatted);
}

fn get_edge_set_from_bliss_file(path: String) -> (HashSet<(i32, i32)>, i32) {
    let file = File::open(&path).unwrap();
    let mut edge_set = HashSet::new();
    let reader = BufReader::new(file);
    let mut num_nodes = 0;
    for line in reader.lines() {
        let line = line.unwrap();
        if line.starts_with("p edge") {
            let parts: Vec<&str> = line.split_whitespace().collect();
            num_nodes = parts[2].parse().unwrap();
        }
        if line.starts_with("e") {
            let parts: Vec<&str> = line.split_whitespace().collect();
            let n1: i32 = parts[1].parse().unwrap();
            let n2: i32 = parts[2].parse().unwrap();
            edge_set.insert((n1, n2));
        }
    }
    (edge_set, num_nodes)
} 

fn get_canonical_pattern(index: i32, two_file: bool) -> String {
    let dir_path = &(DIRECTORY_PATH.to_string() + SRC_DIRECTORY);
    let path = dir_path.to_string() + "canonical" + &index.to_string() + ".txt";
    let (edge_set, num_nodes) = get_edge_set_from_bliss_file(path);
    let mut canonical_pattern = "(Match".to_string();
    for i in 1..num_nodes+1 {
        for j in i+1..num_nodes+1 {
            if edge_set.contains(&(i, j)) || edge_set.contains(&(j, i)) {
                let first_node =( (i as u8 + 96) as char).to_string();
                let second_node = ((j as u8 + 96) as char).to_string();
                canonical_pattern += " (-- ";
                canonical_pattern += &first_node;
                canonical_pattern += " ";
                canonical_pattern += &second_node;
                canonical_pattern += ")";
            }
        }
    }
    if two_file {
        let path = dir_path.to_string() + "canonical" + &index.to_string() + &index.to_string() + ".txt";
        let (second_edge_set, _) = get_edge_set_from_bliss_file(path);
        let anti_edge_set: HashSet<(i32, i32)> = second_edge_set.difference(&edge_set).cloned().collect();
        for i in 1..num_nodes+1 {
            for j in i+1..num_nodes+1 {
                if anti_edge_set.contains(&(i, j)) || anti_edge_set.contains(&(j, i)) {
                    let first_node =( (i as u8 + 96) as char).to_string();
                    let second_node = ((j as u8 + 96) as char).to_string();
                    canonical_pattern += " (!- ";
                    canonical_pattern += &first_node;
                    canonical_pattern += " ";
                    canonical_pattern += &second_node;
                    canonical_pattern += ")";
                }
            }
        }
    }
    canonical_pattern += ")";
    canonical_pattern
}

fn collect_anti_edges_numbers(pattern: &str) -> HashSet<(usize, usize)> {
    let mut anti_edges_number = HashSet::new();
    let anti_edges = collect_anti_edges(pattern);
    for (fst, snd) in anti_edges {
        let fst_number = alphabet_to_number(&fst);
        let snd_number = alphabet_to_number(&snd);
        anti_edges_number.insert((fst_number, snd_number));
    }
    anti_edges_number
} 

fn write_input_patterns_to_file(patterns: &Vec<String>, path: &str) -> Vec<(GraphInfo, HashSet<(usize, usize)>)> {
    let mut pattern_infos = vec![];
    let mut index = 0;
    for pattern in patterns {
        let edge_induced_pattern = convert_to_edge_induced_pattern(&pattern.to_string(), false);
        let num_nodes = get_num_nodes(&pattern);
        let pattern_info: GraphInfo = parse_input(&edge_induced_pattern, num_nodes);
        let anti_edges_numbers = collect_anti_edges_numbers(&pattern);
        let bliss_graph = make_graph_file(&pattern_info, true);
        let file_path = path.to_string() + &index.to_string() + ".txt";
        write_to_file(bliss_graph, file_path); 
        index += 1;
        pattern_infos.push((pattern_info, anti_edges_numbers));
    }
    pattern_infos
}

fn read_node_permutation_from_file(file_name: &str) -> HashMap<usize, usize> {
    let mut map = HashMap::new();
    let file = File::open(file_name).unwrap();
    let reader = BufReader::new(file);
    for line in reader.lines() {
        let line = line.unwrap();
        let mut split = line.split_whitespace();
        if let (Some(key), Some(value)) = (split.next(), split.next()) {
            if let (Ok(key), Ok(value)) = (key.parse::<usize>(), value.parse::<usize>()) {
                map.insert(key, value);
            }
        }
    }
    map
}

fn collect_anti_edges(input: &str) -> HashSet<(String, String)> {
    let re = Regex::new(r"!\-\s*(\w+)\s+(\w+)").unwrap();
    let mut result = HashSet::new();
    for cap in re.captures_iter(input) {
        let first = cap[1].to_string();
        let second = cap[2].to_string();
        result.insert((first, second));
    }

    result
}

fn create_permuted_pattern_for_moprh_rule(pattern_info: &(GraphInfo, HashSet<(usize, usize)>), node_permutation: &HashMap<usize, usize>) -> String {
    let original_pattern = &pattern_info.0.graph;
    let anti_edges = &pattern_info.1;
    let mut permuted_pattern = "(Match".to_string();
    for i in 0..original_pattern.len() {
        for j in i+1..original_pattern.len() {
            if anti_edges.contains(&(node_permutation[&i]+1, node_permutation[&j]+1)) || anti_edges.contains(&(node_permutation[&j]+1, node_permutation[&i]+1)) {
                permuted_pattern += " (!- ";
                permuted_pattern += &number_to_alphabet(i+1);
                permuted_pattern += " ";
                permuted_pattern += &number_to_alphabet(j+1);
                permuted_pattern += ")";
            }
            else if original_pattern[node_permutation[&i]][node_permutation[&j]] == 1 {
                permuted_pattern += " (-- ";
                permuted_pattern += &number_to_alphabet(i+1);
                permuted_pattern += " ";
                permuted_pattern += &number_to_alphabet(j+1);
                permuted_pattern += ")";
            }
            else {
                permuted_pattern += " (!- ";
                permuted_pattern += &number_to_alphabet(i+1);
                permuted_pattern += " ";
                permuted_pattern += &number_to_alphabet(j+1);
                permuted_pattern += ")";
            }
        }
    }
    permuted_pattern += ")";
    permuted_pattern
}

fn create_permuted_pattern(pattern_info: &(GraphInfo, HashSet<(usize, usize)>), node_permutation: &HashMap<usize, usize>) -> String {
    let original_pattern = &pattern_info.0.graph;
    let anti_edges = &pattern_info.1;
    let mut permuted_pattern = "(Match".to_string();
    for i in 0..original_pattern.len() {
        for j in i+1..original_pattern.len() {
            if original_pattern[node_permutation[&i]][node_permutation[&j]] == 1 {
                permuted_pattern += " (-- ";
                permuted_pattern += &number_to_alphabet(i+1);
                permuted_pattern += " ";
                permuted_pattern += &number_to_alphabet(j+1);
                permuted_pattern += ")";
            }
            else if anti_edges.contains(&(node_permutation[&i]+1, node_permutation[&j]+1)) || anti_edges.contains(&(node_permutation[&j]+1, node_permutation[&i]+1)) {
                permuted_pattern += " (!- ";
                permuted_pattern += &number_to_alphabet(i+1);
                permuted_pattern += " ";
                permuted_pattern += &number_to_alphabet(j+1);
                permuted_pattern += ")";
            }
        }
    }
    permuted_pattern += ")";
    permuted_pattern
}


fn create_canonical_pattern_from_file(path: &str, pattern_infos: &Vec<(GraphInfo, HashSet<(usize, usize)>)>) -> Vec<String> {
    let mut canonical_patterns = vec![];
    for i in 0..pattern_infos.len() {
        let file_path = path.to_string() + &i.to_string() + ".txt";
        let node_permutation = read_node_permutation_from_file(&file_path);
        let canonical_pattern = create_permuted_pattern(&pattern_infos[i], &node_permutation);
        canonical_patterns.push(canonical_pattern);
    }
    canonical_patterns
}

fn compute_canonical_patterns(patterns: &Vec<String>) -> Vec<String> {
    let path = &(DIRECTORY_PATH.to_string() + SRC_DIRECTORY);
    fs::create_dir(path);
    let pattern_infos = write_input_patterns_to_file(patterns, path);
    write_to_pipe(&BLISS_PIPE_NAME, "start".to_string());
    get_done_signal();
    let canonical_patterns = create_canonical_pattern_from_file(path, &pattern_infos);
    fs::remove_dir_all(DIRECTORY_PATH.to_string() + SRC_DIRECTORY);
    canonical_patterns
}

fn make_patterns_canonical(patterns: &Vec<String>) -> Vec<String> {
    let num_patterns = NUM_PATTERNS.lock().unwrap();
    write_to_pipe(&BLISS_PIPE_NAME, (*num_patterns).to_string());
    compute_canonical_patterns(patterns)
}

fn read_input_patterns_from_file(filename: &str) -> Vec<String> {
    let input = File::open(filename).unwrap();
    let reader = BufReader::new(input);
    let mut patterns = vec![];
    for line in reader.lines() {
        let line = line.unwrap();
        patterns.push(line);
    }
    patterns
}
