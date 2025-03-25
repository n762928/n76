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


#[derive(Debug, Clone, PartialEq, Eq)]
struct Morph {
    provenance: Var,
    pattern: Var,
}

impl Applier<SimpleLanguage, ()> for Morph {

    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance_id = subst[self.provenance];
        let provenance = egraph.id_to_expr(provenance_id);
        let provenance_string = format!("{}", provenance);
        let pattern_id = subst[self.pattern];
        let pattern = egraph.id_to_expr(pattern_id);
        let pattern_string = format!("{}", pattern);
        let provenance_pattern_string = provenance_string + " " + &pattern_string;
        if is_in_global_morph_patterns(&provenance_pattern_string) {
            return vec![];
        }
        let edge_induced_pattern = convert_to_edge_induced_pattern(&pattern.to_string(), false);
        let num_nodes = get_num_nodes(&pattern.to_string());
        let pattern_info: GraphInfo = parse_input(&edge_induced_pattern, num_nodes);
        if is_graph_complete(pattern_info.num_edges, pattern_info.graph.len() as i32) {
            return vec![];
        }
        let pattern_string_clone = pattern_string.clone();
        insert_to_global_morph_patterns(pattern_string_clone);
        let new_pattern = generate_morph_rewrite_rule(&pattern_string, &provenance_id, egraph);
        if egraph.union(matched_id, new_pattern) {
            // println!("merged:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

fn parse_union_string(input: String) -> (String, String) {
    let mut num_par = 0;
    let mut left = String::new();
    let mut right = String::new();
    let mut found_left = false;
    let mut right_start_index = 0;
    for (i, c) in input.chars().enumerate() {
        if c == '(' {
            num_par += 1;
        }
        if c == ')' {
            num_par -= 1;
            if num_par == 0 {
                if !found_left {
                    left = input[..i+1].to_string();
                    found_left = true;
                    right_start_index = i;
                }
                else {
                    right = input[right_start_index+2..i+1].to_string();
                    break;
                }
            }
        }
    }
    (left, right)
}

fn parse_count_string(input: String) -> (i32, String) {
    let (num_string, rest) = input.split_once(' ').unwrap();
    let num: i32 = num_string.parse().unwrap();
    let mut rest_string = rest.to_string();
    rest_string.pop();
    (num, rest_string)
}

fn parse_morph_string(input: String) -> (String, String) {
    let first_paren_end = input.find(')').unwrap();
    let second_paren_start = input[first_paren_end + 1..].find('(').unwrap() + first_paren_end + 1;
    let provenance = &input[0..=first_paren_end];
    let pattern = &input[second_paren_start..input.len() - 1];
    (provenance.to_string(), pattern.to_string())
}

fn parse_const_string(input: String) -> (String, String) {
    let mut inside_parentheses = false;
    let mut provenance = String::new();
    let mut formula = String::new();
    
    for c in input.chars() {
        if c == '(' {
            inside_parentheses = true;
        }
        
        if inside_parentheses {
            provenance.push(c);
        } else if !c.is_whitespace() {
            formula.push(c);
        }
        
        if c == ')' {
            inside_parentheses = false;
        }
    }
    formula = formula.trim_end_matches(')').to_string();
    (provenance, formula)
}



fn merge_and_dedup(input: String) -> (HashMap<String, HashMap<String, i32>>) {
    let mut patterns_count_map = HashMap::new();
    let (key_word, rest) = input.split_once(' ').unwrap();
    match key_word {
        "(Union" => {
            let(left, right) = parse_union_string(rest.to_string());
            patterns_count_map = merge_and_dedup(left);
            let second_map = merge_and_dedup(right);
            for (pattern, inner_map) in second_map {
                if !patterns_count_map.contains_key(&pattern) {
                    patterns_count_map.insert(pattern, inner_map);
                    continue;
                }
                for (provenance, num) in inner_map {
                    if patterns_count_map[&pattern].contains_key(&provenance) {
                        *patterns_count_map.get_mut(&pattern).unwrap().get_mut(&provenance).unwrap() += num;
                    }
                    else {
                        patterns_count_map.get_mut(&pattern).unwrap().insert(provenance, num);
                    }
                }
            }
        },
        "(Count" => {
            let (num, right) = parse_count_string(rest.to_string());
            patterns_count_map = merge_and_dedup(right);
            for (key, inner_map) in patterns_count_map.iter_mut() {
                for (provenance, value) in inner_map {
                    *value *= num;
                }
            }
        },
        "(Morph" => {
            let (provenance, pattern) = parse_morph_string(rest.to_string());
            let inner_map = HashMap::from([(provenance, 1)]);
            patterns_count_map.insert(pattern, inner_map);
        },
        "(Const" => {
            let (provenance, formula) = parse_const_string(rest.to_string());
            let inner_map = HashMap::from([(provenance, 1)]);
            patterns_count_map.insert(formula, inner_map);
        },
        _ => {},

    };
    
    patterns_count_map
}


fn create_count_expr(egraph: &mut EGraph<SimpleLanguage, ()>, pattern: &String, provenance: &String, num: &i32, is_const_pattern: bool) -> Id {
    let pattern_rec_expr: RecExpr<SimpleLanguage> = pattern.parse().unwrap();
    let provenance_rec_expr: RecExpr<SimpleLanguage> = provenance.parse().unwrap();
    let pattern_id = egraph.add_expr(&pattern_rec_expr);
    let provenance_id = egraph.add_expr(&provenance_rec_expr);
    let mut morph_const_id = Id::from(0_usize);
    if is_const_pattern {
        morph_const_id = egraph.add(SimpleLanguage::Const([provenance_id, pattern_id]));
    }
    else {
        morph_const_id = egraph.add(SimpleLanguage::Morph([provenance_id, pattern_id]));
    }
    let num_i64 = *num as i64;
    let num_id = egraph.add(SimpleLanguage::Num(num_i64));
    let count_id = egraph.add(SimpleLanguage::Count([num_id, morph_const_id]));
    count_id
}

fn generate_compound_provenance(map: &HashMap<String, i32>) -> (String, i32) {
    let num_patterns = NUM_PATTERNS.lock().unwrap();
    let mut keys = vec![];
    let mut new_count = 0;
    for i in 0..*num_patterns {
        let key = "(Pi ".to_string() + &i.to_string() + ")";
        if map.contains_key(&key) {
            keys.push(i);
            new_count += map.get(&key).unwrap();
        }
    }
    if keys.len() > 1 {
        let mut new_key = "(Pi".to_string();
        for num in keys {
            new_key += " ";
            new_key += &num.to_string();
        }
        new_key += ")";
        (new_key, new_count)
    } else {
        (String::new(), new_count)
    }
}

fn merge_left_right_maps(
    l_map: HashMap<String, HashMap<String, i32>>, 
    r_map: HashMap<String, HashMap<String, i32>>
) -> HashMap<String, HashMap<String, i32>> {
    let mut join_map = l_map.clone();
    for (pattern, inner_map) in r_map {
        if !join_map.contains_key(&pattern) {
            join_map.insert(pattern, inner_map);
            continue;
        }
        for (provenance, num) in inner_map {
            if join_map[&pattern].contains_key(&provenance) {
                *join_map.get_mut(&pattern).unwrap().get_mut(&provenance).unwrap() += num;
            }
            else {
                join_map.get_mut(&pattern).unwrap().insert(provenance, num);
            }
        }
    }
    let mut final_map = HashMap::new();
    for (key, inner_map) in join_map {
        let (new_provenance, new_count) = generate_compound_provenance(&inner_map);
        if new_provenance != "" {
            let new_inner_map = HashMap::from([(new_provenance, new_count)]);
            final_map.insert(key, new_inner_map);
            continue;
        }
        final_map.insert(key, inner_map);
    }
    final_map
}

fn is_coumpound_provenance(provenance: &String) -> bool {
    let trimmed = provenance.trim_matches(|c| c == '(' || c == ')').trim();
    let arg_count = trimmed.split_whitespace().count();
    arg_count > 2
}

fn create_final_union_node_from_map(egraph: &mut EGraph<SimpleLanguage, ()>, map: &HashMap<String, HashMap<String, i32>>) -> (bool, Id) {
    let mut iteration = 0;
    let mut id = Id::from(0_usize);
    for (pattern, inner_map) in map {
        for (provenance, num) in inner_map {
            if *num == 0 && !is_coumpound_provenance(provenance) {
                continue;
            }
            let mut count_id = Id::from(0_usize);
            if pattern.chars().next().unwrap() == 'F' {
                count_id = create_count_expr(egraph, pattern, provenance, num, true);
            }
            else {
                count_id = create_count_expr(egraph, pattern, provenance, num, false);
            }
            if iteration == 0 {
                id = count_id;
            }
            else {
                id = egraph.add(SimpleLanguage::Union([count_id, id]));
            }
            iteration += 1;
        }
    }
    if iteration == 0 {
        (false, id)
    }
    else {
        (true, id)
    }
}
