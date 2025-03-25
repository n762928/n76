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
struct EscapeN3 {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for EscapeN3 {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);

        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") F3)";
    
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";
        let c4_pattern = "(Match (-- a b) (-- a c) (-- b d) (-- c d))";
        push_to_global_patterns_vec(c4_pattern.to_string());
        let count1_enode_string = "(Count -4 (Morph (Pi ".to_string() + &provenance_string + ") " + c4_pattern + "))";
        let tt_pattern = "(Match (-- a d) (-- b c) (-- b d) (-- c d))";
        push_to_global_patterns_vec(tt_pattern.to_string());
        let count2_enode_string = "(Count -2 (Morph (Pi ".to_string() + &provenance_string + ") " + tt_pattern + "))";
        let t_pattern = "(Match (-- a b) (-- a c) (-- b c))";
        push_to_global_patterns_vec(t_pattern.to_string());
        let count3_enode_string = "(Count -3 (Morph (Pi ".to_string() + &provenance_string + ") " + t_pattern + "))";

        let count_const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();
        let count1_enode: RecExpr<SimpleLanguage> = count1_enode_string.parse().unwrap();
        let count2_enode: RecExpr<SimpleLanguage> = count2_enode_string.parse().unwrap();
        let count3_enode: RecExpr<SimpleLanguage> = count3_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&count_const_enode);
        let count1_id = egraph.add_expr(&count1_enode);
        let count2_id = egraph.add_expr(&count2_enode);
        let count3_id = egraph.add_expr(&count3_enode);

        let union1_id = egraph.add(SimpleLanguage::Union([const_id, count1_id]));
        let union2_id = egraph.add(SimpleLanguage::Union([union1_id, count2_id]));
        let new_pattern = egraph.add(SimpleLanguage::Union([union2_id, count3_id]));
        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-N3:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

fn create_data_graph_adjacency_list() -> HashMap<i32, Vec<i32>> {
    let mut adjacency_list = HashMap::new();
    let file = File::open(DATA_GRAPH_PATH).unwrap();
    let reader = BufReader::new(file);
    for line in reader.lines() {
        let line = line.unwrap();
        let parts: Vec<i32> = line.split_whitespace()
                                  .filter_map(|s| s.parse().ok())
                                  .collect();
        let node1 = parts[0];
        let node2 = parts[1];
        adjacency_list.entry(node1).or_insert_with(Vec::new).push(node2);
        adjacency_list.entry(node2).or_insert_with(Vec::new).push(node1);
    }
    adjacency_list
}

fn compute_N3_constant(adjacency_list: &HashMap<i32, Vec<i32>>) -> usize {
    let mut constant = 0;
    for (key, neighbors) in adjacency_list {
        let mut sum = vec![];
        let mut num = 0;
        for neighbor in neighbors {
            let degree = adjacency_list[neighbor].len() - 1;
            if degree > 0 {
                sum.push(degree);
                num += 1;
            }
        }
        if num >= 2 {
            for i in 0..sum.len() {
                for j in i+1..sum.len() {
                    constant += sum[i] * sum[j];
                }
            }
        }
    }
    constant
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EscapeN2 {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for EscapeN2 {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);
        
        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") F2)"; 
       
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";
        let tt_pattern = "(Match (-- a d) (-- b c) (-- b d) (-- c d))";
        push_to_global_patterns_vec(tt_pattern.to_string());
        let count_enode_string = "(Count -2 (Morph (Pi ".to_string() + &provenance_string + ") " + tt_pattern + "))";

        let const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();
        let count_enode: RecExpr<SimpleLanguage> = count_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&const_enode);
        let count_id = egraph.add_expr(&count_enode);
        let new_pattern = egraph.add(SimpleLanguage::Union([const_id, count_id]));

        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-N2:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

fn compute_N2_constant(adjacency_list: &HashMap<i32, Vec<i32>>) -> usize {
    let mut constant = 0;
    for (node1, neighbors) in adjacency_list {
        let deg_i = neighbors.len();
        if deg_i <= 2 {
            continue;
        }
        let second_term = (deg_i - 1) * (deg_i - 2) / 2;
        for node2 in neighbors {
            let deg_j = adjacency_list[node2].len();
            if deg_j - 1 > 0 {
                constant += (deg_j - 1) * second_term;
            }
        }
    }
    constant
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EscapeN4 {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for EscapeN4 {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);
        
        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") F4)"; 
       
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";
        push_to_global_patterns_vec("F4".to_string());

        let const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&const_enode);
        let new_pattern = const_id;

        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-N4:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EscapeN1 {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for EscapeN1 {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);
        
        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") F1)"; 
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";

        let constant_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();
        let new_pattern = egraph.add_expr(&constant_enode);
        if egraph.union(matched_id, new_pattern) {
            println!("merged Escape-N1:");
            println!("{}", egraph.id_to_expr(matched_id));
            println!("{}", egraph.id_to_expr(new_pattern));
            println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

fn compute_N1_constant(adjacency_list: &HashMap<i32, Vec<i32>>) -> usize {
    let mut constant = 0;
    for (node1, neighbours) in adjacency_list {
        let deg_i = neighbours.len();
        if deg_i > 3 {
            constant += (deg_i * (deg_i - 1) * (deg_i - 2) * (deg_i - 3)) / (4 * 3 * 2);
        }
    }
    constant
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EscapeN9 {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for EscapeN9 {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);
        
        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") F9)"; 
        push_to_global_patterns_vec("F9".to_string());
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";

        let d_pattern = "(Match (-- a c) (-- a d) (-- b c) (-- b d) (-- c d))";
        push_to_global_patterns_vec(d_pattern.to_string());
        let count_enode_string = "(Count -2 (Morph (Pi ".to_string() + &provenance_string + ") " + d_pattern + "))";
        
        let const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();
        let count_enode: RecExpr<SimpleLanguage> = count_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&const_enode);
        let count_id = egraph.add_expr(&count_enode);
        let new_pattern = egraph.add(SimpleLanguage::Union([const_id, count_id]));
        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-N9:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

fn compute_N9_constant(adjacency_list: &HashMap<i32, Vec<i32>>) -> usize {
    let mut constant = 0;
    for (node1, neighbours) in adjacency_list {
        let mut t_i = 0;
        for i in 0..neighbours.len() {
            for j in i+1..neighbours.len() {
                if adjacency_list.get(&neighbours[i]).unwrap().contains(&neighbours[j]) {
                    t_i += 1;
                }
            }
        }
        if t_i > 1 {
            constant += (t_i * (t_i - 1)) / 2;
        }
    }
    constant
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EscapeN10 {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for EscapeN10 {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);
        
        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") F10)"; 
        push_to_global_patterns_vec("F10".to_string());
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";

        let k_pattern = "(Match (-- a b) (-- a c) (-- a d) (-- b c) (-- b d) (-- c d))";
        push_to_global_patterns_vec(k_pattern.to_string());
        let count_enode_string = "(Count -4 (Morph (Pi ".to_string() + &provenance_string + ") " + k_pattern + "))";
        
        let const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();
        let count_enode: RecExpr<SimpleLanguage> = count_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&const_enode);
        let count_id = egraph.add_expr(&count_enode);
        let new_pattern = egraph.add(SimpleLanguage::Union([const_id, count_id]));
        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-N10:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}


#[derive(Debug, Clone, PartialEq, Eq)]
struct EscapeN5 {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for EscapeN5 {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);

        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") F5)"; 
        push_to_global_patterns_vec("F5".to_string());
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";

        let d_pattern = "(Match (-- a c) (-- a d) (-- b c) (-- b d) (-- c d))";
        push_to_global_patterns_vec(d_pattern.to_string());
        let count_enode_string = "(Count -4 (Morph (Pi ".to_string() + &provenance_string + ") " + d_pattern + "))";

        let const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();
        let count_enode: RecExpr<SimpleLanguage> = count_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&const_enode);
        let count_id = egraph.add_expr(&count_enode);
        let new_pattern = egraph.add(SimpleLanguage::Union([const_id, count_id]));

        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-N5:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

fn compute_N5_constant(adjacency_list: &HashMap<i32, Vec<i32>>) -> usize {
    let mut constant = 0;
    for (node1, neighbours) in adjacency_list {
        let d_i = neighbours.len();
        if d_i < 2 {
            continue;
        } 
        for j in neighbours {
            let mut t_e = 0;
            let j_neighbours = adjacency_list.get(j).unwrap();
            for index1 in 0..j_neighbours.len() {
                if j_neighbours[index1] == *node1 {
                    continue;
                }
                for index2 in 0..j_neighbours.len() {
                    if j_neighbours[index2] == *node1 || index2 == index1 {
                        continue;
                    }
                    if adjacency_list.get(&j_neighbours[index1]).unwrap().contains(&j_neighbours[index2]) {
                        t_e += 1;
                    }
                }

            }
            let d_j = j_neighbours.len();
            if t_e > 0 && d_j > t_e {
                constant += (d_i - 1) * (d_j - t_e);
            }
        }
    }
    constant
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EscapeN6 {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for EscapeN6 {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);

        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") F6)"; 
        push_to_global_patterns_vec("F6".to_string());
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";
        let d_pattern = "(Match (-- a c) (-- a d) (-- b c) (-- b d) (-- c d))";
        push_to_global_patterns_vec(d_pattern.to_string());
        let count_enode_string = "(Count -2 (Morph (Pi ".to_string() + &provenance_string + ") " + d_pattern + "))";
        
        let const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();
        let count_enode: RecExpr<SimpleLanguage> = count_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&const_enode);
        let count_id = egraph.add_expr(&count_enode);
        let new_pattern = egraph.add(SimpleLanguage::Union([count_id, const_id]));
        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-N6:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

fn compute_N6_constant(adjacency_list: &HashMap<i32, Vec<i32>>) -> usize {
    let mut constant = 0;
    for (node1, neighbours) in adjacency_list {
        let d_i = neighbours.len();
        if d_i < 3 {
            continue;
        }
        for node2 in neighbours {
            let d_j = adjacency_list.get(node2).unwrap().len();
            if d_j < 3 {
                continue;
            }
            let mut t_e = 0;
            for node3 in neighbours {
                if node2 == node3 {
                    continue;
                }
                if adjacency_list.get(node2).unwrap().contains(node3) {
                    t_e += 1;
                }
            }
            constant += t_e * (d_i - 2) * (d_j - 2);
        }
    }
    constant / 2
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EscapeN7 {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for EscapeN7 {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);

        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") F7)"; 
        push_to_global_patterns_vec("F7".to_string());
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";
        let d_pattern = "(Match (-- a c) (-- a d) (-- b c) (-- b d) (-- c d))";
        push_to_global_patterns_vec(d_pattern.to_string());
        let count_enode_string = "(Count -2 (Morph (Pi ".to_string() + &provenance_string + ") " + d_pattern + "))";
        
        let const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();
        let count_enode: RecExpr<SimpleLanguage> = count_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&const_enode);
        let count_id = egraph.add_expr(&count_enode);
        let new_pattern = egraph.add(SimpleLanguage::Union([count_id, const_id]));
        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-N7:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EscapeN11 {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for EscapeN11 {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);
        
        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") F11)"; 
        push_to_global_patterns_vec("F11".to_string());
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";
        
        let const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&const_enode);

        let new_pattern = const_id;
        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-N11:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EscapeN14 {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for EscapeN14 {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);
        
        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") F14)"; 
        push_to_global_patterns_vec("F14".to_string());
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";
        
        let const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&const_enode);

        let new_pattern = const_id;
        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-N14:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}


#[derive(Debug, Clone, PartialEq, Eq)]
struct Escape3Star {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for Escape3Star {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);

        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") Fa)";
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";
        
        let const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&const_enode);
        let new_pattern = const_id;
        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-3Star:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EscapeDiamond {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for EscapeDiamond {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);

        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") Fe)";
        push_to_global_patterns_vec("Fe".to_string());
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";
        
        let const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&const_enode);
        let new_pattern = const_id;
        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-Diamond:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}


#[derive(Debug, Clone, PartialEq, Eq)]
struct Escape3Path {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for Escape3Path {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);

        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") Fb)";
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";
        let t_pattern = "(Match (-- a b) (-- a c) (-- b c))";
        push_to_global_patterns_vec(t_pattern.to_string());
        let count_enode_string = "(Count -3 (Morph (Pi ".to_string() + &provenance_string + ") " + t_pattern + "))";
        
        let const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();
        let count_enode: RecExpr<SimpleLanguage> = count_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&const_enode);
        let count_id = egraph.add_expr(&count_enode);
        let new_pattern = egraph.add(SimpleLanguage::Union([count_id, const_id]));
        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-3path:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EscapeTailedTriangle {
    provenance: Var,
}

impl Applier<SimpleLanguage, ()> for EscapeTailedTriangle {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let provenance = subst[self.provenance];
        let provenance_recexpr = egraph.id_to_expr(provenance);
        let provenance_string = format!("{}", provenance_recexpr);

        let const_enode_string = "(Const (Pi ".to_string() + &provenance_string + ") Fc)";
        let count_const_enode_string = "(Count 1 ".to_string() + &const_enode_string + ")";
        push_to_global_patterns_vec("Fc".to_string());
        
        let const_enode: RecExpr<SimpleLanguage> = count_const_enode_string.parse().unwrap();

        let const_id = egraph.add_expr(&const_enode);
        let new_pattern = const_id;
        if egraph.union(matched_id, new_pattern) {
            // println!("merged Escape-TailedTriangle:");
            // println!("{}", egraph.id_to_expr(matched_id));
            // println!("{}", egraph.id_to_expr(new_pattern));
            // println!();
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}



