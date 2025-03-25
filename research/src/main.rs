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

mod count;
mod cost;
mod utils;
mod morph;
mod escape;
mod union;

use crate::count::*;
use crate::cost::*;
use crate::utils::*;
use crate::morph::*;
use crate::escape::*;
use crate::union::*;

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

struct GlobalMapWrapper(UnsafeCell<HashMap<String, f64>>);
struct GlobalVecWrapper(UnsafeCell<Vec<String>>);
struct GlobalSetWrapper(UnsafeCell<HashSet<String>>);

unsafe impl Sync for GlobalVecWrapper {}
unsafe impl Sync for GlobalMapWrapper {}
unsafe impl Sync for GlobalSetWrapper {}

// Step 3: Use the wrapper type in lazy_static!
lazy_static! {
    static ref GLOBAL_MAP: GlobalMapWrapper = GlobalMapWrapper(UnsafeCell::new(HashMap::new()));
    static ref GLOBAL_Patterns_VEC: GlobalVecWrapper = GlobalVecWrapper(UnsafeCell::new(Vec::new()));
    static ref GLOBAL_Morph_Patterns: GlobalSetWrapper = GlobalSetWrapper(UnsafeCell::new(HashSet::new()));
}

// Unsafe function to get mutable reference to the global map
unsafe fn get_global_map() -> &'static mut HashMap<String, f64> {
    &mut *GLOBAL_MAP.0.get()
}

unsafe fn get_global_patterns_vec() -> &'static mut Vec<String> {
    &mut *GLOBAL_Patterns_VEC.0.get()
}

fn push_to_global_patterns_vec(value: String) {
    unsafe {
        let map = get_global_map();
        if !map.contains_key(&value) {
            let vec = get_global_patterns_vec();
            vec.push(value.clone());
            map.insert(value, 0.0);
        }
    }
}

unsafe fn get_global_morph_patterns() -> &'static mut HashSet<String> {
    &mut *GLOBAL_Morph_Patterns.0.get()
}

fn insert_to_global_morph_patterns(value: String) {
    unsafe {
        let set = get_global_morph_patterns();
        set.insert(value);
    }
}

fn is_in_global_morph_patterns(value: &String) -> bool {
    unsafe {
        let set = get_global_morph_patterns();
        set.contains(value)
    }
}




define_language! {
    enum SimpleLanguage {
        "--" = Edge([Id; 2]),
        "!-" = AntiEdge([Id; 2]),
        "<>" = NotEqual([Id; 2]),
        "Match" = Match(Box<[Id]>),
        "Union" = Union([Id; 2]),
        "Count" = Count([Id; 2]),
        "Morph" = Morph([Id; 2]),
        "Pi" = Pi(Box<[Id]>),
        "Const" = Const([Id; 2]),
        Num(i64),
        Symbol(Symbol),
    }
}


fn get_static_rewrite_rules() -> Vec<Rewrite<SimpleLanguage, ()>> {
    vec![
        rewrite!("escape-3star"; "(Morph (Pi ?provenance) (Match (-- a d) (-- b d) (-- c d)))" => {Escape3Star {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("escape-diamond"; "(Morph (Pi ?provenance) (Match (-- a c) (-- a d) (-- b c) (-- b d) (-- c d)))" => {EscapeDiamond {
            provenance: "?provenance".parse().unwrap(),
        }}),

        rewrite!("escape-3path"; "(Morph (Pi ?provenance) (Match (-- a c) (-- b d) (-- c d)))" => {Escape3Path {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("escape-tailed_triangle"; "(Morph (Pi ?provenance) (Match (-- a d) (-- b c) (-- b d) (-- c d)))" => {EscapeTailedTriangle {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("escape-N1"; "(Morph (Pi ?provenance) (Match (-- a e) (-- b e) (-- c e) (-- d e)))" => {EscapeN1 {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("escape-N2"; "(Morph (Pi ?provenance) (Match (-- a d) (-- b e) (-- c e) (-- d e)))" => {EscapeN2 {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("escape-N3"; "(Morph (Pi ?provenance) (Match (-- a d) (-- b e) (-- c d) (-- c e)))" => {EscapeN3 {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("escape-N4"; "(Morph (Pi ?provenance) (Match (-- a e) (-- b e) (-- c d) (-- c e) (-- d e)))" => {EscapeN4 {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("escape-N5"; "(Morph (Pi ?provenance) (Match (-- a d) (-- b c) (-- b e) (-- c e) (-- d e)))" => {EscapeN5 {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("escape-N6"; "(Morph (Pi ?provenance) (Match (-- a d) (-- b e) (-- c d) (-- c e) (-- d e)))" => {EscapeN6 {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("escape-N7"; "(Morph (Pi ?provenance) (Match (-- a e) (-- b c) (-- b d) (-- c e) (-- d e)))" => {EscapeN7 {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("escape-N9"; "(Morph (Pi ?provenance) (Match (-- a b) (-- a e) (-- b e) (-- c d) (-- c e) (-- d e)))" => {EscapeN9 {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("escape-N10"; "(Morph (Pi ?provenance) (Match (-- a c) (-- b d) (-- b e) (-- c d) (-- c e) (-- d e)))" => {EscapeN10 {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("escape-N11"; "(Morph (Pi ?provenance) (Match (-- a e) (-- b d) (-- b e) (-- c d) (-- c e) (-- d e)))" => {EscapeN11 {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("escape-N14"; "(Morph (Pi ?provenance) (Match (-- a d) (-- a e) (-- b d) (-- b e) (-- c d) (-- c e) (-- d e)))" => {EscapeN14 {
            provenance: "?provenance".parse().unwrap(),
        }}),
        rewrite!("morph"; "(Morph ?provenance ?pattern)" => { Morph {
            provenance: "?provenance".parse().unwrap(),
            pattern: "?pattern".parse().unwrap(),
        }}),
        rewrite!("union_switch"; "(Union ?a ?b)" => "(Union ?b ?a)"),
        rewrite!("union_dist"; "(Union ?a (Union ?b ?c))" => "(Union (Union ?a ?b) ?c)"),

        // rewrite!("union"; "(Union ?l ?r)" => { Union {
        //     l: "?l".parse().unwrap(),
        //     r: "?r".parse().unwrap(),
        // }}),
        // rewrite!("count"; "(Count ?num (Union ?l ?r))" => { Count {
        //     num: "?num".parse().unwrap(),
        //     l: "?l".parse().unwrap(),
        //     r: "?r".parse().unwrap(),
        // }}),

        rewrite!("union_dedup_prov_dif"; "(Union (Count ?num1 (Morph ?pi1 ?pat)) (Count ?num2 (Morph ?pi2 ?pat)))" => { UnionDedupDiff {
            provenance1: "?pi1".parse().unwrap(),
            provenance2: "?pi2".parse().unwrap(),
            num1: "?num1".parse().unwrap(),
            num2: "?num2".parse().unwrap(),
            pattern: "?pat".parse().unwrap(),
        }}),
        rewrite!("union_dedup_const"; "(Union (Count ?num1 (Const ?pi1 ?f)) (Count ?num2 (Const ?pi2 ?f)))" => { UnionDedupConst {
            provenance1: "?pi1".parse().unwrap(),
            provenance2: "?pi2".parse().unwrap(),
            num1: "?num1".parse().unwrap(),
            num2: "?num2".parse().unwrap(),
            formula: "?f".parse().unwrap(),
        }}),
        rewrite!("count_dist"; "(Count ?num (Union ?l ?r))" => "(Union (Count ?num ?l) (Count ?num ?r))"),
        rewrite!("count_mult"; "(Count ?num1 (Count ?num2 ?rest))" => { CountMult {
            num1: "?num1".parse().unwrap(),
            num2: "?num2".parse().unwrap(),
            rest: "?rest".parse().unwrap(),
        }}),
    ]
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CountMult {
    num1: Var,
    num2: Var,
    rest: Var,
}

impl Applier<SimpleLanguage, ()> for CountMult {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let num1 = subst[self.num1];
        let num2 = subst[self.num2];
        let rest = subst[self.rest];

        let num1_recexpr = egraph.id_to_expr(num1);
        let num2_recexpr = egraph.id_to_expr(num2);
        let num1_string = format!("{}", num1_recexpr);
        let num2_string = format!("{}", num2_recexpr);
        let num1_i32: i64 = num1_string.parse().unwrap();
        let num2_i32: i64 = num2_string.parse().unwrap();
        let new_num = num1_i32.checked_mul(num2_i32).unwrap_or(i64::MAX);
        if new_num == i64::MAX {
            return vec![];
        }
        let new_num_id = egraph.add(SimpleLanguage::Num(new_num));
        let count_id = egraph.add(SimpleLanguage::Count([new_num_id, rest]));
        let new_pattern = count_id;
        if egraph.union(matched_id, new_pattern) {
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}


#[derive(Debug, Clone, PartialEq, Eq)]
struct UnionDedupDiff {
    provenance1: Var,
    provenance2: Var,
    num1: Var,
    num2: Var,
    pattern: Var,
}

impl Applier<SimpleLanguage, ()> for UnionDedupDiff {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let num1 = subst[self.num1];
        let num2 = subst[self.num2];
        let pattern = subst[self.pattern];
        let provenance1 = subst[self.provenance1];
        let provenance2 = subst[self.provenance2];

        let provenance1_recexpr = egraph.id_to_expr(provenance1);
        let provenance2_recexpr = egraph.id_to_expr(provenance2);
        let provenance1_string = format!("{}", provenance1_recexpr);
        let provenance2_string = format!("{}", provenance2_recexpr);
        let num1_recexpr = egraph.id_to_expr(num1);
        let num2_recexpr = egraph.id_to_expr(num2);
        let num1_string = format!("{}", num1_recexpr);
        let num2_string = format!("{}", num2_recexpr);
        let num1_i32: i64 = num1_string.parse().unwrap();
        let num2_i32: i64 = num2_string.parse().unwrap();
        let new_num = num1_i32.checked_add(num2_i32).unwrap_or(i64::MAX);
        if new_num == i64::MAX {
            return vec![];
        }
        let new_num_id = egraph.add(SimpleLanguage::Num(new_num as i64));
        let mut provenance_id = Id::from(0_usize);

        if provenance1_string == provenance2_string {
            provenance_id = provenance1;
            if new_num == 0 {
                let formula_string = "F0";
                let formula_enode: RecExpr<SimpleLanguage> = formula_string.parse().unwrap();
                let formula = egraph.add_expr(&formula_enode);
                let const_id =  egraph.add(SimpleLanguage::Const([provenance_id, formula]));
                let new_num = 1;
                let new_num_id = egraph.add(SimpleLanguage::Num(new_num as i64));
                let count_id = egraph.add(SimpleLanguage::Count([new_num_id, const_id]));
                let new_pattern = count_id;
                if egraph.union(matched_id, new_pattern) {
                    // println!("merged in union:");
                    // println!("{}", egraph.id_to_expr(matched_id));
                    // println!("{}", egraph.id_to_expr(new_pattern));
                    // println!();
                    return vec![new_pattern]
                } else {
                    return vec![]
                }
            }
        }
        else {
            let provenances_string = get_merged_provenance(&provenance1_string, &provenance2_string);
            let final_provenance_string = "(Pi ".to_string() + &provenances_string + ")";
            let final_provenance_recexpr: RecExpr<SimpleLanguage> = final_provenance_string.parse().unwrap();
            provenance_id = egraph.add_expr(&final_provenance_recexpr);
        }
        let morph_id = egraph.add(SimpleLanguage::Morph([provenance_id, pattern]));
        let count_id = egraph.add(SimpleLanguage::Count([new_num_id, morph_id]));
        let new_pattern = count_id;
        if egraph.union(matched_id, new_pattern) {
            // println!("merged in union:");
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
struct UnionDedupConst {
    provenance1: Var,
    provenance2: Var,
    num1: Var,
    num2: Var,
    formula: Var,
}

impl Applier<SimpleLanguage, ()> for UnionDedupConst {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let num1 = subst[self.num1];
        let num2 = subst[self.num2];
        let formula = subst[self.formula];
        let provenance1 = subst[self.provenance1];
        let provenance2 = subst[self.provenance2];

        let provenance1_recexpr = egraph.id_to_expr(provenance1);
        let provenance2_recexpr = egraph.id_to_expr(provenance2);
        let provenance1_string = format!("{}", provenance1_recexpr);
        let provenance2_string = format!("{}", provenance2_recexpr);
        let num1_recexpr = egraph.id_to_expr(num1);
        let num2_recexpr = egraph.id_to_expr(num2);
        let num1_string = format!("{}", num1_recexpr);
        let num2_string = format!("{}", num2_recexpr);
        let num1_i32: i32 = num1_string.parse().unwrap_or(i32::MAX);
        let num2_i32: i32 = num2_string.parse().unwrap_or(i32::MAX);
        let new_num = num1_i32.checked_add(num2_i32).unwrap_or(i32::MAX);
        let new_num_id = egraph.add(SimpleLanguage::Num(new_num as i64));
        let mut provenance_id = Id::from(0_usize);

        if provenance1_string == provenance2_string {
            provenance_id = provenance1;
            if new_num == 0 {
                let formula_string = "F0";
                let formula_enode: RecExpr<SimpleLanguage> = formula_string.parse().unwrap();
                let formula = egraph.add_expr(&formula_enode);
                let const_id =  egraph.add(SimpleLanguage::Const([provenance_id, formula]));
                let new_num = 1;
                let new_num_id = egraph.add(SimpleLanguage::Num(new_num as i64));
                let count_id = egraph.add(SimpleLanguage::Count([new_num_id, const_id]));
                let new_pattern = count_id;
                if egraph.union(matched_id, new_pattern) {
                    // println!("merged in union:");
                    // println!("{}", egraph.id_to_expr(matched_id));
                    // println!("{}", egraph.id_to_expr(new_pattern));
                    // println!();
                    return vec![new_pattern]
                } else {
                    return vec![]
                }
            }
        }
        else {
            let provenances_string = get_merged_provenance(&provenance1_string, &provenance2_string);
            let final_provenance_string = "(Pi ".to_string() + &provenances_string + ")";
            let final_provenance_recexpr: RecExpr<SimpleLanguage> = final_provenance_string.parse().unwrap();
            provenance_id = egraph.add_expr(&final_provenance_recexpr);
        }
        let const_id = egraph.add(SimpleLanguage::Const([provenance_id, formula]));
        let count_id = egraph.add(SimpleLanguage::Count([new_num_id, const_id]));
        let new_pattern = count_id;
        if egraph.union(matched_id, new_pattern) {
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

fn process_string(s: &str) -> Vec<i32> {
    // Step 1 & 2: Remove the first 4 characters and the last character
    let trimmed = &s[4..s.len()-1];

    // Step 3: Split by whitespace and convert to numbers
    trimmed
        .split_whitespace()   // split into parts by whitespace
        .map(|x| x.parse::<i32>().unwrap())  // parse each part as an integer
        .collect()
}

fn get_merged_provenance(p1: &str, p2: &str) -> String {
    let mut numbers: Vec<i32> = process_string(p1);
    numbers.extend(process_string(p2));
    let unique_numbers: HashSet<_> = numbers.into_iter().collect(); // Remove duplicates
    let mut sorted_numbers: Vec<_> = unique_numbers.into_iter().collect(); // Convert back to Vec
    sorted_numbers.sort(); // Sort the numbers
    sorted_numbers.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(" ")
}
 

struct Union_Dedup {
    num1: Var,
    num2: Var,
    provenance: Var,
    pattern: Var,
}

impl Applier<SimpleLanguage, ()> for Union_Dedup {
    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let num1 = subst[self.num1];
        let num2 = subst[self.num2];
        let pattern = subst[self.pattern];
        let provenance = subst[self.provenance];

        let num1_recexpr = egraph.id_to_expr(num1);
        let num2_recexpr = egraph.id_to_expr(num2);
        let num1_string = format!("{}", num1_recexpr);
        let num2_string = format!("{}", num2_recexpr);
        let num1_i32: i32 = num1_string.parse().unwrap();
        let num2_i32: i32 = num2_string.parse().unwrap();
        let new_num = num1_i32 + num2_i32;
        let new_num_id = egraph.add(SimpleLanguage::Num(new_num as i64));

        let provenance_id = egraph.add(SimpleLanguage::Pi(Box::new([provenance])));
        let morph_id = egraph.add(SimpleLanguage::Morph([provenance_id, pattern]));
        let count_id = egraph.add(SimpleLanguage::Count([new_num_id, morph_id]));
        let new_pattern = count_id;
        if egraph.union(matched_id, new_pattern) {
            vec![new_pattern]
        } else {
            vec![]
        }
    }   
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let patterns = read_input_patterns_from_file(&args[1]);
    fs::create_dir(DIRECTORY_PATH);
    create_pipes();
    initialize_num_patterns(patterns.len());
    let canonical_patterns = make_patterns_canonical(&patterns);
    // let canonical_patterns = patterns;
    let mut s = String::new();
    let provenance = 0;
    for i in 0..patterns.len() {
        let pattern = "(Count 1 (Morph ".to_string() + "(Pi " + &i.to_string() + ") " + &canonical_patterns[i] + "))";
        // let pattern = "(Count 1 (Morph ".to_string() + "(Pi " + &provenance.to_string() + ") " + &canonical_patterns[i] + "))";
        push_to_global_patterns_vec(canonical_patterns[i].to_string());
        if i == 0 {
            s = pattern;
            continue;
        }
        s = "(Union ".to_string() + &s + " " + &pattern + ")";
    }
    println!("{}", s);
    let start = Instant::now();
    let (alt_patterns_string, optimized_cost, mut egraph) = simplify(&s, vec![]);
    // println!("alternative patterns {}", alt_patterns_string);
    let end = Instant::now();
    println!("generation time: {}", (end - start).as_secs());
    write_to_pipe(BLISS_PIPE_NAME, "done".to_string());
    let alt_patterns = parse_alt_patterns_string(alt_patterns_string);
    print_alt_patterns(&alt_patterns, &optimized_cost);
    get_patterns_formulas(&alt_patterns, &mut egraph);
    fs::remove_dir_all(DIRECTORY_PATH.to_string() + COST_DIRECTORY);
}

