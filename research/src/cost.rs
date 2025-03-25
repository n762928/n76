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

pub struct NaiveCostFunction;
impl CostFunction<SimpleLanguage> for NaiveCostFunction {
    type Cost = f64;
    fn cost<C, D>(&mut self, enode: &SimpleLanguage, mut costs: C, get_node: D) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
        D: FnMut(Id) -> SimpleLanguage,
    {
        let node_string = format!("{:?}", enode);
        let index = node_string.find('(').unwrap();
        let node_type = &node_string[..index];
        if node_type == "Match" {
            let pattern = enode.build_recexpr(get_node); 
            let pattern_string = format!("{}", pattern);
            let mut cost = 0.0;
            unsafe {
                let map = get_global_map();
                cost = *map.get(&pattern_string).unwrap();
                
                // println!("{} {}", pattern_string, cost);
            }
            // find_pattern_cost(&format!("{}", pattern));
            return enode.fold(cost, |sum, id| add_f64(sum, costs(id)));
        }
        else if node_type == "Const" {
            let pattern = enode.build_recexpr(get_node); 
            let pattern_string = format!("{}", pattern);
            let (key_word, rest) = pattern_string.split_once(' ').unwrap();
            let (provenance, formula) = parse_const_string(rest.to_string());
            let mut cost = 0.0;
            unsafe {
                let map = get_global_map();
                if map.contains_key(&formula) {
                    cost = *map.get(&formula).unwrap();
                }
            }
            // find_pattern_cost(&format!("{}", pattern));
            return enode.fold(cost, |sum, id| add_f64(sum, costs(id)));
        }
        return enode.fold(0.0, |sum, id| add_f64(sum, costs(id)));
    }
}

fn test_function(rw: &Rewrite<SimpleLanguage, ()>) -> () {
    // println!("hello");
    // let node_string = format!("{:?}", rw);
    // println!("{}", node_string);
    // // let mut var = rewrite!("rule1"; "(Match (-- a b))" => "(Match (-- c c))");
    // // rw = &mut var;
    // println!("{:?}", rw);  
}

fn change_costs() {
    unsafe {
        let map = get_global_map();
        map.insert("(Match p2)".to_string(), 0.0);
        map.insert("(Match p5)".to_string(), 0.0);
        map.insert("(Match p4)".to_string(), 0.0);
    }
}

fn custom_costs() {
    unsafe {
        let map = get_global_map();
        map.insert("(Match p1)".to_string(), 100.0);
        map.insert("(Match p2)".to_string(), 40.0);
        map.insert("(Match p3)".to_string(), 50.0);
        map.insert("(Match p4)".to_string(), 5.0);
        map.insert("(Match p5)".to_string(), 8.0);
    }
}