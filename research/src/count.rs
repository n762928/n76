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
struct Count {
    num: Var, 
    l: Var,
    r: Var,
}

impl Applier<SimpleLanguage, ()> for Count {

    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let num_id = subst[self.num];
        let l_id = subst[self.l];
        let r_id = subst[self.r];
        let l_pattern = egraph.id_to_expr(l_id);
        let l_string = format!("{}", l_pattern);
        let r_pattern = egraph.id_to_expr(r_id);
        let r_string = format!("{}", r_pattern);
        let num_pattern = egraph.id_to_expr(num_id);
        let num_string = format!("{}", num_pattern);
        let num: i32 = num_string.parse().unwrap();
        let l_result = dist_count(l_string, num);
        let r_result = dist_count(r_string, num);
        let new_l_id = egraph.add_expr(&l_result);
        let new_r_id = egraph.add_expr(&r_result);
        let new_id = egraph.add(SimpleLanguage::Union([new_l_id, new_r_id]));
        if egraph.union(matched_id, new_id) {
            println!("merged in count:");
            println!("{}", egraph.id_to_expr(matched_id));
            println!("{}", egraph.id_to_expr(new_id));
            println!();
            vec![new_id]
        } else {
            vec![]
        }
    }
      
}


pub fn add_f64(a: f64, b: f64) -> f64 {
    a + b
}
