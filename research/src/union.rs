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
struct Union {
    l: Var,
    r: Var,
}

impl Applier<SimpleLanguage, ()> for Union {

    fn apply_one(&self, egraph: &mut EGraph<SimpleLanguage, ()>, matched_id: Id, subst: &Subst, searcher_pattern: Option<&PatternAst<SimpleLanguage>>, rule_name: Symbol) -> Vec<Id> {
        let l_id = subst[self.l];
        let r_id = subst[self.r];
        let l_pattern = egraph.id_to_expr(l_id);
        let l_string = format!("{}", l_pattern);
        let r_pattern = egraph.id_to_expr(r_id);
        let r_string = format!("{}", r_pattern);
        let l_map = merge_and_dedup(l_string);
        let r_map = merge_and_dedup(r_string);
        let final_map = merge_left_right_maps(l_map, r_map);
        let (can_merge, new_id) = create_final_union_node_from_map(egraph, &final_map);
        if !can_merge {
            return vec![];
        }
        if egraph.union(matched_id, new_id) {
            println!("merged in union:");
            println!("{}", egraph.id_to_expr(matched_id));
            println!("{}", egraph.id_to_expr(new_id));
            println!();
            vec![new_id]
        } else {
            vec![]
        }
    }
      
}

fn dist_count(input: String, num: i32) -> RecExpr<SimpleLanguage> {
    let mut output = String::new();
    let (key_word, rest) = input.split_once(' ').unwrap();
    match key_word {
        "(Union" => {
            let (l, r) = parse_union_string(rest.to_string());
            let new_l = "(Count ".to_string() + &num.to_string() + " " + &l + ")";
            let new_r = "(Count ".to_string() + &num.to_string() + " " + &r + ")";
            output = "(Union ".to_string() + &new_l + " " + &new_r + ")";
        },
        "(Count" => {
            let (prev_num, right) = parse_count_string(rest.to_string());
            let new_num = num * prev_num;
            output = "(Count ".to_string() + &new_num.to_string() + " " + &right + ")";
        },
        "(Morph" => {
            output = "(Count ".to_string() + &num.to_string() + "(Morph " + rest + ")";
        },
        "(Const" => {
            output = "(Count ".to_string() + &num.to_string() + "(Const " + rest + ")";
        },
        _ => {},
    };
    output.parse().unwrap()
}
