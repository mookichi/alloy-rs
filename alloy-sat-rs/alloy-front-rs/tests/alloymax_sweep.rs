//! AlloyMax course-benchmark sweep (Iter 14 experiment).
//!
//! Gated on `ALLOYMAX_COURSE_DIR` (skipped silently when absent).
//! Optional `ALLOYMAX_ONLY=<substring>` restricts to matching files.
//!
//! Method per `sat_*.als` (Alloy* Pareto query, higher-order `no`):
//!  1. FINDER: replace the `run AnySchedule` block with
//!     `run Finder { validSchedule[courses] }`, lower it, and maximize
//!     the interest hits as cell-conjunction softs
//!     (`Objective::And` over `Student.interests × Student.courses`
//!     cells — no counting circuit). A max-total solution is provably
//!     Pareto-optimal (any dominator would raise the total).
//!  2. VERIFIER: pin per-student hit counts from the optimum and ask
//!     for a strict dominator (`>=` all, `>` some). UNSAT certifies
//!     Pareto-optimality. All first-order.

use alloy_front_rs::{parse_module, run_command, Lowerer};
use alloy_kodkod_rs::opt::{CellRef, Objective};
use std::collections::{HashMap, HashSet};
use std::time::Instant;

fn course_dir() -> Option<String> {
    std::env::var("ALLOYMAX_COURSE_DIR").ok()
}

/// Replace the trailing `run AnySchedule {...} for ...` block (brace
/// matched) with `new_cmd`.
fn replace_run_block(src: &str, new_cmd: &str) -> String {
    let start = src
        .find("run AnySchedule")
        .expect("benchmark file must contain run AnySchedule");
    let brace = src[start..]
        .find('{')
        .expect("run block must open a brace")
        + start;
    let bytes = src.as_bytes();
    let mut depth = 0;
    let mut end = brace;
    for (i, &b) in bytes.iter().enumerate().skip(brace) {
        if b == b'{' {
            depth += 1;
        } else if b == b'}' {
            depth -= 1;
            if depth == 0 {
                end = i + 1;
                break;
            }
        }
    }
    assert!(depth == 0, "unbalanced braces in run block");
    // Extend through the end of the scope line (`} for 4 Int`).
    let line_end = src[end..]
        .find('\n')
        .map(|k| end + k)
        .unwrap_or(src.len());
    format!("{}{}{}", &src[..start], new_cmd, &src[line_end..])
}

fn sig_of(universe: &alloy_kodkod_rs::universe::Universe, atom_idx: u32) -> String {
    let name = universe
        .atom(atom_idx as usize)
        .map(|s| s.to_string())
        .unwrap_or_default();
    name.rsplit_once('$')
        .map(|(s, _)| s.to_string())
        .unwrap_or(name)
}

#[test]
fn alloymax_course_sweep() {
    let dir = match course_dir() {
        Some(d) => d,
        None => {
            eprintln!("SKIP: set ALLOYMAX_COURSE_DIR to run the course sweep");
            return;
        }
    };
    let only = std::env::var("ALLOYMAX_ONLY").unwrap_or_default();
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .expect("read course dir")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| {
            p.extension().map(|x| x == "als").unwrap_or(false)
                && p.file_name()
                    .map(|n| n.to_string_lossy().starts_with("sat_"))
                    .unwrap_or(false)
                && p.file_name()
                    .map(|n| n.to_string_lossy().contains(&only))
                    .unwrap_or(true)
        })
        .collect();
    files.sort();
    assert!(!files.is_empty(), "no sat_*.als in {dir}");
    eprintln!(
        "file | students | cells(C) | pairs | finder cost/time/calls | verify"
    );
    for path in files {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let src = std::fs::read_to_string(&path).expect("read model");
        let t_all = Instant::now();

        // ---- FINDER ----
        let finder_src = replace_run_block(
            &src,
            "run Finder {\n  validSchedule[courses]\n} for 4 Int",
        );
        let m = parse_module(&finder_src).expect("parse finder");
        let mut lower = Lowerer::new(&m);
        let problem = lower.prepare_command(0).expect("lower finder");
        // Resolve interests/courses relations by pool name.
        let mut by_name: HashMap<String, alloy_kodkod_rs::relation::RelationId> =
            HashMap::new();
        for r in problem.bounds.relations() {
            by_name.insert(problem.bounds.pool().name(r).to_string(), r);
        }
        let ci = by_name["Student.interests"];
        let cc = by_name["Student.courses"];
        let up_i = problem.bounds.upper_bound(ci).cloned().expect("I upper");
        let up_c = problem.bounds.upper_bound(cc).cloned().expect("C upper");
        let mut imap: HashMap<Vec<u32>, i64> = HashMap::new();
        for idx in up_i.index_view().iter() {
            if let Some(v) = up_i.dims_vector(idx as usize) {
                imap.insert(v, idx);
            }
        }
        let mut pairs: Vec<(CellRef, CellRef, i64)> = Vec::new();
        for idx in up_c.index_view().iter() {
            if let Some(v) = up_c.dims_vector(idx as usize) {
                if let Some(&j) = imap.get(&v) {
                    pairs.push((
                        CellRef {
                            relation: cc,
                            tuple_index: idx,
                        },
                        CellRef {
                            relation: ci,
                            tuple_index: j,
                        },
                        1,
                    ));
                }
            }
        }
        let n_cells = up_c.len();
        let solver = alloy_kodkod_rs::solver::Solver::with_options(
            alloy_kodkod_rs::solver::SolverOptions {
                bitwidth: problem.bitwidth,
                ..Default::default()
            },
        );
        let mut arena = problem.arena;
        let n_pairs = pairs.len();
        let t0 = Instant::now();
        let sol = solver
            .solve_opt(
                &mut arena,
                problem.formula,
                &problem.bounds,
                Objective::max_and(pairs),
            )
            .expect("optimize");
        let dt_finder = t0.elapsed();
        assert!(sol.satisfiable, "{name}: finder UNSAT");
        let cost = sol.cost.expect("finder cost");
        let inst = sol.instance.as_ref().expect("finder instance");

        // ---- per-student hit counts from the optimum ----
        let set_c: HashSet<i64> = inst
            .tuples(cc)
            .map(|ts| ts.index_view().iter().collect())
            .unwrap_or_default();
        let set_i: HashSet<i64> = inst
            .tuples(ci)
            .map(|ts| ts.index_view().iter().collect())
            .unwrap_or_default();
        let mut hits: HashMap<String, i64> = HashMap::new();
        let mut students: HashSet<String> = HashSet::new();
        for &idx in set_c.union(&set_i) {
            if let Some(v) = up_c.dims_vector(idx as usize) {
                let s = sig_of(problem.bounds.universe(), v[0]);
                students.insert(s.clone());
                if set_c.contains(&idx) && set_i.contains(&idx) {
                    *hits.entry(s).or_insert(0) += 1;
                }
            }
        }
        // Students with no tuples at all still need constraints (k=0).
        let mut stus: Vec<String> = students.into_iter().collect();
        stus.sort();
        let maxk = stus
            .iter()
            .map(|s| hits.get(s).copied().unwrap_or(0))
            .max()
            .unwrap_or(0);
        assert!(
            maxk < 8,
            "{name}: per-student hits {maxk} exceed 4-bit scope"
        );

        // ---- VERIFIER: no strict dominator exists ----
        let mut ge: Vec<String> = Vec::new();
        let mut gt: Vec<String> = Vec::new();
        for s in &stus {
            let k = hits.get(s).copied().unwrap_or(0);
            ge.push(format!("#({s}.interests & {s}.courses) >= {k}"));
            gt.push(format!("#({s}.interests & {s}.courses) > {k}"));
        }
        let verify_cmd = format!(
            "run Verify {{\n  validSchedule[courses]\n  {} and\n  ({})\n}} for 4 Int",
            ge.join(" and\n  "),
            gt.join(" or\n  ")
        );
        let verify_src = replace_run_block(&src, &verify_cmd);
        let m2 = parse_module(&verify_src).expect("parse verifier");
        let t1 = Instant::now();
        let vsol = run_command(&m2, 0).expect("verify solve");
        let dt_verify = t1.elapsed();
        assert!(
            !vsol.satisfiable,
            "{name}: dominator EXISTS (finder not Pareto-optimal)"
        );
        // ---- STRONG VERIFY: no alternative improves ANY single student
        // (the benchmark's literal `no courses'` query: simultaneous
        // individual maxima). UNSAT here = optimum satisfies the file
        // as written, not just Pareto-optimality.
        let strong_cmd = format!(
            "run StrongVerify {{\n  validSchedule[courses]\n  ({})\n}} for 4 Int",
            gt.join(" or\n  ")
        );
        let strong_src = replace_run_block(&src, &strong_cmd);
        let m3 = parse_module(&strong_src).expect("parse strong verifier");
        let t2 = Instant::now();
        let ssol = run_command(&m3, 0).expect("strong verify solve");
        let dt_strong = t2.elapsed();
        let strong = if ssol.satisfiable {
            "IMPROVER-EXISTS"
        } else {
            "UNSAT simultaneous-maximal"
        };
        eprintln!(
            "{name} | {} stus | {n_cells} cells | {n_pairs} pairs | cost={cost} finder={:.1}s/{}calls | UNSAT verify={:.1}s | {strong}={:.1}s (total {:.1}s)",
            stus.len(),
            dt_finder.as_secs_f64(),
            sol.sat_calls,
            dt_verify.as_secs_f64(),
            dt_strong.as_secs_f64(),
            t_all.elapsed().as_secs_f64()
        );
    }
}
