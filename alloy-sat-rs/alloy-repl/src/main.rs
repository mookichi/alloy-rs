//! alloy-repl: interactive REPL for Alloy (Rust native).
//!
//! Named stores (explicit, no hidden slots):
//! - `:run`/`:check` build a `Cnf` and save it under a name.
//! - `:solve` solves a named `Cnf` and saves the solution under a name.
//! - `:query`/`:validate`/`:show` take explicit names; bare forms fall back
//!   to the visible defaults (`*` in `:cnfs`/`:sols`, switched via `:use`).
//! - `sig`/`fact`/`pred`/`fun`/`assert`/`run`/`check` lines accumulate as
//!   model fragments (re-enter a name to replace it); multi-line input
//!   continues on `... ` until braces balance.
//! - `:eval <expr|formula>` checks satisfiability (`run { ... }` wrap).
//! - Bare expression lines are `:eval` (never stored).
//! - `:save <file>` writes a solution as an Alloy pin fact;
//!   `:add <file>` loads a file back as a fragment. Atom names (`A$0`)
//!   resolve as singleton sets, so pins round-trip.

use std::collections::HashMap;

use alloy_front_rs::{
    check, eval, fragment_keys, parse_module, query, run, solve, validate, Cnf, CnfKind,
    CommandKind, IncrementalSession, Instance, Module, PartialInstance,
};

mod fmt;
use clap::Parser as ClapParser;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

#[derive(ClapParser)]
#[command(
    name = "alloy-repl",
    about = "Alloy REPL (Rust): declare, run/check -> Cnf, solve/eval/query"
)]
struct Cli {
    /// .als file to preload
    file: Option<String>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum InputKind {
    Decl,
    Bare,
    Eval,
    Query,
}

struct Pending {
    kind: InputKind,
    text: String,
    depth: i32,
    /// For `Eval`: solution save name (`as <sol>`).
    /// For `Query`: solution reference name (`in <sol>`, None = default).
    target: Option<String>,
}

struct StoredSol {
    sat: bool,
    instance: Option<Instance>,
    /// Origin Cnf store name; empty for `:eval` solutions (no Cnf context).
    from_cnf: String,
}

struct Session {
    base_src: String,
    fragments: Vec<(Vec<String>, String)>,
    current_src: String,
    module: Option<Module>,
    source_desc: String,
    cnfs: HashMap<String, Cnf>,
    sols: HashMap<String, StoredSol>,
    cnf_order: Vec<String>,
    sol_order: Vec<String>,
    default_cnf: Option<String>,
    default_sol: Option<String>,
    pending: Option<Pending>,
}

impl Session {
    fn new() -> Self {
        Session {
            base_src: String::new(),
            fragments: Vec::new(),
            current_src: String::new(),
            module: None,
            source_desc: String::new(),
            cnfs: HashMap::new(),
            sols: HashMap::new(),
            cnf_order: Vec::new(),
            sol_order: Vec::new(),
            default_cnf: None,
            default_sol: None,
            pending: None,
        }
    }

    fn joined_source(&self) -> String {
        let mut src = self.base_src.clone();
        for (_, text) in &self.fragments {
            if !src.is_empty() && !src.ends_with('\n') {
                src.push('\n');
            }
            src.push_str(text);
            src.push('\n');
        }
        src
    }

    /// Parse `src`, committing it (and `frags`) only on success.
    fn commit_source(
        &mut self,
        src: String,
        frags: Vec<(Vec<String>, String)>,
        desc: String,
        note: &str,
    ) -> bool {
        match parse_module(&src) {
            Ok(m) => {
                let n = m.commands.len();
                self.fragments = frags;
                self.current_src = src;
                self.module = Some(m);
                self.source_desc = desc;
                self.clear_stores();
                println!("{note} ({n} commands)");
                true
            }
            Err(e) => {
                println!("parse error: {e}");
                false
            }
        }
    }

    fn rebuild(&mut self, note: &str) {
        let src = self.joined_source();
        let frags = self.fragments.clone();
        let desc = self.source_desc.clone();
        self.commit_source(src, frags, desc, note);
    }

    fn load_file(&mut self, path: &str) {
        match std::fs::read_to_string(path) {
            Ok(src) => {
                let mut sess = Session::new();
                sess.base_src = src;
                let joined = sess.joined_source();
                // Commit into self only on success, keeping the old session otherwise.
                match parse_module(&joined) {
                    Ok(m) => {
                        let n = m.commands.len();
                        self.base_src = sess.base_src;
                        self.fragments = Vec::new();
                        self.current_src = joined;
                        self.module = Some(m);
                        self.source_desc = path.to_string();
                        self.clear_stores();
                        self.pending = None;
                        println!("loaded ({n} commands)");
                    }
                    Err(e) => println!("parse error: {e}"),
                }
            }
            Err(e) => println!("cannot read {path}: {e}"),
        }
    }

    fn add_fragment(&mut self, text: &str) {
        if first_token(text) == "module" {
            println!("hint: no `module` header needed in the REPL (use :load for files)");
            return;
        }
        let keys = match fragment_keys(text) {
            Ok(k) => k,
            Err(e) => {
                println!("parse error: {e}");
                return;
            }
        };
        let mut frags = self.fragments.clone();
        let mut replaced = 0;
        if !keys.is_empty() {
            let before = frags.len();
            frags.retain(|(ks, _)| ks.iter().all(|k| !keys.contains(k)));
            replaced = before - frags.len();
        }
        frags.push((keys, text.to_string()));
        let mut src = self.base_src.clone();
        for (_, t) in &frags {
            if !src.is_empty() && !src.ends_with('\n') {
                src.push('\n');
            }
            src.push_str(t);
            src.push('\n');
        }
        let desc = self.source_desc.clone();
        let note = if replaced > 0 {
            format!("replaced {replaced} fragment(s), rebuilt")
        } else {
            "added fragment, rebuilt".to_string()
        };
        self.commit_source(src, frags, desc, &note);
    }

    fn clear_stores(&mut self) {
        let nc = self.cnfs.len();
        let ns = self.sols.len();
        self.cnfs.clear();
        self.sols.clear();
        self.cnf_order.clear();
        self.sol_order.clear();
        self.default_cnf = None;
        self.default_sol = None;
        if nc + ns > 0 {
            println!("model changed: dropped {nc} cnfs, {ns} solutions");
        }
    }

    fn list_commands(&self) {
        match &self.module {
            None => println!("no module loaded (use :load <file> or type declarations)"),
            Some(m) if m.commands.is_empty() => println!("no commands in module"),
            Some(m) => {
                for (i, c) in m.commands.iter().enumerate() {
                    let (kind, name) = match &c.kind {
                        CommandKind::Run(n) => ("run", n.clone().unwrap_or_default()),
                        CommandKind::Check(n) => ("check", n.clone().unwrap_or_default()),
                    };
                    println!("{i:02}. {kind:<6} {name}");
                }
            }
        }
    }

    fn list_cnfs(&self) {
        if self.cnf_order.is_empty() {
            println!("no cnfs (use :run|:check first; :help for forms)");
            return;
        }
        for name in &self.cnf_order {
            let mark = match &self.default_cnf {
                Some(d) if d == name => "*",
                _ => " ",
            };
            match self.cnfs.get(name) {
                Some(cnf) => println!("{mark} {name}  ({})", cnf.summary()),
                None => println!("{mark} {name}  (gone)"),
            }
        }
    }

    fn list_sols(&self) {
        if self.sol_order.is_empty() {
            println!("no solutions (use :solve first; :help for forms)");
            return;
        }
        for name in &self.sol_order {
            let mark = match &self.default_sol {
                Some(d) if d == name => "*",
                _ => " ",
            };
            match self.sols.get(name) {
                Some(s) => {
                    let st = if s.sat { "SAT" } else { "UNSAT" };
                    if s.from_cnf.is_empty() {
                        println!("{mark} {name}  {st} (from :eval)");
                    } else {
                        println!("{mark} {name}  {st} <- {}", s.from_cnf);
                    }
                }
                None => println!("{mark} {name}  (gone)"),
            }
        }
    }

    fn do_use(&mut self, name: &str) {
        if self.cnfs.contains_key(name) && self.sols.contains_key(name) {
            self.default_cnf = Some(name.to_string());
            self.default_sol = Some(name.to_string());
            println!("default: cnf `{name}` + solution `{name}`");
        } else if self.cnfs.contains_key(name) {
            self.default_cnf = Some(name.to_string());
            // Point the solution default at the newest solution from this cnf, if any.
            let mut best: Option<String> = None;
            for s in &self.sol_order {
                if let Some(st) = self.sols.get(s) {
                    if st.from_cnf == name {
                        best = Some(s.clone());
                    }
                }
            }
            if let Some(b) = best {
                self.default_sol = Some(b.clone());
                println!("default cnf `{name}` (+ solution `{b}`)");
            } else {
                println!("default cnf `{name}`");
            }
        } else if self.sols.contains_key(name) {
            let from = self
                .sols
                .get(name)
                .map(|s| s.from_cnf.clone())
                .unwrap_or_default();
            self.default_sol = Some(name.to_string());
            if !from.is_empty() && self.cnfs.contains_key(&from) {
                self.default_cnf = Some(from.clone());
                println!("default solution `{name}` (+ cnf `{from}`)");
            } else {
                println!("default solution `{name}`");
            }
        } else {
            println!("no cnf or solution named `{name}` (:cnfs / :sols to list)");
        }
    }

    fn list_fragments(&self) {
        if self.fragments.is_empty() {
            println!("no fragments (model comes from :load file)");
            return;
        }
        for (i, (keys, text)) in self.fragments.iter().enumerate() {
            let first = text
                .lines()
                .map(str::trim)
                .find(|l| !l.is_empty() && !l.starts_with("--") && !l.starts_with("//"))
                .unwrap_or("");
            let key = if keys.is_empty() {
                "append".to_string()
            } else {
                keys.join(",")
            };
            println!("{i:02}. [{key}] {first}");
        }
    }

    /// Delete one entered fragment by `:fragments` index, then rebuild.
    /// The rebuild invalidates saved Cnfs/solutions (model changed).
    fn drop_fragment(&mut self, arg: Option<&str>) {
        let idx: usize = match arg {
            Some(a) => match a.parse() {
                Ok(i) => i,
                Err(_) => {
                    println!("usage: :drop <fragment-index> (:fragments to list)");
                    return;
                }
            },
            None => {
                println!("usage: :drop <fragment-index> (:fragments to list)");
                return;
            }
        };
        if idx >= self.fragments.len() {
            println!("no fragment #{idx} (:fragments to list)");
            return;
        }
        let mut frags = self.fragments.clone();
        let (_, text) = frags.remove(idx);
        let first = text.lines().next().unwrap_or("").to_string();
        let mut src = self.base_src.clone();
        for (_, t) in &frags {
            if !src.is_empty() && !src.ends_with('\n') {
                src.push('\n');
            }
            src.push_str(t);
            src.push('\n');
        }
        let desc = self.source_desc.clone();
        self.commit_source(
            src,
            frags,
            desc,
            &format!("dropped fragment {idx:02} [{first}], rebuilt"),
        );
    }

    fn resolve_index(&self, arg: Option<&str>) -> Result<usize, String> {
        let m = self.module.as_ref().ok_or("no module loaded")?;
        match arg {
            None => {
                if m.commands.len() == 1 {
                    Ok(0)
                } else {
                    Err(
                        "usage: :run|:check <index|name> [as <cnf>] (module has several commands)"
                            .into(),
                    )
                }
            }
            Some(a) => {
                if let Ok(i) = a.parse::<usize>() {
                    if i < m.commands.len() {
                        return Ok(i);
                    }
                    return Err(format!("no command #{i}"));
                }
                m.find_command(a)
                    .ok_or_else(|| format!("no command named `{a}`"))
            }
        }
    }

    /// Save `cnf` under `name` (auto-suffixed on collision) or overwrite an
    /// explicit `as` name. Returns the final name.
    fn store_cnf(&mut self, cnf: Cnf, want: Option<&str>) -> String {
        match want {
            Some(n) => {
                let overwrote = self.cnfs.contains_key(n);
                if !overwrote {
                    self.cnf_order.push(n.to_string());
                }
                self.cnfs.insert(n.to_string(), cnf);
                self.default_cnf = Some(n.to_string());
                if overwrote {
                    println!("overwrote cnf `{n}`");
                }
                n.to_string()
            }
            None => {
                let base = cnf
                    .command_name
                    .clone()
                    .filter(|s| !s.is_empty())
                    .unwrap_or_else(|| format!("{}{}", cnf.kind, cnf.command_index));
                let mut name = base.clone();
                let mut k = 2;
                while self.cnfs.contains_key(&name) {
                    name = format!("{base}_{k}");
                    k += 1;
                }
                self.cnf_order.push(name.clone());
                self.cnfs.insert(name.clone(), cnf);
                self.default_cnf = Some(name.clone());
                name
            }
        }
    }

    /// Save a solution; auto name inherits the Cnf store name.
    fn store_sol(
        &mut self,
        want: Option<&str>,
        from_cnf: &str,
        sat: bool,
        instance: Option<Instance>,
    ) -> String {
        match want {
            Some(n) => {
                let overwrote = self.sols.contains_key(n);
                if !overwrote {
                    self.sol_order.push(n.to_string());
                }
                self.sols.insert(
                    n.to_string(),
                    StoredSol {
                        sat,
                        instance,
                        from_cnf: from_cnf.to_string(),
                    },
                );
                self.default_sol = Some(n.to_string());
                if overwrote {
                    println!("overwrote solution `{n}`");
                }
                n.to_string()
            }
            None => {
                let mut name = from_cnf.to_string();
                let mut k = 2;
                while self.sols.contains_key(&name) {
                    name = format!("{from_cnf}_{k}");
                    k += 1;
                }
                self.sol_order.push(name.clone());
                self.sols.insert(
                    name.clone(),
                    StoredSol {
                        sat,
                        instance,
                        from_cnf: from_cnf.to_string(),
                    },
                );
                self.default_sol = Some(name.clone());
                name
            }
        }
    }

    fn do_build(
        &mut self,
        kind: CnfKind,
        target: Option<&str>,
        as_name: Option<&str>,
    ) -> Option<String> {
        if let Some(n) = as_name {
            if !is_valid_name(n) {
                println!("bad name `{n}` (use [A-Za-z0-9_.#-]+)");
                return None;
            }
        }
        let idx = match self.resolve_index(target) {
            Ok(i) => i,
            Err(e) => {
                println!("{e}");
                return None;
            }
        };
        let m = self.module.as_ref().expect("checked");
        let built = match kind {
            CnfKind::Run => run(m, idx),
            CnfKind::Check => check(m, idx),
        };
        match built {
            Ok(cnf) => {
                let summary = cnf.summary();
                let name = self.store_cnf(cnf, as_name);
                println!("saved cnf `{name}` ({summary}) *default");
                println!("hint: :solve {name} to solve, :show {name} to view cnf");
                Some(name)
            }
            Err(e) => {
                println!("build error: {e}");
                None
            }
        }
    }

    fn print_solution(&self, inst: &Option<Instance>, is_check: bool) {
        match inst {
            Some(i) => {
                if is_check {
                    println!("SAT -- counterexample found:");
                } else {
                    println!("SAT -- example found:");
                }
                println!("{}", fmt::instance_alloy(i));
            }
            None => {
                if is_check {
                    println!("UNSAT -- no counterexample (assertion holds; empty)");
                } else {
                    println!("UNSAT -- no example (empty)");
                }
            }
        }
    }

    fn resolve_cnf(&self, name: &str) -> Option<&Cnf> {
        self.cnfs.get(name)
    }

    fn default_cnf_name(&self) -> Option<String> {
        self.default_cnf.clone()
    }

    fn default_sol_name(&self) -> Option<String> {
        self.default_sol.clone()
    }

    fn do_solve(&mut self, cnf_arg: Option<&str>, as_name: Option<&str>) {
        if let Some(n) = as_name {
            if !is_valid_name(n) {
                println!("bad name `{n}` (use [A-Za-z0-9_.#-]+)");
                return;
            }
        }
        let cnf_name = match cnf_arg {
            Some(n) => n.to_string(),
            None => match self.default_cnf_name() {
                Some(n) => n,
                None => {
                    println!("no cnf selected (use :run|:check first, :cnfs to list)");
                    return;
                }
            },
        };
        let cnf = match self.resolve_cnf(&cnf_name) {
            Some(c) => c.clone(),
            None => {
                // Migration hint: the old `:solve <command>` auto-build is gone.
                if self.module.is_some() && self.resolve_index(Some(&cnf_name)).is_ok() {
                    println!("no cnf named `{cnf_name}` (did you mean :run {cnf_name} first?)");
                } else {
                    println!("no cnf named `{cnf_name}` (:cnfs to list)");
                }
                return;
            }
        };
        match solve(&cnf) {
            Ok(inst) => {
                let sat = inst.is_some();
                self.print_solution(&inst, cnf.is_check());
                let sol_name = self.store_sol(as_name, &cnf_name, sat, inst);
                println!("saved solution `{sol_name}` <- `{cnf_name}` *default");
            }
            Err(e) => println!("solve error: {e}"),
        }
    }

    fn do_eval_text(&mut self, expr: &str, save_as: Option<&str>) {
        if let Some(n) = save_as {
            if !is_valid_name(n) {
                println!("bad name `{n}` (use [A-Za-z0-9_.#-]+)");
                return;
            }
        }
        if self.module.is_none() {
            println!("no module loaded");
            return;
        }
        match eval(&self.current_src, expr) {
            Ok(sol) => {
                self.print_solution(&sol.instance, false);
                if let Some(n) = save_as {
                    let sat = sol.satisfiable;
                    let name = self.store_sol(Some(n), "", sat, sol.instance);
                    println!("saved solution `{name}` (from :eval; no Cnf context) *default");
                }
            }
            Err(e) => println!("eval error: {e}"),
        }
    }

    fn do_query_text(&self, expr: &str, sol_arg: Option<&str>) {
        let sol_name = match sol_arg {
            Some(n) => n.to_string(),
            None => match self.default_sol_name() {
                Some(n) => n,
                None => {
                    println!(":query needs a solution (use :solve first; form: :query <expr> [in <sol>])");
                    return;
                }
            },
        };
        let stored = match self.sols.get(&sol_name) {
            Some(s) => (s.from_cnf.clone(), s.instance.clone()),
            None => {
                println!("no solution named `{sol_name}` (:sols to list)");
                return;
            }
        };
        let (from_cnf, inst_owned) = stored;
        if from_cnf.is_empty() {
            println!("solution `{sol_name}` is from :eval (no Cnf context for :query)");
            return;
        }
        let inst_owned = match inst_owned {
            Some(i) => i,
            None => {
                println!("solution `{sol_name}` is UNSAT (no instance to query)");
                return;
            }
        };
        let cnf_owned = match self.cnfs.get(&from_cnf) {
            Some(c) => c.clone(),
            None => {
                println!("solution `{sol_name}` refers to cnf `{from_cnf}` which is gone");
                return;
            }
        };
        let m = match &self.module {
            Some(m) => m,
            None => {
                println!("no module loaded");
                return;
            }
        };
        let scope = match m.commands.get(cnf_owned.command_index) {
            Some(c) => &c.scope,
            None => {
                println!("command for `{sol_name}` is gone (rebuild with :run|:check)");
                return;
            }
        };
        match query(m, scope, &cnf_owned, expr, &inst_owned) {
            Ok((arity, ts)) => println!("{}", fmt::set_alloy(ts.universe(), arity, &ts)),
            Err(e) => println!("query error: {e}"),
        }
    }

    fn do_bare_expr(&mut self, expr: &str) {
        if self.module.is_none() {
            println!("no module loaded");
            return;
        }
        self.do_eval_text(expr, None);
    }

    fn do_validate(&self, sol_arg: Option<&str>, cnf_arg: Option<&str>) {
        let sol_name = match sol_arg {
            Some(n) => n,
            None => match self.default_sol.as_deref() {
                Some(n) => n,
                None => {
                    println!("usage: :validate <sol> [in <cnf>]");
                    return;
                }
            },
        };
        let stored = match self.sols.get(sol_name) {
            Some(s) => s,
            None => {
                println!("no solution named `{sol_name}` (:sols to list)");
                return;
            }
        };
        let cnf_name: &str = match cnf_arg {
            Some(n) => n,
            None => {
                if stored.from_cnf.is_empty() {
                    println!("solution `{sol_name}` is from :eval (no Cnf to validate against)");
                    return;
                }
                &stored.from_cnf
            }
        };
        let cnf = match self.cnfs.get(cnf_name) {
            Some(c) => c,
            None => {
                println!("no cnf named `{cnf_name}` (:cnfs to list)");
                return;
            }
        };
        let inst = match &stored.instance {
            Some(i) => i,
            None => {
                println!("solution `{sol_name}` is UNSAT (no instance to validate)");
                return;
            }
        };
        match validate(cnf, inst) {
            Some(back) => {
                println!("valid -- `{sol_name}` is a model of `{cnf_name}`, as-is:");
                println!("{}", fmt::instance_alloy(&back));
            }
            None => println!("invalid -- `{sol_name}` is not a model of `{cnf_name}` (none/empty)"),
        }
    }

    /// Write a (partial) instance as an Alloy pin fact.
    ///
    /// `rels` selects relations by pool name (`+` tokens already stripped by
    /// the caller); empty selects every non-skolem relation. Field relations
    /// (`Owner.field`) are emitted under their bare field name when it is
    /// unambiguous — dotted names would parse as joins, not references.
    /// Skolems, ints, and unreferenceable (ambiguous/slashed) relations are
    /// skipped with a notice.
    fn do_save(&self, file: &str, sol_arg: Option<&str>, rels: &[&str]) {
        let sol_name: &str = match sol_arg {
            Some(n) => n,
            None => match self.default_sol.as_deref() {
                Some(n) => n,
                None => {
                    println!(
                        "no solution saved yet (use :solve first; \
                         form: :save <file> [in <sol>] [rels...])"
                    );
                    return;
                }
            },
        };
        let stored = match self.sols.get(sol_name) {
            Some(s) => s,
            None => {
                println!("no solution named `{sol_name}` (:sols to list)");
                return;
            }
        };
        let inst = match &stored.instance {
            Some(i) => i,
            None => {
                println!("solution `{sol_name}` is UNSAT (nothing to save)");
                return;
            }
        };
        let pool = inst.pool();
        let all_names: Vec<String> = inst
            .relation_tuples()
            .map(|(r, _)| pool.name(r).to_string())
            .collect();
        // Resolve the selection to pool names.
        let wanted: Vec<String> = if rels.is_empty() {
            all_names
                .iter()
                .filter(|n| {
                    inst.find_relation_by_name(n)
                        .map(|r| !pool.is_skolem(r))
                        .unwrap_or(false)
                })
                .cloned()
                .collect()
        } else {
            let mut out = Vec::new();
            for want in rels {
                let pool_name = if all_names.iter().any(|n| n == want) {
                    want.to_string()
                } else if let Some(hit) = unique_bare_field(&all_names, want) {
                    hit
                } else {
                    println!("no relation `{want}` in solution `{sol_name}`");
                    return;
                };
                if pin_ref(&all_names, &pool_name).is_none() {
                    println!("cannot reference `{pool_name}` in Alloy (ambiguous field)");
                    return;
                }
                out.push(pool_name);
            }
            out
        };
        let mut lines: Vec<(String, String)> = Vec::new();
        let mut skipped_skolem = 0;
        let mut skipped_ref = 0;
        for name in &wanted {
            let r = match inst.find_relation_by_name(name) {
                Some(r) => r,
                None => continue,
            };
            if pool.is_skolem(r) {
                skipped_skolem += 1;
                continue;
            }
            let emit = match pin_ref(&all_names, name) {
                Some(e) => e,
                None => {
                    skipped_ref += 1;
                    continue;
                }
            };
            let ts = inst.tuples(r).expect("resolved relation has tuples");
            lines.push((emit, fmt::set_expr_alloy(inst.universe(), ts.arity(), ts)));
        }
        if lines.is_empty() {
            println!("nothing to save (all selected relations skipped)");
            return;
        }
        let base = file.rsplit('/').next().unwrap_or(file);
        let stem = match base.rfind('.') {
            Some(i) if i > 0 => &base[..i],
            _ => base,
        };
        let text = fmt::pin_fact_text(stem, sol_name, inst.universe().size(), &lines);
        match std::fs::write(file, &text) {
            Ok(()) => {
                let mut msg = format!(
                    "saved {file} (fact from `{sol_name}`, {} relations pinned)",
                    lines.len()
                );
                let mut skipped = Vec::new();
                if skipped_skolem > 0 {
                    skipped.push(format!("{skipped_skolem} skolem"));
                }
                if skipped_ref > 0 {
                    skipped.push(format!("{skipped_ref} unreferenceable"));
                }
                let n_ints = inst.int_tuples().count();
                if n_ints > 0 {
                    skipped.push(format!("{n_ints} int"));
                }
                if !skipped.is_empty() {
                    msg.push_str(&format!("; skipped {}", skipped.join(", ")));
                }
                println!("{msg}");
            }
            Err(e) => println!("cannot write {file}: {e}"),
        }
    }

    /// Load a file back as a model fragment (replace semantics via fact name).
    fn do_add(&mut self, file: &str) {
        match std::fs::read_to_string(file) {
            Ok(text) => self.add_fragment(&text),
            Err(e) => println!("cannot read {file}: {e}"),
        }
    }

    /// Inspect a binary partial instance (decode + summary, no solving).
    fn do_pread(&self, file: &str) {
        let bytes = match std::fs::read(file) {
            Ok(b) => b,
            Err(e) => {
                println!("cannot read {file}: {e}");
                return;
            }
        };
        let partial = match PartialInstance::decode(&bytes) {
            Ok(p) => p,
            Err(e) => {
                println!("{file}: {e}");
                return;
            }
        };
        println!(
            "apin {file}: universe {}, {} relations, {} ints, {} bytes",
            partial.universe_size,
            partial.rels.len(),
            partial.ints.len(),
            bytes.len()
        );
        for r in &partial.rels {
            println!("  {} ({}): {} tuples", r.name, r.arity, r.indices.len());
        }
        for p in &partial.ints {
            println!("  int {} -> {}", p.value, p.tuple);
        }
    }

    /// Pin a binary partial onto a Cnf in a throwaway session and solve.
    ///
    /// `gated` wraps the units in one fresh selector (retractable shape);
    /// in a one-shot session the outcome equals permanent units — the flag
    /// exists for forward compatibility with persistent sessions.
    #[allow(clippy::too_many_arguments)]
    fn do_ppin(
        &mut self,
        file: &str,
        rels: &[&str],
        cnf_arg: Option<&str>,
        sol_arg: Option<&str>,
        gated: bool,
    ) {
        if let Some(n) = sol_arg {
            if !is_valid_name(n) {
                println!("bad name `{n}` (use [A-Za-z0-9_.#-]+)");
                return;
            }
        }
        let mut partial = match read_partial(file) {
            Ok(p) => p,
            Err(e) => {
                println!("{e}");
                return;
            }
        };
        if !rels.is_empty() {
            partial = match partial.project(rels) {
                Ok(p) => p,
                Err(e) => {
                    println!("{e}");
                    return;
                }
            };
        }
        let (cnf_name, cnf) = match self.resolve_cnf_owned(cnf_arg) {
            Ok(v) => v,
            Err(e) => {
                println!("{e}");
                return;
            }
        };
        let mut sess = match IncrementalSession::open(&cnf) {
            Ok(s) => s,
            Err(e) => {
                println!("session error: {e}");
                return;
            }
        };
        if gated {
            let sel = match partial.apply_gated(&mut sess) {
                Ok(sel) => sel,
                Err(e) => {
                    println!("pin error: {e}");
                    return;
                }
            };
            println!(
                "pinned {} (gated #{sel}) from {file}",
                partial_summary(&partial)
            );
            match sess.solve(&[sel]) {
                Ok(inst) => {
                    self.print_solution(&inst, cnf.is_check());
                    let sat = inst.is_some();
                    let name = self.store_sol(sol_arg, &cnf_name, sat, inst);
                    println!("saved solution `{name}` <- `{cnf_name}` *default");
                }
                Err(e) => println!("solve error: {e}"),
            }
        } else {
            let n = match partial.apply_units(&mut sess) {
                Ok(n) => n,
                Err(e) => {
                    println!("pin error: {e}");
                    return;
                }
            };
            println!(
                "pinned {n} units from {file} ({})",
                partial_summary(&partial)
            );
            match sess.solve(&[]) {
                Ok(inst) => {
                    self.print_solution(&inst, cnf.is_check());
                    let sat = inst.is_some();
                    let name = self.store_sol(sol_arg, &cnf_name, sat, inst);
                    println!("saved solution `{name}` <- `{cnf_name}` *default");
                }
                Err(e) => println!("solve error: {e}"),
            }
        }
    }

    /// Exclude a binary partial (nogood over its value) and solve.
    #[allow(clippy::too_many_arguments)]
    fn do_pavoid(
        &mut self,
        file: &str,
        rels: &[&str],
        cnf_arg: Option<&str>,
        sol_arg: Option<&str>,
        gated: bool,
    ) {
        if let Some(n) = sol_arg {
            if !is_valid_name(n) {
                println!("bad name `{n}` (use [A-Za-z0-9_.#-]+)");
                return;
            }
        }
        let partial = match read_partial(file) {
            Ok(p) => p,
            Err(e) => {
                println!("{e}");
                return;
            }
        };
        let (cnf_name, cnf) = match self.resolve_cnf_owned(cnf_arg) {
            Ok(v) => v,
            Err(e) => {
                println!("{e}");
                return;
            }
        };
        let mut sess = match IncrementalSession::open(&cnf) {
            Ok(s) => s,
            Err(e) => {
                println!("session error: {e}");
                return;
            }
        };
        let project: Option<Vec<&str>> = if rels.is_empty() {
            None
        } else {
            Some(rels.to_vec())
        };
        let clause = match partial.avoid_clause(&sess, project.as_deref()) {
            Ok(c) => c,
            Err(e) => {
                println!("avoid error: {e}");
                return;
            }
        };
        if clause.is_empty() {
            println!("nothing to exclude (scope covers no free cells)");
            return;
        }
        if gated {
            let sel = match sess.add_gated(std::slice::from_ref(&clause)) {
                Ok(sel) => sel,
                Err(e) => {
                    println!("avoid error: {e}");
                    return;
                }
            };
            println!(
                "avoiding {} (gated #{sel}, {} lits) from {file}",
                partial_summary(&partial),
                clause.len()
            );
            match sess.solve(&[sel]) {
                Ok(inst) => {
                    self.print_solution(&inst, cnf.is_check());
                    let sat = inst.is_some();
                    let name = self.store_sol(sol_arg, &cnf_name, sat, inst);
                    println!("saved solution `{name}` <- `{cnf_name}` *default");
                }
                Err(e) => println!("solve error: {e}"),
            }
        } else {
            match sess.add_clauses(std::slice::from_ref(&clause)) {
                Ok(()) => {}
                Err(e) => {
                    println!("avoid error: {e}");
                    return;
                }
            }
            println!(
                "avoiding {} ({} lits) from {file}",
                partial_summary(&partial),
                clause.len()
            );
            match sess.solve(&[]) {
                Ok(inst) => {
                    self.print_solution(&inst, cnf.is_check());
                    let sat = inst.is_some();
                    let name = self.store_sol(sol_arg, &cnf_name, sat, inst);
                    println!("saved solution `{name}` <- `{cnf_name}` *default");
                }
                Err(e) => println!("solve error: {e}"),
            }
        }
    }

    /// Resolve a solution reference to an owned (name, instance) pair.
    fn sol_instance(&self, sol_arg: Option<&str>) -> Result<(String, Instance), String> {
        let sol_name = match sol_arg {
            Some(n) => n.to_string(),
            None => self
                .default_sol
                .clone()
                .ok_or_else(|| "no solution saved yet (use :solve first)".to_string())?,
        };
        let stored = self
            .sols
            .get(&sol_name)
            .ok_or_else(|| format!("no solution named `{sol_name}` (:sols to list)"))?;
        let inst = stored
            .instance
            .clone()
            .ok_or_else(|| format!("solution `{sol_name}` is UNSAT (nothing to use)"))?;
        Ok((sol_name, inst))
    }

    /// Resolve a Cnf reference to an owned (name, Cnf) pair.
    fn resolve_cnf_owned(&self, arg: Option<&str>) -> Result<(String, Cnf), String> {
        let name = match arg {
            Some(n) => n.to_string(),
            None => self.default_cnf.clone().ok_or_else(|| {
                "no cnf selected (use :run|:check first, :cnfs to list)".to_string()
            })?,
        };
        let cnf = match self.cnfs.get(&name) {
            Some(c) => c.clone(),
            None => {
                if self.module.is_some() && self.resolve_index(Some(&name)).is_ok() {
                    return Err(format!(
                        "no cnf named `{name}` (did you mean :run {name} first?)"
                    ));
                }
                return Err(format!("no cnf named `{name}` (:cnfs to list)"));
            }
        };
        Ok((name, cnf))
    }

    /// Write a (partial) instance in binary APIN form (lossless, incl. ints).
    /// Relation filter mirrors `:save` (exact or unique bare field); no
    /// Alloy-reference filtering applies since indices transfer directly.
    fn do_psave(&self, file: &str, sol_arg: Option<&str>, rels: &[&str]) {
        let (sol_name, inst) = match self.sol_instance(sol_arg) {
            Ok(v) => v,
            Err(e) => {
                println!("{e}");
                return;
            }
        };
        let pool = inst.pool();
        let all_names: Vec<String> = inst
            .relation_tuples()
            .map(|(r, _)| pool.name(r).to_string())
            .collect();
        let only_owned: Option<Vec<String>> = if rels.is_empty() {
            None
        } else {
            let mut out = Vec::new();
            for want in rels {
                if all_names.iter().any(|n| n == want) {
                    out.push(want.to_string());
                } else if let Some(hit) = unique_bare_field(&all_names, want) {
                    out.push(hit);
                } else {
                    println!("no relation `{want}` in solution `{sol_name}`");
                    return;
                }
            }
            Some(out)
        };
        let only_refs: Option<Vec<&str>> = only_owned
            .as_ref()
            .map(|v| v.iter().map(|s| s.as_str()).collect());
        let partial = match PartialInstance::extract(&inst, only_refs.as_deref()) {
            Ok(p) => p,
            Err(e) => {
                println!("extract error: {e}");
                return;
            }
        };
        let bytes = partial.encode();
        match std::fs::write(file, &bytes) {
            Ok(()) => {
                let mut msg = format!(
                    "saved {file} (.apin from `{sol_name}`, {} relations, {} ints, {} bytes)",
                    partial.rels.len(),
                    partial.ints.len(),
                    bytes.len()
                );
                if !partial.skipped_skolem.is_empty() {
                    msg.push_str(&format!(
                        "; skipped {} skolem",
                        partial.skipped_skolem.len()
                    ));
                }
                println!("{msg}");
            }
            Err(e) => println!("cannot write {file}: {e}"),
        }
    }

    fn show_cnf(&self, name: &str, limit: usize) {
        let cnf = match self.cnfs.get(name) {
            Some(c) => c,
            None => {
                println!("no cnf named `{name}` (:cnfs to list)");
                return;
            }
        };
        println!("cnf `{name}`: {}", cnf.summary());
        println!("  bitwidth={} skolemize={}", cnf.bitwidth, cnf.skolemize);
        for (i, cl) in cnf.clauses.iter().take(limit).enumerate() {
            let line: Vec<String> = cl.iter().map(|l| l.to_string()).collect();
            println!("  c{i}: {}", line.join(" "));
        }
        if cnf.clauses.len() > limit {
            println!("  ... ({} more clauses)", cnf.clauses.len() - limit);
        }
    }

    fn show_sol(&self, name: &str) {
        let s = match self.sols.get(name) {
            Some(s) => s,
            None => {
                println!("no solution named `{name}` (:sols to list)");
                return;
            }
        };
        match &s.instance {
            Some(inst) => {
                let kind = if s.from_cnf.is_empty() {
                    "SAT (from :eval)".to_string()
                } else {
                    format!("SAT <- `{}`", s.from_cnf)
                };
                println!("solution `{name}`: {kind}\n{}", fmt::instance_alloy(inst));
            }
            None => println!("solution `{name}`: UNSAT (none / empty)"),
        }
    }

    /// `:show [name] [N]`: no args = both defaults; numeric-only = N for the
    /// default cnf; name (+ optional N) = that entry (cnf and/or solution).
    fn do_show(&self, args: &[&str]) {
        if args.is_empty() {
            match (&self.default_cnf, &self.default_sol) {
                (None, None) => println!("nothing to show (use :run then :solve)"),
                (Some(c), _) => {
                    self.show_cnf(c, 10);
                    if let Some(s) = &self.default_sol {
                        self.show_sol(s);
                    } else {
                        println!("no solution yet (:solve {c})");
                    }
                }
                (None, Some(s)) => self.show_sol(s),
            }
            return;
        }
        if args.len() == 1 && args[0].parse::<usize>().is_ok() {
            let limit: usize = args[0].parse().unwrap_or(10);
            match &self.default_cnf {
                Some(c) => self.show_cnf(c, limit),
                None => println!("no cnf selected (:cnfs to list)"),
            }
            return;
        }
        let name = args[0];
        let limit: usize = args.get(1).and_then(|a| a.parse().ok()).unwrap_or(10);
        let has_cnf = self.cnfs.contains_key(name);
        let has_sol = self.sols.contains_key(name);
        if !has_cnf && !has_sol {
            println!("no cnf or solution named `{name}` (:cnfs / :sols to list)");
            return;
        }
        if has_cnf {
            self.show_cnf(name, limit);
        }
        if has_sol {
            self.show_sol(name);
        }
    }

    fn submit_pending(&mut self, pending: Pending) {
        match pending.kind {
            InputKind::Decl => self.add_fragment(&pending.text),
            InputKind::Bare => self.do_bare_expr(&pending.text),
            InputKind::Eval => self.do_eval_text(&pending.text, pending.target.as_deref()),
            InputKind::Query => self.do_query_text(&pending.text, pending.target.as_deref()),
        }
    }
}

fn print_help() {
    println!("declare (accumulate into the model; re-enter a name to replace):");
    println!("  sig ... / fact ... / pred ... / fun ... / assert ... / open ...");
    println!("  run ... / check ...      as a fragment when it names no command");
    println!("  multi-line continues on `... ` until braces balance;");
    println!("  blank line or a `:command` line submits pending input first");
    println!("named stores (Cnf and solution namespaces are separate):");
    println!("  :run <i|name> [as <cnf>]    build Cnf, save it (auto: command name, else run0..)");
    println!("  :check <i|name> [as <cnf>]  build negated Cnf, save it");
    println!("  :solve [<cnf>] [as <sol>]   solve named Cnf (no arg = *default), save solution");
    println!("  :query <expr> [in <sol>]    evaluate against named solution (no in = *default)");
    println!("    NOTE: `in` collides with Alloy `in`; the trailing `in <sol>` is used only");
    println!("    when <sol> names a stored solution, else the whole text is the expression.");
    println!("    Use `@ <sol>` as an unambiguous alternative: `:query A @ someA`.");
    println!("  :validate <sol> [in <cnf>]  validate solution vs Cnf (no in = its origin Cnf)");
    println!("  :show [name] [N]            show Cnf clauses and/or solution (no arg = defaults)");
    println!("  :eval <expr> [as <sol>]     satisfiability check (bare expr lifts with some)");
    println!("  <expr>                    bare line: :eval (never stored)");
    println!("commands:");
    println!("  :load <file>        load .als model (fragments + stores cleared)");
    println!("  :list               list run/check commands in the module");
    println!("  :cnfs               list saved Cnfs (* = default)");
    println!("  :sols               list saved solutions (* = default)");
    println!("  :use <name>         switch default to a Cnf and/or solution");
    println!("  :fragments          list entered fragments");
    println!("  :drop <i>           delete fragment by index, rebuild (stores cleared)");
    println!("  :save <file> [in <sol>] [rels...]  write solution as Alloy pin fact");
    println!("  :add <file>         load a file back as a fragment (replaces same pin)");
    println!("  :psave <file> [in <sol>] [rels...] write solution as binary partial (.apin)");
    println!("  :pread <file>       inspect a binary partial (no solving)");
    println!("  :ppin <file> [rels...] [to <cnf>] [as <sol>] [gated]");
    println!("                       pin a binary partial onto a Cnf, solve once");
    println!("  :pavoid <file> [rels...] [to <cnf>] [as <sol>] [gated]");
    println!("                       exclude a binary partial (nogood), solve once");
    println!("  :reset              drop entered fragments, keep :load file (stores cleared)");
    println!("  :help               this help");
    println!("  :quit               exit (Ctrl-D also exits)");
    println!("notes: `let` works inside pred/fun bodies and :eval/:query expressions.");
}

/// Reference form for a pool relation name inside an emitted pin fact.
///
/// Plain sig names emit as-is. `Owner.field` emits as bare `field` iff that
/// name is unambiguous (exactly one dotted owner, and no top-level relation
/// already uses it): dotted syntax would parse as a join, not a reference.
/// Anything else (slashes, ambiguity) yields `None` (skip with notice).
fn pin_ref(all_names: &[String], name: &str) -> Option<String> {
    if name.contains('/') {
        return None;
    }
    let (_, field) = match name.split_once('.') {
        None => return Some(name.to_string()),
        Some((_, f)) if !f.contains('/') => ((), f),
        Some(_) => return None,
    };
    let owners = all_names
        .iter()
        .filter(|n| n.rsplit('.').next() == Some(field))
        .count();
    let bare_taken = all_names.iter().any(|n| n == field);
    if owners == 1 && !bare_taken {
        Some(field.to_string())
    } else {
        None
    }
}

/// Resolve an explicit `:save` relation argument: exact pool name first,
/// then a unique bare field name.
fn unique_bare_field(all_names: &[String], want: &str) -> Option<String> {
    let mut hits = all_names
        .iter()
        .filter(|n| n.rsplit('.').next() == Some(want) && !n.contains('/') && *n != want);
    match (hits.next(), hits.next()) {
        (Some(one), None) => Some(one.clone()),
        _ => None,
    }
}

fn first_token(s: &str) -> &str {
    s.split_whitespace().next().unwrap_or("")
}

fn second_token(s: &str) -> &str {
    s.split_whitespace().nth(1).unwrap_or("")
}

/// `sig`/`pred`/…-style declaration (excluding bare `run`/`check`, which go
/// through build-or-add). `one`/`lone`/`some`/`var` count only before `sig`.
fn looks_like_decl(s: &str) -> bool {
    match first_token(s) {
        "sig" | "abstract" | "fact" | "pred" | "fun" | "assert" | "open" => true,
        "one" | "lone" | "some" | "var" => second_token(s) == "sig",
        _ => false,
    }
}

fn brace_delta(s: &str) -> i32 {
    let code = s.split("//").next().unwrap_or("");
    let code = code.split("--").next().unwrap_or(code);
    code.chars().filter(|&c| c == '{').count() as i32
        - code.chars().filter(|&c| c == '}').count() as i32
}

fn is_valid_name(n: &str) -> bool {
    !n.is_empty()
        && n.chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '#' | '-'))
}

/// Split trailing `as <name>`: returns (head_tokens, as_name).
fn split_as<'a>(rest: &[&'a str]) -> (Vec<&'a str>, Option<&'a str>) {
    if let Some(pos) = rest.iter().position(|&t| t == "as") {
        let head = rest[..pos].to_vec();
        let tail = &rest[pos + 1..];
        if tail.len() == 1 {
            (head, Some(tail[0]))
        } else {
            // Malformed: let the caller emit usage. Encode by returning a
            // sentinel head that cannot resolve.
            (head, Some("__bad_as__"))
        }
    } else {
        (rest.to_vec(), None)
    }
}

/// Split a `:query` body into (expr, sol). The trailing `in <sol>` / `@ <sol>`
/// is honored only when `<sol>` is a single token; ambiguity with Alloy `in`
/// is resolved by the caller checking the solution store.
fn split_query_in<'a>(sess: &Session, body: &'a str) -> (&'a str, Option<&'a str>) {
    let toks: Vec<&str> = body.split_whitespace().collect();
    // Unambiguous `@` separator first.
    if let Some(pos) = toks.iter().rposition(|&t| t == "@") {
        if pos + 1 == toks.len() - 1 && pos > 0 {
            let cut = body.rfind('@').unwrap();
            return (body[..cut].trim(), Some(toks[pos + 1]));
        }
        return (body, None);
    }
    // `in`: use only if the trailing token names a stored solution.
    if let Some(pos) = toks.iter().rposition(|&t| t == "in") {
        if pos + 1 == toks.len() - 1 && pos > 0 {
            let cand = toks[pos + 1];
            if sess.sols.contains_key(cand) {
                // Re-cut on the last " in " occurrence.
                if let Some(cut) = body.rmatch_indices(" in ").next().map(|(i, _)| i) {
                    let expr = body[..cut].trim();
                    if !expr.is_empty() {
                        return (expr, Some(cand));
                    }
                }
            }
        }
    }
    (body, None)
}

/// Split `:save` args into (file, sol, rels).
/// Forms: `<file>`, `<file> in <sol>`, either followed by relation names
/// (`+` tokens ignored, so `A + B` and `A B` agree).
fn parse_save_args<'a>(
    rest: &[&'a str],
) -> Result<(&'a str, Option<&'a str>, Vec<&'a str>), &'static str> {
    const USAGE: &str = "usage: :save <file> [in <sol>] [rels...]";
    if rest.is_empty() {
        return Err(USAGE);
    }
    let file = rest[0];
    let (sol, rels) = if rest.get(1) == Some(&"in") {
        if rest.len() < 3 {
            return Err(USAGE);
        }
        (Some(rest[2]), &rest[3..])
    } else {
        (None, &rest[1..])
    };
    // Relation names may be space- and/or `+`-separated (`B f`, `B+f`,
    // `B + f` all agree); `+` never occurs inside a name.
    let rels = rels
        .iter()
        .flat_map(|t| t.split('+'))
        .filter(|t| !t.is_empty())
        .collect();
    Ok((file, sol, rels))
}

/// Read and decode a binary partial instance file.
fn read_partial(file: &str) -> Result<PartialInstance, String> {
    let bytes = std::fs::read(file).map_err(|e| format!("cannot read {file}: {e}"))?;
    PartialInstance::decode(&bytes).map_err(|e| format!("{file}: {e}"))
}

/// One-line partial summary (`A + B (3 rels, 2 ints)`).
fn partial_summary(p: &PartialInstance) -> String {
    let mut s = if p.rels.is_empty() {
        "no relations".to_string()
    } else {
        p.rels
            .iter()
            .map(|r| r.name.clone())
            .collect::<Vec<_>>()
            .join(" + ")
    };
    s.push_str(&format!(" ({} rels, {} ints)", p.rels.len(), p.ints.len()));
    s
}

/// Parsed `:ppin`/`:pavoid` arguments.
struct PpinArgs<'a> {
    file: &'a str,
    rels: Vec<&'a str>,
    cnf: Option<&'a str>,
    sol: Option<&'a str>,
    gated: bool,
}

/// Split `:ppin`/`:pavoid` args: `<file> [rels...] [to <cnf>] [as <sol>] [gated]`.
/// Relation names may be `+`-joined (`B+f`, `B + f`, `B f` all agree).
/// `to`/`as`/`gated` are reserved words here (as with `in`/`as` elsewhere).
fn parse_ppin_args<'a>(
    rest: &[&'a str],
    usage: &'static str,
) -> Result<PpinArgs<'a>, &'static str> {
    if rest.is_empty() {
        return Err(usage);
    }
    let file = rest[0];
    let mut rels = Vec::new();
    let mut cnf = None;
    let mut sol = None;
    let mut gated = false;
    let mut i = 1;
    while i < rest.len() {
        match rest[i] {
            "to" => {
                i += 1;
                cnf = Some(*rest.get(i).ok_or(usage)?);
            }
            "as" => {
                i += 1;
                sol = Some(*rest.get(i).ok_or(usage)?);
            }
            "gated" => gated = true,
            t => {
                for part in t.split('+') {
                    if !part.is_empty() {
                        rels.push(part);
                    }
                }
            }
        }
        i += 1;
    }
    Ok(PpinArgs {
        file,
        rels,
        cnf,
        sol,
        gated,
    })
}

/// Split a `:validate` body into (sol, cnf). Forms: `<sol>`, `<sol> in <cnf>`,
/// `<sol> @ <cnf>`.
fn split_validate<'a>(rest: &[&'a str]) -> (Option<&'a str>, Option<&'a str>) {
    if rest.is_empty() {
        return (None, None);
    }
    if let Some(pos) = rest.iter().position(|&t| t == "in" || t == "@") {
        if pos == 0 || rest.len() != pos + 2 {
            return (Some("__bad__"), Some("__bad__"));
        }
        (Some(rest[0]), Some(rest[pos + 1]))
    } else if rest.len() == 1 {
        (Some(rest[0]), None)
    } else {
        (Some("__bad__"), Some("__bad__"))
    }
}

const BARE_COMMANDS: &[&str] = &[
    "help",
    "h",
    "?",
    "quit",
    "exit",
    "q",
    "load",
    "l",
    "list",
    "ls",
    "fragments",
    "drop",
    "save",
    "add",
    "psave",
    "pread",
    "ppin",
    "pavoid",
    "solve",
    "s",
    "validate",
    "v",
    "show",
    "reset",
    "cnfs",
    "sols",
    "use",
    "query",
    "eval",
];

fn main() {
    let cli = Cli::parse();
    let mut sess = Session::new();
    if let Some(path) = cli.file {
        sess.load_file(&path);
    } else {
        println!("alloy-repl: type declarations, :load <file>, :help for commands.");
    }

    let mut rl = DefaultEditor::new().unwrap_or_else(|e| {
        eprintln!("rustyline init failed: {e}");
        std::process::exit(1);
    });
    let _ = rl.load_history(".alloy_repl_history");

    loop {
        let prompt = if sess.pending.is_some() {
            "... "
        } else {
            "alloy> "
        };
        let line = match rl.readline(prompt) {
            Ok(l) => l,
            Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => break,
            Err(e) => {
                eprintln!("read error: {e}");
                break;
            }
        };
        let trimmed = line.trim();
        // Blank line submits a pending multi-line input, else ignored.
        if trimmed.is_empty() {
            if let Some(pending) = sess.pending.take() {
                let _ = rl.add_history_entry(pending.text.clone());
                sess.submit_pending(pending);
            }
            continue;
        }
        if sess.pending.is_none() && (trimmed.starts_with("--") || trimmed.starts_with("//")) {
            continue;
        }
        let _ = rl.add_history_entry(line.clone());

        // A `:command` line submits any pending input first, then runs.
        if sess.pending.is_some() && trimmed.starts_with(':') {
            if let Some(pending) = sess.pending.take() {
                sess.submit_pending(pending);
            }
        }
        // Continuation of a pending multi-line input.
        if let Some(mut pending) = sess.pending.take() {
            pending.text.push('\n');
            pending.text.push_str(trimmed);
            pending.depth += brace_delta(trimmed);
            if pending.depth <= 0 {
                sess.submit_pending(pending);
            } else {
                sess.pending = Some(pending);
            }
            continue;
        }

        // Explicit `:command`.
        if let Some(body) = trimmed.strip_prefix(':') {
            let mut parts = body.split_whitespace();
            let cmd = parts.next().unwrap_or("");
            // NOTE: parts borrows body; collect the rest before &mut sess calls.
            let rest: Vec<&str> = parts.collect();
            let arg = rest.first().copied();
            match cmd {
                "help" | "h" | "?" => print_help(),
                "quit" | "exit" | "q" => break,
                "load" | "l" => match arg {
                    Some(p) => sess.load_file(p),
                    None => println!("usage: :load <file.als>"),
                },
                "list" | "ls" => sess.list_commands(),
                "cnfs" => sess.list_cnfs(),
                "sols" => sess.list_sols(),
                "use" => match arg {
                    Some(n) => sess.do_use(n),
                    None => println!("usage: :use <cnf|sol>"),
                },
                "fragments" => sess.list_fragments(),
                "drop" => {
                    if rest.len() != 1 {
                        println!("usage: :drop <fragment-index> (:fragments to list)");
                    } else {
                        sess.drop_fragment(arg);
                    }
                }
                "save" => match parse_save_args(&rest) {
                    Ok((file, sol, rels)) => sess.do_save(file, sol, &rels),
                    Err(usage) => println!("{usage}"),
                },
                "add" => match arg {
                    Some(p) => sess.do_add(p),
                    None => println!("usage: :add <file>"),
                },
                "psave" => match parse_save_args(&rest) {
                    Ok((file, sol, rels)) => sess.do_psave(file, sol, &rels),
                    Err(usage) => println!("{usage}"),
                },
                "pread" => match arg {
                    Some(p) => sess.do_pread(p),
                    None => println!("usage: :pread <file>"),
                },
                "ppin" => match parse_ppin_args(
                    &rest,
                    "usage: :ppin <file> [rels...] [to <cnf>] [as <sol>] [gated]",
                ) {
                    Ok(a) => sess.do_ppin(a.file, &a.rels, a.cnf, a.sol, a.gated),
                    Err(usage) => println!("{usage}"),
                },
                "pavoid" => match parse_ppin_args(
                    &rest,
                    "usage: :pavoid <file> [rels...] [to <cnf>] [as <sol>] [gated]",
                ) {
                    Ok(a) => sess.do_pavoid(a.file, &a.rels, a.cnf, a.sol, a.gated),
                    Err(usage) => println!("{usage}"),
                },
                "reset" => {
                    sess.fragments.clear();
                    sess.rebuild("reset");
                }
                "run" | "check" => {
                    let kind = if cmd == "run" {
                        CnfKind::Run
                    } else {
                        CnfKind::Check
                    };
                    let (head, as_name) = split_as(&rest);
                    if as_name == Some("__bad_as__") || head.len() > 1 {
                        println!("usage: :{cmd} <index|name> [as <cnf>]");
                    } else {
                        sess.do_build(kind, head.first().copied(), as_name);
                    }
                }
                "solve" | "s" => {
                    let (head, as_name) = split_as(&rest);
                    if as_name == Some("__bad_as__") || head.len() > 1 {
                        println!("usage: :solve [<cnf>] [as <sol>]");
                    } else {
                        sess.do_solve(head.first().copied(), as_name);
                    }
                }
                "validate" | "v" => {
                    let (sol, cnf) = split_validate(&rest);
                    if sol == Some("__bad__") {
                        println!("usage: :validate <sol> [in <cnf>]");
                    } else {
                        sess.do_validate(sol, cnf);
                    }
                }
                "show" => sess.do_show(&rest),
                "eval" => {
                    let raw = body["eval".len()..].trim();
                    if raw.is_empty() {
                        println!("usage: :eval <expr|formula> [as <sol>]");
                    } else {
                        // Split trailing `as <sol>` on the raw text.
                        let toks: Vec<&str> = raw.split_whitespace().collect();
                        let (_head, as_name) = split_as(&toks);
                        if as_name == Some("__bad_as__") {
                            println!("usage: :eval <expr|formula> [as <sol>]");
                        } else {
                            let cut = if as_name.is_some() {
                                raw.rmatch_indices(" as ").next().map(|(i, _)| i)
                            } else {
                                None
                            };
                            let expr = match cut {
                                Some(i) => raw[..i].trim(),
                                None => raw,
                            };
                            if expr.is_empty() {
                                println!("usage: :eval <expr|formula> [as <sol>]");
                            } else {
                                let owned = as_name.map(|s| s.to_string());
                                start_or_submit(&mut sess, InputKind::Eval, expr, owned);
                            }
                        }
                    }
                }
                "query" => {
                    let raw = body["query".len()..].trim();
                    if raw.is_empty() {
                        println!("usage: :query <expr> [in <sol>]");
                    } else {
                        let (expr, sol) = split_query_in(&sess, raw);
                        let owned = sol.map(|s| s.to_string());
                        start_or_submit(&mut sess, InputKind::Query, expr, owned);
                    }
                }
                _ => println!("unknown command `:{cmd}` (:help for list)"),
            }
            continue;
        }

        // Bare line: explicit command name without colon (legacy).
        let head = first_token(trimmed);
        if BARE_COMMANDS.contains(&head) {
            let mut parts = trimmed.split_whitespace();
            let cmd = parts.next().unwrap_or("");
            let rest: Vec<&str> = parts.collect();
            let arg = rest.first().copied();
            // Recompute the raw tail for query/eval (they take free-form text).
            let tail = trimmed[cmd.len()..].trim();
            match cmd {
                "help" | "h" | "?" => print_help(),
                "quit" | "exit" | "q" => break,
                "load" | "l" => match arg {
                    Some(p) => sess.load_file(p),
                    None => println!("usage: :load <file.als>"),
                },
                "list" | "ls" => sess.list_commands(),
                "cnfs" => sess.list_cnfs(),
                "sols" => sess.list_sols(),
                "use" => match arg {
                    Some(n) => sess.do_use(n),
                    None => println!("usage: :use <cnf|sol>"),
                },
                "fragments" => sess.list_fragments(),
                "drop" => {
                    if rest.len() != 1 {
                        println!("usage: drop <fragment-index> (:fragments to list)");
                    } else {
                        sess.drop_fragment(arg);
                    }
                }
                "save" => match parse_save_args(&rest) {
                    Ok((file, sol, rels)) => sess.do_save(file, sol, &rels),
                    Err(usage) => println!("{usage}"),
                },
                "add" => match arg {
                    Some(p) => sess.do_add(p),
                    None => println!("usage: add <file>"),
                },
                "psave" => match parse_save_args(&rest) {
                    Ok((file, sol, rels)) => sess.do_psave(file, sol, &rels),
                    Err(usage) => println!("{usage}"),
                },
                "pread" => match arg {
                    Some(p) => sess.do_pread(p),
                    None => println!("usage: pread <file>"),
                },
                "ppin" => match parse_ppin_args(
                    &rest,
                    "usage: ppin <file> [rels...] [to <cnf>] [as <sol>] [gated]",
                ) {
                    Ok(a) => sess.do_ppin(a.file, &a.rels, a.cnf, a.sol, a.gated),
                    Err(usage) => println!("{usage}"),
                },
                "pavoid" => match parse_ppin_args(
                    &rest,
                    "usage: pavoid <file> [rels...] [to <cnf>] [as <sol>] [gated]",
                ) {
                    Ok(a) => sess.do_pavoid(a.file, &a.rels, a.cnf, a.sol, a.gated),
                    Err(usage) => println!("{usage}"),
                },
                "reset" => {
                    sess.fragments.clear();
                    sess.rebuild("reset");
                }
                "solve" | "s" => {
                    let (head, as_name) = split_as(&rest);
                    if as_name == Some("__bad_as__") || head.len() > 1 {
                        println!("usage: solve [<cnf>] [as <sol>]");
                    } else {
                        sess.do_solve(head.first().copied(), as_name);
                    }
                }
                "validate" | "v" => {
                    let (sol, cnf) = split_validate(&rest);
                    if sol == Some("__bad__") {
                        println!("usage: validate <sol> [in <cnf>]");
                    } else {
                        sess.do_validate(sol, cnf);
                    }
                }
                "show" => sess.do_show(&rest),
                "eval" => {
                    if tail.is_empty() {
                        println!("usage: eval <expr|formula> [as <sol>]");
                    } else {
                        let toks: Vec<&str> = tail.split_whitespace().collect();
                        let (_head, as_name) = split_as(&toks);
                        if as_name == Some("__bad_as__") {
                            println!("usage: eval <expr|formula> [as <sol>]");
                        } else {
                            let cut = match as_name {
                                Some(_) => tail.rmatch_indices(" as ").next().map(|(i, _)| i),
                                None => None,
                            };
                            let expr = match cut {
                                Some(i) => tail[..i].trim(),
                                None => tail,
                            };
                            let owned = as_name.map(|s| s.to_string());
                            start_or_submit(&mut sess, InputKind::Eval, expr, owned);
                        }
                    }
                }
                "query" => {
                    if tail.is_empty() {
                        println!("usage: query <expr> [in <sol>]");
                    } else {
                        let (expr, sol) = split_query_in(&sess, tail);
                        let owned = sol.map(|s| s.to_string());
                        start_or_submit(&mut sess, InputKind::Query, expr, owned);
                    }
                }
                _ => println!("unknown command `{cmd}` (:help for list)"),
            }
            continue;
        }

        // Bare `run`/`check`: build when it names a command, else a fragment.
        if head == "run" || head == "check" {
            let toks: Vec<&str> = trimmed.split_whitespace().collect();
            // toks[0] is run|check; support optional trailing `as <cnf>`.
            let tail = &toks[1..];
            let (head_t, as_name) = split_as(tail);
            let kind = if head == "run" {
                CnfKind::Run
            } else {
                CnfKind::Check
            };
            let arg_owned: Option<String> = head_t.first().map(|s| s.to_string());
            if as_name == Some("__bad_as__") || head_t.len() > 1 {
                start_or_submit(&mut sess, InputKind::Decl, trimmed, None);
            } else if sess.module.is_some() && sess.resolve_index(arg_owned.as_deref()).is_ok() {
                sess.do_build(kind, arg_owned.as_deref(), as_name);
            } else if sess.module.is_none() {
                println!("no module loaded");
            } else {
                start_or_submit(&mut sess, InputKind::Decl, trimmed, None);
            }
            continue;
        }

        // Declaration fragment vs bare expression.
        if looks_like_decl(trimmed) {
            start_or_submit(&mut sess, InputKind::Decl, trimmed, None);
        } else {
            start_or_submit(&mut sess, InputKind::Bare, trimmed, None);
        }
    }
    let _ = rl.save_history(".alloy_repl_history");
    println!("bye");
}

/// Begin (or immediately submit) a multi-line input.
fn start_or_submit(sess: &mut Session, kind: InputKind, text: &str, target: Option<String>) {
    let depth = brace_delta(text);
    if depth <= 0 {
        let pending = Pending {
            kind,
            text: text.to_string(),
            depth: 0,
            target,
        };
        sess.submit_pending(pending);
    } else {
        sess.pending = Some(Pending {
            kind,
            text: text.to_string(),
            depth,
            target,
        });
    }
}
