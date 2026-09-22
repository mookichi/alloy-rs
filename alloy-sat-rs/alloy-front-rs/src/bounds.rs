//! Scope resolution: turns a command's scope clause into concrete sig
//! population bounds and the universe atom table.
//!
//! Naming matches the Java engine (`Book$0`, int atoms `-8`..`7`) so
//! results stay comparable with the Java oracle.

use crate::ast::{Module, Scope, ScopeEntry, SigMult, SigRel};
use alloy_kodkod_rs::bounds::Bounds;
use alloy_kodkod_rs::relation::RelationId;
use alloy_kodkod_rs::tuple::Tuple;
use alloy_kodkod_rs::tupleset::TupleSet;
use alloy_kodkod_rs::universe::Universe;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

pub const DEFAULT_SCOPE: u32 = 3;

/// Bit-lane group ids for the builtin `EReal` lanes in the kodkod
/// int-bound group registry (`Bounds::bound_exactly_int_in`).
/// Group 0 stays the builtin `Int` namespace.
pub const LANE_M: u32 = 1;
pub const LANE_E: u32 = 2;
pub const LANE_P: u32 = 3;
pub const LANE_K: u32 = 4;

/// Builtin `EReal` field lanes: (field name, bit-lane group).
/// Lane atoms live in `Resolved::lane_atoms[group]` (bit positions,
/// value = index, two's-complement MSB reading via `BitsIn`).
pub const EREAL_LANES: [(&str, u32); 4] =
    [("m", LANE_M), ("e", LANE_E), ("p", LANE_P), ("k", LANE_K)];

/// Builtin `EReal` operation/predicate names that imply EReal allocation
/// when called (mirrors the `util/mepk` library surface).
pub const EREAL_OPS: &[&str] = &[
    "erealAdd",
    "erealSub",
    "erealMul",
    "erealDiv",
    "erealWellformed",
    "erealDivGuard",
    "erealNeedsRefine",
    "erealCombineK",
    "erealLsb",
    "erealRadiusExp",
    "erealTau",
    "setEReal",
];

#[derive(Debug)]
pub struct SigInfo {
    #[allow(dead_code)]
    pub name: String,
    #[allow(dead_code)]
    pub parent: Option<String>,
    #[allow(dead_code)]
    pub rel: SigRel,
    #[allow(dead_code)]
    pub mult: SigMult,
    /// Concrete atoms allocated for THIS sig (empty for abstract parents).
    pub atoms: Vec<String>,
}

pub struct Resolved {
    pub universe: Arc<Universe>,
    /// Circuit width `E = min(W, 30)` (drives Kodkod `set_bitwidth`).
    pub bitwidth: u32,
    /// Int atom count `W` (atoms `{0, .., W-1}`).
    pub int_count: u32,
    /// Step atoms `{Step$0, ..}` (empty in static commands).
    pub step_atoms: Vec<String>,
    pub sigs: HashMap<String, SigInfo>,
    /// Every declared sig relation (sig name -> relation).
    #[allow(dead_code)]
    pub sig_rel: HashMap<String, RelationId>,
    /// Atoms reachable through each sig including descendants (for typing).
    pub closure_atoms: HashMap<String, Vec<String>>,
    /// For `in` children: atoms are a subset of parent's atoms.
    pub in_children_atoms: HashMap<String, Vec<String>>,
    /// Builtin `EReal` atoms (`EReal$0, ..`; empty unless the module uses
    /// `EReal`, mirroring lazy Int allocation).
    pub ereal_atoms: Vec<String>,
    /// Allocated `EReal` population (`for N EReal`, else default scope).
    /// Informational (atom list is authoritative); kept for scope
    /// introspection and future `exactly` handling.
    #[allow(dead_code)]
    pub ereal_count: u32,
    /// Bit-lane atoms by group (`LANE_M/E/P/K`): bit positions whose
    /// value is the index (two's-complement MSB reading via `BitsIn`).
    /// Empty unless `EReal` is used.
    pub lane_atoms: HashMap<u32, Vec<String>>,
    /// Lane widths from the `for n Int` rule (+ `MEPK_*_WIDTH` overrides).
    /// Stored for lowering/display introspection.
    #[allow(dead_code)]
    pub mepk_widths: alloy_kodkod_rs::mepk::MepkWidths,
}

impl Resolved {
    /// All atoms of a sig including its subtree (children, recursively).
    pub fn atoms_of(&self, name: &str) -> Vec<String> {
        self.closure_atoms.get(name).cloned().unwrap_or_default()
    }
}

fn build_scope_map(
    module: &Module,
    scope: &Scope,
) -> (HashMap<String, (u32, bool)>, u32, u32, u32, bool) {
    let mut m: HashMap<String, (u32, bool)> = HashMap::new();
    for (name, e) in &scope.entries {
        match e {
            ScopeEntry::Num(n) => {
                m.insert(name.clone(), (*n, false));
            }
            ScopeEntry::Exactly(n) => {
                m.insert(name.clone(), (*n, true));
            }
        }
    }
    let overall = scope.overall.unwrap_or(DEFAULT_SCOPE);
    // Bit-vector model: `for W Int` (else 4) gives W atoms `{0, .., W-1}`
    // with W-bit circuits capped at 30 (`E = min(W, 30)`). Int atoms are
    // allocated lazily: models that never mention Int as a set pay zero
    // universe cost.
    let bitwidth = crate::ast::effective_bitwidth(module, scope);
    let int_count = crate::ast::effective_int_count(scope);
    let needs_int = crate::ast::module_needs_int_atoms(module, scope);
    (m, overall, bitwidth, int_count, needs_int)
}

/// Sigs that transitively `extend` the builtin `EReal` (through
/// `extends`-links only; `in`-children are handled separately).
/// Fixed point so declaration order does not matter.
pub fn ereal_extenders(module: &Module) -> HashSet<String> {
    let mut out: HashSet<String> = HashSet::new();
    loop {
        let mut grew = false;
        for sd in &module.sigs {
            if sd.rel == SigRel::In {
                continue;
            }
            if let Some(p) = &sd.extends {
                if p == "EReal" || out.contains(p) {
                    for n in &sd.names {
                        if out.insert(n.clone()) {
                            grew = true;
                        }
                    }
                }
            }
        }
        if !grew {
            break;
        }
    }
    out
}

/// True when the module mentions the builtin `EReal` (as a type, a scope
/// entry, or an `ereal*` operation call). Conservative: any textual
/// mention allocates (harmless over-approximation); a missed mention
/// would fail loudly at lowering instead.
fn module_mentions_ereal(module: &Module, scope: &Scope) -> bool {
    use crate::ast::{Expr, Formula, IntExpr};
    if scope.entries.iter().any(|(n, _)| n == "EReal") {
        return true;
    }
    fn expr_mentions(e: &Expr, hit: &mut bool) {
        if *hit {
            return;
        }
        match e {
            Expr::Name(n, _) if n == "EReal" => *hit = true,
            Expr::Name(..) | Expr::Univ | Expr::None_ | Expr::Iden | Expr::IntAtom
            | Expr::StepAtom | Expr::Bits(..) | Expr::RealLit(..) => {}
            Expr::Bin(_, a, b) => {
                expr_mentions(a, hit);
                expr_mentions(b, hit);
            }
            Expr::Transpose(x) | Expr::TClosure(x) | Expr::RClosure(x) | Expr::Prime(x)
            | Expr::AtExpr(x) | Expr::ArrowMult(_, x) | Expr::LeadMult(_, x) => {
                expr_mentions(x, hit)
            }
            Expr::Comprehension(ds, body) => {
                for d in ds {
                    expr_mentions(&d.expr, hit);
                }
                formula_mentions(body, hit);
            }
            Expr::If(c, t, el) => {
                formula_mentions(c, hit);
                expr_mentions(t, hit);
                expr_mentions(el, hit);
            }
            Expr::Bracket(base, args) => {
                expr_mentions(base, hit);
                for a in args {
                    expr_mentions(a, hit);
                }
            }
            Expr::Call(name, args, _) => {
                if name == "EReal" || EREAL_OPS.contains(&name.as_str()) {
                    *hit = true;
                    return;
                }
                for a in args {
                    expr_mentions(a, hit);
                }
            }
            Expr::LetBind(binds, body) => {
                for (_, ex) in binds {
                    expr_mentions(ex, hit);
                }
                expr_mentions(body, hit);
            }
        }
    }
    fn intexpr_mentions(e: &IntExpr, hit: &mut bool) {
        match e {
            IntExpr::Lit(..) => {}
            IntExpr::Card(x, _) | IntExpr::Val(x, _) | IntExpr::BitsVal(x, _)
            | IntExpr::SumOf(x, _) => expr_mentions(x, hit),
            IntExpr::Bin(_, a, b) => {
                intexpr_mentions(a, hit);
                intexpr_mentions(b, hit);
            }
            IntExpr::Sum(ds, body, _) => {
                for d in ds {
                    expr_mentions(&d.expr, hit);
                }
                intexpr_mentions(body, hit);
            }
        }
    }
    fn formula_mentions(f: &Formula, hit: &mut bool) {
        if *hit {
            return;
        }
        match f {
            Formula::Const(_) | Formula::Pin(..) | Formula::BadIn(..) => {}
            Formula::Cmp(_, a, b, _) => {
                expr_mentions(a, hit);
                expr_mentions(b, hit);
            }
            Formula::IntCmp(_, a, b, _) => {
                intexpr_mentions(a, hit);
                intexpr_mentions(b, hit);
            }
            Formula::Quant(_, ds, body) | Formula::MaxSomeDecl(ds, body) => {
                for d in ds {
                    expr_mentions(&d.expr, hit);
                }
                formula_mentions(body, hit);
            }
            Formula::Multi(_, e, _) => expr_mentions(e, hit),
            Formula::MaxSome(e) | Formula::MinSome(e) => expr_mentions(e, hit),
            Formula::Maximize(e) | Formula::Minimize(e) => intexpr_mentions(e, hit),
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b)
            | Formula::Iff(a, b) | Formula::Until(a, b) | Formula::Releases(a, b)
            | Formula::Since(a, b) | Formula::Triggered(a, b) => {
                formula_mentions(a, hit);
                formula_mentions(b, hit);
            }
            Formula::Not(x)
            | Formula::Always(x)
            | Formula::Eventually(x)
            | Formula::Before(x)
            | Formula::Historically(x)
            | Formula::Once(x)
            | Formula::Keeping(x)
            | Formula::Goal(x)
            | Formula::Restore(x)
            | Formula::Initially(x)
            | Formula::Regularly(x)
            | Formula::Consistently(x)
            | Formula::OverflowCond(_, x) => formula_mentions(x, hit),
            Formula::LetBind(binds, body) => {
                for (_, ex) in binds {
                    expr_mentions(ex, hit);
                }
                formula_mentions(body, hit);
            }
            Formula::Call(name, args, _) => {
                if name == "EReal" || EREAL_OPS.contains(&name.as_str()) {
                    *hit = true;
                    return;
                }
                for a in args {
                    expr_mentions(a, hit);
                }
            }
        }
    }
    let mut hit = false;
    for sd in &module.sigs {
        if sd.extends.as_deref() == Some("EReal") {
            return true;
        }
        for d in &sd.fields {
            expr_mentions(&d.expr, &mut hit);
        }
        if let Some(f) = &sd.fact {
            formula_mentions(f, &mut hit);
        }
        if hit {
            return true;
        }
    }
    for (_, f) in module.facts.iter().chain(module.soft_facts.iter()) {
        formula_mentions(f, &mut hit);
        if hit {
            return true;
        }
    }
    for p in &module.paras {
        formula_mentions(&p.body, &mut hit);
        if let Some(e) = &p.body_expr {
            expr_mentions(e, &mut hit);
        }
        for d in &p.params {
            expr_mentions(&d.expr, &mut hit);
        }
        if hit {
            return true;
        }
    }
    for pd in &module.partials {
        for e in &pd.entries {
            expr_mentions(&e.left, &mut hit);
            expr_mentions(&e.right, &mut hit);
        }
        if hit {
            return true;
        }
    }
    hit
}

/// Resolves scopes into universe + per-sig atom allocations.
pub fn resolve(module: &Module, scope: &Scope) -> Result<Resolved, String> {
    let (user, overall, bitwidth, int_count, needs_int) = build_scope_map(module, scope);
    let mepk_widths =
        alloy_kodkod_rs::mepk::MepkWidths::from_env(int_count).map_err(|e| format!("mepk: {e}"))?;
    let needs_ereal = module_mentions_ereal(module, scope);
    // Lane widths must fit the problem circuit width, but only when lanes
    // are actually allocated: wider lanes would misread (top bits wrap
    // mod 2^E). Point at the Int scope for relief.
    if needs_ereal {
        for (name, w) in [
            ("MEPK_M_WIDTH", mepk_widths.m_width),
            ("MEPK_E_WIDTH", mepk_widths.e_width),
            ("MEPK_P_WIDTH", mepk_widths.p_width),
            ("MEPK_K_WIDTH", mepk_widths.k_width),
        ] {
            if w > bitwidth {
                return Err(format!(
                    "{name}={w} exceeds problem bitwidth {bitwidth}; lane values would wrap. \
                     Raise it via `for N Int` (need E >= {w}) or lower {name}"
                ));
            }
        }
    }
    let ereal_count = scope
        .entries
        .iter()
        .find(|(n, _)| n == "EReal")
        .map(|(_, e)| match e {
            ScopeEntry::Num(n) | ScopeEntry::Exactly(n) => *n,
        })
        .unwrap_or(DEFAULT_SCOPE);
    // `EReal` is a reserved builtin: user declarations are rejected
    // (extension is allowed: `in` shares atoms, `extends` partitions).
    for sd in &module.sigs {
        if sd.names.iter().any(|n| n == "EReal") {
            return Err("sig EReal is reserved by the builtin EReal signature".to_string());
        }
    }

    // index declarations
    let mut parents: HashMap<&str, Option<String>> = HashMap::new();
    let mut children: HashMap<String, Vec<String>> = HashMap::new();
    let mut mults: HashMap<&str, SigMult> = HashMap::new();
    let mut sig_rels: HashMap<&str, SigRel> = HashMap::new();
    let mut all_names: Vec<String> = Vec::new();
    for sd in &module.sigs {
        for n in &sd.names {
            if parents.insert(n.as_str(), sd.extends.clone()).is_some() {
                return Err(format!("duplicate sig {n}"));
            }
            mults.insert(n.as_str(), sd.mult);
            sig_rels.insert(n.as_str(), sd.rel);
            all_names.push(n.clone());
            if let Some(p) = &sd.extends {
                if p == "Int" || p == "Signed" {
                    // Java parity (verified against the Java frontend with
                    // Version.experimental=true): `extends Int` is rejected,
                    // while `in Int` (subset of the builtin Int) is accepted.
                    // `Signed` mirrors `Int` exactly (same atoms).
                    if sd.rel != SigRel::In {
                        return Err(format!(
                            "sig {n} cannot extend the builtin \"{p}\" signature"
                        ));
                    }
                    children.entry(p.clone()).or_default().push(n.clone());
                } else if p == "EReal" {
                    // Builtin `EReal`: `in EReal` accepted (subset of the
                    // EReal atoms); `extends EReal` accepted with Alloy
                    // partition semantics (subset + disjoint siblings +
                    // parent covered by extenders; membership constraints
                    // in lower.rs, shared upper bounds below).
                    children.entry(p.clone()).or_default().push(n.clone());
                } else {
                    if !all_names.iter().any(|x| x == p)
                        && module.sigs.iter().all(|s| !s.names.contains(p))
                    {
                        return Err(format!("sig {n} extends unknown parent {p}"));
                    }
                    children.entry(p.clone()).or_default().push(n.clone());
                }
            }
        }
    }

    // allocation: process hierarchies top-down
    // For `sig in`, the child does NOT allocate its own atoms; it shares
    // the parent's atoms (subset constraint added as formula in lower.rs).
    let mut atoms_of: HashMap<String, Vec<String>> = HashMap::new();

    fn is_root(parents: &HashMap<&str, Option<String>>, n: &str) -> bool {
        parents.get(n).map(|p| p.is_none()).unwrap_or(true)
    }

    let mut roots: Vec<String> = all_names
        .iter()
        .filter(|n| is_root(&parents, n))
        .cloned()
        .collect();

    // Per-sig 0-based numbering (Java Kodkod style: `Book$0`): each sig's
    // atoms are numbered from 0, not from a shared global counter.
    let alloc_for = |name: &str, count: u32| -> Vec<String> {
        (0..count).map(|i| format!("{name}${i}")).collect()
    };

    // iterate until fixed point so parents seen before children regardless of order
    let mut pending: Vec<String> = roots.split_off(0);
    roots = pending.clone();
    pending.clear();

    // simple queue of hierarchy roots
    roots.sort();
    for root in &roots {
        // gather subtree in BFS order
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(root.clone());
        let mut order: Vec<String> = Vec::new();
        while let Some(cur) = queue.pop_front() {
            order.push(cur.clone());
            for c in children.get(&cur).cloned().unwrap_or_default() {
                queue.push_back(c);
            }
        }
        // total for the root node itself
        let (total, exact) = user.get(root.as_str()).copied().unwrap_or((overall, false));
        // one/lone sigs cap at 1 atom
        let rmult = mults.get(root.as_str()).copied().unwrap_or(SigMult::None);
        let has_children = children.contains_key(root);
        let total = match rmult {
            SigMult::One | SigMult::Lone => 1,
            _ => total,
        };
        if !has_children {
            let at = alloc_for(
                root,
                total.max(if rmult == SigMult::Lone || rmult == SigMult::Some {
                    1
                } else {
                    0
                }),
            );
            atoms_of.insert(root.clone(), at);
            continue;
        }
        // Check if there are any non-in children that need atom allocation
        let kids = children.get(root).unwrap().clone();
        let non_in_kids: Vec<&String> = kids
            .iter()
            .filter(|k| sig_rels.get(k.as_str()).copied().unwrap_or(SigRel::None) != SigRel::In)
            .collect();
        // If all children are `in` children, allocate atoms for the root itself
        // (in children share the parent's atoms, so the parent must have them)
        if non_in_kids.is_empty() {
            let at = alloc_for(
                root,
                total.max(if rmult == SigMult::Lone || rmult == SigMult::Some {
                    1
                } else {
                    0
                }),
            );
            atoms_of.insert(root.clone(), at);
            continue;
        }
        // distribute among direct children that have no user scope
        // skip `in` children - they don't allocate atoms
        let mut remaining = total;
        let mut unspecified: Vec<&String> = kids
            .iter()
            .filter(|k| {
                !user.contains_key(k.as_str())
                    && sig_rels.get(k.as_str()).copied().unwrap_or(SigRel::None) != SigRel::In
            })
            .collect();
        unspecified.sort();
        let share = if unspecified.is_empty() {
            0
        } else {
            remaining / unspecified.len() as u32
        };
        for k in &kids {
            // `in` children share parent atoms; don't allocate
            if sig_rels.get(k.as_str()).copied().unwrap_or(SigRel::None) == SigRel::In {
                continue;
            }
            if let Some((n, _)) = user.get(k) {
                let kmult = mults.get(k.as_str()).copied().unwrap_or(SigMult::None);
                let n2 = match kmult {
                    SigMult::One | SigMult::Lone => 1,
                    _ => *n,
                };
                atoms_of.insert(k.clone(), alloc_for(k, n2));
            } else {
                let kmult = mults.get(k.as_str()).copied().unwrap_or(SigMult::None);
                let take = match kmult {
                    SigMult::One | SigMult::Lone => 1,
                    _ => {
                        let t = share.min(remaining);
                        remaining -= t;
                        t
                    }
                };
                atoms_of.insert(k.clone(), alloc_for(k, take));
            }
        }
        let _ = exact;
    }

    // For `in` children, their atoms are a subset of the parent's atoms.
    // Do NOT add them to atoms_of (which feeds the universe); instead
    // record the relationship so bind_sigs can set the correct upper bound.
    // Resolve transitively: if B in A in Top, B gets Top's atoms.
    let mut in_children_atoms: HashMap<String, Vec<String>> = HashMap::new();
    // First pass: collect direct in-relationships
    let mut in_direct: HashMap<String, String> = HashMap::new();
    for sd in &module.sigs {
        if sd.rel == SigRel::In {
            if let Some(p) = &sd.extends {
                for n in &sd.names {
                    in_direct.insert(n.clone(), p.clone());
                }
            }
        }
    }
    // Second pass: resolve transitively to a root with allocated atoms.
    // A builtin `Int`/`Signed` ancestor terminates at the int atoms
    // `{0, .., W-1}` for the effective atom count (same naming as the
    // universe construction below). With lazy allocation (`needs_int ==
    // false`) the range is empty; that path is unreachable for `in Int`
    // children (which set `needs_int`), so the empty case only guards
    // the type level.
    let int_atoms: Vec<String> = if needs_int {
        (0..int_count).map(|v| v.to_string()).collect()
    } else {
        Vec::new()
    };
    // Builtin `EReal` atoms + bit-lane atoms (lazy like Int: allocated
    // only when the module mentions `EReal`).
    let ereal_atoms: Vec<String> = if needs_ereal {
        (0..ereal_count).map(|i| format!("EReal${i}")).collect()
    } else {
        Vec::new()
    };
    let mut lane_atoms: HashMap<u32, Vec<String>> = HashMap::new();
    if needs_ereal {
        lane_atoms.insert(
            LANE_M,
            (0..mepk_widths.m_width).map(|i| format!("M${i}")).collect(),
        );
        lane_atoms.insert(
            LANE_E,
            (0..mepk_widths.e_width).map(|i| format!("E${i}")).collect(),
        );
        lane_atoms.insert(
            LANE_P,
            (0..mepk_widths.p_width).map(|i| format!("P${i}")).collect(),
        );
        lane_atoms.insert(
            LANE_K,
            (0..mepk_widths.k_width).map(|i| format!("K${i}")).collect(),
        );
    }
    for n in &all_names {
        if let Some(parent) = in_direct.get(n) {
            let mut cur = parent.clone();
            while let Some(next_parent) = in_direct.get(&cur) {
                cur = next_parent.clone();
            }
            // cur is now the root (non-in) ancestor, or builtin
            // `Int`/`Signed`/`EReal`
            if cur == "Int" || cur == "Signed" {
                in_children_atoms.insert(n.clone(), int_atoms.clone());
            } else if cur == "EReal" || ereal_extenders(&module).contains(&cur) {
                in_children_atoms.insert(n.clone(), ereal_atoms.clone());
            } else {
                let root_atoms = atoms_of.get(&cur).cloned().unwrap_or_default();
                in_children_atoms.insert(n.clone(), root_atoms);
            }
        }
    }
    // `extends EReal` descendants share the EReal atoms as their upper
    // bound (like `in` children); the partition (subset/disjoint/cover)
    // is enforced by formulas in lower.rs.
    for n in ereal_extenders(&module) {
        in_children_atoms.insert(n, ereal_atoms.clone());
    }

    // closure atoms: include own + descendants
    let mut closure: HashMap<String, Vec<String>> = HashMap::new();
    for n in &all_names {
        let mut acc = atoms_of.get(n).cloned().unwrap_or_default();
        // `in` children's atoms are parent's atoms, already in parent's acc
        if let Some(in_atoms) = in_children_atoms.get(n) {
            acc = in_atoms.clone();
        }
        let mut queue = std::collections::VecDeque::new();
        // only add non-in children to the queue (in children don't expand further)
        if let Some(cs) = children.get(n) {
            for c in cs {
                if !in_children_atoms.contains_key(c) {
                    queue.push_back(c.clone());
                }
            }
        }
        while let Some(cur) = queue.pop_front() {
            acc.extend(atoms_of.get(&cur).cloned().unwrap_or_default());
            if let Some(cs) = children.get(&cur) {
                for c in cs {
                    if !in_children_atoms.contains_key(c) {
                        queue.push_back(c.clone());
                    }
                }
            }
        }
        closure.insert(n.clone(), acc);
    }

    // universe: every allocated atom, sorted for determinism
    let mut flat: Vec<String> = atoms_of.values().flatten().cloned().collect();
    flat.sort();
    // int atoms (lazy: omitted entirely when Int is never used as a set)
    let int_names: Vec<String> = if needs_int {
        (0..int_count).map(|v| v.to_string()).collect()
    } else {
        Vec::new()
    };
    // Step atoms: temporal step count (`for N steps`, default 4 when the
    // module carries temporal operators), else empty (static = empty set).
    let temporal = module.facts.iter().any(|(_, f)| f.has_temporal())
        || module.soft_facts.iter().any(|(_, f)| f.has_temporal())
        || module.paras.iter().any(|p| p.body.has_temporal())
        || module.sigs.iter().any(|sd| {
            sd.fact.as_ref().is_some_and(|f| f.has_temporal())
                || sd.fields.iter().any(|d| d.expr.has_temporal())
        });
    let step_n: u32 = match scope.steps {
        Some(n) => n,
        None => {
            if temporal {
                4
            } else {
                0
            }
        }
    };
    let step_atoms: Vec<String> = (0..step_n).map(|i| format!("Step${i}")).collect();
    let mut uni_atoms: Vec<String> = flat.clone();
    uni_atoms.extend(int_names.iter().cloned());
    uni_atoms.extend(step_atoms.iter().cloned());
    uni_atoms.extend(ereal_atoms.iter().cloned());
    for atoms in lane_atoms.values() {
        uni_atoms.extend(atoms.iter().cloned());
    }
    let refs: Vec<&str> = uni_atoms.iter().map(|s| s.as_str()).collect();
    let universe = Universe::new(refs).map_err(|e| format!("universe: {e}"))?;

    let mut sigs = HashMap::new();
    for n in &all_names {
        sigs.insert(
            n.clone(),
            SigInfo {
                name: n.clone(),
                parent: parents.get(n.as_str()).cloned().flatten(),
                rel: *sig_rels.get(n.as_str()).unwrap_or(&SigRel::None),
                mult: *mults.get(n.as_str()).unwrap_or(&SigMult::None),
                atoms: atoms_of.get(n).cloned().unwrap_or_default(),
            },
        );
    }
    // Builtin `Step`: reserved name (lexer maps any case/plural to the
    // scope keyword, so a user `sig Step` cannot parse; rename to avoid).
    sigs.insert(
        "Step".to_string(),
        SigInfo {
            name: "Step".to_string(),
            parent: None,
            rel: SigRel::None,
            mult: SigMult::None,
            atoms: step_atoms.clone(),
        },
    );
    // Builtin `EReal` (atoms allocated lazily; empty when unused).
    sigs.insert(
        "EReal".to_string(),
        SigInfo {
            name: "EReal".to_string(),
            parent: None,
            rel: SigRel::None,
            mult: SigMult::None,
            atoms: ereal_atoms.clone(),
        },
    );

    Ok(Resolved {
        universe,
        bitwidth,
        int_count,
        step_atoms: step_atoms.clone(),
        sigs,
        sig_rel: HashMap::new(),
        closure_atoms: {
            let mut c = closure;
            c.insert("Step".to_string(), step_atoms);
            c.insert("EReal".to_string(), ereal_atoms.clone());
            c
        },
        in_children_atoms,
        ereal_atoms,
        ereal_count,
        lane_atoms,
        mepk_widths,
    })
}

/// Builds bounds for every sig relation on `bounds`.
///
/// Alloy semantics: a plain sig's population is FLEXIBLE up to its scope
/// (lower = empty, upper = allocated atoms); `one sig` exists exactly;
/// `lone sig` allows empty; `exactly` scopes pin lower = upper.
pub fn bind_sigs(
    module: &Module,
    res: &Resolved,
    _pool: &Arc<alloy_kodkod_rs::relation::RelationPool>,
    arena: &mut alloy_kodkod_rs::ast::AstArena,
    b: &mut Bounds,
    cmd_scope: &crate::ast::Scope,
) -> Result<(), String> {
    use std::collections::HashMap as HM;
    let mut exact: HM<String, bool> = HM::new();
    for sd in &module.sigs {
        for n in &sd.names {
            exact.insert(n.clone(), sd.mult == SigMult::One);
        }
    }
    for (name, e) in &cmd_scope.entries {
        if matches!(e, ScopeEntry::Exactly(_)) {
            exact.insert(name.clone(), true);
        }
    }
    for name in res.sigs.keys() {
        let rel = arena.relation(name, 1);
        let mut ts = TupleSet::new(&res.universe, 1).map_err(|e| e.to_string())?;
        // For `in` children, use parent's atoms as upper bound
        let atoms = if let Some(in_atoms) = res.in_children_atoms.get(name) {
            in_atoms.clone()
        } else {
            res.atoms_of(name)
        };
        for a in &atoms {
            let idx = res.universe.index(a).map_err(|e| e.to_string())?;
            ts.insert_index(idx as i64);
        }
        let lo = TupleSet::new(&res.universe, 1).map_err(|e| e.to_string())?;
        let is_exact = *exact.get(name).unwrap_or(&false)
            || (cmd_scope.overall_exact && !cmd_scope.entries.iter().any(|(n, _)| n == name))
            || name == "Step";
        // `some sig` requires a non-empty lower bound
        let has_some_mult = module
            .sigs
            .iter()
            .any(|sd| sd.mult == SigMult::Some && sd.names.iter().any(|n| n == name));
        if is_exact {
            b.bound_exactly(rel, &ts).map_err(|e| e.to_string())?;
        } else if has_some_mult {
            // lower = first atom, upper = allocated atoms
            let mut lo_set = TupleSet::new(&res.universe, 1).map_err(|e| e.to_string())?;
            if let Some(first_a) = atoms.first() {
                let idx = res.universe.index(first_a).map_err(|e| e.to_string())?;
                lo_set.insert_index(idx as i64);
            }
            b.bound(rel, &lo_set, &ts).map_err(|e| e.to_string())?;
        } else {
            b.bound(rel, &lo, &ts).map_err(|e| e.to_string())?;
        }
    }
    Ok(())
}

/// Helper: tupleset from atom names.
pub fn ts_of(res: &Resolved, atoms: &[String]) -> Result<TupleSet, String> {
    let mut ts = TupleSet::new(&res.universe, 1).map_err(|e| e.to_string())?;
    for a in atoms {
        let idx = res.universe.index(a).map_err(|e| e.to_string())?;
        ts.insert_index(idx as i64);
    }
    Ok(ts)
}

/// Helper: singleton tuple from atom names.
pub fn tuple_of(res: &Resolved, atoms: &[String]) -> Result<Tuple, String> {
    let strs: Vec<&str> = atoms.iter().map(|s| s.as_str()).collect();
    Tuple::from_atoms(&res.universe, &strs).map_err(|e| e.to_string())
}
