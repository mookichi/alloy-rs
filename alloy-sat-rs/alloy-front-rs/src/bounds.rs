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
use std::sync::Arc;

pub const DEFAULT_SCOPE: u32 = 3;
pub const DEFAULT_BITWIDTH: u32 = 4;

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
    pub bitwidth: u32,
    pub sigs: HashMap<String, SigInfo>,
    /// Every declared sig relation (sig name -> relation).
    #[allow(dead_code)]
    pub sig_rel: HashMap<String, RelationId>,
    /// Atoms reachable through each sig including descendants (for typing).
    pub closure_atoms: HashMap<String, Vec<String>>,
    /// For `in` children: atoms are a subset of parent's atoms.
    pub in_children_atoms: HashMap<String, Vec<String>>,
}

impl Resolved {
    /// All atoms of a sig including its subtree (children, recursively).
    pub fn atoms_of(&self, name: &str) -> Vec<String> {
        self.closure_atoms.get(name).cloned().unwrap_or_default()
    }
}

fn build_scope_map(_module: &Module, scope: &Scope) -> (HashMap<String, (u32, bool)>, u32, u32) {
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
    // `k Int` sets bitwidth k; plain Int entry means number of int atoms?
    // Alloy uses `for N Int` as bitwidth N. Default bitwidth 4.
    let bitwidth = scope.int_scope.unwrap_or(DEFAULT_BITWIDTH).max(1);
    (m, overall, bitwidth)
}

/// Resolves scopes into universe + per-sig atom allocations.
pub fn resolve(module: &Module, scope: &Scope) -> Result<Resolved, String> {
    let (user, overall, bitwidth) = build_scope_map(module, scope);

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
                if !all_names.iter().any(|x| x == p)
                    && module.sigs.iter().all(|s| !s.names.contains(p))
                {
                    return Err(format!("sig {n} extends unknown parent {p}"));
                }
                children.entry(p.clone()).or_default().push(n.clone());
            }
        }
    }

    // allocation: process hierarchies top-down
    // For `sig in`, the child does NOT allocate its own atoms; it shares
    // the parent's atoms (subset constraint added as formula in lower.rs).
    let mut atoms_of: HashMap<String, Vec<String>> = HashMap::new();
    let mut counter: usize = 0;

    fn is_root(parents: &HashMap<&str, Option<String>>, n: &str) -> bool {
        parents.get(n).map(|p| p.is_none()).unwrap_or(true)
    }

    let mut roots: Vec<String> = all_names
        .iter()
        .filter(|n| is_root(&parents, n))
        .cloned()
        .collect();

    let alloc_for = |name: &str, count: u32, counter: &mut usize| -> Vec<String> {
        let mut v = Vec::new();
        for i in 0..count {
            v.push(format!("{name}${}", *counter + i as usize));
        }
        *counter += count as usize;
        v
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
                &mut counter,
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
                &mut counter,
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
                atoms_of.insert(k.clone(), alloc_for(k, n2, &mut counter));
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
                atoms_of.insert(k.clone(), alloc_for(k, take, &mut counter));
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
    // Second pass: resolve transitively to a root with allocated atoms
    for n in &all_names {
        if let Some(parent) = in_direct.get(n) {
            let mut cur = parent.clone();
            while let Some(next_parent) = in_direct.get(&cur) {
                cur = next_parent.clone();
            }
            // cur is now the root (non-in) ancestor
            let root_atoms = atoms_of.get(&cur).cloned().unwrap_or_default();
            in_children_atoms.insert(n.clone(), root_atoms);
        }
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
    // int atoms
    let half = 1i64 << (bitwidth - 1);
    let int_names: Vec<String> = ((-half)..(half)).map(|v| v.to_string()).collect();
    let mut uni_atoms: Vec<String> = flat.clone();
    uni_atoms.extend(int_names.iter().cloned());
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

    Ok(Resolved {
        universe,
        bitwidth,
        sigs,
        sig_rel: HashMap::new(),
        closure_atoms: closure,
        in_children_atoms,
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
            || (cmd_scope.overall_exact && !cmd_scope.entries.iter().any(|(n, _)| n == name));
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
