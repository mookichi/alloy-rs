use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BoolRef(pub i32);

impl BoolRef {
    pub fn slot(self) -> u32 {
        self.0.unsigned_abs()
    }

    pub fn sign(self) -> bool {
        self.0 > 0
    }

    pub fn flip(self) -> BoolRef {
        BoolRef(-self.0)
    }

    pub fn is_const(self) -> bool {
        self.0 == CONST_TRUE || self.0 == CONST_FALSE
    }

    pub fn const_value(self) -> bool {
        self.0 > 0
    }
}

pub const CONST_TRUE: i32 = i32::MAX;
pub const CONST_FALSE: i32 = -i32::MAX;

pub fn const_true() -> BoolRef {
    BoolRef(CONST_TRUE)
}

pub fn const_false() -> BoolRef {
    BoolRef(CONST_FALSE)
}

fn const_of(r: BoolRef) -> Option<bool> {
    r.is_const().then_some(r.const_value())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoolNode {
    Var,
    And(Vec<BoolRef>),
    Or(Vec<BoolRef>),
    Ite { c: BoolRef, t: BoolRef, e: BoolRef },
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum GateKey {
    And(Vec<i32>),
    Or(Vec<i32>),
    Ite(i32, bool, i32, i32),
}

#[derive(Default)]
pub struct BoolFactory {
    nodes: Vec<BoolNode>,
    cache: HashMap<GateKey, BoolRef>,
}

impl BoolFactory {
    pub fn new() -> BoolFactory {
        BoolFactory::default()
    }

    pub fn variable(&mut self) -> BoolRef {
        let slot = self.nodes.len() as u32 + 1;
        self.nodes.push(BoolNode::Var);
        BoolRef(slot as i32)
    }

    /// Debug helper: structural description of a slot's node.
    pub fn debug_node(&self, slot: u32) -> String {
        match slot.checked_sub(1).and_then(|i| self.nodes.get(i as usize)) {
            None => format!("#{slot}=<oob>"),
            Some(BoolNode::Var) => format!("v{slot}"),
            Some(BoolNode::And(ins)) => {
                let parts: Vec<String> = ins.iter().map(|r| format!("{}", r.0)).collect();
                format!("{}=AND{}", slot, parts.join(","))
            }
            Some(BoolNode::Or(ins)) => {
                let parts: Vec<String> = ins.iter().map(|r| format!("{}", r.0)).collect();
                format!("{}=OR{}", slot, parts.join(","))
            }
            Some(BoolNode::Ite { c, t, e }) => {
                format!("{}=ITE({},{},{})", slot, c.0, t.0, e.0)
            }
        }
    }

    pub fn num_slots(&self) -> usize {
        self.nodes.len()
    }

    pub fn node(&self, r: BoolRef) -> Option<&BoolNode> {
        let slot = r.slot();
        if slot == 0 || slot as usize > self.nodes.len() {
            None
        } else {
            Some(&self.nodes[slot as usize - 1])
        }
    }

    pub fn not(&self, r: BoolRef) -> BoolRef {
        r.flip()
    }

    pub fn and(&mut self, inputs: &[BoolRef]) -> BoolRef {
        match self.fold(inputs, false) {
            Folded::Const(c) => bool_const(c),
            Folded::Single(r) => r,
            Folded::Children(kids) => {
                self.gate(GateKey::And(kids.iter().map(|r| r.0).collect()), kids)
            }
        }
    }

    pub fn or(&mut self, inputs: &[BoolRef]) -> BoolRef {
        match self.fold(inputs, true) {
            Folded::Const(c) => bool_const(c),
            Folded::Single(r) => r,
            Folded::Children(kids) => {
                self.gate(GateKey::Or(kids.iter().map(|r| r.0).collect()), kids)
            }
        }
    }

    pub fn ite(&mut self, c: BoolRef, t: BoolRef, e: BoolRef) -> BoolRef {
        if let Some(v) = const_of(c) {
            return if v { t } else { e };
        }
        if t == e {
            return t;
        }
        let nt = self.not(t);
        let ne = self.not(e);
        if t == const_true() && e == const_false() {
            return c;
        }
        if t == const_false() && e == const_true() {
            return c.flip();
        }
        if e == const_false() {
            return self.and(&[c, t]);
        }
        if t == const_false() {
            return self.and(&[c.flip(), e]);
        }
        if e == const_true() {
            return self.or(&[c.flip(), t]);
        }
        if t == const_true() {
            return self.or(&[c, e]);
        }
        let _ = (nt, ne);
        let k = GateKey::Ite(c.slot() as i32, c.sign(), t.0, e.0);
        let kids = vec![c, t, e];
        self.gate(k, kids)
    }

    fn gate(&mut self, k: GateKey, kids: Vec<BoolRef>) -> BoolRef {
        if let Some(&existing) = self.cache.get(&k) {
            return existing;
        }
        let slot = self.nodes.len() as u32 + 1;
        let node = match &k {
            GateKey::And(_) => BoolNode::And(kids),
            GateKey::Or(_) => BoolNode::Or(kids),
            GateKey::Ite(ca, cs, t, e) => BoolNode::Ite {
                c: BoolRef(if *cs { *ca } else { -*ca }),
                t: BoolRef(*t),
                e: BoolRef(*e),
            },
        };
        self.nodes.push(node);
        let r = BoolRef(slot as i32);
        self.cache.insert(k, r);
        r
    }

    fn fold(&self, inputs: &[BoolRef], is_or: bool) -> Folded {
        let mut kids: Vec<i32> = Vec::with_capacity(inputs.len());
        for &r in inputs {
            if let Some(v) = const_of(r) {
                if v == is_or {
                    return Folded::Const(is_or);
                }
                continue;
            }
            kids.push(r.0);
        }
        kids.sort_unstable();
        kids.dedup();
        // complementary literals: AND(x, ¬x) = FALSE / OR(x, ¬x) = TRUE.
        // Sorted ascending, negatives precede positives, so a complement
        // pair (-x, +x) is generally NOT adjacent (any other negative
        // literal in between breaks the windows(2) check). Probe membership
        // with binary search instead.
        for &k in kids.iter() {
            if k >= 0 {
                break;
            }
            if kids.binary_search(&-k).is_ok() {
                return Folded::Const(is_or);
            }
        }
        // absorption: AND(x, OR(x, …)) = x / OR(x, AND(x, …)) = x
        // Only worth the snapshot when some kid is actually a compound gate.
        let absorb_kind_is_and = !is_or; // inside an AND we absorb OR-kids
        let has_compound = kids.iter().any(|&k| {
            matches!(
                self.node(BoolRef(k)),
                Some(BoolNode::Or(_)) | Some(BoolNode::And(_))
            )
        });
        let before = kids.len();
        if has_compound {
            let snapshot = kids.clone();
            kids.retain(|&k| {
                // Absorption identities (x \/ AND(x,..) = x, x /\ OR(x,..) = x)
                // require the absorbed kid to occur UNNEGATED: dropping
                // \neg(OR(y, x)) from AND(\neg(OR(y,x)), x) would claim
                // FALSE == x. Hence only positive handles may match.
                if k < 0 {
                    return true;
                }
                let dropped = match self.node(BoolRef(k)) {
                    Some(BoolNode::Or(cs)) if absorb_kind_is_and => {
                        cs.iter().any(|c| snapshot.contains(&c.0) && c.0 != k)
                    }
                    Some(BoolNode::And(cs)) if is_or => cs.iter().any(|c| snapshot.contains(&c.0)),
                    _ => false,
                };
                !dropped
            });
        }
        if kids.len() != before {
            kids.sort_unstable();
            kids.dedup();
            for &k in kids.iter() {
                if k >= 0 {
                    break;
                }
                if kids.binary_search(&-k).is_ok() {
                    return Folded::Const(is_or);
                }
            }
        }
        match kids.len() {
            0 => Folded::Const(!is_or),
            1 => Folded::Single(BoolRef(kids[0])),
            _ => Folded::Children(kids.into_iter().map(BoolRef).collect()),
        }
    }

    /// Evaluate a circuit against `model`.
    ///
    /// Convention: `model` is indexed 0-based over SAT variables, i.e.
    /// Var(slot s) reads `model[s - 1]`. Callers building models from
    /// SAT-solver assignments must map var v -> model[v - 1]; getting
    /// this wrong shifts every primary literal by one and silently
    /// inverts diagnostics (this cost a full debugging session).
    pub fn eval(&self, r: BoolRef, model: &[bool]) -> bool {
        let mut memo = Vec::new();
        self.eval_memo(r, model, &mut memo)
    }

    pub fn eval_memo(&self, r: BoolRef, model: &[bool], memo: &mut Vec<Option<bool>>) -> bool {
        if let Some(value) = const_of(r) {
            return value;
        }
        let slot = r.slot() as usize;
        if slot == 0 || slot > self.nodes.len() {
            panic!("dangling BoolRef");
        }
        if memo.len() >= slot {
            if let Some(inner) = memo[slot - 1] {
                return if r.sign() { inner } else { !inner };
            }
        }
        while memo.len() < slot {
            memo.push(None);
        }
        let inner = match self.node(r).expect("dangling BoolRef") {
            BoolNode::Var => model[slot - 1],
            BoolNode::And(kids) => kids.iter().all(|&k| self.eval_memo(k, model, memo)),
            BoolNode::Or(kids) => kids.iter().any(|&k| self.eval_memo(k, model, memo)),
            BoolNode::Ite { c, t, e } => {
                if self.eval_memo(*c, model, memo) {
                    self.eval_memo(*t, model, memo)
                } else {
                    self.eval_memo(*e, model, memo)
                }
            }
        };
        memo[slot - 1] = Some(inner);
        if r.sign() {
            inner
        } else {
            !inner
        }
    }
}

fn bool_const(v: bool) -> BoolRef {
    BoolRef(if v { CONST_TRUE } else { CONST_FALSE })
}

enum Folded {
    Const(bool),
    Single(BoolRef),
    Children(Vec<BoolRef>),
}
