//! Lightweight abstract types for the set-vs-int disambiguation.
//!
//! The `+` token has no single dynamic dispatch: set position parses to
//! `BinOp::Union` and int position to `IntBinOp::Add`. This module is the
//! single source of truth for the shape predicates and cast decisions
//! that used to be scattered across `parser.rs`, `lower.rs` (`bool`
//! int-flavored flags) and `snippet.rs`.
//!
//! Deliberately *not* Java Alloy's `Type` (product types over the sig
//! lattice): no sig-mismatch checking, no strictness change. `Unknown`
//! behaves like `Plain` (not int) so current lenient behavior is
//! preserved; it exists so future gradual strictness has a home.

use crate::ast::{Expr, IntExpr};

/// Abstract flavor of a set-valued expression in the bit-vector model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SetKind {
    /// Plain (non-integer) sig atoms.
    Plain,
    /// Denotes int atoms (`Int`/`Signed` sets, numeric literals, `MSB`,
    /// `{...}` bit-sets); integer arithmetic/comparison is bitmask
    /// meaningful.
    Int,
    /// Cannot decide (comprehension, unresolved call, ...). Treated as
    /// non-int today; reserved for gradual strictness (warn-first).
    Unknown,
}

impl SetKind {
    pub fn from_bool(b: bool) -> Self {
        if b { SetKind::Int } else { SetKind::Plain }
    }

    pub fn is_int(self) -> bool {
        matches!(self, SetKind::Int)
    }

    /// Conjunction used for `Bin`/`Join` flavor propagation:
    /// `Int && Int = Int`, anything else is `Plain` (preserves the old
    /// `bool &&` semantics; `Unknown` degrades to `Plain`).
    pub fn and(self, other: Self) -> Self {
        if self.is_int() && other.is_int() {
            SetKind::Int
        } else {
            SetKind::Plain
        }
    }
}

/// Shared type-mismatch message for integer positions (single source so
/// parser/lower/snippet diagnostics stay identical).
pub const INT_MISMATCH_MSG: &str = "type mismatch: integer comparison/arithmetic requires an `Int`/`Signed` set (use `{...}` braces for int literals, e.g. `{0, 2} = 5`)";

/// `=`/`!=` rewind rule (`parser.rs::parse_comparison`): when the
/// relational (set) reading wins over the speculative int reading.
/// NOTE: deliberately stricter than the `set = int-expr` probe: a
/// leading int shape with a set-typed operand (`0 - A = X`, `{} = none`)
/// stays relational here; the integer route for mixed trees applies on
/// the right of `=`/`!=` only (write `X = 0 - A`).
pub fn should_rewind_eq(l: &IntExpr, r: &IntExpr) -> bool {
    (!r.int_typed() && !l.bare_int()) || (l.brace_pure() && r.brace_pure())
}

/// REPL `:query` routing (`snippet.rs::query_value`): true when the tree
/// is integer-shaped.
pub fn is_int_query(ie: &IntExpr) -> bool {
    ie.int_typed() && !ie.rewind_bitsval_eq()
}

/// `in`/`not in` probe: a genuine int tree left of `in` is a type error;
/// brace-pure set shapes (`{1}+{2}`) stay relational.
pub fn int_left_of_in_is_error(ie: &IntExpr) -> bool {
    ie.int_typed() && !ie.brace_pure()
}

/// `set = int-expr` bitmask reading (right side commits to int).
pub fn set_eq_rhs_is_int(ie: &IntExpr) -> bool {
    ie.int_typed() && !ie.brace_pure()
}

/// Which Kodkod cast a set-typed operand in int position needs.
/// Today both `Val` (SUM-cast heritage) and `BitsVal` lower via the
/// `BITS` bitmask cast; `SumOf` (explicit `sum e`) uses `SUM`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntCast {
    Bits,
    Sum,
}

pub fn cast_for_intexpr(ie: &IntExpr) -> Option<IntCast> {
    match ie {
        IntExpr::Val(..) | IntExpr::BitsVal(..) => Some(IntCast::Bits),
        IntExpr::SumOf(..) => Some(IntCast::Sum),
        _ => None,
    }
}

/// Flavor of a leaf expression that needs no environment. `None` means
/// "consult env/relations" (names, joins, calls...).
pub fn leaf_kind(e: &Expr) -> Option<SetKind> {
    match e {
        Expr::IntAtom | Expr::Bits(..) => Some(SetKind::Int),
        Expr::Name(n, _) => {
            if n.parse::<i64>().is_ok()
                || n == "MSB"
                || n == "int"
                || n == "Int"
                || n == "Signed"
            {
                Some(SetKind::Int)
            } else {
                None
            }
        }
        Expr::Univ | Expr::None_ | Expr::StepAtom => Some(SetKind::Plain),
        Expr::Comprehension(..) => Some(SetKind::Unknown),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(v: i64) -> IntExpr {
        IntExpr::Lit(v, 0)
    }

    fn bits(e: Expr) -> IntExpr {
        IntExpr::BitsVal(Box::new(e), 0)
    }

    fn val(e: Expr) -> IntExpr {
        IntExpr::Val(Box::new(e), 0)
    }

    fn name(n: &str) -> Expr {
        Expr::Name(n.to_string(), 0)
    }

    #[test]
    fn setkind_and_preserves_bool_semantics() {
        use SetKind::*;
        assert_eq!(Int.and(Int), Int);
        assert_eq!(Int.and(Plain), Plain);
        assert_eq!(Plain.and(Int), Plain);
        assert_eq!(Unknown.and(Int), Plain);
        assert!(!Unknown.is_int());
        assert_eq!(SetKind::from_bool(true), Int);
        assert_eq!(SetKind::from_bool(false), Plain);
    }

    #[test]
    fn rewind_table() {
        // `{0}+{1} = {0,1}`: both brace-pure -> rewind to set.
        let l = IntExpr::Bin(
            crate::ast::IntBinOp::Add,
            Box::new(bits(name("0"))),
            Box::new(bits(name("1"))),
        );
        let r = bits(name("2"));
        assert!(should_rewind_eq(&l, &r));
        // `1+2 = X`: left bare-int commits to int (no rewind even though
        // right is set-typed).
        let li = IntExpr::Bin(
            crate::ast::IntBinOp::Add,
            Box::new(lit(1)),
            Box::new(lit(2)),
        );
        let rv = val(name("X"));
        assert!(!should_rewind_eq(&li, &rv));
        // `x = 5` shape: left Val, right bare lit -> no rewind here;
        // the int route is taken and `lower_int`'s flavor gate rejects
        // plain sigs (use `{5}` for the set reading).
        assert!(!should_rewind_eq(&val(name("x")), &lit(5)));
        // `#A = 4`: both int-typed, not brace-pure -> no rewind.
        let card = IntExpr::Card(Box::new(name("A")), 0);
        assert!(!should_rewind_eq(&card, &lit(4)));
        // Leading mixed shapes stay relational here (`0 - A = X` rewinds;
        // the integer route applies on the right of `=` only).
        let sub = IntExpr::Bin(
            crate::ast::IntBinOp::Sub,
            Box::new(lit(0)),
            Box::new(val(name("A"))),
        );
        assert!(should_rewind_eq(&sub, &val(name("X"))));
        // `(A + B) = S`: lone Vals on both sides -> rewind to set.
        let add = IntExpr::Bin(
            crate::ast::IntBinOp::Add,
            Box::new(val(name("A"))),
            Box::new(val(name("B"))),
        );
        assert!(should_rewind_eq(&add, &val(name("S"))));
    }

    #[test]
    fn mixed_int_table() {
        // Lone Val stays relational.
        assert!(!val(name("A")).mixed_int());
        // Hard-int leaves commit.
        assert!(lit(1).mixed_int());
        assert!(bits(name("0")).mixed_int());
        // Mixed trees commit even with Val inside.
        let sub = IntExpr::Bin(
            crate::ast::IntBinOp::Sub,
            Box::new(lit(0)),
            Box::new(val(name("A"))),
        );
        assert!(sub.mixed_int());
        assert!(!sub.brace_pure());
        // Pure Val combinations stay relational.
        let add = IntExpr::Bin(
            crate::ast::IntBinOp::Add,
            Box::new(val(name("A"))),
            Box::new(val(name("B"))),
        );
        assert!(!add.mixed_int());
    }

    #[test]
    fn query_and_in_probes() {
        assert!(is_int_query(&lit(1)));
        assert!(!is_int_query(&bits(name("0"))));
        assert!(int_left_of_in_is_error(&lit(1)));
        assert!(!int_left_of_in_is_error(&bits(name("0"))));
        assert!(set_eq_rhs_is_int(&lit(5)));
        assert!(!set_eq_rhs_is_int(&bits(name("0"))));
    }

    #[test]
    fn cast_routing() {
        assert_eq!(cast_for_intexpr(&val(name("x"))), Some(IntCast::Bits));
        assert_eq!(cast_for_intexpr(&bits(name("0"))), Some(IntCast::Bits));
        assert_eq!(
            cast_for_intexpr(&IntExpr::SumOf(Box::new(name("A")), 0)),
            Some(IntCast::Sum)
        );
        assert_eq!(cast_for_intexpr(&lit(1)), None);
    }

    #[test]
    fn leaf_kinds() {
        assert_eq!(leaf_kind(&Expr::IntAtom), Some(SetKind::Int));
        assert_eq!(leaf_kind(&name("MSB")), Some(SetKind::Int));
        assert_eq!(leaf_kind(&name("3")), Some(SetKind::Int));
        assert_eq!(leaf_kind(&Expr::Univ), Some(SetKind::Plain));
        assert_eq!(leaf_kind(&name("A")), None);
    }
}
