#![cfg(feature = "ipasir")]

//! Iter-6 example suite: small kodkod-style problems (csp-flavored) with an
//! expected SAT/UNSAT table, solved through the `Solver` facade.

#[path = "puzzles.rs"]
mod puzzles;

use alloy_kodkod_rs::Solver;
use puzzles::{coloring, pigeonhole, queens};

struct Case {
    name: &'static str,
    build: fn() -> puzzles::Puzzle,
    expect_sat: bool,
}

fn cases() -> Vec<Case> {
    vec![
        Case {
            name: "queens2",
            build: || queens(2),
            expect_sat: false,
        },
        Case {
            name: "queens3",
            build: || queens(3),
            expect_sat: false,
        },
        Case {
            name: "queens4",
            build: || queens(4),
            expect_sat: true,
        },
        Case {
            name: "queens6",
            build: || queens(6),
            expect_sat: true,
        },
        Case {
            name: "pigeonhole3x2",
            build: || pigeonhole(3, 2),
            expect_sat: false,
        },
        Case {
            name: "pigeonhole3x3",
            build: || pigeonhole(3, 3),
            expect_sat: true,
        },
        Case {
            name: "pigeonhole4x3",
            build: || pigeonhole(4, 3),
            expect_sat: false,
        },
        Case {
            name: "triangle2color",
            build: || coloring(3, &[(0, 1), (1, 2), (0, 2)], 2),
            expect_sat: false,
        },
        Case {
            name: "triangle3color",
            build: || coloring(3, &[(0, 1), (1, 2), (0, 2)], 3),
            expect_sat: true,
        },
        Case {
            name: "path2color",
            build: || coloring(4, &[(0, 1), (1, 2), (2, 3)], 2),
            expect_sat: true,
        },
        Case {
            name: "k4e_3color",
            build: || coloring(4, &[(0, 1), (1, 2), (2, 3), (0, 2), (0, 3)], 3),
            expect_sat: true,
        },
    ]
}

#[test]
fn examples_suite_matches_expected_table() {
    let solver = Solver::new();
    for case in cases() {
        let mut p = (case.build)();
        let sol = solver
            .solve(&mut p.arena, p.formula, &p.bounds)
            .unwrap_or_else(|e| panic!("{}: translate failed: {e}", case.name));
        assert_eq!(
            sol.satisfiable,
            case.expect_sat,
            "{}: expected {}, got {}",
            case.name,
            if case.expect_sat { "SAT" } else { "UNSAT" },
            if sol.satisfiable { "SAT" } else { "UNSAT" }
        );
        if case.expect_sat {
            assert!(
                sol.instance.is_some(),
                "{}: SAT must materialize instance",
                case.name
            );
        }
    }
}
