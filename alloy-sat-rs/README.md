# alloy-sat-rs

Alloy/Pardinus の Rust 再実装。`.als` のパースから SAT 求解・最適化・REPL までを
Rust ネイティブで完結させ、Java 実装は差分オラクルおよび GUI/CLI ホストとして残す。
Cargo ワークスペース (5 クレート、計 ~33k 行) + Java 対向物 (engine/mepk 等) からなる。

```
.als ──► alloy-front-rs ──► alloy-kodkod-rs ──► alloy-ipasir ──► 解
 (lex/parse/      (FOL→bool→CNF,          (CaDiCaL / Splr)
  lower/Cnf)       Int/temporal/opt/         ▲
                   mepk回路)                 │ SatSolver trait
                                             │
alloy-repl (対話層: Cnf/解の名前付きstore) ────┘
alloy-engine-rs (Java↔Rust 直列化 ARE1/ARE2 + C ABI/JNI)
```

## クレート

### `alloy-front-rs` — フロントエンド (lex→parse→lower→Cnf)
| モジュール | 役割 |
|---|---|
| `lex.rs` / `parser.rs` / `ast.rs` / `types.rs` | 字句・構文・AST・型 (Alloy 6 準拠 + 拡張: `<->`、`{A,B}`集合リテラル、`Int`/`Signed`、`partial`、`maximize`/`minimize`、`some/no Overflow`) |
| `bounds.rs` / `lower.rs` | Universe 構築・Kodkod AST/Bounds への lowering (bitmask-Int、EReal、temporal展開、partial desugar、optマーカー) |
| `cnf.rs` | `Cnf` (high-level arena+bounds+formula保持): `run`/`check`/`solve`/temporal/validate、二段階 overflow 探索 |
| `incremental.rs` | `IncrementalSession` (増分セッション) |
| `partial.rs` | ASTレベル partial instance (`partial`定義 + `pin`/`avoid`) |
| `cegis.rs` | CEGIS ドライバ |
| `snippet.rs` | `:eval`/`:query` 用スニペット評価 |
| `fuzzgen.rs` | 構造化モデル生成 + 力まかせオラクル (fuzz用) |
| `bin/als.rs` | `als` CLI (`als_solve`例あり) |

テスト 23 ファイル (`e2e`, `bitvec`, `int_bv`, `opt_cmd`, `temporal`, `total_order`, `partial_ast`, `ereal`, `alloymax_sweep`, `overflow_syntax`, `signed_overflow`, `snippets`, …) + fuzz targets。

### `alloy-kodkod-rs` — 関係論理コア (Pardinus 移植)
| モジュール | 役割 |
|---|---|
| `intset`/`universe`/`tuple`/`tupleset`/`relation`/`dimensions`/`bmatrix` | 集合・宇宙・行列基盤 |
| `ast`/`bounds`/`instance`/`solver` | AST アリーナ・境界・解・求解器 |
| `bool`/`cnf`/`sat` (+`ipasir_bridge`, feature `ipasir`) | Bool回路・CNF翻訳・バックエンド抽象 |
| `fol`/`eval`/`simplify`/`skolem` | FOL→bool、評価器、簡単化、Skolem化 |
| `int`/`int_ext` | 2の補数 `IntCircuit` (加減乗除算・比較・ choice) |
| `temporal` | 時制展開・評価 |
| `opt` | OLL/Fu-Malik core-guided 最適化 |
| `ucore` | UNSATコア (selector assumption + RCE相当最小化) |
| `mepk` | `(m,e,p,k)` 誤差追跡擬似実数回路 |
| `pardinus` | Pardinus互換 API |

テスト 25 ファイル (`fol`, `fol_int`, `int_circuit`, `opt`, `ucore`, `temporal`, `mepk_circuit`, `lane_bits`, `puzzles`, `differential`, …)、計 436 `#[test]`。

### `alloy-repl` — 対話 REPL (`alloy-repl` バイナリ)
* Cnf と解の名前付き store (`:cnfs`/`:sols`、`*` が既定、` :use` 切替)。
* `:run`/`:check` で Cnf 構築 → `:solve`/`:next` で求解 → `:query`/`:eval`/`:show`/`:validate` で検査。
* 最適化: `:optimize`、`:max`/`:min`/`:maxw`/`:minw` (+`cost=` 表示)。
* バイナリ partial instance: `:psave`/`:pread`/`:ppin`/`:pavoid` (`.apin`)。
* Mepk: `:mepk add|sub|mul|div|lit|widths` (`mepk_cmd.rs`)。
* 素行は `:eval` (SAT判定) / `:mode query` 切替で `:query`。詳細は起動後 `:help`。
* 表示規則: 集合は `{A$0, B$0}` 形 (`fmt.rs`)。

### `alloy-engine-rs` — Java 連携 (`liballoy_engine.so`)
* 問題直列化 ARE1/ARE2 (solver options + dynamic trailer) → Rust パイプライン → モデル復元。
* C ABI + JNI (`--features jni`)。Java 側 `RustSerializer`、`A4Solution` のエンジン分岐、CLI `exec --engine rust [--decompose hybrid|parallel] [--core]`。
* 受け入れ: extra/models 83 例題スイープで Java/Rust 一致 (結果 `docs/engine-sweep-results.txt`)。

### `alloy-ipasir` — SAT 層 (`liballoy_ipasir.so`)
* IPASIR 標準 C ABI (`ipasir_*` 同期ファサード) + `alloy_worker_*` 非同期 ABI。
* セッションごとに Rust ワーカースレッド 1 本; バックエンドはそのスレッド内に留まる。
* バックエンド: `cadical` (既定、増分・assumptions・割込み対応) / `splr` (純Rust、assumptions非対応)。`ALLOY_SAT_BACKEND` で選択。
* `--features jni` で JNI 10 関数を公開 → Java `IpasirWorker` (`org.alloytools.pardinus.native`)。CLI `exec --solver ipasir`。
* 制約: `ipasir_set_learn` は no-op。

## 意味論の要点 (Java との差異)
詳細は `docs/java-divergences.md` (§1–§8)。概要:
* **構文拡張**: 逆積 `<->`/`-<`、`for Int 8` 等の語順緩和、`{A,B}` 集合リテラル。
* **bitmask統一Int** (§3): `for W Int` で原子 `{0..W-1}`、回路幅 `E=min(W+1,30)`。
  int位置の集合は bitmask 値 (`X = 5` ⟺ `X = {0,2}`)。`Signed` ビュー、`MSB`、intアトム遅延割当。
* **partial/pin/avoid** (§5): ASTレベル部分インスタンス (`Sig$tag` ラベルは定義内局所)。
* **最適化** (§6): `maximize`/`minimize` コマンド、pred内マーカー (時制では `initially`/`goal`/`restore` で時点指定)、`maxsome`/`minsome`/`soft fact` (AlloyMax subset)。
* **オーバーフロー** (§7–§8): `some/no Overflow {F}`。`run` は溢れなし優先+fallback、`check` は wrapping 優先。評価器は E-bit ラップ。
* **Mepk/EReal**: `(m,e,p,k)` 形式。`sig A { x: EReal }`、`erealAdd/Sub/Mul/Div`、`setEReal[x, 3.14]`。Java 対向物は `org.alloytools.alloy.core` の `MepkOps.java` + `models/util/mepk.als` (`MepkOpsTest`: 10 tests)。

## ビルド / テスト

```sh
cargo build --release
cargo test --workspace --exclude alloy-ipasir   # 既定 (CaDiCaLのC++ビルド回避)
cargo test -p alloy-kodkod-rs --features ipasir # E2E/differential 込み
cargo test -p alloy-ipasir                      # SAT層 (cadical+splr)
cargo run -p alloy-repl                         # REPL
cargo run -p alloy-front-rs --bin als -- --help # CLI
```

Java 連携:
```sh
cargo build --release -p alloy-engine-rs --features jni  # liballoy_engine.so
./gradlew :org.alloytools.alloy.core:test --tests "edu.mit.csail.sdg.alloy4.MepkOpsTest"
java -Dalloy.native.lib.alloy_engine=$PWD/alloy-sat-rs/target/release/liballoy_engine.so \
  -jar org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar \
  exec --engine rust -f org.alloytools.alloy.extra/extra/models/book/appendixA/ring.als
```

## ドキュメント
* `docs/java-divergences.md` — Java との意図的差異 (§1–§8、現行仕様の正本)
* `docs/pardinus-core-survey.md` — Pardinus 移行の調査・設計記録
* `docs/agile-iterations.md` — 反復計画・運営規約
* `docs/engine-sweep-results.txt` (+ `engine-sweep-oracle.txt`) — 83例題スイープ結果
* `docs/perf-report.md` — 性能記録
* `docs/repro/` — 再現用モデル
