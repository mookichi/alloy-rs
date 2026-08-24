# Pardinus → Rust 移行 アジャイルイテレーション計画

更新: 2026-08-24

## ベースライン(完了済み資産)

| 資産 | 状態 |
|---|---|
| alloy-ipasir(IPASIR同期+非同期worker+JNI、CaDiCaL/Splr) | ✅ Java統合済み(dist `--solver ipasir` 動作) |
| intset(i64)/universe/tuple/tupleset | ✅ 21 tests |
| ast アリーナ(RelationId インターニング) | ✅ 11 tests |
| bool 回路 + Bool2CNFTranslator + SatSolver トレイト | ✅ 7 tests |
| ipasir ブリッジ(回路→CNF→CaDiCaL E2E) | ✅ 2 tests(feature `ipasir`) |

## 運営規約

- **イテレーション長**: 1週間(小さく出荷)。各イテレーション末尾に「デモ可能な成果物」を必ず持つ
- **DoD**: `cargo test`(デフォルト+`ipasir`)/`clippy` 0警告/`fmt` グリーン。
  Java側へ触る場合は `./gradlew test` もグリーン
- **設計記録**: 各IF完了時に `docs/pardinus-core-survey.md` のチェックリスト更新
- **ベンチ**: Iter 6 で criterion 導入し、以降は主要例題の翻訳時間を毎イテ記録

## イテレーション一覧

### Iter 1: データモデル完成 — Bounds / Instance ✅ 完了(2026-08-24、テスト+8)
- SparseSequence 最小移植(BTreeMap ベース、Ints.bestSet 相当の選択は後回し)
- `Bounds`: lowers/uppers(**挿入順保持**: Vec<RelationId>+HashMap)、intbounds
- `Instance`(+TemporalInstance は Iter 7 へ先送り)
- デモ: Java の ring.als バウンド相当を Rust で構築しダンプ表示
- 受け入れ: Java `BoundsTest` 的性質テストの Rust 移植(境界検証エラー群)

### Iter 2: FOL→bool 基盤 — Dimensions / BooleanMatrix ✅ 完了(2026-08-24、テスト+8)
- `Dimensions`: 行列形状の積/冪演算(472行相当)
- `BooleanMatrix`: 位置→BoolRef の疎写像、セル毎の遅延ゲート生成、
  and/or/ite/project の行列演算(Java の fold 規則を維持)
- デモ: 2×2 行列の結合操作を真理値表と照合
- 受け入れ: 行列演算プロパティテスト(手書き簡約と一致)

### Iter 3: FOL2BoolTranslator 関係子セット ✅ 完了(2026-08-24、テスト+13)
- ast(AstArena)→bool 回路: リーフ解決(Bounds↔Relation)、比較(in/=)、
  quantifier(宣言→行列の product/join)、comprehension、if 式
- スコレム化・最適化パスは**対象外**(後続 Iter で追加)
- デモ: 「all x: one y | x→y」的ミニモデルが回路化され CNF 経由で解ける
- 受け入れ: 手作り小模型 10 例の期待結果(SAT/UNSAT+インスタンス数)

### Iter 4: 整数エンコーディング — TwosComplementInt ✅ 完了(2026-08-24、テスト+13)
- TwosComplementInt(872行): ビット幅管理・算術・比較
- IntExpression 全演算(+ - * / % & | ^ << >>)、sum/cardinality キャスト、
  IntComparison、int 境界(boundExactly)との接続
- デモ: 数独(整数版ではなく関係版だが)NQueens を int エンコードで解く
- 受け入れ: オーバーフロー挙動(bitwidth 越え)の Java 一致確認

### Iter 5: 解の材料化 — Translation 記録 / Evaluator / Instance ✅ 完了(2026-08-24、テスト+6)
- 翻訳ログ: `FolTranslator` に `VarOrigin`(slot→relation→tuple_index)を記録、
  `materialize()` で SAT モデルから `Instance` を構築
- `Evaluator`: インスタンス上で AST 再評価(集合演算・量化子・closure・int 演算)
- デモ/テスト: 4-Queens を solve→materialize→Evaluator 再検証する E2E
  (`tests/solution.rs`。2-queens UNSAT、摂動盤面の拒否も含む)
- **重要なバグ修正**: 量化子の宣言ドメインが自由関係(upper bound のみ)の場合、
  宣言セルのメンバーシップ変数を本体にゲートとして組み込む必要があった
  (kodkod 流: ALL=`ℓ⇒body`、SOME=`ℓ∧body`、comprehension/sum も同様)。
  これが無いと `all x: Q | ...` が恒偽になり 4-queens が UNSAT に。
  回帰テスト `all_over_free_relation_gates_body_by_membership` 追加。
- 受け入れ: 解が制約式を満たすことを Evaluator で再検証 ✓

### Iter 6: Solver ファサード + 実例題スイート ✅ 完了(2026-08-24、テスト+1、ベンチ導入)
- `Solver{SolverOptions}::solve(arena,formula,bounds)->Solution` 統合
  (`src/solver.rs`。SAT モデルは自動 materialize、`solve_with` で任意
  SatSolver 注入可)。`TranslateError::Solver` 追加
- 例題スイート `tests/examples_suite.rs`(11 ケース期待表):
  queens{2,3,4,6} / pigeonhole{3x2,3x3,4x3} / coloring(triangle2/3,
  path2color, k4e_3color)。ビルダは `tests/puzzles.rs` 共通化
- criterion ベンチ(`benches/nqueens.rs`: queens8/10, pigeonhole_5x4,
  coloring_3col + `benches/heavy.rs`: queens16)
- デモ: `cargo run --release --example solve -- queens16` → SAT、盤面表示
  (177s、翻訳支配。12-queens 17.5s)
- **バグ発見(エンコード側)**: join の向き(`~IN.h` ≠ `h.~IN`)と
  自由関係の upper bound を universe 全体に取ってしまう誤りを例題表で検出。
  エンジン本体のバグではなく、例題ビルダの修正で解決
- 受け入れ: 例題表全一致 ✓ 性能レポート初版は `docs/perf-report.md`

### Iter 7: 時制拡張 ✅ 完了(2026-08-24、テスト+6)
- `temporal.rs` 新設: TemporalBoundsExpander 移植(ExplicitUnrolls=true、
  未来演算子フラグメント)。Time{i}_0 状態アトムを宇宙へ追加、変数関係に
  時間拡張関係 `r$t`(アリティ+1)を生成、$t_first/$t_last/$t_next/$t_loop
  補助関係とトレース公理(全単射な next、FIRST.*PREFIX=STATE、LOOP one)を構築
- ltl2fol 書き換え: PRIME / always / eventually / until / releases を
  極性(NNF)伝播つきで純 FOL へ変換。upTo 式は Java 版を忠実移植。
  過去演算子(historically/once/before/since/triggered)と unrolls>1 は明示拒否
- TemporalInstance(LASSO: states + loop_state)抽出と
  TemporalEval(地平線 = steps+cycle の有限スキャン)による検証
- `Solver::solve_temporal()` ファサード統合
- **既存バグ3件を発見・修正**:
  1. `bmatrix::closure_transitive` が反復平方で冪を取りこぼす(循環グラフの
     対角成分欠落)→ 線形累乗に修正
  2. `FolTranslator` の ReflexiveClosure が推移閉包を計算していなかった
     (恒等写像との union のみ)→ closure_transitive+iden に修正
  3. `Evaluator` の Subset 比較が逆方向(a⊇b)→ a⊆b に修正
- テスト+6: エキスパンダ構造/unrolls拒否/token-ring SAT安定性(steps=4,5,6)/
  矛盾仕様 UNSAT 安定性(steps=2,3,5)/until のステップ感受性/静的関係複製
- デモ: `cargo run --release --example ringt -- 4` → SAT ラッソ表示+検証
  (≈1ms)。steps=3 は UNSAT(4周期のトークンは3状態で閉じない)= ステップ
  感受性の実証。受け入れテストは steps 変更に対する結果安定性で代用
  (未来限定のため unrolls は常に 1 = Java の past_depth 挙動と一致)

### Iter 8: 分解ソルバ — PardinusBounds / decomp ✅ 完了(2026-08-24、テスト+2)
> 本体(Iter1-7+バックログ)完成を受け、ユーザ指示で着手。
- `pardinus.rs` 新設:
  - `PardinusBounds`: **イミュータブルビルダー**(部分関係マーク/targets/
    weights/記号上下限)。`resolve_symbolic(env)` で Instance 環境から
    記式評価して具体化 — synchronized 状態機械の代替設計
  - `slice_formula`: DecompFormulaSlicer 移植(トップレベル連言を
    部分関係集合で 2 分割)
  - `solve_dynamic`: 動的2段階の直列実行。ステージ1(部分スライス)→
    **blocking clause による部分モデル探索(上限16回)** → ステージ2
    (完全式+部分関係固定)。時制問題は `solve_temporal_with(anchors)`
    経由で展開宇宙のまま固定する
  - `solve_static_components`: トップレベル連言を共有関係グラフの
    連結成分へ分解し独立求解・マージ。どれか UNSAT なら全体 UNSAT
- PARALLEL 実行と amalgamated/integrated の自動統合は対象外(文書化済み)
- デモ: `cargo run --release --example decomp`
  - 静的: 鳩巣(SAT成分)+三角形2彩色(UNSAT成分)→ 全体UNSATを
    UNSAT成分のみで決定(688µs)
  - 動的: token-ring 2段階 → SAT ラッソ表示+検証(39ms)
- 受け入れテスト(tests/decomp.rs): 動的パリティ(plain==dynamic)、
  UNSAT 伝播、静的成分の独立判定 ✓

### Iter 9: UNSAT コア / prover 機能 ✅ 完了(2026-08-24、テスト+11)
- `ipasir_failed` 実装(user指示どおり **failed assumptions 前提**の設計):
  - alloy-ipasir: `Backend::failed`(CaDiCaL `failed()` を委譲)、worker が
    UNSAT 後の失敗仮定スナップショット(`failed_of`/`failed_core`)、
    `Session::failed`、C ABI `ipasir_failed` + 非同期ABI
    `alloy_worker_assume`/`alloy_worker_failed`(仮定は solve で drain)
  - kodkod: `SatSolver` に assume/failed/failed_core/supports_assumptions
    追加。RecordingSolver は全列挙+削除フィルタで**厳密最小コア**
  - cnf.rs: `translate_conjunct_def` — 各連言項を**単位節なしで定義のみ**
    翻訳し符号付き根リテラルを返す(kodkod の selector axiom の仮定版)。
    極性最適化を無効化し全ゲートに完全定義(共有ゲートの意味論保護)
- `ucore.rs` 新設:
  - `conjuncts_of`(Nodes.conjuncts 相当の連言フラット化)
  - `solve_core_with` / `Solver::solve_core`: 各トップレベル連言を selector
    仮定として解き、UNSAT 時は失敗仮定→**RCE相当の削除フィルタ最小化**
    (各メンバー1回の除去試行=RCEStrategy の root 当たり1試行と同等)。
    定数 false 連言は即自明コア、恒真連言は最初から除外
  - CNFレベル API: `SoftGroup` + `extract_cnf_core`(hard節+softグループ、
    selector 変数エンコード)。AST翻訳なしで使える
- デモ: `cargo run --release --example sudoku_core --features ipasir`
  - 可解 4x4 数独 → SAT 盤面表示
  - 矛盤(同値2ヒントが同一行)+無関係ヒント → UNSAT、初期 failed=
    最小コア={r0c0=1, r0c2=1} を 3 ソルブで特定
- 受け入れテスト(tests/ucore.rs、計9): ListDebug 的縮小シナリオ
  (独立矛盾2組+恒真フィラー7連言 → コア縮小・各メンバー必要性検証)、
  culprit 連言への逆引き、SAT時コア空+Evaluator再検証、
  自明 false 連言、CNFレベル4件(RecordingSolver で ipasir 不要)。
  alloy-ipasir 側 +2(session/非同期ABIの failed テスト)
- 設計記録: Proof/ResolutionTrace の Rust 版設計を
  `docs/pardinus-core-survey.md` §7 に記載(仮定ベースでは不要だが
  minisatprover 完全互換に必要になる場合の設計)

### Iter 10: Java 逆統合 — Rust エンジンの JNI 公開
- C ABI(`alloy_engine_*`)+ JNI ラッパ、`SATFactory` ではなく
  **エンジン差し替え**レベルの API(Alloy CLI/GUI に `--engine rust`)
- 段階導入: まず CLI exec のみ
- デモ: `dist.jar exec --engine rust -f ring.als` が Java エンジンと同結果
- 受け入れ: 全数テスト(69 例題)の Rust エンジン走査レポート

### Iter 10: Java 逆統合 — Rust エンジンの JNI 公開 ✅ 完了(2026-08-24、テスト+2)
- 新クレート `alloy-engine-rs`(cdylib): 問題直列化フォーマット **ARE1**
  (bitwidth/atoms/relations+bounds/variables/ノードDAG/root を varint+zigzag
  でエンコード。ノードタグは kodkod-rs の ast enum と1:1)→ デコードして
  `Solver::solve` → 答え ASAT(関係毎タプル索引)/AUNS/AERR を返す。
  C ABI `alloy_engine_solve`/`alloy_engine_free_buffer` + JNI
  `RustEngineProxy.solveNative(byte[])→byte[]`
- Java 側(org.alloytools.alloy.core):
  - `RustSerializer` — kodkod Formula/Expression/IntExpression/Decls/Bounds を
    子優先+メモ化で ARE1 へ直列化、答えを kodkod Instance/Solution へ復元
    (TupleFactory.tuple(arity,index))。非対応構文は ErrorAPI で明示拒否
    (時制/RelationPredicate/lone・one量化子)
  - `RustEngineProxy` — NativeCode.getLibrary("alloy_engine") でロード
    (`-Dalloy.native.lib.alloy_engine=<so>` 上書き可)
  - `A4Options.engine` 新設 + `A4Solution.solve()` 冒頭で分岐(KKTransformer
    と同型の差し替えポイント)、`CLI exec --engine rust` 配線(CLIのみ=段階導入)
- デモ: `dist.jar exec --engine rust -f ring.als` → SAT(Javaエンジンと同結果)
- 受け入れ: 例題スイート走査(`scripts/sweep-engines.sh`)—
  extra/models 全 **83 モデル**を両エンジンで実行し**結果100%一致**
  (81モデルのSAT/UNSAT完全一致 + 2モデルは両エンジン同一の型エラー=
  高階量化でスキョム不可)。詳細は `docs/engine-sweep-results.txt`
- 既知の v0 制限: UNSATコア/proof 連携なし(Solution.unsatisfiable(stats,null))、
  skolemDepth は Rust 側設定に未接続、時制コマンドは明示拒否

## バックログ(未確定・優先度順)
1. ~~Simplifier/最適化パス~~ ✅ 完了(2026-08-24): Comparison を疎キー
   ユニオンで生成(容量全走査を撤去)、BoolFactory fold に補文リテラル
   打ち切り+吸收則を追加。queens10 -81% / queens16 -86%
2. ~~Skolem 化(HASLab 拡張含む)~~ ✅ 完了(2026-08-24): `skolem.rs`
   (静的: 定数/関数証人、上限境界からの自動バウンド、全域性制約)+
   temporal 拡張(時間列付き証人関係、`all s:STATE | sk⋈s⊆D@s` 制約)。
   `SolverOptions::skolemize`(既定 OFF)。等充足性の注意書きは
   モジュールドキュメント参照
3. ~~PARALLEL 分解モデル(スレッドプール)~~ ✅ 完了(2026-08-24):
   `solve_static_components_parallel` — std::thread::scope + アトミック
   ワークプル(依存ゼロの軽量プール)。ワーカー毎に AstArena をクローン
   (RelationPool は Arc 共有でインターニング整合)、max_threads で上限制御。
   マージはコンポーネント所有関係でゲートし未使用関係の空上書きを防止
   (直列版にも同修正)。パリティテスト(並列/直列/単体+マージインスタンス検証)追加
4. ~~cargo-fuzz による cnf/bool 層の堅牢化~~ ✅ セットアップ完了
   (2026-08-24): `alloy-kodkod-rs/fuzz/` に 3 ターゲット
   (bool_circuit_cnf / closure_warshall / intset_ops)。実行:
   `cd alloy-kodkod-rs && cargo +nightly fuzz run -O --fuzz-dir fuzz <target>`
   ※ nightly toolchain 必須。初回実行で CNF 検証ハーネスの過剰制約を検出・修正済み
5. ~~IntSet bitset 実装差し替え~~ ✅ 完了(2026-08-24): ハイブリッド
   Sparse(sorted Vec)/Dense(bitset) 自動切替。密な積境界で語単位集合演算。
   ベンチ回帰なし(pigeonhole 微改善)、BTreeSet オラクル比較テスト追加

## リスク登録
| リスク | 影響 | 対策 |
|---|---|---|
| 挿入順喪失で CNF 非決定性 | 中 | Bounds 実装時に順序テストを必須化 |
| int bitwidth 越え挙動の差異 | 中 | Iter 4 で Java 差分テスト |
| 時制 unroll の爆発 | 高 | Iter 7 は小型例題に限定し段階拡大 |
| JNI エンジン API の肥大化 | 中 | Iter 10 は CLI 最小面から開始 |
