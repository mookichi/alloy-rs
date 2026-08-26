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

### Iter 11: Wire v2 — SolverOptions + 動的分解の JNI 有効化 ✅ 完了(2026-08-25、テスト+2)
- **ARE2** フォーマット: ヘッダに options byte(skolemize bit + decompose
  mode 2bit)+ max_threads、dynamic 時は末尾に stage-1 partial 関係マーク +
  記号境界エントリ(関係, side, expr node id)。ARE1 も引続きデコード可。
- Java `RustSerializer`: A4Options(skolemDepth / decompose_mode /
  decompose_threads)を伝播。**記号境界の実体化(materialize)**を実装 —
  Alloy は sig/フィールド境界を式で格納するため、Evaluator で固定点まで
  評価し具象タプル集合へ変換してから書き出す。IMPLIES/IFF は脱糖
  (!l∨r、(!l∨r)∧(!r∨l))して対応。BinaryFormula のみならず NaryFormula
  の整順も修正(ノード数は子の後に確定するためサイドバッファ方式)
- Rust `solve_problem_inner`: Decompose::Static/Parallel/Dynamic を
  facade(solve_decomposed / _parallel / solve_dynamic)へ接続。
  dynamic は ARE2 trailer から PardinusBounds を構築し、stage-1 インスタンス
  を投影(universe 再エンコード+時間列除去)した上で `resolve_symbolic` し
  stage-2 境界へ適用 — Pardinus「stage 2 consumes stage 1」を実装
- CLI `exec --decompose off|hybrid|parallel`(rust エンジン専用)、
  A4Options.dup() が engine をコピーしていなかったバグを修正
- 受け入れ: ring.als が rust/hybrid・parallel・plain の全モードで SAT
  (Java と一致)。skolem テスト(depth 3)SAT 一致。例題 83 モデル再走査で
  引続き結果 100% 一致
- 既知の v0 制限: 記式境界の wire 直送(実体化せず Rust 側評価)は未対応、
  temporal コマンドは引続き明示拒否

### Iter 12: UNSAT Core の Java 統合(--core)✅ 完了(2026-08-25)
- **Wire**: ARE2 options byte に bit3 = want_core を追加。回答マジック
  `AUNC` = varint(件数) + 犯者トップレベル連言の DAG ノード位置列。
  `Problem` に `formula_pos_by_id`(FormulaId→ノード位置)を追加
- **Rust**: `solve_problem_inner` で want_core 時は分解より優先して
  `Solver::solve_core`(選択子仮定 + RCE 最小化)を実行。SAT 時は
  CoreSolution.instance から通常 ASAT を生成
- **Java**: `RustSerializer.serialize` が `Serialized`(bytes +
  formulaById 逆引き)を返すように変更。`coreOf(answer)` が AUNC を
  `List<Formula>` へ解決。`readAnswer` は AUNC を AUNS 扱い(後方互換)。
  `A4Solution.rustCore` フィールド + doRust() で代入。
  A4Options.extractCore(dup() 対応)
- **CLI**: `exec --core`(rust エンジン専用ガード付き)。UNSAT 時に
  「unsat core (N): [i] 式...」を表示
- 受け入れ: unsat.als(#A=1 ∧ #A>1)で core=[#A=1, #A>1] を表示、SAT モデル
  では通常動作、--core 无しでは従来表示。wire.rs に are2_unsat_core 追加
  (some p ∧ ¬some p → 最小コア=両方)。workspace 全テスト green、
  clippy 0 警告、gradle test 成功

### 発見事項(Iter 12 作業中)

1. **sweep スクリプトが出力ディレクトリを作っていなかった**ため、
   Iter 10/11 の「83モデル 100% パリティ」記録は実質無意味(全行
   Error/Error の空一致)だったことが発覚。`scripts/sweep-engines.sh`
   に mkdir を追加し再計測した結果:
   - 実パリティ 34/83(SAT/SAT 25 + UNSAT/UNSAT 9)
   - rust 側未対応構文による Error 46(rust Error vs java SAT/UNSAT)
   - 双方エラー 2、タイムアウト 1
   - **真のミスマッチ 2**(addressBook2e.als / mediaAssets.als:
     rust SAT vs java UNSAT)
2. **`no` 式フォーミュラのデシュガー対応**(Iter 12 の副次修正):
   Java シリアライザが `no e` を `¬some e` として wire 生成するように
   変更(m15 最小ケースでの切り分け過程で no 自体は正しいことを確認)
3. **既知バグ → ✅ 修正完了(根因: fold() 吸収則の符号無視)**:
   「量化子内の含意 + 関係差分・和集合」パターンで偽 SAT。最小再現
   m15.als / repro_spurious_sat.rs(5変数量化含意、lo=空 hi=全体)。
   本日判明したこと:
   - **オラクル欠陥修正**: RecordingSolver が 22 変数超で総当たり不能の
     場合、未知を黙って UNSAT と報告していた(sat.rs)。panic で即死する
     よう改修。これによりユニットテストの期待値自体が汚染されていた
   - **バックエンド無関係を証明**: 同一 CNF を CaDiCaL と Splr の両方に
     投入 → どちらも SAT。モデルは全節を充足するが Evaluator による
     意味論検証で反例になっていない(=CNF が過少制約)
   - **極性最適化・AST共有・量化子駆動は全て否定的**:
     optimize_polarity=off でも発現、式ノード非共有でも発現、
     量子化機械を経由しない手動展開(env付き formula_ref × 32 バインディング
     を and で結合)でも発現 → fol.rs の env 付き本体翻訳の組合せで
     制約が失われているのが原因と特定
   - **差分プロパティテスト追加**(tests/differential.rs): ランダム小型
     問題を Solver と「全インスタンス列挙 × 独立 Evaluator」オラクルで
     比較(xorshift 決定論的シード、DIFF_SEEDS で件数制御)。
     現状 500 シードは通過 — 生成器の偏り改善が次ステップ

   - **✅ 根因特定・修正(2026-08-25)**: `bool.rs fold()` の吸収則が
     キッド ハンドルの**符号を無視**してマッチしていた。
     `AND(¬OR(y,x), x)` のような否定複合キッドが、`node(k)` 解決で
     内部の Or ノードを見て子に x を含むだけで吸収削除され、
     `¬(y∨x) ∧ x ≡ x`(実際は偽)という不当簡約が起きていた。
     これが量化含意の前件(¬some(...) 等、否定複合が多用される)で
     制約を消失させ、偽 SAT/擬似反例を生んでいた。
     **修正**: 吸収対象は正ハンドルのみに制限(`if k < 0 { return true }`)。
     - 検証: op_bisect 全変種 0/256 偽割当、repro_spurious_sat 3変種
       すべて UNSAT(ok)、CLI で m15.als UNSAT、addressBook2e.als は
       java と完全一致(delUndoesAdd/addIdempotent UNSAT ほか)、
       83モデル sweep で**応答レベルの矛盾 0件**(rust 未対応構文の
       Error 45件は従来通り別カテゴリ)
     - join_offbyone.rs: 回路レベルの最小回帰テスト(通過)

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

### Iter 17: 時制演算子拡張 — 過去時 LTL + Pardinus 固有演算子 ✅ 完了(2026-08-26)

Java Pardinus `LTL2FOLTranslator` の全演算子を Rust に移植。11 演算子を追加。

**Phase 1: 過去時 LTL (5 演算子)**
- `before P` — 前ステートで P が成立
- `historically P` — 過去全てで P が成立
- `once P` — 過去のいずれかで P が成立
- `a since b` — b が過去に成立し、それ以降 a が成立し続けた
- `a triggered b` — a が成立する限り b も成立した

**Phase 2: Pardinus 固有 (6 演算子)**
- `initially P` — ステート 0 で P が成立
- `goal P` — ステート N（最終）で P が成立
- `restore P` — ステート L（ループ開始）で P が成立
- `keeping P` — 全ステート（最終除く）で P が成立
- `consistently P` — サイクル全体で P が常に成立
- `regularly P` — サイクル中で P がいつか成立

**kodkod-rs 変更:**
- `TemporalFormulaOp` に 6 variant 追加
- `T::Prev` 追加 + `rev_trace_expr()` (逆トレース) + `down_to()` (backward 範囲)
- `Ltl2Fol::formula` で全 11 演算子の FOL 翻訳
- `TemporalEval::formula_at` で全 11 演算子の直接評価
- `expand_bounds` の `unrolls > 1` 許容 + 多重アンロール対応

**alloy-front-rs 変更:**
- lex: 11 キーワード追加
- ast: 11 `Formula` variant + `has_temporal()`
- parser: 前置 9 + 中置 2 = 11 パース規則
- lower: 11 低層化 + `subst_formula` + `replace_var_formula`

- **テスト**: temporal.rs 32 テスト(22 unit + 10 integration)
- **検証**: 全 72 テスト通過、clippy 0 警告、fmt グリーン

## リスク登録
| リスク | 影響 | 対策 |
|---|---|---|
| 挿入順喪失で CNF 非決定性 | 中 | Bounds 実装時に順序テストを必須化 |
| int bitwidth 越え挙動の差異 | 中 | Iter 4 で Java 差分テスト |
| 時制 unroll の爆発 | 高 | Iter 7 は小型例題に限定し段階拡大 |
| JNI エンジン API の肥大化 | 中 | Iter 10 は CLI 最小面から開始 |
