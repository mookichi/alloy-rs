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

### Iter 6: Solver ファサード + 実例題スイート
- `Solver{options,bounds,formula}->Solution` API 統合
- Java 側 69 例題のうち純粋 kodkod 系(csp/sudoku/tptp 小規模)を
  Rust 統合テスト化(期待 SAT/UNSAT 表)
- criterion ベンチ導入(NQueens16 等 5 题)
- デモ: `cargo run --example solve -- queens16`
- 受け入れ: Java 同一例題との結果一致+性能レポート初版

### Iter 7: 時制拡張
- ltl2fol 方式(TemporalBoundsExpander による unroll)から着手
- ast の時制ノード(PRIME/always/until…)の翻訳、TemporalInstance/LASSO
- デモ: RingT 系の小型時制例題を解く
- 受け入れ: unrolls 変更に対する結果安定性テスト

### Iter 8: 分解ソルバ — PardinusBounds / decomp 【優先度低下・後回し】
> ユーザ判断(2026-08-24): Java版並列ソルバはほぼ壊れているため移行優先度低。
> 本体が完成した後に要否を再評価する。
- PardinusBounds(記号境界・targets/weights・amalgamated/integrated)の
  builder 再設計(synchronized 状態機械をイミュータブル化)
- 静的/動的分解(DProblemExecutor)の直列実装(PARALLEL は後日)
- デモ: HotelP 分解例題の Rust 実行
- 受け入れ: 分解=非分解で同一インスタンス集合(小規模)

### Iter 9: UNSAT コア / prover 機能
- alloy-ipasir へ failed assumptions(CaDiCaL `failed()`)露出を追加
  ※ minisatp 代替要件(ListDebug/Sudoku 例題で裏付け済み)
- RCEStrategy 相当のコア最小化、Proof/ResolutionTrace の Rust 版設計
- デモ: Sudoku -core=rce 相当のコア抽出
- 受け入れ: ListDebug の Rust 版がコア縮小に成功

### Iter 10: Java 逆統合 — Rust エンジンの JNI 公開
- C ABI(`alloy_engine_*`)+ JNI ラッパ、`SATFactory` ではなく
  **エンジン差し替え**レベルの API(Alloy CLI/GUI に `--engine rust`)
- 段階導入: まず CLI exec のみ
- デモ: `dist.jar exec --engine rust -f ring.als` が Java エンジンと同結果
- 受け入れ: 全数テスト(69 例題)の Rust エンジン走査レポート

## バックログ(未確定・優先度順)
1. Simplifier/最適化パス(unit propagation 補強、部分式共有強化)
2. Skolem 化(HASLab 拡張含む)
3. PARALLEL 分解モデル(スレッドプール)
4. cargo-fuzz による cnf/bool 層の堅牢化
5. IntSet bitset 実装差し替え(criterion 計測後)

## リスク登録
| リスク | 影響 | 対策 |
|---|---|---|
| 挿入順喪失で CNF 非決定性 | 中 | Bounds 実装時に順序テストを必須化 |
| int bitwidth 越え挙動の差異 | 中 | Iter 4 で Java 差分テスト |
| 時制 unroll の爆発 | 高 | Iter 7 は小型例題に限定し段階拡大 |
| JNI エンジン API の肥大化 | 中 | Iter 10 は CLI 最小面から開始 |
