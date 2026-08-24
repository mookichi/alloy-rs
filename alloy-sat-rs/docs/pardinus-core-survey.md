# Pardinus コアデータ構造調査(Rust移行 第1段)

対象: `org.alloytools.pardinus.core/src/main/java/kodkod`(Java 25 ビルドで検証済み)

## 1. パッケージ別規模

| パッケージ | ファイル数 | 行数 | 役割 |
|---|---|---|---|
| `instance` | 8 | 3,432 | **本次移行対象**: Universe/Tuple/TupleSet/Bounds 系 |
| `util.ints` | 22 | 6,425 | IntSet/IntVector/SparseSequence(疎整数集合) |
| `ast` | 52 | 8,489 | 式/論理式の不変 DAG + visitor |
| `engine` | 120 | 26,113 | 翻訳(fol2sat/ltl2fol/decomp/ucore/bool)+ソルバ |
| `solvers` | 7 | 1,175 | SATFactory 橋口 |

移行順序の根拠: instance → util.ints は依存が最も少なく純粋なデータ構造。
ast はその次(不変木なので所有権模型と好相性)。engine は最終段。

## 2. 各構造の正体

### Universe (189 行)
- `Object[] atoms`(重複禁止・順序保持)+ `HashMap<Object,Integer> indices`
- **equals/hashCode 未オーバーライド = 参照同一性**が等価の意味論
- 実用上のアトムは文字列ラベル("Person0" 等。時制展開は接尾辞で複製)

### Tuple / TupleFactory (133+394 行)
- 実装クラス `IntTuple` は **(arity, index) のみ保持**。atom 列は `index` を
  base=u.size の n 桁数として `atomIndex(i) = (idx / base^(arity-1-i)) % base`
  で都度復元
- `product`: `index' = idx0 * base^arity1 + idx1`
- 容量 = `u.size^arity`、超過時 `CapacityExceededException`

### TupleSet (418 行)
- **実態は arity + IntSet(タプル索引の疎集合)**。全集合演算を IntSet に委譲
- `indexView()` で内部 IntSet を公開(翻訳器が直接利用)
- product/project/contains/add/remove すべて索引空間の演算

### Bounds / PardinusBounds (409+971 行)
- Bounds: `LinkedHashMap<Relation,TupleSet> lowers/uppers`(挿入順が翻訳の
  決定性に影響)+ `TreeSequence<TupleSet> intbounds`(整数→単要素 TupleSet)
- PardinusBounds([HASLab] 分解対応)追加フィールド:
  - `lowers_symb/uppers_symb: Map<Relation, Expression>`(記号境界)
  - `targets / weights`(解探索の誘導)
  - `amalgamated / integrated`(静的×変動パーティション統合)
- **ast.Expression に依存するため AST 移行後に移植**

### Instance / TemporalInstance (372+546 行)
- Instance: `Map<Relation,TupleSet> tuples` + int 境界
- TemporalInstance: `List<Instance> states` + loop/unrolls による
  LASSO 展開(`stateIdomify`)

## 3. util.ints の構成

- 集合: `IntSet`(IF)/ `IntBitSet` / `ArrayIntSet` / `IntTreeSet`
- ベクトル: `IntVector`(ArrayIntVector)
- 疎列: `SparseSequence<T>`(ArraySequence/TreeSequence/RangeSequence)
- 工場: `Ints.bestSet(capacity)` が密度で実装選択

## 4. Rust 設計方針

### 整数幅ポリシー(ユーザ指示)
**配列の添字・カウンタ以外の整数は i64 に統一する。**
タプル索引・容量(`size^arity`)・IntSet 要素はすべて `i64`。
これにより Java の `Integer.MAX_VALUE` 容量チェック(CapacityExceededException)
という制約が実質撤廃される(オーバーフローは checked 演算で明示的エラー)。
usize は添字とカウンタのみに限定。

| Java | Rust | 備考 |
|---|---|---|
| `int index` | `i64` | タプル索引 |
| 容量 `size^arity` | `i64`(checked_pow 相当) | 超過時 CapacityError |
| arity | `u32` | 次元カウンタ |
| atom→index | `HashMap<Arc<str>, u32>` | u32=添字 |
| Universe 参照同一性 | `Arc::ptr_eq` | Java equals が identity のため一致 |
| IntSet | 自前 `IntSet(Vec<i64>` ソート済) | 後続で bitset/tree 実装へ差し替え可 |
| LinkedHashMap(挿入順) | `Vec<RelationId>` + HashMap | Bounds 移行時 |
| Relation オブジェクト同一性 | インターニング `RelationId(u32)` | AST 段で導入 |
| Node DAG | アリーナ id + enum | visitor は match に置換 |

### 所有権
- `Universe` は構築後不変 → `Arc<Universe>` 共有
- `Tuple { universe: Arc<Universe>, arity: u32, index: i64 }`(遅延復元)
- `TupleSet { universe: Arc<Universe>, arity: u32, set: IntSet }`

## 5. 実装状況

- [x] `alloy-kodkod-rs::intset` — i64 ソート済 IntSet(和/交/差/min/max)
- [x] `alloy-kodkod-rs::universe` — Arc<str> アトム、参照同一性
- [x] `alloy-kodkod-rs::tuple` — (arity,index) 遅延復元/product
- [x] `alloy-kodkod-rs::tupleset` — 索引集合演算/product/project/range/area
- [x] `alloy-kodkod-rs::ast` — アリーナ化完了: RelationId/VarId インターニング、
      ExprId/IntId/FormulaId/DeclsId の型別アリーナ、Java準拠の arity 検証
      (union等一致/join l+r-2>=1/unaryはarity2/SUM cast は unary/Decl 規則/
       compose の 0-1-2-N 規約/TRUE-FOLD)、Temporal(PRIME) 対応
- [x] `alloy-kodkod-rs::bool` — ブール回路アリーナ(BoolRef=符号付き参照。
      Not はスロットを消費せず符号反転=Java の label 反転と同一意味論)。
      工場内フォールディング(TRUE/FALSE 吸収・冪等 dedup・ITE 定数畳み込み)、
      (op, 整列済子) キャッシュによる構造共有
- [x] `alloy-kodkod-rs::sat` — SatSolver トレイト + 総当たり RecordingSolver
      (テスト用、≤22 変数)
- [x] `alloy-kodkod-rs::cnf` — Bool2CNFTranslator 移植: 定義的翻訳
      (Tseitin)+ Java 同等の極性最適化(positive/negative 出現ビット)、
      ITE 6節(強化節含む)、トップレベル AND は入力 unit 節パス。
      40 ケースファズで回路評価↔CNF 充足可能性の同値性を検証
- [x] `alloy-kodkod-rs::ipasir_bridge`(feature `ipasir`)— SatSolver を
      alloy-ipasir Session(CaDiCaL)に橋渡し。回路→CNF→CaDiCaL の
      エンドツーエンドファズテスト(30ケース)通過
- [x] `relation` — RelationPool(RwLock インターニング)を抽出し AstArena も委譲。
      AST/インスタンス層で同一 RelationId 空間を共有
- [x] `bounds` — Bounds: 挿入順保持(Vec+HashMap)、intbounds(BTreeMap)、
      Java同等の検証エラー(arity/universe/lower⊂upper/int単一要素)、
      Display は Java toString と同一フォーマット
- [x] `instance` — Instance: add/add_int/tuples/find_relation_by_name、
      挿入順保証(JavaのHashMapより決定的)
- [x] デモ `examples/ring_bounds.rs`(ring.als 相当バウンド構築+ダンプ)
- [x] `dimensions` — Dimensions: square/rectangular/dot/cross/transpose、
      行優先 flat↔vector 変換(Java convert と同一式)
- [x] `bmatrix` — BooleanMatrix: 疎セル(BTreeMap)+BoolCtx(Rc<RefCell>)。
      not(欠損→TRUE)/and(共通鍵交差)/or(和集合)/choice(ITE)/cross
      (AND結合・FALSE節スキップ)/transpose。DefCond と project は
      Iter 4(int)/Iter 8(decomp)へ持ち越し
- [x] デモ `examples/matrix_demo.rs`(2×2 演算の真理値表照合)
- [x] `bmatrix` 追加: `join`(最終列×先頭列のネスト結合、OR蓄積)、
      `closure_transitive`(冪乗反復 n-1 回)
- [x] `bmatrix` 追加: `override_values` — Kodkod定義を忠実移植:
      m[i] = other[i] ∨ (this[i] ∧ ¬OR(other[row(i)]))
      (※ 全タプルpointwise ite ではない。行=先頭列グループ単位で置換)
- [x] `fol` — FOL2BoolTranslator 関係子セット:
      リーフ解決(境界 lower=TRUE / upper\lower=新変数、キャッシュ)、
      univ/iden/none 定数行列、2項/多項集合演算、join、^/*、
      比較(=/in は全位置 XNOR/包含のAND)、quantifier(all/some 宣言直積)、
      comprehension、multiplicity(some/one/lone)、if式(choice)
- [x] テスト13件: 到達可能性・lone/one・閉包・iden・差差/上書き・
      2変数量化子・comprehension・if分岐など
- [x] デモ `examples/fol_demo.rs`(feature ipasir):
      関係nextの機能性+無自己ループ等3ケースを CaDiCaL で解く
- [x] `int` — TwosComplementInt 移植(IntCircuit, リトルエンディアン):
      リップルキャリー加減算(幅=min(max+1,bw))、シフト加算乗算+
      bitwidth 切り詰め、非回復除算(Parhami; 商/余)、bitwise AND/OR/XOR/
      NOT、shl/shr/sha(下位ビット mod width 方式=Javaループ相当)、
      choice、eq/lte 辞書式比較(+neq/lt/gt/gte 恒等変換)
- [x] FolTranslator 拡張: set_bitwidth(既定4)、cardinality(1bit zero-ext
      加算ツリー)、sum(intBounds の位置→値マップと cell の choice 積和)、
      Sum{decls}、IntComparison 全6種、FromInt(int境界アトム行列)
- [x] BoolFactory::ite 簡約規則追加(c/T/F 分岐の標準8則)。
      定数分岐が Ite 下に残留し CNF 翻訳の ConstantInside を招く問題を解消
- [x] テスト+13(回路fuzz 6: 演算/比較/シフト/除算網羅、FOL int 7:
      cardinality・加算・順序・sum境界・FromInt・宣言sum・div/mod)
- [x] 既知差異: overflow ゲート(DefCond系)は未実装(Alloy nooverflow
      相当は後続)。INT_MIN/-1 除算は bitwidth 内で wrap
- [x] 性能: BoolFactory::eval_memo — 評価キャッシュは**ハッシュ不使用**。
      アリーナslot番号を索引とする dense Vec<Option<bool>>(符号は非保持・
      読出し時に適用)。IntCircuit::value_of と BooleanMatrix::eval_dense
      は同一モデルの全bit/全セルで1つのメモを共有。
      int_circuit ファズ: 約110秒 → 0.43秒(約250倍)
- [x] ハッシュ方針: 名前キー(Universe/インターナ)のみ std SipHash。
      数値ID(RelationId等)は全て Vec 直接索引。ゲートキャッシュ
      (GateKey)のみ現状 SipHash — 必要時は依存ゼロのFxHash風実装へ
- [x] ast(アリーナ化)— AstArena で実装済み(変数/式/整数/論理式/宣言を
      フラット Vec+整数 ID で管理、RelationPool は Arc 共有)
- [x] PardinusBounds(記号境界・分解)(Iter11、上記 engine の項参照)
- [x] `eval` — Evaluator: Instance 上の AST 再評価(集合演算・量化子・
      comprehension・closure(Warshall)・cardinality/sum/int 演算)
- [x] `fol` 材料化 — VarOrigin(slot→relation→tuple_index)追跡 +
      materialize(): SAT モデルから Instance 構築。
      **宣言ドメインのメンバーシップ・ゲート**(ALL=`ℓ⇒body`/SOME=`ℓ∧body`)
      を実装 — 自由関係上の量化で必須(kodkod Translator 同様)。
      4-queens E2E(tests/solution.rs): solve→materialize→Evaluator 再検証
- [x] engine.fol2sat 翻訳(関係子セット+int+材料化。残: Project、nooverflow)
- [x] `solver` — Solver ファサード(SolverOptions/Solution)。solve_with で
      任意 SatSolver 注入、ipasir 便利コンストラクタ
- [x] 例題スイート(tests/examples_suite.rs + puzzles.rs): queens/pigeonhole/
      coloring 11 ケース期待表。criterion ベンチ(benches/nqueens, heavy)
- [x] **バグ修正(Iter6-7で発見)**:
      closure_transitive の反復平方→線形累乗(循環時の対角欠落)、
      FolTranslator ReflexiveClosure が推移閉包を欠く、
      Evaluator Subset 比較の逆方向 — いずれも temporal 検証で顕在化
- [x] `temporal` — ltl2fol 移植(未来フラグメント): TemporalBoundsExpander
      (Time アトム追加・r$t 展開・トレース公理)、LTL2FOL 書き換え
      (PRIME/always/eventually/until/releases + NNF 極性伝播。upTo 忠実移植)、
      TemporalInstance(LASSO)抽出、TemporalEval 地平線スキャン検証。
      過去演算子/unrolls>1 は明示拒否(Java の past_depth=1 相当)
      既知差異: 宇宙への状態アトムは「追加」(Java は前置)— 挿入順は
      変数番号の決定性に影響するが内部で一貫
- [x] `skolem` — 静的 Skolem 化: 正極 ∃ を定数/関数証人関係へ置換、
      upper_bound_expr によるドメイン上限から自動バウンド、関数は全域性制約
      (`all u⃗ | $sk(u⃗) ⊆ D`)。非対応ドメイン(join of comprehensions 等)は
      量化子を保持して安全縮退。時制版は temporal.rs 内(HASLab: 時間列付き)
- [x] `intset` — ハイブリッド Sparse/Dense 自動切替(DENSE_MAX=2^22、
      密度しきい値で昇格)。語単位 and/or/not 集合演算。
      BTreeSet オラクル比較プロパティテスト(tests/intset_hybrid.rs)
- [x] fuzz — cargo-fuzz 3ターゲット(bool_circuit_cnf / closure_warshall /
      intset_ops)。実行には nightly 必要。詳細は fuzz/ ディレクトリ
- [x] `pardinus`(Iter8)— PardinusBounds イミュータブルビルダー(部分/
      targets/weights/記号境界+resolve)、DecompFormulaSlicer 移植、
      動的2段階(blocking 探索つき・時制は展開宇宙アンカー方式)、
      静的連結成分分解+マージ。非対応: PARALLEL/amalgamated 自動統合/
      多段探索の完全版
- [x] PARALLEL 分解(バックログ3)— thread::scope ワークプル、
      AstArena Clone 化(プール Arc 共有)、所有関係ゲート付きマージ。
      `Solver::solve_decomposed_parallel(arena,f,bounds,max_threads)`
- [x] `ucore`(Iter9)— UNSAT コア抽出(`-core=rce` 相当)。
      **仮定ベース**: 各トップレベル連言を定義のみ翻訳
      (`translate_conjunct_def`、極性最適化 OFF で全ゲート完全定義、
      符号付き根リテラル返却)し selector を SAT assumption 化。
      UNSAT 後の failed assumptions(CaDiCaL `failed()` /
      `ipasir_failed`)で初期コア→削除フィルタ最小化(各メンバー1試行 =
      RCEStrategy 相当)。CNFレベルは `SoftGroup`+selector 変数エンコード。
      Java の unit-clause selector + resolution proof 方式との差異:
      proof トレース不要の代わりに assumptions 対応ソルバが前提
      (CaDiCaL ○ / Splr ✗ / RecordingSolver 全列挙)

- [x] `engine`(Iter10)— **Java 逆統合**: alloy-engine-rs cdylib(ARE1 ワイヤ
      フォーマット: formula DAG+bounds 直列化、C ABI + JNI)、Java 側
      RustSerializer/RustEngineProxy/A4Options.engine/CLI `--engine rust`。
      例題 83 モデルで両エンジン結果 100% 一致(sweep-engines.sh)。
      非対応: 時制・RelationPredicate・lone/one 量化子(明示拒否)
- [x] PardinusBounds(記号境界・分解)(Iter11)— ARE2: options+
      partials+記号境界 trailer。Java 側の式境界を Evaluator で実体化、
      dynamic 2段階分解(stage-1 投影→resolve_symbolic→stage-2)を
      JNI 経由で有効化(`--decompose hybrid`)。静的/並列分解も接続

## 6. リスク・論点

1. **アトム型**: Java API は Object を許容するが、Alloy 翻訳器の実使用は
   String のみを確認(A4SolutionWriter/TranslateAlloyToKodkod)。v0 は
   `Arc<str>` で固定し、必要になった時点で汎化
2. **挿入順**: Bounds の LinkedHashMap 反復順が CNF 変数番号に波及し、
   生成モデルの決定性/再現性に関与 → Vec+HashMap で順序保持必須
3. **IntSet 性能**: 密な大容量セット(allOf 等)では bitset が有利。
   trait 境界を保ち、ベンチマーク後差し替え
4. **PardinusBounds の synchronized/integrated(Solution)**:
   分割統合はミュータブルな状態機械であり、Rust では builder/イベント列へ
   再設計が必要(API 単純移植不可)

## 7. Proof / ResolutionTrace の Rust 版設計(Iter9 記録・未実装)

Java(minisatprover + RCEStrategy)は解像度証跡を前提とする:

- `ResolutionTrace`: 学習節を `(clause, antecedents)` 付きで保持し、
  `learnable(A)`/`directlyLearnable(A)` で仮定節集合 A から導出可能な
  resolvent 集合を計算。`LazyTrace` が縮小試行の結果を遅延合成する。
- RCEStrategy は「根 selector 変数のうち現在コア末尾の unit に接続される
  ものを1つ除去した CNF 部分集合」を `StrategyUtils.clausesFor` の逆連鎖
  (maxVariable 到達可能性)で切り出し、ドライバ(MiniSatProver.reduce)が
  新しいソルバで再 UNSAT を確認して置換する。

Rust 版を将来実装する場合の設計(本イテレーションでは見送り):

```
struct ResolutionTrace {
    // axioms: 入力節(翻訳ログの root 割当て付き)
    axioms: Vec<(Clause, Option<ConjunctId>)>,
    // learned: 導出順に (resolvent, antecedent pair)
    learned: Vec<(Clause, [u32; 2])>,
}
impl ResolutionTrace {
    fn learnable(&self, subset: &[usize]) -> Vec<usize>;   // 逆連鎖到達
    fn core_units(&self, subset: &[usize]) -> Vec<i64>;     // tail units
}
```

- 取得経路は2案: (a) CaDiCaL の proof log(DRAT)をパースして再構築、
  (b) `ipasir_set_learn`(学習節コールバック)で antecedent 無しの近似
  トレースを蓄積。(a) が完全互換だが DRAT パーサが必要。
- 仮定ベース(現 ucore.rs)との使い分け: 高レベル制約粒度のコア抽出だけ
  なら assumption 方式で十分。**節粒度**の最小化や proof 出力を要する場合
  (minisatprover 完全互換、Sudoku `-core=oce`)に ResolutionTrace を
  追加する。incremental 翻訳では Java 同様 logging を禁止する。
