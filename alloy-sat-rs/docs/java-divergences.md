# Java Alloy との意図的差異

`alloy-front-rs` / `alloy-repl` における、Java版 Alloy (当リポジトリの
`org.alloytools.*`, Alloy 6系) と**意図的に変えている**仕様の一覧。
パリティを目指した箇所 (例: `sig X in Int` の受理、`=`/`!=` の関係専用化、
SUMキャスト、`for 8 Int` のbitwidth解釈) は含まない。

検証方法: Java側は `CompUtil.parseEverything_fromString` および
`A4Solution.eval` (MiniSat改め `minisat` 使用、bitwidth 4) で実測。
`Version.experimental=true` (現行既定) が前提。特に断りがなければ
solve時 (`run`/`check`) と `:eval` は Java と同義であることを確認済み。

## 1. 構文の拡張 (Javaは拒否、Rustは受理)

### 1.1 逆積 `<->`, `-<`
`a <-> b` および `a -< b` はいずれも `b -> a` (右辺→左辺の積) を表す。
`->` と同 precedence・左結合。密着時のみ演算子として認識し、
`a - <b` のように離れている場合は minus + 比較のまま。

- Java実測: `some A <-> some B` はパースエラー (`<->` は Alloy 6 の
  formula演算子ではない。同等の iff は `<=>` / `iff` で、両実装とも受理)。
- すなわち Java に存在しない純粋な拡張。`sig` フィールド型内
  (`in_sig`) では `arrow_type` 側が消費するため対象外。

### 1.2 bitwidth指定の語順バリエーション
Javaは `for 8 Int` のみ。Rustは以下も受理し、いずれも bitwidth 8 と解釈する:

- `for Int 8` (Java実測: パースエラー)
- `for exactly 8 Int` / `for exactly Int 8` (Java実測: パースエラー。
  Java曰く "the exactly keyword is redundant here since the integer
  bitwidth must be exact"。"対称性のための受理" として意図的に緩めている)

### 1.3 集合リテラル `{A, B, ...}`
`{` の直後が宣言でない場合、カンマ区切りの式並びを和集合として読む
(`{A, B}` = `A + B`、単要素 `{A}` や `{A.f, 1}` も可)。宣言が読める
 場合 (`{x: X, y: Y}`) はそちらを優先するため comprehension と競合しない。
formula位置 (`{A, B} = C`) でも比較の左辺として使える。要素内および
束縛ドメイン内の純粋なリテラル演算は畳み込む (`{1+1}` は `{2}`、
`{x : 1+2}` は `{3}`。`#A`/`sum`/変数を含む場合は関係式として読む)。

- Java実測: `{A, B}` は式・fact のいずれでもパースエラー。純粋な拡張。
- 対応する `1+1` の扱い: 式位置の `+` は Java 通り関係和だが、`:query`
  では純int形 (リテラル・`#A`・`sum`・それらの四則演算) を先にint評価
  するため `1+1` → `2` (算術和) を返す。Javaの `1+1` もint式であり、
  Evaluatorは `2` を返す。集合オペランドが混じる (`5 + A`) と関係側に
  回り和集合になる。

## 2. 意味論の差異

### 2.1 ~~`:query` における範囲外整数リテラルはエラー~~ → ラップに統一済み
当初 `:query` のみ範囲外リテラルを拒否していたが、Java実測
(`A4Solution.eval`, bitwidth 4: `100` → `{4}`、`-9` → `{7}`) に合わせて
ラップ (2の補数切詰め) に変更した。現在は solve時・query時とも Java と
同義。(`snippet.rs` の `wrap_int_literals` が `IntCircuit::constant` と
同じ下位ビット切詰めを行う。)

### 2.2 `extends Int` 系エラーメッセージの修飾なし
`sig X extends Int {}` は Java 互換の文言で拒否するが、sig名に
`this/` 接頭辞を付けない (`sig X cannot extend the builtin "Int"
signature`。Javaは `sig this/X cannot ...`)。Rust AST がモジュール修飾名を
持たないためで、文言の対応付け以外に意味差はない。

## 3. 整数型の拡張: ビットベクトル `Int` (bitmask統一規則)

Javaはグローバルbitwidth (`for N Int`) のもと常に `2^w` 個のintアトム
(`-2^(w-1)..2^(w-1)-1`) をuniverseに常駐させる。Rustはビットベクトル
モデルに置き換えた:

- **原子は符号なし `W` 個**: `for W Int` (なければ W = 4) で原子
  `{0, .., W-1}`。例: `for 4 Int` の `Int` は `{0, 1, 2, 3}`。
- **回路幅 `E = min(W + 1, 30)`**: MSB原子の符号付き重み
  (-2^(w-1)) を正の値と区別するため W+1 ビット。リテラル・算術は
  E-bit 2の補数で折返す (例: W = 8 → E = 9 で `300` → `-212`)。
- **bitmask値 (統一値語彙)**: int位置の集合は
  `Σ weight(v)` と読む。`weight(v) = v = W-1 ? -2^(W-1) : 2^v`
  (2の補数のビット分解)。集合のbitmask値は原子の存在ベクトルと
  一対一対応する。
  - `{0, 2}` → 5、`{2}` → 4、`{MSB}` → -8 (W = 4)
  - `{1, 2}` → 6、`{2}` @W = 3 → -4 (原子2がMSBのため)
- **リテラルは常に整数**: `0, 1, 123, -2` はスカラー。
  集合は `{1, 2, 3}` (列挙) か `{1} + {2} + {3}` (単集合の和) で表記。
- **混合比較 `集合 = 整数` は一律 bitmask値比較** (左右対称・
  名前付き/リテラル不問・Int/Signed不問):
  - `X = 5` ⟺ X = `{0, 2}` (bitmask 5)
  - `{2} = 4` は真 (W ≥ 4)。W = 3 では原子2がMSBで重み -4 → 偽。
    W ≤ 2 では原子不在エラー
  - `MSB = 3` は偽 (-8 ≠ 3)、`MSB + 1 = -7` は真
  - `1+2 = {0, 1}` は真 (3 = 3)、`{1, 2} = 3` は偽 (6 ≠ 3)
  - `x = 5` (スカラ変数) は恒偽 (2^v = 5の解なし)。`x = 4` は
    原子2のとき真。単一原子と整数の一致は `{n}` / bit値で表記
- **両辺集合の `=` は従来の集合等価**: `{0}+{1} = {0,1}`、
  `({0,1}-{0}) = {1}`、`{A} = {B}`、`X = {0,1}`、`X = {5}` は
  集合等価 (brace 純粋な `+`/`-` 木は巻き戻し)。
- **int位置の `{...}` も bitmask 値**: `{0, 1} * 2 = 3 * 2` が真。
  混在 (`{0,1} + 2` → 5) も整数確定。
- **`sum e` は Σ atom値**: `sum {0, 1}` は 1 (bitmask 3 とは別物)。
  `X = sum {1,2}` は bitmask(X) = 3 ⟺ X = {0,1}。
- **`in` は両辺集合型のみ**: 左辺が整数式 (`5 in X`、`1+2 in X`) は
  パース時の型エラー。`{3} in X`、`{1}+{2} in X`、`x in X` は
  従来部分集合。
- **`Signed` 型**: `Int` と同一原子の別名ビュー。`sig X in Signed {}`
  と `v: Signed` が通る。`extends Signed` は拒否。
  Int集合との整数比較も bitmask 許可 (Signed/Int 区別なし)。
- **`MSB`**: 集合位置では `{W-1}` 単集合、int位置では bitmask値
  `-2^(W-1)`。
- **`Int[w]` 宣言側幅の廃止**: `Int[8]` は join `8.Int` (arityエラー)。
  実効値は `for W Int` のみ。
- **intアトム遅延割当** (継続): Intを集合として使わないモデルは
  universe・boundsともにintアトムを持たない (例: `for 3` の
  universeは3)。`sig X in Int` は材料化を強制。
- **`:query` の閉論理式** (継続): `:query 1 = 1` 等は instance に対する
  真偽値を返す。集合み `:query` は `Bool` を拒否。

## 4. REPL固有の仕様 (Javaに対応物なし)

Java版にREPLは存在しないため、以下はすべて Rust 側の独自設計:

- **素行の解釈**: 式だけの行は既定で `:eval` (SAT判定・保存なし)。
  `:mode [eval|query]` (`:m`、引数なしはトグル) で `:query`
  (default solution読出し) に切替え可。プロンプト (`alloy> ` /
  `alloy?> `) で現在のモードを表示。
- **`:query` の solution指定**: 末尾の `in <sol>` は Alloy の `in` と
  衝突するため、`<sol>` が保存済みsolution名の場合にのみ solution指定と
  解釈する。曖昧さ回避の専用構文として `@ <sol>` もある。
- **名前付きストア**: `:run`/`:check` が `Cnf` を、`:solve` が solution を
  それぞれ名前付きで保存 (`:cnfs`/`:sols` 一覧、`*` が既定、` :use` 切替)。
  Cnfとsolutionの名前空間は別。
- **`:eval` の素式リフト**: 素の関係式は `some (...)` で包んで充足可能性を
  問う (`als -e` と同じ手口)。
- **pin/apin**: パーシャルインスタンスはバイナリ形式のみ
  (`:psave`/`:pread`/`:ppin`/`:pavoid`, `.apin`)。テキストpin
  (`:save`/`:add`, Alloy fact形式) は廃止した。`gated` は将来の永続
  セッション向けの先行予約であり、現行のワンショット解決では恒久配置と
  同値。
- **atom名 (`A$0`) の扱い** (Java互換): モデル記述内 (sig/field/変数/para/
  fact名の宣言、`fact`・`run`・`:eval` 中の参照) では `$` 含有を拒否する
  (`The name cannot contain the '$' symbol.`。Javaの `Alloy.cup` `nod()` と
  同文言)。atomはsolver出力の表示ラベルであり言語項ではないため。
  唯一の例外は `:query` ワンライナーで、解後の評価としてuniverse atomを
  単集合として参照できる (Javaのsolve後 `frame.a2k` 相当)。番号はscope割当
  順であり、Java visualizerの解後採番と一致するとは限らない。

## 5. ASTレベル・パーシャルインスタンス: `partial` / `pin` / `avoid`

Java・Kodkodいずれにも対応物がない純粋な拡張 (REPLのバイナリ `.apin`
機構とは独立)。テキストpin (`:save`/`:add`) 廃止後の置換えとして、
`$` ラベルをブロック内に閉じ込めたdiagram法を提供する:

```alloy
partial part1 { A = A$book + A$note }   // exact
partial part2 { A$book in A }           // lower
run { pin part1 and #A = 2 } for 3
```

- **定義**: `partial <name> { <entry>, ... }`。エントリは `=` (exact)、
  `L in R` (lower)、`R in S` (upper) の3形式。`!=`/`not in` は不可
  (`avoid` を使う)。エントリの式はラベル (`Sig$tag`)・intリテラル・
  `none`/`{}`・素リレーション参照・dotted参照 (`B.f`)・`+`/`->` のみ。
- **参照**: formula位置の `pin <name>` / `avoid <name>` (`avoid` は
  `Not(pin)` に読む)。`pin P` は `some x... | <連言>` に、`avoid P` は
  その否定にdesugarされ、既存lower→CNF経路のみを通る (Kodkod層無改修)。
- **ラベル規則**: `Sig$tag` のみ (prefixは宣言sig、`Int` 不可、tagは
  ID規則)。同一 `(prefix,tag)` は同一atom、同一prefixの異tagは `!=`
  で区別。ラベルは定義内局所 (`pin P and pin P` は冪等、定義間共有なし)。
  Subsig跨ぎの同一指示は不可。
- **下限のみの `in` との違い**: `:ppin` は記載リレーション完全固定だが、
  `pin` エントリは `=` のみexactで `in` は下限/上限。単独使用は濃度条件に
  縮退する (`avoid {A={x,y}}` ≡ `#A≠2`、`avoid {x in A}` ≡ `A=∅`)。
- **番号非依存**: ラベルは名前であり `A$0` のようなscope番号ではない。
  universe再構成時も名前解決されるため、scope変更に強い (ただしprefix
  sigの割当自体はscope依存)。
- **集合の表示形式**: `:query`・`:solve`/`:show` の表示と `:save` の保存は
  `{A$0, B$0}` 形 (空集合は `{}`、単要素も `{A$0}`)。ただし Signed 型の
  sig は bitmask 値で表示 (`S = 85`)。Signed range の field はオーナー
  原子ごとに分解して表示 (`X$0.s = 123`、空行は `= 0`)。旧 `A + B` / `none`
  表示からの変更で、表示と保存のみ (文法は不変: `+` も `none` も従来通り
  受理し、`{}` は空集合リテラルとして受理)。表示出力はそのまま `:add` や
  `:query {...}` に再投入できる (整数表示の `S = 85` は式 `S = 85`
  としても真なので意味的にも往復する)。

## 6. 最適化コマンド: `maximize` / `minimize` (Rust専用文法)

Java Alloy・Pardinus いずれにも最大最小コマンド文法は存在しない
(Java側の最適化は `PMaxSAT4J`＋target/weightのAPI指定のみ)。以下は
Rustフロント専用の純粋な拡張。ソルバは `alloy-kodkod-rs/src/opt.rs`
の OLL/Fu-Malik core-guided ループ (単一セッション・selector仮定＋
`failed_core` 継承)。

### 6.1 `.als` コマンド文法

```alloy
maximize { <formula> } : <intexpr> for <scope>
minimize { <formula> } : <intexpr> for <scope>
maximize : <intexpr> for <scope>              // facts のみ
maximize predName : <intexpr> for <scope>     // 名前付きpred参照
maximize weights { <rel> : <int>, ... } for <scope>
maximize weights { <rel> : <int>, ... } { <formula> } for <scope>
```

- `maximize` / `minimize` / `weights` は予約語化 (既存83例題に
  識別子衝突なしを確認)。`run` / `check` と並列に `CommandKind` に
  追加 (`Maximize { name, objective }` / `Minimize { name, objective }`)。
- 目的は `OptSpec::Int(IntExpr)`（`: <intexpr>`、既存Int式文法を再利用）
  または `OptSpec::Weights(Vec<(String, i64)>)`（`weights {...}`、重みは
  符号付き整数リテラルのみ）。`{ F }` ボディは `run { F }` と同じ
  auto-para 生成 (`maximize$N`)。
- `weights` 形式と `#` の線形結合 (`2*#r1 + 5*#r2`) は意味が等しいが
  lowering経路が別 (前者は `var_origins`→soft unit節の専用経路で加算
  回路不要、後者は `IntCircuit` 経由)。記述した形式＝使用経路が原則で
  自動判定はしない。
- `for <scope>` / `expect` は `run` と同一解釈。temporal・多目的・
  辞書式は対象外。

### 6.3 AlloyMax 表面文法: `maxsome` / `minsome` / `soft fact`

Java Alloy にも存在しない AlloyMax 方言（`cmu-soda/AlloyMax`
`maxsat_all` ブランチ互換のサブセット）。Kodkod レベルでは
`maxsome e` が式ソフト公式として降りてくる実装（同ブランチの
`Expression.maxSome()` に対応）。

```alloy
run MaxInterests1 {
  validSchedule[courses]
  all stu: Student | maxsome stu.interests & stu.courses
}
soft fact { no lec: Alice.courses.lectures | ... }  // 最適化対象の制約
```

- `maxsome e` / `minsome e`: 式 `e` の各セルに unit soft（重み1）。
  `minsome` は否定記録し、報告コストは自然値に補正する。hard 意味は
  `true`（検証・充足判定には寄与しない）。
- `soft fact F`: lowered root を unit soft 化（重み1）。hard からは外れる。
- いずれも単一セッション OLL（`Objective::Collected`）で解く。`run` /
  `check` コマンド内に現れた場合は自動で最適化経路に振り分け
  （`command_needs_opt`）、素の SAT 経路（`run_command` / `Cnf::solve` /
  temporal）は大声で拒否する（黙って soft を落とさない）。
- 対象外（明示エラー）：`maxsome x: T | F` 宣言形（free な集合値
  witness が必要）、`maxsome[n]` 優先度（全 soft 重み1均一）、
  temporal との併用。

### 6.2 REPL コマンド

| コマンド | 意味 |
|---|---|
| `:max <intexpr> [in <cnf>] [as <sol>]` | Int式の最大化 |
| `:min <intexpr> [in <cnf>] [as <sol>]` | Int式の最小化 |
| `:maxw <rel>:<w>[, ...] [in <cnf>] [as <sol>]` | Σ w·#r の最大化 |
| `:minw <rel>:<w>[, ...] [in <cnf>] [as <sol>]` | Σ w·#r の最小化 |

- 末尾 `in <cnf>` は保存済みCnf名の場合のみCnf指定と解釈 (Alloyの
  `in` との衝突回避は `:query` と同方針)。結果表示に `cost=<n>` を
  付け、`:sols` 一覧にも `cost=` を表示する。
- `Cnf` は `run`/`check` コマンドから作る (`maximize` コマンド自体は
  `Cnf` 化せず `run_opt_command` で直接解く)。`Cnf` は high-level
  (arena/bounds/formula) を保持しているため、REPL目的式はその場で
  lowerして `solve_opt_with` に渡す。
