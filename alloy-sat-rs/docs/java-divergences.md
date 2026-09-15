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

## 3. 整数型の拡張: `Int[w]` と intアトム遅延割当 (A-plan Phase 1)

Javaはグローバルbitwidth (`for N Int`) のもと常に `2^w` 個のintアトムを
universeに常駐させる。Rustは以下を変えている (互換妥協あり):

- **`Int[w]` / `int[w]` 宣言側幅**: `sig C { v: Int[8] }`、
  `all x: Int[6] | ...` を受理 (Java実測: パースエラー)。
  実効bitwidth = `max(既定(`for N Int`、なければ4)、全 `Int[w]`)`。
  幅の妥当域は 1..32 (`Int[0]`・`Int[33]`・`Int[x]` はパースエラー)。
- **intアトム遅延割当**: Intを集合として使わないモデル
  (`Int`/`int` 非言及、集合位置の整数リテラルなし、`sig X in Int` なし、
  `for N Int` なし、純粋な `#A`/`sum`/四則/`IntCmp` のみ) は universe・
  boundsともにintアトムを持たない。例: `sig A{} run{} for 3` の
  universeは3 (従来は3+16)。`#A`・`1+1`・wrapは実効幅で従来通り動く。
- **互換切断点**: Int未使用モデルで `:query Int` / `{x: Int}` は空集合、
  `#Int` は0、集合位置リテラル (`5 + A`、`{1+1}`) はスコープ外エラー
  (明示的ガイダンス付き)。いずれも `for N Int` を付けるかIntに言及
  すれば従来通り。明示 `for N Int` は常に全域を実体化する。
- 過渡仕様として幅はグローバルmaxに畳まれる (宣言ごとの独立幅・符号
  拡張の厳密化は後続Phase)。`sig X in Int[w]` の添字付き継承は未対応
  (`in Int` は実効幅を用いる)。

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
- **pin/apin**: `:save`/`:add` (Alloy fact形式) と `:psave`/`:pread`/
  `:ppin`/`:pavoid` (バイナリ部分インスタンス)。`gated` は将来の永続
  セッション向けの先行予約であり、現行のワンショット解決では恒久配置と
  同値。
