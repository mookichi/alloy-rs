# `(m, e, p, k)` Valid制約の恒久化＋タイト化 (B2/B3/B5/B8/B9)

## 1. 誤差タイト化 (B2/B3)：支配項条件

Lemma 2 の `+1`（`combine_k`由来）は最悪ケース（項が等大）のための余裕で、
項が乖離していれば不要。以下は整数指数比較のみで証明可能（健全性優先、
`mul_tight_sound_fuzz` / `div_two_stage_sound_fuzz` が境界値でゲート）。

- **B2 乗算** (`int_ext::mul_c`): `t1,t2,t3` の最大 `M` と2番手 `S`
  （pairwise-min の最大値。タイ時は `S == M` で従来通り）の差が `M - S >= 2`
  なら `C = e1+e2+M+1`、そうでなければ `+2`。根拠:
  和 `< 2^M·(1+1/4+1/4) < 2^(M+1)`。計測: 軌道上発火率 98.5%。
- **B3 除算** (`int_ext::div_d`): `|u1-u2| >= 2` なら `D = e1-e2+M+2`、
  そうでなければ `+3`（分母下界 `1/2` 分の `+1` は温存）。根拠:
  分子和 `< 1.25·2^(E+M)`。計測: 軌道上発火率 58.5%。
- `combine_k` 自体の `+1` は必要条件のため削れない（`k' >= 1` が必須）。
- ミラー3箇所同期: オラクル (`mepk.rs`)・シンボル層 (`mepk_*_c`)・
  lowering (`ereal_mul`/`ereal_div`: ブランチ分割で同一条件) を同時変更。
  食い違いは `mepk_circuit` 一致テストで検出。

## 2. 狙い撃ち refinement (B5)＋コスト (B8/B9)

- `refine_step` (`mepk_tree.rs`): worst-marginノードの支配側の葉のみ bump。
  加減算は `p` 最小側、乗算は `k-p` 最大側。タイ時は両側
  （§9.1(b)収束形）。**除算は常に両側**:
  スケール商 `qmag = m1<<guard/m2` が両マグニチュードを固定guardで結ぶため、
  片側bumpは商スケールを壊し空虚な `m=0`（walkthroughで `(0,30,14,2)` を
  実測）に収束する。加減乗は正確な整数演算のため免疫。
- no-progressガード: 狙い撃ちで同一targetが改善しなければ両側bumpに
  フォールバック。計測: bump葉数約2割減、反復数は同等、停滞なし。
- コスト: `CegarOutcome::cost = Σ(leaf p 上昇) + COST_GUARD_WEIGHT(4)·guard上昇`。
  `max_cost` 上限＋`CegarError::BudgetExhausted`（収束解は上限到達時も返す）。
  `:cegar budget <n>` で指定、成功行に `cost=` 表示。
- 未着手: B6（Q-block全走査。現行worst経由で実害なしのため保留）、
  B7（root_only。意味論変更のため保留）。

## 3. ERealConstant＋EReal abstract復帰＋als表示

- `als` 出力にEReal認識表示（`front-rs/src/display.rs`、REPLデコーダの移植）。
  raw lane非表示＋所属atomのみ `EReal$i = c ± R`。lane無し出力はバイト同一維持
  （`no_lanes_keeps_legacy_shape`）。`-e <name>` は式の値も表示
  （`format_eval_value`）。非所属atomのゴーストlaneは表示しない
- `-e` は直前実行コマンドのscopeを継承（`inherit_eval_scope`。REPL `:eval` と同則）。
  継承前は既定プロファイルで別解が表示される問題があった。
  `--timing` 側も `run_timed`（parse済み実行）で同一継承
- `-e` は `:query` 化：直前のplain static解があれば再solveせず `query_value` で評価
  （`query_last`＋`format_query_value`＋`query_exit_ok`）。`false` はexit 1維持
- queryのID対応バグ修正：`RelationId` はlowering毎の挿入順カウンタのため、独立再build
  のCnfでqueryすると別relation（空の `Step` 等）に当たり `no x=true` 等の誤答が出る。
  `snippet::query_*` のscratch arenaをinstanceのpool共有に変更（REPLは同一poolの
  ため無影響）。`query_stable_across_rebuilt_cnfs` で回帰ゲート

## 4. ERealConstant＋EReal abstract復帰（本体）

- decimalリテラルは `ERealConstant`（Kodkod `IntConstant` 類比：固定lane、
  atom/scope不消費）としてlowering層で解決（`ERealOp::Const`→`IntExpr::Lit`）。
  kodkod AST不変。旧 `$elit` witness hoisting撤廃
  （`wrap_ereal_lit_args`/`fresh_elit` 削除）。`for 0 EReal` でもリテラル述語はSAT
- 前提が満たされたため `EReal` のカバレッジを復帰（`lower.rs` の exemption 削除）。
  extenderあり＝親は子に被覆（`one sig x extends EReal` は `EReal=[1 atom]`）。
  kid無し＝カバレッジなし（自由値・`for N EReal` 維持）。`some EReal - X` 系テスト反転済み

## 4. Valid制約の恒久化（前回分）

`mepk_formal_rev3.md` §1 (§5) の表現制約を、オラクル・回路・solver lowering の
全層で恒久的に強制する。rev3本文は変えず、本ファイルが実装側の定義とする。

### 4.1. 定義

```text
Valid(m,e,p,k; m_width) :=
  1 <= p <= 127 かつ p <= m_width
  かつ 0 <= k < p
  かつ (m == 0 または 2^(p-1) <= |m| < 2^p)
```

- `e` 整合性 (`2^e <= |c| < 2^(e+1)`, `c = m·2^(e-p+1)`) は正規化から自動的に従う
  ため独立の制約は不要。`m == 0` は正規化の枠外特殊値として `e` 自由
  (rev3 §10.1(a) の除算ガードと対応)。
- `k < p` は rev3 §5 の除算前提を全値に拡張したもの。ただし中間結果の精度喪失
  (`k >= p`) は CEGAR/`erealNeedsRefine` が観測する必要があるため、内部では
  下の2段階で扱う。

### 4.2. 2段階の強制

| 層 | コア (`k>=0` まで) | 厳密 (`k<p` まで) |
|---|---|---|
| Rust: `int_ext::is_valid` / `Mepk::is_valid` / `Mepk::new_valid` | — | 全条件 (`m_width` 指定可) |
| Rust: `mepk_add/mul/div` 入力ゲート (`valid_input`: 正規化+`k>=0`) | 拒否→`None` | `k>=p` は通過 (精度喪失として返しCEGARが検出) |
| Rust: 上記3関数の出力 | 常に正規化 (丸め由来) | `k'>=p'` を返しうる (同上) |
| lowering: `ereal_valid_core` | `erealAdd/Sub/Mul/Div` の全オペランド+結果に conjunction (非正規・`p>m_width` はUNSAT) | — |
| lowering: `erealDiv` | — | 分母に `div_guard (k<p)` + `m!=0` (従来通り) |
| lowering: `erealValid` 述語 (`ereal_valid_strict`) | — | ユーザが目標状態を主張するための公開述語 |
| `erealWellformed` | 従来通り `p>0,k>=0` (互換維持) | — |
| `setEReal`/リテラル変換 | 常にコアValidを生成 (dyadic zero-fill / 非dyadic丸め) | `max_p=1` での非dyadic (`k=1,p=1`) を除き厳密 |

比較述語 (`erealMayEq` 等) は `wellformed` のみ: 区間演算自体は正規化不要で
健全であり、値の構築点 (演算・リテラル) でValidを強制する方針。

### 4.3. 移行メモ

- 旧fixtureの非正規タプル (`(100,6,8,1)` 等) は正規化値に置換済み
  (`(200,5,8,1)` は同一中心値 50)。意図的Invalid (`(50,5,4,4)`) は拒否テスト
  として保持。
- `Mepk::new` 自体は非検査のまま (表示・テスト用): 検査付き構築は
  `Mepk::new_valid` を使う。
- Java 対向物 (`MepkOps.java`)・`mepk.als` ミラーへの反映は未対応。

## 5. builtin `Real` (`EReal extends Real`)

exact 中心 `c = m·2^e` の親ソート。正規形は `m == 0` (e 自由) または
`odd(m)`。`M/E` 幅は EReal と共有 (`MEPK_*_WIDTH` 分離なし)。
`EReal` は `Real` の子として `m/e` を共有し `p/k` のみ独自に持つ。
`Real` は抽象: extender 存在下では被覆 (`one sig X extends Real` は
1値に畳む)、`EReal` 単独時は従来通り。`for M EReal <= N Real` を検査
(互換デフォルトで自動調整)。

### 5.1. 述語と丸めなし原則

`realAdd/Sub/Mul/Div`・`realEq/LT/LTE/GT/GTE`・`realWellformed`・
`realSucc/Pred`・`realUp/Down` 関数・`setReal`・
`setRealNearest/Down/Up`。演算は exact のみ (割切れない除算は UNSAT)。
`realUp/Down` はレーン successor (指数ウィンドウ探索、brute-force 照合済み);
関数形は内包 desugar + 述語位置への自動ホイスト (skolem-fast)。

### 5.2. リテラル近似の明示 opt-in

plain `d` は近似なし (非dyadic は UNSAT、ただし大声エラーではなく
合成可能な UNSAT)。`(d)` 綴り (`ApproxRealLit`) のみ近似を許可:

| 位置 | plain 非dyadic | `(d)` 非dyadic |
|---|---|---|
| 順序比較 | UNSAT | bracket (`X < (L)` ⟺ `X ≤ Down(L)`、判定 exact) |
| `=`/`!=`・演算・`setReal` | UNSAT | `=`/`setReal` は nearest 束縛、演算は UNSAT |
| `(d1) = (d2)` | — | nearest 中心の等価比較 |

`Down(L) < L` が厳密かつレーン値は全て dyadic のため bracket 判定は
真値比較と等価。丸め誤差自体は追跡されない (Down+Up で挟む運用)。
