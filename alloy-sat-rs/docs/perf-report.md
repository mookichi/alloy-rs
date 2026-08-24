# 性能レポート

更新: 2026-08-24(バックログ1 最適化後)。Iter 6 初版からの比較。
環境: Linux / rustc stable / release(`lto=true, codegen-units=1`) /
CaDiCaL(IPASIR 経由)。criterion 10 サンプル。

## E2E solve(翻訳+SAT+materialize)

| 例題 | Iter 6 | 最適化後 | 変化 |
|---|---|---|---|
| pigeonhole 5x4 (UNSAT) | 275 µs | 234 µs | -15% |
| coloring 6頂点7辺/3色 (SAT) | 665 µs | 442 µs | -34% |
| queens 8 (SAT) | 655 ms | 137 ms | **-79%** |
| queens 10 (SAT) | 3.93 s | 0.72 s | **-82%** |
| queens 12 (SAT) | 18.3 s | 3.0 s | **-84%** |
| queens 16 (SAT) | 177 s | 24.4 s | **-86%** |

最適化内容: (1) Comparison の疎キーユニオン生成(容量全走査廃止)、
(2) BoolFactory fold へ補文リテラル打ち切り+吸收則追加。

## Iter 9(2026-08-24)

- 例題実行で回帰確認: `--example solve -- queens10` → **0.64 s**
  (Iter 6 最適化後 0.72 s に対し微改善)。ucore 追加は既存
  `translate_to_cnf` 経路に触れないため翻訳性能は影響なし
- コア抽出のソルブ回数: sudoku_core デモで初期 solve + 削除フィルタ
  = グループ数に対し線形(3 soft groups → 3 solves)

## 観察

- n-queens は 4 項 ATK 関係の量化子展開が支配的で、翻訳時間が
  O(n^4) の行列セル生成 + ゲート数で伸びる。SAT 自体は数秒未満。
  → バックログ 1(部分式共有強化)/ 5(IntSet bitset)で削減を図る
- 小規模問題(≤ 数百 primary vars)は 1ms 未満。オーバーヘッドは無視できる

## 再現

```sh
cargo bench -p alloy-kodkod-rs --features ipasir --bench nqueens
cargo bench -p alloy-kodkod-rs --features ipasir --bench heavy   # queens16(数分)
cargo run -q --release -p alloy-kodkod-rs --features ipasir --example solve -- queens16
```
