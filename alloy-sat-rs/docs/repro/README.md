# 再現アーティファクト(偽 SAT バグ)

- `m15.als`: 最小再現モデル(sig Book { addr: Book -> Book } の delUndoesAdd 型
  check)。java=UNSAT / rust=SAT(偽カウンターエグザンプル)
- `m15.bin` / `m4.bin`: 対応する ARE2 wire ダンプ(-Dalloy.rust.dump で取得)。
  `cargo run -p alloy-engine-rs --example wire_dump -- <bin>` で AST 表示、
  `subset_debug` で連言部分集合求解

デコード後 AST は手書き意味論と一致することを検証済み → fol.rs 側の問題と推定。
ただし mult_dense.rs の孤立プローブは通過するため、wire デコード文脈
(追加の型制約連言・ノード配置)との組み合わせで発現。
