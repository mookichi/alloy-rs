# 性能レポート

更新: 2026-08-26。Java 本家との速度比較を追加。
環境: Linux / rustc 1.98 stable / release(`lto=true, codegen-units=1`) /
CaDiCaL(IPASIR 経由)。Java 25 (Corretto)。

## Rust vs Java 速度比較

### 環境

| 項目 | Rust | Java |
|---|---|---|
| バージョン | rustc 1.98.0 | OpenJDK 25 (Corretto) |
| ビルド | `--release` (lto=true) | gradle dist JAR |
| SAT ソルバ | CaDiCaL (IPASIR) | Sat4J (デフォルト) |
| 計測方法 | `--timing` フラグ | `--timing` フラグ |

### 小規模モデル E2E（parse + lower + solve 合計）

3回中央値。Java は JVM 起動 + パース + solve + 出力生成を含む。

| モデル | Java (ms) | Rust (ms) | スピードアップ |
|---|---|---|---|
| ring | 101.0 | 0.247 | **409x** |
| tube | 175.9 | 0.374 | **470x** |
| undirected | 105.6 | 0.332 | **318x** |
| prison | 106.4 | 0.239 | **445x** |

- 小規模問題（≤ 数百 primary vars）: Rust **300〜470倍高速**
- JVM オーバーヘッド（~100ms）が支配的。Rust の合計は 0.2〜0.4ms
- Rust の lower フェーズは ~50µs と無視できる程度

### Rust フェーズ別内訳（--timing）

| モデル | parse | lower | solve | 合計 |
|---|---|---|---|---|
| ring | 4 µs | 54 µs | 203 µs | 261 µs |
| tube | 4 µs | 53 µs | 207 µs | 264 µs |
| undirected | 5 µs | 46 µs | 263 µs | 314 µs |
| prison | 5 µs | 50 µs | 182 µs | 237 µs |

### Java フェーズ別内訳（--timing）

| モデル | parse | solve | 合計 |
|---|---|---|---|
| ring | ~55 ms | ~46 ms | ~101 ms |
| tube | ~58 ms | ~118 ms | ~176 ms |
| undirected | ~55 ms | ~51 ms | ~106 ms |
| prison | ~55 ms | ~51 ms | ~106 ms |

- Java parse は ~55ms で安定（JVM クラスロード後）
- Java solve はモデルサイズに比例

## E2E solve（翻訳+SAT+materialize）

Iter 6 初版からの比較。criterion 10 サンプル。

| 例題 | Iter 6 | 最適化後 | 変化 |
|---|---|---|---|
| pigeonhole 5x4 (UNSAT) | 275 µs | 226 µs | -18% |
| coloring 6頂点7辺/3色 (SAT) | 665 µs | 401 µs | **-40%** |
| queens 8 (SAT) | 655 ms | 130 ms | **-80%** |
| queens 10 (SAT) | 3.93 s | 0.69 s | **-82%** |
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
- Java との比較: 小規模では JVM オーバーヘッドで 300-470x の差。
  実際の solve 時間のみなら Java Sat4J vs Rust CaDiCaL の差となる。
  大規模問題では Rust のメモリ効率・型安全性が優位。

## 再現

```sh
# Rust Kodkod ベンチ
cargo bench -p alloy-kodkod-rs --features ipasir --bench nqueens
cargo bench -p alloy-kodkod-rs --features ipasir --bench heavy   # queens16(数分)

# Rust E2E 個別計時
cargo run -p alloy-front-rs --release --bin als -- --timing model.als

# Java 個別計時
java -jar org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar \
  exec --timing --output - model.als

# Rust vs Java 比較スクリプト
bash alloy-sat-rs/bench-compare.sh
```
