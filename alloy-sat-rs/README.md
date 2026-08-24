# alloy-sat-rs

Rust 製 SAT ソルバ層(Alloy/Pardinus の Rust 化 Phase 1)。

`liballoy_ipasir.so` は **IPASIR 標準 C ABI** を実装する cdylib で、
Java(JNI)・C/C++・Python 等あらゆる IPASIR クライアントから利用できる。

## 構成

```
alloy-ipasir/
├── src/
│   ├── lib.rs            IPASIR C ABI(同期ファサード)+ alloy_worker_* 非同期ABI
│   ├── worker.rs         ワーカースレッド(コマンドチャネル+キャンセルトークン)
│   ├── backend.rs        Backend trait + CancelToken + ファクトリ
│   ├── cadical_backend.rs CaDiCaL(増分・assumptions・検索中割り込み対応、既定)
│   └── splr_backend.rs   Splr(純Rust、assumptions非対応)
├── tests/
│   ├── session.rs        Rustレベルの動作テスト
│   ├── c_abi.rs          dlopenで実シンボルを検証するIPASIR ABIテスト
│   └── worker_c_abi.rs   非同期ABIテスト(状態ポーリング/中断/並列ワーカー)
include/ipasir.h         Cクライアント用リファレンスヘッダ
```

## スレッドモデル

セッションごとに **Rust ワーカースレッド 1 本** が立ち、バックエンドは
そのスレッド内に留まる。ホストはコマンドと共有ステータスのみ扱う:

```
ホスト(任意スレッド)            ワーカースレッド
alloy_worker_add()      ──►    Add(lits)   → backend.add_clause
alloy_worker_solve()    ──►    Solve       → backend.solve()
alloy_worker_status()   ◄──    共有スロット (-1 実行中 / 10 / 20 / 0)
alloy_worker_cancel()   ──►    AtomicBool → CaDiCaL terminate コールバック
alloy_worker_release()  ──►    Free → drop & join
```

`ipasir_*` 同期 ABI はこの上の薄いファサード(solve は wait でブロック、
`ipasir_set_terminate` のコールバックはポーリングで cancel に変換)。

## ビルド / テスト

```sh
cargo build --release        # target/release/liballoy_ipasir.so
cargo test                   # 既定: cadical + splr の両バックエンド
cargo test --no-default-features --features cadical
cargo test --no-default-features --features splr
```

## バックエンド選択

実行時に `ALLOY_SAT_BACKEND` 環境変数で指定(`cadical` / `splr`)。
未指定なら cadical(splr が入っていればその次)の順。

| | cadical | splr |
|---|---|---|
| 増分解決 | ◎ | △(毎solve再構築) |
| assumptions / UNSATコア(`failed`) | ○ | ✗ |
| 実装 | C++(cargoがビルド) | 純Rust |
| ライセンス | MIT | MPL-2.0 |

## C API(IPASIR、同期)

```c
#include "ipasir.h"
void *s = ipasir_init();
ipasir_add(s, 1); ipasir_add(s, 2); ipasir_add(s, 0); /* x1 ∨ x2 */
int r = ipasir_solve(s);            /* 10=SAT, 20=UNSAT, 0=中断/不明 */
if (r == 10) { int v = ipasir_val(s, 1); }
ipasir_assume(s, -3);               /* 次のsolveへの仮定 */
if (ipasir_solve(s) == 20 && ipasir_failed(s, -3)) {
    /* -3 は UNSAT コアに参加(失敗仮定) */
}
ipasir_set_terminate(s, state, my_abort_cb); /* solve中の割り込み */
ipasir_release(s);
```

## C API(alloy_worker_*、非同期)

```c
void *w = alloy_worker_init();
int32_t c[2] = {1, 2};
alloy_worker_add(w, c, 2);
alloy_worker_assume(w, 5);          /* 次のsolveへの仮定(solveで消費) */
alloy_worker_solve(w);              /* ノンブロッキング */
while (alloy_worker_status(w) == -1) { /* 他の処理 */ }
int r = alloy_worker_wait(w);       /* 最終値で確定待ち */
if (r == 10) int v = alloy_worker_val(w, 1);
else if (r == 20 && alloy_worker_failed(w, 5)) { /* 失敗仮定 */ }
alloy_worker_cancel(w);             /* 実行中断(任意スレッドから) */
alloy_worker_release(w);
```

## 既知の制約(v0)

- `ipasir_set_learn` は no-op(オプション機能)
- splr バックエンドは assumptions 非対応(失敗仮定も取得不可)

## Java 統合(実装済み)

`--features jni` でビルドすると `liballoy_ipasir.so` が JNI エクスポート
(10 関数)を公開し、Java 側の `IpasirWorker`
(`org.alloytools.pardinus.native` モジュール)から使える。

```bash
cargo build --release --features jni
cp target/release/liballoy_ipasir.so \
   ../org.alloytools.pardinus.native/native/linux/amd64/
cd .. && ./gradlew :org.alloytools.pardinus.native:test   # JUnit 4, 6 tests
```

- `IpasirWorker implements SATSolver`: 同期 API に加え
  `solveAsync()/status()/waitSolution()/cancel()/literalValue(int)` を提供。
  `free()` 後の呼び出しは `IllegalStateException`、二重 `free()` は no-op。
- `IpasirRef extends SATFactory`: id=`ipasir`、`@ServiceProvider` 登録済み。
  dist jar の `solvers` 一覧に表示され、CLI では
  `exec --solver ipasir -f model.als` で使用する。
- 単体テストはバンドル jar を経由しないため、テスト側で
  `-Dalloy.native.lib.alloy_ipasir=<soへのパス>` を設定して読み込む。

## alloy-kodkod-rs(Pardinus コア移行・第1段)

`docs/pardinus-core-survey.md` に調査と設計を記載。実装済み:

- `IntSet`: **i64** ソート済疎集合(和/交/差/min/max/bulk 演算)
- `Universe`: `Arc<str>` アトム、参照同一性(`Arc::ptr_eq`=Java の identity equals)
- `Tuple`: (arity, index) のみ保持し atom 列は遅延復元(Java IntTuple 相当)
- `TupleSet`: arity + 索引集合。product/project/range、容量は i64 checked

```bash
cargo test -p alloy-kodkod-rs   # 10 tests
```

### Bool2CNFTranslator 移植(第2段)
- `bool::BoolFactory` — 回路アリーナ。`BoolRef(i32)` 符号付き参照で Not を
  無コスト表現(Java の label 反転と等価)、定数畳み込み+ゲートキャッシュ
- `cnf::translate_to_cnf / translate_into_solver` — 定義的翻訳+極性最適化
- `sat::SatSolver` トレイトでバックエンド非依存(RecordingSolver/将来 ipasir 橋)

### エンドツーエンド(feature `ipasir`)
`IpasirSolver` が `SatSolver` を実装し、回路→CNF→CaDiCaL(ワーカースレッド)
が Rust 内で完結:

```bash
cargo test -p alloy-kodkod-rs --features ipasir   # +2 tests(fuzz 30 cases)
```

### Iter 1 完了: relation/bounds/instance
- RelationPool を抽出し AST↔インスタンス層で同一 id 空間
- Bounds(挿入順・Java同形式Display)/Instance 材料化API
- テスト計38(+ipasir時40)、デモ `cargo run --example ring_bounds`

### Iter 2 完了: dimensions/bmatrix
- Dimensions(dot/cross/transpose、行優先変換)
- BooleanMatrix(疎セル+欠損=FALSE意味論、not欠損→TRUE規則、choice/cross/transpose)
- テスト計46(+ipasir時48)、デモ `cargo run --example matrix_demo`


### Iter 3 完了: fol(FOL→bool 関係子セット)
- BooleanMatrix に join / ^闭包 / override_values(Kodkod行単位定義)追加
- FolTranslator: 境界→回路(下限TRUE/上限差分変数)、量化子は宣言直積、
  comprehension/multiplicity/if式対応(int・時制は後続Iter)
- テスト計59(ipasir時61)。デモ `cargo run --example fol_demo --features ipasir`


### Iter 4 完了: int(TwosComplementInt)
- IntCircuit: 加減乗/非回復除算/bitwise/shl-shr-sha/比較/choice
- FolTranslator 統合: #基数・sum(int境界)・int比較6種・FromInt
- BoolFactory::ite に定数簡約8則(ConstantInside 問題解消)
- テスト計72(ipasir時74)

### Iter 9 完了: UNSAT コア(`-core=rce` 相当)
- `ipasir_failed` / `alloy_worker_failed` + `alloy_worker_assume`(失敗仮定)
- `SatSolver` 拡張(assume/failed)、RecordingSolver は厳密最小コアを全列挙で算出
- `ucore`: 連言フラット化→各項を selector **assumption** 化(定義のみ翻訳)
  → failed から初期コア → RCE相当の削除フィルタ最小化
- CNFレベル `SoftGroup`+`extract_cnf_core`、デモ
  `cargo run --release --example sudoku_core --features ipasir`
  (矛盾ヒント2つを3ソルブで特定)。設計記録は survey doc §7

### Iter 10 完了: Java 逆統合(`--engine rust`)
- 新クレート `alloy-engine-rs`: 問題直列化(ARE1)→ Rust パイプライン →
  モデル復元。C ABI + JNI(`RustEngineProxy.solveNative`)
- Java: `RustSerializer`(kodkod AST/Bounds ⇄ ARE1)、`A4Solution.solve()` の
  エンジン分岐、CLI `exec --engine rust`
- 受け入れ: extra/models 全83例題を両エンジン走査 → **結果100%一致**
  (`scripts/sweep-engines.sh`、結果は docs/engine-sweep-results.txt)

### Iter 11 完了: Wire v2 — 分解とオプションの JNI 有効化
- **ARE2**: solver options(skolemize / decompose mode / threads)+
  dynamic 用 trailer(partial 関係 + 記号境界)
- Java `RustSerializer` が PardinusBounds の**式境界を実体化**(Evaluator
  固定点評価)。IMPLIES/IFF は脱糖して対応
- Rust `solve_dynamic` が記号境界を stage-1 モデルから解決し stage-2 へ適用
  (Pardinus「stage 2 consumes stage 1」)
- CLI: `exec --engine rust --decompose hybrid|parallel`
- 受け入れ: ring.als 全モード SAT 一致、83 例題パリティ維持

```bash
cargo build --release -p alloy-engine-rs --features jni   # liballoy_engine.so
JAVA_HOME=~/.sdkman/candidates/java/25-amzn ./gradlew :org.alloytools.alloy.dist:build -x test
java -Dalloy.native.lib.alloy_engine=$PWD/alloy-sat-rs/target/release/liballoy_engine.so \
  -jar org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar \
  exec --engine rust -f org.alloytools.alloy.extra/extra/models/book/appendixA/ring.als
```
