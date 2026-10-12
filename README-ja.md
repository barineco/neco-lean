# neco-lean

[English](README.md)

`neco-lean` は、Lean 4 でコマンドラインツールや TUI ( 端末のユーザーインターフェース ) を作るためのライブラリです。
個人のコードベースから切り出したものです。

## 機能

目的ごとのモジュールと、それぞれでできることは次のとおりです。

| 目的 | モジュール | できること |
|---|---|---|
| 浮動小数点数への変換 | `NecoLean.Binary64` | 十進数を IEEE 754 倍精度のビット列に変換 ( 最近接偶数への丸め ) |
| ファイルと子プロセス | `NecoLean.System` | バイト列の読み書き、指定したコマンドの実行 |
| コマンドライン入力とメッセージ | `NecoLean.Cli`、`NecoLean.Diagnostic` | 引数の解析、ソース位置を含むメッセージの作成 |
| JSON | `NecoLean.Json` | 解析と、キーの順序を固定した出力 ( 入れ子は 128 段まで ) |
| KDL 文書 | `NecoLean.Kdl`、`NecoLean.Kdl.Ast` | 解析と組み立て、ノードの検索、参照の解決 |
| バイト列の読み取り | `NecoLean.Scanner` | トークン、整数、行の順次読み取り |
| バイト列の出力とハッシュ | `NecoLean.Printer`、`NecoLean.Digest` | 出力の組み立て、SHA-256 の計算 |
| 反復計算 | `NecoLean.Fixpoint` | 不動点の計算 ( 各反復の履歴つき ) |
| ローカルジャッジ | `NecoLean.Judge` | テストケースの検出、実行時間の計測、判定 |
| LLVM IR | `NecoLean.Llvm` | IR の組み立てと検証、テキスト出力、`clang` によるコンパイル |
| TUI | `NecoLean.Tui`、`NecoLean.Tui.Posix` | 画面の組み立てと、POSIX 端末での対話的な実行 |

実行時の失敗は、すべて結果型の値として返ります。

## ビルドとテスト

Lean は 4.32.1 を使い、この版は `lean-toolchain` で指定しています。

```sh
cd path/to/neco-lean
elan show
lake --version
lake build
lake exe neco-lean-tests -- all
```

版を明示して実行する場合は、次のコマンドを使います。

```sh
elan run leanprover/lean4:v4.32.1 lake build
elan run leanprover/lean4:v4.32.1 lake exe neco-lean-tests -- all
```

### 動作環境

Linux と macOS で動きます。
LLVM IR をコンパイルするには、`clang` が必要です。

## インポート

公開しているモジュールをまとめて読み込む場合は、次のように書きます。

```lean
import NecoLean
```

使うモジュールだけを個別にインポートする場合、対象のモジュールは次のとおりです。

```text
NecoLean.Binary64
NecoLean.System
NecoLean.Diagnostic
NecoLean.Cli
NecoLean.Json
NecoLean.Digest
NecoLean.Fixpoint
NecoLean.Scanner
NecoLean.Printer
NecoLean.Judge
NecoLean.Llvm
NecoLean.Kdl
NecoLean.Kdl.Ast
NecoLean.Tui
NecoLean.Tui.Posix
```

`import NecoLean` で読み込まれるのは、上に挙げたモジュールです。
KDL の公式テストベクターを使う検査用のモジュール `NecoLean.Kdl.Vectors` は、個別にインポートして使います。

## 使用例

`examples/` に、公開しているモジュールの使用例があります。

```sh
lake exe neco-lean-example-cli hello Ada
lake exe neco-lean-example-kdl examples/assets/document.kdl
lake exe neco-lean-example-kdl-tui examples/assets/document.kdl
```

- [CliBasic.lean](examples/CliBasic.lean): コマンドライン引数を解析する
- [KdlBasic.lean](examples/KdlBasic.lean): KDL ファイルを読み込んで解析する
- [KdlTreeTui.lean](examples/KdlTreeTui.lean): KDL 文書を木として端末画面に表示する

各使用例の説明は、[examples/README-ja.md](examples/README-ja.md) にあります。

## ライセンス

neco-lean は [MIT License](LICENSE) で公開しています。
`test/kdl-test-cases/` のテストデータは [KDL の公式テストスイート](https://github.com/kdl-org/kdl/tree/4e4c0af9333819aede3cd4867bbc8702dd78f96c/tests/test_cases) から取得したもので、CC-BY-SA 4.0 が適用されます。
