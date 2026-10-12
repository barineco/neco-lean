# neco-lean のサンプル

ライブラリのモジュールを組み合わせた小さなプログラムが三つあります。入力に使う KDL 文書などのファイルは、`assets/` にあります。

各コマンドはリポジトリのルートで実行してください。`lake build` で三つのプログラムもビルドされます。

## コマンドライン引数の解析

[CliBasic.lean](CliBasic.lean) は、コマンドの形式と、その解析結果の型を定義します。

```sh
lake exe neco-lean-example-cli hello Ada
```

実行すると次のように表示されます。

```text
hello, Ada
```

## KDL 文書の読み取り

[KdlBasic.lean](KdlBasic.lean) は、ファイルをバイト列として読み込み、KDL 文書として解析します。解析後は最上位にあるノードの名前を表示します。

```sh
lake exe neco-lean-example-kdl examples/assets/document.kdl
```

この例で使うモジュールは次のとおりです。

- ファイルの読み込み: `NecoLean.System`
- KDL の解析: `NecoLean.Kdl`

## KDL の木を表示する TUI

[KdlTreeTui.lean](KdlTreeTui.lean) は、KDL 文書のノードを木として端末画面に表示し、キーとマウスで操作できるようにします。

```sh
lake exe neco-lean-example-kdl-tui examples/assets/document.kdl
```

**処理の流れ**

1. KDL ファイルをバイト列として読む
2. バイト列を KDL 文書として解析する
3. KDL の各ノードから `NecoLean.Tui.UiNode` を作る
4. `NecoLean.Tui.Tree` から画面モデルを初期化する
5. `NecoLean.Tui.Posix.runModel` で画面を表示し、端末から入力を受け取る

変換の全体は `KdlTreeTui.lean` に記述されています。入力文書は `assets/document.kdl` です。

**利用できる操作**

- `↑`、`↓`: 選択を移動する
- `enter`: ノードを展開または折りたたむ
- `t`: 詳細ペインの位置を切り替える
- `+`、`-`: 詳細ペインの大きさを変更する
- `?`: ヘルプを表示する
- `escape`: ヘルプを閉じる
- `q`: TUI を終了する
- `ctrl-c`: 入力を中断して TUI を終了する
- マウスクリック: 表示中のノードを選択する
- マウスホイール: 木をスクロールする

標準入力と標準出力を TTY に接続した状態で実行してください。終了するときは、TUI が端末の表示と入力の設定を起動前の状態に戻します。
