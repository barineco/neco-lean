-- Generated test vectors shared by the digest and JSON tests.

import NecoLean

set_option autoImplicit false

namespace NecoLean.Test.SharedVectors

inductive JsonInput where
  | json (text : String)
  | hex (bytes : ByteArray)
  deriving BEq

inductive JsonExpected where
  | ok (text : String)
  | error (tag : String)
  deriving BEq

structure JsonVector where
  name : String
  input : JsonInput
  expected : JsonExpected
  deriving BEq

def digestVectors : List (String × ByteArray × String) := [
  ("empty", "".toUTF8, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
  ("abc", "abc".toUTF8, "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
  ("55", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".toUTF8, "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"),
  ("56", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".toUTF8, "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a"),
  ("63", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".toUTF8, "7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34"),
  ("64", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".toUTF8, "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"),
  ("65", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".toUTF8, "635361c48bb9eab14198e76ea8ab7f1a41685d6ad62aa9146d301d4f17eb0ae0"),
  ("1000", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".toUTF8, "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"),
]

def jsonVectors : List JsonVector := [
  { name := "null", input := JsonInput.json "null", expected := JsonExpected.ok "null" },
  { name := "bool-true", input := JsonInput.json "true", expected := JsonExpected.ok "true" },
  { name := "bool-false", input := JsonInput.json "false", expected := JsonExpected.ok "false" },
  { name := "number-negative", input := JsonInput.json "-12.5e+2", expected := JsonExpected.ok "-12.5e+2" },
  { name := "string-escaped", input := JsonInput.json "\"control \\u0001 quote \\\" slash \\\\ Unicode あ\"", expected := JsonExpected.ok "\"control \\u0001 quote \\\" slash \\\\ Unicode あ\"" },
  { name := "array", input := JsonInput.json "[null,7,false]", expected := JsonExpected.ok "[null,7,false]" },
  { name := "object", input := JsonInput.json "{\"b\":2,\"a\":\"あ\"}", expected := JsonExpected.ok "{\"a\":\"あ\",\"b\":2}" },
  { name := "object-canonical", input := JsonInput.json "{\"b\":2,\"a\":\"quote \\\" slash \\\\ newline \\n あ\"}", expected := JsonExpected.ok "{\"a\":\"quote \\\" slash \\\\ newline \\n あ\",\"b\":2}" },
  { name := "duplicate-key", input := JsonInput.json "{\"a\":1,\"a\":2}", expected := JsonExpected.error "duplicate-key" },
  { name := "invalid-utf8-leading", input := JsonInput.hex [255].toByteArray, expected := JsonExpected.error "invalid-utf8" },
  { name := "invalid-utf8-continuation", input := JsonInput.hex [34, 128, 52].toByteArray, expected := JsonExpected.error "invalid-utf8" },
  { name := "invalid-utf8-truncated", input := JsonInput.hex [34, 226, 130, 34].toByteArray, expected := JsonExpected.error "invalid-utf8" },
  { name := "invalid-utf8-overlong", input := JsonInput.hex [34, 192, 128, 34].toByteArray, expected := JsonExpected.error "invalid-utf8" },
  { name := "invalid-utf8-surrogate", input := JsonInput.hex [34, 237, 160, 128, 34].toByteArray, expected := JsonExpected.error "invalid-utf8" },
  { name := "invalid-utf8-too-large", input := JsonInput.hex [34, 244, 144, 128, 128, 34].toByteArray, expected := JsonExpected.error "invalid-utf8" },
  { name := "trailing-token", input := JsonInput.json "true false", expected := JsonExpected.error "trailing" },
  { name := "leading-zero", input := JsonInput.json "01", expected := JsonExpected.error "trailing" },
  { name := "invalid-fraction", input := JsonInput.json "1.", expected := JsonExpected.error "invalid" },
  { name := "invalid-exponent", input := JsonInput.json "1e", expected := JsonExpected.error "invalid" },
  { name := "invalid-empty-sign", input := JsonInput.json "-", expected := JsonExpected.error "invalid" },
  { name := "number-lower-e", input := JsonInput.json "1e5", expected := JsonExpected.ok "1e5" },
  { name := "number-upper-e", input := JsonInput.json "1E5", expected := JsonExpected.ok "1E5" },
  { name := "number-zero-exp", input := JsonInput.json "0e0", expected := JsonExpected.ok "0e0" },
  { name := "number-positive-exp", input := JsonInput.json "1e+5", expected := JsonExpected.ok "1e+5" },
  { name := "number-negative-exp", input := JsonInput.json "1e-5", expected := JsonExpected.ok "1e-5" },
  { name := "surrogate-high", input := JsonInput.json "\"\\ud800\"", expected := JsonExpected.error "invalid" },
  { name := "surrogate-low", input := JsonInput.json "\"\\udfff\"", expected := JsonExpected.error "invalid" },
  { name := "surrogate-pair", input := JsonInput.json "\"\\ud800\\udc00\"", expected := JsonExpected.ok "\"𐀀\"" },
  { name := "escaped-duplicate-key", input := JsonInput.json "{\"a\":1,\"\\u0061\":2}", expected := JsonExpected.error "duplicate-key" },
  { name := "nested-object", input := JsonInput.json "{\"z\":{\"b\":2,\"a\":1},\"a\":{\"d\":{\"y\":2,\"x\":1},\"c\":3}}", expected := JsonExpected.ok "{\"a\":{\"c\":3,\"d\":{\"x\":1,\"y\":2}},\"z\":{\"a\":1,\"b\":2}}" },
  { name := "object-permutation-a", input := JsonInput.json "{\"b\":2,\"a\":1,\"nested\":{\"d\":4,\"c\":3}}", expected := JsonExpected.ok "{\"a\":1,\"b\":2,\"nested\":{\"c\":3,\"d\":4}}" },
  { name := "object-permutation-b", input := JsonInput.json "{\"nested\":{\"c\":3,\"d\":4},\"a\":1,\"b\":2}", expected := JsonExpected.ok "{\"a\":1,\"b\":2,\"nested\":{\"c\":3,\"d\":4}}" },
  { name := "array-permutation-a", input := JsonInput.json "[1,2,3]", expected := JsonExpected.ok "[1,2,3]" },
  { name := "array-permutation-b", input := JsonInput.json "[3,2,1]", expected := JsonExpected.ok "[3,2,1]" },
  { name := "unicode-letter", input := JsonInput.json "\"\\u0041\"", expected := JsonExpected.ok "\"A\"" },
]

end NecoLean.Test.SharedVectors
