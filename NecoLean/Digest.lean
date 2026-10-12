set_option autoImplicit false

namespace NecoLean.Digest

structure Sha256 where
  bytes : Vector UInt8 32
  deriving BEq

private def constants : Array UInt32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e,
   0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624,
   0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3,
   0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
   0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def initial : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

private def rotr (value amount : UInt32) : UInt32 :=
  (value >>> amount) ||| (value <<< (32 - amount))

private def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~x) &&& z)
private def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
private def sigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
private def sigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
private def gamma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
private def gamma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

private def byteAt (block : ByteArray) (index : Nat) : UInt8 :=
  if h : index < block.size then block[index] else 0

private def wordAt (block : ByteArray) (base index : Nat) : UInt32 :=
  let offset := base + index * 4
  ((byteAt block offset).toUInt32 <<< 24) ||| ((byteAt block (offset + 1)).toUInt32 <<< 16) |||
    ((byteAt block (offset + 2)).toUInt32 <<< 8) ||| (byteAt block (offset + 3)).toUInt32

private partial def scheduleExtend (words : Array UInt32) (index : Nat) : Array UInt32 :=
  if index == 64 then words
  else
    let next := gamma1 (words.getD (index - 2) 0) + words.getD (index - 7) 0 +
      gamma0 (words.getD (index - 15) 0) + words.getD (index - 16) 0
    scheduleExtend (words.push next) (index + 1)

private partial def scheduleHead (block : ByteArray) (base index : Nat) (words : Array UInt32) :
    Array UInt32 :=
  if index == 16 then words else scheduleHead block base (index + 1) (words.push (wordAt block base index))

private def schedule (block : ByteArray) (base : Nat) : Array UInt32 :=
  scheduleExtend (scheduleHead block base 0 (Array.emptyWithCapacity 64)) 16

private partial def rounds (words : Array UInt32) (index : Nat)
    (a b c d e f g h : UInt32) : Array UInt32 :=
  if index == 64 then #[a, b, c, d, e, f, g, h]
  else
    let t1 := h + sigma1 e + ch e f g + constants.getD index 0 + words.getD index 0
    let t2 := sigma0 a + maj a b c
    rounds words (index + 1) (t1 + t2) a b c (d + t1) e f g

private def compress (state : Array UInt32) (block : ByteArray) (base : Nat) : Array UInt32 :=
  let result := rounds (schedule block base) 0
    (state.getD 0 0) (state.getD 1 0) (state.getD 2 0) (state.getD 3 0)
    (state.getD 4 0) (state.getD 5 0) (state.getD 6 0) (state.getD 7 0)
  #[state.getD 0 0 + result.getD 0 0, state.getD 1 0 + result.getD 1 0,
    state.getD 2 0 + result.getD 2 0, state.getD 3 0 + result.getD 3 0,
    state.getD 4 0 + result.getD 4 0, state.getD 5 0 + result.getD 5 0,
    state.getD 6 0 + result.getD 6 0, state.getD 7 0 + result.getD 7 0]

private def pad (bytes : ByteArray) : ByteArray :=
  let bitLength := bytes.size * 8
  let withOne := bytes.push 128
  let zeroCount := (56 + 64 - withOne.size % 64) % 64
  let padded := (List.range zeroCount).foldl (fun result _ => result.push 0) withOne
  (List.range 8).reverse.foldl
    (fun result index => result.push (Nat.toUInt8 ((bitLength / (2 ^ (index * 8))) % 256))) padded

private partial def processBlocks (bytes : ByteArray) (offset : Nat) (state : Array UInt32) : Array UInt32 :=
  if offset < bytes.size then processBlocks bytes (offset + 64) (compress state bytes offset)
  else state

private def digestWords (bytes : ByteArray) : Array UInt32 :=
  processBlocks (pad bytes) 0 initial

private def digestByte (words : Array UInt32) (index : Nat) : UInt8 :=
  let word := words.getD (index / 4) 0
  let shifted := match index % 4 with
    | 0 => word >>> 24
    | 1 => word >>> 16
    | 2 => word >>> 8
    | _ => word
  (shifted &&& 255).toUInt8

protected def sha256 (bytes : ByteArray) : Sha256 :=
  let words := digestWords bytes
  { bytes := Vector.ofFn (fun index => digestByte words index.val) }

protected def toHex (digest : Sha256) : String :=
  let digit (value : Nat) : Char :=
    if value < 10 then Char.ofNat (48 + value) else Char.ofNat (87 + value)
  digest.bytes.toList.foldl (fun result byte => result ++ String.ofList [digit (byte.toNat / 16), digit (byte.toNat % 16)]) ""

end NecoLean.Digest
