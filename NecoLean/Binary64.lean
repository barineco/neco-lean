import Init.Data.Float
import Init.Data.Nat.Log2

set_option autoImplicit false

namespace NecoLean.Binary64

structure Decimal where
  negative : Bool
  mantissa : Nat
  exponent : Int
  deriving Repr, BEq, Inhabited

inductive Failure where
  | overflow (input : Decimal)
  deriving Repr, BEq

private def signBits (negative : Bool) : Nat :=
  if negative then 0x8000000000000000 else 0

private partial def natDigitsAux : Nat → Nat → Nat
  | value, count =>
    if value < 10 then count + 1 else natDigitsAux (value / 10) (count + 1)
private def decimalDigits (value : Nat) : Nat :=
  if value = 0 then 1 else natDigitsAux value 0

private def decimalOrder (input : Decimal) : Int :=
  Int.ofNat (decimalDigits input.mantissa - 1) + input.exponent

private def bit (shift : Nat) : Nat :=
  2 ^ shift

private def intPow2 (exponent : Int) : Nat :=
  bit exponent.natAbs

private def scaledQuotient (numerator denominator : Nat) (unitExponent : Int) : Nat × Nat × Nat :=
  let (scaledNumerator, scaledDenominator) :=
    if unitExponent >= 0 then
      (numerator, denominator * intPow2 unitExponent)
    else
      (numerator * intPow2 (-unitExponent), denominator)
  let quotient := scaledNumerator / scaledDenominator
  let remainder := scaledNumerator % scaledDenominator
  (quotient, remainder, scaledDenominator)

private def roundNearestEven (quotient remainder denominator : Nat) : Nat :=
  let twice := remainder * 2
  if twice > denominator then quotient + 1
  else if twice < denominator then quotient
  else if quotient % 2 = 0 then quotient
  else quotient + 1

private def lePow2Scaled (numerator denominator : Nat) (exponent : Int) : Bool :=
  if exponent >= 0 then
    denominator * intPow2 exponent <= numerator
  else
    denominator <= numerator * intPow2 (-exponent)

private def exactBinade (numerator denominator : Nat) : Int :=
  let delta := Int.ofNat numerator.log2 - Int.ofNat denominator.log2
  if lePow2Scaled numerator denominator delta then delta else delta - 1

private def exactRatio (input : Decimal) : Nat × Nat :=
  if input.exponent >= 0 then
    (input.mantissa * (10 ^ input.exponent.toNat), 1)
  else
    (input.mantissa, 10 ^ (-input.exponent).toNat)

private def zeroBits (input : Decimal) : UInt64 :=
  UInt64.ofNat (signBits input.negative)

private def finiteBits (input : Decimal) (exponentField fractionField : Nat) : UInt64 :=
  UInt64.ofNat (signBits input.negative + exponentField * bit 52 + fractionField)

private def roundedNormalBits (input : Decimal) (binade : Int) (quotient : Nat) : Except Failure UInt64 :=
  if quotient >= bit 53 then
    let nextBinade := binade + 1
    if nextBinade > 1023 then
      .error (.overflow input)
    else
      let exponentField := (nextBinade + 1023).toNat
      .ok (finiteBits input exponentField 0)
  else
    let exponentField := (binade + 1023).toNat
    .ok (finiteBits input exponentField (quotient - bit 52))

private def roundedSubnormalBits (input : Decimal) (quotient : Nat) : UInt64 :=
  if quotient >= bit 52 then
    finiteBits input 1 0
  else
    finiteBits input 0 quotient

def Decimal.toBits (input : Decimal) : Except Failure UInt64 :=
  if input.mantissa = 0 then
    .ok (zeroBits input)
  else
    let order := decimalOrder input
    if order >= 309 then
      .error (.overflow input)
    else if order < -324 then
      .ok (zeroBits input)
    else
      let (numerator, denominator) := exactRatio input
      let binade := exactBinade numerator denominator
      if binade > 1023 then
        .error (.overflow input)
      else if binade >= -1022 then
        let (quotient, remainder, scaledDenominator) := scaledQuotient numerator denominator (binade - 52)
        roundedNormalBits input binade (roundNearestEven quotient remainder scaledDenominator)
      else
        let (quotient, remainder, scaledDenominator) := scaledQuotient numerator denominator (-1074)
        .ok (roundedSubnormalBits input (roundNearestEven quotient remainder scaledDenominator))

def Decimal.toFloat (input : Decimal) : Except Failure Float :=
  input.toBits.map Float.ofBits

end NecoLean.Binary64
