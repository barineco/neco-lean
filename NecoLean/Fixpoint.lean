import Init.Data.Nat.Bitwise

set_option autoImplicit false

namespace NecoLean.Fixpoint

abbrev BitMask := Nat
abbrev UniverseMask := BitMask
abbrev BitCount := Nat
abbrev isSubset (subsetBits supersetBits : BitMask) : Prop := Nat.land subsetBits supersetBits = subsetBits

private def subsetCheck (subsetBits supersetBits : BitMask) : Bool :=
  decide (isSubset subsetBits supersetBits)

def popcount : Nat → Nat
  | 0 => 0
  | bits + 1 => (bits + 1) % 2 + popcount ((bits + 1) / 2)
termination_by bits => bits
decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

private theorem popcount_eq_mod_add_div (bits : Nat) :
    popcount bits = bits % 2 + popcount (bits / 2) := by
  cases bits with
  | zero => simp [popcount]
  | succ bits => simp [popcount]

private theorem subset_div_two {x y : Nat} (h : isSubset x y) : isSubset (x / 2) (y / 2) := by
  change (x / 2 &&& y / 2) = x / 2
  rw [← Nat.and_div_two]
  change Nat.bitwise and x y / 2 = x / 2
  exact congrArg (fun n => n / 2) h

private theorem subset_mod_two_le {x y : Nat} (h : isSubset x y) : x % 2 ≤ y % 2 := by
  have hbit := congrArg (fun bits => bits.testBit 0) h
  change (x &&& y).testBit 0 = x.testBit 0 at hbit
  rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero] at hbit
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> simp [hx, hy] at hbit ⊢

private theorem popcount_le_of_subset {x y : Nat} (h : isSubset x y) : popcount x ≤ popcount y := by
  induction y using Nat.div2Induction generalizing x with
  | ind y ih =>
    cases Nat.eq_zero_or_pos y with
    | inl hy =>
      have hx : x = 0 := by simpa [isSubset, hy] using h.symm
      simp [hx, popcount]
    | inr hypos =>
      have hquotient := subset_div_two h
      have hcount := ih hypos hquotient
      have hmodulo := subset_mod_two_le h
      rw [popcount_eq_mod_add_div x, popcount_eq_mod_add_div y]
      omega

private theorem eq_of_subset_and_popcount_eq {x y : Nat}
    (h : isSubset x y) (hcount : popcount x = popcount y) : x = y := by
  induction y using Nat.div2Induction generalizing x with
  | ind y ih =>
    cases Nat.eq_zero_or_pos y with
    | inl hy =>
      have hx : x = 0 := by simpa [isSubset, hy] using h.symm
      omega
    | inr hypos =>
      have hquotient := subset_div_two h
      have hmodulo := subset_mod_two_le h
      have hquotientCount := popcount_le_of_subset hquotient
      rw [popcount_eq_mod_add_div x, popcount_eq_mod_add_div y] at hcount
      have hmoduloEq : x % 2 = y % 2 := by omega
      have hcountEq : popcount (x / 2) = popcount (y / 2) := by omega
      have hquotientEq := ih hypos hquotient hcountEq
      rw [← Nat.div_add_mod x 2, ← Nat.div_add_mod y 2, hquotientEq, hmoduloEq]

private theorem popcount_lt_of_subset_ne {x y : Nat}
    (h : isSubset x y) (hne : x ≠ y) : popcount x < popcount y := by
  apply Nat.lt_of_le_of_ne (popcount_le_of_subset h)
  intro heq
  exact hne (eq_of_subset_and_popcount_eq h heq)

private theorem lor_eq_left_iff (x y : Nat) : Nat.lor x y = x ↔ isSubset y x := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have hbit := congrArg (fun bits => bits.testBit i) h
    change (x ||| y).testBit i = x.testBit i at hbit
    change (y &&& x).testBit i = y.testBit i
    rw [Nat.testBit_or] at hbit
    rw [Nat.testBit_and]
    cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have hbit := congrArg (fun bits => bits.testBit i) h
    change (y &&& x).testBit i = y.testBit i at hbit
    change (x ||| y).testBit i = x.testBit i
    rw [Nat.testBit_and] at hbit
    rw [Nat.testBit_or]
    cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all

private theorem lor_within {x y support : Nat} (hx : isSubset x support) (hy : isSubset y support) : isSubset (Nat.lor x y) support := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hxb := congrArg (fun bits => bits.testBit i) hx
  have hyb := congrArg (fun bits => bits.testBit i) hy
  change (x &&& support).testBit i = x.testBit i at hxb
  change (y &&& support).testBit i = y.testBit i at hyb
  change ((x ||| y) &&& support).testBit i = (x ||| y).testBit i
  simp only [Nat.testBit_and, Nat.testBit_or] at hxb hyb ⊢
  cases hxi : x.testBit i <;> cases hyi : y.testBit i <;> cases hui : support.testBit i <;> simp_all

private theorem strict_lor {current mapped support : Nat}
    (hcurrent : isSubset current support)
    (hmapped : isSubset mapped support)
    (hne : Nat.lor current mapped ≠ current) :
    popcount support - popcount (Nat.lor current mapped) <
      popcount support - popcount current := by
  have hsubset : isSubset current (Nat.lor current mapped) := by
    apply Nat.eq_of_testBit_eq
    intro i
    change (current &&& (current ||| mapped)).testBit i = current.testBit i
    rw [Nat.testBit_and, Nat.testBit_or]
    cases hc : current.testBit i <;> cases hm : mapped.testBit i <;> simp
  have hcount : popcount current < popcount (Nat.lor current mapped) :=
    popcount_lt_of_subset_ne hsubset (by intro h; exact hne h.symm)
  have hwithin := popcount_le_of_subset (lor_within hcurrent hmapped)
  omega


structure RemainingMeasure where
  currentBitCount : BitCount
  universeBitCount : BitCount
  deriving Repr, BEq, DecidableEq

def remainingMeasure (universeMask : UniverseMask) (current : BitMask) : RemainingMeasure :=
  { currentBitCount := popcount current
    universeBitCount := popcount universeMask }

def remainingBitCount (measure : RemainingMeasure) : BitCount :=
  measure.universeBitCount - measure.currentBitCount

structure MonotoneMap (universeMask : UniverseMask) where
  apply : BitMask → BitMask
  monotone : ∀ {leftBits rightBits : BitMask}, isSubset leftBits universeMask → isSubset rightBits universeMask → isSubset leftBits rightBits → isSubset (apply leftBits) (apply rightBits)

structure ClosureInput where
  universeMask : UniverseMask
  initialBits : BitMask
  monotoneMap : MonotoneMap universeMask

inductive ClosureFailure where
  | initialOutsideUniverse
  | mapResultOutsideUniverse
  deriving Repr, BEq, DecidableEq

structure ClosureIteration where
  currentBits : BitMask
  mappedBits : BitMask
  nextBits : BitMask
  remainingMeasure : RemainingMeasure
  deriving Repr, BEq, DecidableEq

abbrev ClosureTrace := List ClosureIteration

structure ClosureResult where
  closureBits : BitMask
  trace : ClosureTrace
  deriving Repr, BEq, DecidableEq

private theorem isSubset_refl (bits : BitMask) : isSubset bits bits := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (bits &&& bits).testBit i = bits.testBit i
  simp

private theorem isSubset_trans {leftBits middleBits rightBits : BitMask} :
  isSubset leftBits middleBits → isSubset middleBits rightBits → isSubset leftBits rightBits := by
  intro leftMiddle middleRight
  apply Nat.eq_of_testBit_eq
  intro i
  have leftBit := congrArg (fun bits => bits.testBit i) leftMiddle
  have middleBit := congrArg (fun bits => bits.testBit i) middleRight
  change (leftBits &&& middleBits).testBit i = leftBits.testBit i at leftBit
  change (middleBits &&& rightBits).testBit i = middleBits.testBit i at middleBit
  change (leftBits &&& rightBits).testBit i = leftBits.testBit i
  simp only [Nat.testBit_and] at leftBit middleBit ⊢
  cases leftValue : leftBits.testBit i <;> cases middleValue : middleBits.testBit i <;>
    cases rightValue : rightBits.testBit i <;> simp_all

private theorem lor_within_universe {leftBits rightBits universeMask : BitMask} :
  isSubset leftBits universeMask → isSubset rightBits universeMask → isSubset (Nat.lor leftBits rightBits) universeMask :=
  lor_within

private theorem strict_lor_decreases_remaining {current mapped universeMask : BitMask} :
  isSubset current universeMask → isSubset mapped universeMask → Nat.lor current mapped ≠ current →
  remainingBitCount (remainingMeasure universeMask (Nat.lor current mapped)) < remainingBitCount (remainingMeasure universeMask current) := by
  intro currentWithin mappedWithin different
  exact strict_lor currentWithin mappedWithin different

private theorem isSubset_lor_left (leftBits rightBits : BitMask) :
    isSubset leftBits (Nat.lor leftBits rightBits) := by
  apply Nat.eq_of_testBit_eq
  intro index
  change (leftBits &&& (leftBits ||| rightBits)).testBit index = leftBits.testBit index
  rw [Nat.testBit_and, Nat.testBit_or]
  cases leftValue : leftBits.testBit index <;> cases rightValue : rightBits.testBit index <;> simp

private def iterateClosure
  (input : ClosureInput) (current : BitMask)
  (currentWithinUniverse : isSubset current input.universeMask) (trace : ClosureTrace) :
  Except ClosureFailure ClosureResult :=
  let mapped := input.monotoneMap.apply current
  if mappedWithinUniverse : subsetCheck mapped input.universeMask then
    let next := Nat.lor current mapped
    let nextTrace := trace ++ [{
      currentBits := current
      mappedBits := mapped
      nextBits := next
      remainingMeasure := remainingMeasure input.universeMask current
    }]
    if next = current then
      .ok { closureBits := current, trace := nextTrace }
    else
      iterateClosure input next (by
        simp only [subsetCheck] at mappedWithinUniverse
        exact lor_within_universe currentWithinUniverse (of_decide_eq_true mappedWithinUniverse)) nextTrace
  else
    .error .mapResultOutsideUniverse
termination_by remainingBitCount (remainingMeasure input.universeMask current)
decreasing_by
  apply strict_lor_decreases_remaining
  · exact currentWithinUniverse
  · simp only [subsetCheck] at mappedWithinUniverse
    exact of_decide_eq_true mappedWithinUniverse
  · assumption

private theorem iterateClosure_contains
    (input : ClosureInput) (current : BitMask)
    (currentWithinUniverse : isSubset current input.universeMask) (trace : ClosureTrace)
    (result : ClosureResult)
    (computed : iterateClosure input current currentWithinUniverse trace = .ok result) :
    isSubset current result.closureBits := by
  unfold iterateClosure at computed
  dsimp only at computed
  split at computed
  · rename_i mappedWithinUniverse
    split at computed
    · rename_i nextEqual
      cases computed
      simpa [nextEqual] using isSubset_refl current
    · rename_i nextDifferent
      exact isSubset_trans (isSubset_lor_left current (input.monotoneMap.apply current))
        (iterateClosure_contains input (Nat.lor current (input.monotoneMap.apply current))
          (lor_within_universe currentWithinUniverse
            (by simp only [subsetCheck] at mappedWithinUniverse
                exact of_decide_eq_true mappedWithinUniverse)) _ result computed)
  · contradiction
termination_by remainingBitCount (remainingMeasure input.universeMask current)
decreasing_by
  apply strict_lor_decreases_remaining
  · exact currentWithinUniverse
  · have mappedWithinUniverse : subsetCheck (input.monotoneMap.apply current) input.universeMask = true := by
      assumption
    simp only [subsetCheck] at mappedWithinUniverse
    exact of_decide_eq_true mappedWithinUniverse
  · assumption

private theorem iterateClosure_preFixpoint
    (input : ClosureInput) (current : BitMask)
    (currentWithinUniverse : isSubset current input.universeMask) (trace : ClosureTrace)
    (result : ClosureResult)
    (computed : iterateClosure input current currentWithinUniverse trace = .ok result) :
    isSubset (input.monotoneMap.apply result.closureBits) result.closureBits := by
  unfold iterateClosure at computed
  dsimp only at computed
  split at computed
  · rename_i mappedWithinUniverse
    split at computed
    · rename_i nextEqual
      cases computed
      apply (lor_eq_left_iff _ _).mp
      exact nextEqual
    · rename_i nextDifferent
      exact iterateClosure_preFixpoint input (Nat.lor current (input.monotoneMap.apply current))
        (lor_within_universe currentWithinUniverse
          (by simp only [subsetCheck] at mappedWithinUniverse
              exact of_decide_eq_true mappedWithinUniverse)) _ result computed
  · contradiction
termination_by remainingBitCount (remainingMeasure input.universeMask current)
decreasing_by
  apply strict_lor_decreases_remaining
  · exact currentWithinUniverse
  · have mappedWithinUniverse : subsetCheck (input.monotoneMap.apply current) input.universeMask = true := by
      assumption
    simp only [subsetCheck] at mappedWithinUniverse
    exact of_decide_eq_true mappedWithinUniverse
  · assumption

private theorem iterateClosure_least
    (input : ClosureInput) (current candidate : BitMask)
    (currentWithinUniverse : isSubset current input.universeMask)
    (currentWithinCandidate : isSubset current candidate)
    (candidateWithinUniverse : isSubset candidate input.universeMask)
    (candidatePreFixpoint : isSubset (input.monotoneMap.apply candidate) candidate)
    (trace : ClosureTrace) (result : ClosureResult)
    (computed : iterateClosure input current currentWithinUniverse trace = .ok result) :
    isSubset result.closureBits candidate := by
  unfold iterateClosure at computed
  dsimp only at computed
  split at computed
  · rename_i mappedWithinUniverse
    split at computed
    · rename_i nextEqual
      cases computed
      exact currentWithinCandidate
    · rename_i nextDifferent
      refine iterateClosure_least input (Nat.lor current (input.monotoneMap.apply current)) candidate
        (lor_within_universe currentWithinUniverse
          (by simp only [subsetCheck] at mappedWithinUniverse
              exact of_decide_eq_true mappedWithinUniverse))
        ?_ candidateWithinUniverse candidatePreFixpoint _ result computed
      apply lor_within_universe currentWithinCandidate
      apply isSubset_trans
      · apply input.monotoneMap.monotone currentWithinUniverse candidateWithinUniverse currentWithinCandidate
      · exact candidatePreFixpoint
  · contradiction
termination_by remainingBitCount (remainingMeasure input.universeMask current)
decreasing_by
  apply strict_lor_decreases_remaining
  · exact currentWithinUniverse
  · have mappedWithinUniverse : subsetCheck (input.monotoneMap.apply current) input.universeMask = true := by
      assumption
    simp only [subsetCheck] at mappedWithinUniverse
    exact of_decide_eq_true mappedWithinUniverse
  · assumption

def computeClosure : ClosureInput → Except ClosureFailure ClosureResult := fun input =>
  if initialWithinUniverse : subsetCheck input.initialBits input.universeMask then
    iterateClosure input input.initialBits (by
      simp only [subsetCheck] at initialWithinUniverse
      exact of_decide_eq_true initialWithinUniverse) []
  else
    .error .initialOutsideUniverse

theorem computeClosure_contains_initial
  (input : ClosureInput) (result : ClosureResult)
  (computed : computeClosure input = .ok result) :
  isSubset input.initialBits result.closureBits := by
  unfold computeClosure at computed
  split at computed
  · rename_i initialWithinUniverse
    exact iterateClosure_contains input input.initialBits
      (by simp only [subsetCheck] at initialWithinUniverse
          exact of_decide_eq_true initialWithinUniverse) [] result computed
  · contradiction

theorem computeClosure_preFixpoint
  (input : ClosureInput) (result : ClosureResult)
  (computed : computeClosure input = .ok result) :
  isSubset (input.monotoneMap.apply result.closureBits) result.closureBits := by
  unfold computeClosure at computed
  split at computed
  · rename_i initialWithinUniverse
    exact iterateClosure_preFixpoint input input.initialBits
      (by simp only [subsetCheck] at initialWithinUniverse
          exact of_decide_eq_true initialWithinUniverse) [] result computed
  · contradiction

theorem computeClosure_least_preFixpoint
  (input : ClosureInput) (result : ClosureResult) (candidate : BitMask)
  (computed : computeClosure input = .ok result)
  (initialWithinCandidate : isSubset input.initialBits candidate)
  (candidateWithinUniverse : isSubset candidate input.universeMask)
  (candidatePreFixpoint : isSubset (input.monotoneMap.apply candidate) candidate) :
  isSubset result.closureBits candidate := by
  unfold computeClosure at computed
  split at computed
  · rename_i initialWithinUniverse
    exact iterateClosure_least input input.initialBits candidate
      (by simp only [subsetCheck] at initialWithinUniverse
          exact of_decide_eq_true initialWithinUniverse)
      initialWithinCandidate candidateWithinUniverse candidatePreFixpoint [] result computed
  · contradiction

end NecoLean.Fixpoint
