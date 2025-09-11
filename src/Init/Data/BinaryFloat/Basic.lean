/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Init.Data.BinaryFloat.Stuff

@[expose] public section

namespace Std

structure FloatFormat where
  /-- The amount of bits in the mantissa including the implicit bit. -/
  prec : Nat
  /--
  The exponent of the infinities, that is, `2 ^ fmt.maxExp` is the first power of two that is
  greater than all finite floating point numbers in this floating point format.
  -/
  maxExp : Nat
  prec_pos : 0 < prec := by decide
  prec_lt_maxExp : prec < maxExp := by decide

namespace FloatFormat

/-- The binary32 floating point format for single precision floating point numbers. -/
def binary32 : FloatFormat where
  prec := 24
  maxExp := 128

/-- The binary64 floating point format for double precision floating point numbers. -/
def binary64 : FloatFormat where
  prec := 53
  maxExp := 1024

variable (fmt : FloatFormat)

/--
The exponent of the smallest representable positive number, that is, every finite floating point
number is a multiple of `2 ^ fmt.minExp`.
-/
def minExp : Int :=
  3 - fmt.maxExp - fmt.prec

/--
Given `e`, compute the exponent of floating point numbers between `2 ^ (e - 1)` (inclusive) and
`2 ^ e` (exclusive). That is, any number in this range will be represented as a multiple of
`2 ^ fmt.fexp e`.
-/
def fexp (e : Int) : Int :=
  max (e - fmt.prec) fmt.minExp

def CanonicalMantissa (m : Nat) (e : Int) :=
  (fmt.fexp (m.size + e)) = e
deriving Decidable

def Bounded (m : Nat) (e : Int) :=
  fmt.CanonicalMantissa m e ∧ e ≤ fmt.maxExp - fmt.prec
deriving Decidable

/-- Discharge linear arithmetic goals related to `fexp` -/
scoped macro "fexp_trivial" : tactic =>
  let fmt := Lean.mkIdent `fmt
  `(tactic| {
    try simp +zetaDelta [FloatFormat.fexp, FloatFormat.minExp, FloatFormat.CanonicalMantissa,
      FloatFormat.Bounded] at *
    have := $(fmt).prec_pos
    have := $(fmt).prec_lt_maxExp
    omega
  })

@[simp]
theorem canonicalMantissa_zero_iff {fmt : FloatFormat} {e : Int} :
    fmt.CanonicalMantissa 0 e ↔ e = fmt.minExp := by
  fexp_trivial

@[simp]
theorem bounded_zero_iff {fmt : FloatFormat} {e : Int} :
    fmt.Bounded 0 e ↔ e = fmt.minExp := by
  fexp_trivial

theorem eq_minExp_of_size_lt_prec {m : Nat} {e : Int} (h : fmt.CanonicalMantissa m e)
    (h' : m.size < fmt.prec) : e = fmt.minExp := by
  fexp_trivial

def roundRatEven (q : Rat) : Rat :=
  let fexp := fmt.fexp (q.log2 + 1)
  (q / 2 ^ fexp).roundEven * 2 ^ fexp

def boundRat (q : Rat) : Rat :=
  max (min (2 ^ fmt.maxExp) q) (-2 ^ fmt.maxExp)

variable {fmt}

theorem minExp_lt_maxExp : fmt.minExp < fmt.maxExp := by
  fexp_trivial

theorem maxExp_pos : 0 < fmt.maxExp := by
  fexp_trivial

theorem minExp_le_maxExp : fmt.minExp ≤ fmt.maxExp := Int.le_of_lt minExp_lt_maxExp

end FloatFormat

inductive BinaryFloat (fmt : FloatFormat) where
  | nan
  | inf (s : Bool)
  | finite (s : Bool) (m : Nat) (e : Int) (h : fmt.Bounded m e)
deriving DecidableEq

namespace BinaryFloat

open scoped FloatFormat

variable {fmt : FloatFormat}

inductive IsFinite : BinaryFloat fmt → Prop where
  | finite (s m e h) : BinaryFloat.IsFinite (.finite s m e h)

attribute [simp] IsFinite.finite

instance (b : BinaryFloat fmt) : Decidable (IsFinite b) :=
  match b with
  | .nan => .isFalse nofun
  | .inf _ => .isFalse nofun
  | .finite _ _ _ _ => .isTrue (.finite ..)

def toRat : BinaryFloat fmt → Rat
  | .nan => 0
  | .inf s => Rat.ofSign s * 2 ^ fmt.maxExp
  | .finite s m e _ => Rat.ofSign s * m * 2 ^ e

protected def zero (s : Bool) : BinaryFloat fmt :=
  .finite s 0 fmt.minExp (fmt.bounded_zero_iff.mpr rfl)

protected def sign : BinaryFloat fmt → Bool
  | .nan => false
  | .inf s => s
  | .finite s _ _ _ => s

protected def neg : BinaryFloat fmt → BinaryFloat fmt
  | .nan => .nan
  | .inf s => .inf (!s)
  | .finite s m e h => .finite (!s) m e h

instance : Neg (BinaryFloat fmt) := ⟨BinaryFloat.neg⟩

protected def blt : BinaryFloat fmt → BinaryFloat fmt → Bool
  | .nan, _ => false
  | _, .nan => false
  | .inf s₁, .inf s₂ => s₁ && !s₂
  | .inf s, .finite _ _ _ _ => s
  | .finite _ _ _ _, .inf s => !s
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _ =>
    match s₁, s₂ with
    | false, false => e₁ ≤ e₂ ∧ (e₁ < e₂ ∨ m₁ < m₂)
    | false, true => false
    | true, false => ¬(m₁ = 0 ∧ m₂ = 0)
    | true, true => e₂ ≤ e₁ ∧ (e₂ < e₁ ∨ m₂ < m₁)

protected def beq : BinaryFloat fmt → BinaryFloat fmt → Bool
  | .nan, _ => false
  | _, .nan => false
  | .inf s₁, .inf s₂ => s₁ == s₂
  | .inf _, .finite _ _ _ _ => false
  | .finite _ _ _ _, .inf _ => false
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _ =>
    (m₁ == 0 && m₂ == 0) || s₁ == s₂ && m₁ == m₂ && e₁ == e₂

protected def ble (a b : BinaryFloat fmt) : Bool :=
  a.blt b || a.beq b

instance : LT (BinaryFloat fmt) := ⟨fun a b => BinaryFloat.blt a b⟩
instance : LE (BinaryFloat fmt) := ⟨fun a b => BinaryFloat.ble a b⟩
instance : BEq (BinaryFloat fmt) := ⟨fun a b => BinaryFloat.beq a b⟩
instance : DecidableLT (BinaryFloat fmt) := fun _ _ => inferInstanceAs (Decidable (_ = _))
instance : DecidableLE (BinaryFloat fmt) := fun _ _ => inferInstanceAs (Decidable (_ = _))

def incMantissa : BinaryFloat fmt → BinaryFloat fmt
  | .nan => .nan
  | .inf s => .inf s
  | .finite s m e h =>
    if h' : m + 1 < 2 ^ fmt.prec then
      .finite s (m + 1) e ?simple
    else if h' : e < fmt.maxExp - fmt.prec then
      .finite s (1 <<< (fmt.prec - 1)) (e + 1) ⟨?overflow, h'⟩
    else
      .inf s
where finally
  case simple =>
    rw [← Nat.size_le] at h'
    simp only [FloatFormat.Bounded, FloatFormat.CanonicalMantissa] at h ⊢
    simp only [h.2, and_true]
    have : m.size ≤ (m + 1).size := Nat.size_mono (Nat.le_add_right m 1)
    fexp_trivial
  case overflow =>
    simp [FloatFormat.CanonicalMantissa, Nat.size_shiftLeft]
    fexp_trivial

def binaryRoundAux (s : Bool) (m : Nat) (e : Int) (exact : Bool)
    (h : e < fmt.fexp (m.size + e)) : BinaryFloat fmt :=
  let fexp := fmt.fexp (m.size + e)
  if h' : fmt.maxExp - fmt.prec < fexp then .inf s else
  let shift := (fexp - e).toNat
  let val := m >>> shift
  have : fmt.CanonicalMantissa val fexp := by fexp_trivial
  let res := .finite s val fexp ⟨this, Int.le_of_not_gt h'⟩
  let b := m.testBit (shift - 1)
  let exact := exact && m &&& (1 <<< (shift - 1) - 1) == 0
  let addOne := b && (!exact || val % 2 == 1)
  if addOne then res.incMantissa else res

def binaryRound (s : Bool) (m : Nat) (e : Int) : BinaryFloat fmt :=
  if h : m = 0 then
    .zero s
  else if h' : 2 ^ fmt.prec ≤ m then
    binaryRoundAux s m e true ?big
  else
    binaryRoundAux s (m <<< (fmt.prec + 1)) (e - (fmt.prec + 1)) true ?small
where finally
  case big =>
    rw [← Nat.lt_size] at h'
    fexp_trivial
  case small =>
    rw [Nat.size_shiftLeft h]
    fexp_trivial

def binaryNormalize (m : Int) (e : Int) : BinaryFloat fmt :=
  binaryRound (m matches .negSucc _) m.natAbs e

protected def ofNat (m : Nat) : BinaryFloat fmt :=
  binaryRound false m 0

protected def ofInt (m : Int) : BinaryFloat fmt :=
  binaryNormalize m 0

protected def mul (a b : BinaryFloat fmt) : BinaryFloat fmt :=
  match a, b with
  | .nan, _ => a
  | _, .nan => b
  | .inf s, .inf s' => .inf (s ^^ s')
  | .inf s, .finite s' m _ _ => if m = 0 then .nan else .inf (s ^^ s')
  | .finite s m _ _, .inf s' => if m = 0 then .nan else .inf (s ^^ s')
  | .finite s₁ m₁ e₁ h₁, .finite s₂ m₂ e₂ h₂ =>
    if h : m₁ * m₂ = 0 then .zero (s₁ ^^ s₂)
    else binaryRoundAux (s₁ ^^ s₂) (m₁ * m₂ * 2) (e₁ + e₂ - 1) true ?_
where finally
  simp only [not_or, Nat.mul_eq_zero] at h
  have : 0 < m₁.size := Nat.pos_of_ne_zero (mt Nat.size_eq_zero_iff.mp h.1)
  have : 0 < m₂.size := Nat.pos_of_ne_zero (mt Nat.size_eq_zero_iff.mp h.2)
  have : m₁.size + m₂.size ≤ (m₁ * m₂ * 2).size := by
    rw [← Nat.pow_one 2, ← Nat.shiftLeft_eq, Nat.size_shiftLeft (Nat.mul_ne_zero h.1 h.2)]
    apply Nat.le_add_of_sub_le
    exact Nat.lt_size_mul h.1 h.2
  fexp_trivial

instance : Mul (BinaryFloat fmt) := ⟨BinaryFloat.mul⟩

def encode (x : BinaryFloat fmt) : BitVec (1 + fmt.maxExp.log2 + fmt.prec) :=
  let sign : BitVec 1 := BitVec.ofBool x.sign
  let exp : BitVec (1 + fmt.maxExp.log2) :=
    match x with
    | .nan | .inf _ => BitVec.allOnes _
    | .finite _ m e _ =>
      if m.size < fmt.prec then
        0#_
      else
        BitVec.ofInt _ (e + fmt.prec + fmt.maxExp - 2)
  let mant : BitVec (fmt.prec - 1) :=
    match x with
    | .nan => BitVec.ofNat _ (2 ^ (fmt.prec - 2))
    | .inf _ => 0#_
    | .finite _ m _ _ => BitVec.ofNat _ m
  (sign ++ exp ++ mant).cast (by fexp_trivial)

def decode (x : BitVec (1 + fmt.maxExp.log2 + fmt.prec)) : BinaryFloat fmt :=
  let sign := x.msb
  let exp := x.extractLsb' (fmt.prec - 1) (1 + fmt.maxExp.log2)
  let mant := x.extractLsb' 0 (fmt.prec - 1)
  if h : exp = .allOnes _ then
    if mant = 0 then
      .inf sign
    else
      .nan
  else if h' : exp = 0 then
    .finite sign mant.toNat fmt.minExp ?subnormal
  else
    .finite sign (mant.toNat + 1 <<< (fmt.prec - 1)) (exp.toNat + 2 - fmt.maxExp - fmt.prec) ?normal
where finally
  case subnormal =>
    have : mant.toNat.size ≤ fmt.prec - 1 := Nat.size_le.mpr mant.isLt
    fexp_trivial
  case normal =>
    simp only [← BitVec.lt_allOnes_iff, BitVec.lt_def, BitVec.toNat_allOnes, Nat.pow_add,
      Nat.pow_one] at h
    have := Nat.log2_self_le (Nat.ne_of_gt fmt.maxExp_pos)
    have : (mant.toNat + 1 <<< (fmt.prec - 1)).size = fmt.prec := by
      rw [Nat.size_eq_iff' (Nat.ne_of_gt fmt.prec_pos), Nat.shiftLeft_eq]
      conv => enter [2, 2]; rw [← Nat.sub_one_add_one_eq_of_pos fmt.prec_pos, Nat.pow_add_one]
      omega
    have : 0 < exp.toNat := by simpa [← BitVec.le_zero_iff] using h'
    rw [← Nat.sub_one_add_one_eq_of_pos this]
    constructor <;> fexp_trivial

-- for `DecidableEq Float`
theorem decode_encode (x : BinaryFloat fmt) (hmax : fmt.maxExp = 2 ^ fmt.maxExp.log2)
    (hprec : 1 < fmt.prec) : decode (encode x) = x := by
  change have a := encode x; decode a = x
  unfold encode
  unfold decode
  extract_lets sign exp mant a sign' exp' mant'
  have hsign : sign' = x.sign := by simp [sign', a, BitVec.msb_append, sign]
  have hexp : exp' = exp := by simp [exp', a, BitVec.extractLsb'_append_eq_ite]
  have hmant : mant' = mant := by
    simp [mant', a, BitVec.extractLsb'_append_eq_ite, Nat.sub_eq_zero_iff_le, Nat.not_le_of_lt hprec]
  simp only [hexp, hmant, BitVec.ofNat_eq_ofNat, hsign]
  rcases x with _ | _ | ⟨s, m, e, h⟩
  · let a := fmt.prec - 2
    have : fmt.prec = a + 2 := by omega
    simp [exp, mant, ← BitVec.toNat_inj, this, Nat.pow_add, Nat.mod_mul, Nat.div_self,
      Nat.two_pow_pos]
  · simp [exp, mant, BinaryFloat.sign]
  · by_cases h' : m.size < fmt.prec
    · cases fmt.eq_minExp_of_size_lt_prec h.1 h'
      have : m < 2 ^ (fmt.prec - 1) := by
        rwa [← Nat.le_sub_one_iff_lt fmt.prec_pos, Nat.size_le] at h'
      simp [h', exp, BinaryFloat.sign, mant, Nat.mod_eq_of_lt this]
    · have hexp2 : exp.toNat = e + ↑fmt.prec + ↑fmt.maxExp - 2 := by
        simp only [h', ↓reduceIte, BitVec.toNat_ofInt, Int.natCast_pow, Int.cast_ofNat_Int,
          Int.ofNat_toNat, ne_eq, Int.reduceEq, not_false_eq_true,
          Int.max_eq_left (Int.emod_nonneg _ (Int.pow_ne_zero _)), exp]
        clear hmant hexp hsign mant' exp' sign' a mant exp sign
        rw [Int.emod_eq_of_lt]
        · fexp_trivial
        · rw [Int.pow_add, Int.pow_succ]
          norm_cast; rw [← hmax]
          fexp_trivial
      simp only [← BitVec.toNat_inj, BitVec.toNat_allOnes, BitVec.toNat_ofNat, Nat.zero_mod,
        BinaryFloat.sign, hexp2, Int.sub_add_cancel, Int.add_sub_cancel]
      simp only [Nat.pow_add, Nat.pow_one, ← hmax, ← Int.natCast_inj, hexp2, Int.cast_ofNat_Int]
      rw [dif_neg (by clear hexp2 hmant hexp hsign mant' exp' sign' a mant exp sign; fexp_trivial)]
      rw [dif_neg (by clear hexp2 hmant hexp hsign mant' exp' sign' a mant exp sign; fexp_trivial)]
      congr 1
      simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.one_mul, mant]
      have : m / 2 ^ (fmt.prec - 1) = 1 := by
        simp [Nat.div_eq_iff, ← Nat.lt_size, ← Nat.mul_two, ← Nat.pow_succ,
          Nat.sub_one_add_one_eq_of_pos fmt.prec_pos, Nat.le_sub_one_iff_lt, ← Nat.size_le]
        clear hexp2 hmant hexp hsign mant' exp' sign' a mant exp sign
        fexp_trivial
      conv => enter [1, 2]; rw [← Nat.mul_one (2 ^ _)]; arg 2; rw [← this]
      rw [Nat.mod_add_div]

end BinaryFloat
