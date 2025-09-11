/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Init.Data.BinaryFloat.Basic

namespace Std

open Lean.Grind.AddCommGroup
open Lean.Grind.OrderedAdd
open Lean.Grind.OrderedRing
open Lean.Grind.Field.IsOrdered

namespace FloatFormat

variable {fmt : FloatFormat}

private theorem roundRatEven_mono_on_pos {a b : Rat}
    (ha : 0 < a) (hb : 0 < b) (h' : fmt.fexp (a.log2 + 1) < fmt.fexp (b.log2 + 1)) :
    fmt.roundRatEven a ≤ fmt.roundRatEven b := by
  rw [roundRatEven, roundRatEven]
  apply Rat.le_trans (b := 2 ^ fmt.prec * 2 ^ fmt.fexp (a.log2 + 1))
  · apply Rat.mul_le_mul_of_nonneg_right _ (Rat.zpow_nonneg (by decide))
    have : (2 : Rat) ^ fmt.prec = Rat.roundEven (2 ^ (fmt.prec : Int)) := by norm_cast
    rw [this, Rat.intCast_le_intCast]
    apply Rat.roundEven_mono
    rw [Rat.div_le_iff (Rat.zpow_pos (by decide)), ← Rat.zpow_add (by decide)]
    apply Rat.le_of_lt ((Rat.log2_lt ha).mp _)
    simp only [fexp]
    omega
  apply Rat.le_trans (b := 2 ^ fmt.prec * 2 ^ (fmt.fexp (b.log2 + 1) - 1))
  · exact Rat.mul_le_mul_of_nonneg_left
      (Rat.zpow_le_zpow_right (by decide) (Int.le_sub_one_of_lt h')) (Rat.pow_nonneg (by decide))
  · rw [Rat.zpow_sub_one (by decide), Rat.mul_comm _ (2⁻¹), ← Rat.mul_assoc]
    apply Rat.mul_le_mul_of_nonneg_right _ (Rat.zpow_nonneg (by decide))
    rw [← Rat.zpow_natCast, ← Rat.zpow_sub_one (by decide)]
    have : (2 : Rat) ^ (fmt.prec - 1 : Int) = Rat.roundEven (2 ^ (fmt.prec - 1 : Int)) := by
      rw [← Nat.sub_one_add_one_eq_of_pos fmt.prec_pos]
      simp only [Int.natCast_add, Int.cast_ofNat_Int, Int.add_sub_cancel]; norm_cast
    rw [this, Rat.intCast_le_intCast]
    apply Rat.roundEven_mono
    rw [Rat.le_div_iff (Rat.zpow_pos (by decide)), ← Rat.zpow_add (by decide)]
    apply (Rat.le_log2 hb).mp
    simp [fexp] at h' ⊢
    omega

@[simp]
theorem roundRatEven_zero : fmt.roundRatEven 0 = 0 := by
  simp [roundRatEven, Rat.div_def]

theorem roundRatEven_neg {q : Rat} :
    fmt.roundRatEven (-q) = -fmt.roundRatEven q := by
  simp only [roundRatEven, Rat.log2_neg, Rat.div_def, Rat.neg_mul, Rat.roundEven_neg,
    Rat.intCast_neg]

theorem roundRatEven_ofSign_mul {b : Bool} {q : Rat} :
    fmt.roundRatEven (Rat.ofSign b * q) = Rat.ofSign b * fmt.roundRatEven q := by
  cases b <;> simp [roundRatEven_neg, Rat.neg_mul]

theorem roundRatEven_nonneg {q : Rat} (hq : 0 ≤ q) : 0 ≤ fmt.roundRatEven q := by
  simp only [roundRatEven]
  apply Rat.mul_nonneg _ (Rat.zpow_nonneg (by decide))
  rw [show (0 : Rat) = Rat.roundEven 0 from rfl, Rat.intCast_le_intCast]
  apply Rat.roundEven_mono
  rw [Rat.div_def]
  exact Rat.mul_nonneg hq (inv_nonneg_iff.mpr (Rat.zpow_nonneg (by decide)))

theorem roundRatEven_nonpos {q : Rat} (hq : q ≤ 0) : fmt.roundRatEven q ≤ 0 := by
  have := fmt.roundRatEven_nonneg (neg_nonneg_iff.mpr hq)
  rw [roundRatEven_neg] at this
  exact neg_nonneg_iff.mp this

theorem roundRatEven_mono {a b : Rat} (h : a ≤ b) :
    fmt.roundRatEven a ≤ fmt.roundRatEven b := by
  by_cases exp_eq : fmt.fexp (a.log2 + 1) = fmt.fexp (b.log2 + 1)
  · simp only [roundRatEven, exp_eq]
    apply Rat.mul_le_mul_of_nonneg_right
    · apply Rat.intCast_le_intCast.mpr
      apply Rat.roundEven_mono
      simp only [Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_right ‹_› (inv_nonneg_iff.mpr (Rat.zpow_nonneg (by decide)))
    · exact Rat.zpow_nonneg (by decide)
  by_cases haz : a = 0
  · simp_all [roundRatEven_nonneg]
  by_cases hbz : b = 0
  · simp_all [roundRatEven_nonpos]
  by_cases han : a < 0
  · by_cases hbn : b < 0
    · have hneg : -b ≤ -a := by simp [neg_le_iff (a := b), h]
      have := fmt.roundRatEven_mono_on_pos (neg_pos_iff.mpr hbn) (neg_pos_iff.mpr han)
      simp only [Rat.log2_neg, roundRatEven_neg, neg_le_iff, Rat.neg_neg] at this
      apply this
      apply Std.lt_of_le_of_ne _ (Ne.symm exp_eq)
      have := Rat.log2_mono (neg_pos_iff.mpr hbn) hneg
      simp only [Rat.log2_neg] at this
      simp only [fexp]
      omega
    · exact Rat.le_trans (fmt.roundRatEven_nonpos (Rat.le_of_lt han))
        (fmt.roundRatEven_nonneg (Rat.not_lt.mp hbn))
  · simp only [Rat.not_lt] at han
    replace han := Rat.lt_of_le_of_ne han (Ne.symm haz)
    have hbn := Std.lt_of_lt_of_le han h
    apply fmt.roundRatEven_mono_on_pos han hbn
    apply Std.lt_of_le_of_ne _ exp_eq
    have := Rat.log2_mono han h
    simp only [fexp]
    omega

theorem roundRatEven_two_zpow_eq_self {i : Int} (hi : fmt.minExp ≤ i) :
    fmt.roundRatEven (2 ^ i) = 2 ^ i := by
  simp only [roundRatEven, fexp, Rat.log2_two_zpow]
  rw [← Rat.zpow_sub (by decide)]
  by_cases h : i + 1 - fmt.prec ≤ fmt.minExp
  · rw [Int.max_eq_right h]
    have : i - fmt.minExp = (i - fmt.minExp).toNat := by omega
    rw [this]
    norm_cast
    rw [Rat.roundEven_natCast]
    simp [← Rat.zpow_natCast, ← this, ← Rat.zpow_add]
  · rw [Int.max_eq_left (Int.le_of_not_le h)]
    have : i - (i + 1 - ↑fmt.prec) = (fmt.prec - 1 : Nat) := by have := fmt.prec_pos; omega
    rw [this]
    norm_cast
    rw [Rat.roundEven_natCast]
    simp only [Int.natCast_pow, Int.cast_ofNat_Int, Rat.intCast_pow, Rat.intCast_ofNat,
      ← Rat.zpow_natCast, ne_eq, Rat.ofNat_eq_ofNat, reduceCtorEq, not_false_eq_true,
      ← Rat.zpow_add]
    congr 1; omega

theorem roundRatEven_two_pow_eq_self {i : Nat} (hi : fmt.minExp ≤ i) :
    fmt.roundRatEven (2 ^ i) = 2 ^ i :=
  fmt.roundRatEven_two_zpow_eq_self (i := i) hi

theorem boundRat_of_ge {q : Rat} (h : 2 ^ fmt.maxExp ≤ q) :
    fmt.boundRat q = 2 ^ fmt.maxExp := by
  simp only [boundRat, min_eq_if, h, ↓reduceIte, max_eq_if]
  simp only [← Rat.zero_sub, Rat.sub_le_iff_le_add, ite_eq_left_iff]
  intro h
  apply absurd _ h
  refine Rat.add_nonneg ?nonneg ?nonneg
  exact Rat.pow_nonneg (by decide)

theorem boundRat_of_le {q : Rat} (h : q ≤ -2 ^ fmt.maxExp) :
    fmt.boundRat q = -2 ^ fmt.maxExp := by
  simp only [boundRat, max_eq_if, le_min_iff, ite_eq_right_iff, and_imp]
  intro h' h''
  cases Rat.le_antisymm h h''
  simp only [min_eq_if, ite_eq_right_iff]
  rw [← Rat.zero_sub, Rat.le_sub_iff_add_le]
  intro h
  apply absurd h
  rw [← Rat.mul_one (2 ^ _), ← Rat.mul_add]
  exact Rat.not_le.mpr (Rat.mul_pos (Rat.pow_pos (by decide)) (by decide +kernel))

theorem boundRat_of_le_of_ge {q : Rat} (h : q ≤ 2 ^ fmt.maxExp)
    (h' : -2 ^ fmt.maxExp ≤ q) :
    fmt.boundRat q = q := by
  simp only [boundRat, min_eq_if, max_eq_if]
  split
  · cases Rat.le_antisymm h ‹_›
    simp [h']
  · rfl

@[simp]
theorem boundRat_zero : fmt.boundRat 0 = 0 := by
  rw [boundRat_of_le_of_ge]
  · exact Rat.pow_nonneg (by decide)
  · exact neg_le_iff.mp <| Rat.pow_nonneg (by decide)

theorem boundRat_neg {q : Rat} :
    fmt.boundRat (-q) = -fmt.boundRat q := by
  by_cases h : q ≤ 2 ^ fmt.maxExp
  · by_cases h' : -2 ^ fmt.maxExp ≤ q
    · rw [boundRat_of_le_of_ge h h', boundRat_of_le_of_ge (neg_le_iff.mp h')]
      rwa [neg_le_iff, Rat.neg_neg]
    · rw [boundRat_of_le (Std.le_of_not_ge h'), Rat.neg_neg,
        boundRat_of_ge (le_neg_iff.mpr (Std.le_of_not_ge h'))]
  · rw [boundRat_of_ge (Std.le_of_not_ge h), boundRat_of_le]
    rw [neg_le_iff, Rat.neg_neg]
    exact Std.le_of_not_ge h

theorem boundRat_ofSign_mul {b : Bool} {q : Rat} :
    fmt.boundRat (Rat.ofSign b * q) = Rat.ofSign b * fmt.boundRat q := by
  cases b <;> simp [boundRat_neg, Rat.neg_mul]

theorem lt_of_exp_lt_of_canonicalMantissa {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : fmt.CanonicalMantissa m₁ e₁) (h₂ : fmt.CanonicalMantissa m₂ e₂)
    (hlt : e₁ < e₂) : m₁ * (2 : Rat) ^ e₁ < m₂ * 2 ^ e₂ := by
  have h : m₁.size + e₁ ≤ (fmt.prec - 1 : Nat) + e₂ := by fexp_trivial
  rw [← Rat.zpow_le_zpow_iff_right (show 1 < 2 by decide), Rat.zpow_add (by decide),
    Rat.zpow_add (by decide)] at h
  apply Std.lt_of_lt_of_le _ (Rat.le_trans h _)
  · apply Rat.mul_lt_mul_of_pos_right _ (Rat.zpow_pos (by decide))
    exact_mod_cast Nat.lt_size_self m₁
  · apply Rat.mul_le_mul_of_nonneg_right _ (Rat.zpow_nonneg (by decide))
    norm_cast
    rw [← Nat.lt_size]
    fexp_trivial

theorem lt_def_of_canonicalMantissa {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : fmt.CanonicalMantissa m₁ e₁) (h₂ : fmt.CanonicalMantissa m₂ e₂) :
    e₁ ≤ e₂ ∧ (e₁ < e₂ ∨ m₁ < m₂) ↔ m₁ * (2 : Rat) ^ e₁ < m₂ * 2 ^ e₂ := by
  obtain h | rfl | h := Int.lt_trichotomy e₁ e₂
  · simp only [Int.le_of_lt h, h, true_or, and_self, true_iff]
    exact lt_of_exp_lt_of_canonicalMantissa h₁ h₂ h
  · simp only [Int.le_refl, Int.lt_irrefl, false_or, true_and, Rat.zpow_pos (show 0 < 2 by decide),
      mul_lt_mul_iff_of_pos_right, Rat.natCast_lt_natCast]
  · simp only [Int.not_le_of_gt h, false_and, false_iff, Rat.not_lt]
    exact Rat.le_of_lt (lt_of_exp_lt_of_canonicalMantissa h₂ h₁ h)

theorem mul_two_pow_inj_of_canonicalMantissa {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : fmt.CanonicalMantissa m₁ e₁) (h₂ : fmt.CanonicalMantissa m₂ e₂) :
    m₁ * (2 : Rat) ^ e₁ = m₂ * 2 ^ e₂ ↔ m₁ = m₂ ∧ e₁ = e₂ := by
  constructor
  · intro h
    have he₁ := (h ▸ mt (lt_of_exp_lt_of_canonicalMantissa h₁ h₂)) (Rat.not_lt.mpr Rat.le_refl)
    have he₂ := (h ▸ mt (lt_of_exp_lt_of_canonicalMantissa h₂ h₁)) (Rat.not_lt.mpr Rat.le_refl)
    cases Int.le_antisymm (Int.not_lt.mp he₁) (Int.not_lt.mp he₂)
    rw [Rat.mul_left_inj (Rat.ne_of_gt (Rat.zpow_pos (by decide)))] at h
    simpa only [and_true, Rat.natCast_inj] using h
  · rintro ⟨rfl, rfl⟩
    rfl

end FloatFormat

/-- Home-made `positivity` tactic -/
local syntax "pos" : tactic

macro_rules
  | `(tactic| pos) =>
    `(tactic| {
      with_reducible focus
      first
        | decide
        | assumption
        | apply Rat.pow_pos
        | apply Rat.pow_nonneg
        | apply Rat.zpow_pos
        | apply Rat.zpow_nonneg
        | apply Rat.mul_pos
        | apply Rat.mul_nonneg
        | apply Rat.div_pos
        | apply Rat.div_nonneg
        | apply Rat.natCast_nonneg
        | apply Rat.natCast_pos.mpr
        | apply Nat.pos_of_ne_zero; assumption
      all_goals pos
    })

namespace BinaryFloat

variable {fmt : FloatFormat}

open scoped FloatFormat

@[simp]
theorem toRat_nan : toRat (nan : BinaryFloat fmt) = 0 := rfl

theorem toRat_inf (s) :
    toRat (.inf s : BinaryFloat fmt) =
     Rat.ofSign s * 2 ^ fmt.maxExp := rfl

@[simp]
theorem toRat_inf_false : toRat (.inf false : BinaryFloat fmt) = 2 ^ fmt.maxExp := by
  simp [toRat_inf]

@[simp]
theorem toRat_inf_true : toRat (.inf true : BinaryFloat fmt) = -2 ^ fmt.maxExp := by
  simp [toRat_inf, Rat.neg_mul]

theorem toRat_finite {s m e h} :
    toRat (.finite s m e h : BinaryFloat fmt) =
     Rat.ofSign s * m * 2 ^ e := rfl

@[simp]
theorem toRat_finite_false {m e h} : toRat (.finite false m e h : BinaryFloat fmt) = m * 2 ^ e := by
  simp [toRat_finite]

@[simp]
theorem toRat_finite_true {m e h} : toRat (.finite true m e h : BinaryFloat fmt) = -(m * 2 ^ e) := by
  simp [toRat_finite, Rat.neg_mul]

@[simp]
theorem toRat_zero : toRat (.zero s : BinaryFloat fmt) = 0 := by
  simp [toRat, BinaryFloat.zero]

theorem toRat_lt_two_pow_maxExp {x : BinaryFloat fmt} (h : x.IsFinite) : toRat x < 2 ^ fmt.maxExp := by
  rcases h with ⟨s, m, e, h⟩
  have : m.size + e ≤ fmt.maxExp := by fexp_trivial
  rw [← Rat.zpow_le_zpow_iff_right (show 1 < 2 by decide)] at this
  apply Std.lt_of_lt_of_le _ this
  cases s
  · rw [toRat_finite_false, Rat.zpow_add (by decide)]
    apply Rat.mul_lt_mul_of_pos_right _ (by pos)
    exact_mod_cast m.lt_size_self
  · simp only [toRat_finite_true]
    exact Std.lt_of_le_of_lt (b := 0) (neg_le_iff.mp (Rat.mul_nonneg (by pos) (by pos))) (by pos)

theorem toRat_le_two_pow_maxExp (x : BinaryFloat fmt) : toRat x ≤ 2 ^ fmt.maxExp := by
  rcases x with _ | ⟨s⟩ | _
  · rw [toRat_nan]
    pos
  · cases s
    · simp [Rat.le_refl]
    · simp only [toRat_inf_true, Rat.neg_le_self_iff]; pos
  · exact Rat.le_of_lt (toRat_lt_two_pow_maxExp (IsFinite.finite ..))

theorem IsFinite.neg {x : BinaryFloat fmt} (h : IsFinite x) : IsFinite (-x) := by
  cases h
  apply IsFinite.finite

@[simp]
theorem neg_nan : -nan = (nan : BinaryFloat fmt) := rfl

@[simp]
theorem neg_inf : -inf s = (inf !s : BinaryFloat fmt) := rfl

@[simp]
theorem neg_finite : -finite s m e h = (finite (!s) m e h : BinaryFloat fmt) := rfl

@[simp]
protected theorem neg_zero : -.zero s = (.zero (!s) : BinaryFloat fmt) := rfl

@[simp]
theorem toRat_neg (x : BinaryFloat fmt) : (-x).toRat = -x.toRat := by
  rcases x with _ | ⟨s⟩ | ⟨s⟩
  · rfl
  · cases s <;> simp
  · cases s <;> simp

theorem neg_two_pow_maxExp_lt_toRat {x : BinaryFloat fmt} (h : x.IsFinite) :
    -2 ^ fmt.maxExp < toRat x := by
  rw [neg_lt_iff, ← toRat_neg]
  exact toRat_lt_two_pow_maxExp h.neg

theorem neg_two_pow_maxExp_le_toRat (x : BinaryFloat fmt) :
    -2 ^ fmt.maxExp ≤ toRat x := by
  rw [neg_le_iff, ← toRat_neg]
  exact (-x).toRat_le_two_pow_maxExp

theorem lt_def {a b : BinaryFloat fmt} : a < b ↔ a ≠ nan ∧ b ≠ nan ∧ a.toRat < b.toRat := by
  change a.blt b ↔ _
  unfold BinaryFloat.blt
  split
  · simp
  · simp
  · rename_i s s'
    have : -(2 : Rat) ^ fmt.maxExp < 2 ^ fmt.maxExp :=
      Std.lt_of_lt_of_le (b := 0) (neg_lt_iff.mp (Rat.pow_pos (by decide))) (by pos)
    cases s <;> cases s' <;> simp [Rat.lt_irrefl, this, Std.Asymm.asymm _ _ this]
  · rename_i s _ _ _ _
    cases s
    · simp [Rat.not_lt, toRat_le_two_pow_maxExp]
    · simp [neg_two_pow_maxExp_lt_toRat]
  · rename_i s
    cases s
    · simp [toRat_lt_two_pow_maxExp]
    · simp [Rat.not_lt, neg_two_pow_maxExp_le_toRat]
  · rename_i s₁ m₁ e₁ h₁ s₂ m₂ e₂ h₂
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    split
    · simp [fmt.lt_def_of_canonicalMantissa h₁.1 h₂.1]
    · simp only [Bool.false_eq_true, toRat_finite_false, toRat_finite_true, false_iff, Rat.not_lt]
      exact Rat.le_trans (b := 0) (neg_le_iff.mp (mul_nonneg (by pos) (by pos))) (by pos)
    · simp only [decide_eq_true_eq, toRat_finite_true, toRat_finite_false,
        Decidable.not_iff_comm (a := _ ∧ _), Rat.not_lt]
      constructor
      · intro h
        have h' : 0 ≤ m₂ * (2 : Rat) ^ e₂ := by pos
        have h'' : 0 ≤ m₁ * (2 : Rat) ^ e₁ := by pos
        have h''' : -(m₁ * (2 : Rat) ^ e₁) ≤ 0 := neg_le_iff.mpr <| by rw [Rat.neg_zero]; pos
        have heq₁ := Rat.le_antisymm (neg_nonneg_iff.mp (Rat.le_trans h' h)) h''
        have heq₂ := Rat.le_antisymm (Rat.le_trans h h''') h'
        simp_all [Rat.mul_eq_zero, Rat.ne_of_gt (Rat.zpow_pos (show 0 < 2 by decide))]
      · intro ⟨h₁, h₂⟩
        simp [h₁, h₂, Rat.le_refl]
    · simp [fmt.lt_def_of_canonicalMantissa h₂.1 h₁.1, neg_lt_iff (a := (m₁ : Rat) * _)]

theorem beq_def {a b : BinaryFloat fmt} : a == b ↔ a ≠ nan ∧ b ≠ nan ∧ a.toRat = b.toRat := by
  change a.beq b ↔ _
  unfold BinaryFloat.beq
  split
  · simp
  · simp
  · rename_i s s'
    have : -(2 : Rat) ^ fmt.maxExp ≠ 2 ^ fmt.maxExp :=
      Rat.ne_of_lt <| Std.lt_of_lt_of_le (b := 0) (neg_lt_iff.mp (Rat.pow_pos (by decide))) (by pos)
    cases s <;> cases s' <;> simp [this, this.symm]
  · rename_i s _ _ _ _
    cases s
    · simp [Rat.ne_of_gt, toRat_lt_two_pow_maxExp]
    · simp [Rat.ne_of_lt, neg_two_pow_maxExp_lt_toRat]
  · rename_i s
    cases s
    · simp [Rat.ne_of_lt, toRat_lt_two_pow_maxExp]
    · simp [Rat.ne_of_gt, neg_two_pow_maxExp_lt_toRat]
  · rename_i s₁ m₁ e₁ h₁ s₂ m₂ e₂ h₂
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, ne_eq, reduceCtorEq,
      not_false_eq_true, true_and]
    by_cases hm : m₁ = 0 ∧ m₂ = 0
    · simp [hm, toRat_finite]
    · simp only [hm, false_or, toRat_finite]
      by_cases hs : s₁ = s₂
      · simp only [hs, true_and, Rat.mul_assoc (Rat.ofSign _), Rat.mul_comm (Rat.ofSign _) (_ * _),
          Rat.mul_left_inj (Rat.ofSign_ne_zero _), fmt.mul_two_pow_inj_of_canonicalMantissa h₁.1 h₂.1]
      · replace hs := Bool.eq_not_of_ne hs
        simp only [hs, Bool.not_eq_eq_eq_not, Bool.eq_not_self, false_and, Rat.ofSign_not,
          Rat.neg_mul (Rat.ofSign _), ← Rat.mul_neg, Rat.mul_assoc (Rat.ofSign _), false_iff, ne_eq,
          Rat.mul_comm (Rat.ofSign _) (_ * _), Rat.mul_left_inj (Rat.ofSign_ne_zero _)]
        intro h
        rw [Rat.neg_mul] at h
        have h' : 0 ≤ m₁ * (2 : Rat) ^ e₁ := by pos
        have h'' : 0 ≤ m₂ * (2 : Rat) ^ e₂ := by pos
        have heq₁ := Rat.le_antisymm (h ▸ neg_le_iff.mp h') h''
        have heq₂ := Rat.le_antisymm (neg_nonneg_iff.mp (h ▸ h'')) h'
        simp only [Rat.mul_eq_zero, Rat.natCast_eq_zero_iff,
          Rat.ne_of_gt (Rat.zpow_pos (show 0 < 2 by decide)), or_false] at heq₁ heq₂
        exact absurd ⟨heq₂, heq₁⟩ hm

theorem le_iff_lt_or_beq {a b : BinaryFloat fmt} : a ≤ b ↔ a < b ∨ a == b := by
  change a.ble b ↔ a.blt b ∨ a.beq b
  simp [BinaryFloat.ble]

theorem le_def {a b : BinaryFloat fmt} : a ≤ b ↔ a ≠ nan ∧ b ≠ nan ∧ a.toRat ≤ b.toRat := by
  rw [le_iff_lt_or_beq, lt_def, beq_def, ← and_assoc, ← and_assoc, ← and_assoc, ← and_or_left,
    Std.le_iff_lt_or_eq]

theorem toRat_incMantissa_finite (s m e h) :
    (incMantissa (.finite s m e h : BinaryFloat fmt)).toRat =
      Rat.ofSign s * (m + 1) * 2 ^ e := by
  simp only [incMantissa]
  split
  · simp [toRat]
  have : m < 2 ^ fmt.prec := by rw [← Nat.size_le]; fexp_trivial
  have hm : m + 1 = 2 ^ fmt.prec := by omega
  split
  · simp only [toRat, ne_eq, Rat.ofNat_eq_ofNat, reduceCtorEq, not_false_eq_true, Rat.zpow_add_one]
    rw [Rat.mul_comm _ 2, ← Rat.mul_assoc, Rat.mul_assoc _ _ 2]
    congr 2; norm_cast
    simp [hm, Nat.shiftLeft_eq, ← Nat.pow_succ, Nat.sub_one_add_one_eq_of_pos fmt.prec_pos]
  · simp only [toRat, Rat.mul_assoc]
    congr 1
    have he : e = (fmt.maxExp - fmt.prec : Nat) := by fexp_trivial
    simp only [he, Rat.zpow_natCast]
    norm_cast
    simp [hm, ← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt fmt.prec_lt_maxExp)]

theorem neg_incMantissa (x : BinaryFloat fmt) : -x.incMantissa = (-x).incMantissa := by
  simp only [incMantissa]
  split <;> simp [apply_dite (- · : BinaryFloat fmt → _)]

@[simp]
theorem binaryRoundAux_zero {s : Bool} {e : Int} {exact : Bool}
    (h : e < fmt.fexp (0 + e)) :
    binaryRoundAux s 0 e exact h = .zero s := by
  rw [binaryRoundAux]
  split
  · fexp_trivial
  · have : fmt.fexp e = fmt.minExp := by fexp_trivial
    simp [BinaryFloat.zero, this]

theorem toRat_binaryRoundAux_false {m : Nat} {e : Int} {exact : Bool}
    (h : e < fmt.fexp (m.size + e)) {q : Rat}
    (hme₁ : m * 2 ^ e ≤ q) (hme₂ : q < (m + 1) * 2 ^ e)
    (hexact : exact ↔ q = m * 2 ^ e) :
    toRat (binaryRoundAux false m e exact h) = fmt.boundRat (fmt.roundRatEven q) := by
  by_cases hmz : m = 0
  · subst hmz
    simp only [Rat.natCast_ofNat, Rat.zero_mul, Rat.zero_add, Rat.one_mul, binaryRoundAux_zero,
      BinaryFloat.zero, toRat_finite_false] at hme₁ hme₂ ⊢
    by_cases hqz : 0 = q
    · simp [← hqz]
    have := (Rat.log2_lt (Rat.lt_of_le_of_ne hme₁ hqz)).mpr hme₂
    simp only [FloatFormat.roundRatEven]
    rw [Rat.roundEven_of_gt_of_lt (i := 0)]
    · simp
    · exact Std.lt_of_lt_of_le (b := 0) (by decide +kernel) (by pos)
    · simp only [Rat.div_mul, Rat.intCast_ofNat, Rat.zero_mul, Rat.zero_add]
      rw [Rat.div_lt_iff' (by pos), Rat.div_def, Rat.mul_one]
      rw [← Rat.zpow_sub_one (by decide), ← Rat.log2_lt (Rat.lt_of_le_of_ne hme₁ hqz)]
      fexp_trivial
  have hmeqfloor : m = (q / 2 ^ e).floor := by
    rw [eq_comm, Rat.floor_eq_iff, Rat.le_div_iff (by pos), Rat.div_lt_iff (by pos)]
    exact ⟨hme₁, hme₂⟩
  have qpos : 0 < q := Std.lt_of_lt_of_le (by pos) hme₁
  have : m.size ≠ 0 := mt Nat.size_eq_zero_iff.mp hmz
  have log2q : m.size + e = q.log2 + 1 := by
    rw [← Int.sub_eq_iff_eq_add, eq_comm, Rat.log2_eq_iff qpos, Int.sub_add_cancel,
      show m.size + e - 1 = (m.size - 1 : Nat) + e by omega, Rat.zpow_add (by decide),
      Rat.zpow_add (by decide)]
    constructor
    · apply Rat.le_trans (Rat.mul_le_mul_of_nonneg_right _ (by pos)) hme₁
      exact_mod_cast Nat.size_self_le' hmz
    · apply Std.lt_of_lt_of_le hme₂ (Rat.mul_le_mul_of_nonneg_right _ (by pos))
      exact_mod_cast m.lt_size_self
  rw [binaryRoundAux]
  have : fmt.maxExp - fmt.prec < fmt.fexp (m.size + e) ↔
      fmt.maxExp ≤ q.log2 := by fexp_trivial
  simp -zeta only [this, Rat.le_log2 qpos]
  split
  · simp only [toRat, Rat.ofSign_false, Rat.one_mul]
    rw [FloatFormat.boundRat_of_ge]
    rw [← fmt.roundRatEven_two_pow_eq_self fmt.minExp_le_maxExp]
    exact fmt.roundRatEven_mono ‹_›
  · extract_lets shift val hcanon res b exact' addOne
    rw [FloatFormat.boundRat_of_le_of_ge ?le ?ge]
    case le =>
      rw [← fmt.roundRatEven_two_pow_eq_self fmt.minExp_le_maxExp]
      exact fmt.roundRatEven_mono (Std.le_of_not_ge ‹_›)
    case ge =>
      exact Rat.le_trans (neg_le_iff.mp (Rat.pow_nonneg (by decide)))
        (fmt.roundRatEven_nonneg (Rat.le_of_lt qpos))
    let (eq := ratVal_eq) ratVal := q / 2 ^ fmt.fexp (q.log2 + 1)
    rw [log2q] at h
    have val_eq : val = ratVal.floor := by
      simp only [val, ratVal, Nat.shiftRight_eq_div_pow, shift, Int.natCast_ediv,
        ← Rat.floor_div_natCast, Rat.natCast_pow, Rat.natCast_ofNat, ← Rat.zpow_natCast, hmeqfloor]
      rw [Int.toNat_of_nonneg (by omega), Rat.div_div, ← Rat.zpow_add (by decide), log2q]
      congr; omega
    have mdiv_eq : m / 2 ^ (shift - 1) = (ratVal * 2).floor := by
      simp only [hmeqfloor, Int.zero_le_ofNat, ← Rat.floor_div_intCast_of_nonneg (Int.pow_nonneg _),
        Rat.intCast_pow, Rat.intCast_ofNat, ← Rat.zpow_natCast, Rat.div_div, ne_eq,
        Rat.ofNat_eq_ofNat, reduceCtorEq, not_false_eq_true, ← Rat.zpow_add, Rat.div_mul,
        ← Rat.zpow_sub_one', shift, ratVal, log2q]
      congr 3; omega
    have exact'_iff : exact' ↔ (ratVal * 2).floor = ratVal * 2 := by
      simp only [log2q, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod,
        Bool.and_eq_true, hexact, beq_iff_eq, ← Int.natCast_inj, Int.natCast_emod, Int.natCast_pow,
        Int.cast_ofNat_Int, exact', shift, hmeqfloor, ratVal]
      simp only [← Rat.intCast_inj, Rat.intCast_natCast] at hmeqfloor
      rw [hmeqfloor, ← Rat.div_eq_iff (Rat.ne_of_gt (by pos)), eq_comm]
      simp only [Rat.div_mul, ne_eq, Rat.ofNat_eq_ofNat, reduceCtorEq, not_false_eq_true,
        ← Rat.zpow_sub_one']
      rw [iff_comm, Rat.floor_eq_self_iff_floor_mul_eq_self_and_dvd _ (2 ^ (shift - 1))
        (Nat.ne_of_gt (Nat.two_pow_pos _ ))]
      simp only [Rat.natCast_pow, Rat.natCast_ofNat, ← Rat.zpow_natCast, Rat.div_mul, ne_eq,
        Rat.ofNat_eq_ofNat, reduceCtorEq, not_false_eq_true, ← Rat.zpow_sub, Int.natCast_pow,
        Int.cast_ofNat_Int, Int.dvd_iff_emod_eq_zero]
      have : fmt.fexp (q.log2 + 1) - 1 - ↑(shift - 1) = e := by fexp_trivial
      simp only [this]
      simp [shift, log2q]
    have addOne_iff : addOne ↔ (ratVal * 2).floor % 2 = 1 ∧
        (↑(ratVal * 2).floor ≠ ratVal * 2 ∨ ratVal.floor % 2 = 1) := by
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        ← Bool.not_eq_true, exact'_iff, beq_iff_eq, ne_eq, ← val_eq, addOne, b]
      norm_cast
      simp [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, ← Int.natCast_inj, mdiv_eq]
    rw [FloatFormat.roundRatEven, ← ratVal_eq, Rat.roundEven_eq_floor]
    simp only [← addOne_iff]
    split
    · simp [log2q, ← val_eq, res, Rat.intCast_natCast, toRat_incMantissa_finite]
    · simp [log2q, ← val_eq, res, Rat.intCast_natCast, toRat_finite]

theorem sign_binaryRoundAux {s : Bool} {m : Nat} {e : Int} {exact : Bool}
    (h : e < fmt.fexp (m.size + e)) :
    (binaryRoundAux s m e exact h).sign = s := by
  simp only [binaryRoundAux]
  split
  · rfl
  · split
    · rw [incMantissa]
      · split
        · rfl
        · split <;> rfl
    · rfl

theorem binaryRoundAux_not {s : Bool} {m : Nat} {e : Int} {exact : Bool}
    (h : e < fmt.fexp (m.size + e)) :
    binaryRoundAux (!s) m e exact h = -binaryRoundAux s m e exact h := by
  simp only [binaryRoundAux]
  split
  · simp
  · split <;> simp [neg_incMantissa]

theorem binaryRoundAux_ne_nan {m : Nat} {e : Int} {exact : Bool}
    (h : e < fmt.fexp (m.size + e)) :
    binaryRoundAux s m e exact h ≠ nan := by
  simp only [binaryRoundAux]
  split
  · nofun
  · split
    · rw [incMantissa]
      split
      · nofun
      split <;> nofun
    · nofun

theorem toRat_binaryRoundAux {s : Bool} {m : Nat} {e : Int} {exact : Bool}
    (h : e < fmt.fexp (m.size + e)) {q : Rat}
    (hme₁ : m * 2 ^ e ≤ q) (hme₂ : q < (m + 1) * 2 ^ e)
    (hexact : exact ↔ q = m * 2 ^ e) :
    toRat (binaryRoundAux s m e exact h) = Rat.ofSign s * fmt.boundRat (fmt.roundRatEven q) := by
  cases s
  · simp [toRat_binaryRoundAux_false h hme₁ hme₂ hexact]
  · rw [← Bool.not_false, binaryRoundAux_not]
    simp [toRat_binaryRoundAux_false h hme₁ hme₂ hexact, Rat.neg_mul]

theorem toRat_binaryRound (s : Bool) (m : Nat) (e : Int) :
    toRat (binaryRound s m e : BinaryFloat fmt) =
      Rat.ofSign s * fmt.boundRat (fmt.roundRatEven (m * 2 ^ e)) := by
  rw [binaryRound]
  split
  · simp_all
  split
  · apply toRat_binaryRoundAux
    · exact Rat.le_refl
    · simp only [Rat.add_mul, Rat.one_mul]
      conv => lhs; apply (Rat.add_zero _).symm
      rw [Rat.add_lt_add_iff_left]
      pos
    · simp
  · rw [toRat_binaryRoundAux (q := (m <<< (fmt.prec + 1)) * 2 ^ (e - (fmt.prec + 1)))]
    · have : fmt.prec + 1 + (e - (fmt.prec + 1)) = e := by omega
      simp [Nat.shiftLeft_eq, Rat.mul_assoc, ← Rat.zpow_add, ← Rat.zpow_natCast, this]
    · exact Rat.le_refl
    · simp only [Rat.add_mul, Rat.one_mul]
      conv => lhs; apply (Rat.add_zero _).symm
      rw [Rat.add_lt_add_iff_left]
      pos
    · simp

theorem toRat_binaryNormalize (m : Int) (e : Int) :
    toRat (binaryNormalize m e : BinaryFloat fmt) =
      fmt.boundRat (fmt.roundRatEven (m * 2 ^ e)) := by
  cases m
  · simp [binaryNormalize, toRat_binaryRound, Rat.intCast_natCast]
  · have (a : Nat) : Int.natAbs (a + 1) = a + 1 := rfl
    simp [binaryNormalize, toRat_binaryRound, Int.negSucc_eq, Rat.neg_mul,
      Rat.intCast_natCast, fmt.boundRat_neg, fmt.roundRatEven_neg, this]

theorem toRat_ofNat (n : Nat) :
    toRat (BinaryFloat.ofNat n : BinaryFloat fmt) = fmt.boundRat (fmt.roundRatEven n) := by
  simp [BinaryFloat.ofNat, toRat_binaryRound]

theorem toRat_ofInt (n : Int) :
    toRat (BinaryFloat.ofInt n : BinaryFloat fmt) = fmt.boundRat (fmt.roundRatEven n) := by
  simp [BinaryFloat.ofInt, toRat_binaryNormalize]

theorem toRat_mul {a b : BinaryFloat fmt} (ha : a.IsFinite) (hb : b.IsFinite) :
    (a * b).toRat = fmt.boundRat (fmt.roundRatEven (a.toRat * b.toRat)) := by
  cases ha <;> cases hb
  change (BinaryFloat.mul _ _).toRat = _
  simp only [BinaryFloat.mul, toRat_finite]
  split
  · rename_i h
    simp only [Nat.mul_eq_zero] at h
    obtain h | h := h <;> simp [h]
  · rename_i s₁ m₁ e₁ h₁ s₂ m₂ e₂ h₂ h
    rw [toRat_binaryRoundAux (q := (m₁ * m₂ * 2 : Nat) * 2 ^ (e₁ + e₂ - 1))]
    · simp only [Rat.natCast_mul, Rat.natCast_ofNat, ne_eq, Rat.ofNat_eq_ofNat, reduceCtorEq,
        not_false_eq_true, Rat.zpow_sub_one', Rat.mul_right_comm _ 2, ← Rat.mul_div_assoc,
        Rat.div_mul_cancel]
      have : Rat.ofSign s₁ * ↑m₁ * 2 ^ e₁ * (Rat.ofSign s₂ * ↑m₂ * 2 ^ e₂) =
          (Rat.ofSign s₁ * Rat.ofSign s₂) * ((m₁ * m₂) * (2 ^ e₁ * 2 ^ e₂)) := by ac_rfl
      rw [this, ← Rat.ofSign_xor, fmt.roundRatEven_ofSign_mul, fmt.boundRat_ofSign_mul,
        ← Rat.zpow_add (by decide)]
    · simp only [Rat.natCast_mul, Rat.natCast_ofNat, Rat.le_refl]
    · simp only [Rat.natCast_mul, Rat.natCast_ofNat, Rat.add_mul, Rat.one_mul]
      conv => lhs; apply (Rat.add_zero _).symm
      rw [Rat.add_lt_add_iff_left]
      pos
    · simp

end BinaryFloat

end Std
