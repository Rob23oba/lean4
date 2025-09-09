/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Init.Data.Rat.Lemmas
public import Init.Grind

@[expose] public section

open Lean.Grind.AddCommGroup
open Lean.Grind.OrderedAdd
open Lean.Grind.OrderedRing
open Lean.Grind.Field.IsOrdered

def Nat.size (n : Nat) : Nat :=
  if n = 0 then 0 else n.log2 + 1

@[simp]
theorem Nat.size_le {a b : Nat} : a.size ≤ b ↔ a < 2 ^ b := by
  rw [size]
  split
  · simp [Nat.pow_pos, *]
  · simp [Nat.add_one_le_iff, Nat.log2_lt, *]

theorem Nat.lt_size_self (a : Nat) : a < 2 ^ a.size := Nat.size_le.mp (Nat.le_refl _)

@[simp]
theorem Nat.lt_size {a b : Nat} : a < b.size ↔ 2 ^ a ≤ b := by
  rw [← Decidable.not_iff_not]
  simp

@[simp] theorem Nat.size_zero : (0).size = 0 := rfl
@[simp] theorem Nat.size_one : (1).size = 1 := rfl
@[simp] theorem Nat.size_two : (2).size = 2 := rfl

theorem Nat.size_eq_iff {a b : Nat} : a.size = b ↔ 2 ^ b / 2 ≤ a ∧ a < 2 ^ b := by
  simp only [Nat.le_antisymm_iff, size_le, and_comm, and_congr_left_iff]
  intro h
  rcases b with _ | b
  · simp
  · simp [Nat.add_one_le_iff, Nat.pow_succ]

@[simp]
theorem Nat.size_eq_zero_iff {a : Nat} : a.size = 0 ↔ a = 0 := by
  simp [Nat.size_eq_iff]

theorem Nat.size_self_le (a : Nat) : 2 ^ a.size / 2 ≤ a :=
  (Nat.size_eq_iff.mp rfl).1

@[simp]
theorem Nat.size_shiftRight {a b : Nat} : (a >>> b).size = a.size - b := by
  rw [Nat.size_eq_iff, Nat.shiftRight_eq_div_pow]
  by_cases h : b ≤ a.size
  · rw [← Nat.pow_div h (by decide), Nat.div_div_eq_div_mul, Nat.mul_comm,
      ← Nat.div_div_eq_div_mul]
    constructor
    · exact Nat.div_le_div_right a.size_self_le
    · apply Nat.div_lt_div_of_lt_of_dvd
      · exact pow_dvd_pow_iff_le_right'.mpr h
      · exact a.lt_size_self
  · simpa [Nat.sub_eq_zero_of_le (Nat.le_of_not_le h)] using Nat.le_of_not_le h

theorem Nat.size_shiftLeft {a b : Nat} (h : a ≠ 0) : (a <<< b).size = a.size + b := by
  rw [Nat.size_eq_iff, Nat.shiftLeft_eq, Nat.pow_add]
  constructor
  · rw [Nat.mul_comm, Nat.mul_div_assoc, Nat.mul_comm]
    · exact Nat.mul_le_mul_right _ a.size_self_le
    · rw (occs := .pos [1]) [← Nat.pow_one 2]
      apply Nat.pow_dvd_pow
      exact Nat.pos_of_ne_zero (mt a.size_eq_zero_iff.mp h)
  · exact Nat.mul_lt_mul_of_pos_right a.lt_size_self b.two_pow_pos

def Rat.roundEven (q : Rat) : Int :=
  if q.den = 1 then q.num else
  if q.den = 2 then (q.num + 1) / 4 * 2 else
  (q.num * 2 / q.den + 1) / 2

protected def Rat.abs (q : Rat) : Rat :=
  ⟨q.num.natAbs, q.den, q.den_nz, q.reduced⟩

protected theorem Rat.num_abs (q : Rat) : q.abs.num = q.num.natAbs := rfl
protected theorem Rat.den_abs (q : Rat) : q.abs.den = q.den := rfl

protected theorem Rat.abs_def (q : Rat) : q.abs = if 0 ≤ q then q else -q := by
  simp only [← Rat.num_nonneg, Neg.neg]
  rcases q with ⟨n, d, nz, r⟩
  simp only [Rat.abs, Rat.neg]
  split <;> (simp; omega)

protected theorem Rat.abs_of_nonneg {q : Rat} (h : 0 ≤ q) : q.abs = q := by
  simp [Rat.abs_def, *]

protected theorem Rat.abs_of_nonpos {q : Rat} (h : q ≤ 0) : q.abs = -q := by
  simp only [Rat.abs_def, ite_eq_right_iff]
  intro h'
  cases Rat.le_antisymm h h'; rfl

@[simp]
protected theorem Rat.neg_zero : -0 = (0 : Rat) := rfl

@[simp]
protected theorem Rat.neg_neg (x : Rat) : - -x = x :=
  neg_neg x

@[simp]
protected theorem Rat.abs_neg (q : Rat) : (-q).abs = q.abs := by
  simp [Rat.abs]

@[simp]
protected theorem Rat.abs_abs (q : Rat) : q.abs.abs = q.abs := by
  simp [Rat.abs]

@[simp]
theorem Rat.roundEven_intCast (i : Int) : (i : Rat).roundEven = i := rfl

@[simp]
theorem Rat.roundEven_natCast (i : Nat) : (i : Rat).roundEven = i := rfl

@[simp]
theorem Rat.roundEven_ofNat (n : Nat) : (no_index (OfNat.ofNat n) : Rat).roundEven = OfNat.ofNat n := rfl

protected theorem Rat.zero_sub (a : Rat) : 0 - a = -a := by
  simp [Rat.sub_eq_add_neg, Rat.zero_add]

protected theorem Rat.mul_div_comm (a b c : Rat) : a * b / c = a / c * b := by
  rw [Rat.div_def, Rat.div_def, Rat.mul_assoc, Rat.mul_assoc, Rat.mul_comm b]

protected theorem Rat.mul_div_assoc (a b c : Rat) : a * b / c = a * (b / c) := by
  rw [Rat.div_def, Rat.div_def, Rat.mul_assoc]

protected theorem Rat.sub_mul (a b c : Rat) : (a - b) * c = a * c - b * c := by
  simp [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul]

protected theorem Rat.add_div (a b c : Rat) : (a + b) / c = a / c + b / c := by
  simp [Rat.div_def, Rat.add_mul]

protected theorem Rat.sub_div (a b c : Rat) : (a - b) / c = a / c - b / c := by
  simp [Rat.div_def, Rat.sub_mul]

@[simp]
protected theorem Rat.inv_one : (1 : Rat)⁻¹ = 1 := by with_unfolding_all rfl

@[simp]
protected theorem Rat.div_one (a : Rat) : a / 1 = a := by
  simp [Rat.div_def]

protected theorem Rat.add_right_comm (a b c : Rat) : a + b + c = a + c + b := by
  rw [Rat.add_assoc, Rat.add_comm b, ← Rat.add_assoc]

protected theorem Rat.add_sub_cancel (a b : Rat) : a + b - b = a := by
  simp [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]

protected theorem Rat.sub_add_cancel (a b : Rat) : a - b + b = a := by
  simp [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero]

protected theorem Rat.add_lt_add_iff_left {a b c : Rat} : a + b < a + c ↔ b < c := by
  rw [← Decidable.not_iff_not, Rat.not_lt, Rat.not_lt, Rat.add_le_add_left]

protected theorem Rat.add_lt_add_iff_right {a b c : Rat} : a + c < b + c ↔ a < b := by
  rw [← Decidable.not_iff_not, Rat.not_lt, Rat.not_lt, Rat.add_le_add_right]

protected theorem Rat.sub_lt_iff_lt_add {a b c : Rat} : a - b < c ↔ a < c + b := by
  simpa [Rat.sub_add_cancel] using (@Rat.add_lt_add_iff_right (a - b) c b).symm

protected theorem Rat.sub_le_iff_le_add {a b c : Rat} : a - b ≤ c ↔ a ≤ c + b := by
  simpa [Rat.sub_add_cancel] using (@Rat.add_le_add_right (a - b) c b).symm

protected theorem Rat.sub_eq_iff_eq_add {a b c : Rat} : a - b = c ↔ a = c + b :=
  ⟨(by simpa only [Rat.sub_add_cancel] using congrArg (· + b) ·),
    (by simpa only [Rat.add_sub_cancel] using congrArg (· - b) ·)⟩

protected theorem Rat.lt_sub_iff_add_lt {a b c : Rat} : a < b - c ↔ a + c < b := by
  simpa [Rat.sub_add_cancel] using (@Rat.add_lt_add_iff_right a (b - c) c).symm

protected theorem Rat.le_sub_iff_add_le {a b c : Rat} : a ≤ b - c ↔ a + c ≤ b := by
  simpa [Rat.sub_add_cancel] using (@Rat.add_le_add_right a (b - c) c).symm

protected theorem Rat.eq_sub_iff_add_eq {a b c : Rat} : a = b - c ↔ a + c = b :=
  ⟨(by simpa only [Rat.sub_add_cancel] using congrArg (· + c) ·),
    (by simpa only [Rat.add_sub_cancel] using congrArg (· - c) ·)⟩

protected theorem Rat.div_le_iff {a b c : Rat} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  simpa [Rat.not_lt] using not_congr (Rat.lt_div_iff hb)

protected theorem Rat.div_le_iff' {a b c : Rat} (hb : 0 < b) : a / b ≤ c ↔ a ≤ b * c := by
  simpa [Rat.not_lt] using not_congr (Rat.lt_div_iff' hb)

protected theorem Rat.div_eq_iff {a b c : Rat} (hb : b ≠ 0) : a / b = c ↔ a = c * b :=
  ⟨(by simpa only [Rat.div_mul_cancel hb] using congrArg (· * b) ·),
    (by simpa only [Rat.mul_div_cancel hb] using congrArg (· / b) ·)⟩

protected theorem Rat.div_eq_iff' {a b c : Rat} (hb : b ≠ 0) : a / b = c ↔ a = b * c := by
  rw [Rat.div_eq_iff hb, Rat.mul_comm]

protected theorem Rat.le_div_iff {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  simpa [Rat.not_lt] using not_congr (Rat.div_lt_iff hc)

protected theorem Rat.le_div_iff' {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ c * a ≤ b := by
  simpa [Rat.not_lt] using not_congr (Rat.div_lt_iff' hc)

@[simp]
theorem Rat.floor_mkRat (n : Int) (d : Nat) : (mkRat n d).floor = n / d := by
  by_cases h : d = 0
  · simp [h, Rat.floor]
  cases h' : mkRat n d
  obtain ⟨m, hm, rfl, rfl⟩ := Rat.mkRat_num_den h h'
  simp [Nat.pos_of_ne_zero hm, Rat.floor_def]

theorem Rat.roundEven_intCast_add_half (i : Int) :
    (i + 1 / 2 : Rat).roundEven = if 2 ∣ i then i else i + 1 := by
  have : (i * 2 + 1).gcd (2 : Int) = 1 := by simp
  have : (i + 1 / 2) = Rat.mk' (i * 2 + 1) 2 (by simp) this := by
    simp [Rat.mk'_eq_divInt, Rat.divInt_eq_div, Rat.add_div, Rat.mul_div_cancel]
  simp only [roundEven, this, Nat.succ_ne_self, ↓reduceIte]
  omega

theorem Nat.coprime_two_right {n : Nat} : n.Coprime 2 ↔ ¬2 ∣ n := by
  simp only [coprime_iff_gcd_eq_one]
  rw [← Nat.div_add_mod n 2]
  cases Nat.mod_two_eq_zero_or_one n <;> simp_all [Nat.dvd_iff_mod_eq_zero]

theorem Rat.roundEven_of_gt_of_lt {i : Int} {q : Rat}
    (h : i * 2 - 1 < q * 2) (h' : q * 2 < i * 2 + 1) :
    q.roundEven = i := by
  unfold roundEven
  obtain ⟨n, d, nz, r⟩ := q
  simp only [mk'_eq_divInt, divInt_eq_div, ← Rat.mul_div_comm, intCast_pos, Int.natCast_pos,
    Nat.pos_of_ne_zero nz, Rat.lt_div_iff, Rat.div_lt_iff] at h h'
  norm_cast at h h'
  dsimp only
  split
  · cases ‹d = 1›
    omega
  · split
    · cases ‹d = 2›
      have := Nat.coprime_two_right.mp r
      omega
    · have := (Int.ediv_eq_iff_of_pos (mod_cast Nat.pos_of_ne_zero nz)).mp (rfl : n * 2 / d = _)
      generalize n * 2 / d = a at this
      rw (occs := .pos [3]) [← Int.one_mul d] at this
      rw [← Int.add_mul] at this
      replace h := Int.lt_trans h this.2
      replace h' := Int.lt_of_le_of_lt this.1 h'
      rw [Int.mul_lt_mul_right (mod_cast Nat.pos_of_ne_zero nz)] at h h'
      omega

theorem Int.sub_add (a b c : Int) : a - b + c = a - (b - c) := by omega

theorem Rat.roundEven_cases (q : Rat) :
    ∃ i : Int, q * 2 = i * 2 + 1 ∨ i * 2 - 1 < q * 2 ∧ q * 2 < i * 2 + 1 := by
  rcases q with ⟨n, d, nz, r⟩
  simp only [mk'_eq_divInt, divInt_eq_div, ne_eq, intCast_eq_zero_iff, Int.natCast_eq_zero, nz,
    not_false_eq_true, Rat.div_eq_iff, ← Rat.mul_div_comm, intCast_pos, Int.natCast_pos,
    Nat.pos_of_ne_zero nz, Rat.lt_div_iff, Rat.div_lt_iff]
  norm_cast
  rw [exists_or, Classical.or_iff_not_imp_left, not_exists]
  intro h
  exists (n * 2 / d + 1) / 2
  constructor
  · apply Std.lt_of_le_of_ne
    · apply Int.mul_le_of_le_ediv (mod_cast Nat.pos_of_ne_zero nz)
      omega
    · symm
      simpa [Int.sub_mul, Int.sub_add] using h ((n * 2 / d + 1) / 2 - 1)
  · apply Int.lt_mul_of_ediv_lt (mod_cast Nat.pos_of_ne_zero nz)
    omega

theorem Rat.roundEven_le (a : Rat) : a.roundEven ≤ a + 1 / 2 := by
  obtain ⟨i, h | h⟩ := a.roundEven_cases
  · rw [eq_comm, ← Rat.div_eq_iff (by decide), Rat.add_div, Rat.mul_div_cancel (by decide)] at h
    rw [← h, Rat.roundEven_intCast_add_half, Rat.add_assoc,
      show (1 : Rat) / 2 + 1 / 2 = 1 by decide +kernel]
    norm_cast
    omega
  · rw [Rat.roundEven_of_gt_of_lt h.1 h.2]
    rw [Rat.sub_lt_iff_lt_add, ← Rat.lt_div_iff (by decide), Rat.add_div,
      Rat.mul_div_cancel (by decide)] at h
    exact Rat.le_of_lt h.1

theorem Rat.roundEven_mul_two_le (a : Rat) : a.roundEven * 2 ≤ a * 2 + 1 := by
  simpa [Rat.add_mul, Rat.div_mul_cancel] using
    Rat.mul_le_mul_of_nonneg_right a.roundEven_le (show 0 ≤ 2 by decide)

theorem Rat.le_roundEven (a : Rat) : a - 1 / 2 ≤ a.roundEven := by
  obtain ⟨i, h | h⟩ := a.roundEven_cases
  · rw [eq_comm, ← Rat.div_eq_iff (by decide), Rat.add_div, Rat.mul_div_cancel (by decide)] at h
    rw [← h, Rat.roundEven_intCast_add_half, Rat.add_sub_cancel]
    norm_cast
    omega
  · rw [Rat.roundEven_of_gt_of_lt h.1 h.2]
    rw [← Rat.sub_lt_iff_lt_add, ← Rat.div_lt_iff (c := i) (by decide), Rat.sub_div,
      Rat.mul_div_cancel (by decide)] at h
    exact Rat.le_of_lt h.2

theorem Rat.le_roundEven_mul_two (a : Rat) : a * 2 - 1 ≤ a.roundEven * 2 := by
  simpa [Rat.sub_mul, Rat.div_mul_cancel] using
    Rat.mul_le_mul_of_nonneg_right a.le_roundEven (show 0 ≤ 2 by decide)

@[simp]
theorem Rat.roundEven_neg (a : Rat) : (-a).roundEven = -a.roundEven := by
  obtain ⟨i, h | h⟩ := a.roundEven_cases
  · rw [eq_comm, ← Rat.div_eq_iff (by decide), Rat.add_div, Rat.mul_div_cancel (by decide)] at h
    rw [← h, Rat.roundEven_intCast_add_half]
    have : -(i + (1 : Rat) / 2) = (-i - 1 : Int) + 1 / 2 := by
      simp [neg_add, Rat.sub_eq_add_neg, Rat.add_assoc,
        show -1 + (1 : Rat) / 2 = -(1 / 2) by decide +kernel]
    rw [this, Rat.roundEven_intCast_add_half]
    omega
  · rw [Rat.roundEven_of_gt_of_lt h.1 h.2]
    rw [Rat.roundEven_of_gt_of_lt (i := -i)]
    · rw [Rat.neg_mul, lt_neg_iff]
      simp [Rat.sub_eq_add_neg, neg_add, Rat.neg_mul, h]
    · rw [Rat.neg_mul, neg_lt_iff]
      simp_all [Rat.sub_eq_add_neg, neg_add, Rat.neg_mul]

theorem Rat.roundEven_mono {a b : Rat} (h : a ≤ b) : a.roundEven ≤ b.roundEven := by
  apply Decidable.byContradiction fun h' => ?_
  rw [Int.not_le] at h'
  replace h := Rat.lt_of_le_of_ne h (by intro; simp_all)
  obtain ⟨n, hn⟩ := h'.dest
  have h₁ := a.roundEven_le
  have h₂ := b.le_roundEven
  rw [← hn] at h₁
  simp only [Nat.succ_eq_add_one, Int.natCast_add, Int.cast_ofNat_Int, Rat.intCast_add,
    intCast_ofNat] at h₁
  apply absurd h
  rw [Rat.not_lt]
  rw [Rat.sub_le_iff_le_add] at h₂
  rw [← Rat.sub_le_iff_le_add] at h₁
  rw [← Rat.add_assoc, Rat.sub_eq_add_neg, Rat.add_assoc,
    show (1 : Rat) + -(1 / 2) = 1 / 2 by decide +kernel, Rat.add_right_comm] at h₁
  refine Rat.le_trans h₂ (Rat.le_trans ?_ h₁)
  simpa [Rat.add_zero] using (@Rat.add_le_add_left 0 n (b.roundEven + 1 / 2)).mpr Rat.natCast_nonneg

instance : Std.LawfulOrderInf Rat where
  le_min_iff a b c := by
    simp only [Rat.instMin, minOfLe]
    split
    · exact iff_self_and.mpr (Rat.le_trans · ‹_›)
    · exact iff_and_self.mpr (Rat.le_trans · (Std.le_of_not_ge ‹_›))

instance : Std.LawfulOrderSup Rat where
  max_le_iff a b c := by
    simp only [Rat.instMax, maxOfLe]
    split
    · exact iff_and_self.mpr (Rat.le_trans ‹_›)
    · exact iff_self_and.mpr (Rat.le_trans (Std.le_of_not_ge ‹_›))

protected def Rat.log2 (q : Rat) : Int :=
  let i : Int := q.num.natAbs.log2 - q.den.log2
  if q.den <<< i.toNat ≤ q.num.natAbs <<< (-i).toNat then i else i - 1

theorem Rat.log2_abs (q : Rat) : q.abs.log2 = q.log2 := by
  cases q
  simp [Rat.abs, Rat.log2]

theorem Rat.log2_neg (q : Rat) : (-q).log2 = q.log2 := by
  simp [Rat.log2]

private theorem Rat.log2_helper (q : Rat) (i : Int) :
    q.den <<< i.toNat ≤ q.num.natAbs <<< (-i).toNat ↔ 2 ^ i ≤ q.abs := by
  simp only [Nat.shiftLeft_eq, ← natCast_le_natCast, natCast_mul, natCast_pow, natCast_ofNat]
  simp only [Rat.pow_pos (by decide : (0 : Rat) < 2), ← Rat.div_le_iff]
  simp only [Rat.natCast_pos, q.den_pos, Rat.mul_div_assoc, ← Rat.le_div_iff']
  simp +decide only [← Rat.zpow_natCast, div_def (_ ^ _), ← Rat.zpow_neg, ← Rat.zpow_add]
  rw [Int.add_neg_eq_sub, Int.toNat_sub_toNat_neg, ← Rat.intCast_natCast, ← Rat.num_abs,
    ← Rat.den_abs, ← Rat.mkRat_eq_div, Rat.mkRat_self]

attribute [norm_cast] Rat.zpow_natCast

namespace Std

public instance {α : Type u} [LT α] [LE α] [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) ]
    [Std.LawfulOrderLT α] : Trans (α := α) (· < ·) (· ≤ ·) (· < ·) where
  trans {a b c} hab hbc := by
    simp only [lt_iff_le_and_not_ge] at hab ⊢
    constructor
    · exact le_trans hab.1 hbc
    · intro hca
      exact hab.2.elim (le_trans hbc hca)

public instance {α : Type u} [LT α] [LE α] [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·) ]
    [Std.LawfulOrderLT α] : Trans (α := α) (· ≤ ·) (· < ·) (· < ·) where
  trans {a b c} hab hbc := by
    simp only [lt_iff_le_and_not_ge] at hbc ⊢
    constructor
    · exact le_trans hab hbc.1
    · intro hca
      exact hbc.2.elim (le_trans hca hab)

end Std

theorem Rat.log2_self_le_abs {q : Rat} (h : q ≠ 0) : 2 ^ q.log2 ≤ q.abs := by
  unfold Rat.log2
  extract_lets i
  simp only [log2_helper]
  split
  · assumption
  · rw [Rat.abs, Rat.mk'_eq_divInt, Rat.divInt_eq_div, Rat.le_div_iff (mod_cast Rat.den_pos _)]
    calc
      _ ≤ (2 : Rat) ^ (i - 1) * 2 ^ (q.den.log2 + 1 : Int) :=
        Rat.mul_le_mul_of_nonneg_left
          (Rat.le_of_lt (mod_cast q.abs.den.lt_log2_self))
          (Rat.zpow_nonneg (by decide))
      _ = 2 ^ (q.num.natAbs.log2 : Int) := by
        rw [← Rat.zpow_add (by decide)]
        congr 1; omega
      _ ≤ _ := mod_cast Nat.log2_self_le (by simp [h])

theorem Rat.abs_lt_log2_self {q : Rat} : q.abs < 2 ^ (q.log2 + 1) := by
  unfold Rat.log2
  extract_lets i
  simp only [log2_helper]
  split
  · rw [Rat.abs, Rat.mk'_eq_divInt, Rat.divInt_eq_div, Rat.div_lt_iff (mod_cast Rat.den_pos _)]
    calc
      _ < (2 : Rat) ^ (q.num.natAbs.log2 + 1 : Int) := mod_cast Nat.lt_log2_self
      _ = _ := by
        rw [← Rat.zpow_add (by decide)]
        congr 1; omega
      2 ^ (i + 1) * 2 ^ (q.den.log2 : Int) ≤ _ :=
        Rat.mul_le_mul_of_nonneg_left
          (mod_cast q.den.log2_self_le (by simp [Rat.den_nz]))
          (Rat.zpow_nonneg (by decide))
  · simp_all [Rat.not_le]

theorem Rat.log2_self_le {q : Rat} (h : 0 < q) : 2 ^ q.log2 ≤ q := by
  simpa only [Rat.abs_of_nonneg (Rat.le_of_lt h)] using q.log2_self_le_abs (Rat.ne_of_gt h)

theorem Rat.lt_log2_self {q : Rat} : q < 2 ^ (q.log2 + 1) := by
  by_cases h : 0 ≤ q
  · simpa only [Rat.abs_of_nonneg h] using q.abs_lt_log2_self
  · exact trans (Rat.not_le.mp h) (Rat.zpow_pos (show 0 < 2 by decide))

protected theorem Rat.zpow_lt_zpow_right {q : Rat} {a b : Int} (hq : 1 < q) (h : a < b) : q ^ a < q ^ b := by
  have hqpos : 0 < q := trans (show 0 < 1 by decide +kernel) hq
  obtain ⟨n, rfl⟩ := h.dest
  rw [Rat.zpow_add (Rat.ne_of_gt hqpos)]
  rw (occs := .pos [1]) [← Rat.mul_one (q ^ a)]
  apply Rat.mul_lt_mul_of_pos_left
  · clear h
    induction n with
    | zero => simp [hq]
    | succ k ih =>
      simp only [Nat.succ_eq_add_one, Int.natCast_add, Int.cast_ofNat_Int,
        Rat.zpow_add_one (m := k + 1) (Rat.ne_of_gt hqpos)]
      rw [← Rat.mul_one 1]
      apply Std.lt_of_lt_of_le (Rat.mul_lt_mul_of_pos_right ih (by decide))
      exact Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hq)
        (Rat.le_trans (by decide) (Rat.le_of_lt ih))
  · exact Rat.zpow_pos hqpos

@[simp]
theorem Rat.one_zpow (i : Int) : (1 : Rat) ^ i = 1 := by
  rcases i with n | n
  · induction n <;> simp_all [Rat.zpow_add_one]
  · induction n <;> simp_all [Rat.zpow_add_one, Int.negSucc_eq, Rat.zpow_neg]

protected theorem Rat.zpow_le_zpow_right {q : Rat} {a b : Int} (hq : 1 ≤ q) (h : a ≤ b) : q ^ a ≤ q ^ b := by
  by_cases h₁ : a = b
  · simp [h₁, Rat.le_refl]
  by_cases h₂ : 1 = q
  · simp [← h₂, Rat.le_refl]
  exact Rat.le_of_lt (Rat.zpow_lt_zpow_right (Rat.lt_of_le_of_ne hq h₂) (Std.lt_of_le_of_ne h h₁))

protected theorem Rat.zpow_le_zpow_iff_right {q : Rat} {a b : Int} (hq : 1 < q) :
    q ^ a ≤ q ^ b ↔ a ≤ b := by
  constructor
  · refine Decidable.not_imp_not.mp fun h => ?_
    simp only [Int.not_le, Rat.not_le] at h ⊢
    exact Rat.zpow_lt_zpow_right hq h
  · exact Rat.zpow_le_zpow_right (Rat.le_of_lt hq)

protected theorem Rat.zpow_lt_zpow_iff_right {q : Rat} {a b : Int} (hq : 1 < q) :
    q ^ a < q ^ b ↔ a < b := by
  constructor
  · refine Decidable.not_imp_not.mp fun h => ?_
    simp only [Int.not_lt, Rat.not_lt] at h ⊢
    exact Rat.zpow_le_zpow_right (Rat.le_of_lt hq) h
  · exact Rat.zpow_lt_zpow_right hq

theorem Rat.le_log2 {i : Int} {q : Rat} (h : 0 < q) : i ≤ q.log2 ↔ 2 ^ i ≤ q := by
  constructor
  · intro hi
    exact Rat.le_trans (Rat.zpow_le_zpow_right (by decide) hi) (Rat.log2_self_le h)
  · intro hi
    rw [← Int.lt_add_one_iff]
    rw [← Rat.zpow_lt_zpow_iff_right (show 1 < 2 by decide)]
    exact Std.lt_of_le_of_lt hi Rat.lt_log2_self

theorem Rat.log2_lt {i : Int} {q : Rat} (h : 0 < q) : q.log2 < i ↔ q < 2 ^ i := by
  apply Decidable.not_iff_not.mp
  simp only [Int.not_lt, Rat.le_log2 h, Rat.not_lt]

theorem Rat.log2_mono {a b : Rat} (ha : 0 < a) (h : a ≤ b) : a.log2 ≤ b.log2 := by
  apply Decidable.byContradiction fun h' => ?_
  rw [Int.not_le] at h'
  have h₁ := a.log2_self_le ha
  have h₂ := b.lt_log2_self
  apply absurd h
  rw [Rat.not_le]
  exact trans h₂ (trans (Rat.zpow_le_zpow_right (by decide) h') h₁)

@[simp]
theorem Rat.log2_two_zpow (i : Int) : (2 ^ i : Rat).log2 = i := by
  apply Int.le_antisymm
  · apply Int.le_of_lt_add_one
    apply (Rat.log2_lt (Rat.zpow_pos (by decide))).mpr
    exact Rat.zpow_lt_zpow_right (by decide) (Int.le_refl _)
  · exact (Rat.le_log2 (Rat.zpow_pos (by decide))).mpr Rat.le_refl

@[simp]
theorem Rat.log2_two_pow (i : Nat) : (2 ^ i : Rat).log2 = i := Rat.log2_two_zpow i

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

@[simp]
theorem canonicalMantissa_zero_iff {fmt : FloatFormat} {e : Int} :
    fmt.CanonicalMantissa 0 e ↔ e = fmt.minExp := by
  simp only [CanonicalMantissa, fexp, Nat.size_zero, Int.cast_ofNat_Int, Int.zero_add]
  have := fmt.prec_pos
  omega

@[simp]
theorem bounded_zero_iff {fmt : FloatFormat} {e : Int} :
    fmt.Bounded 0 e ↔ e = fmt.minExp := by
  simp only [Bounded, canonicalMantissa_zero_iff, minExp, and_iff_left_iff_imp]
  have := fmt.prec_pos
  have := fmt.prec_lt_maxExp
  omega

def roundRatEven (q : Rat) : Rat :=
  let fexp := fmt.fexp (q.log2 + 1)
  (q / 2 ^ fexp).roundEven * 2 ^ fexp

def boundRat (q : Rat) : Rat :=
  max (min (2 ^ fmt.maxExp) q) (-2 ^ fmt.maxExp)

variable {fmt}

theorem minExp_lt_maxExp : fmt.minExp < fmt.maxExp := by
  cases fmt
  simp [minExp]
  omega

theorem minExp_le_maxExp : fmt.minExp ≤ fmt.maxExp := Int.le_of_lt minExp_lt_maxExp

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

theorem roundRatEven_two_pow_eq_self {i : Int} (hi : fmt.minExp ≤ i) :
    fmt.roundRatEven (2 ^ i) = 2 ^ i := by
  simp only [roundRatEven, fexp, Rat.log2_two_zpow]
  by_cases h : i + 1 - fmt.prec ≤ fmt.minExp
  · rw [Int.max_eq_right h, Rat.div_def, ← Rat.zpow_neg, ← Rat.zpow_add (by decide),
      Int.add_neg_eq_sub]
    have : i - fmt.minExp = (i - fmt.minExp).toNat := by omega
    rw [this]
    norm_cast
    rw [Rat.roundEven_natCast]
    simp [← Rat.zpow_natCast, ← this, ← Rat.zpow_add]
  · sorry


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

end FloatFormat

inductive BinaryFloat (fmt : FloatFormat) where
  | nan
  | inf (s : Bool)
  | finite (s : Bool) (m : Nat) (e : Int) (h : fmt.Bounded m e)
deriving DecidableEq

namespace BinaryFloat

variable {fmt : FloatFormat}

protected def zero (s : Bool) : BinaryFloat fmt :=
  .finite s 0 fmt.minExp (fmt.bounded_zero_iff.mpr rfl)

protected def neg : BinaryFloat fmt → BinaryFloat fmt
  | .nan => .nan
  | .inf s => .inf (!s)
  | .finite s m e h => .finite (!s) m e h

instance : Neg (BinaryFloat fmt) := ⟨BinaryFloat.neg⟩

@[simp]
theorem neg_nan : -nan = (nan : BinaryFloat fmt) := rfl

def binaryRoundAux (s : Bool) (m : Nat) (e : Int) (exact : Bool)
    (h : e < fmt.fexp (m.size + e)) : BinaryFloat fmt :=
  let fexp := fmt.fexp (m.size + e)
  if h' : fmt.maxExp - fmt.prec < fexp then .inf s else
  let shift := (fexp - e).toNat
  let val := m >>> shift
  have : fmt.CanonicalMantissa val fexp := by
    simp only [FloatFormat.fexp, FloatFormat.CanonicalMantissa, Nat.size_shiftRight, val, shift,
      fexp] at h ⊢
    omega
  let b := m.testBit (shift - 1)
  let exact := exact && m &&& (1 <<< shift - 1) == 0
  let addOne := b && (!exact || val % 2 == 1)
  if addOne then
    .finite s (val + 1) fexp sorry
  else .finite s val fexp ⟨this, Int.le_of_not_gt h'⟩

def toRat : BinaryFloat fmt → Rat
  | .nan => 0
  | .inf s => (if s then -1 else 1) * 2 ^ fmt.maxExp
  | .finite s m e _ => (if s then -1 else 1) * m * 2 ^ e

theorem toRat_binaryRoundAux_of_nonneg {m : Nat} {e : Int} {exact : Bool}
    (h : e < fmt.fexp (m.size + e)) {q : Rat}
    (hme₁ : m * 2 ^ e ≤ q) (hme₂ : q < (m + 1) * 2 ^ e)
    (hexact : exact ↔ q = m * 2 ^ e) :
    toRat (binaryRoundAux false m e exact h) = fmt.boundRat (fmt.roundRatEven q) := by
  rw [binaryRoundAux]
  split
  · simp only [toRat, Bool.false_eq_true, ↓reduceIte, Rat.one_mul]
    rw [FloatFormat.boundRat_of_ge]
    sorry
  · sorry

end BinaryFloat
