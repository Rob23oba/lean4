/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Init.Data.Rat.Lemmas
public import Init.Data.BitVec.Lemmas
public import Init.Grind.Ordered.Rat
public import Init.Grind.Ordered.Field
public import Init.Data.AC

@[expose] public section

open Lean.Grind.AddCommGroup
open Lean.Grind.OrderedAdd
open Lean.Grind.OrderedRing
open Lean.Grind.Field.IsOrdered

@[simp]
theorem BitVec.extractLsb'_cast {n m : Nat} {start len : Nat} {x : BitVec n} (h : n = m) :
    extractLsb' start len (x.cast h) = extractLsb' start len x := by
  simp [extractLsb']

@[simp]
theorem BitVec.zero_eq_allOnes_iff {n : Nat} : 0#n = allOnes n ↔ n = 0 := by
  constructor
  · intro h
    simpa using congrArg (·.getLsbD 0) h
  · rintro rfl
    rfl

@[simp]
theorem BitVec.allOnes_eq_zero_iff {n : Nat} : allOnes n = 0#n ↔ n = 0 :=
  eq_comm.trans BitVec.zero_eq_allOnes_iff

def Nat.size (n : Nat) : Nat :=
  if n = 0 then 0 else n.log2 + 1

theorem Nat.size_le {a b : Nat} : a.size ≤ b ↔ a < 2 ^ b := by
  rw [size]
  split
  · simp [Nat.pow_pos, *]
  · simp [Nat.add_one_le_iff, Nat.log2_lt, *]

theorem Nat.lt_size_self (a : Nat) : a < 2 ^ a.size := Nat.size_le.mp (Nat.le_refl _)

theorem Nat.lt_size {a b : Nat} : a < b.size ↔ 2 ^ a ≤ b := by
  rw [← Decidable.not_iff_not]
  simp [Nat.size_le]

@[simp] theorem Nat.size_zero : (0).size = 0 := rfl
@[simp] theorem Nat.size_one : (1).size = 1 := rfl
@[simp] theorem Nat.size_two : (2).size = 2 := rfl

theorem Nat.size_eq_iff {a b : Nat} : a.size = b ↔ 2 ^ b / 2 ≤ a ∧ a < 2 ^ b := by
  simp only [Nat.le_antisymm_iff, size_le, and_comm, and_congr_left_iff]
  intro h
  rcases b with _ | b
  · simp
  · simp [Nat.add_one_le_iff, Nat.pow_succ, Nat.lt_size]

theorem Nat.size_eq_iff' {a b : Nat} (h : b ≠ 0) :
    a.size = b ↔ 2 ^ (b - 1) ≤ a ∧ a < 2 ^ b := by
  rw [← Nat.pow_div (Nat.pos_of_ne_zero h) (by decide)]
  exact Nat.size_eq_iff

@[simp]
theorem Nat.size_eq_zero_iff {a : Nat} : a.size = 0 ↔ a = 0 := by
  simp [Nat.size_eq_iff]

theorem Nat.size_eq_log2_add_one {a : Nat} (ha : a ≠ 0) : a.size = a.log2 + 1 := by
  simp [Nat.size, ha]

theorem Nat.size_self_le (a : Nat) : 2 ^ a.size / 2 ≤ a :=
  (Nat.size_eq_iff.mp rfl).1

theorem Nat.size_self_le' {a : Nat} (ha : a ≠ 0) : 2 ^ (a.size - 1) ≤ a := by
  rw [← Nat.pow_div (Nat.pos_of_ne_zero (mt Nat.size_eq_zero_iff.mp ha)) (by decide)]
  exact Nat.size_self_le a

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
  · simpa [Nat.sub_eq_zero_of_le (Nat.le_of_not_le h), Nat.size_le] using Nat.le_of_not_le h

theorem Nat.size_shiftLeft {a b : Nat} (h : a ≠ 0) : (a <<< b).size = a.size + b := by
  rw [Nat.size_eq_iff, Nat.shiftLeft_eq, Nat.pow_add]
  constructor
  · rw [Nat.mul_comm, Nat.mul_div_assoc, Nat.mul_comm]
    · exact Nat.mul_le_mul_right _ a.size_self_le
    · rw (occs := .pos [1]) [← Nat.pow_one 2]
      apply Nat.pow_dvd_pow
      exact Nat.pos_of_ne_zero (mt a.size_eq_zero_iff.mp h)
  · exact Nat.mul_lt_mul_of_pos_right a.lt_size_self b.two_pow_pos

theorem Nat.size_mono {a b : Nat} (h : a ≤ b) : a.size ≤ b.size := by
  rw [Nat.size_le]
  exact Nat.lt_of_le_of_lt h (lt_size_self b)

theorem Nat.le_log2_mul {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.log2 + b.log2 ≤ (a * b).log2 := by
  rw [Nat.le_log2 (Nat.mul_ne_zero ha hb), Nat.pow_add]
  exact Nat.mul_le_mul (log2_self_le ha) (log2_self_le hb)

theorem Nat.log2_mul_le (a b : Nat) :
    (a * b).log2 ≤ a.log2 + b.log2 + 1 := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [Nat.le_iff_lt_add_one, Nat.add_right_comm a.log2, Nat.add_assoc,
    Nat.log2_lt (Nat.mul_ne_zero ha hb), Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt lt_log2_self lt_log2_self

theorem Nat.lt_size_mul {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.size + b.size - 1 ≤ (a * b).size := by
  simp only [ne_eq, ha, not_false_eq_true, size_eq_log2_add_one, hb, add_succ_sub_one,
    Nat.mul_ne_zero, Nat.add_right_comm]
  exact Nat.succ_le_succ (Nat.le_log2_mul ha hb)

theorem Nat.size_mul_le (a b : Nat) :
    (a * b).size ≤ a.size + b.size := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simp only [ne_eq, ha, not_false_eq_true, hb, Nat.mul_ne_zero, size_eq_log2_add_one,
    ← Nat.add_assoc, Nat.add_right_comm, Nat.add_le_add_iff_right]
  exact log2_mul_le a b

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

instance : Std.Commutative (α := Rat) (· + ·) := ⟨Rat.add_comm⟩
instance : Std.Associative (α := Rat) (· + ·) := ⟨Rat.add_assoc⟩
instance : Std.LawfulIdentity (α := Rat) (· + ·) 0 where
  left_id := Rat.zero_add
  right_id := Rat.add_zero

instance : Std.Commutative (α := Rat) (· * ·) := ⟨Rat.mul_comm⟩
instance : Std.Associative (α := Rat) (· * ·) := ⟨Rat.mul_assoc⟩
instance : Std.LawfulIdentity (α := Rat) (· * ·) 1 where
  left_id := Rat.one_mul
  right_id := Rat.mul_one

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

@[simp]
protected theorem Rat.sub_zero (a : Rat) : a - 0 = a := by
  simp [Rat.sub_eq_add_neg, Rat.add_zero]

@[simp]
protected theorem Rat.div_zero (a : Rat) : a / 0 = 0 := by
  simp [Rat.div_def]

protected theorem Rat.div_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b :=
  Rat.mul_nonneg ha (inv_nonneg_iff.mpr hb)

protected theorem Rat.div_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a / b :=
  Rat.mul_pos ha (inv_pos_iff.mpr hb)

protected theorem Rat.div_div (a b c : Rat) : a / b / c = a / (b * c) := by
  simp [div_def, Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm]

protected theorem Rat.div_mul (a b c : Rat) : a / b * c = a / (b / c) := by
  simp [div_def, Rat.inv_mul_rev, Rat.inv_inv, Rat.mul_assoc, Rat.mul_comm c]

protected theorem Rat.mul_left_comm (a b c : Rat) : a * (b * c) = b * (a * c) := by
  rw [← Rat.mul_assoc, ← Rat.mul_assoc, Rat.mul_comm b]

protected theorem Rat.mul_right_comm (a b c : Rat) : a * b * c = a * c * b := by
  rw [Rat.mul_assoc, Rat.mul_assoc, Rat.mul_comm b]

protected theorem Rat.mul_div_comm (a b c : Rat) : a * b / c = a / c * b := by
  rw [Rat.div_def, Rat.div_def, Rat.mul_right_comm]

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

protected theorem Rat.neg_le_self_iff {a : Rat} : -a ≤ a ↔ 0 ≤ a := by
  rw [← Rat.zero_sub, Rat.sub_le_iff_le_add, ← Rat.one_mul a, ← Rat.add_mul,
    mul_nonneg_iff, show 1 + 1 = (2 : Rat) by decide +kernel]
  simp +decide

protected theorem Rat.neg_lt_self_iff {a : Rat} : -a < a ↔ 0 < a := by
  rw [← Rat.zero_sub, Rat.sub_lt_iff_lt_add, ← Rat.one_mul a, ← Rat.add_mul,
    mul_pos_iff, show 1 + 1 = (2 : Rat) by decide +kernel]
  simp +decide

protected theorem Rat.div_le_iff {a b c : Rat} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  simpa [Rat.not_lt] using not_congr (Rat.lt_div_iff hb)

protected theorem Rat.div_le_iff' {a b c : Rat} (hb : 0 < b) : a / b ≤ c ↔ a ≤ b * c := by
  simpa [Rat.not_lt] using not_congr (Rat.lt_div_iff' hb)

protected theorem Rat.div_eq_iff {a b c : Rat} (hb : b ≠ 0) : a / b = c ↔ a = c * b :=
  ⟨(by simpa only [Rat.div_mul_cancel hb] using congrArg (· * b) ·),
    (by simpa only [Rat.mul_div_cancel hb] using congrArg (· / b) ·)⟩

protected theorem Rat.div_eq_iff' {a b c : Rat} (hb : b ≠ 0) : a / b = c ↔ a = b * c := by
  rw [Rat.div_eq_iff hb, Rat.mul_comm]

protected theorem Rat.eq_div_iff {a b c : Rat} (hc : c ≠ 0) : a = b / c ↔ a * c = b := by
  rw [eq_comm, Rat.div_eq_iff hc, eq_comm]

protected theorem Rat.eq_div_iff' {a b c : Rat} (hc : c ≠ 0) : a = b / c ↔ c * a = b := by
  rw [Rat.eq_div_iff hc, Rat.mul_comm]

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

theorem Rat.floor_eq_iff {q : Rat} {i : Int} : q.floor = i ↔ i ≤ q ∧ q < i + 1 := by
  constructor
  · rintro rfl
    constructor
    · exact floor_le q
    · exact_mod_cast lt_floor_add_one q
  · intro ⟨h, h'⟩
    apply Int.le_antisymm
    · rw [Int.le_iff_lt_add_one, Rat.floor_lt_iff]
      assumption_mod_cast
    · rwa [Rat.le_floor_iff]

@[simp]
theorem Rat.floor_ofNat (n : Nat) : Rat.floor (no_index (OfNat.ofNat n)) = OfNat.ofNat n := rfl

theorem Rat.floor_div_intCast_of_nonneg {q : Rat} {n : Int} (hn : 0 ≤ n) :
    (q / n : Rat).floor = q.floor / n := by
  by_cases h : n = 0
  · simp [h]
  replace hn := Std.lt_of_le_of_ne hn (Ne.symm h)
  rw [Rat.floor_eq_iff]
  constructor
  · rw [Rat.le_div_iff (Rat.intCast_pos.mpr hn)]
    norm_cast
    rw [← Rat.le_floor_iff]
    exact Int.ediv_mul_le q.floor h
  · rw [Rat.div_lt_iff (Rat.intCast_pos.mpr hn)]
    norm_cast
    rw [← Rat.floor_lt_iff]
    exact Int.lt_ediv_add_one_mul_self q.floor hn

theorem Rat.floor_div_natCast (q : Rat) (n : Nat) : (q / n).floor = q.floor / n :=
  Rat.floor_div_intCast_of_nonneg (Int.natCast_nonneg n)

theorem Rat.floor_div_ofNat (q : Rat) (n : Nat) :
    (q / no_index (OfNat.ofNat n)).floor = q.floor / no_index (OfNat.ofNat n) :=
  Rat.floor_div_natCast q n

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
    ∃ i : Int, q = i + 1 / 2 ∨ i * 2 - 1 < q * 2 ∧ q * 2 < i * 2 + 1 := by
  rcases q with ⟨n, d, nz, r⟩
  simp only [mk'_eq_divInt, divInt_eq_div, ne_eq, intCast_eq_zero_iff, Int.natCast_eq_zero, nz,
    not_false_eq_true, Rat.div_eq_iff', ← Rat.mul_div_comm, intCast_pos, Int.natCast_pos,
    Nat.pos_of_ne_zero nz, Rat.lt_div_iff, Rat.div_lt_iff]
  norm_cast
  rw [exists_or, Classical.or_iff_not_imp_left, not_exists]
  intro h
  conv at h => intro i; rw [← Rat.mul_div_cancel (a := i) (show 2 ≠ 0 by decide), ← Rat.add_div,
    ← Rat.mul_div_assoc, eq_comm, Rat.div_eq_iff (by decide), eq_comm, Rat.mul_comm d]
  norm_cast at h
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
  · rw [h, Rat.roundEven_intCast_add_half, Rat.add_assoc,
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
  · rw [h, Rat.roundEven_intCast_add_half, Rat.add_sub_cancel]
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
  · rw [h, Rat.roundEven_intCast_add_half]
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

@[simp]
theorem Rat.floor_add_intCast (q : Rat) (i : Int) : (q + i).floor = q.floor + i := by
  rw [Rat.floor_eq_iff]
  simp only [Rat.intCast_add, Rat.add_le_add_right, Rat.add_right_comm _ i,
    Rat.add_lt_add_iff_right, ← Rat.floor_eq_iff]

@[simp]
theorem Rat.floor_intCast_add (i : Int) (q : Rat) : (i + q).floor = i + q.floor := by
  rw [Rat.add_comm i, Rat.floor_add_intCast, Int.add_comm]

theorem Rat.floor_eq_self_iff_floor_mul_eq_self_and_dvd (q : Rat) (n : Nat) (hn : n ≠ 0) :
    q.floor = q ↔ (q * n).floor = q * n ∧ (n : Int) ∣ (q * n).floor := by
  rw [← Rat.mul_div_cancel (a := q) (mod_cast hn : (n : Rat) ≠ 0)]
  rw [floor_div_natCast, eq_comm, Rat.div_eq_iff (mod_cast hn),
    Rat.mul_div_cancel (mod_cast hn)]
  norm_cast
  constructor
  · intro h
    simp only [Int.ediv_mul_self, Rat.intCast_sub] at h
    have h' := trans (q * n).floor_le h
    rw [Rat.le_sub_iff_add_le] at h'
    conv at h' => rhs; apply (Rat.add_zero _).symm
    rw [Rat.add_le_add_left] at h'
    norm_cast at h'
    replace h' := Int.le_antisymm h' (Int.emod_nonneg (q * n).floor (mod_cast hn))
    symm at h
    simp_all [Int.dvd_of_emod_eq_zero]
  · intro ⟨h, k, hk⟩
    rw [hk, Int.mul_ediv_cancel_left _ (mod_cast hn), ← Int.mul_comm, ← hk, h]

theorem Rat.floor_half : (1 / 2 : Rat).floor = 0 := by decide +kernel

theorem Rat.mul_left_inj {a b c : Rat} (h : c ≠ 0) : a * c = b * c ↔ a = b := by
  constructor
  · intro h'
    simpa [Rat.mul_div_cancel h] using congrArg (· / c) h'
  · exact congrArg (· * c)

theorem Rat.roundEven_eq_floor {q : Rat} :
    q.roundEven = q.floor +
      if (q * 2).floor % 2 = 1 ∧ ((q * 2).floor ≠ q * 2 ∨ q.floor % 2 = 1)
      then 1 else 0 := by
  obtain ⟨i, h | h⟩ := q.roundEven_cases
  · rw [h, roundEven_intCast_add_half]
    have hnorm : (i * 2 : Rat) = (i * 2 : Int) := by norm_cast
    conv => enter [2, 2, 1, 2, 1]; rw [ne_eq, ← Rat.mul_left_inj (show 2 ≠ 0 by decide)]
    suffices (if i % 2 = 0 then i else i + 1) = i + if i % 2 = 1 then 1 else 0 by
      simpa [-Rat.intCast_mul, hnorm, floor_half, Rat.add_mul, Rat.div_mul_cancel,
        Int.dvd_iff_emod_eq_zero] using this
    split
    · simp [‹i % 2 = 0›]
    · simp [i.emod_two_eq.resolve_left ‹_›]
  · rw [roundEven_of_gt_of_lt h.1 h.2]
    by_cases h' : i ≤ q
    · have hq2 : (q * 2).floor = i * 2 := by
        simpa [Rat.floor_eq_iff, h] using Rat.mul_le_mul_of_nonneg_right h' (by decide)
      have hq : q.floor = i := by
        rw [← Int.mul_ediv_cancel i (show 2 ≠ 0 by decide), ← hq2, ← Rat.floor_div_ofNat,
          Rat.mul_div_cancel (by decide)]
      simp [hq, hq2]
    · rw [Rat.not_le] at h'
      have hq2 : (q * 2).floor = i * 2 - 1 := by
        simpa [Rat.floor_eq_iff, Rat.le_of_lt h.1, Rat.sub_add_cancel]
          using Rat.mul_lt_mul_of_pos_right h' (by decide)
      have hq : q.floor = i - 1 := by
        have : (i * 2 - 1) / 2 = i - 1 := by omega
        rw [← this, ← hq2, ← Rat.floor_div_ofNat, Rat.mul_div_cancel (by decide)]
      simp only [hq, hq2, Int.mul_sub_emod_self_right, Int.reduceNeg, Int.neg_emod_two,
        Int.reduceMod, Rat.intCast_sub, Rat.intCast_mul, intCast_ofNat, ne_eq, true_and]
      simp [Rat.ne_of_lt h.1]

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

theorem Std.le_iff_lt_or_eq {α : Type u} [LE α] [LT α] [IsPartialOrder α] [LawfulOrderLT α]
    {a b : α} : a ≤ b ↔ a < b ∨ a = b := by
  constructor
  · rw [Classical.or_iff_not_imp_right]
    exact Std.lt_of_le_of_ne
  · rintro (h | rfl)
    · exact Std.le_of_lt h
    · exact Std.le_refl a

protected def Rat.log2 (q : Rat) : Int :=
  let i : Int := q.num.natAbs.log2 - q.den.log2
  if q.den <<< i.toNat ≤ q.num.natAbs <<< (-i).toNat then i else i - 1

theorem Rat.log2_abs (q : Rat) : q.abs.log2 = q.log2 := by
  cases q
  simp [Rat.abs, Rat.log2]

theorem Rat.log2_neg (q : Rat) : (-q).log2 = q.log2 := by
  simp [Rat.log2]

theorem Rat.zpow_sub {q : Rat} (hq : q ≠ 0) (m n : Int) : q ^ (m - n) = q ^ m / q ^ n := by
  rw [Int.sub_eq_add_neg, Rat.zpow_add hq, Rat.zpow_neg, Rat.div_def]

protected theorem Rat.zpow_sub_one' {q : Rat} (hq : q ≠ 0) (m : Int) :
    q ^ (m - 1) = q ^ m / q :=
  Rat.zpow_sub_one hq m

private theorem Rat.log2_helper (q : Rat) (i : Int) :
    q.den <<< i.toNat ≤ q.num.natAbs <<< (-i).toNat ↔ 2 ^ i ≤ q.abs := by
  simp only [Nat.shiftLeft_eq, ← natCast_le_natCast, natCast_mul, natCast_pow, natCast_ofNat]
  simp only [Rat.pow_pos (by decide : (0 : Rat) < 2), ← Rat.div_le_iff]
  simp only [Rat.natCast_pos, q.den_pos, Rat.mul_div_assoc, ← Rat.le_div_iff']
  simp +decide only [← Rat.zpow_natCast, ← Rat.zpow_sub]
  rw [Int.toNat_sub_toNat_neg, ← Rat.intCast_natCast, ← Rat.num_abs,
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

protected theorem Rat.pow_le_pow_right {q : Rat} {a b : Nat} (hq : 1 ≤ q) (h : a ≤ b) :
    q ^ a ≤ q ^ b :=
  mod_cast @Rat.zpow_le_zpow_right q a b (mod_cast hq) (mod_cast h)

protected theorem Rat.zpow_le_zpow_iff_right {q : Rat} {a b : Int} (hq : 1 < q) :
    q ^ a ≤ q ^ b ↔ a ≤ b := by
  constructor
  · refine Decidable.not_imp_not.mp fun h => ?_
    simp only [Int.not_le, Rat.not_le] at h ⊢
    exact Rat.zpow_lt_zpow_right hq h
  · exact Rat.zpow_le_zpow_right (Rat.le_of_lt hq)

protected theorem Rat.pow_le_pow_iff_right {q : Rat} {a b : Nat} (hq : 1 < q) :
    q ^ a ≤ q ^ b ↔ a ≤ b :=
  mod_cast @Rat.zpow_le_zpow_iff_right q a b (mod_cast hq)

protected theorem Rat.zpow_lt_zpow_iff_right {q : Rat} {a b : Int} (hq : 1 < q) :
    q ^ a < q ^ b ↔ a < b := by
  constructor
  · refine Decidable.not_imp_not.mp fun h => ?_
    simp only [Int.not_lt, Rat.not_lt] at h ⊢
    exact Rat.zpow_le_zpow_right (Rat.le_of_lt hq) h
  · exact Rat.zpow_lt_zpow_right hq

protected theorem Rat.pow_lt_pow_iff_right {q : Rat} {a b : Nat} (hq : 1 < q) :
    q ^ a < q ^ b ↔ a < b :=
  mod_cast @Rat.zpow_lt_zpow_iff_right q a b (mod_cast hq)

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

theorem Rat.log2_eq_iff {q : Rat} {i : Int} (hq : 0 < q) :
    q.log2 = i ↔ 2 ^ i ≤ q ∧ q < 2 ^ (i + 1) := by
  constructor
  · rintro rfl
    exact ⟨log2_self_le hq, lt_log2_self⟩
  · intro ⟨h, h'⟩
    apply Int.le_antisymm
    · rwa [Int.le_iff_lt_add_one, Rat.log2_lt hq]
    · rwa [Rat.le_log2 hq]

def Rat.ofSign (b : Bool) : Rat :=
  match b with
  | false => 1
  | true => -1

@[simp] theorem Rat.ofSign_false : ofSign false = 1 := rfl
@[simp] theorem Rat.ofSign_true : ofSign true = -1 := rfl

theorem Rat.ofSign_not : ∀ (a : Bool), ofSign (!a) = -ofSign a := by decide
theorem Rat.ofSign_xor : ∀ (a b : Bool), ofSign (a ^^ b) = ofSign a * ofSign b := by decide +kernel
theorem Rat.ofSign_bne : ∀ (a b : Bool), ofSign (a != b) = ofSign a * ofSign b := Rat.ofSign_xor
theorem Rat.ofSign_ne_zero : ∀ (a : Bool), ofSign a ≠ 0 := by decide

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

protected def zero (s : Bool) : BinaryFloat fmt :=
  .finite s 0 fmt.minExp (fmt.bounded_zero_iff.mpr rfl)

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

protected def sign : BinaryFloat fmt → Bool
  | .nan => false
  | .inf s => s
  | .finite s _ _ _ => s

protected def neg : BinaryFloat fmt → BinaryFloat fmt
  | .nan => .nan
  | .inf s => .inf (!s)
  | .finite s m e h => .finite (!s) m e h

instance : Neg (BinaryFloat fmt) := ⟨BinaryFloat.neg⟩

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
