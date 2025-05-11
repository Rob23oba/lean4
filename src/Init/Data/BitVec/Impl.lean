/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
--module

prelude
import Init.Data.BitVec.Lemmas

protected def BitVec.hpowImpl.term {x : BitVec w} (h : ¬x = 0#w) :
    sizeOf (x >>> 1) < sizeOf x := by
  change 1 + (1 + x.toNat >>> 1) < 1 + (1 + x.toNat)
  simp only [Nat.add_lt_add_iff_left, Nat.shiftRight_eq_div_pow]
  apply Nat.bitwise_rec_lemma
  simpa only [← BitVec.toNat_inj] using h

protected def BitVec.hpowImpl (x y : BitVec w) : BitVec w :=
  go x y 1#w
where
  go (x y res : BitVec w) : BitVec w :=
    if y = 0#w then res
    else if y &&& 1#w = 1#w then go (x * x) (y >>> 1) (res * x)
    else go (x * x) (y >>> 1) res
  termination_by y
  decreasing_by all_goals exact BitVec.hpowImpl.term ‹_›

theorem Nat.exists_of_mod_eq {x y z : Nat} (h : x % y = z) : ∃ a, x = y * a + z :=
  ⟨x / y, h.symm ▸ (div_add_mod x y).symm⟩

@[csimp]
theorem BitVec.hpowImpl_eq_hpow : @BitVec.hpow = @BitVec.hpowImpl := by
  funext w x y
  rw [← BitVec.one_mul (x.hpow y), BitVec.hpow]
  change _ = hpowImpl.go x y 1#w
  symm
  induction x, y, 1#w using hpowImpl.go.induct_unfolding
  · simp
  all_goals
  rename_i hy hy' ih
  have : 1 % 2 ^ w = 1 :=
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (length_pos_of_ne hy))
  simp only [ih, BitVec.toNat_ushiftRight]
  simp only [← toNat_inj, toNat_and, toNat_ofNat, this, Nat.and_one_is_mod,
    Nat.mod_two_not_eq_one] at hy'
  rcases Nat.exists_of_mod_eq hy' with ⟨a, ha⟩
  rw [Nat.add_comm] at ha
  simp [ha, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left, BitVec.pow_add, BitVec.pow_mul',
    BitVec.pow_two, BitVec.mul_pow, BitVec.mul_assoc]

theorem Nat.mod_two_pow_add_one_eq_or_of_mod_two_pow_eq {n k x : Nat} (h : n % 2 ^ k = x) :
    n % 2 ^ (k + 1) = x ∨ n % 2 ^ (k + 1) = x + 2 ^ k := by
  rw [Nat.pow_succ, Nat.mod_mul, h, Nat.add_eq_left, Nat.add_left_cancel_iff]
  conv => rhs; rhs; apply (Nat.mul_one _).symm
  rw [Nat.mul_left_cancel_iff (Nat.two_pow_pos _), Nat.mul_eq_zero]
  simp only [NeZero.ne, false_or]
  apply Nat.mod_two_eq_zero_or_one

theorem Nat.pow_two_pow_mod_two_pow (n i : Nat) (hn : 0 < n) : (i ^ (2 ^ n)) % (2 ^ n) = i % 2 := by
  match n, hn with | k + 1, hn' => ?_
  clear hn' hn n
  have : (i % 2) * (i % 2) = i % 2 := by
    generalize h : i % 2 = x
    have hlt : x < 2 := h ▸ Nat.mod_lt _ (by decide)
    match x, hlt with
    | 0, _ | 1, _ => decide
  induction k with
  | zero => simp [Nat.pow_two, Nat.mul_mod, Nat.mod_mod, this]
  | succ k ih =>
    have this' (i k) : i % 2 % (2 ^ (k + 1)) = i % 2 := by
      apply Nat.mod_eq_of_lt
      apply Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide))
      rw [Nat.pow_succ]
      exact Nat.mul_le_mul_right 2 (Nat.two_pow_pos k)
    conv => lhs; lhs; rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_two]
    rw [Nat.mul_mod]
    rcases Nat.mod_two_pow_add_one_eq_or_of_mod_two_pow_eq ih with (h | h)
    · rw [h, this, this']
    · have this'' (a b) : (a + b) * (a + b) = a * a+ 2 * a * b + b * b := by
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm b a, Nat.add_assoc, Nat.two_mul]
      rw [h, this'', this, ← Nat.pow_add, Nat.mul_comm 2, Nat.mul_assoc, ← Nat.pow_add_one']
      rw [← Nat.add_assoc, Nat.add_right_comm _ k 1, Nat.pow_add _ (k + 2)]
      conv =>
        lhs; rw [Nat.add_mod]; lhs
        conv => lhs; rw [Nat.add_mod]; lhs; rw [this', Nat.mul_mod_left, Nat.add_zero]
        conv => rhs; rw [Nat.mul_mod_right]
        rw [this', Nat.add_zero]
      rw [this']

theorem BitVec.pow_two_pow_eqkk (x : BitVec w) : x ^ (2 ^ w) = x &&& 1#w := by
  by_cases h : w = 0
  · exact BitVec.eq_of_zero_length h
  simp only [← toNat_inj, BitVec.toNat_pow, toNat_and, toNat_ofNat]
  replace h : 0 < w := by omega
  rw [Nat.pow_two_pow_mod_two_pow _ _ h]
  have : 1 < 2 ^ w := Nat.pow_lt_pow_right (by decide) h
  rw [Nat.mod_eq_of_lt this, Nat.and_one_is_mod]

theorem BitVec.pow_mul_two_pow_eq {x : BitVec w} (h : x &&& 1#w = 1#w) (n : Nat) : x ^ (n * 2 ^ w) = 1#w := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [Nat.succ_mul, BitVec.pow_add, BitVec.pow_two_pow_eq, h, BitVec.mul_one, ih]
