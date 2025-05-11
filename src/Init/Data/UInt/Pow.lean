/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
import Init.Data.UInt.Bitwise
import Init.Data.AC
import Init.SizeOfLemmas

protected def BitVec.hpow.term {x : BitVec w} (h : ¬x = 0#w) :
    sizeOf (x >>> 1) < sizeOf x := by
  change 1 + (1 + x.toNat >>> 1) < 1 + (1 + x.toNat)
  simp only [Nat.add_lt_add_iff_left, Nat.shiftRight_eq_div_pow]
  apply Nat.bitwise_rec_lemma
  change ¬⟨⟨x.toNat, x.isLt⟩⟩ = (⟨⟨0, _⟩⟩ : BitVec w) at h
  simpa only [BitVec.ofFin.injEq, Fin.mk.injEq] using h

protected def BitVec.hpow (x y : BitVec w) : BitVec w :=
  go x y 1#w
where
  go (x y res : BitVec w) : BitVec w :=
    if y = 0#w then res
    else if y &&& 1#w = 1#w then go (x * x) (y >>> 1) (res * x)
    else go (x * x) (y >>> 1) res
  termination_by y
  decreasing_by all_goals exact BitVec.hpow.term ‹_›

instance : Pow (BitVec w) (BitVec w) := ⟨BitVec.hpow⟩

@[simp]
protected theorem BitVec.toNat_pow (x : BitVec w) (y : Nat) : (x ^ y).toNat = (x.toNat ^ y) % 2 ^ w := by
  induction y with
  | zero => simp
  | succ k ih => simp [BitVec.pow_succ, ih, Nat.pow_succ]

theorem Nat.exists_of_mod_eq {x y z : Nat} (h : x % y = z) : ∃ a, x = y * a + z :=
  ⟨x / y, h.symm ▸ (div_add_mod x y).symm⟩

protected theorem BitVec.pow_mul (x : BitVec w) (m n : Nat) : x ^ (m * n) = (x ^ m) ^ n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.mul_succ, BitVec.pow_add, ih, BitVec.pow_succ]

protected theorem BitVec.pow_mul' (x : BitVec w) (m n : Nat) : x ^ (m * n) = (x ^ n) ^ m := by
  rw [Nat.mul_comm, BitVec.pow_mul]

protected theorem BitVec.mul_pow (x y : BitVec w) (n : Nat) : (x * y) ^ n = x ^ n * y ^ n := by
  induction n with
  | zero => simp
  | succ k ih => simp only [BitVec.pow_succ, ih]; ac_rfl

@[simp]
theorem BitVec.hpow_eq_pow (x y : BitVec w) : x ^ y = x ^ y.toNat := by
  rw [← BitVec.one_mul (x ^ y.toNat)]
  change hpow.go x y 1#w = _
  induction x, y, 1#w using hpow.go.induct_unfolding
  · simp
  all_goals
  rename_i hy hy' ih
  have : 1 % 2 ^ w = 1 :=
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (length_pos_of_ne hy))
  simp only [ih, BitVec.toNat_ushiftRight]
  simp only [← toNat_inj, toNat_and, toNat_ofNat, this, Nat.and_one_is_mod,
    Nat.mod_two_not_eq_one] at hy'
  rcases Nat.exists_of_mod_eq hy' with ⟨a, ha⟩
  simp [ha, Nat.shiftRight_eq_div_pow, Nat.mul_add_div, BitVec.pow_add,
    BitVec.pow_mul', BitVec.pow_succ, BitVec.mul_pow] <;> ac_rfl

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
    · have this'' (a b) : (a + b) * (a + b) = a * a + b * b + 2 * a * b := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm b a]
        rw [Nat.two_mul, Nat.add_mul]
        ac_rfl
      rw [h, this'', this, ← Nat.pow_add, Nat.mul_comm 2, Nat.mul_assoc, ← Nat.pow_add_one']
      rw [show k + 1 + (k + 1) = k + 1 + 1 + k from by ac_rfl, Nat.pow_add]
      conv =>
        lhs; rw [Nat.add_mod]; lhs
        conv => lhs; rw [Nat.add_mod]; lhs; rw [this', Nat.mul_mod_right, Nat.add_zero]
        conv => rhs; rw [Nat.mul_mod_left]
        rw [this', Nat.add_zero]
      rw [this']

theorem BitVec.pow_two_pow_eq (x : BitVec w) : x ^ (2 ^ w) = x &&& 1#w := by
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

theorem BitVec.pow_eq_pow_mod {x : BitVec w} (h : x &&& 1#w = 1#w) (n : Nat) : x ^ n = x ^ (n % 2 ^ w) := by
  conv => lhs; rw [← Nat.div_add_mod n (2 ^ w)]
  rw [BitVec.pow_add, Nat.mul_comm, BitVec.pow_mul_two_pow_eq h, BitVec.one_mul]

theorem BitVec.and_one_not_eq_one_iff (h : 0 < w) (x : BitVec w) : ¬x &&& 1#w = 1#w ↔ x &&& 1#w = 0#w := by
  have : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h)
  simp [BitVec.toNat_eq, this]

theorem BitVec.pow_eq_zero_of_le {x : BitVec w} (h : x &&& 1#w = 0#w) {n : Nat} (h' : 2 ^ w ≤ n) : x ^ n = 0#w := by
  obtain ⟨k, rfl⟩ := Nat.le.dest h'
  rw [BitVec.pow_add, BitVec.pow_two_pow_eq, h, BitVec.zero_mul]

theorem BitVec.pow_eq_ite_lt_or_and_eq_one (x : BitVec w) (n : Nat) :
    x ^ n = (if n < 2 ^ w ∨ x &&& 1#w = 1#w then x ^ (n % 2 ^ w) else 0#w) := by
  split
  · rename_i h
    rcases h with h | h
    · rw [Nat.mod_eq_of_lt h]
    · rw [BitVec.pow_eq_pow_mod h]
  · rename_i h
    by_cases hw : w = 0
    · exact eq_of_zero_length hw
    · simp only [_root_.not_or, Nat.not_lt,
        BitVec.and_one_not_eq_one_iff (Nat.zero_lt_of_ne_zero hw)] at h
      rw [BitVec.pow_eq_zero_of_le h.2 h.1]



/--
The homogenous power operation, raising an 8-bit unsigned integer to an 8-bit unsigned
integer power, wrapping around on overflow. Usually accessed via the `^` operator.
-/
protected def UInt8.hpow (x y : UInt8) : UInt8 :=
  go x y 1
where
  go (x y res : UInt8) : UInt8 :=
    if y = 0 then res
    else if y &&& 1 = 1 then go (x * x) (y >>> 1) (res * x)
    else go (x * x) (y >>> 1) res
  termination_by y
  decreasing_by all_goals simp [← UInt8.toNat_inj] at * <;> omega

/--
The homogenous power operation, raising a 16-bit unsigned integer to a 16-bit unsigned
integer power, wrapping around on overflow. Usually accessed via the `^` operator.
-/
protected def UInt16.hpow (x y : UInt16) : UInt16 :=
  go x y 1
where
  go (x y res : UInt16) : UInt16 :=
    if y = 0 then res
    else if y &&& 1 = 1 then go (x * x) (y >>> 1) (res * x)
    else go (x * x) (y >>> 1) res
  termination_by y
  decreasing_by all_goals simp [← UInt16.toNat_inj] at * <;> omega

/--
The homogenous power operation, raising a 32-bit unsigned integer to a 32-bit unsigned
integer power, wrapping around on overflow. Usually accessed via the `^` operator.
-/
protected def UInt32.hpow (x y : UInt32) : UInt32 :=
  go x y 1
where
  go (x y res : UInt32) : UInt32 :=
    if y = 0 then res
    else if y &&& 1 = 1 then go (x * x) (y >>> 1) (res * x)
    else go (x * x) (y >>> 1) res
  termination_by y
  decreasing_by all_goals simp [← UInt32.toNat_inj] at * <;> omega

/--
The homogenous power operation, raising a 64-bit unsigned integer to a 64-bit unsigned
integer power, wrapping around on overflow. Usually accessed via the `^` operator.
-/
protected def UInt64.hpow (x y : UInt64) : UInt64 :=
  go x y 1
where
  go (x y res : UInt64) : UInt64 :=
    if y = 0 then res
    else if y &&& 1 = 1 then go (x * x) (y >>> 1) (res * x)
    else go (x * x) (y >>> 1) res
  termination_by y
  decreasing_by all_goals simp [← UInt64.toNat_inj] at * <;> omega

/--
The homogenous power operation, raising a word-sized unsigned integer to a word-sized unsigned
integer power, wrapping around on overflow. Usually accessed via the `^` operator.
-/
protected def USize.hpow (x y : USize) : USize :=
  go x y 1
where
  go (x y res : USize) : USize :=
    if y = 0 then res
    else if y &&& 1 = 1 then go (x * x) (y >>> 1) (res * x)
    else go (x * x) (y >>> 1) res
  termination_by y
  decreasing_by all_goals
    have : 1 < System.Platform.numBits := Nat.lt_of_lt_of_le (by decide) System.Platform.le_numBits
    simp [← USize.toNat_inj, Nat.mod_eq_of_lt this] at * <;> omega

instance : Pow UInt8 UInt8 := ⟨UInt8.hpow⟩
instance : Pow UInt16 UInt16 := ⟨UInt16.hpow⟩
instance : Pow UInt32 UInt32 := ⟨UInt32.hpow⟩
instance : Pow UInt64 UInt64 := ⟨UInt64.hpow⟩
instance : Pow USize USize := ⟨USize.hpow⟩

theorem UInt8.toBitVec_hpow (x y : UInt8) : (x ^ y).toBitVec = x.toBitVec ^ y.toBitVec := by
  change (UInt8.hpow.go x y 1).toBitVec = BitVec.hpow.go x.toBitVec y.toBitVec (1 : UInt8).toBitVec
  induction x, y, (1 : UInt8) using UInt8.hpow.go.induct_unfolding <;>
    rw [BitVec.hpow.go] <;> simp_all [← UInt8.toBitVec_inj]

theorem UInt16.toBitVec_hpow (x y : UInt16) : (x ^ y).toBitVec = x.toBitVec ^ y.toBitVec := by
  change (UInt16.hpow.go x y 1).toBitVec = BitVec.hpow.go x.toBitVec y.toBitVec (1 : UInt16).toBitVec
  induction x, y, (1 : UInt16) using UInt16.hpow.go.induct_unfolding <;>
    rw [BitVec.hpow.go] <;> simp_all [← UInt16.toBitVec_inj]

theorem UInt32.toBitVec_hpow (x y : UInt32) : (x ^ y).toBitVec = x.toBitVec ^ y.toBitVec := by
  change (UInt32.hpow.go x y 1).toBitVec = BitVec.hpow.go x.toBitVec y.toBitVec (1 : UInt32).toBitVec
  induction x, y, (1 : UInt32) using UInt32.hpow.go.induct_unfolding <;>
    rw [BitVec.hpow.go] <;> simp_all [← UInt32.toBitVec_inj]

theorem UInt64.toBitVec_hpow (x y : UInt64) : (x ^ y).toBitVec = x.toBitVec ^ y.toBitVec := by
  change (UInt64.hpow.go x y 1).toBitVec = BitVec.hpow.go x.toBitVec y.toBitVec (1 : UInt64).toBitVec
  induction x, y, (1 : UInt64) using UInt64.hpow.go.induct_unfolding <;>
    rw [BitVec.hpow.go] <;> simp_all [← UInt64.toBitVec_inj]

theorem USize.toBitVec_hpow (x y : USize) : (x ^ y).toBitVec = x.toBitVec ^ y.toBitVec := by
  change (USize.hpow.go x y 1).toBitVec = BitVec.hpow.go x.toBitVec y.toBitVec (1 : USize).toBitVec
  have : 1 < System.Platform.numBits := Nat.lt_of_lt_of_le (by decide) System.Platform.le_numBits
  induction x, y, (1 : USize) using USize.hpow.go.induct_unfolding <;>
    rw [BitVec.hpow.go] <;> simp_all [← USize.toBitVec_inj, Nat.mod_eq_of_lt this]

@[simp]
theorem UInt8.toBitVec_pow (x : UInt8) (n : Nat) : (x ^ n).toBitVec = x.toBitVec ^ n := by
  induction n <;> simp [UInt8.pow_succ, BitVec.pow_succ, *]

@[simp]
theorem UInt16.toBitVec_pow (x : UInt16) (n : Nat) : (x ^ n).toBitVec = x.toBitVec ^ n := by
  induction n <;> simp [UInt16.pow_succ, BitVec.pow_succ, *]

@[simp]
theorem UInt32.toBitVec_pow (x : UInt32) (n : Nat) : (x ^ n).toBitVec = x.toBitVec ^ n := by
  induction n <;> simp [UInt32.pow_succ, BitVec.pow_succ, *]

@[simp]
theorem UInt64.toBitVec_pow (x : UInt64) (n : Nat) : (x ^ n).toBitVec = x.toBitVec ^ n := by
  induction n <;> simp [UInt64.pow_succ, BitVec.pow_succ, *]

@[simp]
theorem USize.toBitVec_pow (x : USize) (n : Nat) : (x ^ n).toBitVec = x.toBitVec ^ n := by
  induction n <;> simp [USize.pow_succ, BitVec.pow_succ, *]

protected def UInt8.powImpl (x : UInt8) (n : Nat) : UInt8 :=
  if n < UInt8.size ∨ x &&& 1 = 1 then x ^ ofNat n else 0

protected def UInt16.powImpl (x : UInt16) (n : Nat) : UInt16 :=
  if n < UInt16.size ∨ x &&& 1 = 1 then x ^ ofNat n else 0

protected def UInt32.powImpl (x : UInt32) (n : Nat) : UInt32 :=
  if n < UInt32.size ∨ x &&& 1 = 1 then x ^ ofNat n else 0

protected def UInt64.powImpl (x : UInt64) (n : Nat) : UInt64 :=
  if n < UInt64.size ∨ x &&& 1 = 1 then x ^ ofNat n else 0

protected def USize.powImpl (x : USize) (n : Nat) : USize :=
  if n < USize.size ∨ x &&& 1 = 1 then x ^ ofNat n else 0

@[inline] protected def UInt8.instPowImpl : Pow UInt8 Nat := ⟨UInt8.powImpl⟩
@[inline] protected def UInt16.instPowImpl : Pow UInt16 Nat := ⟨UInt16.powImpl⟩
@[inline] protected def UInt32.instPowImpl : Pow UInt32 Nat := ⟨UInt32.powImpl⟩
@[inline] protected def UInt64.instPowImpl : Pow UInt64 Nat := ⟨UInt64.powImpl⟩
@[inline] protected def USize.instPowImpl : Pow USize Nat := ⟨USize.powImpl⟩

@[csimp]
theorem UInt8.pow_eq_powImpl : UInt8.pow = UInt8.powImpl := by
  funext x n; change x ^ n = _; rw [UInt8.powImpl]
  simpa [← UInt8.toBitVec_inj, apply_ite UInt8.toBitVec, UInt8.toBitVec_hpow] using
    BitVec.pow_eq_ite_lt_or_and_eq_one x.toBitVec n

@[csimp]
theorem UInt16.pow_eq_powImpl : UInt16.pow = UInt16.powImpl := by
  funext x n; change x ^ n = _; rw [UInt16.powImpl]
  simpa [← UInt16.toBitVec_inj, apply_ite UInt16.toBitVec, UInt16.toBitVec_hpow] using
    BitVec.pow_eq_ite_lt_or_and_eq_one x.toBitVec n

@[csimp]
theorem UInt32.pow_eq_powImpl : UInt32.pow = UInt32.powImpl := by
  funext x n; change x ^ n = _; rw [UInt32.powImpl]
  simpa [← UInt32.toBitVec_inj, apply_ite UInt32.toBitVec, UInt32.toBitVec_hpow] using
    BitVec.pow_eq_ite_lt_or_and_eq_one x.toBitVec n

@[csimp]
theorem UInt64.pow_eq_powImpl : UInt64.pow = UInt64.powImpl := by
  funext x n; change x ^ n = _; rw [UInt64.powImpl]
  simpa [← UInt64.toBitVec_inj, apply_ite UInt64.toBitVec, UInt64.toBitVec_hpow] using
    BitVec.pow_eq_ite_lt_or_and_eq_one x.toBitVec n

@[csimp]
theorem USize.pow_eq_powImpl : USize.pow = USize.powImpl := by
  funext x n; change x ^ n = _; rw [USize.powImpl]
  simpa [← USize.toBitVec_inj, apply_ite USize.toBitVec, USize.toBitVec_hpow] using
    BitVec.pow_eq_ite_lt_or_and_eq_one x.toBitVec n

@[csimp] theorem UInt8.instPow_eq_instPowImpl : instPowUInt8Nat = UInt8.instPowImpl := congrArg Pow.mk UInt8.pow_eq_powImpl
@[csimp] theorem UInt16.instPow_eq_instPowImpl : instPowUInt16Nat = UInt16.instPowImpl := congrArg Pow.mk UInt16.pow_eq_powImpl
@[csimp] theorem UInt32.instPow_eq_instPowImpl : instPowUInt32Nat = UInt32.instPowImpl := congrArg Pow.mk UInt32.pow_eq_powImpl
@[csimp] theorem UInt64.instPow_eq_instPowImpl : instPowUInt64Nat = UInt64.instPowImpl := congrArg Pow.mk UInt64.pow_eq_powImpl
@[csimp] theorem USize.instPow_eq_instPowImpl : instPowUSizeNat = USize.instPowImpl := congrArg Pow.mk USize.pow_eq_powImpl
