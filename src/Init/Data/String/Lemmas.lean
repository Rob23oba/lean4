/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Robin Arnez
-/
module

prelude
public import Init.Data.Char.Lemmas
public import Init.Data.List.Lex
public import all Init.Data.String.Basic
public import Init.Grind

public section

namespace String

protected theorem data_eq_of_eq {a b : String} (h : a = b) : a.data = b.data :=
  h ▸ rfl
protected theorem ne_of_data_ne {a b : String} (h : a.data ≠ b.data) : a ≠ b :=
  fun h' => absurd (String.data_eq_of_eq h') h

@[simp] protected theorem not_le {a b : String} : ¬ a ≤ b ↔ b < a := Decidable.not_not
@[simp] protected theorem not_lt {a b : String} : ¬ a < b ↔ b ≤ a := Iff.rfl
@[simp] protected theorem le_refl (a : String) : a ≤ a := List.le_refl _
@[simp] protected theorem lt_irrefl (a : String) : ¬ a < a := List.lt_irrefl _

attribute [local instance] Char.notLTTrans Char.notLTAntisymm Char.notLTTotal

protected theorem le_trans {a b c : String} : a ≤ b → b ≤ c → a ≤ c := List.le_trans
protected theorem lt_trans {a b c : String} : a < b → b < c → a < c := List.lt_trans
protected theorem le_total (a b : String) : a ≤ b ∨ b ≤ a := List.le_total _ _
protected theorem le_antisymm {a b : String} : a ≤ b → b ≤ a → a = b := fun h₁ h₂ => ext (List.le_antisymm (as := a.data) (bs := b.data) h₁ h₂)
protected theorem lt_asymm {a b : String} (h : a < b) : ¬ b < a := List.lt_asymm h
protected theorem ne_of_lt {a b : String} (h : a < b) : a ≠ b := by
  have := String.lt_irrefl a
  intro h; subst h; contradiction

theorem append_eq (s₁ s₂ : String) : s₁ ++ s₂ = ⟨s₁.data ++ s₂.data⟩ := rfl

@[simp] theorem byteIdx_endPos (s : String) : s.endPos.byteIdx = s.utf8ByteSize := rfl
@[simp] theorem utf8ByteSize_empty : "".utf8ByteSize = 0 := rfl

@[simp]
theorem mk_eq_empty_iff (l : List Char) : String.mk l = "" ↔ l = [] := by
  rw [String.mk.injEq]

theorem eq_empty_iff_utf8ByteSize_eq_zero (s : String) : s = "" ↔ s.utf8ByteSize = 0 := by
  rcases s with ⟨_ | ⟨_, _⟩⟩ <;> simp [utf8ByteSize, utf8ByteSize.go]

theorem eq_empty_iff_length_eq_zero (s : String) : s = "" ↔ s.length = 0 := by
  rcases s with ⟨_ | ⟨_, _⟩⟩ <;> simp

@[simp] theorem Pos.add_zero (p : Pos) : p + 0 = p := rfl
@[simp] theorem Pos.zero_add (p : Pos) : 0 + p = p := by simp [Pos.ext_iff]

@[simp] theorem Pos.zero_eq_iff (p : Pos) : 0 = p ↔ p = 0 := eq_comm

@[simp] theorem Pos.add_eq_zero_iff (p₁ p₂ : Pos) : p₁ + p₂ = 0 ↔ p₁ = 0 ∧ p₂ = 0 := by simp [ext_iff]
@[simp] theorem Pos.addChar_ne_zero (p : Pos) (c : Char) : p + c ≠ 0 := by simp [ext_iff]
@[simp] theorem Pos.addString_eq_zero_iff (p : Pos) (s : String) : p + s = 0 ↔ p = 0 ∧ s = "" := by
  simp [ext_iff, eq_empty_iff_utf8ByteSize_eq_zero]

@[simp] theorem Pos.addString_empty (p : Pos) : p + "" = p := rfl

@[simp] theorem nthPosAux_zero (cs : List Char) : nthPosAux cs 0 = 0 := rfl
@[simp] theorem nthPosAux_nil (i : Nat) : nthPosAux [] i = ⟨i⟩ := by cases i <;> rfl

@[simp]
theorem nthPosAux_cons_add_one (c : Char) (cs : List Char) :
    nthPosAux (c :: cs) (i + 1) = nthPosAux cs i + c := rfl

theorem nthPos_zero (s : String) : s.nthPos 0 = 0 := rfl
theorem nthPos_empty (i : Nat) : "".nthPos i = ⟨i⟩ := by cases i <;> rfl

theorem nthPos_mk_cons_add_one (c : Char) (l : List Char) (i : Nat) :
    nthPos ⟨c :: l⟩ (i + 1) = nthPos ⟨l⟩ i + c := by
  rfl

theorem nthPos_append_add_length (s₁ s₂ : String) (i : Nat) :
    nthPos (s₁ ++ s₂) (i + s₁.length) = nthPos s₂ i + s₁ := by
  rcases s₁ with ⟨cs⟩
  induction cs <;> simp_all [nthPos, ← Nat.add_assoc, Pos.ext_iff, utf8ByteSize, utf8ByteSize.go]

theorem nthPos_length {s : String} : s.nthPos s.length = s.endPos := by
  rcases s with ⟨cs⟩
  simp only [length_mk, endPos, utf8ByteSize]
  induction cs <;> simp_all [utf8ByteSize.go, Pos.addChar_eq, nthPos]

theorem utf8ByteSize_eq_byteIdx_nthPos_length (s : String) :
    s.utf8ByteSize = (s.nthPos s.length).byteIdx :=
  congrArg Pos.byteIdx nthPos_length.symm

theorem nthPos_of_length_le {s : String} {i : Nat} (h : s.length ≤ i) :
    s.nthPos i = ⟨s.utf8ByteSize + i - s.length⟩ := by
  obtain ⟨a, rfl⟩ := h.dest; clear h
  rw (occs := .pos [1]) [← append_empty s, Nat.add_comm, nthPos_append_add_length, nthPos_empty]
  simp [Pos.ext_iff, Nat.add_comm _ a, ← Nat.add_assoc]

@[simp]
theorem nthPos_le_nthPos_iff {s : String} {a b : Nat} :
    (nthPos s a).byteIdx ≤ (nthPos s b).byteIdx ↔ a ≤ b := by
  dsimp [nthPos]
  induction s.data generalizing a b with
  | nil => simp
  | cons ch cs ih => cases a <;> cases b <;> simp_all

@[simp]
theorem nthPos_lt_nthPos_iff {s : String} {a b : Nat} :
    (s.nthPos a).byteIdx < (s.nthPos b).byteIdx ↔ a < b := by
  simp [← Nat.not_le]

@[simp]
theorem nthPos_inj' {s : String} {a b : Nat} :
    (nthPos s a).byteIdx = (nthPos s b).byteIdx ↔ a = b := by
  simp [Nat.le_antisymm_iff]

@[simp]
theorem nthPos_inj {s : String} {a b : Nat} :
    s.nthPos a = s.nthPos b ↔ a = b := by
  simp [Pos.ext_iff]

@[simp]
theorem nthPos_eq_zero_iff {s : String} {a : Nat} :
    s.nthPos a = 0 ↔ a = 0 :=
  nthPos_inj (b := 0)

@[simp]
theorem nthPos_eq_zero_iff' {s : String} {a : Nat} :
    (s.nthPos a).byteIdx = 0 ↔ a = 0 :=
  nthPos_inj' (b := 0)

@[simp]
theorem nthPos_pos_iff {s : String} {a : Nat} :
    0 < (s.nthPos a).byteIdx ↔ 0 < a :=
  nthPos_lt_nthPos_iff (a := 0)

theorem posToIdxAux?_eq_some_iff {cs : List Char} {i p : Pos} :
    posToIdxAux? cs i p = some n ↔ n < cs.length ∧ nthPosAux cs n + i = p := by
  fun_induction posToIdxAux? generalizing n <;> cases n <;> simp_all +arith [Pos.ext_iff]

@[simp]
theorem posToIdx?_eq_some_iff (s : String) (p : Pos) :
    posToIdx? s p = some n ↔ n < s.length ∧ s.nthPos n = p := by
  simpa using posToIdxAux?_eq_some_iff (i := 0)

@[simp]
theorem posToIdx?_eq_none_iff (s : String) (p : Pos) :
    posToIdx? s p = none ↔ ∀ n, s.nthPos n = p → s.length ≤ n := by
  simp [Option.eq_none_iff_forall_ne_some, @imp_not_comm (_ < s.length)]

@[simp]
theorem isSome_posToIdx?_iff (s : String) (p : Pos) :
    (posToIdx? s p).isSome ↔ ∃ n, n < s.length ∧ s.nthPos n = p := by
  simp [Option.isSome_iff_exists]

@[simp] theorem posToIdx?_empty (p : Pos) : "".posToIdx? p = none := rfl

@[simp]
theorem posToIdx?_nthPos (s : String) (n : Nat) :
    s.posToIdx? (s.nthPos n) = if n < s.length then some n else none := by
  split <;> simp_all [Option.eq_none_iff_forall_ne_some, Pos.ext_iff, imp_not_comm]

theorem posToIdx?_of_nthPos_ne {s : String} {p : Pos} (h : ∀ i, s.nthPos i ≠ p) :
    s.posToIdx? p = none := by
  simp [Option.eq_none_iff_forall_ne_some, h]

theorem posToIdx?_mk_cons_addChar (c : Char) (cs : List Char) (p : Pos) :
    posToIdx? ⟨c :: cs⟩ (p + c) = (posToIdx? ⟨cs⟩ p).map (· + 1) := by
  ext (_ | _) <;> simp [Pos.ext_iff, nthPos, eq_comm (a := 0)]

theorem posToIdx?_append_addString (s₁ s₂ : String) (p : Pos) :
    posToIdx? (s₁ ++ s₂) (p + s₁) = (posToIdx? s₂ p).map (· + s₁.length) := by
  rcases s₁ with ⟨cs⟩
  have := posToIdx?_mk_cons_addChar
  induction cs <;> simp_all [Pos.addString_eq, utf8ByteSize, utf8ByteSize.go, append_eq,
    ← Nat.add_assoc, Pos.addChar_eq, Function.comp_def]

theorem utf8GetAux_eq_posToIdxAux? :
    utf8GetAux s p p' = (posToIdxAux? s p p').elim default (s[·]!) := by
  fun_induction utf8GetAux <;> simp [*, posToIdxAux?]

theorem get_eq_posToIdx? :
    get s p = (posToIdx? s p).elim default (s.data[·]!) :=
  utf8GetAux_eq_posToIdxAux?

@[simp]
theorem get_nthPos (s : String) (n : Nat) : s.get (s.nthPos n) = s.data[n]! := by
  grind [get_eq_posToIdx?, posToIdx?_nthPos, length]

@[simp]
theorem get_zero (s : String) : s.get 0 = s.data[0]! := by
  rw [← s.nthPos_zero, String.get_nthPos]

/- LHS is the `simp` normal form of `s.nthPos n + s.get (s.nthPos n)` -/
@[simp]
theorem nthPos_addChar_get (s : String) (n : Nat) :
    s.nthPos n + s.data[n]?.getD 'A' = s.nthPos (n + 1) := by
  simp only [nthPos]
  induction s.data generalizing n <;> cases n <;> try rfl
  · rename_i ch _ ih n
    simpa +arith [Pos.ext_iff] using congrArg (· + ch) (ih n)

@[simp]
theorem next_nthPos (s : String) (n : Nat) :
    s.next (s.nthPos n) = s.nthPos (n + 1) := by
  simp [next]

@[simp]
theorem atEnd_nthPos (s : String) (n : Nat) :
    s.atEnd (s.nthPos n) = decide (s.length ≤ n) := by
  simp [atEnd, ge_iff_le, utf8ByteSize_eq_byteIdx_nthPos_length]

@[simp]
theorem get'_nthPos {s : String} {n : Nat} (h : ¬s.atEnd (s.nthPos n)) :
    s.get' (s.nthPos n) h = s.data[n]'(by simpa using h) := by
  simp only [atEnd_nthPos, decide_eq_true_eq, Nat.not_le, String.length] at h
  simp_all [get'_eq]

theorem Pos.isValid.go_iff_posToIdx? (cs : List Char) (i p : Pos) :
    go p cs i ↔ (posToIdxAux? cs i p).isSome ∨ p.byteIdx = i.byteIdx + utf8ByteSize.go cs := by
  fun_induction go <;> simp_all +arith [posToIdxAux?, utf8ByteSize.go, Pos.ext_iff, eq_comm (a := p.byteIdx)]

theorem Pos.isValid_iff_posToIdx? (s : String) (p : Pos) :
    p.isValid s ↔ (s.posToIdx? p).isSome ∨ p = s.endPos := by
  simp [isValid, isValid.go_iff_posToIdx?, Pos.ext_iff, posToIdx?, utf8ByteSize]

theorem Pos.isValid_iff (s : String) (p : Pos) :
    p.isValid s ↔ ∃ i, i ≤ s.length ∧ p = s.nthPos i := by
  grind [nthPos_length, isValid_iff_posToIdx?, isSome_posToIdx?_iff, ext_iff]

theorem utf8SetAux_eq_posToIdx? (cs : List Char) (i p : Pos) (ch : Char) :
    utf8SetAux ch cs i p = (posToIdxAux? cs i p).elim cs (cs.set · ch) := by
  fun_induction utf8SetAux <;> simp [posToIdxAux?, Option.apply_elim (List.cons _), *]

theorem set_eq_posToIdx? (s : String) (p : Pos) (ch : Char) :
    s.set p ch = (posToIdx? s p).elim s (⟨s.data.set · ch⟩) := by
  simp only [set, utf8SetAux_eq_posToIdx?, Option.apply_elim String.mk, posToIdx?]

@[simp]
theorem String.set_nthPos (s : String) (n : Nat) (ch : Char) :
    s.set (s.nthPos n) ch = ⟨s.data.set n ch⟩ := by
  simp only [set_eq_posToIdx?, posToIdx?_nthPos, String.length]
  grind [List.set_eq_of_length_le, cases String]

theorem utf8PrevAux_nthPos (cs : List Char) (p : Pos) (n : Nat) :
    utf8PrevAux cs p (p + (String.mk cs).nthPos (n + 1)) = p + (String.mk cs).nthPos n := by
  rcases cs with _ | ⟨c, cs⟩
  · simp [utf8PrevAux, Pos.add_eq, nthPos]
  · simp only [utf8PrevAux, nthPos_mk_cons_add_one]
    split
    · simp_all +arith [nthPos_zero]
    · rename_i h
      replace h : 0 < n := by simpa [Pos.le_iff] using h
      let k + 1 := n
      simpa +arith [Pos.add_eq, Pos.addChar_eq, nthPos_mk_cons_add_one]
        using String.utf8PrevAux_nthPos cs (p + c) k

@[simp]
theorem String.prev_nthPos (s : String) (n : Nat) :
    s.prev (s.nthPos n) = s.nthPos (n - 1) := by
  rcases n with _ | k
  · simp [nthPos]
  rw [String.prev, ← Pos.zero_add (s.nthPos _), String.utf8PrevAux_nthPos]
  simp

/--
Runtime implementation of `String.nthPos`.
-/
def nthPosImpl (s : String) (n : Nat) : Pos :=
  go n 0
where
  go (n : Nat) (p : Pos) : Pos :=
    match n with
    | 0 => p
    | k + 1 =>
      if h : s.atEnd p then
        ⟨p.byteIdx + k + 1⟩
      else
        go k (s.next' p h)

theorem nthPosImpl.go_nthPos {s : String} {n i : Nat} (h : i ≤ s.length) :
    go s n (s.nthPos i) = s.nthPos (i + n) := by
  match n with
  | 0 => rfl
  | k + 1 =>
    simp only [go, atEnd_nthPos, decide_eq_true_eq, next'_eq, next_nthPos, dite_eq_ite]
    split
    · grind [nthPos_of_length_le]
    · have := @nthPosImpl.go_nthPos s k (i + 1)
      grind

@[csimp]
theorem nthPos_eq_nthPosImpl : @nthPos = @nthPosImpl := by
  funext s n
  rw [nthPosImpl, ← nthPos_zero, nthPosImpl.go_nthPos (Nat.zero_le _), Nat.zero_add]

theorem atEnd_empty : "".atEnd p := by
  simp [atEnd]

/--
Runtime implementation of `String.posToIdx?`.
-/
def posToIdxImpl? (s : String) (p : Pos) : Option Nat :=
  if h : s.atEnd p then none
  else go 0 0 rfl (by grind [← eq_empty_iff_length_eq_zero, atEnd_empty]) h (by simp)
where
  go (n : Nat) (i : Pos) (hi : i = s.nthPos n) (hn : n ≤ s.length) (hp : ¬s.atEnd p)
      (hp2 : p < i → s.posToIdx? p = none) : Option Nat :=
    if h : i < p then
      have : n < s.length := Nat.lt_of_le_of_ne hn (by grind [atEnd, nthPos_length, pos_lt_eq, byteIdx_endPos])
      go (n + 1) (s.next' i (by simp_all)) (by simp_all) this hp (by simp_all; grind [nthPos_lt_nthPos_iff])
    else if p = i then
      some n
    else
      none
  termination_by s.utf8ByteSize - i.byteIdx
  decreasing_by
    have := (s.get i).utf8Size_pos
    grind [String.next, String.next', String.atEnd, Pos.addChar_byteIdx]

theorem posToIdxImpl?.go_nthPos {s : String} {p : Pos} {n : Nat} {i : Pos}
    (hi : i = s.nthPos n) (hn : n ≤ s.length) (hp : ¬s.atEnd p) (hp2 : p < i → s.posToIdx? p = none) :
    go s p n i hi hn hp hp2 = s.posToIdx? p := by
  symm; fun_induction go s p n i hi hn hp hp2 <;>
    simp_all [-posToIdx?_eq_none_iff, Pos.ext_iff, Nat.lt_of_le_of_ne]

@[csimp]
theorem posToIdx?_eq_posToIdxImpl? : @posToIdx? = @posToIdxImpl? := by
  funext s n; rw [posToIdxImpl?]
  split
  · simp only [posToIdx?_eq_none_iff]
    rintro _ rfl
    simp_all
  · rw [posToIdxImpl?.go_nthPos]

end String
