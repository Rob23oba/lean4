/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Wojciech Nawrocki, Leonardo de Moura, Mario Carneiro, Alex Keizer, Harun Khan, Abdalrhman M Mohamed
-/
module

prelude
public import Init.Data.Fin.Basic

public section

set_option linter.missingDocs true

/-!
This module exists to provide the very basic `BitVec` definitions required for
`Init.Data.UInt.BasicAux`.
-/

namespace BitVec

section Nat

/--
The bitvector with value `i mod 2^n`.
-/
@[expose, match_pattern]
protected def ofNat (n : Nat) (i : Nat) : BitVec n where
  toFin := Fin.ofNat (2^n) i

instance instOfNat : OfNat (BitVec n) i where ofNat := .ofNat n i

/-- Return the bound in terms of toNat. -/
theorem isLt (x : BitVec w) : x.toNat < 2^w := x.toFin.isLt

grind_pattern isLt => x.toNat, 2^w

end Nat

section arithmetic

/--
Adds two bitvectors. This can be interpreted as either signed or unsigned addition modulo `2^n`.
Usually accessed via the `+` operator.

SMT-LIB name: `bvadd`.
-/
@[expose]
protected def add (x y : BitVec n) : BitVec n := .ofNat n (x.toNat + y.toNat)
instance : Add (BitVec n) := ⟨BitVec.add⟩

/--
Subtracts one bitvector from another. This can be interpreted as either signed or unsigned subtraction
modulo `2^n`. Usually accessed via the `-` operator.

-/
@[expose]
protected def sub (x y : BitVec n) : BitVec n := .ofNat n ((2^n - y.toNat) + x.toNat)
instance : Sub (BitVec n) := ⟨BitVec.sub⟩

end arithmetic

end BitVec
