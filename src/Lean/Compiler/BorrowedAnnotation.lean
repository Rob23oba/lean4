/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Expr

public section
namespace Lean

def markBorrowed (e : Expr) : Expr :=
  mkAnnotation `borrowed e

def isMarkedBorrowed (e : Expr) : Bool :=
  annotation? `borrowed e |>.isSome

/--
`borrowedReturn` is used to mark return values that are borrowed. This only applies to object return
values and should only occur in the impure phase or in the pure phase for externs. The bits in the
mask represent places the value can be borrowed from:

Bit 0 represents borrowing from the function declaration (as long as the function is alive, the
return value is too). This is used for persistent values from the same module as the function
declaration where the function and the persistent value could be deleted.

Bit 1 represents borrowing from the last parameter, bit 2 from the second to last and so on.
-/
@[expose, match_pattern]
def markBorrowedReturn (mask : Nat) (e : Expr) : Expr :=
  .mdata ⟨[(`borrowedReturn, .ofNat mask)]⟩ e

end Lean
