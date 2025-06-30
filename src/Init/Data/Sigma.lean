/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robin Arnez
-/
module

prelude
public import Init.SimpLemmas
public import Init.NotationExtra

public section

namespace Sigma

variable {α : Type u} {β : α → Type v}

@[simp]
protected theorem «forall» {p : (a : α) × β a → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b => h ⟨a, b⟩, fun h ⟨a, b⟩ => h a b⟩

@[simp]
protected theorem «exists» {p : (a : α) × β a → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩⟩

end Sigma
