/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Control.Lawful.Basic
import Init.RCases
import Init.ByCases

-- Mapping by a function with a left inverse is injective.
theorem map_inj_of_left_inverse [Functor m] [LawfulFunctor m] {f : α → β}
    (w : ∃ g : β → α, ∀ x, g (f x) = x) {x y : m α} :
    f <$> x = f <$> y ↔ x = y := by
  rcases w with ⟨g, w⟩
  constructor
  · intro h
    replace h := congrArg (g <$> ·) h
    simpa [w] using h
  · intro h
    rw [h]

-- Mapping by an injective function is injective, as long as the domain is nonempty.
theorem map_inj_of_nonempty [Functor m] [LawfulFunctor m] [Nonempty α] {f : α → β}
    (w : ∀ x y, f x = f y → x = y) {x y : m α} :
    f <$> x = f <$> y ↔ x = y := by
  apply map_inj_of_left_inverse ?_
  let ⟨a⟩ := ‹Nonempty α›
  refine ⟨?_, ?_⟩
  · intro b
    by_cases p : ∃ a, f a = b
    · exact Exists.choose p
    · exact a
  · intro b
    simp only [exists_apply_eq_apply, ↓reduceDIte]
    apply w
    apply Exists.choose_spec (p := fun a => f a = f b)

theorem map_inj_of_inj [Monad m] [LawfulMonad m] {f : α → β}
    (w : ∀ x y, f x = f y → x = y) {x y : m α} :
    f <$> x = f <$> y ↔ x = y := by
  by_cases h' : Nonempty α
  · exact map_inj_of_nonempty w
  · have this (z : m α) : z = (do let a ← z; let b ← pure (f a); x) := by
      conv => lhs; rw [← bind_pure z]
      congr; funext; exact (h' ⟨‹α›⟩).elim
    constructor
    · intro h
      rw [this x, this y, ← bind_assoc, ← bind_assoc]
      rw [← map_eq_pure_bind, ← map_eq_pure_bind, h]
    · intro h
      rw [h]
