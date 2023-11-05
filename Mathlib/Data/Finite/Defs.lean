/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Logic.Equiv.Basic

#align_import data.finite.defs from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Definition of the `Finite` typeclass

This file defines a typeclass `Finite` saying that `α : Sort*` is finite. A type is `Finite` if it
is equivalent to `Fin n` for some `n`. We also define `Infinite α` as a typeclass equivalent to
`¬Finite α`.

The `Finite` predicate has no computational relevance and, being `Prop`-valued, gets to enjoy proof
irrelevance -- it represents the mere fact that the type is finite.  While the `Finite` class also
represents finiteness of a type, a key difference is that a `Fintype` instance represents finiteness
in a computable way: it gives a concrete algorithm to produce a `Finset` whose elements enumerate
the terms of the given type. As such, one generally relies on congruence lemmas when rewriting
expressions involving `Fintype` instances.

Every `Fintype` instance automatically gives a `Finite` instance, see `Fintype.finite`, but not vice
versa. Every `Fintype` instance should be computable since they are meant for computation. If it's
not possible to write a computable `Fintype` instance, one should prefer writing a `Finite` instance
instead.

## Main definitions

* `Finite α` denotes that `α` is a finite type.
* `Infinite α` denotes that `α` is an infinite type.

## Implementation notes

The definition of `Finite α` is not just `Nonempty (Fintype α)` since `Fintype` requires
that `α : Type*`, and the definition in this module allows for `α : Sort*`. This means
we can write the instance `Finite.prop`.

## Tags

finite, fintype
-/


universe u v

open Function

variable {α β : Sort*}

/-- A type is `Finite` if it is in bijective correspondence to some
`Fin n`.

While this could be defined as `Nonempty (Fintype α)`, it is defined
in this way to allow there to be `Finite` instances for propositions.
-/
class inductive Finite (α : Sort*) : Prop
  | intro {n : ℕ} : α ≃ Fin n → Finite _

theorem finite_iff_exists_equiv_fin {α : Sort*} : Finite α ↔ ∃ n, Nonempty (α ≃ Fin n) :=
  ⟨fun ⟨e⟩ => ⟨_, ⟨e⟩⟩, fun ⟨_, ⟨e⟩⟩ => ⟨e⟩⟩

theorem Finite.exists_equiv_fin (α : Sort*) [h : Finite α] : ∃ n : ℕ, Nonempty (α ≃ Fin n) :=
  finite_iff_exists_equiv_fin.mp h

theorem Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) : Finite β := by
  cases' h with n e
  exact Finite.intro (f.symm.trans e)

theorem Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β :=
  ⟨fun _ => Finite.of_equiv _ f, fun _ => Finite.of_equiv _ f.symm⟩

theorem Function.Bijective.finite_iff {f : α → β} (h : Bijective f) : Finite α ↔ Finite β :=
  (Equiv.ofBijective f h).finite_iff

theorem Finite.ofBijective [Finite α] {f : α → β} (h : Bijective f) : Finite β :=
  h.finite_iff.mp ‹_›

instance [Finite α] : Finite (PLift α) :=
  Finite.of_equiv α Equiv.plift.symm

instance {α : Type v} [Finite α] : Finite (ULift.{u} α) :=
  Finite.of_equiv α Equiv.ulift.symm

/-- A type is said to be infinite if it is not finite. Note that `Infinite α` is equivalent to
`IsEmpty (Fintype α)` or `IsEmpty (Finite α)`. -/
class Infinite (α : Sort*) : Prop where
  /-- assertion that `α` is `¬Finite`-/
  not_finite : ¬Finite α

@[simp]
theorem not_finite_iff_infinite : ¬Finite α ↔ Infinite α :=
  ⟨Infinite.mk, fun h => h.1⟩

@[simp]
theorem not_infinite_iff_finite : ¬Infinite α ↔ Finite α :=
  not_finite_iff_infinite.not_right.symm

theorem Equiv.infinite_iff (e : α ≃ β) : Infinite α ↔ Infinite β :=
  not_finite_iff_infinite.symm.trans <| e.finite_iff.not.trans not_finite_iff_infinite

instance [Infinite α] : Infinite (PLift α) :=
  Equiv.plift.infinite_iff.2 ‹_›

instance {α : Type v} [Infinite α] : Infinite (ULift.{u} α) :=
  Equiv.ulift.infinite_iff.2 ‹_›

theorem finite_or_infinite (α : Sort*) : Finite α ∨ Infinite α :=
  or_iff_not_imp_left.2 not_finite_iff_infinite.1

/-- `Infinite α` is not `Finite`-/
theorem not_finite (α : Sort*) [Infinite α] [Finite α] : False :=
  @Infinite.not_finite α ‹_› ‹_›

protected theorem Finite.false [Infinite α] (_ : Finite α) : False :=
  not_finite α

protected theorem Infinite.false [Finite α] (_ : Infinite α) : False :=
  @Infinite.not_finite α ‹_› ‹_›

alias ⟨Finite.of_not_infinite, Finite.not_infinite⟩ := not_infinite_iff_finite
