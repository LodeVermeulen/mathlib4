/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Multiset.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Set.Pointwise.Basic

/-!
# To move
-/

section AddMonoidWithOne
variable (R : Type*) [AddMonoidWithOne R] [IsRightCancelAdd R] (p : ℕ) [CharP R p]

lemma CharP.natCast_injOn_Iio : (Set.Iio p).InjOn ((↑) : ℕ → R) :=
  fun _a ha _b hb hab ↦ ((natCast_eq_natCast _ _).1 hab).eq_of_lt_of_lt ha hb

end AddMonoidWithOne

namespace Finset
variable {α β : Type*} {A : Finset α} {B : Finset β}

/-- Reorder a finset.

The difference with `Finset.card_bij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.card_nbij` is that the bijection is allowed to use membership of the
domain, rather than being a non-dependent function. -/
lemma card_bij (i : ∀ a ∈ A, β) (hi : ∀ a ha, i a ha ∈ B)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ B, ∃ a ha, i a ha = b) : A.card = B.card := by
  classical
  calc
    A.card = A.attach.card := card_attach.symm
    _      = (A.attach.image fun a : { a // a ∈ A } => i a.1 a.2).card := Eq.symm ?_
    _      = B.card := ?_
  · apply card_image_of_injective
    intro ⟨_, _⟩ ⟨_, _⟩ h
    simpa using i_inj _ _ _ _ h
  · congr 1
    ext b
    constructor <;> intro h
    · obtain ⟨_, _, rfl⟩ := mem_image.1 h; apply hi
    · obtain ⟨a, ha, rfl⟩ := i_surj b h; exact mem_image.2 ⟨⟨a, ha⟩, by simp⟩

/-- Reorder a finset.

The difference with `Finset.card_bij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.card_nbij'` is that the bijection and its inverse are allowed to use
membership of the domains, rather than being non-dependent functions. -/
lemma card_bij' (i : ∀ a ∈ A, β) (j : ∀ a ∈ B, α) (hi : ∀ a ha, i a ha ∈ B)
    (hj : ∀ a ha, j a ha ∈ A) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) : A.card = B.card := by
  refine card_bij i hi (fun a1 h1 a2 h2 eq ↦ ?_) (fun b hb ↦ ⟨_, hj b hb, right_inv b hb⟩)
  rw [← left_inv a1 h1, ← left_inv a2 h2]
  simp only [eq]

/-- Reorder a finset.

The difference with `Finset.card_nbij'` is that the bijection is specified as a surjective
injection, rather than by an inverse function.

The difference with `Finset.card_bij` is that the bijection is a non-dependent function, rather than
being allowed to use membership of the domain. -/
lemma card_nbij (i : α → β) (hi : ∀ a ∈ A, i a ∈ B) (i_inj : (A : Set α).InjOn i)
    (i_surj : (A : Set α).SurjOn i B) : A.card = B.card :=
  card_bij (fun a _ ↦ i a) hi i_inj (by simpa using i_surj)

/-- Reorder a finset.

The difference with `Finset.card_nbij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.card_bij'` is that the bijection and its inverse are non-dependent
functions, rather than being allowed to use membership of the domains.

The difference with `Finset.card_equiv` is that bijectivity is only required to hold on the domains,
rather than on the entire types. -/
lemma card_nbij' (i : α → β) (j : β → α) (hi : ∀ a ∈ A, i a ∈ B) (hj : ∀ a ∈ B, j a ∈ A)
    (left_inv : ∀ a ∈ A, j (i a) = a) (right_inv : ∀ a ∈ B, i (j a) = a) : A.card = B.card :=
  card_bij' (fun a _ ↦ i a) (fun b _ ↦ j b) hi hj left_inv right_inv

/-- Specialization of `Finset.card_nbij'` that automatically fills in most arguments.

See `Fintype.card_equiv` for the version where `A` and `B` are `univ`. -/
lemma card_equiv (e : α ≃ β) (hst : ∀ i, i ∈ A ↔ e i ∈ B) : A.card = B.card := by
  refine card_nbij' e e.symm ?_ ?_ ?_ ?_ <;> simp [hst]

/-- Specialization of `Finset.card_bij` that automatically fills in most arguments.

See `Fintype.card_bijective` for the version where `A` and `B` are `univ`. -/
lemma card_bijective (e : α → β) (he : e.Bijective) (hst : ∀ i, i ∈ A ↔ e i ∈ B) :
    A.card = B.card := card_equiv (.ofBijective e he) hst

end Finset
