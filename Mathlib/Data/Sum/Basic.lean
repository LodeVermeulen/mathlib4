/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
import Mathlib.Logic.Function.Basic

#align_import data.sum.basic from "leanprover-community/mathlib"@"bd9851ca476957ea4549eb19b40e7b5ade9428cc"

/-!
# Additional lemmas about sum types

Most of the former contents of this file have been moved to Std.
-/


universe u v w x

variable {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {γ δ : Type*}

namespace Sum


theorem exists_sum {γ : α ⊕ β → Sort*} (p : (∀ ab, γ ab) → Prop) :
    (∃ fab, p fab) ↔ (∃ fa fb, p (Sum.rec fa fb)) := by
  rw [← not_forall_not, forall_sum]
  simp

theorem inl_injective : Function.Injective (inl : α → Sum α β) := fun _ _ ↦ inl.inj

theorem inr_injective : Function.Injective (inr : β → Sum α β) := fun _ _ ↦ inr.inj

theorem sum_rec_congr (P : α ⊕ β → Sort*) (f : ∀ i, P (inl i)) (g : ∀ i, P (inr i))
    {x y : α ⊕ β} (h : x = y) :
    @Sum.rec _ _ _ f g x = cast (congr_arg P h.symm) (@Sum.rec _ _ _ f g y) := by cases h; rfl

section get


variable {x y : Sum α β}


theorem eq_left_iff_getLeft_eq {a : α} : x = inl a ↔ ∃ h, x.getLeft h = a := by
  cases x <;> simp

theorem eq_right_iff_getRight_eq {b : β} : x = inr b ↔ ∃ h, x.getRight h = b := by
  cases x <;> simp


theorem getLeft_eq_getLeft? (h₁ : x.isLeft) (h₂ : x.getLeft?.isSome) :
    x.getLeft h₁ = x.getLeft?.get h₂ := by simp [← getLeft?_eq_some_iff]

theorem getRight_eq_getRight? (h₁ : x.isRight) (h₂ : x.getRight?.isSome) :
    x.getRight h₁ = x.getRight?.get h₂ := by simp [← getRight?_eq_some_iff]


@[simp] theorem isSome_getLeft?_iff_isLeft : x.getLeft?.isSome ↔ x.isLeft := by
  rw [isLeft_iff, Option.isSome_iff_exists]; simp

@[simp] theorem isSome_getRight?_iff_isRight : x.getRight?.isSome ↔ x.isRight := by
  rw [isRight_iff, Option.isSome_iff_exists]; simp

end get


open Function (update update_eq_iff update_comp_eq_of_injective update_comp_eq_of_forall_ne)

@[simp]
theorem update_elim_inl [DecidableEq α] [DecidableEq (Sum α β)] {f : α → γ} {g : β → γ} {i : α}
    {x : γ} : update (Sum.elim f g) (inl i) x = Sum.elim (update f i x) g :=
  update_eq_iff.2 ⟨by simp, by simp (config := { contextual := true })⟩

@[simp]
theorem update_elim_inr [DecidableEq β] [DecidableEq (Sum α β)] {f : α → γ} {g : β → γ} {i : β}
    {x : γ} : update (Sum.elim f g) (inr i) x = Sum.elim f (update g i x) :=
  update_eq_iff.2 ⟨by simp, by simp (config := { contextual := true })⟩

@[simp]
theorem update_inl_comp_inl [DecidableEq α] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α}
    {x : γ} : update f (inl i) x ∘ inl = update (f ∘ inl) i x :=
  update_comp_eq_of_injective _ inl_injective _ _

@[simp]
theorem update_inl_apply_inl [DecidableEq α] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i j : α}
    {x : γ} : update f (inl i) x (inl j) = update (f ∘ inl) i x j := by
  rw [← update_inl_comp_inl, Function.comp_apply]

@[simp]
theorem update_inl_comp_inr [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α} {x : γ} :
    update f (inl i) x ∘ inr = f ∘ inr :=
  (update_comp_eq_of_forall_ne _ _) fun _ ↦ inr_ne_inl

theorem update_inl_apply_inr [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α} {j : β} {x : γ} :
    update f (inl i) x (inr j) = f (inr j) :=
  Function.update_noteq inr_ne_inl _ _

@[simp]
theorem update_inr_comp_inl [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : β} {x : γ} :
    update f (inr i) x ∘ inl = f ∘ inl :=
  (update_comp_eq_of_forall_ne _ _) fun _ ↦ inl_ne_inr

theorem update_inr_apply_inl [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α} {j : β} {x : γ} :
    update f (inr j) x (inl i) = f (inl i) :=
  Function.update_noteq inl_ne_inr _ _

@[simp]
theorem update_inr_comp_inr [DecidableEq β] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : β}
    {x : γ} : update f (inr i) x ∘ inr = update (f ∘ inr) i x :=
  update_comp_eq_of_injective _ inr_injective _ _

@[simp]
theorem update_inr_apply_inr [DecidableEq β] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i j : β}
    {x : γ} : update f (inr i) x (inr j) = update (f ∘ inr) i x j := by
  rw [← update_inr_comp_inr, Function.comp_apply]


@[simp]
theorem swap_leftInverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap

@[simp]
theorem swap_rightInverse : Function.RightInverse (@swap α β) swap :=
  swap_swap


section LiftRel


end LiftRel

section Lex


end Lex

end Sum

open Sum

namespace Function

theorem Injective.sum_elim {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (hfg : ∀ a b, f a ≠ g b) : Injective (Sum.elim f g)
  | inl _, inl _, h => congr_arg inl <| hf h
  | inl _, inr _, h => (hfg _ _ h).elim
  | inr _, inl _, h => (hfg _ _ h.symm).elim
  | inr _, inr _, h => congr_arg inr <| hg h

theorem Injective.sum_map {f : α → β} {g : α' → β'} (hf : Injective f) (hg : Injective g) :
    Injective (Sum.map f g)
  | inl _, inl _, h => congr_arg inl <| hf <| inl.inj h
  | inr _, inr _, h => congr_arg inr <| hg <| inr.inj h

theorem Surjective.sum_map {f : α → β} {g : α' → β'} (hf : Surjective f) (hg : Surjective g) :
    Surjective (Sum.map f g)
  | inl y =>
    let ⟨x, hx⟩ := hf y
    ⟨inl x, congr_arg inl hx⟩
  | inr y =>
    let ⟨x, hx⟩ := hg y
    ⟨inr x, congr_arg inr hx⟩

theorem Bijective.sum_map {f : α → β} {g : α' → β'} (hf : Bijective f) (hg : Bijective g) :
    Bijective (Sum.map f g) :=
  ⟨hf.injective.sum_map hg.injective, hf.surjective.sum_map hg.surjective⟩

end Function

namespace Sum

open Function

@[simp]
theorem map_injective {f : α → γ} {g : β → δ} :
    Injective (Sum.map f g) ↔ Injective f ∧ Injective g :=
  ⟨fun h =>
    ⟨fun a₁ a₂ ha => inl_injective <| @h (inl a₁) (inl a₂) (congr_arg inl ha : _), fun b₁ b₂ hb =>
      inr_injective <| @h (inr b₁) (inr b₂) (congr_arg inr hb : _)⟩,
    fun h => h.1.sum_map h.2⟩

@[simp]
theorem map_surjective {f : α → γ} {g : β → δ} :
    Surjective (Sum.map f g) ↔ Surjective f ∧ Surjective g :=
  ⟨ fun h => ⟨
      (fun c => by
        obtain ⟨a | b, h⟩ := h (inl c)
        · exact ⟨a, inl_injective h⟩
        · cases h),
      (fun d => by
        obtain ⟨a | b, h⟩ := h (inr d)
        · cases h
        · exact ⟨b, inr_injective h⟩)⟩,
    fun h => h.1.sum_map h.2⟩

@[simp]
theorem map_bijective {f : α → γ} {g : β → δ} :
    Bijective (Sum.map f g) ↔ Bijective f ∧ Bijective g :=
  (map_injective.and map_surjective).trans <| and_and_and_comm


theorem elim_update_left [DecidableEq α] [DecidableEq β] (f : α → γ) (g : β → γ) (i : α) (c : γ) :
    Sum.elim (Function.update f i c) g = Function.update (Sum.elim f g) (inl i) c := by
  ext x
  rcases x with x | x
  · by_cases h : x = i
    · subst h
      simp
    · simp [h]
  · simp

theorem elim_update_right [DecidableEq α] [DecidableEq β] (f : α → γ) (g : β → γ) (i : β) (c : γ) :
    Sum.elim f (Function.update g i c) = Function.update (Sum.elim f g) (inr i) c := by
  ext x
  rcases x with x | x
  · simp
  · by_cases h : x = i
    · subst h
      simp
    · simp [h]

end Sum

/-!
### Ternary sum

Abbreviations for the maps from the summands to `α ⊕ β ⊕ γ`. This is useful for pattern-matching.
-/

namespace Sum3

/-- The map from the first summand into a ternary sum. -/
@[match_pattern, simp, reducible]
def in₀ (a : α) : Sum α (Sum β γ) :=
  inl a

/-- The map from the second summand into a ternary sum. -/
@[match_pattern, simp, reducible]
def in₁ (b : β) : Sum α (Sum β γ) :=
  inr <| inl b

/-- The map from the third summand into a ternary sum. -/
@[match_pattern, simp, reducible]
def in₂ (c : γ) : Sum α (Sum β γ) :=
  inr <| inr c

end Sum3
