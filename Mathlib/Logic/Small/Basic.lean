/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic.PPWithUniv

#align_import logic.small.basic from "leanprover-community/mathlib"@"d012cd09a9b256d870751284dd6a29882b0be105"

/-!
# Small types

A type is `w`-small if there exists an equivalence to some `S : Type w`.

We provide a noncomputable model `Shrink α : Type w`, and `equivShrink α : α ≃ Shrink α`.

A subsingleton type is `w`-small for any `w`.

If `α ≃ β`, then `Small.{w} α ↔ Small.{w} β`.
-/

set_option autoImplicit true


universe u w v v'

/-- A type is `Small.{w}` if there exists an equivalence to some `S : Type w`.
-/
@[mk_iff, pp_with_univ]
class Small (α : Type v) : Prop where
  /-- If a type is `Small.{w}`, then there exists an equivalence with some `S : Type w` -/
  equiv_small : ∃ S : Type w, Nonempty (α ≃ S)

/-- Constructor for `Small α` from an explicit witness type and equivalence.
-/
theorem Small.mk' {α : Type v} {S : Type w} (e : α ≃ S) : Small.{w} α :=
  ⟨⟨S, ⟨e⟩⟩⟩

/-- An arbitrarily chosen model in `Type w` for a `w`-small type.
-/
def Shrink (α : Type v) [Small.{w} α] : Type w :=
  Classical.choose (@Small.equiv_small α _)

/-- The noncomputable equivalence between a `w`-small type and a model.
-/
noncomputable def equivShrink (α : Type v) [Small.{w} α] : α ≃ Shrink α :=
  Nonempty.some (Classical.choose_spec (@Small.equiv_small α _))

@[ext]
theorem Shrink.ext {α : Type v} [Small.{w} α] {x y : Shrink α}
    (w : (equivShrink _).symm x = (equivShrink _).symm y) : x = y := by
  simpa using w

-- It would be nice to mark this as `aesop cases` if
-- https://github.com/JLimperg/aesop/issues/59
-- is resolved.
@[eliminator]
protected noncomputable def Shrink.rec [Small.{w} α] {F : Shrink α → Sort v}
    (h : ∀ X, F (equivShrink _ X)) : ∀ X, F X :=
  fun X => ((equivShrink _).apply_symm_apply X) ▸ (h _)

--Porting note: Priority changed to 101
instance (priority := 101) small_self (α : Type v) : Small.{v} α :=
  Small.mk' <| Equiv.refl α

theorem small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃ β) : Small.{w} α :=
  let ⟨_, ⟨f⟩⟩ := hβ.equiv_small
  Small.mk' (e.trans f)

theorem small_lift (α : Type u) [hα : Small.{v} α] : Small.{max v w} α :=
  let ⟨⟨_, ⟨f⟩⟩⟩ := hα
  Small.mk' <| f.trans (Equiv.ulift.{w}).symm

instance (priority := 100) small_max (α : Type v) : Small.{max w v} α :=
  small_lift.{v, w} α

instance small_ulift (α : Type u) [Small.{v} α] : Small.{v} (ULift.{w} α) :=
  small_map Equiv.ulift

theorem small_type : Small.{max (u + 1) v} (Type u) :=
  small_max.{max (u + 1) v} _

section

open Classical

theorem small_congr {α : Type*} {β : Type*} (e : α ≃ β) : Small.{w} α ↔ Small.{w} β :=
  ⟨fun h => @small_map _ _ h e.symm, fun h => @small_map _ _ h e⟩

instance small_subtype (α : Type v) [Small.{w} α] (P : α → Prop) : Small.{w} { x // P x } :=
  small_map (equivShrink α).subtypeEquivOfSubtype'

theorem small_of_injective {α : Type v} {β : Type w} [Small.{u} β] {f : α → β}
    (hf : Function.Injective f) : Small.{u} α :=
  small_map (Equiv.ofInjective f hf)

theorem small_of_surjective {α : Type v} {β : Type w} [Small.{u} α] {f : α → β}
    (hf : Function.Surjective f) : Small.{u} β :=
  small_of_injective (Function.injective_surjInv hf)

theorem small_subset {α : Type v} {s t : Set α} (hts : t ⊆ s) [Small.{u} s] : Small.{u} t :=
  let f : t → s := fun x => ⟨x, hts x.prop⟩
  @small_of_injective _ _ _ f fun _ _ hxy => Subtype.ext (Subtype.mk.inj hxy)

instance (priority := 100) small_subsingleton (α : Type v) [Subsingleton α] : Small.{w} α := by
  rcases isEmpty_or_nonempty α with ⟨⟩ <;> skip
  · apply small_map (Equiv.equivPEmpty α)
  · apply small_map Equiv.punitOfNonemptyOfSubsingleton

/-- This can be seen as a version of `small_of_surjective` in which the function `f` doesn't
    actually land in `β` but in some larger type `γ` related to `β` via an injective function `g`.
    -/
theorem small_of_injective_of_exists {α : Type v} {β : Type w} {γ : Type v'} [Small.{u} α]
    (f : α → γ) {g : β → γ} (hg : Function.Injective g) (h : ∀ b : β, ∃ a : α, f a = g b) :
    Small.{u} β := by
  by_cases hβ : Nonempty β
  · refine' small_of_surjective (f := Function.invFun g ∘ f) (fun b => _)
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, by rw [Function.comp_apply, ha, Function.leftInverse_invFun hg]⟩
  · simp only [not_nonempty_iff] at hβ
    infer_instance

/-!
We don't define `small_of_fintype` or `small_of_countable` in this file,
to keep imports to `logic` to a minimum.
-/


instance small_Pi {α} (β : α → Type*) [Small.{w} α] [∀ a, Small.{w} (β a)] :
    Small.{w} (∀ a, β a) :=
  ⟨⟨∀ a' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.piCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩

instance small_sigma {α} (β : α → Type*) [Small.{w} α] [∀ a, Small.{w} (β a)] :
    Small.{w} (Σa, β a) :=
  ⟨⟨Σa' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.sigmaCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩

instance small_prod {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (α × β) :=
  ⟨⟨Shrink α × Shrink β, ⟨Equiv.prodCongr (equivShrink α) (equivShrink β)⟩⟩⟩

instance small_sum {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (Sum α β) :=
  ⟨⟨Sum (Shrink α) (Shrink β), ⟨Equiv.sumCongr (equivShrink α) (equivShrink β)⟩⟩⟩

instance small_set {α} [Small.{w} α] : Small.{w} (Set α) :=
  ⟨⟨Set (Shrink α), ⟨Equiv.Set.congr (equivShrink α)⟩⟩⟩

instance small_range {α : Type v} {β : Type w} (f : α → β) [Small.{u} α] :
    Small.{u} (Set.range f) :=
  small_of_surjective Set.surjective_onto_range

instance small_image {α : Type v} {β : Type w} (f : α → β) (S : Set α) [Small.{u} S] :
    Small.{u} (f '' S) :=
  small_of_surjective Set.surjective_onto_image

theorem not_small_type : ¬Small.{u} (Type max u v)
  | ⟨⟨S, ⟨e⟩⟩⟩ =>
    @Function.cantor_injective (Σα, e.symm α) (fun a => ⟨_, cast (e.3 _).symm a⟩) fun a b e => by
      dsimp at e
      injection e with h₁ h₂
      simpa using h₂

end
