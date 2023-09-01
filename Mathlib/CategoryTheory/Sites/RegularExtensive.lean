/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Sites.Coherent
/-!

# The Regular and Extensive Coverages

This file defines two coverages on a category `C`.

The first one is called the *regular* coverage and for that to exist, the category `C` must satisfy
a condition called `Regular C`. This means that effective epimorphisms can be "pulled back". The
covering sieves of this coverage are generated by presieves consisting of a single effective
epimorphism.

The second one is called the *extensive* coverage and for that to exist, the category `C` must
satisfy a condition called `Extensive C`. This means `C` has finite coproducts and that those
are preserved by pullbacks. The covering sieves of this coverage are generated by presieves
consisting finitely many arrows that together induce an isomorphism from the coproduct to the
target.

In `extensive_union_regular_generates_coherent`, we prove that the union of these two coverages
generates the coherent topology on `C` if `C` is precoherent, extensive and regular.

TODO: figure out under what conditions `Regular` and `Extensive` are implied by `Precoherent` and
vice versa.

-/

universe v u w

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C]

/--
The condition `Regular C` is property that effective epis can be "pulled back" along any
morphism. This is satisfied e.g. by categories that have pullbacks that preserve effective
epimorphisms (like `Profinite` and `CompHaus`), and categories where every object is projective
(like  `Stonean`).
-/
class Regular : Prop where
  /--
  For `X`, `Y`, `Z`, `f`, `g` like in the diagram, where `g` is an effective epi, there exists
  an object `W`, a morphism `i : W ⟶ Z` and an effective epi `h : W ⟶ X` making the diagram
  commute.
  ```
  W --i-→ Z
  |       |
  h       g
  ↓       ↓
  X --f-→ Y
  ```
  -/
  exists_fac : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) [EffectiveEpi g],
    (∃ (W : C) (h : W ⟶ X) (_ : EffectiveEpi h) (i : W ⟶ Z), i ≫ g = h ≫ f)

/--
Describes the property of having pullbacks of morphsims into a finite coproduct, where one
of the morphisms is an inclusion map into the coproduct (up to isomorphism).
-/
class HasPullbacksOfInclusions : Prop where
    /-- For any morphism `f : X ⟶ Z`, where `Z` is the coproduct of `i : (a : α) → Y a ⟶ Z` with
    `α` finite, the pullback of `f` and `i a` exists for every `a : α`. -/
    has_pullback : ∀ {X Z : C} {α : Type w} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α),
    HasPullback f (i a)

instance {α : Type w} (Y : (a : α) → C) [HasCoproduct Y] :
    IsIso (Sigma.desc (fun a ↦ Sigma.ι Y a)) := by
  suffices (Sigma.desc fun a ↦ Sigma.ι Y a) = 𝟙 _ by rw [this]; infer_instance
  ext
  simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Category.comp_id]

instance [HasPullbacksOfInclusions C] {X : C} {α : Type w} (Y : (a : α) → C)
    [Fintype α] [HasCoproduct Y] (f : X ⟶ ∐ Y) (a : α) :
    HasPullback f (Sigma.ι Y a) := HasPullbacksOfInclusions.has_pullback f (fun a ↦ Sigma.ι Y a) a

instance [HasPullbacksOfInclusions C] {X Z : C} {α : Type w} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α) :
    HasPullback f (i a) := HasPullbacksOfInclusions.has_pullback f i a

/--
If `C` has pullbacks then it has the pullbacks relevant to `HasPullbacksOfInclusions`.
-/
instance (priority := 10) [HasPullbacks C] :
  HasPullbacksOfInclusions C := ⟨fun _ _ _ => inferInstance⟩

/--
A category is *extensive* if it has all finite coproducts and those coproducts are preserved
by pullbacks (we only require the relevant pullbacks to exist, via `HasPullbacksOfInclusions`).
-/
class Extensive extends HasFiniteCoproducts C, HasPullbacksOfInclusions C : Prop where
  /-- Pulling back an isomorphism from a coproduct yields an isomorphism. -/
  sigma_desc_iso : ∀ {α : Type w} [Fintype α] {X : C} {Z : α → C} (π : (a : α) → Z a ⟶ X)
    {Y : C} (f : Y ⟶ X) (_ : IsIso (Sigma.desc π)),
    IsIso (Sigma.desc ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _))

/--
The regular coverage on a regular category `C`.
-/
def regularCoverage [Regular C] : Coverage C where
  covering B := { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f }
  pullback := by
    intro X Y f S ⟨Z, π, hπ, h_epi⟩
    have := Regular.exists_fac f π
    obtain ⟨W, h, _, i, this⟩ := this
    refine ⟨Presieve.singleton h, ⟨?_, ?_⟩⟩
    · exact ⟨W, h, by {rw [Presieve.ofArrows_pUnit h]}, inferInstance⟩
    · intro W g hg
      cases hg
      refine ⟨Z, i, π, ⟨?_, this⟩⟩
      cases hπ
      rw [Presieve.ofArrows_pUnit]
      exact Presieve.singleton.mk

/--
The extensive coverage on an extensive category `C`
-/
def extensiveCoverage [Extensive C] : Coverage C where
  covering B := { S | ∃ (α : Type) (_ : Fintype α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }
  pullback := by
    intro X Y f S ⟨α, hα, Z, π, hS, h_iso⟩
    let Z' : α → C := fun a ↦ pullback f (π a)
    let π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst
    refine ⟨@Presieve.ofArrows C _ _ α Z' π', ⟨?_, ?_⟩⟩
    · constructor
      exact ⟨hα, Z', π', ⟨by simp only, Extensive.sigma_desc_iso (fun x => π x) f h_iso⟩⟩
    · intro W g hg
      rcases hg with ⟨a⟩
      refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
      rw [hS]
      refine Presieve.ofArrows.mk a

variable {C}

/-- TODO: `IsSplitMono f` or `IsSplitEpi f` is probably enough. -/
noncomputable
def EffectiveEpi_compStruct {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X)
    [IsIso f] [EffectiveEpi g]  :
    EffectiveEpiStruct (g ≫ f) where
  desc e h :=
    inv f ≫ EffectiveEpi.desc g e (fun g₁ g₂ hg ↦ h g₁ g₂
    (by rw [← Category.assoc, hg, Category.assoc]))
  fac e h := by
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, EffectiveEpi.fac]
  uniq e h m hm := by
    simp only [IsIso.eq_inv_comp]
    simp only [Category.assoc] at hm
    exact EffectiveEpi.uniq g e _ (f ≫ m) hm

noncomputable
def EffectiveEpiFamily_compStruct {B Y : C} {α : Type w} [Extensive C] [Fintype α]
    (X : α → C) (π : (a : α) → (X a ⟶ B)) (g : B ⟶ Y)
    [IsIso (Sigma.desc π)] [EffectiveEpi g]  :
    EffectiveEpiFamilyStruct X (fun a ↦ (π a ≫ g)) where
  desc e h := by
    apply EffectiveEpi.desc g ((inv (Sigma.desc π)) ≫ (Sigma.desc e))
    intro Z g₁ g₂ hg
    let P₁ := fun a ↦ pullback g₁ (π a)
    let ρ₁ : (a : α) → P₁ a ⟶ Z := fun a ↦ pullback.fst
    let P₂ := fun a ↦ pullback g₂ (π a)
    let ρ₂ : (a : α) → P₂ a ⟶ Z := fun a ↦ pullback.fst
    haveI h₁ := Extensive.sigma_desc_iso π g₁ inferInstance
    haveI h₂ := Extensive.sigma_desc_iso π g₂ inferInstance
    have hh₁ : ∀ a, ρ₁ a ≫ g₁ ≫ g = ρ₁ a ≫ g₂ ≫ g := fun a ↦ by rw [hg]
    have hh₂ : ∀ a, ρ₂ a ≫ g₁ ≫ g = ρ₂ a ≫ g₂ ≫ g := fun a ↦ by rw [hg]
    have hg₁ := fun a ↦ pullback.condition (f := g₁) (g := π a)
    have hg₂ := fun a ↦ pullback.condition (f := g₂) (g := π a)
    sorry
  fac e h := by sorry
    -- simp only [Category.assoc, IsIso.hom_inv_id_assoc, EffectiveEpi.fac]
  uniq e h m hm := by sorry
    -- simp only [IsIso.eq_inv_comp]
    -- simp only [Category.assoc] at hm
    -- exact EffectiveEpi.uniq g e _ (f ≫ m) hm

/--
Given an `EffectiveEpiFamily X π` such that the coproduct of `X` exists, `Sigma.desc π` is an
`EffectiveEpi`.
-/
noncomputable
def EffectiveEpiFamilyStruct_descStruct {B : C} {α : Type w} [Extensive C] [Fintype α]
    (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpi (Sigma.desc π)]  :
    EffectiveEpiFamilyStruct X π where
  desc e h := by
    apply EffectiveEpi.desc (Sigma.desc π) (Sigma.desc e)
    have hfac := EffectiveEpi.fac (Sigma.desc π) (Sigma.desc e)
    have huniq := EffectiveEpi.uniq (Sigma.desc π) (Sigma.desc e)
    intro Z g₁ g₂ hg
    let P₁ := fun a ↦ pullback g₁ (Sigma.ι X a)
    let ρ₁ : (a : α) → P₁ a ⟶ Z := fun a ↦ pullback.fst
    haveI := Extensive.sigma_desc_iso (fun a ↦ Sigma.ι X a) g₁ inferInstance
    let P₂ := fun a ↦ pullback g₂ (Sigma.ι X a)
    let ρ₂ : (a : α) → P₂ a ⟶ Z := fun a ↦ pullback.fst
    haveI h₁ := Extensive.sigma_desc_iso (fun a ↦ Sigma.ι X a) g₁ inferInstance
    haveI h₂ := Extensive.sigma_desc_iso (fun a ↦ Sigma.ι X a) g₂ inferInstance
    have hh₁ : ∀ a, ρ₁ a ≫ g₁ ≫ Sigma.desc π = ρ₁ a ≫ g₂ ≫ Sigma.desc π := fun a ↦ by rw [hg]
    have hh₂ : ∀ a, ρ₂ a ≫ g₁ ≫ Sigma.desc π = ρ₂ a ≫ g₂ ≫ Sigma.desc π := fun a ↦ by rw [hg]
    suffices : (asIso (Sigma.desc ρ₁)).inv ≫ Sigma.desc ρ₁ ≫ g₁ ≫ (Sigma.desc e) =
        inv (Sigma.desc ρ₂) ≫ (Sigma.desc ρ₂) ≫ g₂ ≫ (Sigma.desc e)
    · simp only [asIso_inv, IsIso.inv_hom_id_assoc] at this
      exact this
    rw [Iso.inv_comp_eq (asIso (Sigma.desc ρ₁))]
    ext b
    simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app, asIso_hom,
      IsIso.inv_hom_id_assoc]
    rw [← Category.assoc, pullback.condition, Category.assoc]
    simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    have hg₁ := pullback.condition (f := g₁) (g := Sigma.ι X b)
    have hg₂ := pullback.condition (f := g₂) (g := Sigma.ι X b)
    have hh : pullback.fst (f := g₁) (g := Sigma.ι X b) ≫ g₁ ≫ Sigma.desc π =
        pullback.fst ≫ g₂ ≫ Sigma.desc π := by rw [hg]
    rw [← Category.assoc, hg₁] at hh
    simp only [Category.assoc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app] at hh
    have := h b b (pullback.snd : P₁ b ⟶ X b)-- ?_--(pullback.fst ≫ Sigma.ι X b)
    sorry
  fac e h := sorry
  uniq e _ m hm := sorry

instance {B : C} {α : Type w} (X : α → C) (π : (a : α) → (X a ⟶ B)) [HasCoproduct X]
    [EffectiveEpiFamily X π] : EffectiveEpi (Sigma.desc π) :=
  ⟨⟨EffectiveEpiFamily_descStruct X π⟩⟩

-- noncomputable
-- def EffectiveEpiFamilyStruct_of_iso_desc {B : C} {α : Type w} [Fintype α]
--     (X : α → C) (π : (a : α) → (X a ⟶ B)) [Extensive C] [IsIso (Sigma.desc π)]  :
--     EffectiveEpiFamilyStruct X π where
--   desc e h := inv (Sigma.desc π) ≫ Sigma.desc e
--   fac e h a := by
--     have : π a = Sigma.ι X a ≫ Sigma.desc π := by
--       simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
--     rw [this, Category.assoc]
--     simp only [IsIso.hom_inv_id_assoc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
--   uniq := sorry

-- instance {B : C} {α : Type w} [Fintype α]
--     (X : α → C) (π : (a : α) → (X a ⟶ B)) [Extensive C] [IsIso (Sigma.desc π)]  :
--     EffectiveEpiFamily X π :=
--   ⟨⟨EffectiveEpiFamilyStruct_of_iso_desc X π⟩⟩


instance [Regular C] [Extensive C] : Precoherent C where
  pullback f α _ X₁ π₁ _ := by
    haveI : EffectiveEpi (Sigma.desc π₁) := inferInstance
    obtain ⟨W, h, _, i, hh⟩ := Regular.exists_fac f (Sigma.desc π₁)
    have hi := Extensive.sigma_desc_iso (fun a ↦ Sigma.ι X₁ a) i inferInstance
    let P := fun a ↦ pullback i (Sigma.ι X₁ a)
    refine ⟨α, inferInstance, P, fun a ↦ pullback.fst ≫ h,
      ⟨?_, ⟨id, fun b ↦ pullback.snd, ?_⟩⟩⟩
    · sorry
    · intro b
      simp only [id_eq, Category.assoc, ← hh]
      rw [← Category.assoc, pullback.condition]
      simp only [Category.assoc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]

end CategoryTheory
