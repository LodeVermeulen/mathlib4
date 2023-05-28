/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Shift.Basic

/-!
# Functors which commute with shifts

Let `C` and `D` be two categories equipped with shifts by an additive monoid `A`. In this file,
we define the notion of functor `F : C ⥤ D` which "commute" with these shifts. The associated
type class is `[F.CommShift A]`. The data consists of commutation isomorphisms
`F.commShiftIso a : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` for all `a : A`
which satisfy a compatibility with the addition and the zero. After this was formalised in Lean,
it was found that this definition is exactly the definition which appears in Jean-Louis
Verdier's thesis (I 1.2.3/1.2.4), allthough the language is different. (In Verdier's thesis,
the shift is not given by a monoidal functor `Discrete A ⥤ C ⥤ C`, but by a fibred
category `C ⥤ BA`, where `BA` is the category with one object, the endomorphisms of which
identify to `A`. The choice of a cleavage for this fibered category gives the individual
shift functors.)

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

namespace CategoryTheory

open Category

namespace Functor

variable {C D E : Type _} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G : D ⥤ E) (A : Type _) [AddMonoid A]
  [HasShift C A] [HasShift D A] [HasShift E A]

namespace CommShift

/-- For any functor `F : C ⥤ D`, this is the obvious isomorphism
`shiftFunctor C (0 : A) ⋙ F ≅ F ⋙ shiftFunctor D (0 : A)` deduced from the
isomorphisms `shiftFunctorZero` on both categories `C` and `D`. -/
@[simps!]
noncomputable def isoZero : shiftFunctor C (0 : A) ⋙ F ≅ F ⋙ shiftFunctor D (0 : A) :=
  isoWhiskerRight (shiftFunctorZero C A) F ≪≫ F.leftUnitor ≪≫
     F.rightUnitor.symm ≪≫ isoWhiskerLeft F (shiftFunctorZero D A).symm

variable {F A}

/-- If a functor `F : C ⥤ D` is equipped with "commutation isomorphisms" with the
shifts by `a` and `b`, then there is a commutation isomorphism for the shift by `c` when
`a + b = c`. -/
@[simps!]
noncomputable def isoAdd' {a b c : A} (h : a + b = c)
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) :
    shiftFunctor C c ⋙ F ≅ F ⋙ shiftFunctor D c :=
  isoWhiskerRight (shiftFunctorAdd' C _ _ _ h) F ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ e₂ ≪≫ (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e₁ _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (shiftFunctorAdd' D _ _ _ h).symm

/-- If a functor `F : C ⥤ D` is equipped with "commutation isomorphisms" with the
shifts by `a` and `b`, then there is a commutation isomorphism for the shift by `a + b`. -/
noncomputable def isoAdd {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) :
    shiftFunctor C (a + b) ⋙ F ≅ F ⋙ shiftFunctor D (a + b) :=
  CommShift.isoAdd' rfl e₁ e₂

@[simp]
lemma isoAdd_hom_app  {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) :
      (CommShift.isoAdd e₁ e₂).hom.app X =
        F.map ((shiftFunctorAdd C a b).hom.app X) ≫ e₂.hom.app ((shiftFunctor C a).obj X) ≫
          (shiftFunctor D b).map (e₁.hom.app X) ≫ (shiftFunctorAdd D a b).inv.app (F.obj X) := by
  simp only [isoAdd, isoAdd'_hom_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

@[simp]
lemma isoAdd_inv_app  {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) :
      (CommShift.isoAdd e₁ e₂).inv.app X = (shiftFunctorAdd D a b).hom.app (F.obj X) ≫
        (shiftFunctor D b).map (e₁.inv.app X) ≫ e₂.inv.app ((shiftFunctor C a).obj X) ≫
        F.map ((shiftFunctorAdd C a b).inv.app X) := by
  simp only [isoAdd, isoAdd'_inv_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

end CommShift

/-- A functor `F` commute with the shift by a monoid `A` if it is equipped with
commutation isomorphisms with the shifts by all `a : A`, and these isomorphisms
satisfy coherence properties with respect to `0 : A` and the addition in `A`. -/
class CommShift where
  iso (a : A) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
  zero : iso 0 = CommShift.isoZero F A := by aesop_cat
  add (a b : A) : iso (a + b) = CommShift.isoAdd (iso a) (iso b) := by aesop_cat

variable {A}

/-- If a functor `F` commutes with the shift by `A` (i.e. `[F.CommShift A]`), then
`F.commShiftIso a` is the given isomorphism `shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a`. -/
def commShiftIso [F.CommShift A] (a : A) :
    shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  CommShift.iso a

-- Note: The following two lemmas are introduced in order to have more proofs work `by simp`.
-- Indeed, `simp only [(F.commShiftIso a).hom.naturality f]` would almost never work because
-- of the compositions of functors which appear in both the source and target of
-- `F.commShiftIso a`. Otherwise, we would be forced to use `erw [NatTrans.naturality]`.

@[reassoc (attr := simp)]
lemma commShiftIso_hom_naturality [F.CommShift A] {X Y : C} (f : X ⟶ Y) (a : A) :
    F.map (f⟦a⟧') ≫ (F.commShiftIso a).hom.app Y =
      (F.commShiftIso a).hom.app X ≫ (F.map f)⟦a⟧' :=
  (F.commShiftIso a).hom.naturality f

@[reassoc (attr := simp)]
lemma commShiftIso_inv_naturality [F.CommShift A] {X Y : C} (f : X ⟶ Y) (a : A) :
    (F.map f)⟦a⟧' ≫ (F.commShiftIso a).inv.app Y =
      (F.commShiftIso a).inv.app X ≫ F.map (f⟦a⟧') :=
  (F.commShiftIso a).inv.naturality f

variable (A)

lemma commShiftIso_zero [F.CommShift A] :
  F.commShiftIso (0 : A) = CommShift.isoZero F A :=
  CommShift.zero

variable {A}

lemma commShiftIso_add [F.CommShift A] (a b : A):
  F.commShiftIso (a + b) = CommShift.isoAdd (F.commShiftIso a) (F.commShiftIso b) :=
  CommShift.add a b

lemma commShiftIso_add' [F.CommShift A] {a b c : A} (h : a + b = c) :
  F.commShiftIso c = CommShift.isoAdd' h (F.commShiftIso a) (F.commShiftIso b) := by
  subst h
  simp only [commShiftIso_add, CommShift.isoAdd]

namespace CommShift

variable (C)

instance id : CommShift (𝟭 C) A where
  iso := fun a => rightUnitor _ ≪≫ (leftUnitor _).symm

variable {C F G}

variable [F.CommShift A] [G.CommShift A]

instance comp : (F ⋙ G).CommShift A where
  iso a := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.commShiftIso a) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (G.commShiftIso a) ≪≫
    (Functor.associator _ _ _).symm
  zero := by
    ext X
    dsimp
    simp only [id_comp, comp_id, commShiftIso_zero, isoZero_hom_app, ← Functor.map_comp_assoc,
      assoc, Iso.inv_hom_id_app, id_obj, comp_map, comp_obj]
  add := fun a b => by
    ext X
    dsimp
    simp only [commShiftIso_add, isoAdd_hom_app]
    dsimp
    simp only [comp_id, id_comp, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, comp_obj]
    simp only [map_comp, assoc, commShiftIso_hom_naturality_assoc]

end CommShift

lemma commShiftIso_comp_hom_app [F.CommShift A] [G.CommShift A] (a : A) (X : C) :
    (commShiftIso (F ⋙ G) a).hom.app X =
      G.map ((commShiftIso F a).hom.app X) ≫ (commShiftIso G a).hom.app (F.obj X) := by
  simp [commShiftIso, CommShift.iso]

lemma commShiftIso_comp_inv_app [F.CommShift A] [G.CommShift A] (a : A) (X : C) :
    (commShiftIso (F ⋙ G) a).inv.app X =
      (commShiftIso G a).inv.app (F.obj X) ≫ G.map ((commShiftIso F a).inv.app X) := by
  simp [commShiftIso, CommShift.iso]

end Functor

namespace NatTrans

variable {C D E : Type _} [Category C] [Category D] [Category E]
  {F₁ F₂ F₃ : C ⥤ D} (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) (e : F₁ ≅ F₂)
    (G G' : D ⥤ E) (τ'' : G ⟶ G')
  (A : Type _) [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A]
  [F₁.CommShift A] [F₂.CommShift A] [F₃.CommShift A]
    [G.CommShift A] [G'.CommShift A]

class CommShift : Prop :=
  comm' : ∀ (a : A), (F₁.commShiftIso a).hom ≫ whiskerRight τ _ =
    whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom

namespace CommShift

section

variable {A}
variable [NatTrans.CommShift τ A]

lemma comm (a : A) : (F₁.commShiftIso a).hom ≫ whiskerRight τ _ =
    whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom := by
  apply comm'

@[reassoc]
lemma comm_app (a : A) (X : C) :
    (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' =
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X :=
  NatTrans.congr_app (comm τ a) X

lemma shift_app (a : A) (X : C) :
    (τ.app X)⟦a⟧' = (F₁.commShiftIso a).inv.app X ≫
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X := by
  rw [← comm_app, Iso.inv_hom_id_app_assoc]

lemma app_shift (a : A) (X : C) :
    τ.app (X⟦a⟧) = (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' ≫
      (F₂.commShiftIso a).inv.app X := by
  erw [comm_app_assoc, Iso.hom_inv_id_app, Category.comp_id]

end

instance of_iso_inv [NatTrans.CommShift e.hom A] :
  NatTrans.CommShift e.inv A := ⟨fun a => by
  ext X
  dsimp
  rw [← cancel_epi (e.hom.app (X⟦a⟧)), e.hom_inv_id_app_assoc, ← comm_app_assoc,
    ← Functor.map_comp, e.hom_inv_id_app, Functor.map_id]
  dsimp
  rw [Category.comp_id]⟩

lemma of_isIso [IsIso τ] [NatTrans.CommShift τ A] :
    NatTrans.CommShift (inv τ) A := by
  haveI : NatTrans.CommShift (asIso τ).hom A := by
    dsimp
    infer_instance
  change NatTrans.CommShift (asIso τ).inv A
  infer_instance

variable (F₁)

instance id : NatTrans.CommShift (𝟙 F₁) A := ⟨by aesop_cat⟩

instance comp [NatTrans.CommShift τ A] [NatTrans.CommShift τ' A] :
    NatTrans.CommShift (τ ≫ τ') A := ⟨fun a => by
  ext X
  simp [comm_app_assoc, comm_app]⟩

variable {F₁}

instance whiskerRight [NatTrans.CommShift τ A] :
    NatTrans.CommShift (whiskerRight τ G) A := ⟨fun a => by
  ext X
  simp only [Functor.comp_obj, whiskerRight_twice, comp_app,
    whiskerRight_app, Functor.comp_map, whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc]
  erw [← NatTrans.naturality]
  dsimp
  simp only [← G.map_comp_assoc, comm_app]⟩

variable {G G'} (F₁)

instance whiskerLeft [NatTrans.CommShift τ'' A] :
    NatTrans.CommShift (whiskerLeft F₁ τ'') A := ⟨fun a => by
  ext X
  simp only [Functor.comp_obj, comp_app, whiskerRight_app, whiskerLeft_app, whiskerLeft_twice,
    Functor.commShiftIso_comp_hom_app, Category.assoc, ← NatTrans.naturality_assoc, comm_app]⟩

end CommShift

end NatTrans

namespace Functor

section hasShiftOfFullyFaithful

variable {C D : Type _} [Category C] [Category D] [AddMonoid A] [HasShift D A]
  (F : C ⥤ D) [Full F] [Faithful F]
  (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shiftFunctor D i)

namespace CommShift

def of_hasShiftOfFullyFaithful :
    letI := hasShiftOfFullyFaithful F s i; F.CommShift A := by
  letI := hasShiftOfFullyFaithful F s i
  exact
  { iso := i
    zero := by
      ext X
      simp only [comp_obj, isoZero_hom_app, ShiftMkCore.shiftFunctorZero_eq, Iso.symm_hom,
        map_hasShiftOfFullyFaithful_zero_hom_app, id_obj, Category.assoc,
        Iso.hom_inv_id_app, Category.comp_id]
    add := fun a b => by
      ext X
      simp only [comp_obj, isoAdd_hom_app, ShiftMkCore.shiftFunctorAdd_eq, Iso.symm_hom,
        map_hasShiftOfFullyFaithful_add_hom_app, Category.assoc, ShiftMkCore.shiftFunctor_eq,
        Iso.inv_hom_id_app_assoc, ← (shiftFunctor D b).map_comp_assoc, Iso.inv_hom_id_app,
        Functor.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id] }

end CommShift

lemma shiftFunctorIso_of_hasShiftOfFullyFaithful (a : A) :
    letI := hasShiftOfFullyFaithful F s i;
    letI := CommShift.of_hasShiftOfFullyFaithful F s i;
    F.commShiftIso a = i a := by
  rfl

end hasShiftOfFullyFaithful

lemma map_shiftFunctorComm {C D : Type _} [Category C] [Category D] {A : Type _} [AddCommMonoid A]
  [HasShift C A] [HasShift D A] (F : C ⥤ D) [F.CommShift A] (X : C) (a b : A) :
    F.map ((shiftFunctorComm C a b).hom.app X) = (F.commShiftIso b).hom.app (X⟦a⟧) ≫
      ((F.commShiftIso a).hom.app X)⟦b⟧' ≫ (shiftFunctorComm D a b).hom.app (F.obj X) ≫
      ((F.commShiftIso b).inv.app X)⟦a⟧' ≫ (F.commShiftIso a).inv.app (X⟦b⟧) := by
  have eq := NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add a b)) X
  simp only [comp_obj, CommShift.isoAdd_hom_app,
    ← cancel_epi (F.map ((shiftFunctorAdd C a b).inv.app X)), Category.assoc,
    ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp, F.map_comp] at eq
  simp only [shiftFunctorComm_eq D a b _ rfl]
  dsimp
  simp only [Functor.map_comp, shiftFunctorAdd'_eq_shiftFunctorAdd, Category.assoc,
    ← reassoc_of% eq,
    shiftFunctorComm_eq C a b _ rfl]
  dsimp
  rw [Functor.map_comp]
  congr 1
  simp only [NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add' (add_comm b a))) X,
    CommShift.isoAdd'_hom_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp
  simp only [Functor.map_id, Category.id_comp, Iso.hom_inv_id_app, comp_obj, Category.comp_id]

@[simp]
lemma map_shiftFunctorCompIsoId_hom_app
    {C D : Type _} [Category C] [Category D] {A : Type _} [AddMonoid A]
    [HasShift C A] [HasShift D A] (F : C ⥤ D) [F.CommShift A] (X : C) (a b : A) (h : a + b = 0) :
    F.map ((shiftFunctorCompIsoId C a b h).hom.app X) =
      (F.commShiftIso b).hom.app (X⟦a⟧) ≫ ((F.commShiftIso a).hom.app X)⟦b⟧' ≫
        (shiftFunctorCompIsoId D a b h).hom.app (F.obj X) := by
  dsimp [shiftFunctorCompIsoId]
  have eq := NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add' h)) X
  simp only [commShiftIso_zero, comp_obj, CommShift.isoZero_hom_app,
    CommShift.isoAdd'_hom_app] at eq
  rw [← cancel_epi (F.map ((shiftFunctorAdd' C a b 0 h).hom.app X)), ← reassoc_of% eq, F.map_comp]
  simp only [Iso.inv_hom_id_app, id_obj, Category.comp_id, ← F.map_comp_assoc, Iso.hom_inv_id_app,
    F.map_id, Category.id_comp]

@[simp]
lemma map_shiftFunctorCompIsoId_inv_app
    {C D : Type _} [Category C] [Category D] {A : Type _} [AddMonoid A]
    [HasShift C A] [HasShift D A] (F : C ⥤ D) [F.CommShift A] (X : C) (a b : A) (h : a + b = 0) :
    F.map ((shiftFunctorCompIsoId C a b h).inv.app X) =
        (shiftFunctorCompIsoId D a b h).inv.app (F.obj X) ≫
      ((F.commShiftIso a).inv.app X)⟦b⟧' ≫
      (F.commShiftIso b).inv.app (X⟦a⟧) := by
  rw [← cancel_epi (F.map ((shiftFunctorCompIsoId C a b h).hom.app X)), ← F.map_comp,
    Iso.hom_inv_id_app, F.map_id, map_shiftFunctorCompIsoId_hom_app]
  simp only [comp_obj, id_obj, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]

end Functor

end CategoryTheory
