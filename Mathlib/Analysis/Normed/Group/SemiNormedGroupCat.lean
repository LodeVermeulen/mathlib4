/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Riccardo Brasca
-/
import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.Elementwise

#align_import analysis.normed.group.SemiNormedGroup from "leanprover-community/mathlib"@"17ef379e997badd73e5eabb4d38f11919ab3c4b3"

/-!
# The category of seminormed groups

We define `SemiNormedGroupCat`, the category of seminormed groups and normed group homs between
them, as well as `SemiNormedGroupCat₁`, the subcategory of norm non-increasing morphisms.
-/

set_option linter.uppercaseLean3 false

noncomputable section

universe u

open CategoryTheory

/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
def SemiNormedGroupCat : Type (u + 1) :=
  Bundled SeminormedAddCommGroup

namespace SemiNormedGroupCat

instance bundledHom : BundledHom @NormedAddGroupHom where
  toFun := @NormedAddGroupHom.toFun
  id := @NormedAddGroupHom.id
  comp := @NormedAddGroupHom.comp

deriving instance LargeCategory for SemiNormedGroupCat

-- Porting note: deriving fails for ConcreteCategory, adding instance manually.
-- See https://github.com/leanprover-community/mathlib4/issues/5020
-- deriving instance LargeCategory, ConcreteCategory for SemiRingCat
instance : ConcreteCategory SemiNormedGroupCat := by
  dsimp [SemiNormedGroupCat]
  infer_instance

instance : CoeSort SemiNormedGroupCat (Type*) where
  coe X := X.α

/-- Construct a bundled `SemiNormedGroupCat` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGroupCat :=
  Bundled.of M

instance (M : SemiNormedGroupCat) : SeminormedAddCommGroup M :=
  M.str

-- Porting Note: added
instance toAddMonoidHomClass {V W : SemiNormedGroupCat} : AddMonoidHomClass (V ⟶ W) V W where
  coe := (forget SemiNormedGroupCat).map
  coe_injective' := fun f g h => by cases f; cases g; congr
  map_add f := f.map_add'
  map_zero f := (AddMonoidHom.mk' f.toFun f.map_add').map_zero

-- Porting note: added to ease automation
@[ext]
lemma ext {M N : SemiNormedGroupCat} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  FunLike.ext _ _ h

@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGroupCat.of V : Type u) = V :=
  rfl

-- Porting note : marked with high priority to short circuit simplifier's path
@[simp (high)]
theorem coe_id (V : SemiNormedGroupCat) : (𝟙 V : V → V) = id :=
  rfl

-- Porting note : marked with high priority to short circuit simplifier's path
@[simp (high)]
theorem coe_comp {M N K : SemiNormedGroupCat} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M → K) = g ∘ f :=
  rfl

instance : Inhabited SemiNormedGroupCat :=
  ⟨of PUnit⟩

instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGroupCat.of V) :=
  i

instance {M N : SemiNormedGroupCat} : Zero (M ⟶ N) :=
  NormedAddGroupHom.zero

@[simp]
theorem zero_apply {V W : SemiNormedGroupCat} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroupCat where

theorem isZero_of_subsingleton (V : SemiNormedGroupCat) [Subsingleton V] : Limits.IsZero V := by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim

instance hasZeroObject : Limits.HasZeroObject SemiNormedGroupCat.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

theorem iso_isometry_of_normNoninc {V W : SemiNormedGroupCat} (i : V ≅ W) (h1 : i.hom.NormNoninc)
    (h2 : i.inv.NormNoninc) : Isometry i.hom := by
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  apply le_antisymm (h1 v)
  calc
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    ‖v‖ = ‖i.inv (i.hom v)‖ := by erw [Iso.hom_inv_id_apply]
    _ ≤ ‖i.hom v‖ := h2 _

end SemiNormedGroupCat

/-- `SemiNormedGroupCat₁` is a type synonym for `SemiNormedGroupCat`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
def SemiNormedGroupCat₁ : Type (u + 1) :=
  Bundled SeminormedAddCommGroup

namespace SemiNormedGroupCat₁

instance : CoeSort SemiNormedGroupCat₁ (Type*) where
  coe X := X.α

instance : LargeCategory.{u} SemiNormedGroupCat₁ where
  Hom X Y := { f : NormedAddGroupHom X Y // f.NormNoninc }
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp {X Y Z} f g := ⟨g.1.comp f.1, g.2.comp f.2⟩

-- Porting Note: Added
instance instFunLike (X Y : SemiNormedGroupCat₁) : FunLike (X ⟶ Y) X (fun _ => Y) where
  coe f := f.1.toFun
  coe_injective' _ _ h := Subtype.val_inj.mp (NormedAddGroupHom.coe_injective h)

@[ext]
theorem hom_ext {M N : SemiNormedGroupCat₁} (f g : M ⟶ N) (w : (f : M → N) = (g : M → N)) :
    f = g :=
  Subtype.eq (NormedAddGroupHom.ext (congr_fun w))

instance : ConcreteCategory.{u} SemiNormedGroupCat₁ where
  forget :=
    { obj := fun X => X
      map := fun f => f }
  forget_faithful := { }

-- Porting note: added
instance toAddMonoidHomClass {V W : SemiNormedGroupCat₁} : AddMonoidHomClass (V ⟶ W) V W where
  map_add f := f.1.map_add'
  map_zero f := (AddMonoidHom.mk' f.1 f.1.map_add').map_zero

/-- Construct a bundled `SemiNormedGroupCat₁` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGroupCat₁ :=
  Bundled.of M

instance (M : SemiNormedGroupCat₁) : SeminormedAddCommGroup M :=
  M.str

/-- Promote a morphism in `SemiNormedGroupCat` to a morphism in `SemiNormedGroupCat₁`. -/
def mkHom {M N : SemiNormedGroupCat} (f : M ⟶ N) (i : f.NormNoninc) :
    SemiNormedGroupCat₁.of M ⟶ SemiNormedGroupCat₁.of N :=
  ⟨f, i⟩

-- @[simp] -- Porting note: simpNF linter claims LHS simplifies with `SemiNormedGroupCat₁.coe_of`
theorem mkHom_apply {M N : SemiNormedGroupCat} (f : M ⟶ N) (i : f.NormNoninc) (x) :
    mkHom f i x = f x :=
  rfl

/-- Promote an isomorphism in `SemiNormedGroupCat` to an isomorphism in `SemiNormedGroupCat₁`. -/
@[simps]
def mkIso {M N : SemiNormedGroupCat} (f : M ≅ N) (i : f.hom.NormNoninc) (i' : f.inv.NormNoninc) :
    SemiNormedGroupCat₁.of M ≅ SemiNormedGroupCat₁.of N where
  hom := mkHom f.hom i
  inv := mkHom f.inv i'
  hom_inv_id := by apply Subtype.eq; exact f.hom_inv_id
  inv_hom_id := by apply Subtype.eq; exact f.inv_hom_id

instance : HasForget₂ SemiNormedGroupCat₁ SemiNormedGroupCat where
  forget₂ :=
    { obj := fun X => X
      map := fun f => f.1 }

@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGroupCat₁.of V : Type u) = V :=
  rfl

-- Porting note : marked with high priority to short circuit simplifier's path
@[simp (high)]
theorem coe_id (V : SemiNormedGroupCat₁) : ⇑(𝟙 V) = id :=
  rfl

-- Porting note : marked with high priority to short circuit simplifier's path
@[simp (high)]
theorem coe_comp {M N K : SemiNormedGroupCat₁} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M → K) = g ∘ f :=
  rfl

-- Porting note: deleted `coe_comp'`, as we no longer have the relevant coercion.
#noalign SemiNormedGroup₁.coe_comp'

instance : Inhabited SemiNormedGroupCat₁ :=
  ⟨of PUnit⟩

instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGroupCat₁.of V) :=
  i

-- Porting note: extracted from `Limits.HasZeroMorphisms` instance below.
instance (X Y : SemiNormedGroupCat₁) : Zero (X ⟶ Y) where
  zero := ⟨0, NormedAddGroupHom.NormNoninc.zero⟩

@[simp]
theorem zero_apply {V W : SemiNormedGroupCat₁} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroupCat₁ where

theorem isZero_of_subsingleton (V : SemiNormedGroupCat₁) [Subsingleton V] : Limits.IsZero V := by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim

instance hasZeroObject : Limits.HasZeroObject SemiNormedGroupCat₁.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

theorem iso_isometry {V W : SemiNormedGroupCat₁} (i : V ≅ W) : Isometry i.hom := by
  change Isometry (⟨⟨i.hom, map_zero _⟩, fun _ _ => map_add _ _ _⟩ : V →+ W)
  refine' AddMonoidHomClass.isometry_of_norm _ _
  intro v
  apply le_antisymm (i.hom.2 v)
  calc
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    ‖v‖ = ‖i.inv (i.hom v)‖ := by erw [Iso.hom_inv_id_apply]
    _ ≤ ‖i.hom v‖ := i.inv.2 _

end SemiNormedGroupCat₁
