/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Pi.Algebra
import Mathlib.Logic.Equiv.Basic

#align_import algebra.hom.equiv.basic from "leanprover-community/mathlib"@"1ac8d4304efba9d03fa720d06516fac845aa5353"

/-!
# Multiplicative and additive equivs

In this file we define two extensions of `Equiv` called `AddEquiv` and `MulEquiv`, which are
datatypes representing isomorphisms of `AddMonoid`s/`AddGroup`s and `Monoid`s/`Group`s.

## Notations

* ``infix ` ≃* `:25 := MulEquiv``
* ``infix ` ≃+ `:25 := AddEquiv``

The extended equivs all have coercions to functions, and the coercions are the canonical
notation when treating the isomorphisms as maps.

## Tags

Equiv, MulEquiv, AddEquiv
-/


variable {F α β A B M N P Q G H : Type*}

/-- Makes a `OneHom` inverse from the bijective inverse of a `OneHom` -/
@[to_additive (attr := simps)
  "Make a `ZeroHom` inverse from the bijective inverse of a `ZeroHom`"]
def OneHom.inverse [One M] [One N]
    (f : OneHom M N) (g : N → M)
    (h₁ : Function.LeftInverse g f) :
  OneHom N M :=
  { toFun := g,
    map_one' := by rw [← f.map_one, h₁] }

/-- Makes a multiplicative inverse from a bijection which preserves multiplication. -/
@[to_additive (attr := simps)
  "Makes an additive inverse from a bijection which preserves addition."]
def MulHom.inverse [Mul M] [Mul N] (f : M →ₙ* N) (g : N → M)
    (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N →ₙ* M where
  toFun := g
  map_mul' x y :=
    calc
      g (x * y) = g (f (g x) * f (g y)) := by rw [h₂ x, h₂ y]
      _ = g (f (g x * g y)) := by rw [f.map_mul]
      _ = g x * g y := h₁ _

/-- The inverse of a bijective `MonoidHom` is a `MonoidHom`. -/
@[to_additive (attr := simps)
  "The inverse of a bijective `AddMonoidHom` is an `AddMonoidHom`."]
def MonoidHom.inverse {A B : Type*} [Monoid A] [Monoid B] (f : A →* B) (g : B → A)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : B →* A :=
  { (f : OneHom A B).inverse g h₁,
    (f : A →ₙ* B).inverse g h₁ h₂ with toFun := g }

/-- `AddEquiv α β` is the type of an equiv `α ≃ β` which preserves addition. -/
structure AddEquiv (A B : Type*) [Add A] [Add B] extends A ≃ B, AddHom A B

/-- `AddEquivClass F A B` states that `F` is a type of addition-preserving morphisms.
You should extend this class when you extend `AddEquiv`. -/
class AddEquivClass (F : Type*) (A B : outParam (Type*)) [Add A] [Add B]
    extends EquivLike F A B where
  /-- Preserves addition. -/
  map_add : ∀ (f : F) (a b), f (a + b) = f a + f b

/-- The `Equiv` underlying an `AddEquiv`. -/
add_decl_doc AddEquiv.toEquiv

/-- The `AddHom` underlying an `AddEquiv`. -/
add_decl_doc AddEquiv.toAddHom

/-- `MulEquiv α β` is the type of an equiv `α ≃ β` which preserves multiplication. -/
@[to_additive]
structure MulEquiv (M N : Type*) [Mul M] [Mul N] extends M ≃ N, M →ₙ* N
-- Porting note: remove when `to_additive` can do this
-- https://github.com/leanprover-community/mathlib4/issues/660
attribute [to_additive existing] MulEquiv.toMulHom

/-- The `Equiv` underlying a `MulEquiv`. -/
add_decl_doc MulEquiv.toEquiv

/-- The `MulHom` underlying a `MulEquiv`. -/
add_decl_doc MulEquiv.toMulHom

/-- `MulEquivClass F A B` states that `F` is a type of multiplication-preserving morphisms.
You should extend this class when you extend `MulEquiv`. -/
@[to_additive]
class MulEquivClass (F : Type*) (A B : outParam (Type*)) [Mul A] [Mul B] extends
  EquivLike F A B where
  /-- Preserves multiplication. -/
  map_mul : ∀ (f : F) (a b), f (a * b) = f a * f b

/-- Notation for a `MulEquiv`. -/
infixl:25 " ≃* " => MulEquiv

/-- Notation for an `AddEquiv`. -/
infixl:25 " ≃+ " => AddEquiv

namespace MulEquivClass

variable (F)

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) instMulHomClass (F : Type*)
    [Mul M] [Mul N] [h : MulEquivClass F M N] : MulHomClass F M N :=
  { h with coe := h.coe, coe_injective' := FunLike.coe_injective' }

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) instMonoidHomClass
    [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] :
    MonoidHomClass F M N :=
  { MulEquivClass.instMulHomClass F with
    coe := fun _ => _,
    map_one := fun e =>
      calc
        e 1 = e 1 * 1 := (mul_one _).symm
        _ = e 1 * e (MulEquivClass.toEquivLike.inv e (1 : N) : M) :=
          congr_arg _ (MulEquivClass.toEquivLike.right_inv e 1).symm
        _ = e (MulEquivClass.toEquivLike.inv e (1 : N)) := by rw [← map_mul, one_mul]
        _ = 1 := MulEquivClass.toEquivLike.right_inv e 1 }

-- See note [lower instance priority]
instance (priority := 100) toZeroHomClass
    [MulZeroClass α] [MulZeroClass β] [MulEquivClass F α β] :
    ZeroHomClass F α β where
  map_zero := fun e =>
    calc
      e 0 = e 0 * e (EquivLike.inv e 0) := by rw [← map_mul, zero_mul]
        _ = 0 := by simp

-- See note [lower instance priority]
instance (priority := 100) toMonoidWithZeroHomClass
    [MulZeroOneClass α] [MulZeroOneClass β] [MulEquivClass F α β] :
    MonoidWithZeroHomClass F α β :=
  { MulEquivClass.instMonoidHomClass F, MulEquivClass.toZeroHomClass F with }

variable {F}

@[to_additive (attr := simp)]
theorem map_eq_one_iff {M N} [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] (h : F) {x : M} :
    h x = 1 ↔ x = 1 := _root_.map_eq_one_iff h (EquivLike.injective h)

@[to_additive]
theorem map_ne_one_iff {M N} [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] (h : F) {x : M} :
    h x ≠ 1 ↔ x ≠ 1 := _root_.map_ne_one_iff h (EquivLike.injective h)

end MulEquivClass

/-- Turn an element of a type `F` satisfying `MulEquivClass F α β` into an actual
`MulEquiv`. This is declared as the default coercion from `F` to `α ≃* β`. -/
@[to_additive (attr := coe)
"Turn an element of a type `F` satisfying `AddEquivClass F α β` into an actual
`AddEquiv`. This is declared as the default coercion from `F` to `α ≃+ β`."]
def MulEquivClass.toMulEquiv [Mul α] [Mul β] [MulEquivClass F α β] (f : F) : α ≃* β :=
  { (f : α ≃ β), (f : α →ₙ* β) with }

/-- Any type satisfying `MulEquivClass` can be cast into `MulEquiv` via
`MulEquivClass.toMulEquiv`. -/
@[to_additive "Any type satisfying `AddEquivClass` can be cast into `AddEquiv` via
`AddEquivClass.toAddEquiv`. "]
instance [Mul α] [Mul β] [MulEquivClass F α β] : CoeTC F (α ≃* β) :=
  ⟨MulEquivClass.toMulEquiv⟩

namespace MulEquiv

@[to_additive]
instance [Mul M] [Mul N] : MulEquivClass (M ≃* N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    apply Equiv.coe_fn_injective h₁
  map_mul f := f.map_mul'

@[to_additive] -- shortcut instance that doesn't generate any subgoals
instance [Mul M] [Mul N] : CoeFun (M ≃* N) fun _ => M → N where
  coe f := f

variable [Mul M] [Mul N] [Mul P] [Mul Q]

@[to_additive (attr := simp)]
theorem toEquiv_eq_coe (f : M ≃* N) : f.toEquiv = f :=
  rfl

-- Porting note: added, to simplify `f.toMulHom` back to the coercion via `MulHomClass.toMulHom`.
@[to_additive (attr := simp)]
theorem toMulHom_eq_coe (f : M ≃* N) : f.toMulHom = ↑f :=
  rfl

-- Porting note: `to_fun_eq_coe` no longer needed in Lean4
#noalign mul_equiv.to_fun_eq_coe
#noalign add_equiv.to_fun_eq_coe

@[to_additive (attr := simp)]
theorem coe_toEquiv (f : M ≃* N) : ⇑(f : M ≃ N) = f := rfl

-- porting note: todo: `MulHom.coe_mk` simplifies `↑f.toMulHom` to `f.toMulHom.toFun`,
-- not `f.toEquiv.toFun`; use higher priority as a workaround
@[to_additive (attr := simp 1100)]
theorem coe_toMulHom {f : M ≃* N} : (f.toMulHom : M → N) = f := rfl

/-- A multiplicative isomorphism preserves multiplication. -/
@[to_additive "An additive isomorphism preserves addition."]
protected theorem map_mul (f : M ≃* N) : ∀ x y, f (x * y) = f x * f y :=
  _root_.map_mul f

/-- Makes a multiplicative isomorphism from a bijection which preserves multiplication. -/
@[to_additive "Makes an additive isomorphism from a bijection which preserves addition."]
def mk' (f : M ≃ N) (h : ∀ x y, f (x * y) = f x * f y) : M ≃* N := ⟨f, h⟩

@[to_additive]
protected theorem bijective (e : M ≃* N) : Function.Bijective e :=
  EquivLike.bijective e

@[to_additive]
protected theorem injective (e : M ≃* N) : Function.Injective e :=
  EquivLike.injective e

@[to_additive]
protected theorem surjective (e : M ≃* N) : Function.Surjective e :=
  EquivLike.surjective e

/-- The identity map is a multiplicative isomorphism. -/
@[to_additive (attr := refl) "The identity map is an additive isomorphism."]
def refl (M : Type*) [Mul M] : M ≃* M :=
  { Equiv.refl _ with map_mul' := fun _ _ => rfl }

@[to_additive]
instance : Inhabited (M ≃* M) := ⟨refl M⟩

/-- An alias for `h.symm.map_mul`. Introduced to fix the issue in
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.234183.20.60simps.60.20maximum.20recursion.20depth
-/
@[to_additive]
lemma symm_map_mul {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) (x y : N) :
    h.symm (x * y) = h.symm x * h.symm y :=
  (h.toMulHom.inverse h.toEquiv.symm h.left_inv h.right_inv).map_mul x y

/-- The inverse of an isomorphism is an isomorphism. -/
@[to_additive (attr := symm) "The inverse of an isomorphism is an isomorphism."]
def symm {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) : N ≃* M :=
  ⟨h.toEquiv.symm, h.symm_map_mul⟩

@[to_additive] -- porting note: no longer a `simp`, see below
theorem invFun_eq_symm {f : M ≃* N} : f.invFun = f.symm := rfl
-- Porting note: to_additive translated the name incorrectly in mathlib 3.

@[to_additive (attr := simp)]
theorem coe_toEquiv_symm (f : M ≃* N) : ((f : M ≃ N).symm : N → M) = f.symm := rfl

@[to_additive (attr := simp)]
theorem equivLike_inv_eq_symm (f : M ≃* N) : EquivLike.inv f = f.symm := rfl

-- we don't hyperlink the note in the additive version, since that breaks syntax highlighting
-- in the whole file.

/-- See Note [custom simps projection] -/
@[to_additive "See Note [custom simps projection]"] -- this comment fixes the syntax highlighting "
def Simps.symm_apply (e : M ≃* N) : N → M :=
  e.symm

initialize_simps_projections AddEquiv (toFun → apply, invFun → symm_apply)

initialize_simps_projections MulEquiv (toFun → apply, invFun → symm_apply)

@[to_additive (attr := simp)]
theorem toEquiv_symm (f : M ≃* N) : (f.symm : N ≃ M) = (f : M ≃ N).symm := rfl

-- porting note: doesn't align with Mathlib 3 because `MulEquiv.mk` has a new signature
@[to_additive (attr := simp)]
theorem coe_mk (f : M ≃ N) (hf : ∀ x y, f (x * y) = f x * f y) : (mk f hf : M → N) = f := rfl

-- Porting note: `toEquiv_mk` no longer needed in Lean4
#noalign mul_equiv.to_equiv_mk
#noalign add_equiv.to_equiv_mk

@[to_additive (attr := simp)]
theorem symm_symm (f : M ≃* N) : f.symm.symm = f := rfl

@[to_additive]
theorem symm_bijective : Function.Bijective (symm : M ≃* N → N ≃* M) :=
  Equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩

-- Porting note: this doesn't really align with mathlib3's `symm_mk`,
-- because the signature of `MulEquiv.mk` has changed.
@[to_additive (attr := simp)]
theorem symm_mk (f : M ≃ N) (h) :
    (MulEquiv.mk f h).symm = ⟨f.symm, (MulEquiv.mk f h).symm_map_mul⟩ := rfl

@[to_additive (attr := simp)]
theorem refl_symm : (refl M).symm = refl M := rfl

/-- Transitivity of multiplication-preserving isomorphisms -/
@[to_additive (attr := trans) "Transitivity of addition-preserving isomorphisms"]
def trans (h1 : M ≃* N) (h2 : N ≃* P) : M ≃* P :=
  { h1.toEquiv.trans h2.toEquiv with
    map_mul' := fun x y => show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y) by
      rw [h1.map_mul, h2.map_mul] }

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[to_additive (attr := simp) "`e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`."]
theorem apply_symm_apply (e : M ≃* N) (y : N) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[to_additive (attr := simp) "`e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`."]
theorem symm_apply_apply (e : M ≃* N) (x : M) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]
theorem symm_comp_self (e : M ≃* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[to_additive (attr := simp)]
theorem self_comp_symm (e : M ≃* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[to_additive (attr := simp)]
theorem coe_refl : ↑(refl M) = id := rfl

@[to_additive (attr := simp)]
theorem refl_apply (m : M) : refl M m = m := rfl

@[to_additive (attr := simp)]
theorem coe_trans (e₁ : M ≃* N) (e₂ : N ≃* P) : ↑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[to_additive (attr := simp)]
theorem trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) := rfl

@[to_additive (attr := simp)]
theorem symm_trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (p : P) :
    (e₁.trans e₂).symm p = e₁.symm (e₂.symm p) := rfl

-- Porting note: `simp` can prove this
@[to_additive]
theorem apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x = e y ↔ x = y :=
  e.injective.eq_iff

@[to_additive]
theorem apply_eq_iff_symm_apply (e : M ≃* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply

@[to_additive]
theorem symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

@[to_additive]
theorem eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[to_additive]
theorem eq_comp_symm {α : Type*} (e : M ≃* N) (f : N → α) (g : M → α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

@[to_additive]
theorem comp_symm_eq {α : Type*} (e : M ≃* N) (f : N → α) (g : M → α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g

@[to_additive]
theorem eq_symm_comp {α : Type*} (e : M ≃* N) (f : α → M) (g : α → N) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g

@[to_additive]
theorem symm_comp_eq {α : Type*} (e : M ≃* N) (f : α → M) (g : α → N) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g

@[to_additive (attr := simp)]
theorem symm_trans_self (e : M ≃* N) : e.symm.trans e = refl N :=
  FunLike.ext _ _ e.apply_symm_apply

@[to_additive (attr := simp)]
theorem self_trans_symm (e : M ≃* N) : e.trans e.symm = refl M :=
  FunLike.ext _ _ e.symm_apply_apply

-- Porting note: `simp` can prove this
@[to_additive]
theorem coe_monoidHom_refl {M} [MulOneClass M] : (refl M : M →* M) = MonoidHom.id M := rfl

-- Porting note: `simp` can prove this
@[to_additive]
theorem coe_monoidHom_trans {M N P} [MulOneClass M] [MulOneClass N] [MulOneClass P]
    (e₁ : M ≃* N) (e₂ : N ≃* P) :
    (e₁.trans e₂ : M →* P) = (e₂ : N →* P).comp ↑e₁ := rfl

/-- Two multiplicative isomorphisms agree if they are defined by the
same underlying function. -/
@[to_additive (attr := ext)
  "Two additive isomorphisms agree if they are defined by the same underlying function."]
theorem ext {f g : MulEquiv M N} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h

@[to_additive]
theorem ext_iff {f g : MulEquiv M N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

@[to_additive (attr := simp)]
theorem mk_coe (e : M ≃* N) (e' h₁ h₂ h₃) : (⟨⟨e, e', h₁, h₂⟩, h₃⟩ : M ≃* N) = e :=
  ext fun _ => rfl

@[to_additive (attr := simp)]
theorem mk_coe' (e : M ≃* N) (f h₁ h₂ h₃) : (MulEquiv.mk ⟨f, e, h₁, h₂⟩ h₃ : N ≃* M) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl

@[to_additive]
protected theorem congr_arg {f : MulEquiv M N} {x x' : M} : x = x' → f x = f x' :=
  FunLike.congr_arg f

@[to_additive]
protected theorem congr_fun {f g : MulEquiv M N} (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x

/-- The `MulEquiv` between two monoids with a unique element. -/
@[to_additive "The `AddEquiv` between two `AddMonoid`s with a unique element."]
def mulEquivOfUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N] : M ≃* N :=
  { Equiv.equivOfUnique M N with map_mul' := fun _ _ => Subsingleton.elim _ _ }

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive "There is a unique additive monoid homomorphism between two additive monoids with
  a unique element."]
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N] : Unique (M ≃* N) where
  default := mulEquivOfUnique
  uniq _ := ext fun _ => Subsingleton.elim _ _

/-!
## Monoids
-/

/-- A multiplicative isomorphism of monoids sends `1` to `1` (and is hence a monoid isomorphism). -/
@[to_additive
  "An additive isomorphism of additive monoids sends `0` to `0`
  (and is hence an additive monoid isomorphism)."]
protected theorem map_one {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) : h 1 = 1 :=
  _root_.map_one h

@[to_additive]
protected theorem map_eq_one_iff {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) {x : M} :
    h x = 1 ↔ x = 1 :=
  MulEquivClass.map_eq_one_iff h

@[to_additive]
theorem map_ne_one_iff {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) {x : M} :
    h x ≠ 1 ↔ x ≠ 1 :=
  MulEquivClass.map_ne_one_iff h

/-- A bijective `Semigroup` homomorphism is an isomorphism -/
@[to_additive (attr := simps! apply) "A bijective `AddSemigroup` homomorphism is an isomorphism"]
noncomputable def ofBijective {M N F} [Mul M] [Mul N] [MulHomClass F M N]
(f : F) (hf : Function.Bijective f) :
    M ≃* N :=
  { Equiv.ofBijective f hf with map_mul' := map_mul f }

-- porting note: todo: simplify `symm_apply` to `surjInv`?
@[to_additive (attr := simp)]
theorem ofBijective_apply_symm_apply {M N} [MulOneClass M] [MulOneClass N] {n : N} (f : M →* N)
    (hf : Function.Bijective f) : f ((Equiv.ofBijective f hf).symm n) = n :=
  (MulEquiv.ofBijective f hf).apply_symm_apply n

/-- Extract the forward direction of a multiplicative equivalence
as a multiplication-preserving function.
-/
@[to_additive "Extract the forward direction of an additive equivalence
  as an addition-preserving function."]
def toMonoidHom {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) : M →* N :=
  { h with map_one' := h.map_one }

@[to_additive (attr := simp)]
theorem coe_toMonoidHom {M N} [MulOneClass M] [MulOneClass N] (e : M ≃* N) :
    ⇑e.toMonoidHom = e := rfl

set_option linter.deprecated false in
@[to_additive]
theorem toMonoidHom_injective {M N} [MulOneClass M] [MulOneClass N] :
    Function.Injective (toMonoidHom : M ≃* N → M →* N) :=
  fun _ _ h => MulEquiv.ext (MonoidHom.ext_iff.1 h)

/-- A multiplicative analogue of `Equiv.arrowCongr`,
where the equivalence between the targets is multiplicative.
-/
@[to_additive (attr := simps apply) "An additive analogue of `Equiv.arrowCongr`,
  where the equivalence between the targets is additive."]
def arrowCongr {M N P Q : Type*} [Mul P] [Mul Q] (f : M ≃ N) (g : P ≃* Q) :
    (M → P) ≃* (N → Q) where
  toFun h n := g (h (f.symm n))
  invFun k m := g.symm (k (f m))
  left_inv h := by ext; simp
  right_inv k := by ext; simp
  map_mul' h k := by ext; simp

/-- A multiplicative analogue of `Equiv.arrowCongr`,
for multiplicative maps from a monoid to a commutative monoid.
-/
@[to_additive (attr := simps apply)
  "An additive analogue of `Equiv.arrowCongr`,
  for additive maps from an additive monoid to a commutative additive monoid."]
-- porting note: @[simps apply] removed because it was making a lemma which
-- wasn't in simp normal form.
def monoidHomCongr {M N P Q} [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q]
    (f : M ≃* N) (g : P ≃* Q) : (M →* P) ≃* (N →* Q) where
  toFun h := g.toMonoidHom.comp (h.comp f.symm.toMonoidHom)
  invFun k := g.symm.toMonoidHom.comp (k.comp f.toMonoidHom)
  left_inv h := by ext; simp
  right_inv k := by ext; simp
  map_mul' h k := by ext; simp

/-- A family of multiplicative equivalences `Π j, (Ms j ≃* Ns j)` generates a
multiplicative equivalence between `Π j, Ms j` and `Π j, Ns j`.

This is the `MulEquiv` version of `Equiv.piCongrRight`, and the dependent version of
`MulEquiv.arrowCongr`.
-/
@[to_additive (attr := simps apply)
  "A family of additive equivalences `Π j, (Ms j ≃+ Ns j)`
  generates an additive equivalence between `Π j, Ms j` and `Π j, Ns j`.

  This is the `AddEquiv` version of `Equiv.piCongrRight`, and the dependent version of
  `AddEquiv.arrowCongr`."]
def piCongrRight {η : Type*} {Ms Ns : η → Type*} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)]
    (es : ∀ j, Ms j ≃* Ns j) : (∀ j, Ms j) ≃* ∀ j, Ns j :=
  { Equiv.piCongrRight fun j => (es j).toEquiv with
    toFun := fun x j => es j (x j),
    invFun := fun x j => (es j).symm (x j),
    map_mul' := fun x y => funext fun j => (es j).map_mul (x j) (y j) }

@[to_additive (attr := simp)]
theorem piCongrRight_refl {η : Type*} {Ms : η → Type*} [∀ j, Mul (Ms j)] :
    (piCongrRight fun j => MulEquiv.refl (Ms j)) = MulEquiv.refl _ := rfl

@[to_additive (attr := simp)]
theorem piCongrRight_symm {η : Type*} {Ms Ns : η → Type*} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)]
    (es : ∀ j, Ms j ≃* Ns j) : (piCongrRight es).symm = piCongrRight fun i => (es i).symm := rfl

@[to_additive (attr := simp)]
theorem piCongrRight_trans {η : Type*} {Ms Ns Ps : η → Type*} [∀ j, Mul (Ms j)]
    [∀ j, Mul (Ns j)] [∀ j, Mul (Ps j)] (es : ∀ j, Ms j ≃* Ns j) (fs : ∀ j, Ns j ≃* Ps j) :
    (piCongrRight es).trans (piCongrRight fs) = piCongrRight fun i => (es i).trans (fs i) := rfl

/-- A family indexed by a nonempty subsingleton type is equivalent to the element at the single
index. -/
@[to_additive (attr := simps!)
  "A family indexed by a nonempty subsingleton type is
  equivalent to the element at the single index."]
def piSubsingleton {ι : Type*} (M : ι → Type*) [∀ j, Mul (M j)] [Subsingleton ι]
    (i : ι) : (∀ j, M j) ≃* M i :=
  { Equiv.piSubsingleton M i with map_mul' := fun _ _ => Pi.mul_apply _ _ _ }

/-!
# Groups
-/

/-- A multiplicative equivalence of groups preserves inversion. -/
@[to_additive "An additive equivalence of additive groups preserves negation."]
protected theorem map_inv [Group G] [DivisionMonoid H] (h : G ≃* H) (x : G) :
    h x⁻¹ = (h x)⁻¹ :=
  _root_.map_inv h x

/-- A multiplicative equivalence of groups preserves division. -/
@[to_additive "An additive equivalence of additive groups preserves subtractions."]
protected theorem map_div [Group G] [DivisionMonoid H] (h : G ≃* H) (x y : G) :
    h (x / y) = h x / h y :=
  _root_.map_div h x y

end MulEquiv

-- porting note: we want to add
-- `@[simps (config := { fullyApplied := false })]`
-- here, but it generates simp lemmas which aren't in simp normal form
-- (they have `toFun` in)
/-- Given a pair of multiplicative homomorphisms `f`, `g` such that `g.comp f = id` and
`f.comp g = id`, returns a multiplicative equivalence with `toFun = f` and `invFun = g`. This
constructor is useful if the underlying type(s) have specialized `ext` lemmas for multiplicative
homomorphisms. -/
@[to_additive
  "Given a pair of additive homomorphisms `f`, `g` such that `g.comp f = id` and
  `f.comp g = id`, returns an additive equivalence with `toFun = f` and `invFun = g`. This
  constructor is useful if the underlying type(s) have specialized `ext` lemmas for additive
  homomorphisms."]
def MulHom.toMulEquiv [Mul M] [Mul N] (f : M →ₙ* N) (g : N →ₙ* M) (h₁ : g.comp f = MulHom.id _)
    (h₂ : f.comp g = MulHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := FunLike.congr_fun h₁
  right_inv := FunLike.congr_fun h₂
  map_mul' := f.map_mul

-- porting note: the next two lemmas were added manually because `@[simps]` is generating
-- lemmas with `toFun` in
@[to_additive (attr := simp)]
theorem MulHom.toMulEquiv_apply [Mul M] [Mul N] (f : M →ₙ* N) (g : N →ₙ* M)
    (h₁ : g.comp f = MulHom.id _) (h₂ : f.comp g = MulHom.id _) :
    ((MulHom.toMulEquiv f g h₁ h₂) : M → N) = f :=
  rfl

@[to_additive (attr := simp)]
theorem MulHom.toMulEquiv_symm_apply [Mul M] [Mul N] (f : M →ₙ* N) (g : N →ₙ* M)
    (h₁ : g.comp f = MulHom.id _) (h₂ : f.comp g = MulHom.id _) :
    (MulEquiv.symm (MulHom.toMulEquiv f g h₁ h₂) : N → M) = ↑g :=
  rfl

/-- Given a pair of monoid homomorphisms `f`, `g` such that `g.comp f = id` and `f.comp g = id`,
returns a multiplicative equivalence with `toFun = f` and `invFun = g`.  This constructor is
useful if the underlying type(s) have specialized `ext` lemmas for monoid homomorphisms. -/
@[to_additive (attr := simps (config := { fullyApplied := false }))
  "Given a pair of additive monoid homomorphisms `f`, `g` such that `g.comp f = id`
  and `f.comp g = id`, returns an additive equivalence with `toFun = f` and `invFun = g`.  This
  constructor is useful if the underlying type(s) have specialized `ext` lemmas for additive
  monoid homomorphisms."]
def MonoidHom.toMulEquiv [MulOneClass M] [MulOneClass N] (f : M →* N) (g : N →* M)
    (h₁ : g.comp f = MonoidHom.id _) (h₂ : f.comp g = MonoidHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := FunLike.congr_fun h₁
  right_inv := FunLike.congr_fun h₂
  map_mul' := f.map_mul

namespace Equiv

section InvolutiveInv

variable (G) [InvolutiveInv G]

/-- Inversion on a `Group` or `GroupWithZero` is a permutation of the underlying type. -/
@[to_additive (attr := simps! (config := { fullyApplied := false }) apply)
    "Negation on an `AddGroup` is a permutation of the underlying type."]
protected def inv : Perm G :=
  inv_involutive.toPerm _

variable {G}

@[to_additive (attr := simp)]
theorem inv_symm : (Equiv.inv G).symm = Equiv.inv G := rfl

end InvolutiveInv

end Equiv
