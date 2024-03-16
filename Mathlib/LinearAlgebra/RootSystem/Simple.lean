/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Systems of simple roots and bases of a root system

This file defines systems of simple roots in a root system.

## Main definitions

* `Thin` : A root system is thin if it admits a functional such that there are only finitely many
roots in the preimage of any interval.  This lets us do inductive constructions of the Cartan
matrix given a basis.
* `RegularElement` : Given a thin root system, a regular element is a linear functional on the
root space that takes no roots to zero.  This corresponds to an element of a Lie algebra with
minimal centralizer.
* `Separation` : A subset of `positive` elements, closed under addition, such that any root is
either positive, or minus one times a positive root.
* `IsIrreducible` : Given a regular element, a root is irreducible if it is positive and is not the
sum of two positive roots.
* `Base`: Given a root pairing and separation, a base is a minimal subset that generates the
positive half.

## Results

None yet

## Todo

* Any regular element yields a separation
* Any base is made of irreducible elements - reducibles would violate minimality?
* The irreducible elements of a separation form a base.
* Any separation (satisfying some condition) comes from some regular element.

* A base is linearly independent in the positive definite case. (use obtuse lemma)

* Define: Cartan Matrices.



## References

* Moody, Pianzola, "Infinite root systems"

-/

variable {ι R M N} [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) (i : ι)

noncomputable section

namespace RootPairing

/-- An element in the coroot space is preregular if any interval in `R` has finite preimage. -/
def IsPreregular (x : N) : Prop := ∀ (n : R), 0 ≤ n →
  Finite { i | 0 ≤ (P.toLin (P.root i) x) ∧ (P.toLin (P.root i) x) ≤ n}

theorem finite_preregular [Finite ι] (x : N) : IsPreregular P x :=
  fun n _ ↦ Finite.Set.finite_inter_of_left (fun i ↦ Preorder.toLE.1 0 ((P.toLin (P.root i)) x))
    fun i ↦ Preorder.toLE.1 ((P.toLin (P.root i)) x) n

/-- A root pairing is thin if there is a preregular element.  Borcherds-Kac-Moody Lie
algebras more or less admit a `ℤ`-grading with finite dimensional pieces (except for Cartan), so
their root systems are always thin. -/
def IsThin : Prop := ∃ (x : N), IsPreregular P x

/-- A regular element is a preregular element that takes no roots to zero. -/
def IsRegularElement (x : N) : Prop := (IsPreregular P x) ∧ ∀(i : ι), P.toLin (P.root i) x ≠ 0

/-- A separation is a subset of roots, called `positive`, such that all roots are either positive or
minus one times positive, and any root that is the sums of positive roots is positive.-/
structure Separation (P : RootPairing ι R M N) where
  pos : ι → Prop
  pos_iff : ∀ i j, P.root i + P.root j = 0 → (pos i ↔ ¬ pos j)
  add_pos : ∀ i j k, pos i → pos j → P.root k = P.root i + P.root j → pos k

/-- Produce a separation from a regular element. (This does not use the preregular property, and
perhaps we should remove and rename that property.  Such a property only makes the separation robust
against small perturbations.)-/
def separation_of_regular (x : N) (hx : IsRegularElement P x) :
    Separation P where
  pos := fun i => P.toLin (P.root i) x > 0
  pos_iff := fun i j hij => by
    have hij' : P.root j = - P.root i := (neg_eq_of_add_eq_zero_right hij).symm
    constructor
    · intro hi
      simp_all only [gt_iff_lt, not_lt, add_right_neg, map_neg, LinearMap.neg_apply,
        Left.neg_nonpos_iff]
      linarith
    · intro hi
      simp_all only [add_right_neg, map_neg, LinearMap.neg_apply, gt_iff_lt, Left.neg_pos_iff,
        not_lt]
      have hi' : P.toLin (P.root i) x ≠ 0 := by
        simp_all only [IsRegularElement, ne_eq, not_false_eq_true]
      exact lt_of_le_of_ne hi (id (Ne.symm hi'))
  add_pos := fun i j k hi hj hijk => by
    simp_all only [gt_iff_lt, map_add, LinearMap.add_apply]
    linarith

/-- A root is decomposable (with respect to a regular element `x`) if it is positive, and is the
sum of two positive roots. -/
def IsDecomposableFor (i : ι) (s : Set ι) : Prop :=
  i ∈ s ∧ ∃ (a b : ι), P.root a + P.root b = P.root i ∧ a ∈ s ∧ b ∈ s

/-- An root is indecomposable if it is positive, and cannot be written as a sum of two positive
roots. -/
def IsIndecomposableFor (x : N) (i : ι) : Prop :=
  P.toLin (P.root i) x > 0 ∧ ¬ ∃(a b : ι),
  P.toLin (P.root a) x > 0 ∧ P.toLin (P.root b) x > 0 ∧ P.root i = P.root a + P.root b

/-!
lemma if `x` is regular, and ι is finite then the indecomposable elements for `x` are a base.
(tricky to generalize, since the proof uses positive-definiteness - maybe semidefinite is okay, so
we can do affine roots.  False in general.)

Make a Cartan matrix.

Show that the Cartan matrix is unique?
Show that there is one Weyl orbit of bases, up to sign?

-/

-- Maybe remove the following?  It only works for finite root systems.

/-- View a root as an element of the span of roots. -/
def root' : ι → (Submodule.span R (Set.range P.root)) :=
  fun i => ⟨P.root i, Submodule.subset_span <| @Set.mem_range_self _ _ P.root i⟩
/-!
/-- A base is a parametrized subset of roots forming an `R`-basis of the span of roots, such
that the coordinates of any root are all nonpositive or all nonnegative. (maybe just restrict this
definition to root systems?)-/
structure Base extends Basis α R (Submodule.span R (Set.range P.root)) where
  /-- An injection from the type parametrizing the basis to the type parametrizing roots. -/
  f : α ↪ ι
  /-- Any basis vector is equal to the corresponding root. -/
  eq_root : ∀ (i : α), DFunLike.coe repr.symm (Finsupp.single i 1) = P.root (f i)
  /-- Any root has same-sign coordinates with respect to the basis. -/
  same_sign : ∀(i : ι) (j k : α), 0 ≤ (repr (P.root' i) j) * (repr (P.root' i) k)
-/
