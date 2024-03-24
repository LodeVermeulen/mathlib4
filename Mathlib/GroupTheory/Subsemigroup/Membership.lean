/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.GroupTheory.Subsemigroup.Basic

#align_import group_theory.subsemigroup.membership from "leanprover-community/mathlib"@"6cb77a8eaff0ddd100e87b1591c6d3ad319514ff"

/-!
# Subsemigroups: membership criteria

In this file we prove various facts about membership in a subsemigroup.
The intent is to mimic `GroupTheory/Submonoid/Membership`, but currently this file is mostly a
stub and only provides rudimentary support.

* `mem_iSup_of_directed`, `coe_iSup_of_directed`, `mem_sSup_of_directed_on`,
  `coe_sSup_of_directed_on`: the supremum of a directed collection of subsemigroup is their union.

## TODO

* Define the `FreeSemigroup` generated by a set. This might require some rather substantial
  additions to low-level API. For example, developing the subtype of nonempty lists, then defining
  a product on nonempty lists, powers where the exponent is a positive natural, et cetera.
  Another option would be to define the `FreeSemigroup` as the subsemigroup (pushed to be a
  semigroup) of the `FreeMonoid` consisting of non-identity elements.

## Tags
subsemigroup
-/

variable {ι : Sort*} {M A B : Type*}

section NonAssoc

variable [Mul M]

open Set

namespace Subsemigroup

-- TODO: this section can be generalized to `[MulMemClass B M] [CompleteLattice B]`
-- such that `complete_lattice.le` coincides with `set_like.le`
@[to_additive]
theorem mem_iSup_of_directed {S : ι → Subsemigroup M} (hS : Directed (· ≤ ·) S) {x : M} :
    (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ le_iSup S i hi⟩
  suffices x ∈ closure (⋃ i, (S i : Set M)) → ∃ i, x ∈ S i by
    simpa only [closure_iUnion, closure_eq (S _)] using this
  refine fun hx ↦ closure_induction hx (fun y hy ↦ mem_iUnion.mp hy) ?_
  · rintro x y ⟨i, hi⟩ ⟨j, hj⟩
    rcases hS i j with ⟨k, hki, hkj⟩
    exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩
#align subsemigroup.mem_supr_of_directed Subsemigroup.mem_iSup_of_directed
#align add_subsemigroup.mem_supr_of_directed AddSubsemigroup.mem_iSup_of_directed

@[to_additive]
theorem coe_iSup_of_directed {S : ι → Subsemigroup M} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subsemigroup M) : Set M) = ⋃ i, S i :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]
#align subsemigroup.coe_supr_of_directed Subsemigroup.coe_iSup_of_directed
#align add_subsemigroup.coe_supr_of_directed AddSubsemigroup.coe_iSup_of_directed

@[to_additive]
theorem mem_sSup_of_directed_on {S : Set (Subsemigroup M)} (hS : DirectedOn (· ≤ ·) S) {x : M} :
    x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, Subtype.coe_mk,
    exists_prop]
#align subsemigroup.mem_Sup_of_directed_on Subsemigroup.mem_sSup_of_directed_on
#align add_subsemigroup.mem_Sup_of_directed_on AddSubsemigroup.mem_sSup_of_directed_on

@[to_additive]
theorem coe_sSup_of_directed_on {S : Set (Subsemigroup M)} (hS : DirectedOn (· ≤ ·) S) :
    (↑(sSup S) : Set M) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directed_on hS]
#align subsemigroup.coe_Sup_of_directed_on Subsemigroup.coe_sSup_of_directed_on
#align add_subsemigroup.coe_Sup_of_directed_on AddSubsemigroup.coe_sSup_of_directed_on

@[to_additive]
theorem mem_sup_left {S T : Subsemigroup M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T := by
  have : S ≤ S ⊔ T := le_sup_left
  tauto
#align subsemigroup.mem_sup_left Subsemigroup.mem_sup_left
#align add_subsemigroup.mem_sup_left AddSubsemigroup.mem_sup_left

@[to_additive]
theorem mem_sup_right {S T : Subsemigroup M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T := by
  have : T ≤ S ⊔ T := le_sup_right
  tauto
#align subsemigroup.mem_sup_right Subsemigroup.mem_sup_right
#align add_subsemigroup.mem_sup_right AddSubsemigroup.mem_sup_right

@[to_additive]
theorem mul_mem_sup {S T : Subsemigroup M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T :=
  mul_mem (mem_sup_left hx) (mem_sup_right hy)
#align subsemigroup.mul_mem_sup Subsemigroup.mul_mem_sup
#align add_subsemigroup.add_mem_sup AddSubsemigroup.add_mem_sup

@[to_additive]
theorem mem_iSup_of_mem {S : ι → Subsemigroup M} (i : ι) : ∀ {x : M}, x ∈ S i → x ∈ iSup S := by
  have : S i ≤ iSup S := le_iSup _ _
  tauto
#align subsemigroup.mem_supr_of_mem Subsemigroup.mem_iSup_of_mem
#align add_subsemigroup.mem_supr_of_mem AddSubsemigroup.mem_iSup_of_mem

@[to_additive]
theorem mem_sSup_of_mem {S : Set (Subsemigroup M)} {s : Subsemigroup M} (hs : s ∈ S) :
    ∀ {x : M}, x ∈ s → x ∈ sSup S := by
  have : s ≤ sSup S := le_sSup hs
  tauto
#align subsemigroup.mem_Sup_of_mem Subsemigroup.mem_sSup_of_mem
#align add_subsemigroup.mem_Sup_of_mem AddSubsemigroup.mem_sSup_of_mem

/-- An induction principle for elements of `⨆ i, S i`.
If `C` holds all elements of `S i` for all `i`, and is preserved under multiplication,
then it holds for all elements of the supremum of `S`. -/
@[to_additive (attr := elab_as_elim)
"An induction principle for elements of `⨆ i, S i`. If `C` holds all
elements of `S i` for all `i`, and is preserved under addition, then it holds for all elements of
the supremum of `S`."]
theorem iSup_induction (S : ι → Subsemigroup M) {C : M → Prop} {x₁ : M} (hx₁ : x₁ ∈ ⨆ i, S i)
    (mem : ∀ i, ∀ x₂ ∈ S i, C x₂) (mul : ∀ x y, C x → C y → C (x * y)) : C x₁ := by
  rw [iSup_eq_closure] at hx₁
  refine' closure_induction hx₁ (fun x₂ hx₂ => _) mul
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx₂
  exact mem _ _ hi
#align subsemigroup.supr_induction Subsemigroup.iSup_induction
#align add_subsemigroup.supr_induction AddSubsemigroup.iSup_induction

/-- A dependent version of `Subsemigroup.iSup_induction`. -/
@[to_additive (attr := elab_as_elim)
"A dependent version of `AddSubsemigroup.iSup_induction`."]
theorem iSup_induction' (S : ι → Subsemigroup M) {C : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    (mem : ∀ (i) (x) (hxS : x ∈ S i), C x (mem_iSup_of_mem i ‹_›))
    (mul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem ‹_› ‹_›)) {x₁ : M}
    (hx₁ : x₁ ∈ ⨆ i, S i) : C x₁ hx₁ := by
  refine Exists.elim ?_ fun (hx₁' : x₁ ∈ ⨆ i, S i) (hc : C x₁ hx₁') => hc
  refine @iSup_induction _ _ _ S (fun x' => ∃ hx'', C x' hx'') _ hx₁
      (fun i x₂ hx₂ => ?_) fun x₃ y => ?_
  · exact ⟨_, mem _ _ hx₂⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, mul _ _ _ _ Cx Cy⟩
#align subsemigroup.supr_induction' Subsemigroup.iSup_induction'
#align add_subsemigroup.supr_induction' AddSubsemigroup.iSup_induction'

end Subsemigroup

end NonAssoc
