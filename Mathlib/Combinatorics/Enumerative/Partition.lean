/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Multiset.Dedup
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic.ApplyFun

#align_import combinatorics.partition from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Partitions

A partition of a natural number `n` is a way of writing `n` as a sum of positive integers, where the
order does not matter: two sums that differ only in the order of their summands are considered the
same partition. This notion is closely related to that of a composition of `n`, but in a composition
of `n` the order does matter.
A summand of the partition is called a part.

## Main functions

* `p : Partition n` is a structure, made of a multiset of integers which are all positive and
  add up to `n`.

## Implementation details

The main motivation for this structure and its API is to show Euler's partition theorem, and
related results.

The representation of a partition as a multiset is very handy as multisets are very flexible and
already have a well-developed API.

## TODO

Link this to Young diagrams.

## Tags

Partition

## References

<https://en.wikipedia.org/wiki/Partition_(number_theory)>
-/

open Multiset

open BigOperators

namespace Nat

/-- A partition of `n` is a multiset of positive integers summing to `n`. -/
@[ext]
structure Partition (n : ℕ) where
  /-- positive integers summing to `n`-/
  parts : Multiset ℕ
  /-- proof that the `parts` are positive-/
  parts_pos : ∀ {i}, i ∈ parts → 0 < i
  /-- proof that the `parts` sum to `n`-/
  parts_sum : parts.sum = n
  -- Porting note: chokes on `parts_pos`
  --deriving DecidableEq
#align nat.partition Nat.Partition

namespace Partition

-- TODO: This should be automatically derived, see lean4#2914
instance decidableEqPartition {n : ℕ} : DecidableEq (Partition n) :=
  fun _ _ => decidable_of_iff' _ <| Partition.ext_iff _ _

/-- A composition induces a partition (just convert the list to a multiset). -/
@[simps]
def ofComposition (n : ℕ) (c : Composition n) : Partition n where
  parts := c.blocks
  parts_pos hi := c.blocks_pos hi
  parts_sum := by rw [Multiset.sum_coe, c.blocks_sum]
#align nat.partition.of_composition Nat.Partition.ofComposition

theorem ofComposition_surj {n : ℕ} : Function.Surjective (ofComposition n) := by
  rintro ⟨b, hb₁, hb₂⟩
  rcases Quotient.exists_rep b with ⟨b, rfl⟩
  exact ⟨⟨b, hb₁, by simpa using hb₂⟩, Partition.ext _ _ rfl⟩
#align nat.partition.of_composition_surj Nat.Partition.ofComposition_surj

-- The argument `n` is kept explicit here since it is useful in tactic mode proofs to generate the
-- proof obligation `l.sum = n`.
/-- Given a multiset which sums to `n`, construct a partition of `n` with the same multiset, but
without the zeros.
-/
@[simps]
def ofSums (n : ℕ) (l : Multiset ℕ) (hl : l.sum = n) : Partition n where
  parts := l.filter (· ≠ 0)
  parts_pos hi := (of_mem_filter hi).bot_lt
  parts_sum := by
    have lz : (l.filter (· = 0)).sum = 0 := by simp [sum_eq_zero_iff]
    rwa [← filter_add_not (· = 0) l, sum_add, lz, zero_add] at hl
#align nat.partition.of_sums Nat.Partition.ofSums

/-- A `Multiset ℕ` induces a partition on its sum. -/
@[simps!]
def ofMultiset (l : Multiset ℕ) : Partition l.sum := ofSums _ l rfl
#align nat.partition.of_multiset Nat.Partition.ofMultiset

/-- An element `s` of `Sym σ n` induces a partition given by its multiplicities. -/
def ofSym {n : ℕ} {σ : Type*} (s : Sym σ n) [DecidableEq σ] : n.Partition where
  parts := s.1.dedup.map s.1.count
  parts_pos := by simp [Multiset.count_pos]
  parts_sum := by
    have : sum (map (fun a ↦ count a s.1) s.1.dedup) =
      Finset.sum (toFinset s.1) fun a ↦ count a s.1 := rfl
    rw [this, Multiset.toFinset_sum_count_eq]
    exact s.2

variable {n : ℕ} {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]

lemma ofSym_map (e : σ ≃ τ) (s : Sym σ n) :
    Nat.Partition.ofSym (s.map e) = Nat.Partition.ofSym s := by
  simp only [ofSym, Sym.val_eq_coe, Sym.coe_map, toFinset_val, mk.injEq]
  rw [Multiset.dedup_map_of_injective e.injective]
  simp only [map_map, Function.comp_apply]
  congr; funext i
  rw [← Multiset.count_map_eq_count' e _ e.injective]

/-- An equivalence between `σ` and `τ` induces an equivalence between the subtypes of `Sym σ n` and
`Sym τ n` corresponding to a given partition. -/
def ofSym_shape_equiv (μ : Partition n) (e : σ ≃ τ) :
    {x : Sym σ n // Nat.Partition.ofSym x = μ} ≃ {x : Sym τ n // Nat.Partition.ofSym x = μ} where
  toFun := fun x => ⟨Sym.equivCongr e x, by simp [ofSym_map, x.2]⟩
  invFun := fun x => ⟨Sym.equivCongr e.symm x, by simp [ofSym_map, x.2]⟩
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- The partition of exactly one part. -/
def indiscrete (n : ℕ) : Partition n := ofSums n {n} rfl
#align nat.partition.indiscrete_partition Nat.Partition.indiscrete

instance {n : ℕ} : Inhabited (Partition n) := ⟨indiscrete n⟩

@[simp] lemma indiscrete_parts {n : ℕ} (hn : n ≠ 0) : (indiscrete n).parts = {n} := by
  simp [indiscrete, filter_eq_self, hn]

@[simp] lemma partition_zero_parts (p : Partition 0) : p.parts = 0 :=
  eq_zero_of_forall_not_mem fun _ h => (p.parts_pos h).ne' <| sum_eq_zero_iff.1 p.parts_sum _ h

instance UniquePartitionZero : Unique (Partition 0) where
  uniq _ := Partition.ext _ _ <| by simp

@[simp] lemma partition_one_parts (p : Partition 1) : p.parts = {1} := by
  have h : p.parts = replicate (card p.parts) 1 := eq_replicate_card.2 fun x hx =>
    ((le_sum_of_mem hx).trans_eq p.parts_sum).antisymm (p.parts_pos hx)
  have h' : card p.parts = 1 := by simpa using (congrArg sum h.symm).trans p.parts_sum
  rw [h, h', replicate_one]

instance UniquePartitionOne : Unique (Partition 1) where
  uniq _ := Partition.ext _ _ <| by simp

lemma ofSym_one (s : Sym σ 1) : Nat.Partition.ofSym s = Nat.Partition.indiscrete 1 := by
  ext; simp

/-- The equivalence between `σ` and `1`-tuples of elements of σ -/
def ofSym_equiv_onePart (σ : Type*) [DecidableEq σ] : σ ≃
    { a : Sym σ 1 // Nat.Partition.ofSym a = Nat.Partition.indiscrete 1 } where
  toFun := fun a => ⟨Sym.oneEquiv a, by ext; simp⟩
  invFun := fun a => Sym.oneEquiv.symm a.1
  left_inv := by intro a; simp only [Sym.oneEquiv_apply]; rfl
  right_inv := by intro a; simp only [Equiv.apply_symm_apply, Subtype.coe_eta]

@[simp]
lemma ofSym_equiv_onePart_apply (i : σ) :
    ((Nat.Partition.ofSym_equiv_onePart σ) i : Multiset σ) = {i} := rfl

/-- The number of times a positive integer `i` appears in the partition `ofSums n l hl` is the same
as the number of times it appears in the multiset `l`.
(For `i = 0`, `Partition.non_zero` combined with `Multiset.count_eq_zero_of_not_mem` gives that
this is `0` instead.)
-/
theorem count_ofSums_of_ne_zero {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) {i : ℕ} (hi : i ≠ 0) :
    (ofSums n l hl).parts.count i = l.count i :=
  count_filter_of_pos hi
#align nat.partition.count_of_sums_of_ne_zero Nat.Partition.count_ofSums_of_ne_zero

theorem count_ofSums_zero {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) :
    (ofSums n l hl).parts.count 0 = 0 :=
  count_filter_of_neg fun h => h rfl
#align nat.partition.count_of_sums_zero Nat.Partition.count_ofSums_zero

/-- Show there are finitely many partitions by considering the surjection from compositions to
partitions.
-/
instance (n : ℕ) : Fintype (Partition n) :=
  Fintype.ofSurjective (ofComposition n) ofComposition_surj

/-- The finset of those partitions in which every part is odd. -/
def odds (n : ℕ) : Finset (Partition n) :=
  Finset.univ.filter fun c => ∀ i ∈ c.parts, ¬Even i
#align nat.partition.odds Nat.Partition.odds

/-- The finset of those partitions in which each part is used at most once. -/
def distincts (n : ℕ) : Finset (Partition n) :=
  Finset.univ.filter fun c => c.parts.Nodup
#align nat.partition.distincts Nat.Partition.distincts

/-- The finset of those partitions in which every part is odd and used at most once. -/
def oddDistincts (n : ℕ) : Finset (Partition n) :=
  odds n ∩ distincts n
#align nat.partition.odd_distincts Nat.Partition.oddDistincts

end Partition

end Nat
