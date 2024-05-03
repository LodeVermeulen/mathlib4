/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Combinatorics.Additive.FreimanHom

#align_import combinatorics.additive.salem_spencer from "leanprover-community/mathlib"@"acf5258c81d0bc7cb254ed026c1352e685df306c"

/-!
# Salem-Spencer sets and Roth numbers

This file defines Salem-Spencer sets and the Roth number of a set.

A Salem-Spencer set is a set without arithmetic progressions of length `3`. Equivalently, the
average of any two distinct elements is not in the set.

The Roth number of a finset is the size of its biggest Salem-Spencer subset. This is a more general
definition than the one often found in mathematical literature, where the `n`-th Roth number is
the size of the biggest Salem-Spencer subset of `{0, ..., n - 1}`.

## Main declarations

* `MulSalemSpencer`: Predicate for a set to be multiplicative Salem-Spencer.
* `AddSalemSpencer`: Predicate for a set to be additive Salem-Spencer.
* `mulRothNumber`: The multiplicative Roth number of a finset.
* `addRothNumber`: The additive Roth number of a finset.
* `rothNumberNat`: The Roth number of a natural. This corresponds to
  `addRothNumber (Finset.range n)`.

## TODO

* Can `addSalemSpencer_iff_eq_right` be made more general?
* Generalize `MulSalemSpencer.image` to Freiman homs

## Tags

Salem-Spencer, Roth, arithmetic progression, average, three-free
-/


open Finset Function Metric Nat

open Pointwise

variable {F α β 𝕜 E : Type*}

section SalemSpencer

open Set

section Monoid

variable [Monoid α] [Monoid β] (s t : Set α)

/-- A multiplicative Salem-Spencer, aka non averaging, set `s` in a monoid is a set such that the
multiplicative average of any two distinct elements is not in the set. -/
@[to_additive "A Salem-Spencer, aka non averaging, set `s` in an additive monoid
is a set such that the average of any two distinct elements is not in the set."]
def MulSalemSpencer : Prop :=
  ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a * c = b * b → a = b
#align mul_salem_spencer MulSalemSpencer
#align add_salem_spencer AddSalemSpencer

/-- Whether a given finset is Salem-Spencer is decidable. -/
@[to_additive "Whether a given finset is Salem-Spencer is decidable."]
instance {α : Type*} [DecidableEq α] [Monoid α] {s : Finset α} :
    Decidable (MulSalemSpencer (s : Set α)) :=
  decidable_of_iff (∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a * c = b * b → a = b) Iff.rfl

variable {s t}

@[to_additive]
theorem MulSalemSpencer.mono (h : t ⊆ s) (hs : MulSalemSpencer s) : MulSalemSpencer t :=
  fun _ ha _ hb _ hc ↦ hs (h ha) (h hb) (h hc)
#align mul_salem_spencer.mono MulSalemSpencer.mono
#align add_salem_spencer.mono AddSalemSpencer.mono

@[to_additive (attr := simp)]
theorem mulSalemSpencer_empty : MulSalemSpencer (∅ : Set α) := fun _ _ _ ha => ha.elim
#align mul_salem_spencer_empty mulSalemSpencer_empty
#align add_salem_spencer_empty addSalemSpencer_empty

@[to_additive]
theorem Set.Subsingleton.mulSalemSpencer (hs : s.Subsingleton) : MulSalemSpencer s :=
  fun _ ha _ hb _ _ _ ↦ hs ha hb
#align set.subsingleton.mul_salem_spencer Set.Subsingleton.mulSalemSpencer
#align set.subsingleton.add_salem_spencer Set.Subsingleton.addSalemSpencer

@[to_additive (attr := simp)]
theorem mulSalemSpencer_singleton (a : α) : MulSalemSpencer ({a} : Set α) :=
  subsingleton_singleton.mulSalemSpencer
#align mul_salem_spencer_singleton mulSalemSpencer_singleton
#align add_salem_spencer_singleton addSalemSpencer_singleton

@[to_additive AddSalemSpencer.prod]
theorem MulSalemSpencer.prod {t : Set β} (hs : MulSalemSpencer s) (ht : MulSalemSpencer t) :
    MulSalemSpencer (s ×ˢ t) := fun _ ha _ hb _ hc h ↦
  Prod.ext (hs ha.1 hb.1 hc.1 (Prod.ext_iff.1 h).1) (ht ha.2 hb.2 hc.2 (Prod.ext_iff.1 h).2)
#align mul_salem_spencer.prod MulSalemSpencer.prod
#align add_salem_spencer.prod AddSalemSpencer.prod

@[to_additive]
theorem mulSalemSpencer_pi {ι : Type*} {α : ι → Type*} [∀ i, Monoid (α i)] {s : ∀ i, Set (α i)}
    (hs : ∀ i, MulSalemSpencer (s i)) : MulSalemSpencer ((univ : Set ι).pi s) :=
  fun _ ha _ hb _ hc h ↦
  funext fun i => hs i (ha i trivial) (hb i trivial) (hc i trivial) <| congr_fun h i
#align mul_salem_spencer_pi mulSalemSpencer_pi
#align add_salem_spencer_pi addSalemSpencer_pi

end Monoid

section CommMonoid
variable [CommMonoid α] [CommMonoid β] {s : Set α} {t : Set β} {f : α → β} {a : α}

/-- Arithmetic progressions of length three are preserved under `2`-Freiman homomorphisms. --/
@[to_additive]
lemma IsMulFreimanHom.mulSalemSpencer (hf : IsMulFreimanHom 2 s t f) (hf' : s.InjOn f)
    (ht : MulSalemSpencer t) : MulSalemSpencer s :=
  fun _ ha _ hb _ hc habc ↦ hf' ha hb <| ht (hf.mapsTo ha) (hf.mapsTo hb) (hf.mapsTo hc) <|
    hf.mul_eq_mul ha hc hb hb habc
#align mul_salem_spencer.of_image IsMulFreimanHom.mulSalemSpencer
#align add_salem_spencer.of_image IsAddFreimanHom.addSalemSpencer

/-- Arithmetic progressions of length three are preserved under `2`-Freiman isomorphisms. --/
@[to_additive]
lemma IsMulFreimanIso.mulSalemSpencer_congr (hf : IsMulFreimanIso 2 s t f) :
    MulSalemSpencer s ↔ MulSalemSpencer t where
  mpr := hf.isMulFreimanHom.mulSalemSpencer hf.bijOn.injOn
  mp hs a hfa b hfb c hfc habc := by
    obtain ⟨a, ha, rfl⟩ := hf.bijOn.surjOn hfa
    obtain ⟨b, hb, rfl⟩ := hf.bijOn.surjOn hfb
    obtain ⟨c, hc, rfl⟩ := hf.bijOn.surjOn hfc
    exact congr_arg f $ hs ha hb hc $ (hf.mul_eq_mul ha hc hb hb).1 habc

@[to_additive]
theorem MulSalemSpencer.image [FunLike F α β] [MulHomClass F α β] (f : F) (hf : (s * s).InjOn f)
    (h : MulSalemSpencer s) : MulSalemSpencer (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ habc
  rw [h ha hb hc (hf (mul_mem_mul ha hc) (mul_mem_mul hb hb) <| by rwa [map_mul, map_mul])]
#align mul_salem_spencer.image MulSalemSpencer.image
#align add_salem_spencer.image AddSalemSpencer.image

end CommMonoid

section CancelCommMonoid

variable [CancelCommMonoid α] {s : Set α} {a : α}

lemma MulSalemSpencer.eq_right (hs : MulSalemSpencer s) :
    ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a * c = b * b → b = c := by
  rintro a ha b hb c hc habc
  obtain rfl := hs ha hb hc habc
  simpa using habc.symm

@[to_additive] lemma mulSalemSpencer_insert :
    MulSalemSpencer (insert a s) ↔ MulSalemSpencer s ∧
      (∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a * c = b * b → a = b) ∧
        ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → b * c = a * a → b = a := by
  refine ⟨fun hs ↦ ⟨hs.mono (subset_insert _ _),
    fun b hb c hc ↦ hs (Or.inl rfl) (Or.inr hb) (Or.inr hc),
    fun b hb c hc ↦ hs (Or.inr hb) (Or.inl rfl) (Or.inr hc)⟩, ?_⟩
  rintro ⟨hs, ha, ha'⟩ b hb c hc d hd h
  rw [mem_insert_iff] at hb hc hd
  obtain rfl | hb := hb <;> obtain rfl | hc := hc
  · rfl
  all_goals obtain rfl | hd := hd
  · exact (ha' hc hc h.symm).symm
  · exact ha hc hd h
  · exact mul_right_cancel h
  · exact ha' hb hd h
  · obtain rfl := ha hc hb ((mul_comm _ _).trans h)
    exact ha' hb hc h
  · exact hs hb hc hd h
#align mul_salem_spencer_insert mulSalemSpencer_insert
#align add_salem_spencer_insert addSalemSpencer_insert

@[to_additive]
theorem MulSalemSpencer.smul_set (hs : MulSalemSpencer s) : MulSalemSpencer (a • s) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
  exact congr_arg (a • ·) $ hs hb hc hd $ by simpa [mul_mul_mul_comm _ _ a] using h
#align mul_salem_spencer.mul_left MulSalemSpencer.smul_set
#align add_salem_spencer.add_left AddSalemSpencer.vadd_set

#noalign mul_salem_spencer.mul_right
#noalign add_salem_spencer.add_right

@[to_additive]
theorem mulSalemSpencer_smul_set : MulSalemSpencer ((a * ·) '' s) ↔ MulSalemSpencer s :=
  ⟨fun hs b hb c hc d hd h ↦
    mul_left_cancel
      (hs (mem_image_of_mem _ hb) (mem_image_of_mem _ hc) (mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_comm, h, mul_mul_mul_comm]),
    MulSalemSpencer.smul_set⟩
#align mul_salem_spencer_mul_left_iff mulSalemSpencer_smul_set
#align add_salem_spencer_add_left_iff addSalemSpencer_vadd_set

#noalign mul_salem_spencer_mul_right_iff
#noalign add_salem_spencer_add_right_iff

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] {s : Set α} {a : α}

@[to_additive]
theorem mulSalemSpencer_insert_of_lt (hs : ∀ i ∈ s, i < a) :
    MulSalemSpencer (insert a s) ↔
      MulSalemSpencer s ∧ ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a * c = b * b → a = b := by
  refine' mulSalemSpencer_insert.trans _
  rw [← and_assoc]
  exact and_iff_left fun b hb c hc h => ((mul_lt_mul_of_lt_of_lt (hs _ hb) (hs _ hc)).ne h).elim
#align mul_salem_spencer_insert_of_lt mulSalemSpencer_insert_of_lt
#align add_salem_spencer_insert_of_lt addSalemSpencer_insert_of_lt

end OrderedCancelCommMonoid

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α] [NoZeroDivisors α] {s : Set α} {a : α}

theorem MulSalemSpencer.smul_set₀ (hs : MulSalemSpencer s) (ha : a ≠ 0) :
    MulSalemSpencer ((a * ·) '' s) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
  exact congr_arg (a • ·) $ hs hb hc hd $ by simpa [mul_mul_mul_comm _ _ a, ha] using h
#align mul_salem_spencer.mul_left₀ MulSalemSpencer.smul_set₀

#noalign mul_salem_spencer.mul_right₀.mul_right₀

theorem mulSalemSpencer_smul_set₀ (ha : a ≠ 0) : MulSalemSpencer (a • s) ↔ MulSalemSpencer s :=
  ⟨fun hs b hb c hc d hd h ↦
    mul_left_cancel₀ ha
      (hs (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd) <| by
        rw [smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, h, mul_mul_mul_comm]),
    fun hs => hs.smul_set₀ ha⟩
#align mul_salem_spencer_mul_left_iff₀ mulSalemSpencer_smul_set₀

#noalign mul_salem_spencer_mul_right_iff₀

end CancelCommMonoidWithZero

section Nat

theorem addSalemSpencer_iff_eq_right {s : Set ℕ} :
    AddSalemSpencer s ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a + c = b + b → a = c := by
  refine' forall₄_congr fun a _ha b hb => forall₃_congr fun c hc habc => ⟨_, _⟩
  · rintro rfl
    exact (add_left_cancel habc).symm
  · rintro rfl
    simp_rw [← two_mul] at habc
    exact mul_left_cancel₀ two_ne_zero habc
#align add_salem_spencer_iff_eq_right addSalemSpencer_iff_eq_right

end Nat

/-- The frontier of a closed strictly convex set only contains trivial arithmetic progressions.
The idea is that an arithmetic progression is contained on a line and the frontier of a strictly
convex set does not contain lines. -/
theorem addSalemSpencer_frontier [LinearOrderedField 𝕜] [TopologicalSpace E] [AddCommMonoid E]
    [Module 𝕜 E] {s : Set E} (hs₀ : IsClosed s) (hs₁ : StrictConvex 𝕜 s) :
    AddSalemSpencer (frontier s) := by
  intro a ha b hb c hc habc
  obtain rfl : (1 / 2 : 𝕜) • a + (1 / 2 : 𝕜) • c = b := by
    rwa [← smul_add, one_div, inv_smul_eq_iff₀ (show (2 : 𝕜) ≠ 0 by norm_num), two_smul]
  have :=
    hs₁.eq (hs₀.frontier_subset ha) (hs₀.frontier_subset hc) one_half_pos one_half_pos
      (add_halves _) hb.2
  simp [this, ← add_smul]
  ring_nf
  simp
#align add_salem_spencer_frontier addSalemSpencer_frontier

theorem addSalemSpencer_sphere [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]
    (x : E) (r : ℝ) : AddSalemSpencer (sphere x r) := by
  obtain rfl | hr := eq_or_ne r 0
  · rw [sphere_zero]
    exact addSalemSpencer_singleton _
  · convert addSalemSpencer_frontier isClosed_ball (strictConvex_closedBall ℝ x r)
    exact (frontier_closedBall _ hr).symm
#align add_salem_spencer_sphere addSalemSpencer_sphere

end SalemSpencer

open Finset

section RothNumber

variable [DecidableEq α]

section Monoid

variable [Monoid α] [DecidableEq β] [Monoid β] (s t : Finset α)

/-- The multiplicative Roth number of a finset is the cardinality of its biggest multiplicative
Salem-Spencer subset. -/
@[to_additive "The additive Roth number of a finset is the cardinality of its biggest additive
Salem-Spencer subset. The usual Roth number corresponds to `addRothNumber (Finset.range n)`, see
`rothNumberNat`. "]
def mulRothNumber : Finset α →o ℕ :=
  ⟨fun s ↦ Nat.findGreatest (fun m ↦ ∃ t ⊆ s, t.card = m ∧ MulSalemSpencer (t : Set α)) s.card, by
    rintro t u htu
    refine' Nat.findGreatest_mono (fun m => _) (card_le_card htu)
    rintro ⟨v, hvt, hv⟩
    exact ⟨v, hvt.trans htu, hv⟩⟩
#align mul_roth_number mulRothNumber
#align add_roth_number addRothNumber

@[to_additive]
theorem mulRothNumber_le : mulRothNumber s ≤ s.card := Nat.findGreatest_le s.card
#align mul_roth_number_le mulRothNumber_le
#align add_roth_number_le addRothNumber_le

@[to_additive]
theorem mulRothNumber_spec :
    ∃ t ⊆ s, t.card = mulRothNumber s ∧ MulSalemSpencer (t : Set α) :=
  Nat.findGreatest_spec (P := fun m ↦ ∃ t ⊆ s, t.card = m ∧ MulSalemSpencer (t : Set α))
    (Nat.zero_le _) ⟨∅, empty_subset _, card_empty, by norm_cast; exact mulSalemSpencer_empty⟩
#align mul_roth_number_spec mulRothNumber_spec
#align add_roth_number_spec addRothNumber_spec

variable {s t} {n : ℕ}

@[to_additive]
theorem MulSalemSpencer.le_mulRothNumber (hs : MulSalemSpencer (s : Set α)) (h : s ⊆ t) :
    s.card ≤ mulRothNumber t :=
  le_findGreatest (card_le_card h) ⟨s, h, rfl, hs⟩
#align mul_salem_spencer.le_mul_roth_number MulSalemSpencer.le_mulRothNumber
#align add_salem_spencer.le_add_roth_number AddSalemSpencer.le_addRothNumber

@[to_additive]
theorem MulSalemSpencer.mulRothNumber_eq (hs : MulSalemSpencer (s : Set α)) :
    mulRothNumber s = s.card :=
  (mulRothNumber_le _).antisymm <| hs.le_mulRothNumber <| Subset.refl _
#align mul_salem_spencer.roth_number_eq MulSalemSpencer.mulRothNumber_eq
#align add_salem_spencer.roth_number_eq AddSalemSpencer.addRothNumber_eq

@[to_additive (attr := simp)]
theorem mulRothNumber_empty : mulRothNumber (∅ : Finset α) = 0 :=
  Nat.eq_zero_of_le_zero <| (mulRothNumber_le _).trans card_empty.le
#align mul_roth_number_empty mulRothNumber_empty
#align add_roth_number_empty addRothNumber_empty

@[to_additive (attr := simp)]
theorem mulRothNumber_singleton (a : α) : mulRothNumber ({a} : Finset α) = 1 := by
  refine' MulSalemSpencer.mulRothNumber_eq _
  rw [coe_singleton]
  exact mulSalemSpencer_singleton a
#align mul_roth_number_singleton mulRothNumber_singleton
#align add_roth_number_singleton addRothNumber_singleton

@[to_additive]
theorem mulRothNumber_union_le (s t : Finset α) :
    mulRothNumber (s ∪ t) ≤ mulRothNumber s + mulRothNumber t :=
  let ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s ∪ t)
  calc
    mulRothNumber (s ∪ t) = u.card := hcard.symm
    _ = (u ∩ s ∪ u ∩ t).card := by rw [← inter_union_distrib_left, inter_eq_left.2 hus]
    _ ≤ (u ∩ s).card + (u ∩ t).card := card_union_le _ _
    _ ≤ mulRothNumber s + mulRothNumber t := _root_.add_le_add
      ((hu.mono <| inter_subset_left _ _).le_mulRothNumber <| inter_subset_right _ _)
      ((hu.mono <| inter_subset_left _ _).le_mulRothNumber <| inter_subset_right _ _)
#align mul_roth_number_union_le mulRothNumber_union_le
#align add_roth_number_union_le addRothNumber_union_le

@[to_additive]
theorem le_mulRothNumber_product (s : Finset α) (t : Finset β) :
    mulRothNumber s * mulRothNumber t ≤ mulRothNumber (s ×ˢ t) := by
  obtain ⟨u, hus, hucard, hu⟩ := mulRothNumber_spec s
  obtain ⟨v, hvt, hvcard, hv⟩ := mulRothNumber_spec t
  rw [← hucard, ← hvcard, ← card_product]
  refine' MulSalemSpencer.le_mulRothNumber _ (product_subset_product hus hvt)
  rw [coe_product]
  exact hu.prod hv
#align le_mul_roth_number_product le_mulRothNumber_product
#align le_add_roth_number_product le_addRothNumber_product

@[to_additive]
theorem mulRothNumber_lt_of_forall_not_mulSalemSpencer
    (h : ∀ t ∈ powersetCard n s, ¬MulSalemSpencer ((t : Finset α) : Set α)) :
    mulRothNumber s < n := by
  obtain ⟨t, hts, hcard, ht⟩ := mulRothNumber_spec s
  rw [← hcard, ← not_le]
  intro hn
  obtain ⟨u, hut, rfl⟩ := exists_smaller_set t n hn
  exact h _ (mem_powersetCard.2 ⟨hut.trans hts, rfl⟩) (ht.mono hut)
#align mul_roth_number_lt_of_forall_not_mul_salem_spencer mulRothNumber_lt_of_forall_not_mulSalemSpencer
#align add_roth_number_lt_of_forall_not_add_salem_spencer addRothNumber_lt_of_forall_not_addSalemSpencer

end Monoid

section CommMonoid
variable [CommMonoid α] [CommMonoid β] [DecidableEq β] {A : Finset α} {B : Finset β} {f : α → β}

/-- Arithmetic progressions can be pushed forward along bijective 2-Freiman homs. -/
@[to_additive]
lemma IsMulFreimanHom.mulRothNumber_mono (hf : IsMulFreimanHom 2 A B f) (hf' : Set.BijOn f A B) :
    mulRothNumber B ≤ mulRothNumber A := by
  obtain ⟨s, hsB, hcard, hs⟩ := mulRothNumber_spec B
  have hsA : invFunOn f A '' s ⊆ A :=
    (hf'.surjOn.mapsTo_invFunOn.mono (coe_subset.2 hsB) Subset.rfl).image_subset
  have hfsA : Set.SurjOn f A s := hf'.surjOn.mono Subset.rfl (coe_subset.2 hsB)
  rw [← hcard, ← s.card_image_of_injOn ((invFunOn_injOn_image f _).mono hfsA)]
  refine MulSalemSpencer.le_mulRothNumber ?_ (mod_cast hsA)
  simpa using (hf.subset hsA hfsA.bijOn_subset.mapsTo).mulSalemSpencer (hf'.injOn.mono hsA) hs

/-- Arithmetic progressions are preserved under 2-Freiman isos. -/
@[to_additive]
lemma IsMulFreimanIso.mulRothNumber_congr (hf : IsMulFreimanIso 2 A B f) :
    mulRothNumber A = mulRothNumber B := by
  refine le_antisymm ?_ (hf.isMulFreimanHom.mulRothNumber_mono hf.bijOn)
  obtain ⟨s, hsA, hcard, hs⟩ := mulRothNumber_spec A
  rw [← coe_subset] at hsA
  have hfs : Set.InjOn f s := hf.bijOn.injOn.mono hsA
  have := (hf.subset hsA hfs.bijOn_image).mulSalemSpencer_congr.1 hs
  rw [← coe_image] at this
  rw [← hcard, ← Finset.card_image_of_injOn hfs]
  refine this.le_mulRothNumber ?_
  rw [← coe_subset, coe_image]
  exact (hf.bijOn.mapsTo.mono hsA Subset.rfl).image_subset

end CommMonoid

section CancelCommMonoid

variable [CancelCommMonoid α] (s : Finset α) (a : α)

@[to_additive (attr := simp)]
theorem mulRothNumber_map_mul_left :
    mulRothNumber (s.map <| mulLeftEmbedding a) = mulRothNumber s := by
  refine' le_antisymm _ _
  · obtain ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s.map <| mulLeftEmbedding a)
    rw [subset_map_iff] at hus
    obtain ⟨u, hus, rfl⟩ := hus
    rw [coe_map] at hu
    rw [← hcard, card_map]
    exact (mulSalemSpencer_smul_set.1 hu).le_mulRothNumber hus
  · obtain ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec s
    have h : MulSalemSpencer (u.map <| mulLeftEmbedding a : Set α) := by
      rw [coe_map]
      exact hu.smul_set
    convert h.le_mulRothNumber (map_subset_map.2 hus) using 1
    rw [card_map, hcard]
#align mul_roth_number_map_mul_left mulRothNumber_map_mul_left
#align add_roth_number_map_add_left addRothNumber_map_add_left

@[to_additive (attr := simp)]
theorem mulRothNumber_map_mul_right :
    mulRothNumber (s.map <| mulRightEmbedding a) = mulRothNumber s := by
  rw [← mulLeftEmbedding_eq_mulRightEmbedding, mulRothNumber_map_mul_left s a]
#align mul_roth_number_map_mul_right mulRothNumber_map_mul_right
#align add_roth_number_map_add_right addRothNumber_map_add_right

end CancelCommMonoid

end RothNumber

section rothNumberNat

variable {s : Finset ℕ} {k n : ℕ}

/-- The Roth number of a natural `N` is the largest integer `m` for which there is a subset of
`range N` of size `m` with no arithmetic progression of length 3.
Trivially, `rothNumberNat N ≤ N`, but Roth's theorem (proved in 1953) shows that
`rothNumberNat N = o(N)` and the construction by Behrend gives a lower bound of the form
`N * exp(-C sqrt(log(N))) ≤ rothNumberNat N`.
A significant refinement of Roth's theorem by Bloom and Sisask announced in 2020 gives
`rothNumberNat N = O(N / (log N)^(1+c))` for an absolute constant `c`. -/
def rothNumberNat : ℕ →o ℕ :=
  ⟨fun n => addRothNumber (range n), addRothNumber.mono.comp range_mono⟩
#align roth_number_nat rothNumberNat

theorem rothNumberNat_def (n : ℕ) : rothNumberNat n = addRothNumber (range n) :=
  rfl
#align roth_number_nat_def rothNumberNat_def

theorem rothNumberNat_le (N : ℕ) : rothNumberNat N ≤ N :=
  (addRothNumber_le _).trans (card_range _).le
#align roth_number_nat_le rothNumberNat_le

theorem rothNumberNat_spec (n : ℕ) :
    ∃ t ⊆ range n, t.card = rothNumberNat n ∧ AddSalemSpencer (t : Set ℕ) :=
  addRothNumber_spec _
#align roth_number_nat_spec rothNumberNat_spec

/-- A verbose specialization of `addSalemSpencer.le_addRothNumber`, sometimes convenient in
practice. -/
theorem AddSalemSpencer.le_rothNumberNat (s : Finset ℕ) (hs : AddSalemSpencer (s : Set ℕ))
    (hsn : ∀ x ∈ s, x < n) (hsk : s.card = k) : k ≤ rothNumberNat n :=
  hsk.ge.trans <| hs.le_addRothNumber fun x hx => mem_range.2 <| hsn x hx
#align add_salem_spencer.le_roth_number_nat AddSalemSpencer.le_rothNumberNat

/-- The Roth number is a subadditive function. Note that by Fekete's lemma this shows that
the limit `rothNumberNat N / N` exists, but Roth's theorem gives the stronger result that this
limit is actually `0`. -/
theorem rothNumberNat_add_le (M N : ℕ) :
    rothNumberNat (M + N) ≤ rothNumberNat M + rothNumberNat N := by
  simp_rw [rothNumberNat_def]
  rw [range_add_eq_union, ← addRothNumber_map_add_left (range N) M]
  exact addRothNumber_union_le _ _
#align roth_number_nat_add_le rothNumberNat_add_le

@[simp]
theorem rothNumberNat_zero : rothNumberNat 0 = 0 :=
  rfl
#align roth_number_nat_zero rothNumberNat_zero

theorem addRothNumber_Ico (a b : ℕ) : addRothNumber (Ico a b) = rothNumberNat (b - a) := by
  obtain h | h := le_total b a
  · rw [tsub_eq_zero_of_le h, Ico_eq_empty_of_le h, rothNumberNat_zero, addRothNumber_empty]
  convert addRothNumber_map_add_left _ a
  rw [range_eq_Ico, map_eq_image]
  convert (image_add_left_Ico 0 (b - a) _).symm
  exact (add_tsub_cancel_of_le h).symm
#align add_roth_number_Ico addRothNumber_Ico

open Asymptotics Filter

theorem rothNumberNat_isBigOWith_id :
    IsBigOWith 1 atTop (fun N => (rothNumberNat N : ℝ)) fun N => (N : ℝ) :=
  isBigOWith_of_le _ <| by simpa only [Real.norm_natCast, Nat.cast_le] using rothNumberNat_le
set_option linter.uppercaseLean3 false in
#align roth_number_nat_is_O_with_id rothNumberNat_isBigOWith_id

/-- The Roth number has the trivial bound `rothNumberNat N = O(N)`. -/
theorem rothNumberNat_isBigO_id : (fun N => (rothNumberNat N : ℝ)) =O[atTop] fun N => (N : ℝ) :=
  rothNumberNat_isBigOWith_id.isBigO
set_option linter.uppercaseLean3 false in
#align roth_number_nat_is_O_id rothNumberNat_isBigO_id

lemma Fin.addRothNumber_eq_rothNumberNat (hkn : 2 * k ≤ n) :
    addRothNumber (Iio k : Finset (Fin n.succ)) = rothNumberNat k :=
  IsAddFreimanIso.addRothNumber_congr $ mod_cast isAddFreimanIso_Iio two_ne_zero hkn

lemma Fin.addRothNumber_le_rothNumberNat (k n : ℕ) (hkn : k ≤ n) :
    addRothNumber (Iio k : Finset (Fin n.succ)) ≤ rothNumberNat k := by
  suffices h : Set.BijOn (Nat.cast : ℕ → Fin n.succ) (range k) (Iio k : Finset (Fin n.succ)) by
    exact (AddMonoidHomClass.isAddFreimanHom (Nat.castRingHom _) h.mapsTo).addRothNumber_mono h
  refine ⟨?_, (CharP.natCast_injOn_Iio _ n.succ).mono (by simp; omega), ?_⟩
  · simpa using fun x ↦ cast_strictMono hkn
  simp only [Set.SurjOn, coe_Iio, Set.subset_def, Set.mem_Iio, Set.mem_image, lt_iff_val_lt_val,
    val_cast_of_lt, Nat.lt_succ_iff.2 hkn, coe_range]
  exact fun x hx ↦ ⟨x, hx, by simp⟩

end rothNumberNat
