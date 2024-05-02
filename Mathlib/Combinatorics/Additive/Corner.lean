/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Combinatorics.Additive.SalemSpencer
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-!
# The corners theorem and Roth's theorem

This file proves the corners theorem and Roth's theorem.

## References

* [Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
* [Wikipedia, *Corners theorem*](https://en.wikipedia.org/wiki/Corners_theorem)
-/

section LinearOrderedSemifield
variable {α : Type*} [LinearOrderedSemifield α] {a b c : α}

end LinearOrderedSemifield

attribute [simp] Fin.val_eq_val

open Finset SimpleGraph SimpleGraph.TripartiteFromTriangles Sum Sum3
open Function hiding graph

variable {n : ℕ} {ε : ℝ}

/-- A corner in `s` is three points of the form `(x, y), (x + h, y), (x, y + h)`. A corner is
nontrivial if `h ≠ 0`. A corner with `h ≤ 0` is called an anticorner. Here, we record `x`, `y`, `d`.
-/
def IsCorner (s : Finset (ℤ × ℤ)) : ℤ → ℤ → ℤ → Prop :=
  fun x y d ↦ (x, y) ∈ s ∧ (x + d, y) ∈ s ∧ (x, y + d) ∈ s

lemma IsCorner.mono {s t : Finset (ℤ × ℤ)} (hst : s ⊆ t) {x y d : ℤ} (h : IsCorner s x y d) :
    IsCorner t x y d :=
  ⟨hst h.1, hst h.2.1, hst h.2.2⟩

namespace Corners
variable {s : Finset (Fin n × Fin n)} {x : Fin n × Fin n × Fin (n + n)}

/-- The triangle indices for the proof of the corners theorem construction. -/
private def triangleIndices (s : Finset (Fin n × Fin n)) : Finset (Fin n × Fin n × Fin (n + n)) :=
  s.map ⟨fun ab ↦ (ab.1, ab.2, ⟨ab.1.val + ab.2.val, add_lt_add ab.1.2 ab.2.2⟩), by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨⟩; rfl⟩

@[simp] lemma mem_triangleIndices :
  x ∈ triangleIndices s ↔ (x.1, x.2.1) ∈ s ∧ x.2.2 = ⟨_, add_lt_add x.1.2 x.2.1.2⟩ := by
  simp only [triangleIndices, Prod.ext_iff, mem_map, Embedding.coeFn_mk, exists_prop, Prod.exists,
    eq_comm]
  refine ⟨?_, fun h ↦ ⟨_, _, h.1, rfl, rfl, h.2⟩⟩
  rintro ⟨_, _, h₁, rfl, rfl, h₂⟩
  exact ⟨h₁, h₂⟩

lemma mk_mem_triangleIndices {a b : Fin n} {c : Fin (n + n)} :
    (a, b, c) ∈ triangleIndices s ↔ (a, b) ∈ s ∧ c = ⟨_, add_lt_add a.2 b.2⟩ := mem_triangleIndices

@[simp] lemma card_triangleIndices : (triangleIndices s).card = s.card := card_map _

instance triangleIndices.instExplicitDisjoint : ExplicitDisjoint (triangleIndices s) := by
  constructor
  all_goals
    simp only [mk_mem_triangleIndices, Prod.mk.inj_iff, exists_prop, forall_exists_index, and_imp]
    rintro a b _ a' - rfl - h'
    simp [*] at * <;> assumption

lemma noAccidental (h : ∀ (x y : ℕ) d, IsCorner (s.image $ Prod.map (↑) (↑)) x y d → d = 0) :
    NoAccidental (triangleIndices s) where
  wow a a' b b' c c' ha hb hc := by
    simp only [mem_triangleIndices] at ha hb hc
    refine .inl $ .symm $ Fin.ext $ Nat.cast_injective $ sub_eq_zero.1 $ h a b _
      ⟨mem_image_of_mem _ hc.1, ?_, ?_⟩
    · simpa only [add_sub_cancel] using mem_image_of_mem _ ha.1
    rw [ha.2, Fin.mk_eq_mk] at hb
    convert mem_image_of_mem _ hb.1
    simpa [Prod.ext_iff, ← add_sub_right_comm, sub_eq_iff_eq_add, add_comm]
      using congr_arg Int.ofNat hb.2

lemma farFromTriangleFree_graph (hε : ε * n ^ 2 ≤ s.card) :
  (graph $ triangleIndices s).FarFromTriangleFree (ε / 16) := by
  refine farFromTriangleFree _ ?_
  simp_rw [card_triangleIndices, Fintype.card_fin, mul_comm_div, Nat.cast_pow, Nat.cast_add]
  ring_nf
  simpa only [mul_comm] using hε

lemma weak_corners_theorem {ε : ℝ} (hε : 0 < ε) :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ s : Finset (Fin n × Fin n), ε * n^2 ≤ s.card →
      ∃ x y : ℕ, ∃ d ≠ 0, IsCorner (s.image $ Prod.map (↑) (↑)) x y d := by
  refine ⟨⌊(triangleRemovalBound (ε / 16) * 64)⁻¹⌋₊ + 1, fun n hn s hA ↦ ?_⟩
  rw [Nat.add_one_le_iff] at hn
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt hn
  have hε₁ : ε ≤ 1 := by
    have := hA.trans (Nat.cast_le.2 s.card_le_univ)
    simp only [sq, Nat.cast_mul, Fintype.card_prod, Fintype.card_fin] at this
    rwa [mul_le_iff_le_one_left] at this
    exact mul_pos (Nat.cast_pos.2 n_pos) (Nat.cast_pos.2 n_pos)
  by_contra! h
  simp_rw [not_imp_not] at h
  haveI := noAccidental h
  rw [Nat.floor_lt' n_pos.ne', inv_pos_lt_iff_one_lt_mul'] at hn
  refine hn.not_le (le_of_mul_le_mul_right ?_ $ pow_pos (Nat.cast_pos.2 n_pos) 2)
  have h₁ := (farFromTriangleFree_graph hA).le_card_cliqueFinset
  rw [card_triangles, card_triangleIndices] at h₁
  convert h₁.trans (Nat.cast_le.2 $ card_le_univ _) using 1 <;> simp <;> ring
  · have : ε / 16 ≤ 1 := by linarith
    positivity

end Corners

open Corners

lemma alt_set (c : ℕ × ℕ) (s : Finset (ℕ × ℕ)) :
  (s.filter fun (x, y) ↦ x ≤ c.1 ∧ y ≤ c.2 ∧ (c.1 - x, c.2 - y) ∈ s).card =
    ((s ×ˢ s).filter fun ((x₁, y₁), x₂, y₂) ↦ (x₁ + x₂, y₁ + y₂) = c).card := by
  rcases c with ⟨c₁, c₂⟩
  refine (card_congr (fun (a, _) _ ↦ a) ?_ ?_ ?_).symm
  · rintro ⟨⟨a₁, a₂⟩, b₁, b₂⟩ i
    dsimp
    simp only [mem_filter, mem_product, Prod.mk.inj_iff] at i
    simp only [mem_filter]
    rw [← i.2.1, ← i.2.2]
    simpa using i.1
  · aesop
  simp only [and_imp, exists_prop, Prod.forall, mem_filter, exists_and_right, Prod.mk.inj_iff,
    exists_eq_right_right, exists_eq_right, Prod.exists, mem_product]
  refine (fun x y xy hx hy t ↦ ⟨_, _, ⟨xy, t⟩, ?_, ?_⟩) <;>
    rw [← Nat.add_sub_assoc, Nat.add_sub_cancel_left] <;> assumption

lemma correlate {n : ℕ} (hn : 0 < n) (s : Finset (ℕ × ℕ)) (hA : s ⊆ range n ×ˢ range n) :
  ∃ c ∈ range (n + n) ×ˢ range (n + n),
    (s.card : ℝ)^2 / (n + n)^2 ≤
      (s.filter fun (x, y) ↦ x ≤ c.1 ∧ y ≤ c.2 ∧ (c.1 - x, c.2 - y) ∈ s).card := by
  simp_rw [alt_set _ s]
  let f : (ℕ × ℕ) × ℕ × ℕ → ℕ × ℕ := fun ((a, b), c, d) ↦ (a + c, b + d)
  have : ∀ a ∈ s ×ˢ s, f a ∈ range (n + n) ×ˢ range (n + n) := by
    simp only [subset_iff, mem_range, mem_product, two_mul] at hA ⊢
    exact fun a ha ↦ ⟨add_lt_add (hA ha.1).1 (hA ha.2).1, add_lt_add (hA ha.1).2 (hA ha.2).2⟩
  refine exists_le_card_fiber_of_nsmul_le_card_of_maps_to this ?_ ?_
  { simp [hn.ne'] }
  simp only [card_product, card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_add, ← sq]
  rw [mul_div_assoc', mul_div_cancel_left₀]
  simp [hn.ne']

lemma corners_theorem (hε : 0 < ε) :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ s ⊆ range n ×ˢ range n, ε * n^2 ≤ s.card →
    ∃ x y d : ℕ, d ≠ 0 ∧ IsCorner (s.image $ Prod.map (↑) (↑)) x y d := by
  obtain ⟨n₀, hn₀⟩ := weak_corners_theorem (by positivity : 0 < (ε / 2) ^ 2)
  refine ⟨n₀ + 1, fun n hn s hA hAcard ↦ ?_⟩
  obtain ⟨⟨c₁, c₂⟩, -, hA'card⟩ := correlate (Nat.succ_pos'.trans_le hn) s hA
  let A' : Finset (Fin n × Fin n) :=
    univ.filter fun (x, y) ↦ (↑x, ↑y) ∈ s ∧ ↑x ≤ c₁ ∧ ↑y ≤ c₂ ∧ (c₁ - x, c₂ - y) ∈ s
  have hA' : A'.image (Prod.map (↑) (↑) : Fin n × Fin n → ℤ × ℤ) ⊆ s.image (Prod.map (↑) (↑)) :=
    image_subset_iff.2 fun x hx ↦ mem_image.2 ⟨x.map (↑) (↑), by exact (mem_filter.1 hx).2.1, rfl⟩
  have : (ε / 2) ^ 2 * ↑n ^ 2 ≤ A'.card := by
    refine le_trans ?_ (hA'card.trans ?_)
    { rw [← mul_pow, ← div_pow]
      refine pow_le_pow_left (by positivity) ?_ _
      cases n
      { simp }
      rwa [le_div_iff, mul_comm_div, mul_assoc, mul_comm_div, ← two_mul,
        mul_div_cancel_left₀ _ (two_ne_zero' ℝ), ← sq]
      positivity }
    norm_cast
    refine (card_mono ?_).trans (card_image_le (f := Prod.map (↑) (↑)))
    simp only [le_iff_subset, subset_iff, mem_filter, mem_image, mem_univ, true_and, Prod_map,
      exists_prop, Prod.exists, and_imp, Prod.forall, A']
    rintro a b hab hac hbc hcab
    obtain ⟨ha, hb⟩ := mem_product.1 (hA hab)
    exact ⟨⟨a, mem_range.1 ha⟩, ⟨b, mem_range.1 hb⟩, ⟨hab, hac, hbc, hcab⟩, rfl⟩
  obtain ⟨x, y, d, hd, hxyd⟩ := hn₀ _ (Nat.le_of_succ_le hn) A' this
  obtain ⟨d, rfl | rfl⟩ := d.eq_nat_or_neg
  { exact ⟨_, _, _, Nat.cast_ne_zero.1 hd, hxyd.mono hA'⟩ }
  simp only [IsCorner, mem_image, mem_filter, mem_univ, true_and, Prod_map, Prod.mk.inj_iff,
    exists_prop, Prod.exists, A'] at hxyd
  norm_cast at hxyd
  obtain ⟨⟨a₁, a₂, ⟨-, hac₁, hac₂, hac⟩, rfl, rfl⟩, ⟨b₁, b₂, ⟨-, hbc₁, hbc₂, hbc⟩, hba₁, hba₂⟩,
    e₁, e₂, ⟨-, hec₁, hec₂, hec⟩, hea₁, hea₂⟩ := hxyd
  simp only [Nat.cast_inj, Fin.val_eq_val] at hba₂ hea₁
  obtain rfl := hba₂
  obtain rfl := hea₁
  refine ⟨c₁ - e₁, c₂ - b₂, _, Nat.cast_ne_zero.1 $ neg_ne_zero.1 hd, mem_image.2 ⟨_, hac, ?_⟩,
    mem_image.2 ⟨_, hbc, ?_⟩, mem_image.2 ⟨_, hec, ?_⟩⟩ <;> simp [*, sub_add, ← sub_eq_add_neg]

lemma roth (δ : ℝ) (hδ : 0 < δ) :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ s ⊆ range n, δ * n ≤ s.card → ∃ a d, 0 < d ∧ a ∈ s ∧ a + d ∈ s ∧ a + 2 * d ∈ s := by
  obtain ⟨n₀, hn₀⟩ := corners_theorem (by positivity : 0 < δ/4)
  refine ⟨n₀, fun n hn s hA hAcard ↦ ?_⟩
  let B : Finset (ℕ × ℕ) :=
    (range (n + n) ×ˢ range (n + n)).filter fun (x, y) ↦ x ≤ y ∧ y - x ∈ s
  have : n * card s ≤ card B := by
    rw [← card_range n, ← card_product]
    refine card_le_card_of_inj_on (fun (i, a) ↦ (i, i + a)) ?_ ?_
    · rintro ⟨i, a⟩ t
      simp only [mem_range, mem_product] at t
      simp only [true_and, mem_filter, add_tsub_cancel_left, mem_range, le_add_iff_nonneg_right,
        zero_le', mem_product, t.2, and_true, two_mul, B]
      exact ⟨t.1.trans_le (Nat.le_add_right _ _), add_lt_add t.1 (mem_range.1 (hA t.2))⟩
    simp only [and_imp, Prod.forall, mem_range, Prod.mk.inj_iff, mem_product]
    rintro i a₁ - - _ a₂ - - rfl
    simp
  have : δ/4 * ↑(n + n) ^ 2 ≤ B.card := by
    refine le_trans ?_ (Nat.cast_le.2 this)
    rw [Nat.cast_add, ← two_mul, mul_pow, ← mul_assoc, Nat.cast_mul]
    norm_num
    rw [sq, ← mul_assoc, mul_comm _ (s.card : ℝ)]
    exact mul_le_mul_of_nonneg_right hAcard (Nat.cast_nonneg _)
  obtain ⟨x, y, k, hk, xy, xky, xyk⟩ := hn₀ _ (hn.trans le_add_self) B (filter_subset _ _) this
  have : Injective (Prod.map (↑) (↑) : ℕ × ℕ → ℤ × ℤ) :=
    Nat.cast_injective.Prod_map Nat.cast_injective
  replace xy : (x, y) ∈ B := this.mem_finset_image.1 xy
  replace xky : (x + k, y) ∈ B := this.mem_finset_image.1 xky
  replace xyk : (x, y + k) ∈ B := this.mem_finset_image.1 xyk
  refine ⟨y - (x + k), k, pos_iff_ne_zero.2 hk, (mem_filter.1 xky).2.2, ?_, ?_⟩
  { rw [← Nat.sub_add_comm (mem_filter.1 xky).2.1, Nat.add_sub_add_right]
    exact (mem_filter.1 xy).2.2 }
  { rw [← Nat.sub_add_comm (mem_filter.1 xky).2.1, two_mul, ← add_assoc, Nat.add_sub_add_right]
    exact (mem_filter.1 xyk).2.2 }

lemma roth' (δ : ℝ) (hδ : 0 < δ) :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ s ⊆ range n, δ * n ≤ s.card → ¬ AddSalemSpencer (s : Set ℕ) := by
  obtain ⟨n₀, hn₀⟩ := roth δ hδ
  refine ⟨n₀, fun n hn s hA hAcard hA' ↦ ?_⟩
  obtain ⟨a, d, hd, x, y, z⟩ := hn₀ n hn s hA hAcard
  exact mul_ne_zero two_ne_zero hd.ne' (self_eq_add_right.1 $ hA' x z y $ by ring)

open Asymptotics Filter

lemma roth_asymptotic : IsLittleO atTop (fun N ↦ (rothNumberNat N : ℝ)) (fun N ↦ (N : ℝ)) := by
  simp only [isLittleO_iff, eventually_atTop, RCLike.norm_natCast]
  refine fun δ hδ ↦ (roth' δ hδ).imp fun n₀ ↦ forall₂_imp fun n hn h ↦ ?__
  obtain ⟨s, hs₁, hs₂, hs₃⟩ := rothNumberNat_spec n
  rw [← hs₂, ← not_lt]
  exact fun hδn ↦ h _ hs₁ hδn.le hs₃
