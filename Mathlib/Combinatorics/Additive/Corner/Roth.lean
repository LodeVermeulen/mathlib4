/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.Additive.Corner.Defs
import Mathlib.Combinatorics.Additive.SalemSpencer
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-!
# The corners theorem and Roth's theorem

This file proves the corners theorem and Roth's theorem.

## References

* [Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
* [Wikipedia, *Corners theorem*](https://en.wikipedia.org/wiki/Corners_theorem)
-/

namespace Finset
variable {α β : Type*} {A : Finset α} {B : Finset β}

/-- Reorder a finset.

The difference with `Finset.card_bij'` is that the bijection is specified as a surjective injection,
rather than by an inverse function.

The difference with `Finset.card_nbij` is that the bijection is allowed to use membership of the
domain, rather than being a non-dependent function. -/
lemma card_bij (i : ∀ a ∈ A, β) (hi : ∀ a ha, i a ha ∈ B)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ B, ∃ a ha, i a ha = b) : A.card = B.card := by
  classical
  calc
    A.card = A.attach.card := card_attach.symm
    _      = (A.attach.image fun a : { a // a ∈ A } => i a.1 a.2).card := Eq.symm ?_
    _      = B.card := ?_
  · apply card_image_of_injective
    intro ⟨_, _⟩ ⟨_, _⟩ h
    simpa using i_inj _ _ _ _ h
  · congr 1
    ext b
    constructor <;> intro h
    · obtain ⟨_, _, rfl⟩ := mem_image.1 h; apply hi
    · obtain ⟨a, ha, rfl⟩ := i_surj b h; exact mem_image.2 ⟨⟨a, ha⟩, by simp⟩

/-- Reorder a finset.

The difference with `Finset.card_bij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.card_nbij'` is that the bijection and its inverse are allowed to use
membership of the domains, rather than being non-dependent functions. -/
lemma card_bij' (i : ∀ a ∈ A, β) (j : ∀ a ∈ B, α) (hi : ∀ a ha, i a ha ∈ B)
    (hj : ∀ a ha, j a ha ∈ A) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) : A.card = B.card := by
  refine card_bij i hi (fun a1 h1 a2 h2 eq ↦ ?_) (fun b hb ↦ ⟨_, hj b hb, right_inv b hb⟩)
  rw [← left_inv a1 h1, ← left_inv a2 h2]
  simp only [eq]

/-- Reorder a finset.

The difference with `Finset.card_nbij'` is that the bijection is specified as a surjective
injection, rather than by an inverse function.

The difference with `Finset.card_bij` is that the bijection is a non-dependent function, rather than
being allowed to use membership of the domain. -/
lemma card_nbij (i : α → β) (hi : ∀ a ∈ A, i a ∈ B) (i_inj : (A : Set α).InjOn i)
    (i_surj : (A : Set α).SurjOn i B) : A.card = B.card :=
  card_bij (fun a _ ↦ i a) hi i_inj (by simpa using i_surj)

/-- Reorder a finset.

The difference with `Finset.card_nbij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.card_bij'` is that the bijection and its inverse are non-dependent
functions, rather than being allowed to use membership of the domains.

The difference with `Finset.card_equiv` is that bijectivity is only required to hold on the domains,
rather than on the entire types. -/
lemma card_nbij' (i : α → β) (j : β → α) (hi : ∀ a ∈ A, i a ∈ B) (hj : ∀ a ∈ B, j a ∈ A)
    (left_inv : ∀ a ∈ A, j (i a) = a) (right_inv : ∀ a ∈ B, i (j a) = a) : A.card = B.card :=
  card_bij' (fun a _ ↦ i a) (fun b _ ↦ j b) hi hj left_inv right_inv

/-- Specialization of `Finset.card_nbij'` that automatically fills in most arguments.

See `Fintype.card_equiv` for the version where `A` and `B` are `univ`. -/
lemma card_equiv (e : α ≃ β) (hst : ∀ i, i ∈ A ↔ e i ∈ B) : A.card = B.card := by
  refine card_nbij' e e.symm ?_ ?_ ?_ ?_ <;> simp [hst]

/-- Specialization of `Finset.card_bij` that automatically fills in most arguments.

See `Fintype.card_bijective` for the version where `A` and `B` are `univ`. -/
lemma card_bijective (e : α → β) (he : e.Bijective) (hst : ∀ i, i ∈ A ↔ e i ∈ B) :
    A.card = B.card := card_equiv (.ofBijective e he) hst

end Finset

open Finset SimpleGraph SimpleGraph.TripartiteFromTriangles Sum Sum3
open Function hiding graph
open Fintype (card)

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {A B : Finset (G × G)}
  {a b c d x y : G} {n : ℕ} {ε : ℝ}

namespace Corners

/-- The triangle indices for the proof of the corners theorem construction. -/
private def triangleIndices (A : Finset (G × G)) : Finset (G × G × G) :=
  A.map ⟨fun (a, b) ↦ (a, b, a + b), by rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨⟩; rfl⟩

@[simp] lemma mk_mem_triangleIndices : (a, b, c) ∈ triangleIndices A ↔ (a, b) ∈ A ∧ c = a + b := by
  simp only [triangleIndices, Prod.ext_iff, mem_map, Embedding.coeFn_mk, exists_prop, Prod.exists,
    eq_comm]
  refine ⟨?_, fun h ↦ ⟨_, _, h.1, rfl, rfl, h.2⟩⟩
  rintro ⟨_, _, h₁, rfl, rfl, h₂⟩
  exact ⟨h₁, h₂⟩

@[simp] lemma card_triangleIndices : (triangleIndices A).card = A.card := card_map _

instance triangleIndices.instExplicitDisjoint : ExplicitDisjoint (triangleIndices A) := by
  constructor
  all_goals
    simp only [mk_mem_triangleIndices, Prod.mk.inj_iff, exists_prop, forall_exists_index, and_imp]
    rintro a b _ a' - rfl - h'
    simp [Fin.val_eq_val, *] at * <;> assumption

lemma noAccidental (hs : IsCornerFree (A : Set (G × G))) : NoAccidental (triangleIndices A) where
  wow a a' b b' c c' ha hb hc := by
    simp only [mk_mem_triangleIndices] at ha hb hc
    exact .inl $ hs ⟨hc.1, hb.1, ha.1, hb.2.symm.trans ha.2⟩

lemma farFromTriangleFree_graph (hε : ε * card G ^ 2 ≤ A.card) :
    (graph $ triangleIndices A).FarFromTriangleFree (ε / 9) := by
  refine farFromTriangleFree _ ?_
  simp_rw [card_triangleIndices, mul_comm_div, Nat.cast_pow, Nat.cast_add]
  ring_nf
  simpa only [mul_comm] using hε

end Corners

open Corners

/-- The **corners theorem** for finite abelian groups.

The maximum density of a corner-free set in `G × G` goes to zero as `|G|` tends to infinity. -/
theorem corners_theorem (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ G, [AddCommGroup G] → [Fintype G] → n₀ ≤ card G → ∀ A : Finset (G × G),
      ε * card G ^ 2 ≤ A.card → ¬ IsCornerFree (A : Set (G × G)) := by
  refine ⟨⌊(triangleRemovalBound (ε / 9) * 27)⁻¹⌋₊ + 1, fun G _ _ hG A hA h ↦ ?_⟩
  rw [Nat.add_one_le_iff] at hG
  have hε₁ : ε ≤ 1 := by
    have := hA.trans (Nat.cast_le.2 A.card_le_univ)
    simp only [sq, Nat.cast_mul, Fintype.card_prod, Fintype.card_fin] at this
    rwa [mul_le_iff_le_one_left] at this
    positivity
  haveI := noAccidental h
  rw [Nat.floor_lt' (by positivity), inv_pos_lt_iff_one_lt_mul'] at hG
  refine hG.not_le (le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < card G ^ 2))
  classical
  have h₁ := (farFromTriangleFree_graph hA).le_card_cliqueFinset
  rw [card_triangles, card_triangleIndices] at h₁
  convert h₁.trans (Nat.cast_le.2 $ card_le_univ _) using 1 <;> simp <;> ring
  · have : ε / 9 ≤ 1 := by linarith
    positivity

/-- The **corners theorem** for `ℕ`.

The maximum density of a corner-free set in `{1, ..., n} × {1, ..., n}` goes to zero as `n` tends to
infinity. -/
lemma corners_theorem_nat (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ A ⊆ range n ×ˢ range n, ε * n ^ 2 ≤ A.card →
      ¬ IsCornerFree (A : Set (ℕ × ℕ)) := by
  obtain ⟨n₀, hn₀⟩ := corners_theorem (ε / 9) (by positivity)
  refine ⟨n₀ + 1, fun n hn A hAn hAε hA ↦ ?_⟩
  rw [← coe_subset, coe_product] at hAn
  have : (A : Set (ℕ × ℕ)) = Prod.map Fin.val Fin.val '' (Prod.map Nat.cast Nat.cast '' (A : Set (ℕ × ℕ)) : Set (Fin (2 * n).succ × Fin (2 * n).succ)) := sorry
  rw [this] at hA
  have := Fin.isAddFreimanIso_Iio two_ne_zero (le_refl (2 * n))
  have := hA.of_image this.isAddFreimanHom (Fin.val_injective.injOn _) sorry
  rw [← coe_image] at this
  refine hn₀ _ (by simp; omega) _ ?_ this
  calc
    _ = ε / 9 * (2 * n + 1) ^ 2 := by simp
    _ ≤ ε / 9 * (2 * n + n) ^ 2 := by gcongr; simp; omega
    _ = ε * n ^ 2 := by ring
    _ ≤ A.card := hAε
    _ = _ := by
      rw [card_image_of_injOn]
      have : Set.InjOn Nat.cast (range n) :=
        (CharP.natCast_injOn_Iio (Fin (2 * n).succ) (2 * n).succ).mono (by simp; omega)
      exact (this.prodMap this).mono hAn

/-- **Roth's theorem** for finite abelian groups.

The maximum density of a 3AP-free set in `G` goes to zero as `|G|` tends to infinity. -/
lemma roth (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ G, [AddCommGroup G] → [Fintype G] → n₀ ≤ card G → ∀ A : Finset G,
      ε * card G ≤ A.card → ¬ AddSalemSpencer (A : Set G) := by
  obtain ⟨n₀, hn₀⟩ := corners_theorem ε hε
  refine ⟨n₀, fun G _ _ hG A hAcard hA ↦ ?_⟩
  classical
  let B : Finset (G × G) := univ.filter fun (x, y) ↦ y - x ∈ A
  have : ε * card G ^ 2 ≤ B.card := by
    calc
      _ = card G * (ε * card G) := by ring
      _ ≤ card G * A.card := by gcongr
      _ = B.card := ?_
    norm_cast
    rw [← card_univ, ← card_product]
    exact card_equiv ((Equiv.refl _).prodShear fun a ↦ Equiv.addLeft a) (by simp [B])
  obtain ⟨x₁, y₁, x₂, y₂, hx₁y₁, hx₁y₂, hx₂y₁, hxy, hx₁x₂⟩ :
      ∃ x₁ y₁ x₂ y₂, y₁ - x₁ ∈ A ∧ y₂ - x₁ ∈ A ∧ y₁ - x₂ ∈ A ∧ x₁ + y₂ = x₂ + y₁ ∧ x₁ ≠ x₂ := by
    simpa [IsCornerFree, isCorner_iff, B, -exists_and_left, -exists_and_right] using hn₀ _ hG B this
  have := hA hx₂y₁ hx₁y₁ hx₁y₂ $ by -- TODO: This really ought to just be `by linear_combination h`
    rw [sub_add_sub_comm, add_comm, add_sub_add_comm, add_right_cancel_iff,
      sub_eq_sub_iff_add_eq_add, add_comm, hxy, add_comm]
  exact hx₁x₂ $ by simpa using this.symm

/-- **Roth's theorem** for `ℕ`.

The maximum density of a 3AP-free set in `{1, ..., n}` goes to zero as `n` tends to infinity. -/
lemma roth_nat (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ A ⊆ range n, ε * n ≤ A.card → ¬ AddSalemSpencer (A : Set ℕ) := by
  obtain ⟨n₀, hn₀⟩ := roth (ε / 3) (by positivity)
  refine ⟨n₀ + 1, fun n hn A hAn hAε hA ↦ ?_⟩
  rw [← coe_subset, coe_range] at hAn
  have : (A : Set ℕ) = Fin.val '' (Nat.cast '' (A : Set ℕ) : Set (Fin (2 * n).succ)) := sorry
  rw [this] at hA
  have := Fin.isAddFreimanIso_Iio two_ne_zero (le_refl (2 * n))
  have := hA.of_image this.isAddFreimanHom (Fin.val_injective.injOn _) sorry
  rw [← coe_image] at this
  refine hn₀ _ (by simp; omega) _ ?_ this
  calc
    _ = ε / 3 * (2 * n + 1) := by simp
    _ ≤ ε / 3 * (2 * n + n) := by gcongr; simp; omega
    _ = ε * n := by ring
    _ ≤ A.card := hAε
    _ = _ := by
      rw [card_image_of_injOn]
      refine (CharP.natCast_injOn_Iio (Fin (2 * n).succ) (2 * n).succ).mono $ hAn.trans ?_
      simp
      omega

open Asymptotics Filter

lemma roth_asymptotic : IsLittleO atTop (fun N ↦ (rothNumberNat N : ℝ)) (fun N ↦ (N : ℝ)) := by
  simp only [isLittleO_iff, eventually_atTop, RCLike.norm_natCast]
  refine fun ε hε ↦ (roth_nat ε hε).imp fun n₀ ↦ forall₂_imp fun n hn h ↦ ?__
  obtain ⟨A, hs₁, hs₂, hs₃⟩ := rothNumberNat_spec n
  rw [← hs₂, ← not_lt]
  exact fun hδn ↦ h _ hs₁ hδn.le hs₃
