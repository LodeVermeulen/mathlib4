/-
Copyright (c) 2023 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.GroupTheory.PGroup

/-!
# Zagier's "one-sentence proof" of Fermat's theorem on sums of two squares

"The involution on the finite set `S = {(x, y, z) : ℕ × ℕ × ℕ | x ^ 2 + 4 * y * z = p}` defined by
```
(x, y, z) ↦ (x + 2 * z, z, y - x - z) if x < y - z
            (2 * y - x, y, x - y + z) if y - z < x < 2 * y
            (x - 2 * y, x - y + z, y) if x > 2 * y
```
has exactly one fixed point, so `|S|` is odd and the involution defined by
`(x, y, z) ↦ (x, z, y)` also has a fixed point."
-/


namespace Zagier

section Defs

open Finset

variable (k : ℕ) [hk : Fact (4 * k + 1).Prime]

/-- The set of all triples of natural numbers `(x, y, z)` satisfying
`x * x + 4 * y * z = 4 * k + 1`, as a `Set`. -/
def zagierSet : Set (ℕ × ℕ × ℕ) := {t | t.1 * t.1 + 4 * t.2.1 * t.2.2 = 4 * k + 1}

lemma zagierSet_lower_bound {x y z : ℕ} (h : (x, y, z) ∈ zagierSet k) : 0 < x ∧ 0 < y ∧ 0 < z := by
  simp_rw [zagierSet, Set.mem_setOf_eq] at h
  refine' ⟨_, _, _⟩ <;> (by_contra q; push_neg at q; rw [le_zero_iff] at q; subst q; simp at h)
  · apply_fun (· % 4) at h
    simp [mul_assoc, Nat.add_mod] at h
  all_goals cases' (Nat.dvd_prime hk.out).1 (dvd_of_mul_left_eq _ h) with e e <;>
    (subst e; simp at h; subst h; simp at hk; exact hk.out)

lemma zagierSet_upper_bound {x y z : ℕ} (h : (x, y, z) ∈ zagierSet k) :
    x ≤ k + 1 ∧ y ≤ k ∧ z ≤ k := by
  obtain ⟨hx, hy, hz⟩ := zagierSet_lower_bound k h
  simp_rw [zagierSet, Set.mem_setOf_eq] at h
  refine' ⟨_, _, _⟩ <;> nlinarith

/-- The set of all triples of natural numbers `(x, y, z) ∈ (0, k + 1] × (0, k] × (0, k]` satisfying
`x * x + 4 * y * z = 4 * k + 1`, as a `Finset`. This is shown to be equivalent to `zagierSet`. -/
def zagierFinset : Finset (ℕ × ℕ × ℕ) :=
  ((Ioc 0 (k + 1)).product ((Ioc 0 k).product (Ioc 0 k))).filter
    (fun ⟨x, y, z⟩ => x * x + 4 * y * z = 4 * k + 1)

theorem coe_zagierFinset : zagierFinset k = zagierSet k := by
  ext ⟨x, y, z⟩
  refine' ⟨fun h => _, fun h => _⟩
  · unfold zagierFinset at h
    unfold zagierSet; simp_all
  · unfold zagierSet at h
    unfold zagierFinset; simp_all
    have lb := zagierSet_lower_bound k h
    have ub := zagierSet_upper_bound k h
    apply mem_product.2; simp
    constructor; · exact ⟨lb.1, ub.1⟩
    apply mem_product.2; simp
    exact ⟨⟨lb.2.1, ub.2.1⟩, ⟨lb.2.2, ub.2.2⟩⟩

instance : Fintype (zagierSet k) := by rw [← coe_zagierFinset]; infer_instance

end Defs

section Key

variable {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ} [hp : Fact p.Prime]
  (f : Function.End α) (hf : f ^ p = 1)

open Function Submonoid

/-- The powers of a periodic endomorphism form a group with composition as the operation. -/
def groupPowers : Group (powers f) where
  inv := fun ⟨g, hg⟩ => ⟨g ^ (p - 1), by
    rw [mem_powers_iff] at hg ⊢
    obtain ⟨k, hk⟩ := hg
    use k * (p - 1)
    rw [← hk, pow_mul]⟩
  mul_left_inv := fun ⟨g, hg⟩ => by
    simp only [ge_iff_le, mk_mul_mk]
    congr
    rw [← pow_succ', Nat.sub_add_cancel (one_le_two.trans hp.out.two_le)]
    rw [mem_powers_iff] at hg
    obtain ⟨k, hk⟩ := hg
    rw [← hk, ← pow_mul, mul_comm, pow_mul, hf, one_pow]

theorem isPGroup_of_powers : @IsPGroup p (powers f) (groupPowers f hf) := by
  unfold IsPGroup
  intro ⟨g, hg⟩
  use 1
  simp; congr
  rw [mem_powers_iff] at hg
  obtain ⟨k, hk⟩ := hg
  rw [← hk, ← pow_mul, mul_comm, pow_mul, hf, one_pow]

noncomputable instance : Fintype (MulAction.fixedPoints (powers f) α) :=
  Fintype.ofFinite (MulAction.fixedPoints (powers f) α)

theorem card_modEq_card_fixedPoints_of_involutive (hf : Involutive f) :
    Fintype.card α ≡ Fintype.card (MulAction.fixedPoints (powers f) α) [MOD 2] := by
  replace hf := hf.comp_self
  rw [show f ∘ f = f * f by rfl, ← sq] at hf
  exact @IsPGroup.card_modEq_card_fixedPoints _ _ (_) (isPGroup_of_powers f hf) _ _ _ _ _

end Key

section Involution

open Finset Function Submonoid

variable (k : ℕ) [hk : Fact (4 * k + 1).Prime]

/-- The obvious involution `(x, y, z) ↦ (x, z, y)`. Its fixed points correspond to representations
of `4 * k + 1` as a sum of two squares. -/
def obvInvo : Function.End (zagierSet k) := fun ⟨⟨x, y, z⟩, h⟩ => ⟨⟨x, z, y⟩, by
  unfold zagierSet at *
  simp_all
  linarith [h]⟩

lemma obvInvo_apply {p : ℕ × ℕ × ℕ} {hp : p ∈ zagierSet k} :
    (obvInvo k) ⟨p, hp⟩ = (p.1, p.2.2, p.2.1) := by
  rfl

theorem involutive_obvInvo : Involutive (obvInvo k) := by
  unfold Involutive obvInvo zagierSet; simp

theorem sq_add_sq_of_nonempty_fixedPoints
    (hn : (MulAction.fixedPoints (powers (obvInvo k)) (zagierSet k)).Nonempty) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = 4 * k + 1 := by
  simp_rw [sq]
  obtain ⟨⟨⟨x, y, z⟩, he⟩, hf⟩ := hn
  rw [MulAction.mem_fixedPoints, Subtype.forall] at hf
  have := hf (obvInvo k) (mem_powers _)
  apply_fun Subtype.val at this
  rw [Submonoid.smul_def, End.smul_def] at this
  unfold obvInvo at this; simp at this
  unfold zagierSet at he; simp at he
  use x, (2 * y)
  rw [this.1, show 4 * y * y = 2 * y * (2 * y) by linarith] at he
  assumption

/-- The complicated involution, which is shown to have exactly one fixed point `(1, 1, k)`. -/
def complexInvo : Function.End (zagierSet k) := fun ⟨⟨x, y, z⟩, h⟩ =>
  ⟨if x + z < y then ⟨x + 2 * z, z, y - x - z⟩ else
   if 2 * y < x then ⟨x - 2 * y, x + z - y, y⟩ else
                     ⟨2 * y - x, y, x + z - y⟩, by
  unfold zagierSet at *
  simp at h
  split_ifs with less more <;> simp
  · rw [Nat.sub_sub]
    zify [less.le] at h ⊢
    linarith [h]
  · push_neg at less
    zify [less, more.le] at h ⊢
    linarith [h]
  · push_neg at less more
    zify [less, more] at h ⊢
    linarith [h]⟩

theorem involutive_complexInvo : Involutive (complexInvo k) := by
  intro ⟨⟨x, y, z⟩, h⟩
  obtain ⟨xb, _, _⟩ := zagierSet_lower_bound k h
  conv_lhs =>
    arg 2
    tactic => unfold complexInvo
    dsimp
  split_ifs with less more <;> (unfold complexInvo; simp; congr)
  · simp [show ¬(x + 2 * z + (y - x - z) < z) by linarith [less], xb]
    rw [Nat.sub_sub, two_mul, ← tsub_add_eq_add_tsub (by linarith), ← add_assoc,
      Nat.add_sub_cancel, add_comm (x + z), Nat.sub_add_cancel (less.le)]
  · push_neg at less
    simp [(show x - 2 * y + y < x + z - y by zify [more.le, less]; linarith)]
    constructor
    · rw [Nat.sub_add_cancel more.le]
    · rw [Nat.sub_right_comm, Nat.sub_sub _ _ y, ← two_mul, add_comm, Nat.add_sub_assoc more.le,
        Nat.add_sub_cancel]
  · push_neg at less more
    simp [(show ¬(2 * y - x + (x + z - y) < y) by push_neg; zify [less, more]; linarith),
      (show ¬(2 * y < 2 * y - x) by push_neg; zify [more]; linarith)]
    constructor
    · rw [tsub_tsub_assoc (by rfl) more, tsub_self, zero_add]
    · rw [← Nat.add_sub_assoc less (2 * y - x), ← add_assoc, Nat.sub_add_cancel more,
        Nat.sub_sub _ _ y, ← two_mul, add_comm, Nat.add_sub_cancel]

theorem unique_of_mem_fixedPoints {t : zagierSet k}
    (mem : t ∈ (MulAction.fixedPoints (powers (complexInvo k)) (zagierSet k))) :
    t.val = (1, 1, k):= by
  simp only [MulAction.mem_fixedPoints, Subtype.forall] at mem
  replace mem := mem (complexInvo k) (mem_powers _)
  rw [Submonoid.smul_def, End.smul_def] at mem
  unfold complexInvo at mem
  obtain ⟨⟨x, y, z⟩, h⟩ := t
  obtain ⟨xb, yb, zb⟩ := zagierSet_lower_bound k h
  apply_fun Subtype.val at mem
  simp at mem
  split_ifs at mem with less more <;> simp_all
  · obtain ⟨_, _, _⟩ := mem
    simp_all
  · -- True case
    unfold zagierSet at h; simp at h
    replace mem := mem.1
    rw [tsub_eq_iff_eq_add_of_le more, ← two_mul] at mem
    replace mem := (mul_left_cancel₀ two_ne_zero mem).symm
    subst mem
    rw [show x * x + 4 * x * z = x * (x + 4 * z) by linarith] at h
    cases' (Nat.dvd_prime hk.out).1 (dvd_of_mul_left_eq _ h) with e e
    · rw [e, mul_one] at h; subst h
      simp_all [show z = 0 by linarith [e]]
    · rw [e, mul_left_eq_self₀] at h; simp_all
      linarith [e]

theorem fixedPoints_eq_singleton :
    MulAction.fixedPoints (powers (complexInvo k)) (zagierSet k) =
    {⟨(1, 1, k), (by unfold zagierSet; simp; linarith)⟩} := by
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · simp
    intro f h
    rw [Submonoid.smul_def, End.smul_def]
    simp
    rw [mem_powers_iff] at h
    obtain ⟨n, h⟩ := h
    have hi := (involutive_complexInvo k).comp_self
    have h1 : id = (1 : Function.End (zagierSet k)) := by rfl
    rw [show _ ∘ _ = _ * complexInvo k by rfl, ← sq] at hi
    rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩ <;> rw [hm] at h
    · rw [pow_mul, hi, h1, one_pow, ← h1] at h
      rw [← h, id_eq]
    · rw [pow_add, pow_mul, hi, pow_one, h1, one_pow, one_mul] at h
      rw [← h]; unfold complexInvo; simp
  · intro t mem
    replace mem := unique_of_mem_fixedPoints k mem
    unfold zagierSet at t
    congr!

theorem exists_sq_add_sq : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 4 * k + 1 := by
  apply sq_add_sq_of_nonempty_fixedPoints
  have := (card_modEq_card_fixedPoints_of_involutive (obvInvo k) (involutive_obvInvo k)).symm.trans
    (card_modEq_card_fixedPoints_of_involutive (complexInvo k) (involutive_complexInvo k))
  simp_rw [fixedPoints_eq_singleton, Nat.ModEq] at this
  norm_num at this; rw [← Nat.odd_iff] at this
  replace this := Odd.pos this
  rw [← Set.toFinset_card, card_pos, Set.toFinset_nonempty] at this
  assumption

end Involution

end Zagier

/-- **Fermat's theorem on sums of two squares** (Wiedijk #20).
Every prime congruent to 1 mod 4 is the sum of two squares, proved using Zagier's involutions. -/
theorem Nat.Prime.sq_add_sq' {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  have md := div_add_mod p 4
  rw [hp] at md
  have := @Zagier.exists_sq_add_sq (p / 4) (by rw [md]; infer_instance)
  rw [md] at this
  assumption
