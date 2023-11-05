/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.BigOperators.Basic
import Mathlib.Data.Multiset.Basic

#align_import algebra.big_operators.multiset.basic from "leanprover-community/mathlib"@"6c5f73fd6f6cc83122788a80a27cdd54663609f4"

/-!
# Sums and products over multisets

In this file we define products and sums indexed by multisets. This is later used to define products
and sums indexed by finite sets.

## Main declarations

* `Multiset.prod`: `s.prod f` is the product of `f i` over all `i ∈ s`. Not to be mistaken with
  the cartesian product `Multiset.product`.
* `Multiset.sum`: `s.sum f` is the sum of `f i` over all `i ∈ s`.

## Implementation notes

Nov 2022: To speed the Lean 4 port, lemmas requiring extra algebra imports
(`data.list.big_operators.lemmas` rather than `.basic`) have been moved to a separate file,
`algebra.big_operators.multiset.lemmas`.  This split does not need to be permanent.
-/


variable {ι α β γ : Type*}

namespace Multiset

section CommMonoid

variable [CommMonoid α] {s t : Multiset α} {a : α} {m : Multiset ι} {f g : ι → α}

/-- Product of a multiset given a commutative monoid structure on `α`.
  `prod {a, b, c} = a * b * c` -/
@[to_additive
      "Sum of a multiset given a commutative additive monoid structure on `α`.
      `sum {a, b, c} = a + b + c`"]
def prod : Multiset α → α :=
  foldr (· * ·) (fun x y z => by simp [mul_left_comm]) 1

@[to_additive]
theorem prod_eq_foldr (s : Multiset α) :
    prod s = foldr (· * ·) (fun x y z => by simp [mul_left_comm]) 1 s :=
  rfl

@[to_additive]
theorem prod_eq_foldl (s : Multiset α) :
    prod s = foldl (· * ·) (fun x y z => by simp [mul_right_comm]) 1 s :=
  (foldr_swap _ _ _ _).trans (by simp [mul_comm])

@[to_additive (attr := simp, norm_cast)]
theorem coe_prod (l : List α) : prod ↑l = l.prod :=
  prod_eq_foldl _

@[to_additive (attr := simp)]
theorem prod_toList (s : Multiset α) : s.toList.prod = s.prod := by
  conv_rhs => rw [← coe_toList s]
  rw [coe_prod]

@[to_additive (attr := simp)]
theorem prod_zero : @prod α _ 0 = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem prod_cons (a : α) (s) : prod (a ::ₘ s) = a * prod s :=
  foldr_cons _ _ _ _ _

@[to_additive (attr := simp)]
theorem prod_erase [DecidableEq α] (h : a ∈ s) : a * (s.erase a).prod = s.prod := by
  rw [← s.coe_toList, coe_erase, coe_prod, coe_prod, List.prod_erase (mem_toList.2 h)]

@[to_additive (attr := simp)]
theorem prod_map_erase [DecidableEq ι] {a : ι} (h : a ∈ m) :
    f a * ((m.erase a).map f).prod = (m.map f).prod := by
  rw [← m.coe_toList, coe_erase, coe_map, coe_map, coe_prod, coe_prod,
    List.prod_map_erase f (mem_toList.2 h)]

@[to_additive (attr := simp)]
theorem prod_singleton (a : α) : prod {a} = a := by
  simp only [mul_one, prod_cons, ← cons_zero, eq_self_iff_true, prod_zero]

@[to_additive]
theorem prod_pair (a b : α) : ({a, b} : Multiset α).prod = a * b := by
  rw [insert_eq_cons, prod_cons, prod_singleton]

@[to_additive (attr := simp)]
theorem prod_add (s t : Multiset α) : prod (s + t) = prod s * prod t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ => by simp

@[to_additive]
theorem prod_nsmul (m : Multiset α) : ∀ n : ℕ, (n • m).prod = m.prod ^ n
  | 0 => by
    rw [zero_nsmul, pow_zero]
    rfl
  | n + 1 => by rw [add_nsmul, one_nsmul, pow_add, pow_one, prod_add, prod_nsmul m n]

@[to_additive (attr := simp)]
theorem prod_replicate (n : ℕ) (a : α) : (replicate n a).prod = a ^ n := by
  simp [replicate, List.prod_replicate]

@[to_additive]
theorem prod_map_eq_pow_single [DecidableEq ι] (i : ι)
    (hf : ∀ (i') (_ : i' ≠ i), i' ∈ m → f i' = 1) : (m.map f).prod = f i ^ m.count i := by
  induction' m using Quotient.inductionOn with l
  simp [List.prod_map_eq_pow_single i f hf]

@[to_additive]
theorem prod_eq_pow_single [DecidableEq α] (a : α) (h : ∀ (a') (_ : a' ≠ a), a' ∈ s → a' = 1) :
    s.prod = a ^ s.count a := by
  induction' s using Quotient.inductionOn with l
  simp [List.prod_eq_pow_single a h]

@[to_additive]
theorem pow_count [DecidableEq α] (a : α) : a ^ s.count a = (s.filter (Eq a)).prod := by
  rw [filter_eq, prod_replicate]

@[to_additive]
theorem prod_hom [CommMonoid β] (s : Multiset α) {F : Type*} [MonoidHomClass F α β] (f : F) :
    (s.map f).prod = f s.prod :=
  Quotient.inductionOn s fun l => by simp only [l.prod_hom f, quot_mk_to_coe, coe_map, coe_prod]

@[to_additive]
theorem prod_hom' [CommMonoid β] (s : Multiset ι) {F : Type*} [MonoidHomClass F α β] (f : F)
    (g : ι → α) : (s.map fun i => f <| g i).prod = f (s.map g).prod := by
  convert (s.map g).prod_hom f
  exact (map_map _ _ _).symm

@[to_additive]
theorem prod_hom₂ [CommMonoid β] [CommMonoid γ] (s : Multiset ι) (f : α → β → γ)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1) (f₁ : ι → α)
    (f₂ : ι → β) : (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom₂ f hf hf', quot_mk_to_coe, coe_map, coe_prod]

@[to_additive]
theorem prod_hom_rel [CommMonoid β] (s : Multiset ι) {r : α → β → Prop} {f : ι → α} {g : ι → β}
    (h₁ : r 1 1) (h₂ : ∀ ⦃a b c⦄, r b c → r (f a * b) (g a * c)) :
    r (s.map f).prod (s.map g).prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, coe_map, coe_prod]

@[to_additive]
theorem prod_map_one : prod (m.map fun _ => (1 : α)) = 1 := by
  rw [map_const', prod_replicate, one_pow]

@[to_additive (attr := simp)]
theorem prod_map_mul : (m.map fun i => f i * g i).prod = (m.map f).prod * (m.map g).prod :=
  m.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _

@[simp]
theorem prod_map_neg [HasDistribNeg α] (s : Multiset α) :
    (s.map Neg.neg).prod = (-1) ^ card s * s.prod :=
  Quotient.inductionOn s (by simp)

@[to_additive]
theorem prod_map_pow {n : ℕ} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n :=
  m.prod_hom' (powMonoidHom n : α →* α) f

@[to_additive]
theorem prod_map_prod_map (m : Multiset β) (n : Multiset γ) {f : β → γ → α} :
    prod (m.map fun a => prod <| n.map fun b => f a b) =
      prod (n.map fun b => prod <| m.map fun a => f a b) :=
  Multiset.induction_on m (by simp) fun a m ih => by simp [ih]

@[to_additive]
theorem prod_induction (p : α → Prop) (s : Multiset α) (p_mul : ∀ a b, p a → p b → p (a * b))
    (p_one : p 1) (p_s : ∀ a ∈ s, p a) : p s.prod := by
  rw [prod_eq_foldr]
  exact foldr_induction (· * ·) (fun x y z => by simp [mul_left_comm]) 1 p s p_mul p_one p_s

@[to_additive]
theorem prod_induction_nonempty (p : α → Prop) (p_mul : ∀ a b, p a → p b → p (a * b)) (hs : s ≠ ∅)
    (p_s : ∀ a ∈ s, p a) : p s.prod := by
  -- Porting note: used `refine' Multiset.induction _ _`
  induction' s using Multiset.induction_on with a s hsa
  · simp at hs
  rw [prod_cons]
  by_cases hs_empty : s = ∅
  · simp [hs_empty, p_s a]
  have hps : ∀ x, x ∈ s → p x := fun x hxs => p_s x (mem_cons_of_mem hxs)
  exact p_mul a s.prod (p_s a (mem_cons_self a s)) (hsa hs_empty hps)

theorem prod_dvd_prod_of_le (h : s ≤ t) : s.prod ∣ t.prod := by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  simp only [prod_add, dvd_mul_right]

end CommMonoid

theorem prod_dvd_prod_of_dvd [CommMonoid β] {S : Multiset α} (g1 g2 : α → β)
    (h : ∀ a ∈ S, g1 a ∣ g2 a) : (Multiset.map g1 S).prod ∣ (Multiset.map g2 S).prod := by
  apply Multiset.induction_on' S
  · simp
  intro a T haS _ IH
  simp [mul_dvd_mul (h a haS) IH]

section AddCommMonoid

variable [AddCommMonoid α]

/-- `Multiset.sum`, the sum of the elements of a multiset, promoted to a morphism of
`AddCommMonoid`s. -/
def sumAddMonoidHom : Multiset α →+ α where
  toFun := sum
  map_zero' := sum_zero
  map_add' := sum_add

@[simp]
theorem coe_sumAddMonoidHom : (sumAddMonoidHom : Multiset α → α) = sum :=
  rfl

end AddCommMonoid

section CommMonoidWithZero

variable [CommMonoidWithZero α]

theorem prod_eq_zero {s : Multiset α} (h : (0 : α) ∈ s) : s.prod = 0 := by
  rcases Multiset.exists_cons_of_mem h with ⟨s', hs'⟩
  simp [hs', Multiset.prod_cons]

variable [NoZeroDivisors α] [Nontrivial α] {s : Multiset α}

theorem prod_eq_zero_iff : s.prod = 0 ↔ (0 : α) ∈ s :=
  Quotient.inductionOn s fun l => by
    rw [quot_mk_to_coe, coe_prod]
    exact List.prod_eq_zero_iff

theorem prod_ne_zero (h : (0 : α) ∉ s) : s.prod ≠ 0 :=
  mt prod_eq_zero_iff.1 h

end CommMonoidWithZero

section DivisionCommMonoid

variable [DivisionCommMonoid α] {m : Multiset ι} {f g : ι → α}

@[to_additive]
theorem prod_map_inv' (m : Multiset α) : (m.map Inv.inv).prod = m.prod⁻¹ :=
  m.prod_hom (invMonoidHom : α →* α)

@[to_additive (attr := simp)]
theorem prod_map_inv : (m.map fun i => (f i)⁻¹).prod = (m.map f).prod⁻¹ := by
  -- Porting note: used `convert`
  simp_rw [←(m.map f).prod_map_inv', map_map, Function.comp_apply]

@[to_additive (attr := simp)]
theorem prod_map_div : (m.map fun i => f i / g i).prod = (m.map f).prod / (m.map g).prod :=
  m.prod_hom₂ (· / ·) mul_div_mul_comm (div_one _) _ _

@[to_additive]
theorem prod_map_zpow {n : ℤ} : (m.map fun i => f i ^ n).prod = (m.map f).prod ^ n := by
  convert (m.map f).prod_hom (zpowGroupHom n : α →* α)
  simp only [map_map, Function.comp_apply, zpowGroupHom_apply]

end DivisionCommMonoid

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] {a : α} {s : Multiset ι} {f : ι → α}

theorem sum_map_mul_left : sum (s.map fun i => a * f i) = a * sum (s.map f) :=
  Multiset.induction_on s (by simp) fun i s ih => by simp [ih, mul_add]

theorem sum_map_mul_right : sum (s.map fun i => f i * a) = sum (s.map f) * a :=
  Multiset.induction_on s (by simp) fun a s ih => by simp [ih, add_mul]

end NonUnitalNonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring α]

theorem dvd_sum {a : α} {s : Multiset α} : (∀ x ∈ s, a ∣ x) → a ∣ s.sum :=
  Multiset.induction_on s (fun _ => dvd_zero _) fun x s ih h => by
    rw [sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun y hy => h _ <| mem_cons.2 <| Or.inr hy)

end NonUnitalSemiring

/-! ### Order -/


section OrderedCommMonoid

variable [OrderedCommMonoid α] {s t : Multiset α} {a : α}

@[to_additive sum_nonneg]
theorem one_le_prod_of_one_le : (∀ x ∈ s, (1 : α) ≤ x) → 1 ≤ s.prod :=
  Quotient.inductionOn s fun l hl => by simpa using List.one_le_prod_of_one_le hl

@[to_additive]
theorem single_le_prod : (∀ x ∈ s, (1 : α) ≤ x) → ∀ x ∈ s, x ≤ s.prod :=
  Quotient.inductionOn s fun l hl x hx => by simpa using List.single_le_prod hl x hx

@[to_additive sum_le_card_nsmul]
theorem prod_le_pow_card (s : Multiset α) (n : α) (h : ∀ x ∈ s, x ≤ n) : s.prod ≤ n ^ card s := by
  induction s using Quotient.inductionOn
  simpa using List.prod_le_pow_card _ _ h

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
theorem all_one_of_le_one_le_of_prod_eq_one :
    (∀ x ∈ s, (1 : α) ≤ x) → s.prod = 1 → ∀ x ∈ s, x = (1 : α) :=
  Quotient.inductionOn s (by
    simp only [quot_mk_to_coe, coe_prod, mem_coe]
    exact fun l => List.all_one_of_le_one_le_of_prod_eq_one)

@[to_additive]
theorem prod_le_prod_of_rel_le (h : s.Rel (· ≤ ·) t) : s.prod ≤ t.prod := by
  induction' h with _ _ _ _ rh _ rt
  · rfl
  · rw [prod_cons, prod_cons]
    exact mul_le_mul' rh rt

@[to_additive]
theorem prod_map_le_prod_map {s : Multiset ι} (f : ι → α) (g : ι → α) (h : ∀ i, i ∈ s → f i ≤ g i) :
    (s.map f).prod ≤ (s.map g).prod :=
  prod_le_prod_of_rel_le <| rel_map.2 <| rel_refl_of_refl_on h

@[to_additive]
theorem prod_map_le_prod (f : α → α) (h : ∀ x, x ∈ s → f x ≤ x) : (s.map f).prod ≤ s.prod :=
  prod_le_prod_of_rel_le <| rel_map_left.2 <| rel_refl_of_refl_on h

@[to_additive]
theorem prod_le_prod_map (f : α → α) (h : ∀ x, x ∈ s → x ≤ f x) : s.prod ≤ (s.map f).prod :=
  @prod_map_le_prod αᵒᵈ _ _ f h

@[to_additive card_nsmul_le_sum]
theorem pow_card_le_prod (h : ∀ x ∈ s, a ≤ x) : a ^ card s ≤ s.prod := by
  rw [← Multiset.prod_replicate, ← Multiset.map_const]
  exact prod_map_le_prod _ h

end OrderedCommMonoid

theorem prod_nonneg [OrderedCommSemiring α] {m : Multiset α} (h : ∀ a ∈ m, (0 : α) ≤ a) :
    0 ≤ m.prod := by
  revert h
  refine' m.induction_on _ _
  · rintro -
    rw [prod_zero]
    exact zero_le_one
  intro a s hs ih
  rw [prod_cons]
  exact mul_nonneg (ih _ <| mem_cons_self _ _) (hs fun a ha => ih _ <| mem_cons_of_mem ha)

/-- Slightly more general version of `Multiset.prod_eq_one_iff` for a non-ordered `Monoid` -/
@[to_additive
      "Slightly more general version of `Multiset.sum_eq_zero_iff` for a non-ordered `AddMonoid`"]
theorem prod_eq_one [CommMonoid α] {m : Multiset α} (h : ∀ x ∈ m, x = (1 : α)) : m.prod = 1 := by
  induction' m using Quotient.inductionOn with l
  simp [List.prod_eq_one h]

@[to_additive]
theorem le_prod_of_mem [CanonicallyOrderedCommMonoid α] {m : Multiset α} {a : α} (h : a ∈ m) :
    a ≤ m.prod := by
  obtain ⟨m', rfl⟩ := exists_cons_of_mem h
  rw [prod_cons]
  exact _root_.le_mul_right (le_refl a)

@[to_additive le_sum_of_subadditive_on_pred]
theorem le_prod_of_submultiplicative_on_pred [CommMonoid α] [OrderedCommMonoid β] (f : α → β)
    (p : α → Prop) (h_one : f 1 = 1) (hp_one : p 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hps : ∀ a, a ∈ s → p a) : f s.prod ≤ (s.map f).prod := by
  revert s
  refine' Multiset.induction _ _
  · simp [le_of_eq h_one]
  intro a s hs hpsa
  have hps : ∀ x, x ∈ s → p x := fun x hx => hpsa x (mem_cons_of_mem hx)
  have hp_prod : p s.prod := prod_induction p s hp_mul hp_one hps
  rw [prod_cons, map_cons, prod_cons]
  exact (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans (mul_le_mul_left' (hs hps) _)

@[to_additive le_sum_of_subadditive]
theorem le_prod_of_submultiplicative [CommMonoid α] [OrderedCommMonoid β] (f : α → β)
    (h_one : f 1 = 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) :
    f s.prod ≤ (s.map f).prod :=
  le_prod_of_submultiplicative_on_pred f (fun _ => True) h_one trivial (fun x y _ _ => h_mul x y)
    (by simp) s (by simp)

@[to_additive le_sum_nonempty_of_subadditive_on_pred]
theorem le_prod_nonempty_of_submultiplicative_on_pred [CommMonoid α] [OrderedCommMonoid β]
    (f : α → β) (p : α → Prop) (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b)
    (hp_mul : ∀ a b, p a → p b → p (a * b)) (s : Multiset α) (hs_nonempty : s ≠ ∅)
    (hs : ∀ a, a ∈ s → p a) : f s.prod ≤ (s.map f).prod := by
  revert s
  refine' Multiset.induction _ _
  · intro h
    exfalso
    exact h rfl
  rintro a s hs - hsa_prop
  rw [prod_cons, map_cons, prod_cons]
  by_cases hs_empty : s = ∅
  · simp [hs_empty]
  have hsa_restrict : ∀ x, x ∈ s → p x := fun x hx => hsa_prop x (mem_cons_of_mem hx)
  have hp_sup : p s.prod := prod_induction_nonempty p hp_mul hs_empty hsa_restrict
  have hp_a : p a := hsa_prop a (mem_cons_self a s)
  exact (h_mul a _ hp_a hp_sup).trans (mul_le_mul_left' (hs hs_empty hsa_restrict) _)

@[to_additive le_sum_nonempty_of_subadditive]
theorem le_prod_nonempty_of_submultiplicative [CommMonoid α] [OrderedCommMonoid β] (f : α → β)
    (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) (hs_nonempty : s ≠ ∅) :
    f s.prod ≤ (s.map f).prod :=
  le_prod_nonempty_of_submultiplicative_on_pred f (fun _ => True) (by simp [h_mul]) (by simp) s
    hs_nonempty (by simp)

@[simp]
theorem sum_map_singleton (s : Multiset α) : (s.map fun a => ({a} : Multiset α)).sum = s :=
  Multiset.induction_on s (by simp) (by simp)

theorem abs_sum_le_sum_abs [LinearOrderedAddCommGroup α] {s : Multiset α} :
    abs s.sum ≤ (s.map abs).sum :=
  le_sum_of_subadditive _ abs_zero abs_add s

theorem sum_nat_mod (s : Multiset ℕ) (n : ℕ) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Nat.add_mod, *]

theorem prod_nat_mod (s : Multiset ℕ) (n : ℕ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Nat.mul_mod, *]

theorem sum_int_mod (s : Multiset ℤ) (n : ℤ) : s.sum % n = (s.map (· % n)).sum % n := by
  induction s using Multiset.induction <;> simp [Int.add_emod, *]

theorem prod_int_mod (s : Multiset ℤ) (n : ℤ) : s.prod % n = (s.map (· % n)).prod % n := by
  induction s using Multiset.induction <;> simp [Int.mul_emod, *]

end Multiset

@[to_additive]
theorem map_multiset_prod [CommMonoid α] [CommMonoid β] {F : Type*} [MonoidHomClass F α β] (f : F)
    (s : Multiset α) : f s.prod = (s.map f).prod :=
  (s.prod_hom f).symm

@[to_additive]
protected theorem MonoidHom.map_multiset_prod [CommMonoid α] [CommMonoid β] (f : α →* β)
    (s : Multiset α) : f s.prod = (s.map f).prod :=
  (s.prod_hom f).symm
