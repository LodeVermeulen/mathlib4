/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Order.MinMax
import Mathlib.Algebra.Order.Monoid.Lemmas

#align_import algebra.order.monoid.min_max from "leanprover-community/mathlib"@"de87d5053a9fe5cbde723172c0fb7e27e7436473"

/-!
# Lemmas about `min` and `max` in an ordered monoid.
-/


open Function

variable {α β : Type*}

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/


@[to_additive]
theorem fn_min_mul_fn_max [LinearOrder α] [CommSemigroup β] (f : α → β) (n m : α) :
    f (min n m) * f (max n m) = f n * f m := by cases' le_total n m with h h <;> simp [h, mul_comm]

@[to_additive]
theorem min_mul_max [LinearOrder α] [CommSemigroup α] (n m : α) : min n m * max n m = n * m :=
  fn_min_mul_fn_max id n m

section CovariantClassMulLe

variable [LinearOrder α]

section Mul

variable [Mul α]

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)]

@[to_additive]
theorem min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c :=
  (monotone_id.const_mul' a).map_min.symm

@[to_additive]
theorem max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
  (monotone_id.const_mul' a).map_max.symm

end Left

section Right

variable [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]

@[to_additive]
theorem min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c :=
  (monotone_id.mul_const' c).map_min.symm

@[to_additive]
theorem max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
  (monotone_id.mul_const' c).map_max.symm

end Right

@[to_additive]
theorem lt_or_lt_of_mul_lt_mul [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ < a₂ * b₂ → a₁ < a₂ ∨ b₁ < b₂ := by
  contrapose!
  exact fun h => mul_le_mul' h.1 h.2

@[to_additive]
theorem le_or_lt_of_mul_le_mul [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· < ·)] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ < b₂ := by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_le h.1 h.2

@[to_additive]
theorem lt_or_le_of_mul_le_mul [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ < a₂ ∨ b₁ ≤ b₂ := by
  contrapose!
  exact fun h => mul_lt_mul_of_le_of_lt h.1 h.2

@[to_additive]
theorem le_or_le_of_mul_le_mul [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· < ·)] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ ≤ b₂ := by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_lt h.1 h.2

@[to_additive]
theorem mul_lt_mul_iff_of_le_of_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· < ·)] {a₁ a₂ b₁ b₂ : α} (ha : a₁ ≤ a₂)
    (hb : b₁ ≤ b₂) : a₁ * b₁ < a₂ * b₂ ↔ a₁ < a₂ ∨ b₁ < b₂ := by
  refine' ⟨lt_or_lt_of_mul_lt_mul, fun h => _⟩
  cases' h with ha' hb'
  · exact mul_lt_mul_of_lt_of_le ha' hb
  · exact mul_lt_mul_of_le_of_lt ha hb'

end Mul

variable [MulOneClass α]

@[to_additive]
theorem min_le_mul_of_one_le_right [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (hb : 1 ≤ b) :
    min a b ≤ a * b :=
  min_le_iff.2 <| Or.inl <| le_mul_of_one_le_right' hb

@[to_additive]
theorem min_le_mul_of_one_le_left [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b : α}
    (ha : 1 ≤ a) : min a b ≤ a * b :=
  min_le_iff.2 <| Or.inr <| le_mul_of_one_le_left' ha

@[to_additive]
theorem max_le_mul_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    max a b ≤ a * b :=
  max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

end CovariantClassMulLe
