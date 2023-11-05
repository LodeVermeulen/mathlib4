/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Order.Group.Abs

#align_import algebra.order.ring.abs from "leanprover-community/mathlib"@"10b4e499f43088dd3bb7b5796184ad5216648ab1"

/-!
# Absolute values in linear ordered rings.
-/


variable {α : Type*}

section LinearOrderedRing

variable [LinearOrderedRing α] {a b c : α}

@[simp]
theorem abs_one : |(1 : α)| = 1 :=
  abs_of_pos zero_lt_one

@[simp]
theorem abs_two : |(2 : α)| = 2 :=
  abs_of_pos zero_lt_two

theorem abs_mul (a b : α) : |a * b| = |a| * |b| := by
  rw [abs_eq (mul_nonneg (abs_nonneg a) (abs_nonneg b))]
  cases' le_total a 0 with ha ha <;> cases' le_total b 0 with hb hb <;>
    simp only [abs_of_nonpos, abs_of_nonneg, true_or_iff, or_true_iff, eq_self_iff_true, neg_mul,
      mul_neg, neg_neg, *]

/-- `abs` as a `MonoidWithZeroHom`. -/
def absHom : α →*₀ α :=
  { toFun := abs
    map_zero' := abs_zero
    map_one' := abs_one
    map_mul' := abs_mul }

@[simp]
theorem abs_mul_abs_self (a : α) : |a| * |a| = a * a :=
  abs_by_cases (fun x => x * x = a * a) rfl (neg_mul_neg a a)

@[simp]
theorem abs_mul_self (a : α) : |a * a| = a * a := by rw [abs_mul, abs_mul_abs_self]

theorem abs_eq_iff_mul_self_eq : |a| = |b| ↔ a * a = b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact (mul_self_inj (abs_nonneg a) (abs_nonneg b)).symm

theorem abs_lt_iff_mul_self_lt : |a| < |b| ↔ a * a < b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact mul_self_lt_mul_self_iff (abs_nonneg a) (abs_nonneg b)

theorem abs_le_iff_mul_self_le : |a| ≤ |b| ↔ a * a ≤ b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact mul_self_le_mul_self_iff (abs_nonneg a) (abs_nonneg b)

theorem abs_le_one_iff_mul_self_le_one : |a| ≤ 1 ↔ a * a ≤ 1 := by
  simpa only [abs_one, one_mul] using @abs_le_iff_mul_self_le α _ a 1

end LinearOrderedRing

section LinearOrderedCommRing

variable [LinearOrderedCommRing α] {a b c d : α}

theorem abs_sub_sq (a b : α) : |a - b| * |a - b| = a * a + b * b - (1 + 1) * a * b := by
  rw [abs_mul_abs_self]
  simp only [mul_add, add_comm, add_left_comm, mul_comm, sub_eq_add_neg, mul_one, mul_neg,
    neg_add_rev, neg_neg, add_assoc]

end LinearOrderedCommRing

section

variable [Ring α] [LinearOrder α] {a b : α}

@[simp]
theorem abs_dvd (a b : α) : |a| ∣ b ↔ a ∣ b := by
  cases' abs_choice a with h h <;> simp only [h, neg_dvd]

theorem abs_dvd_self (a : α) : |a| ∣ a :=
  (abs_dvd a a).mpr (dvd_refl a)

@[simp]
theorem dvd_abs (a b : α) : a ∣ |b| ↔ a ∣ b := by
  cases' abs_choice b with h h <;> simp only [h, dvd_neg]

theorem self_dvd_abs (a : α) : a ∣ |a| :=
  (dvd_abs a a).mpr (dvd_refl a)

theorem abs_dvd_abs (a b : α) : |a| ∣ |b| ↔ a ∣ b :=
  (abs_dvd _ _).trans (dvd_abs _ _)

end
