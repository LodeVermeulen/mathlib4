/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Benjamin Davidson
-/
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic.Abel

#align_import data.int.parity from "leanprover-community/mathlib"@"e3d9ab8faa9dea8f78155c6c27d62a621f4c152d"

/-!
# Parity of integers

This file contains theorems about the `Even` and `Odd` predicates on the integers.

## Tags

even, odd
-/

namespace Int

variable {m n : ℤ}

@[simp]
theorem emod_two_ne_one : ¬n % 2 = 1 ↔ n % 2 = 0 := by
  cases' emod_two_eq_zero_or_one n with h h <;> simp [h]

-- `EuclideanDomain.mod_eq_zero` uses (2 ∣ n) as normal form
@[local simp]
theorem emod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by
  cases' emod_two_eq_zero_or_one n with h h <;> simp [h]

theorem even_iff : Even n ↔ n % 2 = 0 :=
  ⟨fun ⟨m, hm⟩ => by simp [← two_mul, hm],
    fun h => ⟨n / 2, (emod_add_ediv n 2).symm.trans (by simp [← two_mul, h])⟩⟩

theorem odd_iff : Odd n ↔ n % 2 = 1 :=
  ⟨fun ⟨m, hm⟩ => (by rw [hm, add_emod]; norm_num),
    fun h => ⟨n / 2, (emod_add_ediv n 2).symm.trans (by rw [h]; abel)⟩⟩

theorem not_even_iff : ¬Even n ↔ n % 2 = 1 := by rw [even_iff, emod_two_ne_zero]

theorem not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by rw [odd_iff, emod_two_ne_one]

theorem even_iff_not_odd : Even n ↔ ¬Odd n := by rw [not_odd_iff, even_iff]

@[simp]
theorem odd_iff_not_even : Odd n ↔ ¬Even n := by rw [not_even_iff, odd_iff]

theorem isCompl_even_odd : IsCompl { n : ℤ | Even n } { n | Odd n } := by
  simp [← Set.compl_setOf, isCompl_compl]

theorem even_or_odd (n : ℤ) : Even n ∨ Odd n :=
  Or.imp_right odd_iff_not_even.2 <| em <| Even n

theorem even_or_odd' (n : ℤ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [two_mul, exists_or, Odd, Even] using even_or_odd n

theorem even_xor'_odd (n : ℤ) : Xor' (Even n) (Odd n) := by
  cases even_or_odd n with
  | inl h => exact Or.inl ⟨h, even_iff_not_odd.mp h⟩
  | inr h => exact Or.inr ⟨h, odd_iff_not_even.mp h⟩

theorem even_xor'_odd' (n : ℤ) : ∃ k, Xor' (n = 2 * k) (n = 2 * k + 1) := by
  rcases even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> use k
  · simpa only [← two_mul, Xor', true_and_iff, eq_self_iff_true, not_true, or_false_iff,
      and_false_iff] using (succ_ne_self (2 * k)).symm
  · simp only [Xor', add_right_eq_self, false_or_iff, eq_self_iff_true, not_true, not_false_iff,
      one_ne_zero, and_self_iff]

@[simp]
theorem two_dvd_ne_zero : ¬2 ∣ n ↔ n % 2 = 1 :=
  even_iff_two_dvd.symm.not.trans not_even_iff

instance : DecidablePred (Even : ℤ → Prop) := fun _ => decidable_of_iff _ even_iff.symm

instance : DecidablePred (Odd : ℤ → Prop) := fun _ => decidable_of_iff _ odd_iff_not_even.symm

@[simp]
theorem not_even_one : ¬Even (1 : ℤ) := by
  rw [even_iff]
  norm_num

@[parity_simps]
theorem even_add : Even (m + n) ↔ (Even m ↔ Even n) := by
  cases' emod_two_eq_zero_or_one m with h₁ h₁ <;>
  cases' emod_two_eq_zero_or_one n with h₂ h₂ <;>
  simp [even_iff, h₁, h₂, Int.add_emod]

theorem even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by
  rw [even_add, even_iff_not_odd, even_iff_not_odd, not_iff_not]

set_option linter.deprecated false in

@[simp, deprecated]
theorem not_even_bit1 (n : ℤ) : ¬Even (bit1 n) := by simp [bit1, parity_simps]

theorem two_not_dvd_two_mul_add_one (n : ℤ) : ¬2 ∣ 2 * n + 1 := by
  simp [add_emod]

@[parity_simps]
theorem even_sub : Even (m - n) ↔ (Even m ↔ Even n) := by
  simp [sub_eq_add_neg, parity_simps]

theorem even_sub' : Even (m - n) ↔ (Odd m ↔ Odd n) := by
  rw [even_sub, even_iff_not_odd, even_iff_not_odd, not_iff_not]

@[parity_simps]
theorem even_add_one : Even (n + 1) ↔ ¬Even n := by
  simp [even_add]

@[parity_simps]
theorem even_mul : Even (m * n) ↔ Even m ∨ Even n := by
  cases' emod_two_eq_zero_or_one m with h₁ h₁ <;>
  cases' emod_two_eq_zero_or_one n with h₂ h₂ <;>
  simp [even_iff, h₁, h₂, Int.mul_emod]

theorem odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by simp [not_or, parity_simps]

theorem Odd.of_mul_left (h : Odd (m * n)) : Odd m :=
  (odd_mul.mp h).1

theorem Odd.of_mul_right (h : Odd (m * n)) : Odd n :=
  (odd_mul.mp h).2

@[parity_simps]
theorem even_pow {n : ℕ} : Even (m ^ n) ↔ Even m ∧ n ≠ 0 := by
  induction' n with n ih <;> simp [*, even_mul, pow_succ]
  tauto

theorem even_pow' {n : ℕ} (h : n ≠ 0) : Even (m ^ n) ↔ Even m :=
  even_pow.trans <| and_iff_left h

@[parity_simps]
theorem odd_pow {n : ℕ} : Odd (m ^ n) ↔ Odd m ∨ n = 0 := by
  rw [← not_iff_not, ← Int.even_iff_not_odd, not_or, ← Int.even_iff_not_odd, Int.even_pow]

theorem odd_pow' {n : ℕ} (h : n ≠ 0) : Odd (m ^ n) ↔ Odd m :=
  odd_pow.trans <| or_iff_left h

@[parity_simps]
theorem odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_add, not_iff, odd_iff_not_even]

theorem odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by
  rw [add_comm, odd_add]

theorem ne_of_odd_add (h : Odd (m + n)) : m ≠ n :=
  fun hnot => by simp [hnot, parity_simps] at h

@[parity_simps]
theorem odd_sub : Odd (m - n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_sub, not_iff, odd_iff_not_even]

theorem odd_sub' : Odd (m - n) ↔ (Odd n ↔ Even m) := by
  rw [odd_iff_not_even, even_sub, not_iff, not_iff_comm, odd_iff_not_even]

theorem even_mul_succ_self (n : ℤ) : Even (n * (n + 1)) := by
  simpa [even_mul, parity_simps] using n.even_or_odd

@[simp, norm_cast]
theorem even_coe_nat (n : ℕ) : Even (n : ℤ) ↔ Even n := by
  rw_mod_cast [even_iff, Nat.even_iff]

-- Porting note: was simp. simp can prove this.
@[norm_cast]
theorem odd_coe_nat (n : ℕ) : Odd (n : ℤ) ↔ Odd n := by
  rw [odd_iff_not_even, Nat.odd_iff_not_even, even_coe_nat]

@[simp]
theorem natAbs_even : Even n.natAbs ↔ Even n := by
  simp [even_iff_two_dvd, dvd_natAbs, coe_nat_dvd_left.symm]

-- Porting note: was simp. simp can prove this.
--@[simp]
theorem natAbs_odd : Odd n.natAbs ↔ Odd n := by
  rw [odd_iff_not_even, Nat.odd_iff_not_even, natAbs_even]

alias ⟨_, _root_.Even.natAbs⟩ := natAbs_even

alias ⟨_, _root_.Odd.natAbs⟩ := natAbs_odd

-- Porting note: "protected"-attribute not implemented yet.
-- mathlib3 had:
-- `attribute [protected] Even.natAbs Odd.natAbs`

theorem four_dvd_add_or_sub_of_odd {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    4 ∣ a + b ∨ 4 ∣ a - b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  obtain h | h := Int.even_or_odd (m + n)
  · right
    rw [Int.even_add, ← Int.even_sub] at h
    obtain ⟨k, hk⟩ := h
    convert dvd_mul_right 4 k using 1
    rw [eq_add_of_sub_eq hk, mul_add, add_assoc, add_sub_cancel, ← two_mul, ← mul_assoc]
    rfl
  · left
    obtain ⟨k, hk⟩ := h
    convert dvd_mul_right 4 (k + 1) using 1
    rw [eq_sub_of_add_eq hk, add_right_comm, ← add_sub, mul_add, mul_sub, add_assoc, add_assoc,
      sub_add, add_assoc, ← sub_sub (2 * n), sub_self, zero_sub, sub_neg_eq_add, ← mul_assoc,
      mul_add]
    rfl

theorem two_mul_ediv_two_of_even : Even n → 2 * (n / 2) = n :=
  fun h => Int.mul_ediv_cancel' (even_iff_two_dvd.mp h)

theorem ediv_two_mul_two_of_even : Even n → n / 2 * 2 = n :=
  fun h => Int.ediv_mul_cancel (even_iff_two_dvd.mp h)

theorem two_mul_ediv_two_add_one_of_odd : Odd n → 2 * (n / 2) + 1 = n := by
  rintro ⟨c, rfl⟩
  rw [mul_comm]
  convert Int.ediv_add_emod' (2 * c + 1) 2
  simp [Int.add_emod]

theorem ediv_two_mul_two_add_one_of_odd : Odd n → n / 2 * 2 + 1 = n := by
  rintro ⟨c, rfl⟩
  convert Int.ediv_add_emod' (2 * c + 1) 2
  simp [Int.add_emod]

theorem add_one_ediv_two_mul_two_of_odd : Odd n → 1 + n / 2 * 2 = n := by
  rintro ⟨c, rfl⟩
  rw [add_comm]
  convert Int.ediv_add_emod' (2 * c + 1) 2
  simp [Int.add_emod]

theorem two_mul_ediv_two_of_odd (h : Odd n) : 2 * (n / 2) = n - 1 :=
  eq_sub_of_add_eq (two_mul_ediv_two_add_one_of_odd h)

-- Here are examples of how `parity_simps` can be used with `Int`.
example (m n : ℤ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp [*, (by decide : ¬2 = 0), parity_simps]

example : ¬Even (25394535 : ℤ) := by simp

end Int
