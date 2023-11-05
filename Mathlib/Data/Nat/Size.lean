/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Nat.Pow
import Mathlib.Data.Nat.Bits

#align_import data.nat.size from "leanprover-community/mathlib"@"18a5306c091183ac90884daa9373fa3b178e8607"

/-! Lemmas about `size`. -/

namespace Nat

/-! ### `shiftLeft` and `shiftRight` -/

section
set_option linter.deprecated false

theorem shiftLeft_eq_mul_pow (m) : ∀ n, m <<< n = m * 2 ^ n := shiftLeft_eq _

theorem shiftLeft'_tt_eq_mul_pow (m) : ∀ n, shiftLeft' true m n + 1 = (m + 1) * 2 ^ n
  | 0 => by simp [shiftLeft', pow_zero, Nat.one_mul]
  | k + 1 => by
    change bit1 (shiftLeft' true m k) + 1 = (m + 1) * (2 ^ k * 2)
    rw [bit1_val]
    change 2 * (shiftLeft' true m k + 1) = _
    rw [shiftLeft'_tt_eq_mul_pow m k, mul_left_comm, mul_comm 2]

end


theorem zero_shiftLeft (n) : 0 <<< n = 0 := by simp


theorem shiftLeft'_ne_zero_left (b) {m} (h : m ≠ 0) (n) : shiftLeft' b m n ≠ 0 := by
  induction n <;> simp [bit_ne_zero, shiftLeft', *]

theorem shiftLeft'_tt_ne_zero (m) : ∀ {n}, (n ≠ 0) → shiftLeft' true m n ≠ 0
  | 0, h => absurd rfl h
  | succ _, _ => Nat.bit1_ne_zero _

/-! ### `size` -/


@[simp]
theorem size_zero : size 0 = 0 := by simp [size]

@[simp]
theorem size_bit {b n} (h : bit b n ≠ 0) : size (bit b n) = succ (size n) := by
  rw [size]
  conv =>
    lhs
    rw [binaryRec]
    simp [h]
  rw [div2_bit]

section
set_option linter.deprecated false

@[simp]
theorem size_bit0 {n} (h : n ≠ 0) : size (bit0 n) = succ (size n) :=
  @size_bit false n (Nat.bit0_ne_zero h)

@[simp]
theorem size_bit1 (n) : size (bit1 n) = succ (size n) :=
  @size_bit true n (Nat.bit1_ne_zero n)

@[simp]
theorem size_one : size 1 = 1 :=
  show size (bit1 0) = 1 by rw [size_bit1, size_zero]

end

@[simp]
theorem size_shiftLeft' {b m n} (h : shiftLeft' b m n ≠ 0) :
    size (shiftLeft' b m n) = size m + n := by
  induction' n with n IH <;> simp [shiftLeft'] at h ⊢
  rw [size_bit h, Nat.add_succ]
  by_cases s0 : shiftLeft' b m n = 0 <;> [skip; rw [IH s0]]
  rw [s0] at h ⊢
  cases b; · exact absurd rfl h
  have : shiftLeft' true m n + 1 = 1 := congr_arg (· + 1) s0
  rw [shiftLeft'_tt_eq_mul_pow] at this
  obtain rfl := succ.inj (eq_one_of_dvd_one ⟨_, this.symm⟩)
  simp only [zero_add, one_mul] at this
  obtain rfl : n = 0 :=
    Nat.eq_zero_of_le_zero
      (le_of_not_gt fun hn => ne_of_gt (pow_lt_pow_of_lt_right (by decide) hn) this)
  rfl

-- TODO: decide whether `Nat.shiftLeft_eq` (which rewrites the LHS into a power) should be a simp
-- lemma; it was not in mathlib3. Until then, tell the simpNF linter to ignore the issue.
@[simp, nolint simpNF]
theorem size_shiftLeft {m} (h : m ≠ 0) (n) : size (m <<< n) = size m + n :=
  by simp only [size_shiftLeft' (shiftLeft'_ne_zero_left _ h _), ← shiftLeft'_false]

theorem lt_size_self (n : ℕ) : n < 2 ^ size n := by
  rw [← one_shiftLeft]
  have : ∀ {n}, n = 0 → n < 1 <<< (size n) := by simp
  apply binaryRec _ _ n
  · apply this rfl
  intro b n IH
  by_cases h : bit b n = 0
  · apply this h
  rw [size_bit h, shiftLeft_succ, shiftLeft_eq, one_mul, ← bit0_val]
  exact bit_lt_bit0 _ (by simpa [shiftRight_eq_div_pow] using IH)

theorem size_le {m n : ℕ} : size m ≤ n ↔ m < 2 ^ n :=
  ⟨fun h => lt_of_lt_of_le (lt_size_self _) (pow_le_pow_of_le_right (by decide) h), by
    rw [← one_shiftLeft]; revert n
    apply binaryRec _ _ m
    · intro n
      simp
    · intro b m IH n h
      by_cases e : bit b m = 0
      · simp [e]
      rw [size_bit e]
      cases' n with n
      · exact e.elim (Nat.eq_zero_of_le_zero (le_of_lt_succ h))
      · apply succ_le_succ (IH _)
        apply lt_of_mul_lt_mul_left _ (zero_le 2)
        simp only [← bit0_val, shiftLeft_succ] at *
        exact lt_of_le_of_lt (bit0_le_bit b rfl.le) h⟩

theorem lt_size {m n : ℕ} : m < size n ↔ 2 ^ m ≤ n := by
  rw [← not_lt, Decidable.iff_not_comm, not_lt, size_le]

theorem size_pos {n : ℕ} : 0 < size n ↔ 0 < n := by rw [lt_size]; rfl

theorem size_eq_zero {n : ℕ} : size n = 0 ↔ n = 0 := by
  have := @size_pos n; simp [pos_iff_ne_zero] at this; exact Decidable.not_iff_not.1 this

theorem size_pow {n : ℕ} : size (2 ^ n) = n + 1 :=
  le_antisymm (size_le.2 <| pow_lt_pow_of_lt_right (by decide) (lt_succ_self _))
    (lt_size.2 <| le_rfl)

theorem size_le_size {m n : ℕ} (h : m ≤ n) : size m ≤ size n :=
  size_le.2 <| lt_of_le_of_lt h (lt_size_self _)

theorem size_eq_bits_len (n : ℕ) : n.bits.length = n.size := by
  induction' n using Nat.binaryRec' with b n h ih; · simp
  rw [size_bit, bits_append_bit _ _ h]
  · simp [ih]
  · simpa [bit_eq_zero_iff]

end Nat
