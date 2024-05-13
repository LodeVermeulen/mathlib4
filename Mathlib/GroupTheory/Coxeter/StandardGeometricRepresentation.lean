/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.LinearAlgebra.Reflection
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The standard geometric representation

Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

Let $V$ be the free $\mathbb{R}$ vector space over `B` and let $\{\alpha_i\}$ be the standard basis
of $V$. We define a the *standard bilinear form* on $V$ (`CoxeterMatrix.standardBilinForm`) by
$$\langle \alpha_i, \alpha_{i'}\rangle = -\cos (\pi / M_{i, i'}),$$
where $M$ is the Coxeter matrix of $W$. This is positive definite if and only if $W$ is a finite
group, although we do not prove that in this file.

Then, we have a representation $\rho \colon W \to GL(V)$, called the
*standard geometric representation* (`CoxeterSystem.standardGeometricRepresentation`), given by
$$\rho(s_i) v = v - \langle \alpha_i, v\rangle \alpha_i.$$
We prove that this representation is well defined and faithful (`CoxeterSystem.injective_sgr`).

We prove for all $w$ and $i$ that $\ell(w s_i) + 1 = \ell(w)$ if and only if $\rho(w) \alpha_i$ is a
nonpositive linear combination of the simple roots, and that $\ell(w s_i) = \ell(w) + 1$ if and only
if $\rho(w) \alpha_i$ is a nonnegative linear combination of the simple roots.

## Main definitions

* `CoxeterMatrix.standardBilinForm`
* `CoxeterSystem.standardGeometricRepresentation`

## References

* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)

-/

noncomputable section

open List Real LinearMap

/-! ### The standard geometric representation
Given a Coxeter group `W` whose simple reflections are indexed by a set `B`, we define
the standard geometric representation of `W`, which is a representation of `W` with underlying
vector space `B →₀ ℝ`.
-/
namespace CoxeterMatrix

variable {B : Type*}
variable (M : CoxeterMatrix B)

local notation "V" => B →₀ ℝ

private local instance : AddCommMonoid V := Finsupp.instAddCommMonoid

/-- The simple root at index `i`. That is, the standard basis vector of `B →₀ ℝ` at index `i`. -/
def simpleRoot (i : B) : V := Finsupp.single i 1

local prefix:100 "α" => simpleRoot

/-- The standard bilinear form on `B →₀ ℝ`. Given by `⟪αᵢ, αⱼ⟫ = -cos (π / Mᵢⱼ)`
for `i j : B`, where {αᵢ} is the standard basis of `B →₀ ℝ` and `M` is the Coxeter matrix.
This is positive definite if and only if the associated Coxeter group is finite. -/
def standardBilinForm : LinearMap.BilinForm ℝ V :=
  (Finsupp.lift (V →ₗ[ℝ] ℝ) ℝ B)
    (fun i ↦ ((Finsupp.lift ℝ ℝ B)
      (fun i' ↦ -cos (π / M i i'))))

local notation:max "⟪"  a  ","  b  "⟫" => M.standardBilinForm a b

theorem standardBilinForm_simpleRoot_self (i : B) :
    ⟪α i, α i⟫ = 1 := by simp [standardBilinForm, simpleRoot, M.diagonal i]

theorem standardBilinForm_simpleRoot_simpleRoot (i i' : B) :
    ⟪α i, α i'⟫ = - cos (π / M i i') := by simp [standardBilinForm, simpleRoot]

theorem isSymm_standardBilinForm : LinearMap.IsSymm (standardBilinForm M) := by
  apply LinearMap.isSymm_iff_eq_flip.mpr
  apply (Finsupp.basisSingleOne).ext
  intro i
  apply (Finsupp.basisSingleOne).ext
  intro i'
  simp [standardBilinForm, M.symmetric i i']

theorem standardBilinForm_comm (v v' : V) : ⟪v, v'⟫ = ⟪v', v⟫ := M.isSymm_standardBilinForm.eq v v'

/-- The orthogonal reflection in the vector `v` under the standard bilinear form.
-/
def orthoReflection {v : V} (hv : ⟪v, v⟫ = 1) :
    V →ₗ[ℝ] V := Module.reflection (show ((2 : ℝ) • (standardBilinForm M v)) v = 2 by
      rw [LinearMap.smul_apply, hv]; norm_num)

local prefix:100 "r" => M.orthoReflection

attribute [local simp] Module.reflection
attribute [local simp] Module.preReflection

@[simp]
theorem orthoReflection_apply_self {v : V} (hv : ⟪v, v⟫ = 1) : (r hv) v = -v :=
  Module.reflection_apply_self _

theorem orthoReflection_sq {v : V} (hv : ⟪v, v⟫ = 1) :
    (r hv) * (r hv) = LinearMap.id := by
  apply LinearMap.ext
  exact Module.involutive_reflection (show ((2 : ℝ) • (standardBilinForm M v)) v = 2 by
    rw [LinearMap.smul_apply, hv]; norm_num)

theorem orthoReflection_eq_orthoReflection_iff {v v' : V} (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) :
    r hv = r hv' ↔ ∃ μ : ℝ, v' = μ • v := by
  constructor
  · intro h
    have h₁ : (r hv) v' = (r hv') v' := LinearMap.ext_iff.mp h v'
    rw [M.orthoReflection_apply_self hv'] at h₁
    dsimp [orthoReflection] at h₁
    apply congrArg (v' + ·) at h₁
    rw [add_right_neg, add_sub, ← two_smul ℝ v'] at h₁
    apply sub_eq_zero.mp at h₁
    apply congrArg (((1 : ℝ) / 2) • ·) at h₁
    rw [smul_smul, smul_smul, ← mul_assoc] at h₁
    norm_num at h₁
    use ⟪v, v'⟫
  · rintro ⟨μ, rfl⟩
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hv'
    simp only [map_smul, smul_apply, smul_eq_mul, hv, mul_one] at hv'
    -- hv': μ * μ = 1
    apply LinearMap.ext
    intro w
    dsimp [orthoReflection]
    rw [smul_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_assoc 2,
        mul_comm _ μ, ← mul_assoc μ, hv']
    simp

@[simp]
theorem standardBilinForm_orthoReflection_apply {v : V} {hv : ⟪v, v⟫ = 1} (w w' : V) :
    ⟪(r hv) w, (r hv) w'⟫ = ⟪w, w'⟫ := by
  dsimp [orthoReflection]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  simp only [← M.isSymm_standardBilinForm.eq v w, RingHom.id_apply, hv]
  ring

/-- Any orthogonal reflection is orthogonal with respect to the standard bilinear form. -/
theorem standardBilinForm_compl₁₂_orthoReflection {v : V} (hv : ⟪v, v⟫ = 1) :
    LinearMap.compl₁₂ M.standardBilinForm (r hv) (r hv) = M.standardBilinForm :=
  LinearMap.ext fun w ↦ LinearMap.ext fun w' ↦ M.standardBilinForm_orthoReflection_apply w w'

/-- The orthogonal reflection in the standard basis vector `αᵢ` under the standard bilinear form. -/
def simpleOrthoReflection (i : B) := r (M.standardBilinForm_simpleRoot_self i)

local prefix:100 "σ" => M.simpleOrthoReflection

theorem simpleOrthoReflection_simpleRoot (i i' : B) :
    (σ i) (α i') = α i' + (2 * cos (π / M i i')) • α i := by
  dsimp [simpleOrthoReflection, orthoReflection]
  rw [standardBilinForm_simpleRoot_simpleRoot]
  rw [sub_eq_add_neg, ← neg_smul]
  congr
  ring

@[simp] theorem simpleOrthoReflection_simpleRoot_self (i : B) : (σ i) (α i) = -α i := by
  simp [simpleOrthoReflection_simpleRoot, M.diagonal i, two_smul]

private lemma sin_pi_div_m_ne_zero {m : ℕ} (hm : 1 < m) : sin (π / m) ≠ 0 := by
  have h₀ : 0 < π / m := div_pos pi_pos (zero_lt_one.trans (by exact_mod_cast hm))
  have h₁ : π / m < π := div_lt_self pi_pos (by exact_mod_cast hm)
  exact ne_of_gt (sin_pos_of_pos_of_lt_pi h₀ h₁)

theorem orthoReflection_mul_orthoReflection_pow_apply {v v' : V} {m : ℕ} (k : ℕ) (hm : 1 < m)
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = - cos (π / m)) :
    ((r hv * r hv') ^ k) v =
      (sin ((2 * k + 1) * (π / m)) / sin (π / m)) • v +
        (sin (2 * k * (π / m)) / sin (π / m)) • v' := by
  induction' k with k ih
  · simp [div_self (sin_pi_div_m_ne_zero hm)]
  · -- Apply inductive hypothesis.
    rw [pow_succ', LinearMap.mul_apply, ih, LinearMap.mul_apply]
    -- Expand everything out.
    simp only [map_sub, map_add, map_smul]
    dsimp [orthoReflection]
    simp only [map_sub, map_add, map_smul, smul_sub, smul_add, smul_smul, hv, hv',
      map_smul, LinearMap.smul_apply]
    -- Rewrite using - cos (π / m) = ⟪v, v'⟫.
    rw [M.standardBilinForm_comm v' v, hvv']
    clear hv hv' hvv' ih
    -- Sort the terms and write the entire expression as a • v + b • v'.
    simp only [sub_eq_add_neg, neg_add, ← neg_smul, smul_eq_mul]
    have h₁ : ∀ a b : ℝ, a • v + b • v = (a + b) • v :=
      fun _ _ ↦ (add_smul _ _ _).symm
    have h₂ : ∀ a b : ℝ, a • v' + b • v' = (a + b) • v' :=
      fun _ _ ↦ (add_smul _ _ _).symm
    have h₃ : ∀ a b : ℝ, a • v' + b • v = b • v + a • v' :=
      fun _ _ ↦ add_comm _ _
    have h₄ : ∀ a b c : ℝ, a • v + b • v' + c • v = (a + c) • v + b • v' :=
      fun a b c ↦ (add_right_comm _ _ _).trans (congrArg (· + _) (h₁ a c))
    have h₅ : ∀ a b c : ℝ, a • v + b • v' + c • v' = a • v + (b + c) • v' :=
      fun a b c ↦ (add_assoc _ _ _).trans (congrArg (_ + ·) (h₂ b c))
    simp only [← add_assoc, h₁, h₂, h₃, h₄, h₅]
    clear h₁ h₂ h₃ h₄ h₅
    -- Simplify using the sine and cosine angle addition formula.
    have h₆ : ((2 * (Nat.succ k) + 1) * (π / m)) = 2 * k * (π / m) + π / m + π / m + π / m := by
      rw [Nat.succ_eq_add_one]
      push_cast
      ring
    have h₇ : ((2 * (Nat.succ k)) * (π / m)) = 2 * k * (π / m) + π / m + π / m := by
      rw [Nat.succ_eq_add_one]
      push_cast
      ring
    have h₈ : ((2 * k + 1) * (π / m)) = 2 * k * (π / m) + π / m := by ring
    simp only [h₆, h₇, h₈, sin_add, cos_add]
    clear h₆ h₇ h₈
    -- Now equate the coefficients of `v` and `v'`.
    congr
    · field_simp [sin_pi_div_m_ne_zero hm]
      have := sin_sq_add_cos_sq (π / m)
      linear_combination
        (3 * sin (2 * k * π / m) * cos (π / m) + cos (2 * k * π / m) * sin (π / m)) * this
    · field_simp [sin_pi_div_m_ne_zero hm]
      have := sin_sq_add_cos_sq (π / m)
      linear_combination sin (2 * k * π / m) * this

private lemma orthoReflection_mul_orthoReflection_pow_order_apply_v {v v' : V} {m : ℕ} (hm : 1 < m)
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) :
    (((r hv) * (r hv')) ^ m) v = v := by
  rw [M.orthoReflection_mul_orthoReflection_pow_apply m hm hv hv' hvv']
  rw [add_mul, mul_assoc 2, mul_div_cancel₀ _ (by positivity)]
  simp [add_comm, sin_add_two_pi, sin_two_pi, div_self (sin_pi_div_m_ne_zero hm)]

private lemma orthoReflection_mul_orthoReflection_pow_order_apply_v' {v v' : V} {m : ℕ} (hm : 1 < m)
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) :
    (((r hv) * (r hv')) ^ m) v' = v' := let a := r hv; let b := r hv'; calc
  ((a * b) ^ m) v'
  _ = (b * b * (a * b) ^ m) v'         := by simp [M.orthoReflection_sq hv']
  _ = (b * (b * (a * b) ^ m)) v'       := by rw [mul_assoc]
  _ = (b * ((b * a) ^ m * b)) v'       := by
    congr 2
    exact (SemiconjBy.eq (SemiconjBy.pow_right (by unfold SemiconjBy; group) m))
  _ = (b * (b * a) ^ m * b) v'         := by rw [mul_assoc]
  _ = (b * (b * a) ^ m) (b v')         := LinearMap.mul_apply _ _ _
  _ = (b * (b * a) ^ m) (-v')          := congrArg _ (M.orthoReflection_apply_self hv')
  _ = -((b * (b * a) ^ m) v')          := map_neg _ _
  _ = -(b (((b * a) ^ m) v'))          := congrArg _ (LinearMap.mul_apply _ _ _)
  _ = -(b v')                          := by
    congr
    apply M.orthoReflection_mul_orthoReflection_pow_order_apply_v hm hv' hv
    · rwa [← M.standardBilinForm_comm v v']
  _ = -(-v')                           := congrArg _ (M.orthoReflection_apply_self hv')
  _ = v'                               := neg_neg v'

private lemma can_decomp_into_parallel_and_orthogonal {v v' : V} (w : V) {m : ℕ}
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) (hm : m > 1) :
    ∃ μ₁ μ₂ : ℝ, ⟪v, w - μ₁ • v - μ₂ • v'⟫ = 0 ∧ ⟪v', w - μ₁ • v - μ₂ • v'⟫ = 0 := by
  use (1 / (sin (π / m)) ^ 2) * (⟪v, w⟫ + cos (π / m) * ⟪v', w⟫)
  use (1 / (sin (π / m)) ^ 2) * (⟪v', w⟫ + cos (π / m) * ⟪v, w⟫)
  -- Expand everything out.
  simp only [mul_add, LinearMap.map_sub, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
  -- Use known values of bilinear form.
  rw [(by rw [← M.isSymm_standardBilinForm.eq v' v]; simp : ⟪v', v⟫ = ⟪v, v'⟫)]
  simp only [hv, hv', hvv']
  field_simp [sin_pi_div_m_ne_zero hm]
  ring_nf
  constructor
  all_goals {
    rw [Real.sin_sq]
    ring
  }

private lemma fixed_of_orthogonal {v v' : V} (w : V) {m : ℕ}
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvw : ⟪v, w⟫ = 0) (hv'w : ⟪v', w⟫ = 0) :
    (((r hv) * (r hv')) ^ m) w = w := by
  induction' m with m ih
  · simp
  · rw [pow_succ', LinearMap.mul_apply, ih, LinearMap.mul_apply]
    dsimp [orthoReflection]
    simp [hvw, hv'w]

private lemma orthoReflection_mul_orthoReflection_pow_order {v v' : V} {m : ℕ}
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) (hm : m ≠ 1) :
    ((r hv) * (r hv')) ^ m = 1 := by
  rcases Nat.lt_or_gt_of_ne hm with mlt | mgt
  · simp [Nat.lt_one_iff.mp mlt]
  · apply LinearMap.ext
    intro w
    rcases M.can_decomp_into_parallel_and_orthogonal w hv hv' hvv' mgt with ⟨μ₁, μ₂, hμ⟩
    set! w' := w - μ₁ • v - μ₂ • v' with hw'
    rw [← hw'] at hμ
    rcases hμ with ⟨h₁, h₂⟩
    have h₃ : w = w' + μ₁ • v + μ₂ • v' := by rw [hw']; abel
    simp only [h₃, LinearMap.map_add, LinearMap.map_smul, LinearMap.one_apply]
    congr
    · exact M.fixed_of_orthogonal w' hv hv' h₁ h₂
    · exact M.orthoReflection_mul_orthoReflection_pow_order_apply_v mgt hv hv' hvv'
    · exact M.orthoReflection_mul_orthoReflection_pow_order_apply_v' mgt hv hv' hvv'

end CoxeterMatrix

namespace CoxeterSystem

open CoxeterMatrix

variable {B : Type*}
variable {W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "α" => simpleRoot
local notation:max "⟪"  a  ","  b  "⟫" => M.standardBilinForm a b
local notation:100 "σ" i => M.simpleOrthoReflection i
local notation "V" => B →₀ ℝ

private local instance : AddCommMonoid V := Finsupp.instAddCommMonoid

/-- The standard geometric representation on `B →₀ ℝ`. For `i : B`, the simple reflection `sᵢ`
acts by `sᵢ v = v - 2 ⟪αᵢ, v⟫ * αᵢ`, where {αᵢ} is the standard basis of `B →₀ ℝ`. -/
def standardGeometricRepresentation : Representation ℝ W V := cs.lift ⟨M.simpleOrthoReflection, by
  intro i i'
  rcases em (i = i') with rfl | ne
  · simp [simpleOrthoReflection, orthoReflection_sq, ← LinearMap.one_eq_id]
  · apply M.orthoReflection_mul_orthoReflection_pow_order
    · exact M.standardBilinForm_simpleRoot_simpleRoot i i'
    · exact M.off_diagonal i i' ne⟩

noncomputable alias sgr := standardGeometricRepresentation

local prefix:100 "ρ" => cs.sgr

theorem sgr_simple (i : B) : ρ (s i) = σ i := cs.lift_apply_simple _ i

/-- The standard geometric representation preserves the standard bilinear form. -/
@[simp]
theorem standardBilinForm_sgr_apply (w : W) (v v' : V) :
    ⟪(ρ w) v, (ρ w) v'⟫ = ⟪v, v'⟫ := by
  induction' w using cs.simple_induction with i w₁ w₂ hw₁ hw₂ generalizing v v'
  · simp [sgr_simple, simpleOrthoReflection]
  · simp
  · simp [map_mul, mul_apply, hw₁, hw₂]

theorem standardBilinForm_sgr_inv_apply (w : W) (v v' : V) :
    ⟪(ρ w⁻¹) v, v'⟫ = ⟪v, (ρ w) v'⟫ := by
  convert cs.standardBilinForm_sgr_apply w⁻¹ v ((ρ w) v')
  simp [← mul_apply, ← map_mul]

theorem standardBilinForm_sgr_inv_apply' (w : W) (v v' : V) :
    ⟪v, (ρ w⁻¹) v'⟫ = ⟪(ρ w) v, v'⟫ := by
  convert cs.standardBilinForm_sgr_apply w⁻¹ ((ρ w) v) v'
  simp [← mul_apply, ← map_mul]

/-- The standard geometric representation preserves the standard bilinear form. -/
theorem standardBilinForm_compl₁₂_sgr_apply (w : W) :
    M.standardBilinForm.compl₁₂ (ρ w) (ρ w) = M.standardBilinForm :=
  LinearMap.ext fun v ↦ LinearMap.ext fun v' ↦ cs.standardBilinForm_sgr_apply w v v'

theorem sgr_alternatingWord_apply_simpleRoot (i i' : B) (m : ℕ) (hM : 1 < M i i') :
    (ρ (π (alternatingWord i i' m))) (α i) = if Even m
      then (sin ((m + 1) * (π / M i i')) / sin (π / M i i')) • (α i)
        + (sin (m * (π / M i i')) / sin (π / M i i')) • (α i')
      else (sin (m * (π / M i i')) / sin (π / M i i')) • (α i)
        + (sin ((m + 1) * (π / M i i')) / sin (π / M i i')) • (α i') := by
  rw [prod_alternatingWord_eq_mul_pow, map_mul, map_pow, map_mul, apply_ite cs.sgr, map_one,
    mul_apply]
  simp only [sgr_simple]
  nth_rw 3 [simpleOrthoReflection]
  nth_rw 2 [simpleOrthoReflection]
  rw [orthoReflection_mul_orthoReflection_pow_apply
    (hvv' := M.standardBilinForm_simpleRoot_simpleRoot i i') (hm := hM)]
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [if_pos (by use k), if_pos (by use k), one_apply]
    rw [← two_mul, Nat.mul_div_cancel_left _ (by norm_num : 2 > 0)]
    push_cast
    ring_nf
  · rw [if_neg (by apply Nat.odd_iff_not_even.mp; use k),
      if_neg (by apply Nat.odd_iff_not_even.mp; use k)]
    have h₁ : (2 * k + 1) / 2 = k := by rw [Nat.mul_add_div (by positivity)]; norm_num
    have h₂ : (2 * k : ℕ) = 2 * (k : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_two]
    have h₃ : (2 * k + 1 : ℕ) = 2 * (k : ℝ) + 1 := by
      rw [Nat.cast_add, h₂, Nat.cast_one]
    simp only [h₁, h₂, h₃]
    simp only [map_add, map_smul, map_smul]
    rw [simpleOrthoReflection_simpleRoot_self, simpleOrthoReflection_simpleRoot]
    rw [smul_neg, ← neg_smul, smul_add, smul_smul, add_assoc, ← add_smul]
    congr
    have : (2 * ↑k + 1 + 1) * (π / M i i') = (2 * k + 1) * (π / M i i') + π / M i i' := by
      field_simp
      ring
    rw [this, sin_add]
    have : (2 * k) * (π / M i i') = (2 * k + 1) * π / M i i' - π / M i i' := by
      field_simp
      ring
    rw [this, sin_sub]
    rw [M.symmetric i i']
    ring_nf

theorem sgr_alternatingWord_apply_simpleRoot' (i i' : B) (m : ℕ) (hM : M i i' = 0) :
    (ρ (π (alternatingWord i i' m))) (α i) = if Even m
      then (m + 1 : ℝ) • (α i) + (m : ℝ) • (α i')
      else (m : ℝ) • (α i) + (m + 1 : ℝ) • (α i') := by
  have h₁ : (σ i') (α i) = α i + (2 : ℝ) • α i' := by
    rw [simpleOrthoReflection_simpleRoot, M.symmetric, hM]
    simp
  have h₂ : (σ i) (α i') = (2 : ℝ) • α i + α i' := by
    rw [simpleOrthoReflection_simpleRoot, hM]
    simp only [Nat.cast_zero, div_zero, cos_zero, mul_one]
    abel
  induction' m with m ih
  · simp [alternatingWord]
  · rw [alternatingWord_succ', wordProd_cons, map_mul, mul_apply, ih]
    have := @Nat.even_add_one m
    rcases em (Even m) with even | not_even
    · have succ_not_even : ¬ Even (Nat.succ m) := by tauto
      simp only [if_pos even, if_neg succ_not_even]
      simp only [sgr_simple, map_add, map_smul, h₁, simpleOrthoReflection_simpleRoot_self]
      rw [Nat.cast_succ, smul_add, smul_smul, smul_neg, ← neg_smul, add_assoc, ← add_smul]
      congr 2
      ring
    · have succ_even : Even (Nat.succ m) := by tauto
      simp only [if_neg not_even, if_pos succ_even]
      simp only [sgr_simple, map_add, map_smul, h₂, simpleOrthoReflection_simpleRoot_self]
      rw [Nat.cast_succ, smul_add, smul_smul, smul_neg, ← neg_smul, ← add_assoc, ← add_smul]
      congr 2
      ring

theorem sgr_alternatingWord_apply_simpleRoot_eq_nonneg_smul_add_nonneg_smul
    (i i' : B) (m : ℕ) (hm : m < M i i' ∨ M i i' = 0) :
    ∃ (μ μ' : ℝ), μ ≥ 0 ∧ μ' ≥ 0 ∧
      (ρ (π (alternatingWord i i' m))) (α i) = μ • (α i) + μ' • (α i') := by
  rcases hm with m_lt | M_eq_zero
  · rcases le_or_gt (M i i') 1 with M_le_one | M_gt_one
    · rw [(by linarith : m = 0), alternatingWord]
      use 1, 0
      simp
    · let μ₁ := sin (m * (π / M i i')) / sin (π / M i i')
      let μ₂ := sin ((m + 1) * (π / M i i')) / sin (π / M i i')
      have h₁ : π / M i i' ≤ π := by
        apply div_le_of_nonneg_of_le_mul
        · linarith
        · exact pi_nonneg
        · apply (le_mul_iff_one_le_right pi_pos).mpr
          rw [Nat.one_le_cast]
          linarith
      have h₂ : m * (π / M i i') ≤ π := by
        rw [← mul_div_assoc]
        apply div_le_of_nonneg_of_le_mul
        · linarith
        · exact pi_nonneg
        · rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.le_of_lt m_lt)) pi_nonneg
      have h₃ : (m + 1) * (π / M i i') ≤ π := by
        rw [← mul_div_assoc]
        apply div_le_of_nonneg_of_le_mul
        · linarith
        · exact pi_nonneg
        · rw [mul_comm]
          apply mul_le_mul_of_nonneg_left _ pi_nonneg
          rw [← Nat.cast_succ]
          exact Nat.cast_le.mpr (Nat.succ_le_of_lt m_lt)
      have μ₁_nonneg : 0 ≤ μ₁ := by
        apply div_nonneg
        · apply sin_nonneg_of_nonneg_of_le_pi
          · positivity
          · exact h₂
        · apply sin_nonneg_of_nonneg_of_le_pi
          · positivity
          · exact h₁
      have μ₂_nonneg : 0 ≤ μ₂ := by
        apply div_nonneg
        · apply sin_nonneg_of_nonneg_of_le_pi
          · positivity
          · exact h₃
        · apply sin_nonneg_of_nonneg_of_le_pi
          · positivity
          · exact h₁
      rw [cs.sgr_alternatingWord_apply_simpleRoot i i' m M_gt_one]
      rcases em (Even m) with even | not_even
      · rw [if_pos even]
        use μ₂, μ₁, μ₂_nonneg, μ₁_nonneg
      · rw [if_neg not_even]
        use μ₁, μ₂, μ₁_nonneg, μ₂_nonneg
  · rw [cs.sgr_alternatingWord_apply_simpleRoot' i i' m M_eq_zero]
    rcases em (Even m) with even | not_even
    · rw [if_pos even]
      use m + 1, m, by linarith, by linarith
    · rw [if_neg not_even]
      use m, m + 1, by linarith, by linarith

private theorem sgr_apply_simpleRoot_nonneg_of {w : W} {i : B} (h : ¬cs.IsRightDescent w i) :
    (ρ w) (α i) ≥ 0 := by
  classical
  -- We use induction on the length of `w`.
  generalize hn : ℓ w = n
  induction' n using Nat.strong_induction_on with n ih generalizing w i
  rcases em (w = 1) with rfl | w_ne_one
  · -- If `w = 1`, then the statement is trivial.
    simp only [map_one, one_apply]
    intro i'
    rw [simpleRoot, Finsupp.single_apply, Finsupp.zero_apply, apply_ite (0 ≤ ·)]
    simp
  · -- Otherwise, `w ≠ 1`. Let `i'` be a right descent of `w`.
    have h₁ : 1 ≤ ℓ w := Nat.one_le_iff_ne_zero.mpr (cs.length_eq_zero_iff.mp.mt w_ne_one)
    rcases cs.exists_rightDescent_of_ne_one w_ne_one with ⟨i', hwi'⟩
    -- Use the notation `aw` for alternating product of simple reflections `s i` and `s i'`.
    set aw := fun m ↦ π (alternatingWord i i' m) with haw
    /- Let `m` be the greatest positive integer such that
    `ℓ (w * (π (aw m))⁻¹) + m = ℓ w`.
    (That is, `w` can be written as a product `v * u⁻¹`,
    where `ℓ v + ℓ u = ℓ w` and `u` is a reduced alternating word of length `m` that alternates
    between `i` and `i'`, ending with `i'`.) -/
    set m := Nat.findGreatest (fun m ↦ ℓ (w * (aw m)⁻¹) + m = ℓ w) (ℓ w) with h₂
    /- Because `w` has `i'` as a right descent, we have
    `ℓ (w * (aw 1)⁻¹) + 1 = ℓ w`. So `1 ≤ m`. -/
    have h₃ : 1 ≤ m := by
      apply Nat.le_findGreatest
      · exact h₁
      · simp [haw, alternatingWord]
        exact cs.isRightDescent_iff.mp hwi'
    -- Also, `ℓ (w * (aw m)⁻¹) + m = ℓ w`, by definition of `m`.
    have h₄ : ℓ (w * (aw m)⁻¹) + m = ℓ w := by
      apply Nat.findGreatest_of_ne_zero h₂.symm
      exact Nat.one_le_iff_ne_zero.mp h₃
    clear w_ne_one h₁ h₂
    -- By the maximality of `m`, `ℓ (w * (aw (m + 1))⁻¹) + (m + 1) ≠ ℓ w`.
    have h₅ : ℓ (w * (aw (m + 1))⁻¹) + (m + 1) ≠ ℓ w := by
      rcases Nat.lt_or_ge (ℓ w) (m + 1) with lt | ge
      · linarith only [lt]
      · apply Nat.findGreatest_is_greatest (Nat.lt_succ_self m)
        exact ge
    -- Now we simplify this using `alternatingWord_succ'`.
    rw [haw] at h₅
    dsimp at h₅
    rw [alternatingWord_succ', wordProd_cons, mul_inv_rev, inv_simple, ← mul_assoc] at h₅
    set j := if Even m then i' else i with h₆
    -- `h₅ : ℓ (w * (aw m)⁻¹ * s j) + (m + 1) ≠ length cs w`
    -- By `h₅`, we see that `i''` is not a right descent of `w * (aw m)⁻¹`.
    have h₇ : ¬ cs.IsRightDescent (w * (aw m)⁻¹) j := by
      intro h'
      apply cs.isRightDescent_iff.mp at h'
      rw [add_comm m 1, ← add_assoc, h'] at h₅
      exact h₅ h₄
    /- Let `j' = if Even (m - 1) then i else i'`. So `j` and `j'` are `i` and `i'`, but potentially
    swapped. -/
    set j' := if Even (m - 1) then i' else i with h₈
    /- Let us also prove that `j'` is not a right descent of `w * (aw m)⁻¹`. We will start by
    showing that `(aw m)⁻¹ * (s j') = (aw (m - 1))⁻¹`.-/
    have h₉ : (aw m)⁻¹ * (s j') = (aw (m - 1))⁻¹ := by
      nth_rw 1 [← Nat.sub_add_cancel h₃]
      rw [haw]
      dsimp
      rw [alternatingWord_succ', wordProd_cons, mul_inv_rev, mul_assoc, inv_simple,
        simple_mul_simple_self, mul_one]
    have h₁₀ : ¬ cs.IsRightDescent (w * (aw m)⁻¹) j' := by
      intro h'
      apply cs.isRightDescent_iff.mp at h'
      have := calc
        ℓ (w * (aw (m - 1))⁻¹) + 1 + m
        _ = ℓ (w * (aw m)⁻¹ * (s j')) + 1 + m           := by rw [mul_assoc, h₉]
        _ = ℓ (w * (aw m)⁻¹) + m                        := by rw [h']
        _ = ℓ w                                         := h₄
        _ = ℓ (w * (aw (m - 1))⁻¹ * aw (m - 1))         := by group
        _ ≤ ℓ (w * (aw (m - 1))⁻¹) + ℓ (aw (m - 1))     := cs.length_mul_le _ _
        _ ≤ ℓ (w * (aw (m - 1))⁻¹) + (m - 1)            := by
            apply add_le_add_left
            exact (cs.length_wordProd_le _).trans (le_of_eq (length_alternatingWord i i' (m - 1)))
        _ ≤ ℓ (w * (aw (m - 1))⁻¹) + m                  := by
            apply add_le_add_left
            exact Nat.sub_le _ _
      linarith only [this]
    /- Since `j` and `j'` are not right descents of `w * (aw m)⁻¹`, and `i` and `i'` are just
    `j` and `j'` in some order, we conclude that `i` and `i'` are not right descents of
    `w * (aw m)⁻¹`. -/
    rw [h₆] at h₇
    rw [h₈] at h₁₀
    clear h₅ h₆ h₈ h₉ j j'
    -- `m` is even if and only if `m - 1` is not even
    have h₁₁ := Nat.sub_add_cancel h₃ ▸ @Nat.even_add_one (m - 1)
    have h₁₂ : ¬ cs.IsRightDescent (w * (aw m)⁻¹) i := by
      rcases em (Even (m - 1)) with even | not_even
      · rwa [if_neg (h₁₁.mp.mt (not_not.mpr even))] at h₇
      · rwa [if_neg not_even] at h₁₀
    have h₁₃ : ¬ cs.IsRightDescent (w * (aw m)⁻¹) i' := by
      rcases em (Even (m - 1)) with even | not_even
      · rwa [if_pos even] at h₁₀
      · rwa [if_pos (h₁₁.mpr not_even)] at h₇
    have h₁₄ : ℓ (w * (aw m)⁻¹) < n := by linarith only [h₃, h₄, hn]
    /- By the inductive hypothesis, `ρ (w * (aw m)⁻¹) (α i)` and `ρ (w * (aw m)⁻¹) (α i')` are
    positive. -/
    have h₁₆ := ih (ℓ (w * (aw m)⁻¹)) h₁₄ h₁₂ rfl
    have h₁₇ := ih (ℓ (w * (aw m)⁻¹)) h₁₄ h₁₃ rfl
    clear h₇ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄
    /- Now we must prove the condition `hm : m < M i i' ∨ M i i' = 0` of
    `sgr_alternatingWord_apply_simpleRoot_eq_nonneg_smul_add_nonneg_smul`. First, we show
    that `alternatingWord i i' m` is reduced. -/
    have h₁₈ := calc
      ℓ (w * (aw m)⁻¹) + ℓ (aw m)
      _ ≥ ℓ (w * (aw m)⁻¹ * aw m)                            := cs.length_mul_le _ _
      _ = ℓ w                                                := by group
      _ = ℓ (w * (aw m)⁻¹) + m                               := h₄.symm
      _ = ℓ (w * (aw m)⁻¹) + (alternatingWord i i' m).length := by rw [length_alternatingWord]
    have h₁₉ : cs.IsReduced (alternatingWord i i' m) := by
      unfold IsReduced
      apply _root_.le_antisymm
      · exact cs.length_wordProd_le _
      · linarith only [h₁₈]
    have h₂₀ : m ≤ M i i' ∨ M i i' = 0 := by
      by_contra! h'
      exact cs.not_isReduced_alternatingWord i i' h'.2 h'.1 h₁₉
    clear h₁₈ h₁₉
    /- If `m = M i i'` and `M i i' ≠ 0`, then `aw m` has a reduced word that ends with `i` instead
    of `i'`. We obtain a contradiction from the fact that `i` is not a
    right descent of `w`. -/
    have h₂₁ : ¬ (m = M i i' ∧ M i i' ≠ 0) := by
      rintro ⟨m_eq, _⟩
      have : aw m = π (alternatingWord i' i m) := by
        rw [m_eq]
        nth_rw 2 [M.symmetric i i']
        exact cs.wordProd_braidWord_eq i i'
      rw [this] at h₄
      have := calc
        ℓ (w * s i)
        _ < ℓ (w * s i) + 1                                        := Nat.lt_succ_self _
        _ = ℓ (w * s i * (π (alternatingWord i i' (m - 1)))⁻¹
              * π (alternatingWord i i' (m - 1))) + 1              := by group
        _ ≤ ℓ (w * s i * (π (alternatingWord i i' (m - 1)))⁻¹)
              + ℓ (π (alternatingWord i i' (m - 1))) + 1           := by
                  apply add_le_add_right
                  exact cs.length_mul_le _ _
        _ ≤ ℓ (w * s i * (π (alternatingWord i i' (m - 1)))⁻¹)
              + (alternatingWord i i' (m - 1)).length + 1          := by
                  apply add_le_add_right
                  apply add_le_add_left
                  exact cs.length_wordProd_le _
        _ = ℓ (w * s i * (π (alternatingWord i i' (m - 1)))⁻¹)
              + (m - 1) + 1                                        := by rw [length_alternatingWord]
        _ = ℓ (w * s i * (π (alternatingWord i i' (m - 1)))⁻¹) + m := by
                  rw [add_assoc, Nat.sub_add_cancel h₃]
        _ = ℓ (w * (π (alternatingWord i i' (m - 1)) * s i)⁻¹) + m := by simp [mul_assoc]
        _ = ℓ (w * (π ((alternatingWord i i' (m - 1)).concat i))⁻¹)
              + m                                                  := by rw [cs.wordProd_concat]
        _ = ℓ (w * (π (alternatingWord i' i (m - 1 + 1)))⁻¹) + m   := by rw [alternatingWord_succ]
        _ = ℓ (w * (π (alternatingWord i' i m))⁻¹) + m             := by rw [Nat.sub_add_cancel h₃]
        _ = ℓ w                                                    := h₄
      exact h this
    have h₂₂ : m < M i i' ∨ M i i' = 0 := by
      rw [Nat.lt_iff_le_and_ne]
      tauto
    clear h hwi' h₃ h₄ h₂₀ h₂₁
    -- We have `(ρ w) (α i) = ρ (w * (aw m)⁻¹) ((ρ (aw m)) (α i))`.
    rw [(by group : w = w * (aw m)⁻¹ * (aw m)), map_mul, mul_apply]
    /- Now, we write `((ρ (aw m)) (α i))` as a nonnegative linear combination of `α i` and `α i'`.
    Then expand everything out and use `h₁₆`, `h₁₇`. -/
    rcases cs.sgr_alternatingWord_apply_simpleRoot_eq_nonneg_smul_add_nonneg_smul i i' m h₂₂ with
      ⟨μ, μ', μ_nonneg, μ'_nonneg, h₂₃⟩
    nth_rw 2 [haw]
    dsimp only
    rw [h₂₃, map_add, map_smul, map_smul]
    exact add_nonneg (smul_nonneg μ_nonneg h₁₆) (smul_nonneg μ'_nonneg h₁₇)

/-- If $i$ is not a right descent of $w$, then $\rho(w) \alpha_i$ is positive; that is, it has
nonnegative coordinates and it is nonzero. -/
theorem sgr_apply_simpleRoot_pos_of {w : W} {i : B} (h : ¬cs.IsRightDescent w i) :
    0 < (ρ w) (α i) := by
  apply lt_of_le_of_ne
  · exact cs.sgr_apply_simpleRoot_nonneg_of h
  · intro h'
    have := congrArg (ρ (w⁻¹)) h'
    rw [← mul_apply, ← map_mul, inv_mul_self, map_one, one_apply, map_zero] at this
    exact one_ne_zero (Finsupp.single_eq_zero.mp this.symm)

/-- If $i$ is not a right descent of $w$, then $\rho(w) \alpha_i$ is negative; that is, it has
nonpositive coordinates and it is nonzero. -/
theorem sgr_apply_simpleRoot_neg_of {w : W} {i : B} (h : cs.IsRightDescent w i) :
    (ρ w) (α i) < 0 := by
  apply cs.isRightDescent_iff_not_isRightDescent_mul.mp at h
  apply sgr_apply_simpleRoot_pos_of at h
  rw [map_mul, mul_apply, sgr_simple, simpleOrthoReflection_simpleRoot_self, map_neg] at h
  exact neg_pos.mp h

theorem sgr_apply_simpleRoot_pos_iff {w : W} {i : B} :
    0 < (ρ w) (α i) ↔ ¬ cs.IsRightDescent w i := by
  constructor
  · intro h h'
    exact lt_asymm (cs.sgr_apply_simpleRoot_neg_of h') h
  · intro h
    exact cs.sgr_apply_simpleRoot_pos_of h

theorem sgr_apply_simpleRoot_neg_iff {w : W} {i : B} :
    (ρ w) (α i) < 0 ↔ cs.IsRightDescent w i := by
  constructor
  · intro h
    by_contra h'
    exact lt_asymm (cs.sgr_apply_simpleRoot_pos_of h') h
  · intro h
    exact cs.sgr_apply_simpleRoot_neg_of h

theorem injective_sgr : Function.Injective cs.sgr := by
  classical
  apply (injective_iff_map_eq_one _).mpr
  intro w hw
  by_contra! w_ne_one
  rcases cs.exists_rightDescent_of_ne_one w_ne_one with ⟨i, hi⟩
  have := cs.sgr_apply_simpleRoot_neg_of hi
  rw [hw, one_apply] at this
  have := Finsupp.le_def.mp (le_of_lt this) i
  rw [Finsupp.zero_apply, simpleRoot, Finsupp.single_apply, if_pos (rfl : i = i)] at this
  norm_num at this

end CoxeterSystem

end