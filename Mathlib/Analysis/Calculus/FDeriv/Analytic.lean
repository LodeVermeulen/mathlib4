/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Add

#align_import analysis.calculus.fderiv_analytic from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Frechet derivatives of analytic functions.

A function expressible as a power series at a point has a Frechet derivative there.
Also the special case in terms of `deriv` when the domain is 1-dimensional.
-/


open Filter Asymptotics

open scoped ENNReal

universe u v

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞}
variable {f : E → F} {x : E} {s : Set E}

theorem HasFPowerSeriesAt.hasStrictFDerivAt (h : HasFPowerSeriesAt f p x) :
    HasStrictFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x := by
  refine' h.isBigO_image_sub_norm_mul_norm_sub.trans_isLittleO (IsLittleO.of_norm_right _)
  refine' isLittleO_iff_exists_eq_mul.2 ⟨fun y => ‖y - (x, x)‖, _, EventuallyEq.rfl⟩
  refine' (continuous_id.sub continuous_const).norm.tendsto' _ _ _
  rw [_root_.id, sub_self, norm_zero]
#align has_fpower_series_at.has_strict_fderiv_at HasFPowerSeriesAt.hasStrictFDerivAt

theorem HasFPowerSeriesAt.hasFDerivAt (h : HasFPowerSeriesAt f p x) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p 1)) x :=
  h.hasStrictFDerivAt.hasFDerivAt
#align has_fpower_series_at.has_fderiv_at HasFPowerSeriesAt.hasFDerivAt

theorem HasFPowerSeriesAt.differentiableAt (h : HasFPowerSeriesAt f p x) : DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt
#align has_fpower_series_at.differentiable_at HasFPowerSeriesAt.differentiableAt

theorem AnalyticAt.differentiableAt : AnalyticAt 𝕜 f x → DifferentiableAt 𝕜 f x
  | ⟨_, hp⟩ => hp.differentiableAt
#align analytic_at.differentiable_at AnalyticAt.differentiableAt

theorem AnalyticAt.differentiableWithinAt (h : AnalyticAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x :=
  h.differentiableAt.differentiableWithinAt
#align analytic_at.differentiable_within_at AnalyticAt.differentiableWithinAt

theorem HasFPowerSeriesAt.fderiv_eq (h : HasFPowerSeriesAt f p x) :
    fderiv 𝕜 f x = continuousMultilinearCurryFin1 𝕜 E F (p 1) :=
  h.hasFDerivAt.fderiv
#align has_fpower_series_at.fderiv_eq HasFPowerSeriesAt.fderiv_eq

theorem HasFPowerSeriesOnBall.differentiableOn [CompleteSpace F]
    (h : HasFPowerSeriesOnBall f p x r) : DifferentiableOn 𝕜 f (EMetric.ball x r) := fun _ hy =>
  (h.analyticAt_of_mem hy).differentiableWithinAt
#align has_fpower_series_on_ball.differentiable_on HasFPowerSeriesOnBall.differentiableOn

theorem AnalyticOn.differentiableOn (h : AnalyticOn 𝕜 f s) : DifferentiableOn 𝕜 f s := fun y hy =>
  (h y hy).differentiableWithinAt
#align analytic_on.differentiable_on AnalyticOn.differentiableOn

theorem HasFPowerSeriesOnBall.hasFDerivAt [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y) :=
  (h.changeOrigin hy).hasFPowerSeriesAt.hasFDerivAt
#align has_fpower_series_on_ball.has_fderiv_at HasFPowerSeriesOnBall.hasFDerivAt

theorem HasFPowerSeriesOnBall.fderiv_eq [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    fderiv 𝕜 f (x + y) = continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1) :=
  (h.hasFDerivAt hy).fderiv
#align has_fpower_series_on_ball.fderiv_eq HasFPowerSeriesOnBall.fderiv_eq

/-- If a function has a power series on a ball, then so does its derivative. -/
theorem HasFPowerSeriesOnBall.fderiv [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (fderiv 𝕜 f) p.derivSeries x r := by
  refine .congr (f := fun z ↦ continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin (z - x) 1)) ?_
    fun z hz ↦ ?_
  · refine continuousMultilinearCurryFin1 𝕜 E F
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesOnBall ?_
    simpa using ((p.hasFPowerSeriesOnBall_changeOrigin 1
      (h.r_pos.trans_le h.r_le)).mono h.r_pos h.r_le).comp_sub x
  dsimp only
  rw [← h.fderiv_eq, add_sub_cancel]
  simpa only [edist_eq_coe_nnnorm_sub, EMetric.mem_ball] using hz
#align has_fpower_series_on_ball.fderiv HasFPowerSeriesOnBall.fderiv

/-- If a function is analytic on a set `s`, so is its Fréchet derivative. -/
theorem AnalyticOn.fderiv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (fderiv 𝕜 f) s := by
  intro y hy
  rcases h y hy with ⟨p, r, hp⟩
  exact hp.fderiv.analyticAt
#align analytic_on.fderiv AnalyticOn.fderiv

/-- If a function is analytic on a set `s`, so are its successive Fréchet derivative. -/
theorem AnalyticOn.iteratedFDeriv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) (n : ℕ) :
    AnalyticOn 𝕜 (iteratedFDeriv 𝕜 n f) s := by
  induction' n with n IH
  · rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E[×0]→L[𝕜] F).comp_analyticOn h
  · rw [iteratedFDeriv_succ_eq_comp_left]
    -- Porting note: for reasons that I do not understand at all, `?g` cannot be inlined.
    convert ContinuousLinearMap.comp_analyticOn ?g IH.fderiv
    case g => exact ↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) F)
    simp
#align analytic_on.iterated_fderiv AnalyticOn.iteratedFDeriv

/-- An analytic function is infinitely differentiable. -/
theorem AnalyticOn.contDiffOn [CompleteSpace F] (h : AnalyticOn 𝕜 f s) {n : ℕ∞} :
    ContDiffOn 𝕜 n f s :=
  let t := { x | AnalyticAt 𝕜 f x }
  suffices ContDiffOn 𝕜 n f t from this.mono h
  have H : AnalyticOn 𝕜 f t := fun _x hx ↦ hx
  have t_open : IsOpen t := isOpen_analyticAt 𝕜 f
  contDiffOn_of_continuousOn_differentiableOn
    (fun m _ ↦ (H.iteratedFDeriv m).continuousOn.congr
      fun  _ hx ↦ iteratedFDerivWithin_of_isOpen _ t_open hx)
    (fun m _ ↦ (H.iteratedFDeriv m).differentiableOn.congr
      fun _ hx ↦ iteratedFDerivWithin_of_isOpen _ t_open hx)
#align analytic_on.cont_diff_on AnalyticOn.contDiffOn

theorem AnalyticAt.contDiffAt [CompleteSpace F] (h : AnalyticAt 𝕜 f x) {n : ℕ∞} :
    ContDiffAt 𝕜 n f x := by
  obtain ⟨s, hs, hf⟩ := h.exists_mem_nhds_analyticOn
  exact hf.contDiffOn.contDiffAt hs

end fderiv

section deriv

variable {p : FormalMultilinearSeries 𝕜 𝕜 F} {r : ℝ≥0∞}
variable {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}

protected theorem HasFPowerSeriesAt.hasStrictDerivAt (h : HasFPowerSeriesAt f p x) :
    HasStrictDerivAt f (p 1 fun _ => 1) x :=
  h.hasStrictFDerivAt.hasStrictDerivAt
#align has_fpower_series_at.has_strict_deriv_at HasFPowerSeriesAt.hasStrictDerivAt

protected theorem HasFPowerSeriesAt.hasDerivAt (h : HasFPowerSeriesAt f p x) :
    HasDerivAt f (p 1 fun _ => 1) x :=
  h.hasStrictDerivAt.hasDerivAt
#align has_fpower_series_at.has_deriv_at HasFPowerSeriesAt.hasDerivAt

protected theorem HasFPowerSeriesAt.deriv (h : HasFPowerSeriesAt f p x) :
    deriv f x = p 1 fun _ => 1 :=
  h.hasDerivAt.deriv
#align has_fpower_series_at.deriv HasFPowerSeriesAt.deriv

/-- If a function is analytic on a set `s`, so is its derivative. -/
theorem AnalyticOn.deriv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (deriv f) s :=
  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_analyticOn h.fderiv
#align analytic_on.deriv AnalyticOn.deriv

/-- If a function is analytic on a set `s`, so are its successive derivatives. -/
theorem AnalyticOn.iterated_deriv [CompleteSpace F] (h : AnalyticOn 𝕜 f s) (n : ℕ) :
    AnalyticOn 𝕜 (_root_.deriv^[n] f) s := by
  induction' n with n IH
  · exact h
  · simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv
#align analytic_on.iterated_deriv AnalyticOn.iterated_deriv

end deriv
section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞} {n : ℕ}
variable {f : E → F} {x : E} {s : Set E}

/-! The case of continuously polynomial functions. We get the same differentiability
results as for analytic functions, but without the assumptions that `F` is complete. -/

theorem HasFiniteFPowerSeriesOnBall.differentiableOn
    (h : HasFiniteFPowerSeriesOnBall f p x n r) : DifferentiableOn 𝕜 f (EMetric.ball x r) :=
  fun _ hy ↦ (h.cPolynomialAt_of_mem hy).analyticAt.differentiableWithinAt

theorem HasFiniteFPowerSeriesOnBall.hasFDerivAt (h : HasFiniteFPowerSeriesOnBall f p x n r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1)) (x + y) :=
  (h.changeOrigin hy).toHasFPowerSeriesOnBall.hasFPowerSeriesAt.hasFDerivAt

theorem HasFiniteFPowerSeriesOnBall.fderiv_eq (h : HasFiniteFPowerSeriesOnBall f p x n r)
    {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
    fderiv 𝕜 f (x + y) = continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin y 1) :=
  (h.hasFDerivAt hy).fderiv

/-- If a function has a finite power series on a ball, then so does its derivative. -/
protected theorem HasFiniteFPowerSeriesOnBall.fderiv
    (h : HasFiniteFPowerSeriesOnBall f p x (n + 1) r) :
    HasFiniteFPowerSeriesOnBall (fderiv 𝕜 f) p.derivSeries x n r := by
  refine .congr (f := fun z ↦ continuousMultilinearCurryFin1 𝕜 E F (p.changeOrigin (z - x) 1)) ?_
    fun z hz ↦ ?_
  · refine continuousMultilinearCurryFin1 𝕜 E F
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall ?_
    simpa using
      ((p.hasFiniteFPowerSeriesOnBall_changeOrigin 1 h.finite).mono h.r_pos le_top).comp_sub x
  dsimp only
  rw [← h.fderiv_eq, add_sub_cancel]
  simpa only [edist_eq_coe_nnnorm_sub, EMetric.mem_ball] using hz

/-- If a function has a finite power series on a ball, then so does its derivative.
This is a variant of `HasFiniteFPowerSeriesOnBall.fderiv` where the degree of `f` is `< n`
and not `< n + 1`. -/
theorem HasFiniteFPowerSeriesOnBall.fderiv' (h : HasFiniteFPowerSeriesOnBall f p x n r) :
    HasFiniteFPowerSeriesOnBall (fderiv 𝕜 f) p.derivSeries x (n - 1) r := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [zero_tsub]
    refine HasFiniteFPowerSeriesOnBall.bound_zero_of_eq_zero (fun y hy ↦ ?_) h.r_pos fun n ↦ ?_
    · rw [Filter.EventuallyEq.fderiv_eq (f := fun _ ↦ 0)]
      · rw [fderiv_const, Pi.zero_apply]
      · exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨EMetric.ball x r,
          EMetric.isOpen_ball.mem_nhds hy, fun z hz ↦ by rw [h.eq_zero_of_bound_zero z hz]⟩
    · apply ContinuousMultilinearMap.ext; intro a
      change (continuousMultilinearCurryFin1 𝕜 E F) (p.changeOriginSeries 1 n a) = 0
      rw [p.changeOriginSeries_finite_of_finite h.finite 1 (Nat.zero_le _)]
      exact map_zero _
  · rw [← Nat.succ_pred hn] at h
    exact h.fderiv

/-- If a function is polynomial on a set `s`, so is its Fréchet derivative. -/
theorem CPolynomialOn.fderiv (h : CPolynomialOn 𝕜 f s) :
    CPolynomialOn 𝕜 (fderiv 𝕜 f) s := by
  intro y hy
  rcases h y hy with ⟨p, r, n, hp⟩
  exact hp.fderiv'.cPolynomialAt

/-- If a function is polynomial on a set `s`, so are its successive Fréchet derivative. -/
theorem CPolynomialOn.iteratedFDeriv (h : CPolynomialOn 𝕜 f s) (n : ℕ) :
    CPolynomialOn 𝕜 (iteratedFDeriv 𝕜 n f) s := by
  induction' n with n IH
  · rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E[×0]→L[𝕜] F).comp_cPolynomialOn h
  · rw [iteratedFDeriv_succ_eq_comp_left]
    convert ContinuousLinearMap.comp_cPolynomialOn ?g IH.fderiv
    case g => exact ↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) F)
    simp

/-- A polynomial function is infinitely differentiable. -/
theorem CPolynomialOn.contDiffOn (h : CPolynomialOn 𝕜 f s) {n : ℕ∞} :
    ContDiffOn 𝕜 n f s :=
  let t := { x | CPolynomialAt 𝕜 f x }
  suffices ContDiffOn 𝕜 n f t from this.mono h
  have H : CPolynomialOn 𝕜 f t := fun _x hx ↦ hx
  have t_open : IsOpen t := isOpen_cPolynomialAt 𝕜 f
  contDiffOn_of_continuousOn_differentiableOn
    (fun m _ ↦ (H.iteratedFDeriv m).continuousOn.congr
      fun  _ hx ↦ iteratedFDerivWithin_of_isOpen _ t_open hx)
    (fun m _ ↦ (H.iteratedFDeriv m).analyticOn.differentiableOn.congr
      fun _ hx ↦ iteratedFDerivWithin_of_isOpen _ t_open hx)

theorem CPolynomialAt.contDiffAt (h : CPolynomialAt 𝕜 f x) {n : ℕ∞} :
    ContDiffAt 𝕜 n f x :=
  let ⟨_, hs, hf⟩ := h.exists_mem_nhds_cPolynomialOn
  hf.contDiffOn.contDiffAt hs

end fderiv

section deriv

variable {p : FormalMultilinearSeries 𝕜 𝕜 F} {r : ℝ≥0∞}
variable {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}

/-- If a function is polynomial on a set `s`, so is its derivative. -/
protected theorem CPolynomialOn.deriv (h : CPolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 (deriv f) s :=
  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_cPolynomialOn h.fderiv

/-- If a function is polynomial on a set `s`, so are its successive derivatives. -/
theorem CPolynomialOn.iterated_deriv (h : CPolynomialOn 𝕜 f s) (n : ℕ) :
    CPolynomialOn 𝕜 (deriv^[n] f) s := by
  induction' n with n IH
  · exact h
  · simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv

end deriv

namespace ContinuousMultilinearMap

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 E F)

open FormalMultilinearSeries

protected theorem hasFiniteFPowerSeriesOnBall :
    HasFiniteFPowerSeriesOnBall f f.toFormalMultilinearSeries 0 (Fintype.card ι + 1) ⊤ :=
  .mk' (fun m hm ↦ dif_neg (Nat.succ_le_iff.mp hm).ne) ENNReal.zero_lt_top fun y _ ↦ by
    rw [Finset.sum_eq_single_of_mem _ (Finset.self_mem_range_succ _), zero_add]
    · rw [toFormalMultilinearSeries, dif_pos rfl]; rfl
    · intro m _ ne; rw [toFormalMultilinearSeries, dif_neg ne.symm]; rfl

theorem changeOriginSeries_support {k l : ℕ} (h : k + l ≠ Fintype.card ι) :
    f.toFormalMultilinearSeries.changeOriginSeries k l = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ by
    simp_rw [FormalMultilinearSeries.changeOriginSeriesTerm,
      toFormalMultilinearSeries, dif_neg h.symm, LinearIsometryEquiv.map_zero]

variable {n : ℕ∞} (x : ∀ i, E i)

open Finset in
theorem changeOrigin_toFormalMultilinearSeries [DecidableEq ι] :
    continuousMultilinearCurryFin1 𝕜 (∀ i, E i) F (f.toFormalMultilinearSeries.changeOrigin x 1) =
    f.linearDeriv x := by
  ext y
  rw [continuousMultilinearCurryFin1_apply, linearDeriv_apply,
      changeOrigin, FormalMultilinearSeries.sum]
  cases isEmpty_or_nonempty ι
  · have (l) : 1 + l ≠ Fintype.card ι := by
      rw [add_comm, Fintype.card_eq_zero]; exact Nat.succ_ne_zero _
    simp_rw [Fintype.sum_empty, changeOriginSeries_support _ (this _), zero_apply _, tsum_zero]; rfl
  rw [tsum_eq_single (Fintype.card ι - 1), changeOriginSeries]; swap
  · intro m hm
    rw [Ne, eq_tsub_iff_add_eq_of_le (by exact Fintype.card_pos), add_comm] at hm
    rw [f.changeOriginSeries_support hm, zero_apply]
  rw [sum_apply, ContinuousMultilinearMap.sum_apply, Fin.snoc_zero]
  simp_rw [changeOriginSeriesTerm_apply]
  refine (Fintype.sum_bijective (?_ ∘ Fintype.equivFinOfCardEq (Nat.add_sub_of_le
    Fintype.card_pos).symm) (.comp ?_ <| Equiv.bijective _) _ _ fun i ↦ ?_).symm
  · exact (⟨{·}ᶜ, by
      rw [card_compl, Fintype.card_fin, card_singleton, Nat.add_sub_cancel_left]⟩)
  · use fun _ _ ↦ (singleton_injective <| compl_injective <| Subtype.ext_iff.mp ·)
    intro ⟨s, hs⟩
    have h : sᶜ.card = 1 := by rw [card_compl, hs, Fintype.card_fin, Nat.add_sub_cancel]
    obtain ⟨a, ha⟩ := card_eq_one.mp h
    exact ⟨a, Subtype.ext (compl_eq_comm.mp ha)⟩
  rw [Function.comp_apply, Subtype.coe_mk, compl_singleton, piecewise_erase_univ,
    toFormalMultilinearSeries, dif_pos (Nat.add_sub_of_le Fintype.card_pos).symm]
  simp_rw [domDomCongr_apply, compContinuousLinearMap_apply, ContinuousLinearMap.proj_apply,
    Function.update_apply, (Equiv.injective _).eq_iff, ite_apply]
  congr; ext j
  obtain rfl | hj := eq_or_ne j i
  · rw [Function.update_same, if_pos rfl]
  · rw [Function.update_noteq hj, if_neg hj]

protected theorem hasFDerivAt [DecidableEq ι] : HasFDerivAt f (f.linearDeriv x) x := by
  rw [← changeOrigin_toFormalMultilinearSeries]
  convert f.hasFiniteFPowerSeriesOnBall.hasFDerivAt (y := x) ENNReal.coe_lt_top
  rw [zero_add]

lemma foo (n : ℕ) : 0 ≤ n := by exact?

#check HasFDerivAt.sum

open scoped BigOperators
open Finset (univ)

#check Function.Embedding.toEquivRange

/-
open Classical
noncomputable def boo_to (n : ℕ) :
    (Finset.sigma ((univ : Finset ι).powersetCard n.succ)
        (fun (s : Finset ι) ↦ (univ : Finset (Fin n.succ ≃ s))))
    → Finset.sigma ((univ : Finset ι).powersetCard n)
       (fun (s : Finset ι) ↦ (univ : Finset ((Fin n ≃ s) × {i // i ∉ s}))) := by
  rintro ⟨⟨s, f⟩, p⟩
  let e_emb : Fin n ↪ ι :=
    Fin.castSuccEmb.toEmbedding.trans (f.toEmbedding.trans (Function.Embedding.subtype _))
  let t := (Set.range e_emb).toFinset
  let e : Fin n ≃ t := by
    convert e_emb.toEquivRange
    simp [t]
    rfl
  have : t.card = n := Finset.card_eq_of_equiv_fin e.symm
  have : (f n : ι) ∉ t := by
    simp only [Fin.cast_nat_eq_last, Set.toFinset_range, Fin.castSuccEmb_toEmbedding, mem_image,
      mem_univ, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
      Equiv.coe_toEmbedding, Function.Embedding.coe_subtype, true_and, not_exists, t, e_emb]
    intro j
    exact Subtype.val_injective.ne (f.injective.ne (Fin.castSucc_lt_last j).ne)
  exact ⟨⟨t, ⟨e, ⟨f n, this⟩⟩⟩, by simpa using card_eq_of_equiv_fin e.symm⟩

noncomputable def boo_inv (n : ℕ) :
    (Finset.sigma ((univ : Finset ι).powersetCard n)
       (fun (s : Finset ι) ↦ (univ : Finset ((Fin n ≃ s) × {i // i ∉ s}))))
    → Finset.sigma ((univ : Finset ι).powersetCard n.succ)
        (fun (s : Finset ι) ↦ (univ : Finset (Fin n.succ ≃ s))) := by
  rintro ⟨⟨s, ⟨e, i⟩⟩, p⟩
  let f0 : Fin (n+1) → ι := fun k ↦ if hk : k.1 < n then e ⟨k.1, hk⟩ else i
  have f_inj : Function.Injective f0 := by
    intro k l hkl
    by_cases hk : k.1 < n <;> by_cases hl : l.1 < n <;>
      simp only [hk, ↓reduceDite, hl, f0] at hkl
    · apply Fin.eq_of_val_eq
      simpa using e.injective (Subtype.val_injective hkl)
    · have : (i : ι) ∈ s := by rw [← hkl]; exact coe_mem _
      exact (i.2 this).elim
    · have : (i : ι) ∈ s := by rw [hkl]; exact coe_mem _
      exact (i.2 this).elim
    · omega
  let f_emb : Fin (n + 1) ↪ ι := ⟨f0, f_inj⟩
  let t := (Set.range f_emb).toFinset
  let f : Fin (n + 1) ≃ t := by
    convert f_emb.toEquivRange
    simp [t]
    rfl
  have : t.card = n + 1 := card_eq_of_equiv_fin f.symm
  refine ⟨⟨t, f⟩, ?_⟩
  simpa only [mem_sigma, mem_powersetCard, subset_univ, true_and, mem_univ, and_true] using
    card_eq_of_equiv_fin f.symm

lemma blou {s : Type*} [Fintype s] (n : ℕ) (hs : Fintype.card s = n) :
    Fintype.card (Fin n ≃ s) = n.factorial := by
  conv_rhs => rw [← Fintype.card_fin n]
  apply Fintype.card_equiv
  exact (Fintype.equivFinOfCardEq hs).symm

lemma zou {α : Type*} [Fintype α] : (univ : Finset α).card = Fintype.card α := by exact?
-/

variable [DecidableEq ι]

def piou_to (n : ℕ) : (Fin (n+1) ↪ ι) → (Finset.sigma (univ : Finset (Fin n ↪ ι))
      (fun (e : Fin n ↪ ι) ↦ (univ : Finset {a_1 // a_1 ∉ Set.range e}))) :=
  fun e ↦ ⟨⟨(Fin.succEmb n).toEmbedding.trans e, ⟨e 0, by simp⟩⟩, by simp⟩

def piou_inv (n : ℕ) : (Finset.sigma (univ : Finset (Fin n ↪ ι))
    (fun (e : Fin n ↪ ι) ↦ (univ : Finset {a_1 // a_1 ∉ Set.range e}))) → (Fin (n+1) ↪ ι) := by
  rintro ⟨⟨f, ⟨i, hi⟩⟩, hfi⟩
  refine ⟨fun j ↦ if h : j = 0 then i else f (Fin.pred j h), ?_⟩
  simp only [Set.mem_range, not_exists] at hi
  intro k l hkl
  by_cases hk : k = 0 <;> by_cases hl : l = 0 <;> simp only [hk, ↓reduceDite, hl] at hkl
  · omega
  · exact (hi _ hkl.symm).elim
  · exact (hi _ hkl).elim
  · simpa using f.injective hkl

def piou (n : ℕ) : (Fin (n+1) ↪ ι) ≃ (Finset.sigma (univ : Finset (Fin n ↪ ι))
    (fun (e : Fin n ↪ ι) ↦ (univ : Finset {a_1 // a_1 ∉ Set.range e}))) where
  toFun := piou_to n
  invFun := piou_inv n
  left_inv := by
    intro e
    simp only [piou_to, piou_inv, Fin.castSuccEmb_toEmbedding, Function.Embedding.trans_apply,
      Function.Embedding.coeFn_mk, Fin.castSucc_mk, Fin.eta, Fin.cast_nat_eq_last, dite_eq_ite]
    ext j
    by_cases hj : j = 0
    · simp [hj]
    · simp [hj]
  right_inv := by
    rintro ⟨⟨f, ⟨i, hi⟩⟩, hfi⟩
    simp only [Finset.univ_sigma_univ, piou_to, piou_inv, Function.Embedding.coeFn_mk, ↓reduceDite,
      Subtype.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, and_true]
    ext j
    simp [Fin.succ_ne_zero]

@[simp] lemma piou_symm_apply {n : ℕ} (p : Finset.sigma (univ : Finset (Fin n ↪ ι))
    (fun (e : Fin n ↪ ι) ↦ (univ : Finset {a_1 // a_1 ∉ Set.range e}))) (k : Fin (n + 1)) :
    (piou n).symm p k = if h : k = 0 then p.1.2.1 else p.1.1 (Fin.pred k h) := rfl

lemma range_piou_symm {n : ℕ} (p : Finset.sigma (univ : Finset (Fin n ↪ ι))
    (fun (e : Fin n ↪ ι) ↦ (univ : Finset {a_1 // a_1 ∉ Set.range e}))) :
    Set.range ((piou n).symm p) = Set.range p.1.1 ∪ {p.1.2.1} := by
  apply subset_antisymm
  · rintro - ⟨i, rfl⟩
    rw [piou_symm_apply]
    split <;> simp
  · apply Set.union_subset
    · rintro - ⟨i, rfl⟩
      simp only [Finset.univ_sigma_univ, Set.mem_range]
      exact ⟨Fin.succ i, rfl⟩
    · simp only [Finset.univ_sigma_univ, Set.singleton_subset_iff, Set.mem_range]
      exact ⟨0, rfl⟩

@[simp] lemma range_image_piou {n : ℕ} (e : Fin (n+1) ↪ ι) :
    Set.range (piou n e).1.1 = e '' (Set.Ici 1) := sorry

#check Fin.cons

theorem glou : HasFTaylorSeriesUpTo ⊤ f (fun v n ↦ f.iteratedFDeriv n v) := by
  constructor
  · sorry /-intro y
    simp only [iteratedFDeriv, Finset.powersetCard_zero, iteratedFDerivComponent,
      MultilinearMap.iteratedFDerivComponent, MultilinearMap.domDomRestrictₗ, MultilinearMap.coe_mk,
      MultilinearMap.domDomRestrict_apply, coe_coe, Finset.sum_singleton,
      Fintype.univ_ofSubsingleton, Fintype.card_ofIsEmpty, List.finRange_zero, List.length_nil,
      Finset.empty_val, Equiv.symm_symm,
      Function.Embedding.coeFn_mk, Equiv.equivCongr_refl_left, Equiv.Perm.one_trans,
      Finset.not_mem_empty, ↓reduceDite, uncurry0_apply, Matrix.zero_empty,
      MultilinearMap.mkContinuousMultilinear_apply] -/
  · intro n hn x
    suffices H : curryLeft (iteratedFDeriv f (Nat.succ n) x) = (∑ e : Fin n ↪ ι,
          ((iteratedFDerivComponent f e.toEquivRange).linearDeriv (glouk 𝕜 _ x)) ∘L (glouk 𝕜 _)) by
      sorry /-have A : HasFDerivAt (iteratedFDeriv f n) (∑ e : Fin n ↪ ι,
          ((iteratedFDerivComponent f e.toEquivRange).linearDeriv (glouk 𝕜 _ x))
            ∘L (glouk 𝕜 _)) x := by
        apply HasFDerivAt.sum (fun s hs ↦ ?_)
        exact (ContinuousMultilinearMap.hasFDerivAt _ _).comp x (ContinuousLinearMap.hasFDerivAt _)
      rwa [← H] at A -/
    ext v m
    simp only [curryLeft_apply, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp',
      Finset.sum_apply, Function.comp_apply, linearDeriv_apply, sum_apply]
    simp only [iteratedFDeriv, iteratedFDerivComponent, MultilinearMap.iteratedFDerivComponent,
      MultilinearMap.domDomRestrictₗ, MultilinearMap.coe_mk, MultilinearMap.domDomRestrict_apply,
      coe_coe, MultilinearMap.mkContinuousMultilinear_apply, sum_apply, Finset.sum_sigma',
      MultilinearMap.mkContinuousMultilinear_apply, MultilinearMap.coe_mk]
    conv_rhs => rw [← Finset.sum_coe_sort, ← (piou n).sum_comp]
    congr with e
    congr with k
    dsimp
    by_cases hk : k ∈ Set.range (piou n e).1.1
    · have hk' : k ∈ Set.range e := sorry
      rw [dite_cond_eq_true, dite_cond_eq_true]; rotate_left
      · simpa using hk
      · simpa using hk'






#exit

    rw [← (piou n).symm.sum_comp]
    conv_rhs => rw [← Finset.sum_coe_sort]
    congr with enj
    simp_rw [range_piou_symm]
    let f := (piou n).symm enj
    --rcases enj with ⟨⟨e, ⟨j, hj⟩⟩, -⟩
    congr with k
    dsimp only [Finset.univ_sigma_univ]
    by_cases hk : k ∈ Set.range enj.1.1
    · simp only [Set.union_singleton, Set.mem_insert_iff, hk, or_true, ↓reduceDite]





  · sorry /-intro n hn
    apply continuous_finset_sum _ (fun s hs ↦ ?_)
    apply continuous_finset_sum _ (fun e he ↦ ?_)
    exact (ContinuousMultilinearMap.coe_continuous _).comp (ContinuousLinearMap.continuous _) -/

#exit

lemma cPolynomialAt : CPolynomialAt 𝕜 f x :=
  f.hasFiniteFPowerSeriesOnBall.cPolynomialAt_of_mem
    (by simp only [Metric.emetric_ball_top, Set.mem_univ])

lemma cPolyomialOn : CPolynomialOn 𝕜 f ⊤ := fun x _ ↦ f.cPolynomialAt x

lemma contDiffAt : ContDiffAt 𝕜 n f x := (f.cPolynomialAt x).contDiffAt

lemma contDiff : ContDiff 𝕜 n f := contDiff_iff_contDiffAt.mpr f.contDiffAt

end ContinuousMultilinearMap

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F)

open Fintype ContinuousLinearMap in
theorem derivSeries_apply_diag (n : ℕ) (x : E) :
    derivSeries p n (fun _ ↦ x) x = (n + 1) • p (n + 1) fun _ ↦ x := by
  simp only [derivSeries, compFormalMultilinearSeries_apply, changeOriginSeries,
    compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe,
    Function.comp_apply, ContinuousMultilinearMap.sum_apply, map_sum, coe_sum', Finset.sum_apply,
    continuousMultilinearCurryFin1_apply, Matrix.zero_empty]
  convert Finset.sum_const _
  · rw [Fin.snoc_zero, changeOriginSeriesTerm_apply, Finset.piecewise_same, add_comm]
  · rw [← card, card_subtype, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter,
      Finset.card_powersetCard, ← card, card_fin, eq_comm, add_comm, Nat.choose_succ_self_right]

end FormalMultilinearSeries

namespace HasFPowerSeriesOnBall

open FormalMultilinearSeries ENNReal Nat

variable {p : FormalMultilinearSeries 𝕜 E F} {f : E → F} {x : E} {r : ℝ≥0∞}
  (h : HasFPowerSeriesOnBall f p x r) (y : E)

theorem iteratedFDeriv_zero_apply_diag : iteratedFDeriv 𝕜 0 f x = p 0 := by
  ext
  convert (h.hasSum <| EMetric.mem_ball_self h.r_pos).tsum_eq.symm
  · rw [iteratedFDeriv_zero_apply, add_zero]
  · rw [tsum_eq_single 0 fun n hn ↦ by haveI := NeZero.mk hn; exact (p n).map_zero]
    exact congr(p 0 $(Subsingleton.elim _ _))

open ContinuousLinearMap

private theorem factorial_smul' {n : ℕ} : ∀ {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] {p : FormalMultilinearSeries 𝕜 E F}
    {f : E → F}, HasFPowerSeriesOnBall f p x r →
    n ! • p n (fun _ ↦ y) = iteratedFDeriv 𝕜 n f x (fun _ ↦ y) := by
  induction' n with n ih <;> intro F _ _ _ p f h
  · rw [factorial_zero, one_smul, h.iteratedFDeriv_zero_apply_diag]
  · rw [factorial_succ, mul_comm, mul_smul, ← derivSeries_apply_diag, ← smul_apply,
      ih h.fderiv, iteratedFDeriv_succ_apply_right]
    rfl

variable [CompleteSpace F]

theorem factorial_smul (n : ℕ) :
    n ! • p n (fun _ ↦ y) = iteratedFDeriv 𝕜 n f x (fun _ ↦ y) := by
  cases n
  · rw [factorial_zero, one_smul, h.iteratedFDeriv_zero_apply_diag]
  · rw [factorial_succ, mul_comm, mul_smul, ← derivSeries_apply_diag, ← smul_apply,
      factorial_smul'.{_,u,v} _ h.fderiv, iteratedFDeriv_succ_apply_right]
    rfl

theorem hasSum_iteratedFDeriv [CharZero 𝕜] {y : E} (hy : y ∈ EMetric.ball 0 r) :
    HasSum (fun n ↦ (n ! : 𝕜)⁻¹ • iteratedFDeriv 𝕜 n f x fun _ ↦ y) (f (x + y)) := by
  convert h.hasSum hy with n
  rw [← h.factorial_smul y n, smul_comm, ← smul_assoc, nsmul_eq_mul,
    mul_inv_cancel <| cast_ne_zero.mpr n.factorial_ne_zero, one_smul]

end HasFPowerSeriesOnBall
