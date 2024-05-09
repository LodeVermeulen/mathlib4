/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-!
# ZeroTopSet

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open scoped NNReal ENNReal Topology

open Filter

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {s t : Set α}

namespace Measure

lemma ae_lt_top_of_sigmaFinite [SigmaFinite μ] {f : α → ℝ≥0∞} (hf : Measurable f)
    (h2f : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ :=
  ae_of_forall_measure_lt_top_ae_restrict _ (fun s hs hμs ↦ ae_lt_top hf (h2f s hs hμs))

instance [SigmaFinite (μ.restrict s)] [SigmaFinite (μ.restrict t)] :
    SigmaFinite (μ.restrict (s ∪ t)) := sigmaFinite_of_le _ (restrict_union_le _ _)

lemma measure_eq_iSup_measure_subset [SigmaFinite μ] (hs : MeasurableSet s) :
    μ s = ⨆ (t : Set α) (_ht : MeasurableSet t) (_hμt : μ t ≠ ∞) (_hts : t ⊆ s), μ t := by
  refine le_antisymm ?_ ?_
  · rw [← iSup_restrict_spanningSets]
    simp only [ne_eq, iSup_le_iff]
    intro i
    rw [restrict_apply' (measurable_spanningSets _ _)]
    refine le_trans ?_ (le_iSup _ (s ∩ spanningSets μ i))
    simp only [hs.inter (measurable_spanningSets _ _),
      ((measure_mono (Set.inter_subset_right s _)).trans_lt (measure_spanningSets_lt_top μ _)).ne,
      not_false_eq_true, Set.inter_subset_left, iSup_pos, le_refl]
  · simp only [ne_eq, iSup_le_iff]
    exact fun _ _ _ hts ↦ measure_mono hts

/-! ### Method of exhaustion

If `μ, ν` are two measures with `ν` finite, then there exists a set `s` such that
`μ` is sigma-finite on `s`, and for all sets `t ⊆ sᶜ`, either `ν t = 0` or `μ t = ∞`. -/

lemma exists_isSigmaFiniteSet_measure_ge (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) :
    ∃ t, MeasurableSet t ∧ SigmaFinite (μ.restrict t)
      ∧ (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1/n ≤ ν t := by
  by_cases hC_lt : 1/n < ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s
  · have h_lt_top : ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s < ∞ := by
      refine (?_ : ⨆ (s) (_ : MeasurableSet s)
        (_ : SigmaFinite (μ.restrict s)), ν s ≤ ν Set.univ).trans_lt (measure_lt_top _ _)
      refine iSup_le (fun s ↦ ?_)
      exact iSup_le (fun _ ↦ iSup_le (fun _ ↦ measure_mono (Set.subset_univ s)))
    obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup
      (ENNReal.sub_lt_self h_lt_top.ne (ne_zero_of_lt hC_lt) (by simp) :
          (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1/n
        < ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)
    have ht_meas : MeasurableSet t := by
      by_contra h_not_mem
      simp only [h_not_mem] at ht
      simp at ht
    have ht_mem : SigmaFinite (μ.restrict t) := by
      by_contra h_not_mem
      simp only [h_not_mem] at ht
      simp at ht
    refine ⟨t, ht_meas, ht_mem, ?_⟩
    simp only [ht_meas, ht_mem, iSup_true] at ht
    exact ht.le
  · refine ⟨∅, MeasurableSet.empty, by rw [restrict_empty]; infer_instance, ?_⟩
    rw [tsub_eq_zero_of_le (not_lt.mp hC_lt)]
    exact zero_le'

def sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) : Set α :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose

lemma measurableSet_sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) :
    MeasurableSet (sigmaFiniteSetGE μ ν n) :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.1

instance isSigmaFiniteSet_sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) :
    SigmaFinite (μ.restrict (sigmaFiniteSetGE μ ν n)) :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.2.1

lemma measure_sigmaFiniteSetGE_le (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) :
    ν (sigmaFiniteSetGE μ ν n)
      ≤ ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s := by
  refine (le_iSup (f := fun s ↦ _) (isSigmaFiniteSet_sigmaFiniteSetGE μ ν n)).trans ?_
  exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : SigmaFinite (μ.restrict s)), ν s) (sigmaFiniteSetGE μ ν n)
    (measurableSet_sigmaFiniteSetGE μ ν n)

lemma measure_sigmaFiniteSetGE_ge (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) :
    (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1/n
      ≤ ν (sigmaFiniteSetGE μ ν n) :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.2.2

lemma tendsto_measure_sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] :
    Tendsto (fun n ↦ ν (sigmaFiniteSetGE μ ν n)) atTop
      (𝓝 (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_
    tendsto_const_nhds (measure_sigmaFiniteSetGE_ge μ ν) (measure_sigmaFiniteSetGE_le μ ν)
  nth_rewrite 2 [← tsub_zero (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)]
  refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (Or.inr ENNReal.zero_ne_top)
  simp only [one_div]
  exact ENNReal.tendsto_inv_nat_nhds_zero

def sigmaFiniteSetWRT (μ ν : Measure α) [IsFiniteMeasure ν] : Set α := ⋃ n, sigmaFiniteSetGE μ ν n

lemma measurableSet_sigmaFiniteSetWRT (μ ν : Measure α) [IsFiniteMeasure ν] :
    MeasurableSet (sigmaFiniteSetWRT μ ν) :=
  MeasurableSet.iUnion (measurableSet_sigmaFiniteSetGE _ _)

instance isSigmaFiniteSet_sigmaFiniteSetWRT (μ ν : Measure α) [IsFiniteMeasure ν] :
    SigmaFinite (μ.restrict (sigmaFiniteSetWRT μ ν)) := by
  let f : ℕ × ℕ → Set α := fun p : ℕ × ℕ ↦ (sigmaFiniteSetWRT μ ν)ᶜ
    ∪ (spanningSets (μ.restrict (sigmaFiniteSetGE μ ν p.1)) p.2 ∩ (sigmaFiniteSetGE μ ν p.1))
  suffices (μ.restrict (sigmaFiniteSetWRT μ ν)).FiniteSpanningSetsIn (Set.range f) from
    this.sigmaFinite
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  refine ⟨fun n ↦ f (e n), fun _ ↦ by simp, fun n ↦ ?_, ?_⟩
  · simp only [Nat.pairEquiv_symm_apply, gt_iff_lt, measure_union_lt_top_iff, f, e]
    rw [restrict_apply' (measurableSet_sigmaFiniteSetWRT _ _), Set.compl_inter_self,
      restrict_apply' (measurableSet_sigmaFiniteSetWRT _ _)]
    simp only [measure_empty, ENNReal.zero_lt_top, true_and]
    refine (measure_mono (Set.inter_subset_left _ _)).trans_lt ?_
    rw [← restrict_apply' (measurableSet_sigmaFiniteSetGE μ ν _)]
    exact measure_spanningSets_lt_top _ _
  · simp only [Nat.pairEquiv_symm_apply, f, e]
    rw [← Set.union_iUnion]
    suffices ⋃ n, (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν (Nat.unpair n).1)) n.unpair.2
        ∩ μ.sigmaFiniteSetGE ν n.unpair.1) = sigmaFiniteSetWRT μ ν by
      rw [this, Set.compl_union_self]
    calc ⋃ n, (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν (Nat.unpair n).1)) n.unpair.2
        ∩ μ.sigmaFiniteSetGE ν n.unpair.1)
      = ⋃ n, ⋃ m, (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν n)) m
            ∩ μ.sigmaFiniteSetGE ν n) :=
          Set.iUnion_unpair (fun n m ↦ spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν n)) m
            ∩ μ.sigmaFiniteSetGE ν n)
    _ = ⋃ n, sigmaFiniteSetGE μ ν n := by
        refine Set.iUnion_congr (fun n ↦ ?_)
        rw [← Set.iUnion_inter, iUnion_spanningSets, Set.univ_inter]
    _ = sigmaFiniteSetWRT μ ν := rfl

lemma measure_sigmaFiniteSetWRT (μ ν : Measure α) [IsFiniteMeasure ν] :
    ν (sigmaFiniteSetWRT μ ν)
      = ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s := by
  apply le_antisymm
  · refine (le_iSup (f := fun _ ↦ _) (isSigmaFiniteSet_sigmaFiniteSetWRT μ ν)).trans ?_
    exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : SigmaFinite (μ.restrict s)), ν s) (sigmaFiniteSetWRT μ ν)
      (measurableSet_sigmaFiniteSetWRT μ ν)
  · exact le_of_tendsto' (tendsto_measure_sigmaFiniteSetGE μ ν)
      (fun _ ↦ measure_mono (Set.subset_iUnion _ _))

lemma measure_eq_top_of_subset_compl_sigmaFiniteSetWRT [IsFiniteMeasure ν]
    (hs : MeasurableSet s) (hs_subset_compl : s ⊆ (sigmaFiniteSetWRT μ ν)ᶜ) (hμs : ν s ≠ 0) :
    μ s = ∞ := by
  suffices ¬ SigmaFinite (μ.restrict s) by
    by_contra h
    have h_lt_top : Fact (μ s < ∞) := ⟨Ne.lt_top h⟩
    exact this inferInstance
  intro hsσ
  have h_lt : ν (sigmaFiniteSetWRT μ ν) < ν (sigmaFiniteSetWRT μ ν ∪ s) := by
    rw [measure_union _ hs]
    · exact ENNReal.lt_add_right (measure_ne_top _ _) hμs
    · exact disjoint_compl_right.mono_right hs_subset_compl
  have h_le : ν (sigmaFiniteSetWRT μ ν ∪ s) ≤ ν (sigmaFiniteSetWRT μ ν) := by
    conv_rhs => rw [measure_sigmaFiniteSetWRT]
    refine (le_iSup (f := fun (_ : SigmaFinite (μ.restrict (sigmaFiniteSetWRT μ ν ∪ s))) ↦ _) ?_).trans ?_
    · infer_instance
    · exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : SigmaFinite (μ.restrict _)), ν s) (sigmaFiniteSetWRT μ ν ∪ s)
        ((measurableSet_sigmaFiniteSetWRT μ ν).union hs)
  exact h_lt.not_le h_le

lemma sFinite_of_absolutelyContinuous_aux [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h : ∀ s, MeasurableSet s → ν s ≠ 0 → μ s = ∞) :
    SFinite μ := by
  suffices μ = ν.withDensity (fun _ ↦ ∞) by
    rw [this]
    exact sFinite_withDensity_of_measurable _ measurable_const
  ext s hs
  simp only [withDensity_const, Measure.smul_apply, smul_eq_mul]
  by_cases hνs : ν s = 0
  · simp [hνs, hμν hνs]
  · simp [h s hs hνs, hνs]

lemma sFinite_of_absolutelyContinuous_of_isFiniteMeasure [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    SFinite μ := by
  let s := sigmaFiniteSetWRT μ ν
  have hs : MeasurableSet s := measurableSet_sigmaFiniteSetWRT μ ν
  rw [← restrict_add_restrict_compl (μ := μ) hs]
  have : SFinite (μ.restrict sᶜ) := by
    refine sFinite_of_absolutelyContinuous_aux (hμν.restrict sᶜ) (fun t ht hνt ↦ ?_)
    rw [restrict_apply ht] at hνt ⊢
    refine measure_eq_top_of_subset_compl_sigmaFiniteSetWRT (ht.inter hs.compl) ?_ hνt
    exact Set.inter_subset_right _ _
  infer_instance

lemma sFinite_of_absolutelyContinuous [SFinite ν] (hμν : μ ≪ ν) : SFinite μ :=
  sFinite_of_absolutelyContinuous_of_isFiniteMeasure (hμν.trans (absolutelyContinuous_toFinite ν))

instance [SFinite μ] (f : α → ENNReal) : SFinite (μ.withDensity f) :=
  sFinite_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _)

/-! ### IsZeroTopSet -/

def IsZeroTopSet (s : Set α) (μ : Measure α) : Prop :=
  ∀ t, MeasurableSet t → t ⊆ s → μ t = 0 ∨ μ t = ∞

lemma isZeroTopSet_of_null (hs_zero : μ s = 0) : IsZeroTopSet s μ :=
  fun _ _ ht_subset ↦ Or.inl <| measure_mono_null ht_subset hs_zero

lemma measure_isZeroTopSet (hs0 : IsZeroTopSet s μ) (hs : MeasurableSet s) : μ s = 0 ∨ μ s = ⊤ :=
  hs0 s hs subset_rfl

lemma iSup_measure_subset_eq_zero_of_isZeroTopSet (hs : IsZeroTopSet s μ) :
    ⨆ (t : Set α) (_ : MeasurableSet t) (_ : μ t ≠ ∞) (_ : t ⊆ s), μ t = 0 := by
  simp only [ne_eq, ENNReal.iSup_eq_zero]
  exact fun t ht hμt hts ↦ (hs t ht hts).resolve_right hμt

lemma isZeroTopSet_iff_null [SigmaFinite μ] (hs : MeasurableSet s) :
    IsZeroTopSet s μ ↔ μ s = 0 := by
  refine ⟨fun h ↦ ?_, isZeroTopSet_of_null⟩
  rw [measure_eq_iSup_measure_subset hs, iSup_measure_subset_eq_zero_of_isZeroTopSet h]

def maxZeroTopSet (μ : Measure α) [SFinite μ] : Set α :=
  {x | densityToSigmaFinite μ x = ∞}

lemma measurableSet_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    MeasurableSet (maxZeroTopSet μ) :=
  measurable_densityToSigmaFinite μ (measurableSet_singleton ∞)

lemma isZeroTopSet_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    IsZeroTopSet (maxZeroTopSet μ) μ := by
  intro t ht ht_subset
  rw [← withDensity_densityToSigmaFinite μ, withDensity_apply _ ht]
  have h_int_eq : ∫⁻ a in t, densityToSigmaFinite μ a ∂μ.toSigmaFinite = ∞ * μ.toSigmaFinite t := by
    calc ∫⁻ a in t, densityToSigmaFinite μ a ∂μ.toSigmaFinite
    _ = ∫⁻ _ in t, ∞ ∂μ.toSigmaFinite :=
        set_lintegral_congr_fun ht (ae_of_all _ (fun x hx ↦ ht_subset hx))
    _ = ∞ * μ.toSigmaFinite t := by simp
  rw [h_int_eq]
  by_cases h0 : μ.toSigmaFinite t = 0 <;> simp [h0]

lemma restrict_compl_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    μ.restrict (maxZeroTopSet μ)ᶜ = (μ.toSigmaFinite).restrict (maxZeroTopSet μ)ᶜ := by
  have hμ := withDensity_densityToSigmaFinite μ
  nth_rewrite 1 [← hμ]
  ext s hs
  rw [restrict_apply hs, withDensity_apply _ (hs.inter (measurableSet_maxZeroTopSet μ).compl),
    restrict_apply hs, ← set_lintegral_one]
  refine set_lintegral_congr_fun (hs.inter (measurableSet_maxZeroTopSet μ).compl)
    (ae_of_all _ (fun x hx ↦ ?_))
  simp only [maxZeroTopSet, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
    densityToSigmaFinite_eq_top_iff] at hx
  rw [densityToSigmaFinite_eq_one_iff]
  exact hx.2

lemma toSigmaFinite_add_restrict_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    (μ.toSigmaFinite).restrict (maxZeroTopSet μ)ᶜ + μ.restrict (maxZeroTopSet μ) = μ := by
  rw [← restrict_compl_maxZeroTopSet, restrict_compl_add_restrict (measurableSet_maxZeroTopSet μ)]

lemma restrict_maxZeroTopSet_eq_zero_or_top (μ : Measure α) [SFinite μ] (hs : MeasurableSet s) :
    μ.restrict (maxZeroTopSet μ) s = 0 ∨ μ.restrict (maxZeroTopSet μ) s = ∞ := by
  rw [restrict_apply' (measurableSet_maxZeroTopSet μ)]
  exact isZeroTopSet_maxZeroTopSet μ (s ∩ maxZeroTopSet μ)
    (hs.inter (measurableSet_maxZeroTopSet μ)) (Set.inter_subset_right _ _)

lemma sigmaFinite_iff_measure_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    SigmaFinite μ ↔ μ (maxZeroTopSet μ) = 0 := by
  refine ⟨fun h ↦ (isZeroTopSet_iff_null (measurableSet_maxZeroTopSet μ)).mp
    (isZeroTopSet_maxZeroTopSet μ), fun h ↦ ?_⟩
  rw [← toSigmaFinite_add_restrict_maxZeroTopSet μ, restrict_eq_zero.mpr h, add_zero]
  infer_instance

lemma measure_eq_iSup_measure_subset_toMeasurable [SigmaFinite μ] (s : Set α) :
    μ s = ⨆ (t : Set α) (_ht : MeasurableSet t) (_hμt : μ t ≠ ∞) (_hts : t ⊆ toMeasurable μ s),
      μ t := by
  rw [← measure_toMeasurable s,measure_eq_iSup_measure_subset (measurableSet_toMeasurable _ _)]

lemma isZeroTopSet_iff_ne_iSup_of_eq_top (hμs : μ s = ∞) :
    IsZeroTopSet s μ
      ↔ μ s ≠ ⨆ (t : Set α) (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (hts : t ⊆ s), μ t := by
  refine ⟨fun hs ↦ ?_, fun h ↦ ?_⟩
  · simp [iSup_measure_subset_eq_zero_of_isZeroTopSet hs, hμs]
  · sorry

end Measure

end MeasureTheory
