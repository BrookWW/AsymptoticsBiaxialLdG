module

public import Thesis.Upstream.AmbientWeakPartialAlgebra
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Quantitative (L^2) operations on actual ambient weak derivatives. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

theorem ambient_lpNorm_congr_ae {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {f g : X → E} {p : ℝ≥0∞}
    (h : f =ᵐ[μ] g) : lpNorm f p μ = lpNorm g p μ := by
  by_cases hF : AEStronglyMeasurable f μ
  · rw [← toReal_eLpNorm hF, ← toReal_eLpNorm (hF.congr h),eLpNorm_congr_ae h]
  · rw [lpNorm_of_not_aestronglyMeasurable hF,
      lpNorm_of_not_aestronglyMeasurable (fun hG => hF (hG.congr h.symm))]

/-- A bounded scalar multiplier has its actual (L^p) multiplication bound. -/
theorem lpNorm_smul_le_of_pointwise_abs_le {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}
    {p : ℝ≥0∞} {v : X → E} (hv : MemLp v p μ) {a : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ x, |a x| ≤ C) :
    lpNorm (fun x => a x • v x) p μ ≤ C*lpNorm v p μ := by
  calc
    _ ≤ lpNorm (fun x => C*‖v x‖) p μ := by
      apply lpNorm_mono_real (hv.norm.const_mul C)
      intro x
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (ha x) (norm_nonneg _)
    _ = _ := by
      change lpNorm (C • fun x => ‖v x‖) p μ = _
      rw [lpNorm_const_smul,coe_nnnorm,Real.norm_of_nonneg hC,lpNorm_norm hv.1]

/-- The same multiplier bound with its pointwise controls only in the
domain of the actual measure. -/
theorem lpNorm_smul_restrict_le {n q : ℕ} {U : Set (Domain n)} (hU : MeasurableSet U)
    {v : Domain n → Ambient q} (hv : MemLp v 2 (volume.restrict U))
    {a : Domain n → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ x ∈ U, |a x| ≤ C) :
    lpNorm (fun x => a x • v x) 2 (volume.restrict U) ≤ C*lpNorm v 2 (volume.restrict U) := by
  classical
  have he : (fun x => a x • v x) =ᵐ[volume.restrict U] fun x => U.indicator a x • v x := by
    filter_upwards [ae_restrict_mem (μ := volume) hU] with x hx
    rw [indicator_of_mem hx]
  rw [ambient_lpNorm_congr_ae he]
  apply lpNorm_smul_le_of_pointwise_abs_le hv hC
  intro x
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx]
    exact ha x hx
  · rw [indicator_of_notMem hx,abs_zero]
    exact hC

/-- The derivative of a bounded coefficient times a field is bounded by the
two original (L^2) norms. -/
theorem lpNorm_smoothCoefficient_derivative_le {n q : ℕ} {U : Set (Domain n)}
    (hU : MeasurableSet U) {i : Fin n}
    {u D : Domain n → Ambient q}
    (hu : MemLp u 2 (volume.restrict U)) (hD : MemLp D 2 (volume.restrict U))
    {a : Domain n → ℝ} (ha : ContDiff ℝ ∞ a)
    (C : ℝ) (hC : 0 ≤ C)
    (hValue : ∀ x ∈ U, |a x| ≤ C)
    (hDeriv : ∀ x ∈ U, |coordinateDerivative a ha i x| ≤ C) :
    MemLp (fun x => coordinateDerivative a ha i x • u x + a x • D x) 2 (volume.restrict U) ∧
      lpNorm (fun x => coordinateDerivative a ha i x • u x + a x • D x) 2 (volume.restrict U) ≤
        C*(lpNorm u 2 (volume.restrict U)+lpNorm D 2 (volume.restrict U)) := by
  have hA : MemLp a ∞ (volume.restrict U) :=
    memLp_top_of_bound ha.continuous.aestronglyMeasurable C
      ((ae_restrict_mem (μ := volume) hU).mono fun x hx => by
        simpa only [Real.norm_eq_abs] using hValue x hx)
  have hG : Continuous (coordinateDerivative a ha i) :=
    ((ha.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hDA : MemLp (coordinateDerivative a ha i) ∞ (volume.restrict U) :=
    memLp_top_of_bound hG.aestronglyMeasurable C
      ((ae_restrict_mem (μ := volume) hU).mono fun x hx => by
        simpa only [Real.norm_eq_abs] using hDeriv x hx)
  have h1 := hu.smul (r := (2 : ℝ≥0∞)) hDA
  have h2 := hD.smul (r := (2 : ℝ≥0∞)) hA
  refine ⟨h1.add h2,?_⟩
  calc
    _ ≤ lpNorm (fun x => coordinateDerivative a ha i x • u x) 2 (volume.restrict U) +
        lpNorm (fun x => a x • D x) 2 (volume.restrict U) := lpNorm_add_le h1 (by norm_num)
    _ ≤ C*lpNorm u 2 (volume.restrict U) + C*lpNorm D 2 (volume.restrict U) :=
      add_le_add (lpNorm_smul_restrict_le hU hu hC hDeriv) (lpNorm_smul_restrict_le hU hD hC hValue)
    _ = _ := (mul_add _ _ _).symm

end Thesis
