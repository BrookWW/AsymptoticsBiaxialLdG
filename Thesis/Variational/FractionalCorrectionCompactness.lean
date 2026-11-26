module

public import Thesis.Variational.FractionalTransposition
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-! The fractional limit agrees with the interior limit of the same sequence. -/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem eLpNorm_two_sq_eq_lintegral_tensor
    (μ : Measure Point) (u : Point → S0) :
    eLpNorm u 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (‖u x‖^2) ∂μ := by
  calc
    _ = ∫⁻ x, ‖u x‖ₑ ^2 ∂μ := by
      simpa only [ENNReal.rpow_two, NNReal.coe_two, ENNReal.coe_two] using
        (eLpNorm_nnreal_pow_eq_lintegral (f := u) (μ := μ) (p := (2 : ℝ≥0)) (by norm_num))
    _ = _ := by
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem ConvergesHs.tendstoInMeasure {s : ℝ} {U : Set Point}
    {u : ℕ → Point → S0} {v : Point → S0} (h : ConvergesHs s U u v) :
    TendstoInMeasure (volume.restrict U) u atTop v := by
  let μ := volume.restrict U
  have hDom (n : ℕ) : eLpNorm (u n - v) 2 μ ^2 ≤ fractionalEnergy s U (u n - v) := by
    rw [eLpNorm_two_sq_eq_lintegral_tensor]
    exact self_le_add_right _ _
  have hSq : Tendsto (fun n => eLpNorm (u n - v) 2 μ ^2) atTop (𝓝 0) :=
    ENNReal.tendsto_nhds_zero.2 fun ε hε =>
      (ENNReal.tendsto_nhds_zero.1 h.2.2 ε hε).mono fun n hn => (hDom n).trans hn
  have hRoot := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).tendsto (0 : ℝ≥0∞)
  have hComp := hRoot.comp hSq
  have hRootEq (x : ℝ≥0∞) : (x^2) ^ (1/2 : ℝ) = x := by
    rw [← ENNReal.rpow_natCast_mul, show (↑(2 : ℕ) : ℝ) * (1/2 : ℝ) = 1 by norm_num,
      ENNReal.rpow_one]
  have he : Tendsto (fun n => eLpNorm (u n - v) 2 μ) atTop (𝓝 0) := by
    change Tendsto (fun n => (eLpNorm (u n - v) 2 μ ^ 2) ^ (1/2 : ℝ)) atTop
      (𝓝 ((0 : ℝ≥0∞) ^ (1/2 : ℝ))) at hComp
    simpa only [hRootEq, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1/2)] using hComp
  exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (fun n => (h.1 n).1) h.2.1.1 he

theorem MemHs.energy_le_of_sqrt_bound
    {s : ℝ} {U : Set Point} {u : Point → S0} (h : MemHs s U u) {C : ℝ}
    (hB : Real.sqrt ((fractionalEnergy s U u).toReal) ≤ C) :
    fractionalEnergy s U u ≤ ENNReal.ofReal (C^2) := by
  have hSq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hB 2
  rw [Real.sq_sqrt ENNReal.toReal_nonneg] at hSq
  rw [← ENNReal.ofReal_toReal h.2.ne]
  exact ENNReal.ofReal_le_ofReal hSq

theorem MemHs.memLp_two_and_eLpNorm_le_of_sqrt_bound
    {s : ℝ} {U : Set Point} {u : Point → S0} (h : MemHs s U u) {C : ℝ} (hC : 0 ≤ C)
    (hB : Real.sqrt ((fractionalEnergy s U u).toReal) ≤ C) :
    MemLp u 2 (volume.restrict U) ∧ eLpNorm u 2 (volume.restrict U) ≤ ENNReal.ofReal C := by
  let E := eLpNorm u 2 (volume.restrict U)
  have hL : E^2 ≤ fractionalEnergy s U u := by
    dsimp only [E]
    rw [eLpNorm_two_sq_eq_lintegral_tensor]
    exact self_le_add_right _ _
  have hP := hL.trans (h.energy_le_of_sqrt_bound hB)
  rw [ENNReal.ofReal_pow hC] at hP
  have hRoot := ENNReal.rpow_le_rpow hP (by norm_num : (0 : ℝ) ≤ 1/2)
  have hId (x : ℝ≥0∞) : (x^2)^(1/2 : ℝ) = x := by
    rw [← ENNReal.rpow_natCast_mul, show (↑(2 : ℕ) : ℝ)*(1/2 : ℝ) = 1 by norm_num,
      ENNReal.rpow_one]
  rw [hId, hId] at hRoot
  exact ⟨⟨h.1, hRoot.trans_lt ENNReal.ofReal_lt_top⟩, hRoot⟩

private theorem strong_fractional_limit_ae_eq_of_pointwise
    {U : Set Point} (hU : MeasurableSet U) {s : ℝ} {u : ℕ → Point → S0} {v W : Point → S0}
    (h : ConvergesHs s U u v) (hPoint : ∀ x ∈ U, Tendsto (fun n => u n x) atTop (𝓝 (W x))) :
    v =ᵐ[volume.restrict U] W := by
  obtain ⟨κ, hκ, hv⟩ := h.tendstoInMeasure.exists_seq_tendsto_ae
  filter_upwards [hv, ae_restrict_mem (μ := volume) hU] with x hx hxu
  exact tendsto_nhds_unique hx ((hPoint x hxu).comp hκ.tendsto_atTop)

/-- Once the scaled sequence has its interior pointwise limit, the
fractional compactness produces strong convergence along that same
sequence at each strictly lower fractional exponent. -/
theorem convergesHs_of_pointwise_and_bounded_higher_energy
    (hCompact : External.FractionalSobolevCompactEmbedding)
    {U : Set Point} (hU : IsSmoothDomain U) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1/2)
    {u : ℕ → Point → S0} {W : Point → S0}
    (hsMem : ∀ n, MemHs s U (u n)) (htMem : ∀ n, MemHs t U (u n))
    (hBound : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ᶠ n in atTop, fractionalEnergy t U (u n) ≤ C)
    (hPoint : ∀ x ∈ U, Tendsto (fun n => u n x) atTop (𝓝 (W x))) :
    ConvergesHs s U u W := by
  obtain ⟨κ, v, hκ, hv⟩ := hCompact U hU s t hs hst ht u htMem hBound
  have hAe := strong_fractional_limit_ae_eq_of_pointwise hU.1.1.measurableSet hv
    (fun x hx => (hPoint x hx).comp hκ.tendsto_atTop)
  refine ⟨hsMem, hv.2.1.congr_ae hAe, ?_⟩
  apply tendsto_of_subseq_tendsto
  intro η hη
  obtain ⟨C, hC, hB⟩ := hBound
  obtain ⟨ν, w, hν, hw⟩ := hCompact U hU s t hs hst ht (u ∘ η) (fun n => htMem (η n))
    ⟨C,hC,hη.eventually hB⟩
  have hwAe : w =ᵐ[volume.restrict U] W :=
    strong_fractional_limit_ae_eq_of_pointwise hU.1.1.measurableSet hw
      (fun x hx => (hPoint x hx).comp (hη.comp hν.tendsto_atTop))
  refine ⟨ν, hw.2.2.congr' (Eventually.of_forall fun n => ?_)⟩
  exact fractionalEnergy_congr_ae (EventuallyEq.rfl.sub hwAe)

end Thesis

end
