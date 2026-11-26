module

public import Thesis.MeasureGeometry.CylinderSelection
public import Thesis.MeasureGeometry.LineDensity

/-! Flat blow-ups of the original energy measure on the rectifiable carrier. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace Thesis.MeasureGeometry

private theorem ae_pos_weight_of_positive_density
    {Ω S : Set Point} {μ : Measure Point} [IsFiniteMeasure μ] [μ.OuterRegular]
    (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) {η : ℝ} (hη : 0 < η)
    (hD : ∀ x ∈ S, ∃ θ ≥ η / 2, Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ))
    {f : Point → ℝ≥0∞} (hf : Measurable f)
    (hRep : μ.restrict Ω = (HausdorffOne.restrict S).withDensity f) :
    ∀ᵐ x ∂HausdorffOne.restrict S, 0 < f x := by
  let F := S ∩ {x : Point | f x = 0}
  have hF : MeasurableSet F := hS.inter (measurableSet_eq_fun hf measurable_const)
  have hFS : F ⊆ S := inter_subset_left
  have hμF : μ F = 0 := by
    rw [← show (μ.restrict Ω) F = μ F from by
      rw [Measure.restrict_apply hF, inter_eq_left.mpr (hFS.trans hSΩ)], hRep, withDensity_apply _ hF]
    have hInt : (∫⁻ x in F, f x ∂HausdorffOne.restrict S) = ∫⁻ _ in F, (0 : ℝ≥0∞) ∂HausdorffOne.restrict S := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hF] with x hx
      exact hx.2
    rw [hInt, lintegral_zero]
  have hLen := hausdorffOne_le_of_positive_oneDensity μ hFS hη hD
  rw [hμF, mul_zero] at hLen
  rw [ae_iff]
  have hZero : {x : Point | ¬0 < f x} = {x | f x = 0} := by
    ext x
    simp only [mem_setOf_eq, not_lt, nonpos_iff_eq_zero]
  rw [hZero, Measure.restrict_apply (measurableSet_eq_fun hf measurable_const), inter_comm]
  exact nonpos_iff_eq_zero.mp hLen

private theorem eventually_scaled_test_vanishes_outside {Ω : Set Point} (hΩ : IsOpen Ω)
    {x : Point} (hx : x ∈ Ω) {φ : Point → ℝ} (hφc : HasCompactSupport φ) :
    ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ∀ y ∉ Ω, φ (s⁻¹ • (y - x)) = 0 := by
  obtain ⟨R, hR, hRφ⟩ := hφc.isBounded.subset_closedBall_lt 0 (0 : Point)
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.mp hΩ x hx
  filter_upwards [eventually_mem_positive_interval (div_pos hδ hR)] with s hs
  intro y hy
  apply image_eq_zero_of_notMem_tsupport
  intro hz
  have hzR := mem_closedBall.mp (hRφ hz)
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.1.le)] at hzR
  have hyR : ‖y - x‖ ≤ R * s := by
    simpa only [mul_comm s] using (inv_mul_le_iff₀ hs.1).mp hzR
  have hyδ : dist y x < δ := by
    rw [dist_eq_norm]
    have h := (lt_div_iff₀ hR).mp hs.2
    linarith only [h, hyR]
  exact hy (hδΩ (mem_ball.mpr hyδ))

/-- If the interior restriction has a flat tangent at an interior point,
the original ambient energy measure has the same tangent there. -/
theorem vagueOn_oneBlowup_of_restrict_interior {Ω : Set Point} (hΩ : IsOpen Ω)
    {μ : Measure Point} {x : Point} (hx : x ∈ Ω) {ν : Measure Point}
    (hFlat : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r (μ.restrict Ω)) ν) :
    SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r μ) ν := by
  intro φ hφ hφc hφs
  refine (hFlat φ hφ hφc hφs).congr' ?_
  filter_upwards [eventually_scaled_test_vanishes_outside hΩ hx hφc,
    self_mem_nhdsWithin] with r hSupp hr
  rw [integral_oneBlowup x hr hφ, integral_oneBlowup x hr hφ]
  exact congrArg (r⁻¹ * ·) (setIntegral_eq_integral_of_forall_compl_eq_zero hSupp)

/-- Almost every carrier point has a weighted line tangent for the same
ambient energy measure, with coefficient equal to the literal ball density. -/
theorem ae_flat_energy_line_and_density {Ω S : Set Point} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) (hRect : CountablyRectifiableOne S) (hLen : HausdorffOne S < ⊤)
    {μ : Measure Point} [IsFiniteMeasure μ] [μ.OuterRegular] {η : ℝ} (hη : 0 < η)
    (hD : ∀ x ∈ S, ∃ θ ≥ η / 2, Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ))
    {f : Point → ℝ≥0∞} (hf : Measurable f)
    (hRep : μ.restrict Ω = (HausdorffOne.restrict S).withDensity f) :
    ∀ᵐ x ∂HausdorffOne.restrict S, ∃ (e : Point) (b : ℝ), ‖e‖ = 1 ∧ 0 < b ∧
      SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
        (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r μ)
        (ENNReal.ofReal b • HausdorffOne.restrict ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point)) ∧
      Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 b) := by
  have hPos := ae_pos_weight_of_positive_density hS hSΩ hη hD hf hRep
  have hLen' : Measure.hausdorffMeasure ((1 : ℕ) : ℝ) S < ⊤ := by
    simpa only [Nat.cast_one] using hLen
  have hFin : IsFiniteMeasure ((HausdorffOne.restrict S).withDensity f) := hRep ▸ inferInstanceAs (IsFiniteMeasure (μ.restrict Ω))
  have hFin' : IsFiniteMeasure (((Measure.hausdorffMeasure ((1 : ℕ) : ℝ)).restrict S).withDensity f) := by
    simpa only [Nat.cast_one] using hFin
  have hPos' : ∀ᵐ x ∂(Measure.hausdorffMeasure ((1 : ℕ) : ℝ)).restrict S, 0 < f x := by
    simpa only [Nat.cast_one] using hPos
  have hT0 := SupportingAnalysis.rectifiableMeasureTangents 3 1 S f hS (CountablyRectifiableOne.to_euclidean hRect) hLen' hf hPos' hFin'
  have hT : ∀ᵐ x ∂HausdorffOne.restrict S, ∃ (L : Submodule ℝ Point) (b : ℝ),
      Module.finrank ℝ L = 1 ∧ 0 < b ∧
      SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
        (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r (μ.restrict Ω))
        (ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)) := by
    simpa only [Nat.cast_one, hRep] using hT0
  filter_upwards [hT, ae_restrict_mem hS] with x hx hxS
  obtain ⟨L, b, hL, hb, hLoc⟩ := hx
  have hFlat := vagueOn_oneBlowup_of_restrict_interior hΩ (hSΩ hxS) hLoc
  obtain ⟨e, he, hSpan⟩ := exists_unit_axis_of_finrank_one L hL
  refine ⟨e, b, he, hb, ?_, tendsto_oneDensity_of_flatBlowup hL hb hFlat⟩
  simpa only [hSpan] using hFlat

end Thesis.MeasureGeometry
