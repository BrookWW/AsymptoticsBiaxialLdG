module

public import Thesis.MeasureGeometry.RectifiableStress
public import SupportingAnalysis.Measure.Tangents
public import Mathlib.MeasureTheory.Integral.Average

/-! Flat tangents for the actual one-dimensional Hausdorff carrier and its weights. -/

public section

open Filter MeasureTheory Metric Set
open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace Thesis.MeasureGeometry

/-- The thesis's real-line parametrizations give the same rectifiable carrier
as the Euclidean one-dimensional parametrizations. -/
theorem CountablyRectifiableOne.to_euclidean {S : Set Point} (h : CountablyRectifiableOne S) :
    SupportingAnalysis.CountablyRectifiable 1 S := by
  obtain ⟨f, hf, hnull⟩ := h
  let p : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0
  let g (k : ℕ) := f k ∘ p
  have hg (k : ℕ) : range (g k) = range (f k) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨p y, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨EuclideanSpace.single 0 t, ?_⟩
      change f k (p (EuclideanSpace.single 0 t)) = f k t
      congr 1
  refine ⟨g, ?_, ?_⟩
  · intro k
    obtain ⟨K, hK⟩ := hf k
    exact ⟨_, hK.comp p.lipschitz⟩
  · simpa only [hg, Nat.cast_one] using hnull

/-- The finite Hausdorff carrier has a flat length tangent at almost every
point. Apply the tangent-measure result with constant weight one. -/
theorem ae_flat_tangent_of_countablyRectifiableOne {S : Set Point} (hS : MeasurableSet S)
    (hR : CountablyRectifiableOne S) (hfin : HausdorffOne S < ⊤) :
    let ζ := HausdorffOne.restrict S
    ∀ᵐ x ∂ζ, ∃ (L : Submodule ℝ Point) (b : ℝ), Module.finrank ℝ L = 1 ∧ 0 < b ∧
      SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
        (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r ζ)
        (ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)) := by
  have hfinW : Measure.hausdorffMeasure ((1 : ℕ) : ℝ) S < ⊤ := by
    rw [Nat.cast_one]
    exact hfin
  let ζ := (Measure.hausdorffMeasure ((1 : ℕ) : ℝ)).restrict S
  letI : IsFiniteMeasure ζ := by
    constructor
    simpa only [ζ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using hfinW
  have hF : IsFiniteMeasure (ζ.withDensity (fun _ => (1 : ℝ≥0∞))) := by
    rw [withDensity_const, one_smul]
    infer_instance
  have h := SupportingAnalysis.rectifiableMeasureTangents 3 1 S (fun _ => 1) hS
    (CountablyRectifiableOne.to_euclidean hR) hfinW measurable_const
    (Filter.Eventually.of_forall fun _ => zero_lt_one) hF
  simpa only [Nat.cast_one, withDensity_const, one_smul] using h

/-- Evaluation of a scalar test under the same `r⁻¹` dilation normalization
as the one-dimensional flat tangent theorem. -/
theorem integral_oneBlowup {μ : Measure Point} (x : Point) {r : ℝ} (hr : 0 < r)
    {φ : Point → ℝ} (hφ : Continuous φ) :
    (∫ y, φ y ∂SupportingAnalysis.blownUpMeasure (d := 1) x r μ) =
      r⁻¹ * ∫ y, φ (r⁻¹ • (y - x)) ∂μ := by
  have hmap : Measurable (fun y : Point => r⁻¹ • (y - x)) := by fun_prop
  rw [SupportingAnalysis.blownUpMeasure, integral_smul_measure, Nat.cast_one, zpow_neg, zpow_one,
    ENNReal.toReal_ofReal (inv_nonneg.2 hr.le), smul_eq_mul,
    integral_map hmap.aemeasurable hφ.aestronglyMeasurable]

/-- The Lebesgue-point estimate for each fixed multiple of a shrinking ball,
with all multiples available at the same almost-everywhere point. -/
theorem ae_average_norm_sub_closedBall_mul {μ : Measure Point} [IsFiniteMeasure μ]
    {w : Point → ℝ} (hw : Integrable w μ) :
    ∀ᵐ x ∂μ, ∀ R > (0 : ℝ), Tendsto
      (fun r : ℝ => ⨍ y in closedBall x (R * r), ‖w y - w x‖ ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_average_norm_sub hw.locallyIntegrable] with x hx
  intro R hR
  exact hx.comp ((Besicovitch.tendsto_filterAt μ x).comp
    (SupportingAnalysis.tendsto_const_mul_nhdsGT_zero hR))

/-- Normalized mass in any fixed compact ball stays bounded along a vague
blow-up. The center and the dilation in the bound are those of the tangent. -/
theorem eventually_bounded_rescaled_closedBall {μ : Measure Point} [IsFiniteMeasure μ]
    {x : Point} {τ : Measure Point}
    (hτ : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r μ) τ) {R : ℝ} (hR : 0 < R) :
    ∃ C ≥ (0 : ℝ), ∀ᶠ r : ℝ in 𝓝[>] 0, r⁻¹ * (μ (closedBall x (R * r))).toReal ≤ C := by
  obtain ⟨C, hC, hB⟩ := SupportingAnalysis.eventually_bounded_normalized_closedBall_mass_of_vague_blowup x μ τ hτ
  refine ⟨R * C.toReal, mul_nonneg hR.le ENNReal.toReal_nonneg, ?_⟩
  filter_upwards [(SupportingAnalysis.tendsto_const_mul_nhdsGT_zero hR) hB, self_mem_nhdsWithin]
    with r hB' hr
  have hr0 : 0 < r := hr
  have h := ENNReal.toReal_mono hC hB'
  rw [ENNReal.toReal_mul, Nat.cast_one, zpow_neg, zpow_one, ENNReal.toReal_ofReal
    (inv_nonneg.2 (mul_nonneg hR.le hr0.le))] at h
  calc
    _ = R * ((R * r)⁻¹ * (μ (closedBall x (R * r))).toReal) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hR.le

/-- At a Lebesgue point of an integrable weight, the scaled scalar pairing
with a compactly supported test converges to the tangent pairing times the
value of the weight at the center. -/
theorem tendsto_rescaled_scalar_pairing {μ : Measure Point} [IsFiniteMeasure μ]
    {x : Point} {τ : Measure Point}
    (hτ : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r μ) τ)
    {w : Point → ℝ} (hw : Integrable w μ)
    (hAvg : ∀ R > (0 : ℝ), Tendsto
      (fun r : ℝ => ⨍ y in closedBall x (R * r), ‖w y - w x‖ ∂μ) (𝓝[>] 0) (𝓝 0))
    {φ : Point → ℝ} (hφ : Continuous φ) (hcomp : HasCompactSupport φ) :
    Tendsto (fun r : ℝ => r⁻¹ * ∫ y, w y * φ (r⁻¹ • (y - x)) ∂μ) (𝓝[>] 0)
      (𝓝 (w x * ∫ z, φ z ∂τ)) := by
  obtain ⟨R, hR, hRφ⟩ := hcomp.isBounded.subset_closedBall_lt 0 (0 : Point)
  obtain ⟨M, hM, hMφ⟩ :=
    (hcomp.image hφ.norm).isBounded.subset_closedBall_lt 0 (0 : ℝ)
  have hzero (z : Point) (hz : z ∉ tsupport φ) : φ z = 0 := by
    by_contra h
    exact hz (subset_tsupport _ (Function.mem_support.mpr h))
  have hBound (z : Point) : ‖φ z‖ ≤ M := by
    by_cases hz : z ∈ tsupport φ
    · have hb := hMφ (mem_image_of_mem _ hz)
      simpa only [mem_closedBall, Real.dist_eq, sub_zero, abs_norm] using hb
    · rw [hzero z hz, norm_zero]
      exact hM.le
  let ψ (r : ℝ) (y : Point) := φ (r⁻¹ • (y - x))
  have hψ (r : ℝ) : Continuous (ψ r) := by
    dsimp only [ψ]
    fun_prop
  have hψBound (r : ℝ) : ∀ᵐ y ∂μ, ‖ψ r y‖ ≤ M :=
    Eventually.of_forall fun y => hBound _
  let d (y : Point) := w y - w x
  have hd : Integrable d μ := hw.sub (integrable_const _)
  let err (r : ℝ) := r⁻¹ * ∫ y, d y * ψ r y ∂μ
  let avg (r : ℝ) := ⨍ y in closedBall x (R * r), ‖d y‖ ∂μ
  have hAvg0 : Tendsto avg (𝓝[>] 0) (𝓝 0) := hAvg R hR
  obtain ⟨C, hC, hMass⟩ := eventually_bounded_rescaled_closedBall hτ hR
  have hErr : Tendsto err (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hUp : Tendsto (fun r => M * C * avg r) (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using hAvg0.const_mul (M * C)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUp
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [self_mem_nhdsWithin, hMass] with r hr hMr
    have hr' : 0 < r := hr
    let B := closedBall x (R * r)
    have hOff (y : Point) (hy : y ∉ B) : ψ r y = 0 := by
      apply hzero
      intro hmem
      apply hy
      have hb := hRφ hmem
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hr'] at hb
      rw [mem_closedBall, dist_eq_norm]
      simpa only [mul_comm r R] using (inv_mul_le_iff₀ hr').mp hb
    have hAvg_nonneg : 0 ≤ avg r := by
      change 0 ≤ ⨍ y in B, ‖d y‖ ∂μ
      rw [setAverage_eq, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
        (integral_nonneg fun _ => norm_nonneg _)
    have hInt : ‖∫ y in B, d y * ψ r y ∂μ‖ ≤ M * ∫ y in B, ‖d y‖ ∂μ := by
      rw [← integral_const_mul]
      refine (norm_integral_le_integral_norm _).trans
        (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          ((hd.norm.const_mul M).integrableOn) (Eventually.of_forall fun y => ?_))
      change ‖d y * ψ r y‖ ≤ M * ‖d y‖
      rw [norm_mul, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hBound _) (norm_nonneg _)
    have hAvg_eq : (μ B).toReal * avg r = ∫ y in B, ‖d y‖ ∂μ :=
      measure_smul_setAverage _ (measure_ne_top μ B)
    calc
      ‖err r‖ = r⁻¹ * ‖∫ y in B, d y * ψ r y ∂μ‖ := by
        dsimp only [err]
        rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.2 hr'.le),
          setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hOff y hy, mul_zero])]
      _ ≤ r⁻¹ * (M * ∫ y in B, ‖d y‖ ∂μ) :=
        mul_le_mul_of_nonneg_left hInt (inv_nonneg.2 hr'.le)
      _ = M * (r⁻¹ * (μ B).toReal) * avg r := by rw [← hAvg_eq]; ring
      _ ≤ M * C * avg r := by gcongr
  have hUnweighted : Tendsto (fun r : ℝ => r⁻¹ * ∫ y, ψ r y ∂μ) (𝓝[>] 0)
      (𝓝 (∫ z, φ z ∂τ)) := by
    refine (hτ φ hφ hcomp (subset_univ _)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact integral_oneBlowup x hr hφ
  have hSum := hErr.add (hUnweighted.const_mul (w x))
  simp only [zero_add] at hSum
  refine hSum.congr fun r => ?_
  have hwi := hw.mul_bdd (hψ r).aestronglyMeasurable (hψBound r)
  have hci := (integrable_const (w x)).mul_bdd (hψ r).aestronglyMeasurable (hψBound r)
  have hsplit : (∫ y, d y * ψ r y ∂μ) =
      (∫ y, w y * ψ r y ∂μ) - w x * ∫ y, ψ r y ∂μ := by
    simp only [d, sub_mul]
    rw [integral_sub hwi hci, integral_const_mul]
  change err r + w x * (r⁻¹ * ∫ y, ψ r y ∂μ) = r⁻¹ * ∫ y, w y * ψ r y ∂μ
  dsimp only [err]
  rw [hsplit]
  ring

/-- A countable collection of integrable scalar weights has the same flat
carrier tangent at almost every point. This applies to all entries of a
matrix density using a single line and a single carrier coefficient. -/
theorem ae_flat_tangent_with_scalar_pairings {S : Set Point} (hS : MeasurableSet S)
    (hR : CountablyRectifiableOne S) (hfin : HausdorffOne S < ⊤)
    {ι : Type*} [Countable ι] {w : ι → Point → ℝ}
    (hw : ∀ i, Integrable (w i) (HausdorffOne.restrict S)) :
    let ζ := HausdorffOne.restrict S
    ∀ᵐ x ∂ζ, ∃ (L : Submodule ℝ Point) (b : ℝ), Module.finrank ℝ L = 1 ∧ 0 < b ∧
      let τ := ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)
      SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
        (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r ζ) τ ∧
      ∀ (i : ι) (φ : Point → ℝ), Continuous φ → HasCompactSupport φ →
        Tendsto (fun r : ℝ => r⁻¹ * ∫ y, w i y * φ (r⁻¹ • (y - x)) ∂ζ) (𝓝[>] 0)
          (𝓝 (w i x * ∫ z, φ z ∂τ)) := by
  let ζ := HausdorffOne.restrict S
  letI : IsFiniteMeasure ζ := by
    constructor
    simpa only [ζ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using hfin
  filter_upwards [ae_flat_tangent_of_countablyRectifiableOne hS hR hfin,
    ae_all_iff.2 fun i => ae_average_norm_sub_closedBall_mul (hw i)] with x hx hMean
  obtain ⟨L, b, hL, hb, hTan⟩ := hx
  refine ⟨L, b, hL, hb, hTan, ?_⟩
  intro i φ hφ hφc
  exact tendsto_rescaled_scalar_pairing hTan (hw i) (hMean i) hφ hφc

end Thesis.MeasureGeometry

end
