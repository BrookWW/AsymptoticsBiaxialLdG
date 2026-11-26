module

public import Thesis.MeasureGeometry.PlanarGapGradient
public import Thesis.MeasureGeometry.PlanarLevelGeometry
public import Thesis.MeasureGeometry.PlanarLevelLowerBound

/-! The weighted planar scalar coarea input and its disk-cover application. -/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

/-- Scalar coarea on an open planar set equipped with ordinary area and
one-dimensional Hausdorff measure. -/
def External.PlanarScalarCoarea : Prop :=
  ∀ (U : Set Plane), IsOpen U → ∀ (f : Plane → ℝ), ContDiffOn ℝ 1 f U →
    ∀ (w : ℝ → ℝ≥0∞), Measurable w →
      (∫⁻ x in U, w (f x) * ENNReal.ofReal ‖fderiv ℝ f x‖) =
        ∫⁻ t : ℝ, w t * Measure.hausdorffMeasure 1 (U ∩ {x | f x = t})

/-- Weighted radii of strict sublevel cores are controlled by the area
integral from scalar coarea. -/
theorem planarCoarea_sublevelRadius_le (hcoarea : External.PlanarScalarCoarea)
    {f j : Plane → ℝ} {w : ℝ → ℝ} {R μ A : ℝ}
    (hf : ContinuousOn f (closedBall (0 : Plane) R))
    (hf' : ContDiffOn ℝ 1 f (ball (0 : Plane) R ∩ {x | 0 < f x}))
    (hμR : μ ≤ R)
    (hAnn : ∀ x : Plane, μ ≤ ‖x‖ → ‖x‖ ≤ R → A ≤ f x)
    (hw : Measurable w)
    (hDensity : ∀ x ∈ ball (0 : Plane) R ∩ {x | 0 < f x}, w (f x) * ‖fderiv ℝ f x‖ ≤ j x) :
    (∫⁻ t in Ioo 0 A, ENNReal.ofReal (w t * planarCoverRadius (planarSublevelCore f R t))) ≤
      ∫⁻ x in ball (0 : Plane) R, ENNReal.ofReal (j x) := by
  classical
  let U := ball (0 : Plane) R ∩ {x | 0 < f x}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hF := (hf.mono ball_subset_closedBall).continuousAt (isOpen_ball.mem_nhds hx.1)
    exact Filter.inter_mem (isOpen_ball.mem_nhds hx.1) (hF.preimage_mem_nhds (Ioi_mem_nhds hx.2))
  let W := (Ioo 0 A).indicator (fun t => ENNReal.ofReal (w t))
  have hW : Measurable W := hw.ennreal_ofReal.indicator measurableSet_Ioo
  have hCo := hcoarea U hU f hf' W hW
  calc
    (∫⁻ t in Ioo 0 A, ENNReal.ofReal (w t * planarCoverRadius (planarSublevelCore f R t))) ≤
        ∫⁻ t : ℝ, W t * Measure.hausdorffMeasure 1 (U ∩ {x | f x = t}) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_mono
      intro t
      by_cases ht : t ∈ Ioo 0 A
      · rw [indicator_of_mem ht, ENNReal.ofReal_mul' (planarCoverRadius_nonneg _)]
        have hEq : U ∩ {x | f x = t} = ball (0 : Plane) R ∩ {x | f x = t} := by
          ext x
          constructor
          · exact fun hx => ⟨hx.1.1, hx.2⟩
          · intro hx
            have hxp : 0 < f x := by rw [show f x = t from hx.2]; exact ht.1
            exact ⟨⟨hx.1, hxp⟩, hx.2⟩
        change _ ≤ W t * Measure.hausdorffMeasure 1 (U ∩ {x | f x = t})
        rw [hEq, show W t = ENNReal.ofReal (w t) from indicator_of_mem ht _]
        exact mul_le_mul_right ((planarSublevelCore_inside_and_radius_le hf hμR
          (fun x hx hR => ht.2.trans_le (hAnn x hx hR))).2) _
      · rw [indicator_of_notMem ht]
        exact zero_le
    _ = (∫⁻ x in U, W (f x) * ENNReal.ofReal ‖fderiv ℝ f x‖) := hCo.symm
    _ ≤ ∫⁻ x in U, ENNReal.ofReal (j x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      by_cases hx' : f x ∈ Ioo 0 A
      · rw [show W (f x) = ENNReal.ofReal (w (f x)) from indicator_of_mem hx' _,
          ← ENNReal.ofReal_mul' (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hDensity x hx)
      · rw [show W (f x) = 0 from indicator_of_notMem hx' _, zero_mul]
        exact zero_le
    _ ≤ ∫⁻ x in ball (0 : Plane) R, ENNReal.ofReal (j x) :=
      lintegral_mono_set (μ := volume) (f := fun x => ENNReal.ofReal (j x)) inter_subset_left

/-- The modified spectral gap is continuously differentiable on its
strictly positive locus inside any open smoothness domain. -/
theorem contDiffOn_planarModifiedGap_pos_locus (a : BulkCoefficients)
    (τ : GapSmoothingParameter) {Q : Plane → S0} {U : Set Plane} (hQ : ContDiffOn ℝ 1 Q U) :
    ContDiffOn ℝ 1 (fun x => modifiedSpectralGap a τ (Q x))
      (U ∩ {x | 0 < modifiedSpectralGap a τ (Q x)}) :=
  ((contDiffOn_modifiedSpectralGap a τ).of_le (by decide : (1 : WithTop ℕ∞) ≤ 2)).comp
    (hQ.mono inter_subset_left) (fun x hx => (modifiedSpectralGap_pos_iff a τ (Q x)).mp hx.2)

/-- The spectral projection is continuously differentiable on the same
strictly positive locus. -/
theorem contDiffOn_planarSpectralProjection_pos_locus (a : BulkCoefficients)
    (τ : GapSmoothingParameter) {Q : Plane → S0} {U : Set Plane} (hQ : ContDiffOn ℝ 1 Q U) :
    ContDiffOn ℝ 1 (fun x => (spectralVacuumPoint a (Q x)).val)
      (U ∩ {x | 0 < modifiedSpectralGap a τ (Q x)}) :=
  ((contDiffOn_spectralVacuumPoint a).of_le (by decide)).comp
    (hQ.mono inter_subset_left) (fun x hx => (modifiedSpectralGap_pos_iff a τ (Q x)).mp hx.2)

/-- The gap derivative and the bulk term pay the coarea cost of the
sublevel covering radius. -/
theorem planarModifiedGap_coarea_expense_le (hcoarea : External.PlanarScalarCoarea)
    (a : BulkCoefficients) (τ : GapSmoothingParameter) {Q : Plane → S0} {R μ A ε c : ℝ}
    (hQcts : ContinuousOn Q (closedBall (0 : Plane) R))
    (hQ : ContDiffOn ℝ 1 Q (ball (0 : Plane) R)) (hμR : μ ≤ R) (hε : 0 < ε) (hc : 0 < c)
    (hAnn : ∀ x : Plane, μ ≤ ‖x‖ → ‖x‖ ≤ R → A ≤ modifiedSpectralGap a τ (Q x))
    (hcPotential : ∀ x ∈ ball (0 : Plane) R, c * planarGapLevelWeight (spectralGapSmoothingFactor τ)
      (modifiedSpectralGap a τ (Q x)) ≤ bulkPotential a (Q x)) :
    let f (x : Plane) := modifiedSpectralGap a τ (Q x)
    let w (t : ℝ) := (vacuumRadius a * Real.sqrt c / (3 * ε)) *
      Real.sqrt (planarGapLevelWeight (spectralGapSmoothingFactor τ) t)
    (∫⁻ t in Ioo 0 A, ENNReal.ofReal (w t * planarCoverRadius (planarSublevelCore f R t))) ≤
      ∫⁻ x in ball (0 : Plane) R, ENNReal.ofReal
        (vacuumRadius a ^ 2 / 36 * planarScalarGradientSq f x + bulkPotential a (Q x) / ε ^ 2) := by
  intro f w
  have hf : ContinuousOn f (closedBall (0 : Plane) R) :=
    (continuous_modifiedSpectralGap a τ).comp_continuousOn hQcts
  have hw : Continuous w := by
    dsimp only [w, planarGapLevelWeight]
    fun_prop
  apply planarCoarea_sublevelRadius_le hcoarea hf
    (contDiffOn_planarModifiedGap_pos_locus a τ hQ) hμR hAnn hw.measurable
  intro x hx
  let W := planarGapLevelWeight (spectralGapSmoothingFactor τ) (f x)
  let X := Real.sqrt (planarScalarGradientSq f x)
  let Y := Real.sqrt (bulkPotential a (Q x))
  have hW : 0 ≤ W := le_min (sq_nonneg _) (sq_nonneg _)
  have hX : 0 ≤ planarScalarGradientSq f x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hY : 0 ≤ bulkPotential a (Q x) := (mul_nonneg hc.le hW).trans (hcPotential x hx.1)
  have hR : 0 < vacuumRadius a := vacuumRadius_pos a
  have hSix : 0 < vacuumRadius a / 6 := by positivity
  have hSqrt : Real.sqrt c * Real.sqrt W ≤ Y := by
    rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt (hcPotential x hx.1)
  have hwpos : 0 ≤ w (f x) := by
    dsimp only [w]
    positivity
  have hDensity : w (f x) * ‖fderiv ℝ f x‖ ≤ w (f x) * X :=
    mul_le_mul_of_nonneg_left (norm_fderiv_le_sqrt_planarScalarGradientSq f x) hwpos
  apply hDensity.trans
  have hSqrtBound : w (f x) * X ≤ 2 * (vacuumRadius a / 6 * X) * (Y / ε) := by
    calc
      _ = (vacuumRadius a / (3 * ε) * X) * (Real.sqrt c * Real.sqrt W) := by dsimp only [w, W]; ring
      _ ≤ (vacuumRadius a / (3 * ε) * X) * Y :=
        mul_le_mul_of_nonneg_left hSqrt (by dsimp only [X]; positivity)
      _ = _ := by ring
  apply hSqrtBound.trans
  have hAM := sq_nonneg (vacuumRadius a / 6 * X - Y / ε)
  have hXSq : X ^ 2 = planarScalarGradientSq f x := Real.sq_sqrt hX
  have hYSq : Y ^ 2 = bulkPotential a (Q x) := Real.sq_sqrt hY
  calc
    _ ≤ (vacuumRadius a / 6 * X) ^ 2 + (Y / ε) ^ 2 := by linarith only [hAM]
    _ = _ := by rw [mul_pow, div_pow, div_pow, hXSq, hYSq]; ring

end Thesis
