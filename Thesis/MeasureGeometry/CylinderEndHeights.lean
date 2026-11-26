module

public import Thesis.MeasureGeometry.CylinderSliceEnergy
public import Thesis.MeasureGeometry.EnergyMonotonicity

/-! Choosing the two actual planar endcaps by averaging over height. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

private theorem exists_le_interval_average {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntegrableOn f (Ioo a b)) :
    ∃ t ∈ Ioo a b, f t ≤ (∫ t in Ioo a b, f t) / (b - a) := by
  let I := Ioo a b
  let A := (∫ t in I, f t) / (b - a)
  let μ : Measure ℝ := volume.restrict I
  by_contra! h
  have hIntA : Integrable (fun _ : ℝ => A) μ :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hInt : Integrable (fun t => f t - A) μ := hf.sub hIntA
  have hPos : ∀ᵐ t ∂μ, 0 ≤ f t - A := (ae_restrict_mem measurableSet_Ioo).mono fun t ht =>
    (sub_pos.mpr (h t ht)).le
  have hSupp : I ⊆ Function.support (fun t => f t - A) := fun t ht => (sub_pos.mpr (h t ht)).ne'
  have hMass : 0 < μ I := by
    rw [Measure.restrict_apply measurableSet_Ioo, inter_self, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  have hP := (integral_pos_iff_support_of_nonneg_ae hPos hInt).mpr (hMass.trans_le (measure_mono hSupp))
  rw [integral_sub hf hIntA, integral_const, Measure.real_def, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le), smul_eq_mul] at hP
  have hA : (b - a) * A = ∫ t in I, f t := by
    dsimp only [A]
    rw [mul_div_cancel₀ _ (sub_ne_zero.mpr hab.ne')]
  exact (lt_irrefl (0 : ℝ)) (by linarith only [hP, hA])

theorem closedCylinder_centered_height_subset_ball
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {s r : ℝ}
    (_hs : 0 < s) (hr : r < s) :
    translatedClosedAxisCylinder c (B 2) r (-s) s ⊆ ball c (2 * s) := by
  intro x hx
  let y := x - c
  change y ∈ closedAxisCylinder (B 2) r (-s) s at hx
  have hA : |cylinderHeight (B 2) y| ≤ s := abs_le.mpr hx.2
  have hN := norm_add_le (y - cylinderHeight (B 2) y • B 2) (cylinderHeight (B 2) y • B 2)
  rw [sub_add_cancel, norm_smul, Real.norm_eq_abs, B.orthonormal.norm_eq_one 2, mul_one] at hN
  have hR : ‖y - cylinderHeight (B 2) y • B 2‖ ≤ r := hx.1
  rw [mem_ball, dist_eq_norm]
  change ‖y‖ < 2 * s
  linarith only [hN, hA, hR, hr]

private theorem closedBall_slice_mem_centered_cylinder
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {r s z : ℝ}
    (hz : z ∈ Icc (-s) s) {y : Plane} (hy : y ∈ closedBall 0 r) :
    c + axisChart B (y, z) ∈ translatedClosedAxisCylinder c (B 2) r (-s) s := by
  change c + axisChart B (y, z) - c ∈ closedAxisCylinder (B 2) r (-s) s
  rw [add_sub_cancel_left]
  change cylinderTransverseRadius (B 2) (axisChart B (y, z)) ≤ r ∧
    -s ≤ cylinderHeight (B 2) (axisChart B (y, z)) ∧ cylinderHeight (B 2) (axisChart B (y, z)) ≤ s
  rw [cylinderTransverseRadius_axisChart, cylinderHeight_axisChart]
  exact ⟨mem_closedBall_zero_iff.mp hy, hz.1, hz.2⟩

/-- The two selected planar angular cuts have the actual total cap
energy bounded by four over the half-height times the containing ball's
energy. The end heights remain within the source intervals. -/
theorem exists_good_classical_endHeights
    (a : BulkCoefficients) (ε : ElasticScale) (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    {s r : ℝ} (hs : 0 < s) (hr : r < s) (hΩB : closedBall c (2 * s) ⊆ Ω) :
    ∃ lo ∈ Ioo (-s) (-(s / 2)), ∃ hi ∈ Ioo (s / 2) s,
      planarSmoothEnergy a ε (cylinderSliceMap B c Q lo) r +
        planarSmoothEnergy a ε (cylinderSliceMap B c Q hi) r ≤
          (4 / s) * ∫ x in ball c (2 * s), energyDensity a ε (Q x) (ClassicalGradient Q x) := by
  let F (x : Point) := energyDensity a ε (Q x) (ClassicalGradient Q x)
  let E := ∫ x in ball c (2 * s), F x
  let K := translatedClosedAxisCylinder c (B 2) r (-s) s
  let S := translatedAxisCylinder c (B 2) r (-s) s
  have hK : K ⊆ ball c (2 * s) := closedCylinder_centered_height_subset_ball B c hs hr
  have hS : S ⊆ ball c (2 * s) := (translatedAxisCylinder_subset_closed _ _ _ _ _).trans hK
  have hFb : IntegrableOn F (ball c (2 * s)) :=
    (((continuousOn_classicalEnergyDensity hΩ a ε hQ).mono hΩB).integrableOn_compact
      (isCompact_closedBall c (2 * s))).mono_set ball_subset_closedBall
  have hF₀ (x : Point) : 0 ≤ F x := by
    unfold F energyDensity
    rw [gradientNormSq_eq_sum_norm_sq]
    exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _))
  have hSum : (∫ x in S, F x) ≤ E :=
    setIntegral_mono_set hFb (Eventually.of_forall hF₀) (Eventually.of_forall hS)
  obtain ⟨hFT, hVol⟩ := integral_translatedAxisCylinder_eq_iterated B c r (-s) s F (hFb.mono_set hS)
  let f (z : ℝ) := ∫ y in ball (0 : Plane) r, F (c + axisChart B (y, z))
  have hf : IntegrableOn f (Ioo (-s) s) := hFT.integral_prod_right
  have hf₀ (z : ℝ) : 0 ≤ f z := integral_nonneg fun _ => hF₀ _
  have hloSub : Ioo (-s) (-(s / 2)) ⊆ Ioo (-s) s := fun _ hz => ⟨hz.1, hz.2.trans (by linarith)⟩
  have hhiSub : Ioo (s / 2) s ⊆ Ioo (-s) s := fun _ hz => ⟨(by linarith : -s < s / 2).trans hz.1, hz.2⟩
  obtain ⟨lo, hlo, hLo⟩ := exists_le_interval_average (by linarith : -s < -(s / 2)) (hf.mono_set hloSub)
  obtain ⟨hi, hhi, hHi⟩ := exists_le_interval_average (by linarith : s / 2 < s) (hf.mono_set hhiSub)
  have hFub : (∫ z in Ioo (-s) s, f z) ≤ E := hVol ▸ hSum
  have hLo' : f lo ≤ E / (s / 2) := by
    have hN := setIntegral_mono_set hf (Eventually.of_forall hf₀) (Eventually.of_forall hloSub)
    have h := div_le_div_of_nonneg_right (hN.trans hFub) (half_pos hs).le
    exact (show f lo ≤ (∫ t in Ioo (-s) (-(s / 2)), f t) / (s / 2) by
      convert hLo using 1
      ring).trans h
  have hHi' : f hi ≤ E / (s / 2) := by
    have hN := setIntegral_mono_set hf (Eventually.of_forall hf₀) (Eventually.of_forall hhiSub)
    have h := div_le_div_of_nonneg_right (hN.trans hFub) (half_pos hs).le
    exact (show f hi ≤ (∫ t in Ioo (s / 2) s, f t) / (s / 2) by
      convert hHi using 1
      ring).trans h
  have hP (z : ℝ) (hz : z ∈ Ioo (-s) s) :
      planarSmoothEnergy a ε (cylinderSliceMap B c Q z) r ≤ f z :=
    planarSmoothEnergy_slice_le_volume_integral B c a ε hΩ hQ (fun y hy =>
      hΩB (ball_subset_closedBall (hK (closedBall_slice_mem_centered_cylinder B c (Ioo_subset_Icc_self hz) hy))))
  refine ⟨lo, hlo, hi, hhi, (add_le_add ((hP lo (hloSub hlo)).trans hLo')
    ((hP hi (hhiSub hhi)).trans hHi')).trans_eq ?_⟩
  change E / (s / 2) + E / (s / 2) = (4 / s) * E
  field_simp [hs.ne']
  ring

/-- Ball monotonicity and the logarithmic global bound give the original
uniform endcap budget, with the two independent height selections. -/
theorem good_classical_endHeights_of_logarithmic_ball_bound
    (a : BulkCoefficients) (ε : ElasticScale) (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hEuler : ∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x))
    {M R s r : ℝ} (hM : 0 ≤ M) (hs : 0 < s) (hr : r < s)
    (hSmall : 2 * s ≤ R) (hOuter : closedBall c R ⊆ Ω)
    (hLog : 1 ≤ Real.log (1 / (ε : ℝ)))
    (hEnergy : energy a ε Ω Q (ClassicalGradient Q) ≤ ENNReal.ofReal (M * (Real.log (1 / (ε : ℝ)) + 1))) :
    ∃ lo ∈ Ioo (-s) (-(s / 2)), ∃ hi ∈ Ioo (s / 2) s,
      planarSmoothEnergy a ε (cylinderSliceMap B c Q lo) r +
        planarSmoothEnergy a ε (cylinderSliceMap B c Q hi) r ≤
          (16 * M / R) * Real.log (1 / (ε : ℝ)) := by
  have hR : 0 < R := (mul_pos (by norm_num) hs).trans_le hSmall
  let L := Real.log (1 / (ε : ℝ))
  let F (x : Point) := energyDensity a ε (Q x) (ClassicalGradient Q x)
  have hΩB := (closedBall_subset_closedBall hSmall).trans hOuter
  have hInt : IntegrableOn F (ball c (2 * s)) :=
    (((continuousOn_classicalEnergyDensity hΩ a ε hQ).mono hΩB).integrableOn_compact
      (isCompact_closedBall c (2 * s))).mono_set ball_subset_closedBall
  have hF₀ (x : Point) : 0 ≤ F x := by
    unfold F energyDensity
    rw [gradientNormSq_eq_sum_norm_sq]
    exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _))
  have hEq : (energy a ε (ball c (2 * s)) Q (ClassicalGradient Q)).toReal =
      ∫ x in ball c (2 * s), F x := by
    exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF₀) hInt.1).symm
  have hMono := normalized_classicalBallEnergy_monotoneOn a ε hΩ hQ hEuler hR hOuter
    (show 2 * s ∈ Ioc 0 R from ⟨mul_pos (by norm_num) hs, hSmall⟩)
    (show R ∈ Ioc 0 R from ⟨hR, le_rfl⟩) hSmall
  have hUpperE : energy a ε (ball c R) Q (ClassicalGradient Q) ≤ ENNReal.ofReal (2 * M * L) := by
    apply (lintegral_mono_set (ball_subset_closedBall.trans hOuter)).trans
    apply hEnergy.trans
    apply ENNReal.ofReal_le_ofReal
    change M * (L + 1) ≤ 2 * M * L
    nlinarith only [mul_nonneg hM (sub_nonneg.mpr hLog)]
  have hU : (energy a ε (ball c R) Q (ClassicalGradient Q)).toReal ≤ 2 * M * L := by
    have hC : 0 ≤ 2 * M * L := mul_nonneg (mul_nonneg (by norm_num) hM)
      ((show (0 : ℝ) ≤ 1 by norm_num).trans hLog)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hUpperE).trans_eq (ENNReal.toReal_ofReal hC)
  have hLower := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hs)).mp
    (hMono.trans (div_le_div_of_nonneg_right hU hR.le))
  rw [hEq] at hLower
  have hF : (∫ x in ball c (2 * s), F x) ≤ (4 * M * s / R) * L := by
    apply hLower.trans_eq
    ring
  obtain ⟨lo, hlo, hi, hhi, hEnd⟩ := exists_good_classical_endHeights a ε B c hΩ hQ hs hr hΩB
  refine ⟨lo, hlo, hi, hhi, (hEnd.trans (mul_le_mul_of_nonneg_left hF (by positivity))).trans_eq ?_⟩
  field_simp [hR.ne', hs.ne']
  ring

end Thesis.MeasureGeometry
