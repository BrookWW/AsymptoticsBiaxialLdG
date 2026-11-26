module

public import Thesis.MeasureGeometry.RelativeMeridians
public import Thesis.MeasureGeometry.JunctionSphereSelection

/-! The actual small transverse meridian and its linear normal projection. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

/-- Transversality makes the normal derivative of an embedded disk
injective at its actual point of intersection. -/
theorem transverse_meridian_normal_derivative_injective
    (B : OrthonormalBasis (Fin 3) ℝ Point) {d : Plane → Point} (hd : IsSmoothDiskEmbedding d)
    {y : Plane} (hy : y ∈ ball (0 : Plane) 1)
    (hTrans : B 2 ∉ LinearMap.range (fderiv ℝ d y).toLinearMap) :
    Function.Injective ((axisChartTransverseCoordinates B).comp (fderiv ℝ d y)) := by
  let D := fderiv ℝ d y
  let A := (axisChartTransverseCoordinates B).comp D
  have hDisk : Disk ∈ 𝓝 y := mem_of_superset (isOpen_ball.mem_nhds hy) ball_subset_closedBall
  have hD : Function.Injective D := by
    have h := hd.2.2 y (ball_subset_closedBall hy)
    rwa [fderivWithin_of_mem_nhds hDisk] at h
  have hZero (v : Plane) (h : A v = 0) : v = 0 := by
    have hL : D v ∈ Submodule.span ℝ {B 2} :=
      (axisChartTransverseCoordinates_eq_zero_iff B (D v)).mp h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hL
    by_cases hz : c = 0
    · have hV : D v = D 0 := by rw [map_zero, ← hc, hz, zero_smul]
      exact hD hV
    · exfalso
      apply hTrans
      refine ⟨c⁻¹ • v, ?_⟩
      change D (c⁻¹ • v) = B 2
      rw [map_smul, ← hc, smul_smul, inv_mul_cancel₀ hz, one_smul]
  intro v w h
  apply sub_eq_zero.mp
  apply hZero
  rw [map_sub, h, sub_self]

private theorem exists_positive_lower_norm_on_nativeCircle (A : Plane →L[ℝ] Plane)
    (hA : Function.Injective A) : ∃ m > (0 : ℝ), ∀ z : NativeCircle, m ≤ ‖A z.val‖ := by
  have hP (z : Plane) (hz : z ∈ sphere (0 : Plane) 1) : 0 < ‖A z‖ := by
    have hNorm := mem_sphere_zero_iff_norm.mp hz
    have hne : z ≠ 0 := by intro h; rw [h, norm_zero] at hNorm; norm_num at hNorm
    exact norm_pos_iff.mpr fun h => hne (hA (h.trans A.map_zero.symm))
  obtain ⟨m, hm, hL⟩ := (isCompact_sphere (0 : Plane) 1).exists_forall_le'
    A.continuous.norm.continuousOn hP
  exact ⟨m, hm, fun z => hL z.val z.property⟩

/-- A sufficiently small actual meridian of the transverse disk is
freely homotopic to its linear normal ellipse whenever both boundaries
avoid the point singularities. The annulus is perturbed relative to both
boundary curves inside the same line-free region. -/
theorem exists_small_meridian_homotopy_to_normal_ellipse
    (hAvoid : External.RelativeAnnulusPointAvoidance) (a : BulkCoefficients)
    {Ω S Spt : Set Point} (hΩ : IsOpen Ω) (hS : IsClosed S)
    (hLoc : LocallyFiniteIn (Ω \ S) Spt) {Q : Point → S0}
    (hQ : ContinuousOn Q ((Ω \ S) \ Spt)) (hVac : MapsTo Q ((Ω \ S) \ Spt) (vacuum a))
    (B : OrthonormalBasis (Fin 3) ℝ Point) {d : Plane → Point} (hd : IsSmoothDiskEmbedding d)
    {y : Plane} (hy : y ∈ ball (0 : Plane) 1)
    (hTrans : B 2 ∉ LinearMap.range (fderiv ℝ d y).toLinearMap)
    {R : ℝ} (hR : 0 < R) (hBΩ : ball (d y) R ⊆ Ω)
    (hGerm : ∀ x ∈ ball (d y) R, x ∈ S ↔ axisChartTransverseCoordinates B (x - d y) = 0) :
    let A := (axisChartTransverseCoordinates B).comp (fderiv ℝ d y)
    ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      ‖y‖ + δ ≤ 1 ∧
      ((∀ z : NativeCircle, d (y + δ • z.val) ∉ Spt ∧
        d y + δ • axisChartPlane B (A z.val) ∉ Spt) →
      ∀ b₀ b₁ : C(NativeCircle, vacuum a),
        (∀ z, (b₀ z).val = Q (d (y + δ • z.val))) →
        (∀ z, (b₁ z).val = Q (d y + δ • axisChartPlane B (A z.val))) →
        b₀.Homotopic b₁) := by
  intro A
  let N := axisChartTransverseCoordinates B
  let x := d y
  have hAi : Function.Injective A := transverse_meridian_normal_derivative_injective B hd hy hTrans
  obtain ⟨m, hm, hL⟩ := exists_positive_lower_norm_on_nativeCircle A hAi
  have hCont : ContDiffAt ℝ 1 d y := ((hd.1.of_le (by decide)) y (ball_subset_closedBall hy)).contDiffAt
    (mem_of_superset (isOpen_ball.mem_nhds hy) ball_subset_closedBall)
  have hD : HasFDerivAt d (fderiv ℝ d y) y := (hCont.differentiableAt one_ne_zero).hasFDerivAt
  have hF : HasFDerivAt (N ∘ d) A y := N.hasFDerivAt.comp y hD
  have hErr := hF.isLittleO.def (half_pos hm)
  have hAE : ∀ᶠ z in 𝓝 y, ‖N (d z - x) - A (z - y)‖ ≤ (m / 2) * ‖z - y‖ := by
    filter_upwards [hErr] with z hz
    simpa only [map_sub, Function.comp_apply, x] using hz
  obtain ⟨δE, hδE, hErrBall⟩ := Metric.mem_nhds_iff.mp hAE
  have hDBall : d ⁻¹' ball x R ∈ 𝓝 y :=
    hCont.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hR))
  obtain ⟨δD, hδD, hδDB⟩ := Metric.mem_nhds_iff.mp hDBall
  have hy₁ : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
  let δ₀ := min (1 - ‖y‖) (min δE (min δD (R / (‖A‖ + 1))))
  have hδ₀ : 0 < δ₀ := lt_min (sub_pos.mpr hy₁) (lt_min hδE (lt_min hδD (div_pos hR (by positivity))))
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ
  have hδY : δ < 1 - ‖y‖ := hδ.2.trans_le (min_le_left _ _)
  have hδE' : δ < δE := hδ.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδD' : δ < δD := hδ.2.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδR : δ < R / (‖A‖ + 1) := hδ.2.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hδDisk : ‖y‖ + δ ≤ 1 := by linarith only [hδY]
  refine ⟨hδDisk, ?_⟩
  intro hEnd b₀ b₁ hb₀ hb₁
  let Y (z : NativeCircle) := y + δ • z.val
  let P (z : NativeCircle) := x + δ • axisChartPlane B (A z.val)
  have hϱ (z : NativeCircle) : dist (Y z) y = δ := by
    rw [dist_eq_norm]
    change ‖y + δ • z.val - y‖ = δ
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.1.le,
      mem_sphere_zero_iff_norm.mp z.property, mul_one]
  have hYD (z : NativeCircle) : Y z ∈ Disk := by
    apply mem_closedBall_zero_iff.mpr
    exact (norm_add_le _ _).trans (by
      rw [norm_smul, Real.norm_of_nonneg hδ.1.le, mem_sphere_zero_iff_norm.mp z.property, mul_one]
      exact hδDisk)
  have hDsmall (z : NativeCircle) : d (Y z) ∈ ball x R :=
    hδDB (mem_ball.mpr ((hϱ z).trans_lt hδD'))
  have hEsmall (z : NativeCircle) : P z ∈ ball x R := by
    rw [mem_ball, dist_eq_norm]
    change ‖x + δ • axisChartPlane B (A z.val) - x‖ < R
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.1.le, norm_axisChartPlane]
    have hA := A.le_opNorm z.val
    rw [mem_sphere_zero_iff_norm.mp z.property, mul_one] at hA
    exact (mul_le_mul_of_nonneg_left (hA.trans (le_add_of_nonneg_right zero_le_one)) hδ.1.le).trans_lt
      ((lt_div_iff₀ (show 0 < ‖A‖ + 1 by positivity)).mp hδR)
  have hClose (z : NativeCircle) : ‖N (d (Y z) - x) - δ • A z.val‖ ≤ (m / 2) * δ := by
    have h := hErrBall (mem_ball.mpr ((hϱ z).trans_lt hδE'))
    change ‖N (d (Y z) - x) - A (y + δ • z.val - y)‖ ≤ (m / 2) * ‖y + δ • z.val - y‖ at h
    rw [add_sub_cancel_left, map_smul, norm_smul, Real.norm_of_nonneg hδ.1.le,
      mem_sphere_zero_iff_norm.mp z.property, mul_one] at h
    exact h
  let F (p : unitInterval × NativeCircle) :=
    (1 - p.1.val) • d (Y p.2) + p.1.val • P p.2
  have hYcont : Continuous Y := by dsimp only [Y]; fun_prop
  have hDcont : Continuous (fun z => d (Y z)) := hd.1.continuousOn.comp_continuous hYcont hYD
  have hPcts : Continuous P := by dsimp only [P]; fun_prop
  have hST : Continuous (fun p : unitInterval × NativeCircle => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hA : Continuous (fun p : unitInterval × NativeCircle => 1 - p.1.val) := continuous_const.sub hST
  have hFcts : Continuous F :=
    (hA.smul (hDcont.comp continuous_snd)).add (hST.smul (hPcts.comp continuous_snd))
  let H : C(unitInterval × NativeCircle, Point) := ⟨F,hFcts⟩
  have hHF (p : unitInterval × NativeCircle) : H p ∈ ball x R :=
    convex_ball x R (hDsmall p.2) (hEsmall p.2) (sub_nonneg.mpr p.1.property.2) p.1.property.1 (by ring)
  have hProj (p : unitInterval × NativeCircle) :
      N (H p - x) = δ • A p.2.val + (1 - p.1.val) • (N (d (Y p.2) - x) - δ • A p.2.val) := by
    dsimp only [H, ContinuousMap.coe_mk, F, P]
    simp only [map_sub, map_add, map_smul, N, axisChartTransverseCoordinates_axisChartPlane]
    module
  have hAvoidLine (p : unitInterval × NativeCircle) : H p ∈ Ω \ S := by
    refine ⟨hBΩ (hHF p), ?_⟩
    intro hS
    have hZero := (hGerm _ (hHF p)).mp hS
    rw [hProj p] at hZero
    have hEq : δ • A p.2.val =
        -((1 - p.1.val) • (N (d (Y p.2) - x) - δ • A p.2.val)) :=
      eq_neg_of_add_eq_zero_left hZero
    have hNorm := congrArg norm hEq
    have h₀ : 0 ≤ 1 - p.1.val := sub_nonneg.mpr p.1.property.2
    have h₁ : 1 - p.1.val ≤ 1 := sub_le_self _ p.1.property.1
    rw [norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg hδ.1.le,
      Real.norm_of_nonneg h₀] at hNorm
    have hl := mul_le_mul_of_nonneg_left (hL p.2) hδ.1.le
    have hA := mul_le_mul_of_nonneg_left (hClose p.2) h₀
    have hB := mul_le_mul_of_nonneg_right h₁ (mul_nonneg (half_pos hm).le hδ.1.le)
    nlinarith only [hNorm, hl, hA, hB, mul_pos hδ.1 hm]
  have hSmooth : SmoothNativeAnnulus H := by
    let C (t : ℝ) := (circleNativeParam t).val
    let Y' (p : ℝ × ℝ) := y + δ • C p.2
    let P' (p : ℝ × ℝ) := x + δ • axisChartPlane B (A (C p.2))
    have hY' : ContDiff ℝ ∞ Y' := by
      exact contDiff_const.add ((contDiff_circleNativeParam_val_infty.comp contDiff_snd).const_smul δ)
    have hP' : ContDiff ℝ ∞ P' := by
      exact contDiff_const.add (((axisChartPlane B).contDiff.comp
        (A.contDiff.comp (contDiff_circleNativeParam_val_infty.comp contDiff_snd))).const_smul δ)
    have hD' : ContDiffOn ℝ ∞ (fun p => d (Y' p)) (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :=
      hd.1.comp hY'.contDiffOn (fun p _ => hYD (circleNativeParam p.2))
    refine ⟨fun p => (1 - p.1) • d (Y' p) + p.1 • P' p, ?_, fun _ _ => rfl⟩
    exact (((contDiff_const.sub contDiff_fst).contDiffOn).smul hD').add
      (contDiff_fst.contDiffOn.smul hP'.contDiffOn)
  have hH₀ (z : NativeCircle) : H (0,z) = d (Y z) := by simp [H, F]
  have hH₁ (z : NativeCircle) : H (1,z) = P z := by simp [H, F]
  exact nativeVacuum_homotopic_of_regular_annulus hAvoid a (hΩ.sdiff hS) hLoc hQ hVac
    H hSmooth hAvoidLine (fun z => by rw [hH₀, hH₁]; exact hEnd z) b₀ b₁
    (fun z => (hb₀ z).trans (congrArg Q (hH₀ z)).symm)
    (fun z => (hb₁ z).trans (congrArg Q (hH₁ z)).symm)

end Thesis.MeasureGeometry
