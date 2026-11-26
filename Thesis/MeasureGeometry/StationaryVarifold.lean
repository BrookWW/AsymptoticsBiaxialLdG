module

public import Thesis.MeasureGeometry.ApproximateTangent
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Stationarity of the varifold induced by the rectifiable stress. -/

public section

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff Convolution ENNReal Matrix Matrix.Norms.Frobenius Pointwise
  Topology

namespace Thesis.MeasureGeometry

noncomputable local instance stationaryVarifoldContinuousENorm : ContinuousENorm Tensor :=
  @SeminormedAddGroup.toContinuousENorm Tensor inferInstance

/-- A compactly supported `C¹` test has smooth approximations with support in
the same open domain and uniform error in its Fréchet derivative. -/
theorem exists_smooth_test_approx_fderiv {Ω : Set Point} (hΩ : IsOpen Ω) {X : Point → Point}
    (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) (hXΩ : tsupport X ⊆ Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : Point → Point, ContDiff ℝ ∞ Y ∧ HasCompactSupport Y ∧ tsupport Y ⊆ Ω ∧
      ∀ y, ‖fderiv ℝ Y y - fderiv ℝ X y‖ ≤ ε := by
  let D := fderiv ℝ X
  have hD : Continuous D := hX.continuous_fderiv one_ne_zero
  have hDu : UniformContinuous D := (hXc.fderiv ℝ).uniformContinuous_of_continuous hD
  obtain ⟨a, ha, hDa⟩ := Metric.uniformContinuous_iff.1 hDu ε hε
  obtain ⟨b, hb, hKb⟩ := hXc.isCompact.exists_cthickening_subset_open hΩ hXΩ
  let t := min a b
  have ht : 0 < t := lt_min ha hb
  let χ : ContDiffBump (0 : Point) := ⟨t / 2, t, half_pos ht, half_lt_self ht⟩
  let L : ℝ →L[ℝ] Point →L[ℝ] Point := ContinuousLinearMap.lsmul ℝ ℝ
  let Y := χ.normed volume ⋆[L, volume] X
  have hY : ContDiff ℝ ∞ Y := χ.hasCompactSupport_normed.contDiff_convolution_left L
    (χ.contDiff_normed (n := ⊤)) hX.continuous.locallyIntegrable
  have hYc : HasCompactSupport Y := χ.hasCompactSupport_normed.convolution L hXc
  have hB : IsCompact (closedBall (0 : Point) t + tsupport X) :=
    (isCompact_closedBall _ _).add hXc.isCompact
  have hYs : tsupport Y ⊆ closedBall (0 : Point) t + tsupport X := by
    apply closure_minimal _ hB.isClosed
    refine (support_convolution_subset L).trans (add_subset_add ?_ (subset_tsupport X))
    exact χ.support_normed_eq.subset.trans ball_subset_closedBall
  have hYΩ : tsupport Y ⊆ Ω := by
    refine hYs.trans (Subset.trans ?_ hKb)
    rintro _ ⟨u, hu, v, hv, rfl⟩
    apply mem_cthickening_of_dist_le (u + v) v b (tsupport X) hv
    rw [dist_eq_norm, add_sub_cancel_right]
    exact (mem_closedBall_zero_iff.1 hu).trans (min_le_right a b)
  refine ⟨Y, hY, hYc, hYΩ, ?_⟩
  intro y
  have hDeriv : fderiv ℝ Y y =
      ((χ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] D) y) := by
    rw [(hXc.hasFDerivAt_convolution_right L χ.integrable_normed.locallyIntegrable hX y).fderiv]
    apply integral_congr_ae
    filter_upwards with p
    ext v
    rfl
  rw [hDeriv, ← dist_eq_norm]
  apply ContDiffBump.dist_normed_convolution_le hD.aestronglyMeasurable
  intro z hz
  exact (hDa ((mem_ball.1 hz).trans_le (min_le_left a b))).le

private noncomputable def stressTestPairing (F : Tensor) (D : Point →L[ℝ] Point) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, F i j * D (axis j) i

private theorem norm_directional_entry_le (D : Point →L[ℝ] Point) (i j : Fin 3) :
    ‖D (axis j) i‖ ≤ ‖D‖ := by
  have hAxis : ‖axis j‖ = 1 := by
    change ‖(PiLp.single 2 j (1 : ℝ) : Point)‖ = 1
    rw [PiLp.norm_single 2 (fun _ : Fin 3 => ℝ), norm_one]
  have h := D.le_opNorm (axis j)
  rw [hAxis, mul_one] at h
  exact (PiLp.norm_apply_le (D (axis j)) i).trans h

private theorem norm_stressTestPairing_le (F : Tensor) (D : Point →L[ℝ] Point) :
    ‖stressTestPairing F D‖ ≤ (9 : ℝ) * ‖F‖ * ‖D‖ := by
  unfold stressTestPairing
  calc
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3, F i j * D (axis j) i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, ∑ _ : Fin 3, ‖F‖ * ‖D‖ := by
      apply Finset.sum_le_sum
      intro i _
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (abs_tensor_entry_le_frobenius_norm F i j) (norm_directional_entry_le D i j)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num; ring

private theorem continuous_directional_entry {Z : Type*} [TopologicalSpace Z]
    {D : Z → Point →L[ℝ] Point} (hD : Continuous D) (i j : Fin 3) :
    Continuous (fun y => D y (axis j) i) := by
  let ev : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
  exact ev.continuous.comp ((ContinuousLinearMap.apply ℝ Point (axis j)).continuous.comp hD)

private theorem integrable_stressTestPairing {μ : Measure Point} {F : Point → Tensor}
    (hF : Integrable F μ) {D : Point → Point →L[ℝ] Point} (hD : Continuous D)
    (hDc : HasCompactSupport D) : Integrable (fun y => stressTestPairing (F y) (D y)) μ := by
  obtain ⟨M, hM, hMB⟩ := (hDc.image hD.norm).isBounded.subset_closedBall_lt 0 (0 : ℝ)
  have hB (y : Point) : ‖D y‖ ≤ M := by
    by_cases hy : y ∈ tsupport D
    · have h := hMB (mem_image_of_mem _ hy)
      simpa only [mem_closedBall, Real.dist_eq, sub_zero, abs_norm] using h
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      exact hM.le
  unfold stressTestPairing
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.integrable_comp hF).mul_bdd
    (continuous_directional_entry hD i j).aestronglyMeasurable
    (Eventually.of_forall fun y => (norm_directional_entry_le (D y) i j).trans (hB y))

private theorem stressTestPairing_sub (F : Tensor) (A B : Point →L[ℝ] Point) :
    stressTestPairing F (A - B) = stressTestPairing F A - stressTestPairing F B := by
  simp only [stressTestPairing, _root_.sub_apply, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The distributional zero row divergence law extends to compactly
supported `C¹` tests, keeping their support in the same open domain. -/
theorem rowDivergenceFree_contDiff_one {Ω : Set Point} (hΩ : IsOpen Ω)
    {μ : Measure Point} {F : Point → Tensor} (hF : Integrable F (μ.restrict Ω))
    (hDiv : External.RowDivergenceFree Ω μ F) {X : Point → Point}
    (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) (hXΩ : tsupport X ⊆ Ω) :
    (∫ y in Ω, ∑ i : Fin 3, ∑ j : Fin 3, F y i j * coordDeriv j X y i ∂μ) = 0 := by
  let ξ := μ.restrict Ω
  let I := ∫ y, stressTestPairing (F y) (fderiv ℝ X y) ∂ξ
  let C := 9 * ∫ y, ‖F y‖ ∂ξ
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (integral_nonneg fun _ => norm_nonneg _)
  have hIX := integrable_stressTestPairing hF (hX.continuous_fderiv one_ne_zero) (hXc.fderiv ℝ)
  have hBound (ε : ℝ) (hε : 0 < ε) : ‖I‖ ≤ ε * C := by
    obtain ⟨Y, hY, hYc, hYΩ, hDY⟩ := exists_smooth_test_approx_fderiv hΩ hX hXc hXΩ hε
    have hIY := integrable_stressTestPairing hF (hY.continuous_fderiv (by simp)) (hYc.fderiv ℝ)
    have hZero : (∫ y, stressTestPairing (F y) (fderiv ℝ Y y) ∂ξ) = 0 := hDiv Y hY hYc hYΩ
    let D (y : Point) := fderiv ℝ X y - fderiv ℝ Y y
    have hDNorm (y : Point) : ‖D y‖ ≤ ε := by simpa only [D, norm_sub_rev] using hDY y
    have heq : (∫ y, stressTestPairing (F y) (D y) ∂ξ) = I := by
      simp only [D, stressTestPairing_sub]
      rw [integral_sub hIX hIY, hZero, sub_zero]
    calc
      ‖I‖ = ‖∫ y, stressTestPairing (F y) (D y) ∂ξ‖ := congrArg norm heq.symm
      _ ≤ ∫ y, ‖stressTestPairing (F y) (D y)‖ ∂ξ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (9 * ε) * ‖F y‖ ∂ξ := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (hF.norm.const_mul _)
        apply Eventually.of_forall
        intro y
        refine (norm_stressTestPairing_le _ _).trans ?_
        calc
          _ ≤ (9 : ℝ) * ‖F y‖ * ε :=
            mul_le_mul_of_nonneg_left (hDNorm y) (mul_nonneg (by norm_num) (norm_nonneg (F y)))
          _ = _ := by ring
      _ = ε * C := by rw [integral_const_mul]; dsimp only [C]; ring
  change I = 0
  by_contra hI
  have hIn := norm_pos_iff.2 hI
  have hCp : 0 < C + 1 := add_pos_of_nonneg_of_pos hC zero_lt_one
  let ε := ‖I‖ / (C + 1)
  have hε : 0 < ε := div_pos hIn hCp
  have heq : ε * (C + 1) = ‖I‖ := div_mul_cancel₀ _ hCp.ne'
  exact (hBound ε hε).not_gt ((mul_lt_mul_of_pos_left (lt_add_one C) hε).trans_eq heq)

/-- Sending the interior measure to the point and its stress projection
gives the stationary first-variation identity for the pushforward measure. -/
theorem stationaryVarifold_of_stress_projection {Ω : Set Point} (hΩ : IsOpen Ω)
    {μ : Measure Point} {F : Point → Tensor} (hF : Integrable F (μ.restrict Ω))
    (hDiv : External.RowDivergenceFree Ω μ F) {P : Point → LineProjection} (hP : Measurable P)
    (hEq : (fun x => (P x).val) =ᵐ[μ.restrict Ω] F) :
    IsStationaryVarifold Ω (Measure.map (fun x => (x, P x)) (μ.restrict Ω)) := by
  intro X hX hXc hXΩ
  letI : BorelSpace LineProjection := ⟨rfl⟩
  let ξ := μ.restrict Ω
  let w (y : Point × LineProjection) :=
    ∑ i : Fin 3, ∑ j : Fin 3, y.2.val i j * coordDeriv i X y.1 j
  have hD : Continuous (fun y : Point × LineProjection => fderiv ℝ X y.1) :=
    (hX.continuous_fderiv one_ne_zero).comp continuous_fst
  have hw : Continuous w := by
    unfold w
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.continuous).comp
      (continuous_subtype_val.comp continuous_snd)).mul (continuous_directional_entry hD j i)
  have hMap : Measurable (fun x => (x, P x)) := measurable_id.prodMk hP
  change (∫ y, w y ∂(Measure.map (fun x => (x, P x)) ξ)) = 0
  rw [integral_map hMap.aemeasurable hw.aestronglyMeasurable]
  refine (integral_congr_ae ?_).trans
    (rowDivergenceFree_contDiff_one hΩ hF hDiv hX hXc hXΩ)
  filter_upwards [hEq] with x hx
  change (∑ i : Fin 3, ∑ j : Fin 3, (P x).val i j * coordDeriv i X x j) =
    ∑ i : Fin 3, ∑ j : Fin 3, F x i j * coordDeriv j X x i
  have hSymm (i j : Fin 3) : (P x).val j i = (P x).val i j :=
    congrArg (fun A : Tensor => A i j) (P x).property.1
  rw [Finset.sum_comm]
  change (P x).val = F x at hx
  simp only [hSymm, hx]

/-- The rectifiable stress gives an associated stationary varifold with the
original interior energy measure and the original Hausdorff carrier and weight. -/
theorem exists_associated_stationary_varifold_of_rectifiable_stress {Ω S : Set Point}
    (hΩ : IsOpen Ω) (hS : MeasurableSet S) (hRect : CountablyRectifiableOne S)
    (hfin : HausdorffOne S < ⊤)
    {μ : Measure Point} {F : Point → Tensor} (hF : Integrable F (μ.restrict Ω))
    (hDiv : External.RowDivergenceFree Ω μ F) {θ : Point → ℝ≥0∞}
    (hθ : Measurable θ) (hθfin : (∫⁻ y, θ y ∂HausdorffOne.restrict S) < ⊤)
    (hRep : μ.restrict Ω = (HausdorffOne.restrict S).withDensity θ)
    (hProj : ∀ᵐ x ∂μ.restrict Ω, (F x)ᵀ = F x ∧ F x * F x = F x ∧ (F x).rank = 1) :
    ∃ V : Measure (Point × LineProjection),
      IsAssociatedVarifold Ω S μ V ∧ IsStationaryVarifold Ω V := by
  obtain ⟨P, hP, hEq, hV⟩ := exists_associatedVarifold_with_stress_projection
    hΩ hS hRect hfin hF hDiv hθ hθfin hRep hProj
  exact ⟨_, hV, stationaryVarifold_of_stress_projection hΩ hF hDiv hP hEq⟩

/-- On the interior support, the A-free rectifiable representation and the
zero-divergence stress together produce the stationary varifold. -/
theorem stationary_rectifiable_varifold_of_A19 (hA19 : External.A19Prop31)
    {Ω : Set Point} (hΩ : IsOpen Ω) (μ : FiniteMeasure Point) (F : Point → Tensor)
    (hF : Integrable F ((μ : Measure Point).restrict Ω))
    (hDiv : External.RowDivergenceFree Ω μ F)
    (hB : ∀ᵐ x ∂((μ : Measure Point).restrict Ω), (F x)ᵀ = F x ∧ 1 ≤ (F x).trace ∧ ‖F x‖ ≤ 2 ∧
      ∀ z : Point, tensorQuadratic (F x) z ≤ ‖z‖ ^ 2)
    {η : ℝ} (hη : 0 < η)
    (hD : ∀ x ∈ Ω ∩ (μ : Measure Point).support,
      ∃ θ ≥ η / 2, Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ)) :
    let S := Ω ∩ (μ : Measure Point).support
    CountablyRectifiableOne S ∧ HausdorffOne S < ⊤ ∧
      ∃ V : Measure (Point × LineProjection),
        IsAssociatedVarifold Ω S μ V ∧ IsStationaryVarifold Ω V := by
  obtain ⟨hR, hLen, ⟨θ, hθ, hθfin, hRep⟩, _, hProj⟩ :=
    rectifiable_interior_support_of_A19 hA19 hΩ μ F hF hDiv hB hη hD
  refine ⟨hR, hLen, exists_associated_stationary_varifold_of_rectifiable_stress
    hΩ ?_ hR hLen hF hDiv hθ hθfin hRep ?_⟩
  · exact hΩ.measurableSet.inter (μ : Measure Point).isClosed_support.measurableSet
  · exact hProj.mono fun _ ⟨hs, hP, hr, _⟩ => ⟨hs, hP, hr⟩

end Thesis.MeasureGeometry

end
