module

public import Thesis.Upstream.PoissonL4Potential
import HolderToCK.Analysis.Poisson.RadialPowerDerivatives
import HolderToCK.Analysis.Poisson.DistributionIdentity
import Thesis.Variational.BoundarySmallEnergy
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Second-order tests for the actual scalar Newtonian potential. -/

public section

noncomputable section

open Filter HarmonicMaps HolderToCK MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology

namespace Thesis

/-- A continuous field on an open set pairs integrably with an actual compact test. -/
theorem integrable_scalar_mul_smooth_test {U : Set Point} (hU : IsOpen U)
    {u φ : Point → ℝ} (hu : ContinuousOn u U) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) :
    Integrable (fun x => u x * φ x) volume := by
  have hC : Continuous (fun x => u x * φ x) := continuous_iff_continuousAt.mpr fun x => by
    by_cases hx : x ∈ U
    · exact (hu.continuousAt (hU.mem_nhds hx)).mul hφ.continuousAt
    · have hxnot : x ∉ tsupport φ := fun h => hx (hs h)
      have hE : (fun y => u y * φ y) =ᶠ[𝓝 x] (fun _ => 0 : Point → ℝ) := by
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxnot] with y hy
        rw [image_eq_zero_of_notMem_tsupport (f := φ) hy, mul_zero]
      exact continuousAt_const.congr hE.symm
  exact hC.integrable_of_hasCompactSupport hc.mul_left

private theorem continuousOn_coordDeriv_scalar_two {U : Set Point} (hU : IsOpen U)
    {u : Point → ℝ} (hu : ContDiffOn ℝ 2 u U) (j : Fin 3) :
    ContDiffOn ℝ 1 (coordDeriv j u) U :=
  (ContinuousLinearMap.apply ℝ ℝ (axis j)).contDiff.comp_contDiffOn
    (hu.fderiv_of_isOpen hU (by norm_num))

private theorem continuousOn_coordDeriv_twice_scalar {U : Set Point} (hU : IsOpen U)
    {u : Point → ℝ} (hu : ContDiffOn ℝ 2 u U) (j : Fin 3) :
    ContinuousOn (coordDeriv j (coordDeriv j u)) U := by
  have h := (continuousOn_coordDeriv_scalar_two hU hu j).continuousOn_fderiv_of_isOpen hU le_rfl
  exact h.clm_apply continuousOn_const

/-- The original classical Laplacian can be moved to a compactly supported
scalar test inside the open carrier. -/
theorem integral_scalar_laplacian_test_eq {U : Set Point} (hU : IsOpen U)
    {u φ : Point → ℝ} (hu : ContDiffOn ℝ 2 u U) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) :
    (∫ x, u x * laplacian φ x) = ∫ x, laplacian u x * φ x := by
  have hφ₁ (j : Fin 3) : ContDiff ℝ ∞ (coordDeriv j φ) :=
    (ContinuousLinearMap.apply ℝ ℝ (axis j)).contDiff.comp (hφ.fderiv_right (by simp))
  have hφ₂ (j : Fin 3) : ContDiff ℝ ∞ (coordDeriv j (coordDeriv j φ)) :=
    (ContinuousLinearMap.apply ℝ ℝ (axis j)).contDiff.comp ((hφ₁ j).fderiv_right (by simp))
  have hCompact₁ (j : Fin 3) : HasCompactSupport (coordDeriv j φ) := hc.fderiv_apply ℝ (axis j)
  have hCompact₂ (j : Fin 3) : HasCompactSupport (coordDeriv j (coordDeriv j φ)) :=
    (hCompact₁ j).fderiv_apply ℝ (axis j)
  have hSupp₁ (j : Fin 3) : tsupport (coordDeriv j φ) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ (axis j)).trans hs
  have hSupp₂ (j : Fin 3) : tsupport (coordDeriv j (coordDeriv j φ)) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ (axis j)).trans (hSupp₁ j)
  have hI₁ (j : Fin 3) : Integrable (fun x => u x * coordDeriv j (coordDeriv j φ) x) volume :=
    integrable_scalar_mul_smooth_test hU hu.continuousOn (hφ₂ j).continuous (hCompact₂ j) (hSupp₂ j)
  have hI₂ (j : Fin 3) : Integrable (fun x => coordDeriv j u x * coordDeriv j φ x) volume :=
    integrable_scalar_mul_smooth_test hU (continuousOn_coordDeriv_scalar_two hU hu j).continuousOn
      (hφ₁ j).continuous (hCompact₁ j) (hSupp₁ j)
  have hI₃ (j : Fin 3) : Integrable (fun x => coordDeriv j (coordDeriv j u) x * φ x) volume :=
    integrable_scalar_mul_smooth_test hU (continuousOn_coordDeriv_twice_scalar hU hu j)
      hφ.continuous hc hs
  have hPart (j : Fin 3) :
      (∫ x, u x * coordDeriv j (coordDeriv j φ) x) = ∫ x, coordDeriv j (coordDeriv j u) x * φ x := by
    have hA : (∫ x, u x * coordDeriv j (coordDeriv j φ) x) =
        -(∫ x, coordDeriv j u x * coordDeriv j φ x) :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := axis j) (hI₂ j) (hI₁ j)
        (integrable_scalar_mul_smooth_test hU hu.continuousOn (hφ₁ j).continuous (hCompact₁ j) (hSupp₁ j))
        (fun x hx => ((hu x (hSupp₁ j hx)).contDiffAt (hU.mem_nhds (hSupp₁ j hx))).differentiableAt two_ne_zero)
        (fun x _ => (hφ₁ j).differentiable (by simp) x)
    have hB : (∫ x, coordDeriv j u x * coordDeriv j φ x) =
        -(∫ x, coordDeriv j (coordDeriv j u) x * φ x) :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := axis j) (hI₃ j) (hI₂ j)
        (integrable_scalar_mul_smooth_test hU (continuousOn_coordDeriv_scalar_two hU hu j).continuousOn
          hφ.continuous hc hs)
        (fun x hx => (((continuousOn_coordDeriv_scalar_two hU hu j) x (hs hx)).contDiffAt
          (hU.mem_nhds (hs hx))).differentiableAt one_ne_zero)
        (fun x _ => hφ.differentiable (by simp) x)
    rw [hA, hB, neg_neg]
  simp only [laplacian, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hI₁ i), integral_finsetSum _ (fun i _ => hI₃ i)]
  exact Finset.sum_congr rfl fun j _ => hPart j

/-- The positive normalized inverse-distance kernel in three dimensions. -/
@[expose] def newtonianKernelThree (z : Point) : ℝ :=
  (euclideanSphereArea 3)⁻¹ * poissonInversePower 1 z

theorem newtonianKernelThree_nonneg (z : Point) : 0 ≤ newtonianKernelThree z :=
  mul_nonneg (inv_nonneg.mpr (euclideanSphereArea_pos (by decide)).le) (poissonInversePower_nonneg _ _)

theorem measurable_newtonianKernelThree : Measurable newtonianKernelThree :=
  measurable_const.mul (measurable_poissonInversePower 1)

theorem scalar_laplacian_eq_mathlib_of_smooth {φ : Point → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Point) :
    Laplacian.laplacian φ x = laplacian φ x :=
  scalar_laplacian_coordinateSum φ x hφ.contDiffAt

/-- The translated positive kernel has distributional Laplacian (-\delta_z). -/
theorem integral_newtonianKernelThree_laplacian_test (z : Point)
    {φ : Point → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, newtonianKernelThree (x-z) * laplacian φ x) = -φ z := by
  let ψ (x : Point) := φ (z+x)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_const.add contDiff_id)
  have hψC : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.addLeft z)
  have hΔ (x : Point) : laplacian ψ x = laplacian φ (z+x) := by
    simpa only [one_smul, one_pow] using laplacian_affine_dilation isOpen_univ
      ((hφ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn) z 1 (y := x) (mem_univ _)
  have h := fundamentalPower_distributionPairing (by decide : 3 ≤ 3)
    (hψ.of_le (WithTop.coe_le_coe.mpr le_top)) hψC
  simp_rw [scalar_laplacian_eq_mathlib_of_smooth hψ, hΔ, fundamentalPowerExpression_three] at h
  have hNeg (x : Point) : -(euclideanSphereArea 3)⁻¹ * poissonInversePower 1 x * laplacian φ (z+x) =
      -(newtonianKernelThree x * laplacian φ (z+x)) := by
    simp only [newtonianKernelThree, neg_mul]
  simp_rw [hNeg, integral_neg] at h
  have htr := integral_add_left_eq_self (μ := (volume : Measure Point))
    (fun x => newtonianKernelThree (x-z) * laplacian φ x) z
  have he (x : Point) : z + x - z = x := by abel
  simp only [he] at htr
  refine htr.symm.trans ?_
  simp only [ψ, add_zero] at h
  linarith only [h]

/-- Taking the coordinate Laplacian preserves the support restriction. -/
theorem laplacian_test_tsupport_subset {φ : Point → ℝ} :
    tsupport (laplacian φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro x hx
  by_contra h
  refine hx ?_
  unfold laplacian
  apply Finset.sum_eq_zero
  intro j _
  have hS := (tsupport_fderiv_apply_subset ℝ (f := φ) (axis j))
  exact DFunLike.congr_fun (fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := coordDeriv j φ)
    (fun h' => h (hS h'))) (axis j)

/-- The coordinate Laplacian of a smooth test is continuous. -/
theorem continuous_laplacian_test {φ : Point → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (laplacian φ) := by
  unfold laplacian
  apply continuous_finsetSum Finset.univ
  intro j _
  have h (f : Point → ℝ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (coordDeriv j f) :=
    (ContinuousLinearMap.apply ℝ ℝ (axis j)).contDiff.comp (hf.fderiv_right (by simp))
  exact (h _ (h _ hφ)).continuous

private theorem exists_newtonianKernelThree_test_integral_bound {φ : Point → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {R : ℝ} (hR : 0 < R)
    (hS : tsupport φ ⊆ ball (0 : Point) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closedBall (0 : Point) R,
      Integrable (fun x => newtonianKernelThree (x-z) * laplacian φ x) volume ∧
        (∫ x, ‖newtonianKernelThree (x-z) * laplacian φ x‖) ≤ C := by
  let U := ball (0 : Point) R
  let μ := (volume : Measure Point).restrict U
  let κ := (euclideanSphereArea 3)⁻¹
  have hκ : 0 ≤ κ := inv_nonneg.mpr (euclideanSphereArea_pos (by decide)).le
  have hSupp : tsupport (laplacian φ) ⊆ U := laplacian_test_tsupport_subset.trans hS
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : Point) R).exists_bound_of_continuousOn
    (continuous_laplacian_test hφ).continuousOn
  obtain ⟨L, hL, hLP⟩ := exists_poissonInversePower_conjugate_bound 1 (by norm_num)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let M := (eLpNorm (fun _ : Point => (1 : ℝ)) 4 μ).toReal
  let C := κ * max A 0 * (L * R ^ (9/4 - 1 : ℝ) * M)
  refine ⟨C, by dsimp only [C]; positivity, fun z hz => ?_⟩
  have hK := hLP 0 z R hR hz
  have hJ (x : Point) : newtonianKernelThree (x-z) = κ * poissonInversePower 1 (z-x) := by
    unfold newtonianKernelThree poissonInversePower
    rw [norm_sub_rev]
  have hI := (hK.1.integrable (by unfold poissonL4Conjugate; norm_num)).const_mul (κ*max A 0)
  have he (x : Point) (hx : x ∉ U) : newtonianKernelThree (x-z)*laplacian φ x = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hSupp h)), mul_zero]
  have hB : Integrable (fun x => newtonianKernelThree (x-z) * laplacian φ x) μ := by
    apply hI.mono'
      ((measurable_newtonianKernelThree.comp (continuous_id.sub continuous_const).measurable).aestronglyMeasurable.mul
        (continuous_laplacian_test hφ).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    change ‖newtonianKernelThree (x-z) * laplacian φ x‖ ≤ _
    rw [hJ, norm_mul, Real.norm_of_nonneg (mul_nonneg hκ (poissonInversePower_nonneg _ _))]
    have hF := hA x (ball_subset_closedBall hx)
    exact (mul_le_mul_of_nonneg_left (hF.trans (le_max_left _ _)) (mul_nonneg hκ (poissonInversePower_nonneg _ _))).trans_eq (by ring)
  refine ⟨(integrableOn_iff_integrable_of_support_subset (fun x hx => by
    by_contra hn; exact hx (he x hn))).1 hB, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [he x hx, norm_zero])]
  have hh := integral_mono_ae hB.norm hI ?_
  · have hNorm := integral_poissonL4_product_le
      (show MemLp (fun _ : Point => (1 : ℝ)) 4 μ from memLp_const 1)
      hK.1 (Eventually.of_forall fun _ => poissonInversePower_nonneg _ _)
    simp only [norm_one, mul_one] at hNorm
    have hhK := hNorm.trans (mul_le_mul_of_nonneg_right hK.2 ENNReal.toReal_nonneg)
    rw [integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hhK (mul_nonneg hκ (le_max_right _ _)))
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [hJ, norm_mul, Real.norm_of_nonneg (mul_nonneg hκ (poissonInversePower_nonneg _ _))]
    have hF := hA x (ball_subset_closedBall hx)
    exact (mul_le_mul_of_nonneg_left (hF.trans (le_max_left _ _)) (mul_nonneg hκ (poissonInversePower_nonneg _ _))).trans_eq (by ring)

/-- The actual potential of an integrable bounded-carrier source has the
expected distributional pairing, including when the source is pushed onto
Kelvin image points. -/
theorem newtonianKernelThree_source_laplacian_test {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} [SFinite μ] (z : Y → Point) (hz : Measurable z)
    {B : ℝ} (hB : ∀ᵐ y ∂μ, ‖z y‖ ≤ B)
    {F : Y → ℝ} (hF : Integrable F μ)
    {φ : Point → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => (∫ y, newtonianKernelThree (x-z y)*F y ∂μ) * laplacian φ x) volume ∧
      (∫ x, (∫ y, newtonianKernelThree (x-z y)*F y ∂μ) * laplacian φ x) =
        -∫ y, φ (z y) * F y ∂μ := by
  let G (p : Y × Point) := newtonianKernelThree (p.2-z p.1) * F p.1 * laplacian φ p.2
  have hG : AEStronglyMeasurable G (μ.prod volume) := by
    have h₁ : Measurable (fun p : Y × Point => newtonianKernelThree (p.2-z p.1)) :=
      measurable_newtonianKernelThree.comp (measurable_snd.sub (hz.comp measurable_fst))
    have h₂ := hF.aestronglyMeasurable.comp_fst (ν := (volume : Measure Point))
    exact (h₁.aestronglyMeasurable.mul h₂).mul
      ((continuous_laplacian_test hφ).measurable.comp measurable_snd).aestronglyMeasurable
  obtain ⟨R₀, hR₀⟩ := hc.isBounded.subset_closedBall (0 : Point)
  let R := max 1 (max R₀ B+1)
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hRS : tsupport φ ⊆ ball (0 : Point) R :=
    hR₀.trans (closedBall_subset_ball ((le_max_left R₀ B).trans_lt (lt_add_one _) |>.trans_le (le_max_right _ _)))
  have hRB : B ≤ R := (le_max_right R₀ B).trans
    ((le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (le_max_right _ _))
  obtain ⟨C, hC, h⟩ := exists_newtonianKernelThree_test_integral_bound hφ hR hRS
  have hPair : ∀ᵐ y ∂μ, Integrable (fun x => G (y,x)) volume ∧
      (∫ x, ‖G (y,x)‖) ≤ C*‖F y‖ := by
    filter_upwards [hB] with y hy
    obtain ⟨hi, hb⟩ := h (z y) (mem_closedBall_zero_iff.2 (hy.trans hRB))
    have he (x : Point) : G (y,x) = (newtonianKernelThree (x-z y)*laplacian φ x)*F y := by
      dsimp only [G]
      ring
    refine ⟨hi.mul_const _ |>.congr (Eventually.of_forall fun x => (he x).symm), ?_⟩
    have hNorm (x : Point) : ‖G (y,x)‖ = ‖newtonianKernelThree (x-z y)*laplacian φ x‖ * ‖F y‖ := by
      rw [he, norm_mul]
    simp_rw [hNorm, integral_mul_const]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have hInt : Integrable G (μ.prod volume) := (integrable_prod_iff hG).2
    ⟨hPair.mono fun _ h => h.1, (hF.norm.const_mul C).mono'
      (hG.norm.integral_prod_right') (hPair.mono fun y hy => by
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        exact hy.2)⟩
  have hExt (x : Point) : (∫ y, newtonianKernelThree (x-z y)*F y ∂μ) * laplacian φ x =
      ∫ y, G (y,x) ∂μ := (integral_mul_const _ _).symm
  refine ⟨hInt.integral_prod_right.congr (Eventually.of_forall fun x => (hExt x).symm), ?_⟩
  calc
    _ = ∫ x, ∫ y, G (y,x) ∂μ := integral_congr_ae (Eventually.of_forall hExt)
    _ = ∫ p, G p ∂μ.prod volume := (integral_prod_symm G hInt).symm
    _ = ∫ y, (∫ x, G (y,x)) ∂μ := integral_prod G hInt
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae (Eventually.of_forall fun y => ?_)
      have he (x : Point) : G (y,x) = (newtonianKernelThree (x-z y)*laplacian φ x)*F y := by
        dsimp only [G]
        ring
      simp_rw [he, integral_mul_const, integral_newtonianKernelThree_laplacian_test (z y) hφ hc, neg_mul]

end Thesis

end
