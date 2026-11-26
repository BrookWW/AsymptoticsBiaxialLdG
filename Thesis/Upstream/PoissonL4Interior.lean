module

public import Thesis.Upstream.PoissonL4Potential
import Thesis.Upstream.PoissonBoundedForcing
import Thesis.Variational.InteriorDerivativeAlgebra
import Thesis.Variational.BoundaryPoissonEstimate
import Thesis.Variational.BoundarySmallEnergy
import HarmonicMaps.Analysis.SobolevDifference
import HarmonicMaps.Analysis.HarmonicBallMeanValue
import HolderToCK.Analysis.ClassicalEquation
import HolderToCK.Analysis.Poisson.WeakHarmonicSmooth
import HolderToCK.Analysis.Harmonic.UnitC2Bounds

/-! Interior gradient estimates for actual (L^4) forcing and the native weak graph. -/

public section

noncomputable section

open Filter HarmonicMaps HolderToCK MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal NNReal Topology

namespace Thesis

private theorem mixed_coordDeriv_ambient_comm {q : ℕ} {u : Point → Ambient q} {x : Point}
    (hu : ContDiffAt ℝ 2 u x) (i j : Fin 3) :
    coordDeriv i (coordDeriv j u) x = coordDeriv j (coordDeriv i u) x := by
  have hd := (hu.fderiv_right_succ (n := 1)).differentiableAt one_ne_zero
  have h (k : Fin 3) : fderiv ℝ (coordDeriv k u) x =
      (ContinuousLinearMap.apply ℝ (Ambient q) (axis k)).comp (fderiv ℝ (fderiv ℝ u) x) :=
    ((ContinuousLinearMap.apply ℝ (Ambient q) (axis k)).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  change (fderiv ℝ (coordDeriv j u) x) (axis i) = (fderiv ℝ (coordDeriv i u) x) (axis j)
  rw [h j, h i]
  exact hu.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]) (axis i) (axis j)

private theorem laplacian_coordDeriv_ambient_comm {q : ℕ} {U : Set Point} (hU : IsOpen U)
    {Q : Point → Ambient q} (hQ : ContDiffOn ℝ ∞ Q U) {x : Point} (hx : x ∈ U) (i : Fin 3) :
    laplacian (coordDeriv i Q) x = coordDeriv i (laplacian Q) x := by
  unfold laplacian
  have hD (j : Fin 3) := contDiffOn_coordDeriv_infty hU hQ j
  have hDiff (j : Fin 3) : DifferentiableAt ℝ (coordDeriv j (coordDeriv j Q)) x :=
    ((contDiffOn_coordDeriv_infty hU (hD j) j).differentiableOn (by simp) x hx).differentiableAt
      (hU.mem_nhds hx)
  have hSum := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
    (fun j _ => (hDiff j).hasFDerivAt)
  have hSumEq : coordDeriv i (fun y => ∑ j, coordDeriv j (coordDeriv j Q) y) x =
      ∑ j, coordDeriv i (coordDeriv j (coordDeriv j Q)) x := by
    change (fderiv ℝ (fun y => ∑ j, coordDeriv j (coordDeriv j Q) y) x) (axis i) =
      ∑ j, (fderiv ℝ (coordDeriv j (coordDeriv j Q)) x) (axis i)
    rw [hSum.fderiv, sum_apply]
  rw [hSumEq]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hEq : coordDeriv j (coordDeriv i Q) =ᶠ[𝓝 x] coordDeriv i (coordDeriv j Q) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hyQ := (hQ y hy).contDiffAt (hU.mem_nhds hy)
    exact mixed_coordDeriv_ambient_comm (hyQ.of_le (WithTop.coe_le_coe.mpr le_top)) j i
  have he : coordDeriv j (coordDeriv j (coordDeriv i Q)) x =
      coordDeriv j (coordDeriv i (coordDeriv j Q)) x :=
    DFunLike.congr_fun hEq.fderiv_eq (axis j)
  rw [he]
  have hj := ((hD j) x hx).contDiffAt (hU.mem_nhds hx)
  exact mixed_coordDeriv_ambient_comm (hj.of_le (WithTop.coe_le_coe.mpr le_top)) j i

private theorem laplacian_eq_mathlib_ambient {q : ℕ} {u : Point → Ambient q}
    {x : Point} (hu : ContDiffAt ℝ 2 u x) : Laplacian.laplacian u x = laplacian u x :=
  laplacian_eq_coordinateSum_of_contDiffAt_two u x hu

private theorem harmonic_coordinate_laplacian_zero {q : ℕ} {U : Set Point} (hU : IsOpen U)
    {u : Point → Ambient q} (hu : ContDiffOn ℝ ∞ u U)
    (hLap : ∀ x ∈ U, Laplacian.laplacian u x = 0) (i : Fin 3) :
    ContDiffOn ℝ ∞ (coordDeriv i u) U ∧ ∀ x ∈ U, Laplacian.laplacian (coordDeriv i u) x = 0 := by
  have hV := contDiffOn_coordDeriv_infty hU hu i
  refine ⟨hV, fun x hx => ?_⟩
  have hEq : laplacian u =ᶠ[𝓝 x] (fun _ => 0 : Point → Ambient q) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [← laplacian_eq_mathlib_ambient ((hu y hy).contDiffAt (hU.mem_nhds hy) |>.of_le
      (WithTop.coe_le_coe.mpr le_top))]
    exact hLap y hy
  have he : coordDeriv i (laplacian u) x = coordDeriv i (fun _ => 0 : Point → Ambient q) x :=
    DFunLike.congr_fun hEq.fderiv_eq (axis i)
  rw [laplacian_eq_mathlib_ambient ((hV x hx).contDiffAt (hU.mem_nhds hx) |>.of_le
      (WithTop.coe_le_coe.mpr le_top)),
    laplacian_coordDeriv_ambient_comm hU hu hx, he]
  exact DFunLike.congr_fun (hasFDerivAt_const (0 : Ambient q) x).fderiv (axis i)

private theorem norm_fderiv_harmonic_unit_le_gradL2 :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} (H : Point → Ambient q) (B L : ℝ),
      0 ≤ B → 0 ≤ L → ContDiffOn ℝ ∞ H (ball (0 : Point) (5/8)) →
      (∀ x ∈ ball (0 : Point) (5/8), Laplacian.laplacian H x = 0) →
      ∀ g : Point → ℝ, MemLp g 2 (volume.restrict (ball (0 : Point) (1/2))) →
      (eLpNorm g 2 (volume.restrict (ball (0 : Point) (1/2)))).toReal ≤ B →
      (∀ x ∈ ball (0 : Point) (1/2), ‖fderiv ℝ H x‖ ≤ ‖g x‖ + L) →
      ‖fderiv ℝ H 0‖ ≤ C * (B + L) := by
  let U := ball (0 : Point) (5/8)
  let V := ball (0 : Point) (1/2)
  let μ := (volume : Measure Point).restrict V
  let M := (volume : Measure Point).real V
  have hM : 0 < M := ball_volume_real_pos _ (by norm_num)
  let γ := M⁻¹ * Real.sqrt M
  have hγ : 0 ≤ γ := mul_nonneg (inv_nonneg.mpr hM.le) (Real.sqrt_nonneg _)
  let C := Real.sqrt 3 * (γ + 1)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro q H B L hB hL hH hLap g hg hgb hGrad
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hMass : μ.real univ = M := by
    rw [measureReal_def, show μ univ = volume V from Measure.restrict_apply_univ V]
    rfl
  have hMpow : (eLpNorm (fun _ : Point => (1 : ℝ)) 2 μ).toReal = Real.sqrt M := by
    rw [eLpNorm_const' (1 : ℝ) (by norm_num) (by norm_num), ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      show ‖(1 : ℝ)‖ₑ = 1 by simp, ENNReal.toReal_one, one_mul, ENNReal.toReal_ofNat,
      ← Real.sqrt_eq_rpow]
    exact congrArg Real.sqrt hMass
  have hG : (∫ x, ‖g x‖ ∂μ) ≤ Real.sqrt M * B := by
    have hConj : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr (by norm_num)
    have h := integral_norm_mul_le_realLp_mul hConj
      (show MemLp (fun _ : Point => (1 : ℝ)) (ENNReal.ofReal 2) μ from memLp_const 1)
      (show MemLp g (ENNReal.ofReal 2) μ from by simpa only [ENNReal.ofReal_ofNat] using hg)
    simp only [norm_one, one_mul, ENNReal.ofReal_ofNat, hMpow] at h
    exact h.trans (mul_le_mul_of_nonneg_left hgb (Real.sqrt_nonneg _))
  rw [show C*(B+L) = Real.sqrt 3 *((γ+1)*(B+L)) by dsimp only [C]; ring]
  apply norm_linearMap_le_of_columns_bound (M := (γ + 1) * (B + L)) (fderiv ℝ H 0)
    (mul_nonneg (add_nonneg hγ zero_le_one) (add_nonneg hB hL))
  intro i
  obtain ⟨hHi, hLi⟩ := harmonic_coordinate_laplacian_zero isOpen_ball hH hLap i
  have hClose : closedBall (0 : Point) (1/2) ⊆ U := closedBall_subset_ball (by norm_num)
  have hVS : V ⊆ U := ball_subset_closedBall.trans hClose
  have hMean := harmonic_ball_meanValue (by decide : 2 ≤ 3) (0 : Point) ⟨1/2, by norm_num⟩
    U isOpen_ball hClose (coordDeriv i H) hHi (fun x hx => hLi x (hVS hx))
  have hDInt : Integrable (fun x => ‖coordDeriv i H x‖) μ :=
    (((hHi.continuousOn.mono hClose).norm).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  have hGInt : Integrable (fun x => ‖g x‖) μ := hg.norm.integrable (by norm_num)
  have hI : (∫ x, ‖coordDeriv i H x‖ ∂μ) ≤ (∫ x, ‖g x‖ ∂μ) + L * M := by
    have h := integral_mono_ae hDInt (hGInt.add (integrable_const L)) ?_
    · simpa only [Pi.add_apply, integral_add hGInt (integrable_const L), integral_const,
        smul_eq_mul, hMass, mul_comm M L] using h
    · filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet V)] with x hx
      change ‖fderiv ℝ H x (axis i)‖ ≤ ‖g x‖ + L
      exact ((fderiv ℝ H x).le_opNorm _).trans (by
        rw [show ‖axis i‖ = 1 by simp [axis], mul_one]
        exact hGrad x hx)
  change ‖coordDeriv i H 0‖ ≤ _
  rw [hMean, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hM.le)]
  change M⁻¹ * ‖∫ x, coordDeriv i H x ∂μ‖ ≤ _
  have h₁ := (norm_integral_le_integral_norm (fun x => coordDeriv i H x) (μ := μ)).trans hI
  refine (mul_le_mul_of_nonneg_left (h₁.trans (add_le_add hG le_rfl)) (inv_nonneg.mpr hM.le)).trans ?_
  have he : M⁻¹ * (Real.sqrt M * B + L * M) = γ * B + L := by
    dsimp only [γ]
    rw [mul_add, ← mul_assoc, mul_left_comm M⁻¹ L M, inv_mul_cancel₀ hM.ne', mul_one]
  rw [he]
  nlinarith only [mul_nonneg hγ hL, hB]

private theorem norm_fderiv_harmonic_unit_le_value :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} (H : Point → Ambient q) (M : ℝ), 0 ≤ M →
      ContDiffOn ℝ ∞ H (ball (0 : Point) (5/8)) →
      (∀ x ∈ ball (0 : Point) (5/8), Laplacian.laplacian H x = 0) →
      (∀ x ∈ ball (0 : Point) (5/8), ‖H x‖ ≤ M) →
      ‖fderiv ℝ H 0‖ ≤ C * M := by
  obtain ⟨C, hC, h⟩ := harmonic_unit_c2_bounds 3 (by decide) 1 zero_le_one le_rfl
  refine ⟨1 + C, by linarith only [hC], ?_⟩
  intro q H M hM hDiff hL hB
  have hPoint := (h q H M hM hDiff hL hB).1 1 (by norm_num)
    0 (mem_ball_self (by norm_num))
  have h := (show ‖fderiv ℝ H 0‖ ≤ C * M from by simpa only [norm_iteratedFDeriv_one] using hPoint)
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hM)

/-- Both scale-one interior estimates use the same original (L^4) force. -/
theorem exists_unit_interiorPoissonL4_gradient_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} (u f : Point → Ambient q),
      ContDiffOn ℝ 2 u (ball (0 : Point) 1) →
      (∀ x ∈ ball (0 : Point) 1, laplacian u x = f x) →
      MemLp f 4 (volume.restrict (ball (0 : Point) 1)) →
      MemLp (fderiv ℝ u) 2 (volume.restrict (ball (0 : Point) 1)) →
      let F := (eLpNorm f 4 (volume.restrict (ball (0 : Point) 1))).toReal
      let G := (eLpNorm (fderiv ℝ u) 2 (volume.restrict (ball (0 : Point) 1))).toReal
      ‖fderiv ℝ u 0‖ ≤ C * (G + F) ∧
      ∀ M : ℝ, 0 ≤ M → (∀ x ∈ ball (0 : Point) 1, ‖u x‖ ≤ M) →
        ‖fderiv ℝ u 0‖ ≤ C * (M + F) := by
  obtain ⟨CP, hCP, hPotential⟩ := exists_newtonianPotential_L4_ball_bound
  obtain ⟨CG, hCG, hHarmGrad⟩ := norm_fderiv_harmonic_unit_le_gradL2
  obtain ⟨CM, hCM, hHarmVal⟩ := norm_fderiv_harmonic_unit_le_value
  let C := 1 + CG*(1+CP) + CM*(1+CP) + CP
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro q u f hu hEq hf hDu F G
  let V := ball (0 : Point) 1
  let T := ball (0 : Point) (3/4)
  let U := ballDomain (0 : Point) (5/8)
  let g := T.indicator f
  let P := newtonianPotential (by decide : 2 ≤ 3) g
  let H := u - P
  have hTV : T ⊆ V := ball_subset_ball (by norm_num)
  have hUT : U.val ⊆ T := ball_subset_ball (by norm_num)
  have hfT : MemLp f 4 (volume.restrict T) := hf.mono_measure (Measure.restrict_mono_set volume hTV)
  letI : IsFiniteMeasure (volume.restrict T) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hg₂ : MemLp g 2 volume := (memLp_indicator_iff_restrict measurableSet_ball).2
    (hfT.mono_exponent (by norm_num))
  have hgI : Integrable g volume := (integrable_indicator_iff measurableSet_ball).2
    (hfT.integrable (by norm_num))
  have hgC : HasCompactSupport g := by
    apply (isCompact_closedBall (0 : Point) (3/4)).of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closedBall
    exact support_indicator_subset.trans ball_subset_closedBall
  have hScaleB : closedBall (0 : Point) (3/4) ⊆ V := closedBall_subset_ball (by norm_num)
  have hfCont : ContinuousOn (laplacian u) (closedBall (0 : Point) (3/4)) :=
    (Thesis.continuousOn_laplacian_of_contDiffOn_two isOpen_ball hu).mono hScaleB
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (0 : Point) (3/4)).exists_bound_of_continuousOn hfCont
  have hgBound (x : Point) : ‖g x‖ ≤ max B₀ 0 := by
    by_cases hx : x ∈ T
    · rw [show g x = f x from indicator_of_mem hx _, ← hEq x (hTV hx)]
      exact (hB₀ x (ball_subset_closedBall hx)).trans (le_max_left _ _)
    · rw [show g x = 0 from indicator_of_notMem hx _, norm_zero]
      exact le_max_right _ _
  obtain ⟨hPC, hPWeak⟩ := bounded_compact_newtonian_weakGraph hgI hg₂ hgC hgBound
  have hGB : MemLp g 4 (volume.restrict V) := ((memLp_indicator_iff_restrict measurableSet_ball).2 hfT).mono_measure
    Measure.restrict_le_self
  have hGN : (eLpNorm g 4 (volume.restrict V)).toReal ≤ F := by
    have h := eLpNorm_indicator_le (μ := volume.restrict V) (s := T) (p := (4 : ℝ≥0∞)) (f := f)
    exact ENNReal.toReal_mono hf.eLpNorm_ne_top h
  have hgSupp (x : Point) (hx : x ∉ V) : g x = 0 :=
    indicator_of_notMem (fun hxT => hx (hTV hxT)) _
  obtain ⟨hPV, hPP⟩ := hPotential (0 : Point) (r := 1) one_pos g hGB hgSupp
  have hPValue (x : Point) (hx : x ∈ closedBall (0 : Point) 1) : ‖P x‖ ≤ CP * F := by
    have h := hPV x hx
    simp only [Real.one_rpow, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left hGN hCP.le)
  have hFLip : LipschitzOnWith (Real.toNNReal (CP * F)) P (closedBall (0 : Point) 1) :=
    LipschitzOnWith.of_dist_le_mul (fun x hx y hy => by
      rw [Real.coe_toNNReal _ (mul_nonneg hCP.le ENNReal.toReal_nonneg), dist_eq_norm]
      exact (hPP x hx y hy).trans (by
        rw [Real.one_rpow, mul_one]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGN hCP.le) dist_nonneg))
  have hPgrad (x : Point) (hx : x ∈ V) : ‖fderiv ℝ P x‖ ≤ CP*F := by
    have ht : closedBall (0 : Point) 1 ∈ 𝓝 x :=
      mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall
    have h := norm_fderiv_le_of_lipschitzOn ℝ ht hFLip
    rwa [Real.coe_toNNReal _ (mul_nonneg hCP.le ENNReal.toReal_nonneg)] at h
  let Du (x : Point) (i : Fin 3) := fderiv ℝ u x (EuclideanSpace.single i 1)
  let Dp (x : Point) (i : Fin 3) := potentialGradientColumn i g x
  have hUV : U.val ⊆ V := hUT.trans hTV
  have huW : MemW12 U u Du := by
    have hLoc := memW12Loc_of_contDiffOn_one (ballDomain (0 : Point) 1) (hu.of_le (by norm_num))
    exact ⟨hLoc.1.mono hUV,
      (hLoc.2.1 _ (isCompact_closedBall _ _) hScaleB).mono_measure
        (Measure.restrict_mono_set volume (hUT.trans ball_subset_closedBall)),
      fun i => (hLoc.2.2 i _ (isCompact_closedBall _ _) hScaleB).mono_measure
        (Measure.restrict_mono_set volume (hUT.trans ball_subset_closedBall))⟩
  have huL : WeakPoissonOn U Du f :=
    weakPoissonOn_of_contDiffOn_two_of_laplacian_eq U (hu.mono hUV) (fun x hx => by
      rw [laplacian_eq_mathlib_ambient (((hu.mono hUV) x hx).contDiffAt (U.property.mem_nhds hx))]
      exact hEq x (hUV hx))
  have hpW : MemW12 U P Dp := (hPWeak U isBounded_ball).1
  have hpL : WeakPoissonOn U Dp g := (hPWeak U isBounded_ball).2
  have hHloc := (huW.sub hpW).to_memW12Loc
  have hHweak : WeakPoissonOn U (fun x i => Du x i - Dp x i) (fun _ => 0) := by
    apply (huL.sub hpL).congr EventuallyEq.rfl
    filter_upwards [ae_restrict_mem U.property.measurableSet] with x hx
    rw [show g x = f x from indicator_of_mem (hUT hx) _, sub_self]
  obtain ⟨hHs, hHarm⟩ := hHweak.contDiffOn_of_continuous_weak_harmonic (by decide) U hHloc
    ((hu.continuousOn.mono hUV).sub hPC.continuousOn)
  have hPdiff (x : Point) (hx : x ∈ U.val) : DifferentiableAt ℝ P x := by
    have hEq : P = u - H := by dsimp only [H]; abel
    rw [hEq]
    exact ((((hu.mono hUV) x hx).contDiffAt (U.property.mem_nhds hx)).differentiableAt two_ne_zero).sub
      (((hHs x hx).contDiffAt (U.property.mem_nhds hx)).differentiableAt (by simp))
  have hHDer (x : Point) (hx : x ∈ U.val) :
      fderiv ℝ H x = fderiv ℝ u x - fderiv ℝ P x :=
    fderiv_sub ((((hu.mono hUV) x hx).contDiffAt (U.property.mem_nhds hx)).differentiableAt two_ne_zero)
      (hPdiff x hx)
  have h0 : (0 : Point) ∈ U.val := mem_ball_self (by norm_num)
  have hRec : ‖fderiv ℝ u 0‖ ≤ ‖fderiv ℝ H 0‖ + CP*F := by
    have he : fderiv ℝ u 0 = fderiv ℝ H 0 + fderiv ℝ P 0 := by rw [hHDer 0 h0, sub_add_cancel]
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (hPgrad 0 (hUV h0)))
  refine ⟨?_, ?_⟩
  · let A := ball (0 : Point) (1/2)
    have hA : A ⊆ U.val := ball_subset_ball (by norm_num)
    have hA₂ := hDu.mono_measure (Measure.restrict_mono_set volume (hA.trans hUV))
    have hEl : (eLpNorm (fun x => ‖fderiv ℝ u x‖) 2 (volume.restrict A)).toReal ≤ G := by
      rw [eLpNorm_norm]
      exact ENNReal.toReal_mono hDu.eLpNorm_ne_top (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume (hA.trans hUV)))
    have hGradH (x : Point) (hx : x ∈ A) : ‖fderiv ℝ H x‖ ≤ ‖‖fderiv ℝ u x‖‖ + CP*F := by
      rw [hHDer x (hA hx), Real.norm_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl (hPgrad x (hUV (hA hx))))
    have h := hHarmGrad H G (CP*F) ENNReal.toReal_nonneg (mul_nonneg hCP.le ENNReal.toReal_nonneg)
      hHs hHarm _ hA₂.norm hEl hGradH
    have hO := hRec.trans (add_le_add h le_rfl)
    dsimp only [C]
    have hnF : 0 ≤ F := ENNReal.toReal_nonneg
    have hnG : 0 ≤ G := ENNReal.toReal_nonneg
    nlinarith only [hO, mul_nonneg (mul_nonneg hCG.le hCP.le) hnG, mul_nonneg hCG.le hnF,
      mul_nonneg hCP.le hnG, mul_nonneg (mul_nonneg hCM.le (by positivity : 0 ≤ 1+CP)) (add_nonneg hnG hnF),
      hnG, hnF]
  · intro M hM hUb
    have hB (x : Point) (hx : x ∈ U.val) : ‖H x‖ ≤ M + CP*F :=
      (norm_sub_le _ _).trans (add_le_add (hUb x (hUV hx)) (hPValue x (ball_subset_closedBall (hUV hx))))
    have h := hHarmVal H (M + CP*F) (add_nonneg hM (mul_nonneg hCP.le ENNReal.toReal_nonneg)) hHs hHarm hB
    have hO := hRec.trans (add_le_add h le_rfl)
    dsimp only [C]
    have hnF : 0 ≤ F := ENNReal.toReal_nonneg
    nlinarith only [hO, hM, hnF, mul_nonneg (mul_nonneg hCM.le hCP.le) hM, mul_nonneg hCM.le hnF,
      mul_nonneg hCP.le hM, mul_nonneg (mul_nonneg hCG.le (by positivity : 0 ≤ 1+CP)) (add_nonneg hM hnF)]

/-- Derivative of a classical field under spatial affine dilation. -/
theorem fderiv_affine_dilation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : Point → E} (c : Point) (r : ℝ) {x : Point} (hu : DifferentiableAt ℝ u (c+r • x)) :
    fderiv ℝ (fun y => u (c+r • y)) x = r • fderiv ℝ u (c+r • x) := by
  let Z (y : Point) := c+r • y
  have hZ : HasFDerivAt Z (r • ContinuousLinearMap.id ℝ Point) x :=
    ((hasFDerivAt_id x).const_smul r).const_add c
  change fderiv ℝ (u ∘ Z) x = r • fderiv ℝ u (Z x)
  rw [(hu.hasFDerivAt.comp x hZ).fderiv]
  ext y
  rw [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_apply]

/-- The norm of a positively rescaled field on the affine unit ball. -/
theorem eLpNorm_smul_affine_unitBall_toReal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : Point) {r : ℝ} (hr : 0 < r) (k : ℝ) {p : ℝ≥0∞} (hp : p ≠ ⊤)
    (f : Point → E) :
    let Z (x : Point) := c + r • x
    (eLpNorm (r ^ k • (f ∘ Z)) p (volume.restrict (ball (0 : Point) 1))).toReal =
      r ^ (k - 3 * (1/p).toReal) * (eLpNorm f p (volume.restrict (ball c r))).toReal := by
  intro Z
  let F (x : Point) := c + r • (x-0)
  have hZ : Z = F := by funext x; simp only [Z, F, sub_zero]
  have hS : F ⁻¹' ball c r = ball (0 : Point) 1 := by
    ext x
    exact (affineBall_mem_ball_iff c 0 hr r x).trans (by rw [div_self hr.ne'])
  rw [hZ, eLpNorm_const_smul, ← hS, eLpNorm_affine_preimage c 0 hr _ hp, ← ofReal_norm,
    Real.norm_of_nonneg (Real.rpow_nonneg hr.le _), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hr.le _), ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity)]
  rw [Real.inv_rpow (pow_nonneg hr.le 3), ← Real.rpow_natCast_mul hr.le,
    ← Real.rpow_neg hr.le, ← mul_assoc, ← Real.rpow_add hr]
  norm_num only [Nat.cast_ofNat, sub_eq_add_neg]

private theorem eLpNorm_smul_affine_unitBall_comp_memLp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : Point) {r : ℝ} (hr : 0 < r) (k : ℝ) {p : ℝ≥0∞} {f : Point → E}
    (hf : MemLp f p (volume.restrict (ball c r))) :
    let Z (x : Point) := c + r • x
    MemLp (r ^ k • (f ∘ Z)) p (volume.restrict (ball (0 : Point) 1)) := by
  intro Z
  let F (x : Point) := c + r • (x-0)
  have hZ : Z = F := by funext x; simp only [Z, F, sub_zero]
  have hS : F ⁻¹' ball c r = ball (0 : Point) 1 := by
    ext x
    exact (affineBall_mem_ball_iff c 0 hr r x).trans (by rw [div_self hr.ne'])
  rw [hZ, ← hS]
  exact (memLp_affine_preimage c 0 hr (ball c r) hf).const_smul (r ^ k)

/-- The original interior (L^4) forcing controls the centered gradient
on any ball. The two bounds use either the local gradient (L^2) norm or
the value supremum on that same ball. -/
theorem exists_interiorPoissonL4_gradient_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} (c : Point) {r : ℝ}, 0 < r →
      ∀ (u f : Point → Ambient q),
      ContDiffOn ℝ 2 u (ball c r) → (∀ x ∈ ball c r, laplacian u x = f x) →
      MemLp f 4 (volume.restrict (ball c r)) →
      MemLp (fderiv ℝ u) 2 (volume.restrict (ball c r)) →
      let F := (eLpNorm f 4 (volume.restrict (ball c r))).toReal
      let G := (eLpNorm (fderiv ℝ u) 2 (volume.restrict (ball c r))).toReal
      ‖fderiv ℝ u c‖ ≤ C * (r ^ (-3/2 : ℝ) * G + r ^ (1/4 : ℝ) * F) ∧
      ∀ M : ℝ, 0 ≤ M → (∀ x ∈ ball c r, ‖u x‖ ≤ M) →
        ‖fderiv ℝ u c‖ ≤ C * (r⁻¹ * M + r ^ (1/4 : ℝ) * F) := by
  obtain ⟨C, hC, hUnit⟩ := exists_unit_interiorPoissonL4_gradient_bounds
  refine ⟨C, hC, ?_⟩
  intro q c r hr u f hu hEq hf hDu F G
  let Z (x : Point) := c+r • x
  let v := u ∘ Z
  let g := r ^ 2 • (f ∘ Z)
  have hZ : MapsTo Z (ball (0 : Point) 1) (ball c r) := by
    intro x hx
    have h := affineBall_mem_ball_iff c 0 hr r x
    rw [div_self hr.ne', sub_zero] at h
    exact h.2 hx
  have hZC : ContDiff ℝ 2 Z := contDiff_const.add (contDiff_id.const_smul r)
  have hv : ContDiffOn ℝ 2 v (ball (0 : Point) 1) := hu.comp hZC.contDiffOn hZ
  have hvL (x : Point) (hx : x ∈ ball (0 : Point) 1) : laplacian v x = g x := by
    change laplacian (fun y => u (c+r • y)) x = r ^ 2 • f (Z x)
    rw [laplacian_affine_dilation isOpen_ball hu c r (hZ hx), hEq (Z x) (hZ hx)]
  have hDer (x : Point) (hx : x ∈ ball (0 : Point) 1) :
      fderiv ℝ v x = r • fderiv ℝ u (Z x) :=
    fderiv_affine_dilation c r
      (((hu (Z x) (hZ hx)).contDiffAt (isOpen_ball.mem_nhds (hZ hx))).differentiableAt two_ne_zero)
  have hGradEq : fderiv ℝ v =ᵐ[volume.restrict (ball (0 : Point) 1)] r • (fderiv ℝ u ∘ Z) :=
    (ae_restrict_mem measurableSet_ball).mono fun x hx => hDer x hx
  have hg : MemLp g 4 (volume.restrict (ball (0 : Point) 1)) := by
    have h := eLpNorm_smul_affine_unitBall_comp_memLp c hr 2 hf
    simpa only [Real.rpow_two] using h
  have hvD : MemLp (fderiv ℝ v) 2 (volume.restrict (ball (0 : Point) 1)) := by
    have h := eLpNorm_smul_affine_unitBall_comp_memLp c hr 1 hDu
    simp only [Real.rpow_one] at h
    exact h.ae_eq hGradEq.symm
  obtain ⟨hG, hM⟩ := hUnit v g hv hvL hg hvD
  have hD₀ := hDer 0 (mem_ball_self (by norm_num))
  have hD0 : ‖fderiv ℝ v 0‖ = r * ‖fderiv ℝ u c‖ := by
    rw [hD₀, norm_smul, Real.norm_of_nonneg hr.le]
    simp only [Z, smul_zero, add_zero]
  have h2 : (eLpNorm (fderiv ℝ v) 2 (volume.restrict (ball (0 : Point) 1))).toReal =
      r ^ (1-3/2 : ℝ) * G := by
    rw [eLpNorm_congr_ae hGradEq]
    have h := eLpNorm_smul_affine_unitBall_toReal c hr 1 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (fderiv ℝ u)
    dsimp only at h
    rw [Real.rpow_one, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
    rw [show (1-3*(1/2) : ℝ) = 1-3/2 by ring] at h
    exact h
  have h4 : (eLpNorm g 4 (volume.restrict (ball (0 : Point) 1))).toReal = r ^ (5/4 : ℝ) * F := by
    have h := eLpNorm_smul_affine_unitBall_toReal c hr 2 (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) f
    dsimp only at h
    rw [Real.rpow_two, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
    norm_num at h ⊢
    exact h
  have hGpow : r ^ (1-3/2 : ℝ) = r * r ^ (-3/2 : ℝ) := by
    rw [show (1-3/2 : ℝ) = 1+(-3/2) by ring, Real.rpow_add hr, Real.rpow_one]
  have hFpow : r ^ (5/4 : ℝ) = r * r ^ (1/4 : ℝ) := by
    rw [show (5/4 : ℝ) = 1+1/4 by ring, Real.rpow_add hr, Real.rpow_one]
  refine ⟨?_, ?_⟩
  · apply (mul_le_mul_iff_of_pos_left hr).1
    rw [hD0, h2, h4, hGpow, hFpow] at hG
    exact hG.trans_eq (by ring)
  · intro M hM₀ huB
    apply (mul_le_mul_iff_of_pos_left hr).1
    have h := hM M hM₀ (fun x hx => huB (Z x) (hZ hx))
    rw [hD0, h4, hFpow] at h
    exact h.trans_eq (by field_simp)

private def scalarPoissonCoordinate : ℝ →L[ℝ] Ambient 1 :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))

private theorem scalarPoissonCoordinate_norm (u : ℝ) : ‖scalarPoissonCoordinate u‖ = ‖u‖ := by
  change ‖u • PiLp.single 2 (β := fun _ : Fin 1 => ℝ) (0 : Fin 1) (1 : ℝ)‖ = _
  rw [norm_smul, PiLp.norm_single, norm_one, mul_one]

private theorem scalarPoissonCoordinate_comp_norm (T : Point →L[ℝ] ℝ) :
    ‖scalarPoissonCoordinate.comp T‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [ContinuousLinearMap.comp_apply, scalarPoissonCoordinate_norm]
    exact T.le_opNorm x
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [← scalarPoissonCoordinate_norm (T x)]
    exact (scalarPoissonCoordinate.comp T).le_opNorm x

/-- Scalar version of the native interior estimate. -/
theorem exists_scalar_interiorPoissonL4_gradient_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Point) {r : ℝ}, 0 < r →
      ∀ (u f : Point → ℝ),
      ContDiffOn ℝ 2 u (ball c r) → (∀ x ∈ ball c r, laplacian u x = f x) →
      MemLp f 4 (volume.restrict (ball c r)) →
      MemLp (fderiv ℝ u) 2 (volume.restrict (ball c r)) →
      let F := (eLpNorm f 4 (volume.restrict (ball c r))).toReal
      let G := (eLpNorm (fderiv ℝ u) 2 (volume.restrict (ball c r))).toReal
      ‖fderiv ℝ u c‖ ≤ C * (r ^ (-3/2 : ℝ) * G + r ^ (1/4 : ℝ) * F) ∧
      ∀ M : ℝ, 0 ≤ M → (∀ x ∈ ball c r, ‖u x‖ ≤ M) →
        ‖fderiv ℝ u c‖ ≤ C * (r⁻¹ * M + r ^ (1/4 : ℝ) * F) := by
  obtain ⟨C, hC, h⟩ := exists_interiorPoissonL4_gradient_bounds
  refine ⟨C, hC, ?_⟩
  intro c r hr u f hu hEq hf hDu F G
  let L := scalarPoissonCoordinate
  let v := L ∘ u
  let g := L ∘ f
  have hv : ContDiffOn ℝ 2 v (ball c r) := L.contDiff.comp_contDiffOn hu
  have hvL (x : Point) (hx : x ∈ ball c r) : laplacian v x = g x := by
    change laplacian (fun y => L (u y)) x = L (f x)
    rw [laplacian_compCLM isOpen_ball hu hx L, hEq x hx]
  have hD (x : Point) (hx : x ∈ ball c r) : fderiv ℝ v x = L.comp (fderiv ℝ u x) :=
    (L.hasFDerivAt.comp x (((hu x hx).contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt
      two_ne_zero).hasFDerivAt).fderiv
  have hN (x : Point) (hx : x ∈ ball c r) : ‖fderiv ℝ v x‖ = ‖fderiv ℝ u x‖ := by
    rw [hD x hx]
    exact scalarPoissonCoordinate_comp_norm _
  have hh : ∀ᵐ x ∂volume.restrict (ball c r), ‖fderiv ℝ v x‖ = ‖fderiv ℝ u x‖ :=
    (ae_restrict_mem measurableSet_ball).mono fun x hx => hN x hx
  have hGr := eLpNorm_congr_norm_ae (p := 2) hh
  have hDv : MemLp (fderiv ℝ v) 2 (volume.restrict (ball c r)) := by
    refine ⟨(hv.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)).aestronglyMeasurable
      measurableSet_ball, ?_⟩
    rw [hGr]
    exact hDu.eLpNorm_lt_top
  obtain ⟨hG, hM⟩ := h c hr v g hv hvL (hf.continuousLinearMap_comp L) hDv
  have hF : eLpNorm g 4 (volume.restrict (ball c r)) = eLpNorm f 4 (volume.restrict (ball c r)) :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun x => scalarPoissonCoordinate_norm (f x))
  rw [hN c (mem_ball_self hr), hF, hGr] at hG
  refine ⟨hG, ?_⟩
  intro M hM₀ hUb
  have h := hM M hM₀ (fun x hx => (scalarPoissonCoordinate_norm (u x)).le.trans (hUb x hx))
  rwa [hN c (mem_ball_self hr), hF] at h

end Thesis

end
