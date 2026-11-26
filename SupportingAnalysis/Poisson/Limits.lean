module

public import SupportingAnalysis.Poisson.Regularization
import SupportingAnalysis.Poisson.Derivatives
import SupportingAnalysis.Calculus.LineDerivatives
import HolderToCK.Analysis.Poisson.KernelBounds
import HolderToCK.Analysis.Poisson.PotentialHessianIntegrability

/-! Convolution limits of the compact Newtonian cutoffs on smooth inputs and away from support. -/

public section

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff Convolution Topology

set_option autoImplicit false

namespace SupportingAnalysis

private theorem tendsto_inverse_radius : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))

private theorem tendsto_inverse_volume {d : ℕ} (hd : 0 < d) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ d)⁻¹) atTop (𝓝 0) := by
  simpa only [inv_pow, zero_pow hd.ne'] using tendsto_inverse_radius.pow d

private theorem tendsto_convolution_smallDensity {d : ℕ} (k : RadialProbabilityDensity d)
    {f : E d → ℝ} (hf : Continuous f) (x : E d) :
    Tendsto (fun n : ℕ =>
      (k.scaled (((n : ℝ) + 1)⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x) atTop (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.2
  intro δ hδ
  have hClose : ∀ᶠ y in 𝓝 x, dist (f y) (f x) < δ / 2 :=
    hf.continuousAt.eventually (ball_mem_nhds _ (half_pos hδ))
  obtain ⟨ρ, hρ, hNear⟩ := Metric.mem_nhds_iff.mp hClose
  filter_upwards [tendsto_inverse_radius.eventually_lt_const hρ] with n hn
  let ε : ℝ := ((n : ℝ) + 1)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hDis := dist_convolution_le (μ := (volume : Measure (E d))) (g := f) (x₀ := x)
    (z₀ := f x) (ε := δ / 2) (half_pos hδ).le
    (k.scaled_support_subset hε) (k.scaled_nonnegative ε hε) (k.scaled_mass hε)
    hf.aestronglyMeasurable
    (fun y hy => (hNear (show y ∈ ball x ρ from (ball_subset_ball hn.le) hy)).le)
  have hMul : ContinuousLinearMap.lsmul ℝ ℝ = ContinuousLinearMap.mul ℝ ℝ := rfl
  rw [hMul] at hDis
  exact hDis.trans_lt (half_lt_self hδ)

private theorem tendsto_convolution_largeDensity {d : ℕ} (hd : 0 < d)
    (k : RadialProbabilityDensity d) {f : E d → ℝ} (hf : Integrable f) (x : E d) :
    Tendsto (fun n : ℕ =>
      (k.scaled ((n : ℝ) + 1) ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x) atTop (𝓝 0) := by
  have hcd : HasCompactSupport k.density :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E d) 1)
      (k.support_subset.trans ball_subset_closedBall)
  obtain ⟨M, hM⟩ := hcd.exists_bound_of_continuous k.smooth.continuous
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _)
    (g := fun n : ℕ => (((n : ℝ) + 1) ^ d)⁻¹ * (M * ∫ y, ‖f y‖)) ?_ ?_
  · intro n
    let R : ℝ := (n : ℝ) + 1
    have hR : 0 < R := by dsimp [R]; positivity
    change ‖(k.scaled R ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x‖ ≤
      (R ^ d)⁻¹ * (M * ∫ y, ‖f y‖)
    rw [convolution_mul_swap, ← mul_assoc, ← integral_const_mul]
    apply norm_integral_le_of_norm_le (hf.norm.const_mul ((R ^ d)⁻¹ * M))
    exact Eventually.of_forall fun y => by
      rw [norm_mul, RadialProbabilityDensity.scaled, norm_mul,
        Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg hR.le _))]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.2 (pow_nonneg hR.le _))) (norm_nonneg _)
  · simpa only [zero_mul] using (tendsto_inverse_volume hd).mul tendsto_const_nhds

private theorem convolution_mul_comm_euclidean {d : ℕ} (f g : E d → ℝ) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) = g ⋆[ContinuousLinearMap.mul ℝ ℝ] f := by
  funext x
  rw [convolution_mul_swap, convolution_mul]
  exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)

private theorem scalarHessian_convolution_right {d : ℕ} {f g : E d → ℝ}
    (hf : LocallyIntegrable f volume) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (x : E d) (i j : Fin d) :
    scalarHessian (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x i j =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ] fun y => scalarHessian g y i j) x := by
  have hFirst : (fun y => fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) y (axis i)) =
      f ⋆[ContinuousLinearMap.mul ℝ ℝ] (coordinatePartial i g) :=
    funext fun y => convolution_fderiv_right_apply f hf hg hgc y (axis i)
  unfold scalarHessian
  rw [hFirst, convolution_fderiv_right_apply f hf
    (coordinatePartial_smooth hg i) (hgc.fderiv_apply ℝ (axis i)) x (axis j)]
  rfl

private theorem convolution_laplacian_commute {d : ℕ} {f g : E d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (laplacian f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) = f ⋆[ContinuousLinearMap.mul ℝ ℝ] laplacian g := by
  funext x
  rw [convolution_mul, convolution_mul]
  let w (y : E d) := g (x - y)
  have hw : ContDiff ℝ ∞ w := hg.comp (contDiff_const.sub contDiff_id)
  have hwc : HasCompactSupport w := hgc.comp_homeomorph (Homeomorph.subLeft x)
  simpa only [w, laplacian_reflect hg] using (integral_mul_laplacian_comm hf hw hwc).symm

private theorem laplacian_integrable {d : ℕ} {u : E d → ℝ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) : Integrable (laplacian u) :=
  integrable_finsetSum _ fun i _ =>
    ((smooth_compact_scalarHessian hu huc i i).1.continuous).integrable_of_hasCompactSupport
      (smooth_compact_scalarHessian hu huc i i).2

private theorem truncatedNewtonHessian_convolution_laplacian_eq {d : ℕ} (hd : 0 < d)
    {u : E d → ℝ} (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u)
    (i j : Fin d) (x : E d) (n : ℕ) :
    (truncatedNewtonHessian i j n ⋆[ContinuousLinearMap.mul ℝ ℝ] laplacian u) x =
      ((newtonRadialProbability d).scaled (((n : ℝ) + 1)⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        (fun y => scalarHessian u y i j)) x -
      ((newtonRadialProbability d).scaled ((n : ℝ) + 1) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        (fun y => scalarHessian u y i j)) x := by
  let χ := truncatedNewtonKernel d n
  obtain ⟨hχ, hχc⟩ := truncatedNewtonKernel_smooth_compact hd n
  let H (y : E d) := scalarHessian u y i j
  have hH : Continuous H := (smooth_compact_scalarHessian hu huc i j).1.continuous
  have hHc : HasCompactSupport H := (smooth_compact_scalarHessian hu huc i j).2
  have hLapU := laplacian_integrable hu huc
  have hLapΧ := laplacian_integrable hχ hχc
  let k := newtonRadialProbability d
  let R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hε := inv_pos.mpr hR
  calc
    _ = (laplacian u ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun y => scalarHessian χ y i j)) x := by
      rw [convolution_mul_comm_euclidean]
      rfl
    _ = scalarHessian (laplacian u ⋆[ContinuousLinearMap.mul ℝ ℝ] χ) x i j :=
      (scalarHessian_convolution_right hLapU.locallyIntegrable hχ hχc x i j).symm
    _ = scalarHessian (laplacian χ ⋆[ContinuousLinearMap.mul ℝ ℝ] u) x i j := by
      rw [convolution_laplacian_commute hu hχ hχc, convolution_mul_comm_euclidean]
    _ = (laplacian χ ⋆[ContinuousLinearMap.mul ℝ ℝ] H) x :=
      scalarHessian_convolution_right hLapΧ.locallyIntegrable hu huc x i j
    _ = _ := by
      have hI (r : ℝ) (hr : 0 < r) : Integrable (fun y => k.scaled r y * H (x - y)) :=
        (hHc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
          (k.scaled_integrable hr).locallyIntegrable hH x).integrable
      change (laplacian (truncatedNewtonKernel d n) ⋆[ContinuousLinearMap.mul ℝ ℝ] H) x =
        (k.scaled R⁻¹ ⋆[ContinuousLinearMap.mul ℝ ℝ] H) x -
          (k.scaled R ⋆[ContinuousLinearMap.mul ℝ ℝ] H) x
      simp only [laplacian_truncatedNewtonKernel hd n]
      simp only [convolution_mul, Pi.sub_apply, sub_mul, k, R]
      exact integral_sub (hI _ hε) (hI _ hR)

/-- Convolution of the regularized Hessian with the Laplacian of a smooth compactly supported
function converges to the given coordinate Hessian. -/
theorem tendsto_truncatedNewtonHessian_convolution_laplacian {d : ℕ} (hd : 2 ≤ d)
    (i j : Fin d) {u : E d → ℝ} (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (x : E d) :
    Tendsto (fun n : ℕ =>
      (truncatedNewtonHessian i j n ⋆[ContinuousLinearMap.mul ℝ ℝ] laplacian u) x)
      atTop (𝓝 (scalarHessian u x i j)) := by
  have hd0 : 0 < d := by omega
  let H (y : E d) := scalarHessian u y i j
  have hH : Continuous H := (smooth_compact_scalarHessian hu huc i j).1.continuous
  have hHc : HasCompactSupport H := (smooth_compact_scalarHessian hu huc i j).2
  have hI : Integrable H := hH.integrable_of_hasCompactSupport hHc
  have hs := tendsto_convolution_smallDensity (newtonRadialProbability d) hH x
  have hR := tendsto_convolution_largeDensity hd0 (newtonRadialProbability d) hI x
  simpa only [truncatedNewtonHessian_convolution_laplacian_eq hd0 hu huc, sub_zero] using hs.sub hR

private theorem cutoff_kernel_separated_support {d : ℕ} {b : E d → ℝ}
    {x z : E d} {r : ℝ} (hbr : Function.support b ⊆ ball z r)
    (hx : x ∉ ball z (2 * r)) {y : E d} (hy : y ∈ Function.support b) :
    r ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ dist x z + r := by
  have hzy : dist y z < r := Metric.mem_ball.mp (hbr hy)
  have hxz : 2 * r ≤ dist x z := le_of_not_gt (fun h => hx (Metric.mem_ball.mpr h))
  rw [← dist_eq_norm]
  constructor
  · linarith only [dist_triangle x y z, hxz, hzy]
  · have hTri := dist_triangle x z y
    rw [dist_comm z y] at hTri
    exact hTri.trans (add_le_add_right hzy.le (dist x z))

private theorem integrable_newtonHessian_mul_off_ball {d : ℕ} (hd : 2 ≤ d) (i j : Fin d)
    {b : E d → ℝ} {x z : E d} {r : ℝ} (hb : Integrable b)
    (hbr : Function.support b ⊆ ball z r) (hr : 0 < r) (hx : x ∉ ball z (2 * r)) :
    Integrable (fun y => HolderToCK.hessianKernelExpression i j (x - y) * b y) := by
  let A := ((d : ℝ) + 1) * (HolderToCK.euclideanSphereArea d)⁻¹
  let M := A * r ^ (-(d : ℝ))
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by positivity)
      (inv_nonneg.2 (HolderToCK.euclideanSphereArea_pos (by omega : 0 < d)).le)
  have hMeas : AEStronglyMeasurable (fun y : E d =>
      HolderToCK.hessianKernelExpression i j (x - y)) volume := by
    exact ((HolderToCK.hessianKernelExpression_measurable i j).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  refine (hb.norm.const_mul M).mono' (hMeas.mul hb.aestronglyMeasurable) ?_
  apply Eventually.of_forall
  intro y
  by_cases hy : y ∈ Function.support b
  · have hLow := (cutoff_kernel_separated_support hbr hx hy).1
    have hxy : x - y ≠ 0 := norm_ne_zero_iff.mp (hr.trans_le hLow).ne'
    have hBound := HolderToCK.hessianKernelExpression_bound (by omega : 0 < d) i j _ hxy
    have hPow := Real.rpow_le_rpow_of_nonpos hr hLow (neg_nonpos.2 (Nat.cast_nonneg d))
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [Real.norm_eq_abs]
    exact hBound.trans (mul_le_mul_of_nonneg_left hPow hA)
  · simp only [Function.notMem_support.mp hy, mul_zero, norm_zero, le_refl]

private theorem eventually_uniform_cutoff_kernel_error {d : ℕ} (hd : 2 ≤ d) (i j : Fin d)
    {b : E d → ℝ} {x z : E d} {r : ℝ}
    (hbr : Function.support b ⊆ ball z r) (hr : 0 < r) (hx : x ∉ ball z (2 * r)) :
    ∃ M : ℝ, ∀ᶠ n : ℕ in atTop, ∀ y ∈ Function.support b,
      ‖truncatedNewtonHessian i j n (x - y) - HolderToCK.hessianKernelExpression i j (x - y)‖ ≤
        (((n : ℝ) + 1) ^ d)⁻¹ * M := by
  let u := radialNewtonPotential (newtonRadialProbability d) 1
  let H (w : E d) := scalarHessian u w i j
  have hu : ContDiff ℝ ∞ u := radialNewtonPotential_smooth (by omega : 0 < d) _ one_pos
  have hH : Continuous H := (coordinatePartial_smooth (coordinatePartial_smooth hu i) j).continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E d) 1).exists_bound_of_continuousOn hH.continuousOn
  refine ⟨M, ?_⟩
  have hCast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hLarge : ∀ᶠ n : ℕ in atTop, dist x z + r ≤ (n : ℝ) :=
    (tendsto_atTop.mp hCast) (dist x z + r)
  filter_upwards [tendsto_inverse_radius.eventually_lt_const hr, hLarge] with n hSmall hnLarge
  intro y hy
  let R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨hLow, hHigh⟩ := cutoff_kernel_separated_support hbr hx hy
  have hOff : x - y ∉ closedBall (0 : E d) R⁻¹ := by
    rw [mem_closedBall, dist_zero_right]
    exact not_le.mpr (hSmall.trans_le hLow)
  have hLocal : R⁻¹ • (x - y) ∈ closedBall (0 : E d) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
      inv_mul_eq_div]
    exact (div_le_one hR).mpr
      (hHigh.trans (hnLarge.trans (le_add_of_nonneg_right zero_le_one)))
  rw [truncatedNewtonHessian_eq_off_smallBall hd i j n hOff]
  have he (a b : ℝ) : a - b - a = -b := by ring
  rw [he, norm_neg, norm_mul]
  rw [Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg hR.le _))]
  exact mul_le_mul_of_nonneg_left (hM _ hLocal) (inv_nonneg.2 (pow_nonneg hR.le _))

/-- Away from the support ball, the smoothed Newtonian Hessian convolutions converge to the
ordinary integral against the off-origin kernel. -/
theorem tendsto_truncatedNewtonHessian_convolution_off_ball {d : ℕ} (hd : 2 ≤ d) (i j : Fin d)
    {b : E d → ℝ} {x z : E d} {r : ℝ} (hb : Integrable b)
    (hbr : Function.support b ⊆ ball z r) (hr : 0 < r) (hx : x ∉ ball z (2 * r)) :
    Tendsto (fun n : ℕ => (truncatedNewtonHessian i j n ⋆[ContinuousLinearMap.mul ℝ ℝ] b) x)
      atTop (𝓝 (∫ y, HolderToCK.hessianKernelExpression i j (x - y) * b y)) := by
  let F (y : E d) := HolderToCK.hessianKernelExpression i j (x - y) * b y
  have hF : Integrable F := integrable_newtonHessian_mul_off_ball hd i j hb hbr hr hx
  suffices h : Tendsto (fun n : ℕ =>
      (truncatedNewtonHessian i j n ⋆[ContinuousLinearMap.mul ℝ ℝ] b) x - ∫ y, F y)
      atTop (𝓝 0) by
    change Tendsto _ atTop (𝓝 (∫ y, F y))
    apply (tendsto_sub_const_iff (∫ y, F y)).mp
    simpa only [sub_self] using h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨M, hM⟩ := eventually_uniform_cutoff_kernel_error hd i j hbr hr hx
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (g := fun n : ℕ => (((n : ℝ) + 1) ^ d)⁻¹ * (M * ∫ y, ‖b y‖)) ?_ ?_
  · filter_upwards [hM] with n hn
    obtain ⟨hχ, hχc⟩ := truncatedNewtonKernel_smooth_compact (by omega : 0 < d) n
    obtain ⟨hK, hKc⟩ := smooth_compact_scalarHessian hχ hχc i j
    have hI : Integrable (fun y => truncatedNewtonHessian i j n (x - y) * b y) :=
      (hKc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ)
        hK.continuous hb.locallyIntegrable x).integrable_swap
    rw [convolution_mul_swap, ← integral_sub hI hF, ← mul_assoc, ← integral_const_mul]
    apply norm_integral_le_of_norm_le (hb.norm.const_mul _)
    apply Eventually.of_forall
    intro y
    by_cases hy : y ∈ Function.support b
    · have ht := hn y hy
      dsimp only [F]
      rw [← sub_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    · simp only [F, Function.notMem_support.mp hy, mul_zero, sub_zero, norm_zero, le_refl]
  · simpa only [zero_mul] using (tendsto_inverse_volume (by omega : 0 < d)).mul tendsto_const_nhds

end SupportingAnalysis
