module

public import SupportingAnalysis.Poisson.FundamentalSolution
import SupportingAnalysis.Calculus.LineDerivatives
public import HolderToCK.Analysis.Poisson.KernelCancellation

/-! Compact smooth Newtonian cutoffs with a uniform (L^1) Laplacian bound. -/

public section

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff Convolution Topology

set_option autoImplicit false

namespace SupportingAnalysis

private noncomputable def newtonRadialBump (d : ℕ) (x : E d) : ℝ :=
  Real.smoothTransition (1 - ‖x‖ ^ 2)

private theorem newtonRadialBump_smooth (d : ℕ) : ContDiff ℝ ∞ (newtonRadialBump d) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

private theorem newtonRadialBump_support (d : ℕ) : Function.support (newtonRadialBump d) = ball 0 1 := by
  ext x
  rw [Function.mem_support, newtonRadialBump, ne_eq, Real.smoothTransition.zero_iff_nonpos,
    not_le, mem_ball_zero_iff]
  constructor
  · intro h
    by_contra! hn
    have hPow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hn 2
    nlinarith only [h, hPow]
  · intro h
    exact sub_pos.mpr (pow_lt_one₀ (norm_nonneg _) h (by norm_num))

/-- A fixed smooth radial probability density for the Newtonian cutoffs. -/
noncomputable def newtonRadialProbability (d : ℕ) : RadialProbabilityDensity d := by
  let M := ∫ x, newtonRadialBump d x
  have hNonneg (x : E d) : 0 ≤ newtonRadialBump d x := Real.smoothTransition.nonneg _
  have hCompact : HasCompactSupport (newtonRadialBump d) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 1)
    exact (newtonRadialBump_support d).subset.trans ball_subset_closedBall
  have hI : Integrable (newtonRadialBump d) :=
    (newtonRadialBump_smooth d).continuous.integrable_of_hasCompactSupport hCompact
  have hM : 0 < M := by
    apply (integral_pos_iff_support_of_nonneg hNonneg hI).mpr
    rw [newtonRadialBump_support]
    exact measure_ball_pos volume 0 one_pos
  refine ⟨fun x => M⁻¹ * newtonRadialBump d x,
    contDiff_const.mul (newtonRadialBump_smooth d),
    ⟨fun t => M⁻¹ * Real.smoothTransition (1 - t ^ 2), fun _ => rfl⟩,
    fun x => mul_nonneg (inv_nonneg.2 hM.le) (hNonneg x), ?_, ?_⟩
  · intro x hx
    apply (newtonRadialBump_support d).subset
    exact Function.mem_support.mpr fun h => (Function.mem_support.mp hx) (by simp [h])
  · rw [integral_const_mul]
    exact inv_mul_cancel₀ hM.ne'

/-- The Newtonian potential of the scaled smooth radial probability density. -/
@[expose] noncomputable def radialNewtonPotential {d : ℕ} (k : RadialProbabilityDensity d)
    (R : ℝ) : E d → ℝ :=
  canonicalNewtonian d ⋆[ContinuousLinearMap.mul ℝ ℝ] k.scaled R

theorem radialNewtonPotential_smooth {d : ℕ} (hd : 0 < d) (k : RadialProbabilityDensity d)
    {R : ℝ} (hR : 0 < R) : ContDiff ℝ ∞ (radialNewtonPotential k R) :=
  (k.scaled_hasCompactSupport hR).contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (canonicalNewtonian_locallyIntegrable hd) (k.scaled_smooth R)

theorem laplacian_radialNewtonPotential {d : ℕ} (hd : 0 < d) (k : RadialProbabilityDensity d)
    {R : ℝ} (hR : 0 < R) : laplacian (radialNewtonPotential k R) = k.scaled R := by
  funext x
  unfold radialNewtonPotential
  rw [laplacian_convolution _ (canonicalNewtonian_locallyIntegrable hd)
    (k.scaled_smooth R) (k.scaled_hasCompactSupport hR)]
  have hφ : ContDiff ℝ ∞ (fun y => k.scaled R (x - y)) := (k.scaled_smooth R).comp
    (contDiff_const.sub contDiff_id)
  have ht := canonicalNewtonian_distributionPairing hd _ hφ
    ((k.scaled_hasCompactSupport hR).comp_homeomorph (Homeomorph.subLeft x))
  simpa only [laplacian_reflect (k.scaled_smooth R), sub_zero] using ht

private theorem radialNewtonPotential_eq_kernel_sub_correction {d : ℕ}
    (k : RadialProbabilityDensity d) (R : ℝ) (x : E d) :
    radialNewtonPotential k R x =
      canonicalNewtonian d x - potentialCorrection (canonicalNewtonian d) k R x := by
  rw [radialNewtonPotential, convolution_mul_swap, potentialCorrection, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm (k.scaled R _), sub_sub_cancel]

theorem radialNewtonPotential_eq_off_closedBall {d : ℕ} (hd : 0 < d)
    (k : RadialProbabilityDensity d) {R : ℝ} (hR : 0 < R) {x : E d}
    (hx : x ∉ closedBall 0 R) : radialNewtonPotential k R x = canonicalNewtonian d x := by
  obtain ⟨_, _, h⟩ := compactPotential_canonical hd k
  rw [radialNewtonPotential_eq_kernel_sub_correction,
    image_eq_zero_of_notMem_tsupport (fun hy => hx ((h R hR).1 hy)), sub_zero]

private theorem scalarHessian_sub_smooth {d : ℕ} {f g : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E d) (i j : Fin d) :
    scalarHessian (f - g) x i j = scalarHessian f x i j - scalarHessian g x i j := by
  have hPartial : coordinatePartial i (f - g) = coordinatePartial i f - coordinatePartial i g := by
    funext y
    unfold coordinatePartial
    rw [fderiv_sub (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
    rfl
  change coordinatePartial j (coordinatePartial i (f - g)) x = _
  rw [hPartial, coordinatePartial,
    fderiv_sub ((coordinatePartial_smooth hf i).differentiable (by simp) x)
      ((coordinatePartial_smooth hg i).differentiable (by simp) x)]
  rfl

private theorem laplacian_sub_smooth {d : ℕ} {f g : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : laplacian (f - g) = laplacian f - laplacian g := by
  funext x
  change (∑ i, scalarHessian (f - g) x i i) =
    (∑ i, scalarHessian f x i i) - ∑ i, scalarHessian g x i i
  simp_rw [scalarHessian_sub_smooth hf hg, Finset.sum_sub_distrib]

/-- Difference of two smoothings of the fundamental solution at reciprocal scales. -/
@[expose] noncomputable def truncatedNewtonKernel (d n : ℕ) : E d → ℝ :=
  radialNewtonPotential (newtonRadialProbability d) (((n : ℝ) + 1)⁻¹) -
    radialNewtonPotential (newtonRadialProbability d) ((n : ℝ) + 1)

theorem truncatedNewtonKernel_smooth_compact {d : ℕ} (hd : 0 < d) (n : ℕ) :
    ContDiff ℝ ∞ (truncatedNewtonKernel d n) ∧
      HasCompactSupport (truncatedNewtonKernel d n) := by
  let R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hε := inv_pos.mpr hR
  let k := newtonRadialProbability d
  refine ⟨(radialNewtonPotential_smooth hd k hε).sub
    (radialNewtonPotential_smooth hd k hR), ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E d) R)
  intro x hx
  by_contra! hxR
  have hεR : R⁻¹ ≤ R := by
    have h1 : 1 ≤ R := le_add_of_nonneg_left (Nat.cast_nonneg n)
    exact (inv_le_one_of_one_le₀ h1).trans h1
  have hxε : x ∉ closedBall (0 : E d) R⁻¹ := fun h =>
    hxR (closedBall_subset_closedBall hεR h)
  apply Function.mem_support.mp hx
  change radialNewtonPotential k R⁻¹ x - radialNewtonPotential k R x = 0
  rw [radialNewtonPotential_eq_off_closedBall hd k hε hxε,
    radialNewtonPotential_eq_off_closedBall hd k hR hxR, sub_self]

/-- The signed Laplacian is the difference of two probability densities. -/
theorem laplacian_truncatedNewtonKernel {d : ℕ} (hd : 0 < d) (n : ℕ) :
    laplacian (truncatedNewtonKernel d n) =
      (newtonRadialProbability d).scaled (((n : ℝ) + 1)⁻¹) -
        (newtonRadialProbability d).scaled ((n : ℝ) + 1) := by
  let k := newtonRadialProbability d
  let R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hε := inv_pos.mpr hR
  change laplacian (radialNewtonPotential k R⁻¹ - radialNewtonPotential k R) =
    k.scaled R⁻¹ - k.scaled R
  rw [laplacian_sub_smooth (radialNewtonPotential_smooth hd k hε)
    (radialNewtonPotential_smooth hd k hR),
    laplacian_radialNewtonPotential hd k hε, laplacian_radialNewtonPotential hd k hR]

theorem integral_abs_laplacian_truncatedNewtonKernel_le {d : ℕ} (hd : 0 < d) (n : ℕ) :
    (∫ x, |laplacian (truncatedNewtonKernel d n) x|) ≤ 2 := by
  rw [laplacian_truncatedNewtonKernel hd n]
  let k := newtonRadialProbability d
  let R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hε := inv_pos.mpr hR
  change (∫ x, |k.scaled R⁻¹ x - k.scaled R x|) ≤ 2
  have hIε := k.scaled_integrable hε
  have hIR := k.scaled_integrable hR
  calc
    _ ≤ ∫ x, k.scaled R⁻¹ x + k.scaled R x := by
      refine integral_mono (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hIε.sub hIR).norm)
        (hIε.add hIR) fun x => ?_
      simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (k.scaled_nonnegative _ hε x),
        abs_of_nonneg (k.scaled_nonnegative _ hR x)] using
        abs_sub_le (k.scaled R⁻¹ x) 0 (k.scaled R x)
    _ = _ := by rw [integral_add hIε hIR, k.scaled_mass hε, k.scaled_mass hR]; norm_num

/-- A coordinate Hessian kernel of the compact Newtonian cutoff. -/
@[expose] noncomputable def truncatedNewtonHessian {d : ℕ} (i j : Fin d) (n : ℕ) : E d → ℝ :=
  fun x => scalarHessian (truncatedNewtonKernel d n) x i j

private theorem scalarHessian_congr_open {d : ℕ} {F G : E d → ℝ} {U : Set (E d)}
    (hU : IsOpen U) (he : EqOn F G U) {x : E d} (hx : x ∈ U) (i j : Fin d) :
    scalarHessian F x i j = scalarHessian G x i j := by
  have hFirst : EqOn (coordinatePartial i F) (coordinatePartial i G) U := by
    intro y hy
    have hmem : ∀ᶠ z in 𝓝 y, z ∈ U := hU.mem_nhds hy
    have hEq : F =ᶠ[𝓝 y] G := hmem.mono fun z hz => he hz
    exact congrArg (fun L : E d →L[ℝ] ℝ => L (axis i)) (hEq.fderiv_eq (𝕜 := ℝ))
  have hmem : ∀ᶠ z in 𝓝 x, z ∈ U := hU.mem_nhds hx
  have hEq : coordinatePartial i F =ᶠ[𝓝 x] coordinatePartial i G :=
    hmem.mono fun _ hz => hFirst hz
  exact congrArg (fun L : E d →L[ℝ] ℝ => L (axis j)) (hEq.fderiv_eq (𝕜 := ℝ))

private theorem scalarHessian_canonicalNewtonian {d : ℕ} (hd : 2 ≤ d) {x : E d} (hx : x ≠ 0)
    (i j : Fin d) :
    scalarHessian (canonicalNewtonian d) x i j = HolderToCK.hessianKernelExpression i j x := by
  rw [HolderToCK.hessianKernelExpression_eq i j (⟨x, hx⟩ : {z : E d // z ≠ 0})]
  rcases (show d = 2 ∨ 3 ≤ d by omega) with h | h
  · subst d
    rw [canonicalNewtonian_two]
    exact HolderToCK.fundamentalLog_mixedColumns x hx i j
  · rw [canonicalNewtonian_of_three_le h]
    exact HolderToCK.fundamentalPower_mixedColumns h x hx i j

private theorem radialNewtonPotential_hessian_off_closedBall {d : ℕ} (hd : 2 ≤ d)
    (k : RadialProbabilityDensity d) {R : ℝ} (hR : 0 < R) {x : E d}
    (hx : x ∉ closedBall 0 R) (i j : Fin d) :
    scalarHessian (radialNewtonPotential k R) x i j = HolderToCK.hessianKernelExpression i j x := by
  let U : Set (E d) := (closedBall (0 : E d) R)ᶜ
  have hU : IsOpen U := isClosed_closedBall.isOpen_compl
  have hx0 : x ≠ 0 := fun h => hx (h ▸ mem_closedBall_self hR.le)
  have he : EqOn (radialNewtonPotential k R) (canonicalNewtonian d) U :=
    fun _ h => radialNewtonPotential_eq_off_closedBall (by omega : 0 < d) k hR h
  exact (scalarHessian_congr_open hU he hx i j).trans (scalarHessian_canonicalNewtonian hd hx0 i j)

private theorem canonicalNewtonian_dilation {d : ℕ} (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R) :
    ∃ c : ℝ, ∀ x ≠ (0 : E d),
      canonicalNewtonian d (R • x) = R ^ (2 - (d : ℤ)) * canonicalNewtonian d x + c := by
  rcases (show d = 2 ∨ 3 ≤ d by omega) with h | h
  · subst d
    refine ⟨(2 * Real.pi)⁻¹ * Real.log R, fun x hx => ?_⟩
    rw [canonicalNewtonian_two]
    exact holderLog_dilate hR hx
  · refine ⟨0, fun x _ => ?_⟩
    rw [canonicalNewtonian_of_three_le h, add_zero]
    exact holderPower_dilate hR x

private theorem radialNewtonPotential_dilation {d : ℕ} (hd : 2 ≤ d)
    (k : RadialProbabilityDensity d) {R : ℝ} (hR : 0 < R) :
    ∃ c : ℝ, ∀ x ≠ (0 : E d),
      radialNewtonPotential k R (R • x) = R ^ (2 - (d : ℤ)) * radialNewtonPotential k 1 x + c := by
  obtain ⟨c, hc⟩ := canonicalNewtonian_dilation hd hR
  have hd0 : 0 < d := by omega
  refine ⟨c, fun x hx => ?_⟩
  rw [radialNewtonPotential_eq_kernel_sub_correction, radialNewtonPotential_eq_kernel_sub_correction,
    potentialCorrection_dilate_apply _ (canonicalNewtonian_locallyIntegrable hd0) k hd0
      (2 - (d : ℤ)) c hR (by simpa only [smul_eq_mul] using hc) hx,
    hc x hx, smul_eq_mul]
  ring

private theorem coordinatePartial_affineValue_smulDomain {d : ℕ} {f : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (a b R : ℝ) (x : E d) (i : Fin d) :
    coordinatePartial i (fun y => a * f (R • y) + b) x =
      a * R * coordinatePartial i f (R • x) := by
  have hLin : HasFDerivAt (fun y : E d => R • y) (R • ContinuousLinearMap.id ℝ (E d)) x :=
    (hasFDerivAt_id x).const_smul R
  have hh := ((((hf.differentiable (by simp) (R • x)).hasFDerivAt.comp x hLin).const_mul a).add_const b)
  change HasFDerivAt (fun y : E d => a * f (R • y) + b) _ x at hh
  unfold coordinatePartial
  rw [hh.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

private theorem scalarHessian_affineValue_smulDomain {d : ℕ} {f : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (a b R : ℝ) (x : E d) (i j : Fin d) :
    scalarHessian (fun y => a * f (R • y) + b) x i j =
      a * R ^ 2 * scalarHessian f (R • x) i j := by
  have hFirst :
      coordinatePartial i (fun y => a * f (R • y) + b) =
        fun y => (a * R) * coordinatePartial i f (R • y) + 0 := by
    funext y
    rw [add_zero, coordinatePartial_affineValue_smulDomain hf]
  change coordinatePartial j (coordinatePartial i (fun y => a * f (R • y) + b)) x = _
  rw [hFirst, coordinatePartial_affineValue_smulDomain (coordinatePartial_smooth hf i)]
  change a * R * R * scalarHessian f (R • x) i j = _
  ring

/-- The Hessian of the large-scale smoothing has the inverse-volume dilation. -/
theorem radialNewtonPotential_hessian_dilation {d : ℕ} (hd : 2 ≤ d)
    (k : RadialProbabilityDensity d) {R : ℝ} (hR : 0 < R) {x : E d} (hx : x ≠ 0)
    (i j : Fin d) :
    scalarHessian (radialNewtonPotential k R) x i j =
      (R ^ d)⁻¹ * scalarHessian (radialNewtonPotential k 1) (R⁻¹ • x) i j := by
  obtain ⟨c, hc⟩ := radialNewtonPotential_dilation hd k hR
  let F (y : E d) := R ^ (2 - (d : ℤ)) * radialNewtonPotential k 1 (R⁻¹ • y) + c
  have hEq : EqOn (radialNewtonPotential k R) F ({0}ᶜ : Set (E d)) := by
    intro y hy
    have hne : R⁻¹ • y ≠ (0 : E d) :=
      smul_ne_zero (inv_ne_zero hR.ne') hy
    simpa only [F, smul_smul, mul_inv_cancel₀ hR.ne', one_smul] using hc _ hne
  have hs := scalarHessian_affineValue_smulDomain
    (radialNewtonPotential_smooth (by omega : 0 < d) k one_pos)
    (R ^ (2 - (d : ℤ))) c R⁻¹ x i j
  have hPow : R ^ (2 - (d : ℤ)) * (R⁻¹) ^ 2 = (R ^ d)⁻¹ := by
    rw [zpow_sub₀ hR.ne', zpow_ofNat, zpow_natCast, inv_pow]
    field_simp
  rw [scalarHessian_congr_open isClosed_singleton.isOpen_compl hEq hx i j]
  simpa only [F, hPow] using hs

/-- Outside the smaller smoothing ball, the cutoff Hessian is the Newtonian Hessian
minus the scaled Hessian of a smooth unit-scale potential. -/
theorem truncatedNewtonHessian_eq_off_smallBall {d : ℕ} (hd : 2 ≤ d)
    (i j : Fin d) (n : ℕ) {x : E d}
    (hx : x ∉ closedBall (0 : E d) (((n : ℝ) + 1)⁻¹)) :
    truncatedNewtonHessian i j n x =
      HolderToCK.hessianKernelExpression i j x -
        (((n : ℝ) + 1) ^ d)⁻¹ *
          scalarHessian (radialNewtonPotential (newtonRadialProbability d) 1)
            ((((n : ℝ) + 1)⁻¹) • x) i j := by
  let R : ℝ := (n : ℝ) + 1
  let k := newtonRadialProbability d
  have hR : 0 < R := by dsimp [R]; positivity
  have hε := inv_pos.mpr hR
  have hx0 : x ≠ 0 := fun h => hx (h ▸ mem_closedBall_self hε.le)
  change scalarHessian (radialNewtonPotential k R⁻¹ - radialNewtonPotential k R) x i j = _
  rw [scalarHessian_sub_smooth (radialNewtonPotential_smooth (by omega : 0 < d) k hε)
    (radialNewtonPotential_smooth (by omega : 0 < d) k hR),
    radialNewtonPotential_hessian_off_closedBall hd k hε hx i j,
    radialNewtonPotential_hessian_dilation hd k hR hx0 i j]

end SupportingAnalysis
