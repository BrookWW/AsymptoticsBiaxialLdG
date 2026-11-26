module

public import Thesis.Definitions
import Thesis.Variational.BoundaryBarrier
import Thesis.Variational.BoundarySmallEnergy
import HolderToCK.Analysis.ConvolutionDerivatives
import HarmonicMaps.Analysis.MollificationLocalKernel
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! Maximum principle for continuous scalar distributional subsolutions. -/

public section

noncomputable section

open Filter HarmonicMaps HolderToCK MeasureTheory Metric Set
open scoped BigOperators ContDiff Convolution ENNReal Topology

namespace Thesis

private theorem scalarKernelIntegral_contDiff {u k : Point → ℝ} (hu : Integrable u volume)
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    ContDiff ℝ ∞ (fun x : Point => ∫ y, k (x-y) * u y) := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  change ContDiff ℝ ∞ (u ⋆[L.flip, volume] k)
  exact hc.contDiff_convolution_right L.flip hu.locallyIntegrable hk

private theorem scalarKernelIntegral_fderiv {u k : Point → ℝ} (hu : Integrable u volume)
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) (x v : Point) :
    (fderiv ℝ (fun x : Point => ∫ y, k (x-y) * u y) x) v =
      ∫ y, (fderiv ℝ k (x-y)) v * u y := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  have h := hc.hasFDerivAt_convolution_right L.flip hu.locallyIntegrable
    (hk.of_le (WithTop.coe_le_coe.mpr le_top)) x
  change (fderiv ℝ (u ⋆[L.flip, volume] k) x) v = _
  rw [h.fderiv, convolution_precompR_apply L.flip hu.locallyIntegrable (hc.fderiv ℝ)
    (hk.continuous_fderiv (by simp)) x v]
  rfl

private theorem scalarKernelIntegral_laplacian {u k : Point → ℝ} (hu : Integrable u volume)
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) (x : Point) :
    laplacian (fun x : Point => ∫ y, k (x-y) * u y) x = ∫ y, laplacian k (x-y) * u y := by
  let K (x : Point) := ∫ y, k (x-y) * u y
  have hCol (i : Fin 3) : coordDeriv i K = fun x => ∫ y, coordDeriv i k (x-y) * u y :=
    funext fun x => scalarKernelIntegral_fderiv hu hk hc x (axis i)
  have hD (j : Fin 3) : ContDiff ℝ ∞ (coordDeriv j k) :=
    (ContinuousLinearMap.apply ℝ ℝ (axis j)).contDiff.comp (hk.fderiv_right (by simp))
  have hD₂ (j : Fin 3) : Continuous (coordDeriv j (coordDeriv j k)) :=
    ((ContinuousLinearMap.apply ℝ ℝ (axis j)).continuous.comp ((hD j).continuous_fderiv (by simp)))
  have hC (j : Fin 3) : HasCompactSupport (coordDeriv j k) := hc.fderiv_apply ℝ (axis j)
  have h₂ (j : Fin 3) : Integrable (fun y => coordDeriv j (coordDeriv j k) (x-y) * u y) volume := by
    have hcomp : HasCompactSupport (fun y : Point => coordDeriv j (coordDeriv j k) (x-y)) :=
      ((hC j).fderiv_apply ℝ (axis j)).comp_homeomorph (Homeomorph.subLeft x)
    have hcont : Continuous (fun y : Point => coordDeriv j (coordDeriv j k) (x-y)) :=
      (hD₂ j).comp (continuous_const.sub continuous_id)
    have h := hu.mul_of_top_left (hcont.memLp_top_of_hasCompactSupport hcomp _)
    exact h.congr (Eventually.of_forall fun y => mul_comm _ _)
  change laplacian K x = _
  simp only [laplacian, Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ => h₂ j)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hCol]
  exact scalarKernelIntegral_fderiv hu (hD i) (hC i) x (axis i)

private theorem laplacian_scalar_sub_const {u : Point → ℝ} (c : ℝ) :
    laplacian (fun x => u x - c) = laplacian u := by
  funext x
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i _
  have hEq : coordDeriv i (fun y => u y-c) = coordDeriv i u := by
    funext y
    change (fderiv ℝ (fun y => u y-c) y) (axis i) = _
    rw [fderiv_sub_const]
    rfl
  rw [hEq]

/-- A continuous scalar field whose distributional Laplacian is
nonnegative is bounded above by its boundary upper bound. -/
theorem nonpos_of_distributional_subharmonic
    {U : Set Point} (hU : IsOpen U) {c : Point} {r : ℝ} (hSub : U ⊆ ball c r)
    {u : Point → ℝ} (hu : ContinuousOn u (closure U))
    (hLap : ∀ φ : Point → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x in U, u x * laplacian φ x)
    (hFront : ∀ x ∈ frontier U, u x ≤ 0) :
    ∀ x ∈ closure U, u x ≤ 0 := by
  intro x hx
  by_contra hn
  have hxpos : 0 < u x := lt_of_not_ge hn
  have hxU : x ∈ U := by
    by_contra hxN
    exact hxpos.not_ge (hFront x (by rw [frontier, hU.interior_eq]; exact ⟨hx,hxN⟩))
  have hBound : Bornology.IsBounded U := isBounded_ball.subset hSub
  have hClComp : IsCompact (closure U) := hBound.isCompact_closure
  let d := u x / 4
  have hd : 0 < d := by dsimp only [d]; positivity
  let V := U ∩ {y | d < u y}
  have hV : IsOpen V := (hu.mono subset_closure).isOpen_inter_preimage hU isOpen_Ioi
  have hVU : V ⊆ U := inter_subset_left
  have hVC : closure V ⊆ closure U := closure_mono hVU
  have hClosed : IsCompact (closure V) := hClComp.of_isClosed_subset isClosed_closure hVC
  have hCU : closure V ⊆ U := by
    intro y hy
    by_contra hyN
    have hyF : y ∈ frontier U := by rw [frontier,hU.interior_eq]; exact ⟨hVC hy,hyN⟩
    have hD : d ≤ u y := le_on_closure (fun z hz => (show d < u z from hz.2).le)
      continuousOn_const (hu.mono hVC) hy
    exact hd.not_ge (hD.trans (hFront y hyF))
  have hxD : d < u x := by dsimp only [d]; linarith only [hxpos]
  have hxV : x ∈ V := ⟨hxU, hxD⟩
  have hVbd : ∀ y ∈ frontier V, u y ≤ d := by
    intro y hy
    have hyC : y ∈ closure V := frontier_subset_closure hy
    by_contra hh
    have hyV : y ∈ V := ⟨hCU hyC, lt_of_not_ge hh⟩
    rw [frontier,hV.interior_eq] at hy
    exact hy.2 hyV
  obtain ⟨η, hη, hThick⟩ := hClosed.exists_thickening_subset_open hU hCU
  have hUnif := hClComp.uniformContinuousOn_of_continuous hu
  obtain ⟨ε₀, hε₀, hεD⟩ := Metric.uniformContinuousOn_iff.mp hUnif (d/2) (half_pos hd)
  let ε : PositiveRadius := ⟨min η ε₀ / 2, by positivity⟩
  have hεη : ε.val < η := ((half_lt_self (lt_min hη hε₀)).trans_le (min_le_left _ _))
  have hεε₀ : ε.val < ε₀ := ((half_lt_self (lt_min hη hε₀)).trans_le (min_le_right _ _))
  let k := scaledMollifierKernel 3 ε
  have hkD : ContDiff ℝ ∞ k := scaledMollifierKernel_contDiff _ _
  have hkC : HasCompactSupport k := scaledMollifierKernel_hasCompactSupport _ _
  have hkSupp : tsupport k ⊆ closedBall (0 : Point) (ε.val/2) :=
    scaledMollifierKernel_tsupport_subset_halfBall _ _
  have hkPos (p : Point) : 0 ≤ k p := scaledMollifierKernel_nonneg _ _ _
  let u₀ := U.indicator u
  have hu₀ : Integrable u₀ volume := (integrable_indicator_iff hU.measurableSet).2
    ((hu.integrableOn_compact hClComp).mono_set subset_closure)
  let Q (x : Point) := ∫ y, k (x-y) * u₀ y
  have hQ : ContDiff ℝ ∞ Q := scalarKernelIntegral_contDiff hu₀ hkD hkC
  have hSampling {y z : Point} (hy : y ∈ closure V) (hz : dist z y < η) : z ∈ U :=
    hThick (mem_thickening_iff.2 ⟨y, hy, hz⟩)
  have hQlap (y : Point) (hy : y ∈ V) : 0 ≤ laplacian Q y := by
    let φ := fun z : Point => k (y-z)
    have hφ : ContDiff ℝ ∞ φ := hkD.comp (contDiff_const.sub contDiff_id)
    have hφC : HasCompactSupport φ := hkC.comp_homeomorph (Homeomorph.subLeft y)
    have hφS : tsupport φ ⊆ U := by
      have hInv : tsupport φ = (Homeomorph.subLeft y) ⁻¹' tsupport k :=
        (Homeomorph.subLeft y).preimage_closure (Function.support k) |>.symm.trans rfl
      intro z hz
      have hkz := hkSupp (hInv ▸ hz)
      change y-z ∈ closedBall (0 : Point) (ε.val/2) at hkz
      have hd' : dist z y ≤ ε.val/2 := by
        simpa only [mem_closedBall_zero_iff, dist_eq_norm, norm_sub_rev] using hkz
      exact hSampling (subset_closure hy) (hd'.trans_lt ((half_lt_self ε.property).trans hεη))
    have hΔφ (z : Point) : laplacian φ z = laplacian k (y-z) := by
      have h := laplacian_affine_dilation isOpen_univ (hkD.of_le
        (WithTop.coe_le_coe.mpr le_top)).contDiffOn y (-1) (y := z) (mem_univ _)
      simpa only [neg_one_smul, ← sub_eq_add_neg, neg_one_pow_two, one_smul] using h
    have h := hLap φ hφ hφC hφS (fun _ => hkPos _)
    rw [scalarKernelIntegral_laplacian hu₀ hkD hkC]
    simp_rw [hΔφ] at h
    convert h using 1
    rw [← integral_indicator hU.measurableSet]
    apply integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ U
    · simp only [u₀, indicator_of_mem hz, mul_comm]
    · simp only [u₀, indicator_of_notMem hz, mul_zero]
  have hClose (y : Point) (hy : y ∈ closure V) : dist (Q y) (u y) ≤ d/2 := by
    have hBs : ∀ z ∈ ball y ε.val, dist (u₀ z) (u y) ≤ d/2 := by
      intro z hz
      have hzD : dist z y < ε.val := hz
      have hzU := hSampling hy (hzD.trans hεη)
      rw [show u₀ z = u z from indicator_of_mem hzU _]
      exact (hεD z (subset_closure hzU) y (hVC hy) (hzD.trans hεε₀)).le
    have hκSupp : Function.support k ⊆ ball (0 : Point) ε.val :=
      (subset_tsupport k).trans (hkSupp.trans (closedBall_subset_ball (half_lt_self ε.property)))
    have hB := dist_convolution_le (half_pos hd).le hκSupp hkPos
      (scaledMollifierKernel_integral_one 3 ε) hu₀.aestronglyMeasurable hBs
    have hEq : Q y = ∫ z, k z • u₀ (y-z) := by
      unfold Q
      rw [← integral_sub_left_eq_self (fun z => k z • u₀ (y-z)) volume y]
      simp only [sub_sub_cancel, smul_eq_mul]
    rw [hEq]
    exact hB
  let q (y : Point) := Q y - 2*d
  have hq : ContDiff ℝ ∞ q := hQ.sub contDiff_const
  have hqLap (y : Point) (hy : y ∈ V) : 0 ≤ laplacian q y := by
    change 0 ≤ laplacian (fun y => Q y - 2*d) y
    rw [laplacian_scalar_sub_const]
    exact hQlap y hy
  have hqFront (y : Point) (hy : y ∈ frontier V) : q y ≤ 0 := by
    have h := hClose y (frontier_subset_closure hy)
    rw [Real.dist_eq] at h
    have hyD := (abs_le.mp h).2
    change Q y - 2*d ≤ 0
    linarith only [hyD, hVbd y hy,hd]
  have hCmp := nonpos_of_laplacian_nonneg_on_ball_subset hV (hVU.trans hSub)
    hq.continuous.continuousOn (hq.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn hqLap hqFront x
      (subset_closure hxV)
  have h := hClose x (subset_closure hxV)
  rw [Real.dist_eq] at h
  have hl := (abs_le.mp h).1
  change Q x - 2*d ≤ 0 at hCmp
  dsimp only [d] at hl hCmp
  linarith only [hl,hCmp,hxpos]

end Thesis

end
