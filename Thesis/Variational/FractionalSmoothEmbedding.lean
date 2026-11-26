module

public import Thesis.Definitions
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! The fractional seminorm estimate for smooth fields from their
first derivatives, using translations and the Euclidean radial kernel. -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped BigOperators ContDiff ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem integrableOn_fractional_displacement_kernel
    (s R : ℝ) (hs : s < 1) (hR : 0 < R) :
    IntegrableOn (fun z : Point => ‖z‖ ^ (-1 - 2 * s)) (ball (0 : Point) R) := by
  apply (integrableOn_fun_norm_addHaar (μ := (volume : Measure Point))
    (f := fun t : ℝ => t ^ (-1 - 2 * s))).2
  have h : IntegrableOn (fun t : ℝ => t ^ (1 - 2 * s)) (Ioo 0 R) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hR).2 (by linarith)
  refine (integrableOn_congr_fun ?_ measurableSet_Ioo).2 h
  intro t ht
  rw [show Module.finrank ℝ Point - 1 = 2 by simp [Point]]
  change t ^ (2 : ℕ) * t ^ (-1 - 2 * s) = t ^ (1 - 2 * s)
  rw [← Real.rpow_natCast, ← Real.rpow_add ht.1]
  congr 1
  push_cast
  ring

private def smoothGradientSq (f : Point → S0) (x : Point) : ℝ :=
  ∑ j : Fin 3, ‖coordDeriv j f x‖ ^ 2

private theorem smoothGradientSq_nonneg (f : Point → S0) (x : Point) :
    0 ≤ smoothGradientSq f x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem continuous_smoothGradientSq {f : Point → S0} (hf : ContDiff ℝ ∞ f) :
    Continuous (smoothGradientSq f) := by
  have hD (j : Fin 3) : Continuous (coordDeriv j f) := by
    exact (ContinuousLinearMap.apply ℝ S0 (axis j)).continuous.comp
      (hf.continuous_fderiv (by simp))
  exact continuous_finsetSum _ fun j _ => (hD j).norm.pow 2

private theorem norm_directional_derivative_sq_le
    (f : Point → S0) (x z : Point) :
    ‖fderiv ℝ f x z‖ ^ 2 ≤ 9 * ‖z‖ ^ 2 * smoothGradientSq f x := by
  let L := fderiv ℝ f x
  have hz : (∑ j : Fin 3, z j • axis j) = z := by
    apply PiLp.ext
    intro j
    fin_cases j <;> simp [axis, Fin.sum_univ_three]
  have hL : L z = ∑ j : Fin 3, z j • L (axis j) := by
    conv_lhs => rw [← hz]
    rw [map_sum]
    simp only [map_smul]
  have hCoord (j : Fin 3) : ‖L (axis j)‖ ≤ Real.sqrt (smoothGradientSq f x) :=
    Real.le_sqrt_of_sq_le (Finset.single_le_sum
      (f := fun j : Fin 3 => ‖coordDeriv j f x‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j))
  have hBound : ‖L z‖ ≤ 3 * ‖z‖ * Real.sqrt (smoothGradientSq f x) := by
    rw [hL]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _j : Fin 3, ‖z‖ * Real.sqrt (smoothGradientSq f x) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul]
        exact mul_le_mul (PiLp.norm_apply_le z j) (hCoord j) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by simp; ring
  calc
    _ ≤ (3 * ‖z‖ * Real.sqrt (smoothGradientSq f x)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hBound 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (smoothGradientSq_nonneg f x)]
      ring

private theorem sq_translation_difference_le_line_integral
    {f : Point → S0} (hf : ContDiff ℝ ∞ f) (x z : Point) :
    ‖f (x + z) - f x‖ ^ 2 ≤ 9 * ‖z‖ ^ 2 *
      ∫ t in Ioc (0 : ℝ) 1, smoothGradientSq f (x + t • z) := by
  let P (t : ℝ) := x + t • z
  let D (t : ℝ) := fderiv ℝ f (P t) z
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  have hP : Continuous P := continuous_const.add (continuous_id.smul continuous_const)
  have hDc : Continuous D :=
    (ContinuousLinearMap.apply ℝ S0 z).continuous.comp ((hf.continuous_fderiv (by simp)).comp hP)
  have hP' (t : ℝ) : HasDerivAt P z t := by
    simpa [P] using ((hasDerivAt_id t).smul_const z).const_add x
  have hDer (t : ℝ) : HasDerivAt (f ∘ P) (D t) t :=
    ((hf.differentiable (by simp) (P t)).hasFDerivAt).comp_hasDerivAt t (hP' t)
  have hSeg := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hDer t)
    (hDc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le zero_le_one] at hSeg
  have hF : ∫ t, D t ∂μ = f (x + z) - f x := by
    simpa only [μ, P, Function.comp_apply, one_smul, zero_smul, add_zero] using hSeg
  have hNorm : ‖f (x + z) - f x‖ ≤ ∫ t, ‖D t‖ ∂μ := by
    rw [← hF]
    exact norm_integral_le_integral_norm _
  letI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have hNormInt : Integrable (fun t => ‖D t‖) μ := hDc.norm.integrableOn_Ioc
  have hNormSqInt : Integrable (fun t => ‖D t‖ ^ 2) μ := (hDc.norm.pow 2).integrableOn_Ioc
  have hSq := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le
    (((continuous_id : Continuous (id : ℝ → ℝ)).pow 2).continuousOn)
    isClosed_Ici (.of_forall fun t => norm_nonneg (D t)) hNormInt hNormSqInt
  have hG (t : ℝ) :
      ‖D t‖ ^ 2 ≤ (9 * ‖z‖ ^ 2) * smoothGradientSq f (P t) :=
    norm_directional_derivative_sq_le f (P t) z
  have hGInt : Integrable (fun t => smoothGradientSq f (P t)) μ :=
    ((continuous_smoothGradientSq hf).comp hP).integrableOn_Ioc
  calc
    _ ≤ (∫ t, ‖D t‖ ∂μ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
    _ ≤ ∫ t, ‖D t‖ ^ 2 ∂μ := hSq
    _ ≤ ∫ t, (9 * ‖z‖ ^ 2) * smoothGradientSq f (P t) ∂μ :=
      integral_mono hNormSqInt (hGInt.const_mul _) hG
    _ = _ := integral_const_mul _ _

private theorem lintegral_sq_translation_difference_le
    {f : Point → S0} (hf : ContDiff ℝ ∞ f) (z : Point) :
    ∫⁻ x, ENNReal.ofReal (‖f (x + z) - f x‖ ^ 2) ≤
      ENNReal.ofReal (9 * ‖z‖ ^ 2) * ∫⁻ x, ENNReal.ofReal (smoothGradientSq f x) := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let G (x : Point) (t : ℝ) := smoothGradientSq f (x + t • z)
  have hGc : Continuous (Function.uncurry G) :=
    (continuous_smoothGradientSq hf).comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hGInt (x : Point) : Integrable (G x) μ :=
    ((continuous_smoothGradientSq hf).comp (continuous_const.add (continuous_id.smul continuous_const))).integrableOn_Ioc
  let c := ENNReal.ofReal (9 * ‖z‖ ^ 2)
  have hMeas : Measurable (fun p : Point × ℝ => ENNReal.ofReal (G p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp hGc.measurable
  calc
    _ ≤ ∫⁻ x : Point, c * ∫⁻ t, ENNReal.ofReal (G x t) ∂μ := by
      apply lintegral_mono
      intro x
      refine (ENNReal.ofReal_le_ofReal (sq_translation_difference_le_line_integral hf x z)).trans_eq ?_
      rw [ENNReal.ofReal_mul (by positivity), ofReal_integral_eq_lintegral_ofReal (hGInt x)]
      exact .of_forall fun t => smoothGradientSq_nonneg f _
    _ = c * ∫⁻ x : Point, ∫⁻ t, ENNReal.ofReal (G x t) ∂μ := by
      rw [lintegral_const_mul'' _ hMeas.lintegral_prod_right.aemeasurable]
    _ = c * (∫⁻ t, (∫⁻ x : Point, ENNReal.ofReal (G x t)) ∂μ) := by
      rw [lintegral_lintegral_swap hMeas.aemeasurable]
    _ = _ := by
      have hTrans (t : ℝ) :
          ∫⁻ x : Point, ENNReal.ofReal (G x t) = ∫⁻ x : Point, ENNReal.ofReal (smoothGradientSq f x) := by
        change (∫⁻ x : Point, ENNReal.ofReal (smoothGradientSq f (x + t • z))) = _
        exact lintegral_add_right_eq_self (fun y : Point => ENNReal.ofReal (smoothGradientSq f y)) _
      simp only [hTrans, lintegral_const, μ, c, Measure.restrict_apply_univ, Real.volume_Ioc,
        sub_zero, ENNReal.ofReal_one, mul_one]

/-- The squared (L^2) translation error is bounded by the squared displacement
times the Dirichlet energy of the actual smooth columns. -/
theorem lintegral_sq_smooth_translation_difference_le
    {f : Point → S0} (hf : ContDiff ℝ ∞ f) (z : Point) :
    (∫⁻ x, ENNReal.ofReal (‖f (x + z) - f x‖ ^ 2)) ≤
      ENNReal.ofReal (9 * ‖z‖ ^ 2) * ∫⁻ x, ENNReal.ofReal (∑ j : Fin 3, ‖coordDeriv j f x‖ ^ 2) :=
  lintegral_sq_translation_difference_le hf z

private theorem sq_mul_inv_displacement_power (s : ℝ) (hs : 0 < s) (z : Point) :
    ‖z‖ ^ (2 : ℕ) * (‖z‖ ^ (3 + 2 * s))⁻¹ = ‖z‖ ^ (-1 - 2 * s) := by
  by_cases hz : z = 0
  · simp only [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    rw [Real.zero_rpow (by linarith : (-1 - 2 * s) ≠ 0)]
  · rw [← Real.rpow_neg (norm_nonneg z), ← Real.rpow_natCast,
      ← Real.rpow_add (norm_pos_iff.mpr hz)]
    congr 1
    push_cast
    ring

private theorem lintegral_fractional_displacement_le
    {s : ℝ} (hs : 0 < s) {f : Point → S0} (hf : ContDiff ℝ ∞ f) (z : Point) :
    (∫⁻ x : Point, ENNReal.ofReal (‖f x - f (x + z)‖ ^ 2 / ‖z‖ ^ (3 + 2 * s))) ≤
      ENNReal.ofReal 9 * (∫⁻ x : Point, ENNReal.ofReal (smoothGradientSq f x)) *
        ENNReal.ofReal (‖z‖ ^ (-1 - 2 * s)) := by
  let k := (‖z‖ ^ (3 + 2 * s))⁻¹
  let v (x : Point) := ENNReal.ofReal (‖f (x + z) - f x‖ ^ 2)
  have hCont : Continuous (fun x : Point => f (x + z) - f x) :=
    (hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous
  have hv : Measurable v := ENNReal.measurable_ofReal.comp (hCont.norm.pow 2).measurable
  have hEq (x : Point) : ENNReal.ofReal (‖f x - f (x + z)‖ ^ 2 / ‖z‖ ^ (3 + 2 * s)) =
      v x * ENNReal.ofReal k := by
    rw [norm_sub_rev, div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _)]
  simp only [hEq, lintegral_mul_const'' (ENNReal.ofReal k) hv.aemeasurable]
  have h := lintegral_sq_translation_difference_le hf z
  refine (mul_le_mul' h le_rfl).trans_eq ?_
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9)]
  let G := ∫⁻ x : Point, ENNReal.ofReal (smoothGradientSq f x)
  change ENNReal.ofReal 9 * ENNReal.ofReal (‖z‖ ^ 2) * G * ENNReal.ofReal k =
    ENNReal.ofReal 9 * G * ENNReal.ofReal (‖z‖ ^ (-1 - 2 * s))
  calc
    _ = ENNReal.ofReal 9 * G * (ENNReal.ofReal (‖z‖ ^ 2) * ENNReal.ofReal k) := by ac_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (sq_nonneg _), sq_mul_inv_displacement_power s hs]

private theorem exists_nonlocal_energy_le_of_smooth
    {U : Set Point} (hU : IsBoundedDomain U) (s : ℝ) (hs : 0 < s) (hs₁ : s < 1) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (f : Point → S0), ContDiff ℝ ∞ f →
      (∫⁻ x in U, ∫⁻ y in U, ENNReal.ofReal (‖f x - f y‖ ^ 2 / dist x y ^ (3 + 2 * s))) ≤
        K * ∫⁻ x : Point, ENNReal.ofReal (smoothGradientSq f x) := by
  let R := Metric.diam U + 1
  have hR : 0 < R := add_pos_of_nonneg_of_pos Metric.diam_nonneg zero_lt_one
  let V := ball (0 : Point) R
  let w (z : Point) := ENNReal.ofReal (‖z‖ ^ (-1 - 2 * s))
  let K := ENNReal.ofReal 9 * (∫⁻ z in V, w z)
  have hW := integrableOn_fractional_displacement_kernel s R hs₁ hR
  have hK : K < ⊤ := by
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    have he : (∫⁻ z in V, w z) = ∫⁻ z in V, ‖‖z‖ ^ (-1 - 2 * s)‖ₑ := by
      apply lintegral_congr
      intro z
      dsimp only [w]
      rw [← ofReal_norm, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    rw [he]
    exact hW.2
  refine ⟨K,hK,?_⟩
  intro f hf
  let N (x y : Point) := ENNReal.ofReal (‖f x - f y‖ ^ 2 / dist x y ^ (3 + 2 * s))
  let T (x z : Point) := ENNReal.ofReal (‖f x - f (x + z)‖ ^ 2 / ‖z‖ ^ (3 + 2 * s))
  have hNum : Continuous (fun p : Point × Point => ‖f p.1 - f (p.1 + p.2)‖ ^ 2) :=
    (((hf.continuous.comp continuous_fst).sub
      (hf.continuous.comp (continuous_fst.add continuous_snd))).norm.pow 2)
  have hDen : Measurable (fun p : Point × Point => ‖p.2‖ ^ (3 + 2 * s)) := by fun_prop
  have hT : Measurable (Function.uncurry T) :=
    ENNReal.measurable_ofReal.comp (hNum.measurable.div hDen)
  have hShift (x z : Point) : N x (x + z) = T x z := by
    have he : dist x (x + z) = ‖z‖ := by
      rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
    dsimp only [N,T]
    rw [he]
  have hCut (x : Point) (hx : x ∈ U) :
      ∫⁻ y in U, N x y ≤ ∫⁻ z in V, T x z := by
    rw [← lintegral_indicator hU.1.measurableSet, ← lintegral_indicator measurableSet_ball]
    have hTrans : (∫⁻ z : Point, U.indicator (N x) (x + z)) = ∫⁻ y : Point, U.indicator (N x) y := by
      simpa only [add_comm x] using
        (lintegral_add_right_eq_self (U.indicator (N x)) x)
    rw [← hTrans]
    apply lintegral_mono
    intro z
    change U.indicator (N x) (x + z) ≤ V.indicator (T x) z
    by_cases hz : x + z ∈ U
    · have hzV : z ∈ V := by
        rw [mem_ball, dist_zero_right, ← show dist x (x+z) = ‖z‖ by
          rw [dist_comm, dist_eq_norm, add_sub_cancel_left]]
        exact (dist_le_diam_of_mem hU.2.2 hx hz).trans_lt
          (lt_add_of_pos_right _ zero_lt_one)
      rw [indicator_of_mem hz, indicator_of_mem hzV, hShift]
    · rw [indicator_of_notMem hz]
      exact bot_le
  let G := ∫⁻ x : Point, ENNReal.ofReal (smoothGradientSq f x)
  have hw : Measurable w := by dsimp only [w]; fun_prop
  calc
    (∫⁻ x in U, ∫⁻ y in U, N x y) ≤ ∫⁻ x in U, ∫⁻ z in V, T x z :=
      setLIntegral_mono' hU.1.measurableSet hCut
    _ ≤ ∫⁻ x : Point, ∫⁻ z in V, T x z := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ z in V, ∫⁻ x : Point, T x z := lintegral_lintegral_swap hT.aemeasurable
    _ ≤ ∫⁻ z in V, (ENNReal.ofReal 9 * G) * w z :=
      lintegral_mono (lintegral_fractional_displacement_le hs hf)
    _ = K * G := by
      rw [lintegral_const_mul'' _ hw.aemeasurable]
      exact mul_right_comm _ _ _

/-- On a bounded domain the smooth fractional energy is controlled by the
actual squared first derivatives on the ambient space. -/
theorem exists_fractionalEnergy_le_of_smooth
    {U : Set Point} (hU : IsBoundedDomain U) (s : ℝ) (hs : 0 < s) (hs₁ : s < 1) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (f : Point → S0), ContDiff ℝ ∞ f →
      fractionalEnergy s U f ≤ (∫⁻ x in U, ENNReal.ofReal (‖f x‖ ^ 2)) +
        K * (∫⁻ x : Point, ENNReal.ofReal (∑ j : Fin 3, ‖coordDeriv j f x‖ ^ 2)) := by
  obtain ⟨K,hK,hBound⟩ := exists_nonlocal_energy_le_of_smooth hU s hs hs₁
  exact ⟨K,hK,fun f hf => add_le_add le_rfl (hBound f hf)⟩

end Thesis

end
