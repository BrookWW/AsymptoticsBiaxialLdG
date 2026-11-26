module

public import Thesis.Upstream.CalderonZygmundInterpolation
import Thesis.Upstream.PoissonL4Kernel
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Prod

/-! Strong real convolution bounds from weak first-moment and strong second-moment bounds. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Convolution ENNReal Topology

namespace Thesis

@[expose] def realKernelConvolution (K f : Point → ℝ) : Point → ℝ :=
  K ⋆[ContinuousLinearMap.mul ℝ ℝ] f

theorem realKernelConvolution_apply (K f : Point → ℝ) (x : Point) :
    realKernelConvolution K f x = ∫ y, K (x-y)*f y := by
  unfold realKernelConvolution
  rw [convolution_mul_swap]

private theorem integrable_realKernelConvolution_integrand {K f : Point → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K) (hf : Integrable f) (x : Point) :
    Integrable (fun y => K (x-y)*f y) := by
  simpa only [ContinuousLinearMap.mul_apply',mul_comm] using
    (hKc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable hK x).integrable

private theorem continuous_realKernelConvolution {K f : Point → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K) (hf : Integrable f) :
    Continuous (realKernelConvolution K f) :=
  hKc.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hK hf.locallyIntegrable

private theorem integrable_sq_of_integrable_abs_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : Integrable f μ) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    Integrable (fun x => |f x|^2) μ := by
  refine (hf.abs.const_mul B).mono' (hf.abs.aestronglyMeasurable.pow 2) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _),pow_two]
  exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)

private theorem integrable_sq_realKernelConvolution {K f : Point → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K) (hf : Integrable f) :
    Integrable (fun x => |realKernelConvolution K f x|^2) := by
  have hKI : Integrable K := hK.integrable_of_hasCompactSupport hKc
  have hI : Integrable (realKernelConvolution K f) := hKI.integrable_convolution _ hf
  obtain ⟨C,hC⟩ := hK.norm.bddAbove_range_of_hasCompactSupport hKc.norm
  apply integrable_sq_of_integrable_abs_le hI (B := C * ∫ y, ‖f y‖)
  intro x
  rw [realKernelConvolution_apply,← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hf.norm.const_mul C) (Eventually.of_forall fun y => ?_)).trans_eq
    (integral_const_mul _ _)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC ⟨x-y,rfl⟩) (norm_nonneg _)

private theorem abs_measure_superlevel_le_sq_integral {f : Point → ℝ} (hf : Measurable f)
    {t : ℝ} (ht : 0 < t) :
    volume {x | t/2 < |f x|} ≤ ENNReal.ofReal (4*(t^2)⁻¹) * ∫⁻ x, ENNReal.ofReal (|f x|^2) := by
  have ht₂ : 0 < (t/2)^2 := sq_pos_of_pos (half_pos ht)
  have hm : Measurable (fun x => ENNReal.ofReal (|f x|^2)) := (hf.abs.pow_const (2:ℕ)).ennreal_ofReal
  calc
    _ ≤ volume {x | ENNReal.ofReal ((t/2)^2) ≤ ENNReal.ofReal (|f x|^2)} := by
      apply measure_mono
      intro x hx
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (half_pos ht).le hx.le 2)
    _ ≤ (∫⁻ x, ENNReal.ofReal (|f x|^2)) / ENNReal.ofReal ((t/2)^2) :=
      meas_ge_le_lintegral_div hm.aemeasurable (ENNReal.ofReal_pos.mpr ht₂).ne' ENNReal.ofReal_ne_top
    _ = _ := by
      rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos ht₂, mul_comm]
      have he : ((t/2)^2)⁻¹ = 4*(t^2)⁻¹ := by
        field_simp
        ring
      rw [he]

private theorem eLpNorm_eq_abs_moment_rpow {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (g : X → ℝ) {p : ℝ} (hp : 0 < p) :
    eLpNorm g (ENNReal.ofReal p) μ = (∫⁻ x, ENNReal.ofReal (|g x|^p) ∂μ)^(p⁻¹) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, one_div]
  simp_rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]

private theorem eLpNorm_le_of_abs_moment_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g f : X → ℝ} {p : ℝ} (hp : 0 < p) (A : ℝ≥0∞)
    (h : (∫⁻ x, ENNReal.ofReal (|g x|^p) ∂μ) ≤ A * ∫⁻ x, ENNReal.ofReal (|f x|^p) ∂μ) :
    eLpNorm g (ENNReal.ofReal p) μ ≤ A^(p⁻¹) * eLpNorm f (ENNReal.ofReal p) μ := by
  rw [eLpNorm_eq_abs_moment_rpow g hp, eLpNorm_eq_abs_moment_rpow f hp, ← ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le)]
  exact ENNReal.rpow_le_rpow h (inv_nonneg.mpr hp.le)

/-- First- and second-moment convolution bounds imply a quantitative strong
bound at every intermediate real exponent. -/
theorem realKernelConvolution_intermediateLp {K : Point → ℝ} (hK : Continuous K) (hKc : HasCompactSupport K)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hWeak : ∀ (f : Point → ℝ), Integrable f → ∀ t : ℝ, 0 < t →
      volume {x | t < |realKernelConvolution K f x|} ≤ ENNReal.ofReal (A * (∫ x, |f x|)/t))
    (hStrong : ∀ (f : Point → ℝ), Integrable f → MemLp f 2 →
      (∫ x, |realKernelConvolution K f x|^2) ≤ B*(∫ x, |f x|^2))
    {p : ℝ} (hp : 1 < p) (hq : p < 2) {f : Point → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    eLpNorm (realKernelConvolution K f) (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal (p * (2*A/(p-1)+4*B/(2-p))))^(p⁻¹) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  have hG := continuous_realKernelConvolution hK hKc hfi
  have hTail (t : ℝ) (ht : 0 < t) :
      volume {y | t < |realKernelConvolution K f y|} ≤
        ENNReal.ofReal (2*A) * ENNReal.ofReal (t⁻¹) * (∫⁻ x, if t < |f x| then ENNReal.ofReal |f x| else 0) +
        ENNReal.ofReal (4*B) * ENNReal.ofReal ((t^2)⁻¹) * (∫⁻ x, if |f x| ≤ t then ENNReal.ofReal (|f x|^2) else 0) := by
    let S := {x | t < |f x|}
    have hS : MeasurableSet S := measurableSet_lt measurable_const hf.measurable.abs
    let h := S.indicator f
    let l := Sᶜ.indicator f
    have hI : Integrable h := hfi.indicator hS
    have lI : Integrable l := hfi.indicator hS.compl
    have hlB (x : Point) : |l x| ≤ t := by
      dsimp only [l]
      by_cases hx : x ∈ S
      · rw [indicator_of_notMem (show x ∉ Sᶜ from by simpa using hx),abs_zero]
        exact ht.le
      · rw [indicator_of_mem (show x ∈ Sᶜ from hx)]
        exact le_of_not_gt hx
    have hlSq := integrable_sq_of_integrable_abs_le lI hlB
    have hl₂ : MemLp l 2 := (memLp_two_iff_integrable_sq_norm lI.aestronglyMeasurable).2
      (by simpa only [Real.norm_eq_abs] using hlSq)
    have he (x : Point) : realKernelConvolution K f x = realKernelConvolution K h x + realKernelConvolution K l x := by
      simp only [realKernelConvolution_apply,← integral_add (integrable_realKernelConvolution_integrand hK hKc hI x)
        (integrable_realKernelConvolution_integrand hK hKc lI x), ← mul_add]
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [h,l]
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy,indicator_of_notMem (show y ∉ Sᶜ from by simpa using hy),add_zero]
      · rw [indicator_of_notMem hy,indicator_of_mem (show y ∈ Sᶜ from hy),zero_add]
    have hSub : {y | t < |realKernelConvolution K f y|} ⊆
        {y | t/2 < |realKernelConvolution K h y|} ∪ {y | t/2 < |realKernelConvolution K l y|} := by
      intro x hx
      by_contra! hN
      rw [mem_union, Set.mem_setOf, Set.mem_setOf, not_or] at hN
      have hex : t < |realKernelConvolution K f x| := hx
      rw [he] at hex
      linarith only [hex, abs_add_le (realKernelConvolution K h x) (realKernelConvolution K l x),
        le_of_not_gt hN.1,le_of_not_gt hN.2]
    have hHigh := hWeak h hI (t/2) (half_pos ht)
    rw [show A*(∫ x, |h x|)/(t/2) = (2*A)*t⁻¹*(∫ x, |h x|) by ring,
      ENNReal.ofReal_mul (mul_nonneg (by positivity : 0 ≤ 2*A) (inv_nonneg.mpr ht.le)),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 2*A),
      ofReal_integral_eq_lintegral_ofReal hI.abs (Eventually.of_forall fun _ => abs_nonneg _)] at hHigh
    have hLow := abs_measure_superlevel_le_sq_integral (continuous_realKernelConvolution hK hKc lI).measurable ht
    have hLowSq := integrable_sq_realKernelConvolution hK hKc lI
    have hLowBound := ENNReal.ofReal_le_ofReal (hStrong l lI hl₂)
    rw [ofReal_integral_eq_lintegral_ofReal hLowSq (Eventually.of_forall fun _ => sq_nonneg _),
      ENNReal.ofReal_mul hB,ofReal_integral_eq_lintegral_ofReal hlSq (Eventually.of_forall fun _ => sq_nonneg _)] at hLowBound
    have hLow' := hLow.trans (mul_le_mul_right hLowBound (ENNReal.ofReal (4*(t^2)⁻¹)))
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)] at hLow'
    rw [← mul_assoc, mul_right_comm (ENNReal.ofReal 4), ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)] at hLow'
    refine (measure_mono hSub).trans ((measure_union_le _ _).trans (add_le_add (hHigh.trans_eq ?_) (hLow'.trans_eq ?_)))
    · congr 1
      apply lintegral_congr
      intro x
      by_cases hx : t < |f x| <;> simp [h,S,hx]
    · congr 1
      apply lintegral_congr
      intro x
      by_cases hx : |f x| ≤ t
      · simp [l,S,hx,not_lt_of_ge hx]
      · simp [l,S,hx,lt_of_not_ge hx]
  have hM := cz_strong_moment_of_truncated_superlevel (μ := volume) (ν := volume)
    hf.measurable hG.measurable.aemeasurable hp hq (ENNReal.ofReal (2*A)) (ENNReal.ofReal (4*B)) hTail
  have hC : ENNReal.ofReal p * (ENNReal.ofReal (2*A)*ENNReal.ofReal ((p-1)⁻¹)+
      ENNReal.ofReal (4*B)*ENNReal.ofReal ((2-p)⁻¹)) = ENNReal.ofReal (p*(2*A/(p-1)+4*B/(2-p))) := by
    have hp₁ : 0 < p-1 := sub_pos.mpr hp
    have hq₁ : 0 < 2-p := sub_pos.mpr hq
    rw [← ENNReal.ofReal_mul (by positivity : 0≤2*A), ← ENNReal.ofReal_mul (by positivity : 0≤4*B),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (zero_lt_one.trans hp).le,
      div_eq_mul_inv,div_eq_mul_inv]
  rw [hC] at hM
  exact eLpNorm_le_of_abs_moment_le (zero_lt_one.trans hp) _ hM

/-- The strong quadratic integral estimate in norm form. -/
theorem realKernelConvolution_L2 {K : Point → ℝ} (hK : Continuous K) (hKc : HasCompactSupport K)
    {B : ℝ} (hB : 0 ≤ B) {f : Point → ℝ} (hf : Integrable f) (hf₂ : MemLp f 2)
    (h : (∫ x, |realKernelConvolution K f x|^2) ≤ B*(∫ x, |f x|^2)) :
    eLpNorm (realKernelConvolution K f) 2 volume ≤
      ENNReal.ofReal (B^((2:ℝ)⁻¹)) * eLpNorm f 2 volume := by
  have hF : Integrable (fun x => |f x|^2) := by
    simpa only [Real.norm_eq_abs] using (memLp_two_iff_integrable_sq_norm hf₂.aestronglyMeasurable).1 hf₂
  have hG := integrable_sq_realKernelConvolution hK hKc hf
  have hh := ENNReal.ofReal_le_ofReal h
  rw [ofReal_integral_eq_lintegral_ofReal hG (Eventually.of_forall fun _ => sq_nonneg _),
    ENNReal.ofReal_mul hB, ofReal_integral_eq_lintegral_ofReal hF (Eventually.of_forall fun _ => sq_nonneg _)] at hh
  simp only [← Real.rpow_two] at hh
  have hNorm := eLpNorm_le_of_abs_moment_le (μ := (volume : Measure Point)) (p := 2) two_pos
    (ENNReal.ofReal B) hh
  simpa only [ENNReal.ofReal_ofNat, ← ENNReal.ofReal_rpow_of_nonneg hB (by norm_num : (0:ℝ) ≤ 2⁻¹)] using hNorm

private theorem realKernelConvolution_neg {K f : Point → ℝ} (x : Point) :
    realKernelConvolution (fun z => K (-z)) f x =
      realKernelConvolution K (fun y => f (-y)) (-x) := by
  simp only [realKernelConvolution_apply]
  rw [← integral_neg_eq_self (fun y => K (-x-y)*f (-y)) volume]
  simp only [neg_sub,neg_neg,neg_sub_neg]

private theorem integral_realKernelConvolution_mul_swap {K f w : Point → ℝ}
    (hK : Continuous K) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hw : Continuous w) (hwc : HasCompactSupport w) :
    (∫ x, realKernelConvolution K f x*w x) =
      ∫ y, f y*realKernelConvolution (fun z => K (-z)) w y := by
  let F (x y : Point) := K (x-y)*f y*w x
  have hC : Continuous (Function.uncurry F) := by
    change Continuous (fun z : Point × Point => K (z.1-z.2)*f z.2*w z.1)
    fun_prop
  have hS : HasCompactSupport (Function.uncurry F) := by
    refine HasCompactSupport.intro (hwc.prod hfc) ?_
    intro z hz
    change K (z.1-z.2)*f z.2*w z.1 = 0
    by_cases hz₁ : z.1 ∈ tsupport w
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hz ⟨hz₁,h⟩),mul_zero,zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz₁,mul_zero]
  calc
    _ = ∫ x, ∫ y, F x y := by
      congr 1 with x
      rw [realKernelConvolution_apply, ← integral_mul_const]
    _ = ∫ y, ∫ x, F x y := integral_integral_swap_of_hasCompactSupport hC hS
    _ = _ := by
      simp only [realKernelConvolution_apply, ← integral_const_mul,neg_sub]
      congr 1 with y
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [F]
      ring

private theorem integral_abs_rpow_eq_eLpNorm_toReal_rpow {H : Point → ℝ} {p : ℝ} (hp : 0 < p)
    (hH : MemLp H (ENNReal.ofReal p) volume) :
    (∫ x, |H x|^p) = (eLpNorm H (ENNReal.ofReal p) volume).toReal^p := by
  have hJ : Integrable (fun x => |H x|^p) := by
    simpa only [ENNReal.toReal_ofReal hp.le,Real.norm_eq_abs] using
      hH.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
  have h₀ (x : Point) : 0 ≤ |H x|^p := Real.rpow_nonneg (abs_nonneg _) _
  rw [ENNReal.toReal_rpow,eLpNorm_eq_abs_moment_rpow H hp,← ENNReal.rpow_mul,
    inv_mul_cancel₀ hp.ne',ENNReal.rpow_one,
    ← ofReal_integral_eq_lintegral_ofReal hJ (Eventually.of_forall h₀),
    ENNReal.toReal_ofReal (integral_nonneg h₀)]

/-- The reflected kernel is the adjoint on compactly supported functions.
A bound at the conjugate exponent therefore gives the same bound at `p`. -/
theorem realKernelConvolution_dualLp {K : Point → ℝ} (hK : Continuous K) (hKc : HasCompactSupport K)
    {p : ℝ} (hp : 2 < p) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f : Point → ℝ, Continuous f → HasCompactSupport f →
      eLpNorm (realKernelConvolution K f) (ENNReal.ofReal p.conjExponent) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p.conjExponent) volume)
    {f : Point → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    eLpNorm (realKernelConvolution K f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp₁ : 1 < p := (by norm_num : (1:ℝ) < 2).trans hp
  have hp₀ : 0 < p := zero_lt_one.trans hp₁
  let q := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp₁
  have hq : 0 < q := hpq.symm.pos
  let H := realKernelConvolution K f
  have hfI : Integrable f := hf.integrable_of_hasCompactSupport hfc
  have hH : Continuous H := continuous_realKernelConvolution hK hKc hfI
  have hHc : HasCompactSupport H := hKc.convolution _ hfc
  have hHp : MemLp H (ENNReal.ofReal p) volume := hH.memLp_of_hasCompactSupport hHc
  have hfp : MemLp f (ENNReal.ofReal p) volume := hf.memLp_of_hasCompactSupport hfc
  let V := (eLpNorm H (ENNReal.ofReal p) volume).toReal
  let U := (eLpNorm f (ENNReal.ofReal p) volume).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hU : 0 ≤ U := ENNReal.toReal_nonneg
  let w (x : Point) := H x*|H x|^(p-2)
  have hp₂ : 0 < p-2 := sub_pos.mpr hp
  have hPow : Continuous (fun x : Point => |H x|^(p-2)) :=
    hH.abs.rpow_const (fun x => Or.inr hp₂.le)
  have hw : Continuous w := hH.mul hPow
  have hwc : HasCompactSupport w := hHc.mul_right
  let W := realKernelConvolution (fun z => K (-z)) w
  have hwI : Integrable w := hw.integrable_of_hasCompactSupport hwc
  have hW : Continuous W := continuous_realKernelConvolution (hK.comp continuous_neg)
    (hKc.comp_homeomorph (Homeomorph.neg Point)) hwI
  have hWc : HasCompactSupport W := (hKc.comp_homeomorph (Homeomorph.neg Point)).convolution _ hwc
  have hWq : MemLp W (ENNReal.ofReal q) volume := hW.memLp_of_hasCompactSupport hWc
  have hwq : MemLp w (ENNReal.ofReal q) volume := hw.memLp_of_hasCompactSupport hwc
  have hNeg := Measure.measurePreserving_neg (volume : Measure Point)
  have hWNorm : eLpNorm W (ENNReal.ofReal q) volume ≤ ENNReal.ofReal C * eLpNorm w (ENNReal.ofReal q) volume := by
    let wN (y : Point) := w (-y)
    have hwN : Continuous wN := hw.comp continuous_neg
    have hwNc : HasCompactSupport wN := hwc.comp_homeomorph (Homeomorph.neg Point)
    have hwNI : Integrable wN := hwN.integrable_of_hasCompactSupport hwNc
    have hhW : W = (realKernelConvolution K wN) ∘ Neg.neg := funext (realKernelConvolution_neg (K := K) (f := w))
    rw [hhW,eLpNorm_comp_measurePreserving
      (continuous_realKernelConvolution hK hKc hwNI).aestronglyMeasurable hNeg]
    have hh := h wN hwN hwNc
    change eLpNorm (realKernelConvolution K wN) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal C * eLpNorm (w ∘ Neg.neg) (ENNReal.ofReal q) volume at hh
    rwa [eLpNorm_comp_measurePreserving hw.aestronglyMeasurable hNeg] at hh
  have hWNormR : (eLpNorm W (ENNReal.ofReal q) volume).toReal ≤ C *(eLpNorm w (ENNReal.ofReal q) volume).toReal := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwq.eLpNorm_ne_top) hWNorm
    rwa [ENNReal.toReal_mul,ENNReal.toReal_ofReal hC] at hh
  have hAbs (x : Point) : |w x| = |H x|^(p-1) := by
    dsimp only [w]
    rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    by_cases hx : |H x| = 0
    · rw [hx,zero_mul,Real.zero_rpow (sub_pos.mpr hp₁).ne']
    · have hx₀ := lt_of_le_of_ne (abs_nonneg (H x)) (Ne.symm hx)
      nth_rw 1 [← Real.rpow_one |H x|]
      rw [← Real.rpow_add hx₀,show 1+(p-2)=p-1 by ring]
  have hwNorm : (eLpNorm w (ENNReal.ofReal q) volume).toReal = V^(p-1) := by
    have he := eLpNorm_congr_norm_ae (μ := (volume : Measure Point)) (p := ENNReal.ofReal q)
      (f := w) (g := fun x => ‖H x‖^(p-1)) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs (w x),hAbs,Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),Real.norm_eq_abs])
    have hEq : q*(p-1)=p := by
      dsimp only [q,Real.conjExponent]
      exact div_mul_cancel₀ _ (sub_pos.mpr hp₁).ne'
    rw [he,eLpNorm_norm_rpow _ (sub_pos.mpr hp₁),← ENNReal.ofReal_mul hq.le,hEq,ENNReal.toReal_rpow]
  have hHprod (x : Point) : H x*w x = |H x|^p := by
    dsimp only [w]
    rw [← mul_assoc,← pow_two,← sq_abs]
    by_cases hx : |H x|=0
    · simp [hx,Real.zero_rpow hp₀.ne']
    · rw [← Real.rpow_two,← Real.rpow_add (lt_of_le_of_ne (abs_nonneg (H x)) (Ne.symm hx)),
        show 2+(p-2)=p by ring]
  have hP : V^p ≤ U * (C*V^(p-1)) := by
    calc
      _ = ∫ x, |H x|^p := (integral_abs_rpow_eq_eLpNorm_toReal_rpow hp₀ hHp).symm
      _ = ∫ x, H x*w x := integral_congr_ae (Eventually.of_forall fun x => (hHprod x).symm)
      _ = ∫ y, f y*W y := integral_realKernelConvolution_mul_swap hK hf hfc hw hwc
      _ ≤ ∫ y, ‖f y‖*‖W y‖ := integral_mono
        ((hf.mul hW).integrable_of_hasCompactSupport hfc.mul_right)
        ((hf.norm.mul hW.norm).integrable_of_hasCompactSupport hfc.norm.mul_right)
        (fun _ => by rw [← norm_mul]; exact le_abs_self _)
      _ ≤ U * (eLpNorm W (ENNReal.ofReal q) volume).toReal :=
        integral_norm_mul_le_realLp_mul hpq hfp hWq
      _ ≤ _ := mul_le_mul_of_nonneg_left (hwNorm ▸ hWNormR) hU
  have hVFinal : V ≤ C*U := by
    by_cases he : V=0
    · rw [he]
      positivity
    have hv : 0 < V := lt_of_le_of_ne hV (Ne.symm he)
    have hE : V^p = V*V^(p-1) := by
      symm
      nth_rw 1 [← Real.rpow_one V]
      rw [← Real.rpow_add hv,show 1+(p-1)=p by ring]
    rw [hE,show U*(C*V^(p-1)) = (C*U)*V^(p-1) by ring] at hP
    exact le_of_mul_le_mul_right hP (Real.rpow_pos_of_pos hv _)
  change eLpNorm H (ENNReal.ofReal p) volume ≤ _
  have hE := ENNReal.ofReal_le_ofReal hVFinal
  dsimp only [V,U] at hE
  rwa [ENNReal.ofReal_toReal hHp.eLpNorm_ne_top,ENNReal.ofReal_mul hC,
    ENNReal.ofReal_toReal hfp.eLpNorm_ne_top] at hE

end Thesis

end
