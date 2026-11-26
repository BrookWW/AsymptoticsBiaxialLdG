module

public import SupportingAnalysis.Poisson.Decomposition
public import SupportingAnalysis.Basics
import SupportingAnalysis.Poisson.SquareBound
import SupportingAnalysis.Poisson.Limits
import HolderToCK.Analysis.Poisson.HessianNearFar

/-! The cutoff Hessian weak estimate by a finite Calderón–Zygmund decomposition. -/

public section

open MeasureTheory Metric Set Filter
open scoped BigOperators ContDiff Convolution ENNReal Topology

set_option autoImplicit false

namespace SupportingAnalysis

variable {d : ℕ}

/-- A uniform strict-superlevel bound passes to a pointwise limit. -/
theorem measure_abs_superlevel_le_of_pointwise_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : ℕ → X → ℝ} {g : X → ℝ}
    (hLim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) (a : ℝ) {B : ℝ≥0∞}
    (hm : ∀ n, μ {x | a < |f n x|} ≤ B) : μ {x | a < |g x|} ≤ B := by
  let S (n : ℕ) := {x | a < |f n x|}
  let T (n : ℕ) := ⋂ k, ⋂ _ : n ≤ k, S k
  have hTm : Monotone T := by
    intro n m hnm x hx
    exact mem_iInter.mpr fun k => mem_iInter.mpr fun hk =>
      mem_iInter.mp (mem_iInter.mp hx k) (hnm.trans hk)
  have hsub : {x | a < |g x|} ⊆ ⋃ n, T n := by
    intro x hx
    have hev : ∀ᶠ n in atTop, a < |f n x| :=
      (continuous_abs.continuousAt.tendsto.comp (hLim x)).eventually_const_lt hx
    obtain ⟨n, hn⟩ := eventually_atTop.mp hev
    exact mem_iUnion.mpr ⟨n, mem_iInter.mpr fun k => mem_iInter.mpr fun hk => hn k hk⟩
  have hTbound (n : ℕ) : μ (T n) ≤ B := by
    refine (measure_mono (show T n ⊆ S n from fun x hx =>
      mem_iInter.mp (mem_iInter.mp hx n) (le_refl n))).trans (hm n)
  have hTlim := tendsto_measure_iUnion_atTop (μ := μ) hTm
  exact (measure_mono hsub).trans (le_of_tendsto' hTlim hTbound)

private theorem measure_superlevel_le_integral {f : E d → ℝ} (hf : Integrable f)
    (hfn : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 < t) :
    volume {x | t < f x} ≤ ENNReal.ofReal ((∫ x, f x) / t) := by
  have ht' : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
  calc
    _ ≤ volume {x | ENNReal.ofReal t ≤ ENNReal.ofReal (f x)} :=
      measure_mono (fun x hx => ENNReal.ofReal_le_ofReal (le_of_lt hx))
    _ ≤ (∫⁻ x, ENNReal.ofReal (f x)) / ENNReal.ofReal t :=
      meas_ge_le_lintegral_div hf.aemeasurable.ennreal_ofReal ht' ENNReal.ofReal_ne_top
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos ht,
        ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hfn)]

private theorem memLp_two_of_integrable_abs_le {f : E d → ℝ} (hf : Integrable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : MemLp f 2 := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  have hmeas := (continuous_id.pow 2).comp_aestronglyMeasurable hf.aestronglyMeasurable.norm
  refine (hf.norm.const_mul C).mono' hmeas (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg ‖f x‖), pow_two]
  exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hC x) (norm_nonneg _)

private theorem convolution_add_finset {ι : Type*} [Fintype ι]
    {K a : E d → ℝ} {b : ι → E d → ℝ} (hK : Continuous K) (hKc : HasCompactSupport K)
    (ha : Integrable a) (hb : ∀ i, Integrable (b i)) (x : E d) :
    (K ⋆[ContinuousLinearMap.mul ℝ ℝ] (a + ∑ i, b i)) x =
      (K ⋆[ContinuousLinearMap.mul ℝ ℝ] a) x + ∑ i, (K ⋆[ContinuousLinearMap.mul ℝ ℝ] b i) x := by
  classical
  have hi {f : E d → ℝ} (hf : Integrable f) : Integrable (fun y => K (x - y) * f y) := by
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      (hKc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
        hf.locallyIntegrable hK x).integrable
  simp only [convolution_mul_swap, Pi.add_apply, Finset.sum_apply, mul_add, Finset.mul_sum]
  rw [integral_add (hi ha) (integrable_finsetSum _ fun i _ => hi (hb i)),
    integral_finsetSum _ fun i _ => hi (hb i)]

private theorem hessianKernel_sub_bound (hd : 0 < d) (i j : Fin d)
    {x z y : E d} {r : ℝ} (hx : x ∉ ball z (2 * r)) (hy : y ∈ ball z r) :
    |HolderToCK.hessianKernelExpression i j (x - y) -
      HolderToCK.hessianKernelExpression i j (x - z)| ≤
      HolderToCK.hessianKernelTranslationConstant d * r * ‖z - x‖ ^ (-(d : ℝ) - 1) := by
  have hdist : dist z y < r := by rw [dist_comm]; exact mem_ball.mp hy
  have hfar : 2 * dist z y ≤ ‖z - x‖ := by
    have hlow : 2 * r ≤ dist x z := not_lt.mp fun h => hx (mem_ball.mpr h)
    rw [norm_sub_rev, ← dist_eq_norm]
    linarith only [hdist, hlow]
  have h := HolderToCK.hessianKernelExpression_shift_difference_bound hd i j (-z) (-y) (-x) (by
    simpa only [dist_neg_neg, neg_sub_neg, norm_sub_rev] using hfar)
  rw [dist_neg_neg, neg_sub_neg, neg_sub_neg, abs_sub_comm, norm_sub_rev x z] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdist.le (HolderToCK.hessianKernelTranslationConstant_nonneg hd))
    (Real.rpow_nonneg (norm_nonneg _) _))

private noncomputable def centeredBadIntegral (i j : Fin d) (z : E d) (r : ℝ)
    (b : E d → ℝ) (x : E d) : ℝ :=
  ∫ y in ball z r,
    (HolderToCK.hessianKernelExpression i j (x - y) -
      HolderToCK.hessianKernelExpression i j (x - z)) * b y

private theorem centeredBadIntegral_integrableOn (hd : 0 < d) (i j : Fin d)
    {x z : E d} {r : ℝ} (hx : x ∉ ball z (2 * r)) {b : E d → ℝ}
    (hb : Integrable b) :
    IntegrableOn (fun y => (HolderToCK.hessianKernelExpression i j (x - y) -
      HolderToCK.hessianKernelExpression i j (x - z)) * b y) (ball z r) := by
  let M := HolderToCK.hessianKernelTranslationConstant d * r * ‖z - x‖ ^ (-(d : ℝ) - 1)
  have hk : Measurable fun y : E d => HolderToCK.hessianKernelExpression i j (x - y) :=
    (HolderToCK.hessianKernelExpression_measurable i j).comp
      (continuous_const.sub continuous_id).measurable
  have hInt : Integrable (fun y : E d => M * |b y|)
      (volume.restrict (ball z r)) := (hb.abs.const_mul M).integrableOn
  have hMeas : AEStronglyMeasurable (fun y : E d =>
      (HolderToCK.hessianKernelExpression i j (x - y) -
        HolderToCK.hessianKernelExpression i j (x - z)) * b y)
      (volume.restrict (ball z r)) :=
    ((hk.sub measurable_const).aestronglyMeasurable.mul hb.aestronglyMeasurable).restrict
  refine hInt.mono' hMeas ?_
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_ball : MeasurableSet (ball z r))]
    with y hy
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hessianKernel_sub_bound hd i j hx hy) (abs_nonneg _)

private theorem abs_centeredBadIntegral_le (hd : 0 < d) (i j : Fin d)
    {x z : E d} {r : ℝ} (hr : 0 < r) (hx : x ∉ ball z (2 * r)) {b : E d → ℝ}
    (hb : Integrable b) :
    |centeredBadIntegral i j z r b x| ≤ HolderToCK.hessianKernelTranslationConstant d *
      r * ‖z - x‖ ^ (-(d : ℝ) - 1) * ∫ y, |b y| := by
  let M := HolderToCK.hessianKernelTranslationConstant d * r * ‖z - x‖ ^ (-(d : ℝ) - 1)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (HolderToCK.hessianKernelTranslationConstant_nonneg hd) hr.le)
    (Real.rpow_nonneg (norm_nonneg _) _)
  have hi : IntegrableOn (fun y => M * |b y|) (ball z r) := (hb.abs.const_mul M).integrableOn
  have hl := norm_integral_le_of_norm_le hi (f := fun y =>
    (HolderToCK.hessianKernelExpression i j (x - y) -
      HolderToCK.hessianKernelExpression i j (x - z)) * b y) (by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_ball : MeasurableSet (ball z r))]
      with y hy
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hessianKernel_sub_bound hd i j hx hy) (abs_nonneg _))
  rw [Real.norm_eq_abs, integral_const_mul] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hb.abs (Eventually.of_forall fun _ => abs_nonneg _)) hM)

private theorem centeredBadIntegral_eq_integral (hd : 0 < d) (i j : Fin d)
    {x z : E d} {r : ℝ} (hx : x ∉ ball z (2 * r)) {b : E d → ℝ}
    (hb : Integrable b) (hbS : Function.support b ⊆ ball z r) (hb0 : (∫ y, b y) = 0) :
    centeredBadIntegral i j z r b x =
      ∫ y, HolderToCK.hessianKernelExpression i j (x - y) * b y := by
  let f (y : E d) := (HolderToCK.hessianKernelExpression i j (x - y) -
      HolderToCK.hessianKernelExpression i j (x - z)) * b y
  let C := HolderToCK.hessianKernelExpression i j (x - z)
  have hExt (y : E d) (hy : y ∉ ball z r) : b y = 0 :=
    Function.notMem_support.mp fun h => hy (hbS h)
  have hf : Integrable f := by
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp
      (centeredBadIntegral_integrableOn hd i j hx hb)
    intro y hy
    by_contra hn
    exact Function.mem_support.mp hy (by simp [hExt y hn])
  change (∫ y in ball z r, f y) = _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by simp [f, hExt y hy])]
  have hEq : (fun y => HolderToCK.hessianKernelExpression i j (x - y) * b y) =
      fun y => f y + C * b y := by
    ext y
    dsimp only [f, C]
    ring
  rw [hEq, integral_add hf (hb.const_mul C), integral_const_mul, hb0, mul_zero, add_zero]

private theorem abs_centeredBadIndicator_bound (hd : 0 < d) (i j : Fin d) {z : E d}
    {r : ℝ} (hr : 0 < r) {b : E d → ℝ} (hb : Integrable b) {G : Set (E d)}
    (hG : G ⊆ (ball z (2 * r))ᶜ) (hMeas : Measurable (G.indicator (centeredBadIntegral i j z r b))) :
    Integrable (G.indicator (centeredBadIntegral i j z r b)) ∧
      (∫ x, |G.indicator (centeredBadIntegral i j z r b) x|) ≤
        HolderToCK.hessianKernelTranslationConstant d * HolderToCK.euclideanSphereArea d / 2 *
          ∫ y, |b y| := by
  let C := HolderToCK.hessianKernelTranslationConstant d
  let N := ∫ y, |b y|
  let J (x : E d) := ((ball z (2 * r))ᶜ).indicator
    (fun x => (C * r * N) * ‖z - x‖ ^ (-(d : ℝ) - 1)) x
  have hArea := HolderToCK.euclideanSphereArea_pos hd
  have hC : 0 ≤ C := HolderToCK.hessianKernelTranslationConstant_nonneg hd
  have hN : 0 ≤ N := integral_nonneg fun _ => abs_nonneg _
  have hJ : Integrable J := by
    apply IntegrableOn.integrable_indicator ?_ measurableSet_ball.compl
    have hi := HolderToCK.radialExteriorPower_shifted_integrableOn hd
      (show (0 : ℝ) < 1 by norm_num) (mul_pos two_pos hr) z
    simpa only [zero_sub, IntegrableOn] using hi.const_mul (C * r * N)
  have hl (x : E d) : |G.indicator (centeredBadIntegral i j z r b) x| ≤ J x := by
    by_cases hx : x ∈ G
    · have hx' := hG hx
      rw [indicator_of_mem hx]
      dsimp only [J]
      rw [indicator_of_mem hx']
      refine (abs_centeredBadIntegral_le hd i j hr hx' hb).trans_eq ?_
      dsimp only [C, N]
      ring
    · rw [indicator_of_notMem hx, abs_zero]
      exact indicator_nonneg (fun _ _ => by positivity) _
  have hInt : Integrable (G.indicator (centeredBadIntegral i j z r b)) :=
    hJ.mono' hMeas.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hl x)
  refine ⟨hInt, (integral_mono hInt.abs hJ hl).trans_eq ?_⟩
  dsimp only [J]
  rw [integral_indicator measurableSet_ball.compl, integral_const_mul]
  have hint := HolderToCK.radialExteriorPower_shifted_integral hd
    (show (0 : ℝ) < 1 by norm_num) (mul_pos two_pos hr) z
  simp only [zero_sub, sub_zero, Real.rpow_neg_one, div_one] at hint
  rw [hint]
  field_simp [hr.ne']
  ring

private theorem convolution_abs_superlevel_bound_good {a K : E d → ℝ}
    (ha : Integrable a) (hK : Continuous K) (hKc : HasCompactSupport K)
    {t : ℝ} (ht : 0 < t) {M L : ℝ}
    (hM : 0 ≤ M) (haM : ∀ x, |a x| ≤ M * t)
    (haL : (∫ x, |a x|) ≤ L)
    (hL2 : (∫ x, |(K ⋆[ContinuousLinearMap.mul ℝ ℝ] a) x| ^ 2) ≤
      4 * ∫ x, |a x| ^ 2) :
    volume {x | t / 2 < |(K ⋆[ContinuousLinearMap.mul ℝ ℝ] a) x|} ≤
      ENNReal.ofReal (16 * M * L / t) := by
  let u := K ⋆[ContinuousLinearMap.mul ℝ ℝ] a
  have huI := (hK.integrable_of_hasCompactSupport hKc).integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) ha
  obtain ⟨B, hB⟩ := hK.norm.bddAbove_range_of_hasCompactSupport hKc.norm
  have huBound (x : E d) : |u x| ≤ B * ∫ y, |a y| := by
    dsimp only [u]
    rw [convolution_mul_swap, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (ha.abs.const_mul B)
      (Eventually.of_forall fun y => ?_)).trans_eq (integral_const_mul _ _)
    rw [norm_mul, Real.norm_eq_abs (a y)]
    exact mul_le_mul_of_nonneg_right (hB ⟨x - y, rfl⟩) (abs_nonneg _)
  have hu₂ := memLp_two_of_integrable_abs_le huI huBound
  have ha₂ := memLp_two_of_integrable_abs_le ha haM
  have huSqI : Integrable (fun x => |u x| ^ 2) := by
    simpa only [Real.norm_eq_abs] using
      (memLp_two_iff_integrable_sq_norm huI.aestronglyMeasurable).mp hu₂
  have haSqI : Integrable (fun x => |a x| ^ 2) := by
    simpa only [Real.norm_eq_abs] using
      (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mp ha₂
  have hSq : (∫ x, |a x| ^ 2) ≤ (M * t) * L := by
    calc
      _ ≤ ∫ x, (M * t) * |a x| := by
        refine integral_mono haSqI (ha.abs.const_mul _) (fun x => ?_)
        exact (pow_two _).trans_le (mul_le_mul_of_nonneg_right (haM x) (abs_nonneg _))
      _ ≤ _ := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left haL (mul_nonneg hM ht.le)
  calc
    _ ≤ volume {x | (t / 2) ^ 2 < |u x| ^ 2} := by
      refine measure_mono (fun x hx => ?_)
      exact pow_lt_pow_left₀ (show t / 2 < |u x| from hx) (show 0 ≤ t / 2 by positivity)
        (by decide : 2 ≠ 0)
    _ ≤ ENNReal.ofReal ((∫ x, |u x| ^ 2) / (t / 2) ^ 2) :=
      measure_superlevel_le_integral huSqI (fun _ => sq_nonneg _) (sq_pos_of_pos (half_pos ht))
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hbound : (∫ x, |u x| ^ 2) ≤ 4 * (M * t * L) :=
        hL2.trans (mul_le_mul_of_nonneg_left hSq (by norm_num))
      apply (div_le_iff₀ (sq_pos_of_pos (half_pos ht))).mpr
      refine hbound.trans_eq ?_
      field_simp [ht.ne']
      ring

private theorem cutoffWeakType_of_approximants (hd : 0 < d) (i j : Fin d)
    {F D : E d → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (K : ℕ → E d → ℝ) (hK : ∀ n, Continuous (K n)) (hKc : ∀ n, HasCompactSupport (K n))
    (hL2 : ∀ n (a : E d → ℝ), Integrable a → MemLp a 2 →
      (∫ x, |(K n ⋆[ContinuousLinearMap.mul ℝ ℝ] a) x| ^ 2) ≤ 4 * ∫ x, |a x| ^ 2)
    (hLim : ∀ x, Tendsto (fun n => (K n ⋆[ContinuousLinearMap.mul ℝ ℝ] F) x) atTop (𝓝 (D x)))
    (hOff : ∀ (b : E d → ℝ), Integrable b → ∀ (z : E d) (r : ℝ), 0 < r →
      Function.support b ⊆ ball z r → ∀ x ∉ ball z (2 * r),
        Tendsto (fun n => (K n ⋆[ContinuousLinearMap.mul ℝ ℝ] b) x) atTop
          (𝓝 (∫ y, HolderToCK.hessianKernelExpression i j (x - y) * b y)))
    {t : ℝ} (ht : 0 < t) :
    volume {x | t < |D x|} ≤
      ENNReal.ofReal (((10 : ℝ) ^ d + 16 * ((5 : ℝ) ^ d + 2) +
        2 * HolderToCK.hessianKernelTranslationConstant d * HolderToCK.euclideanSphereArea d) *
        (∫ x, |F x|) / t) := by
  obtain ⟨w⟩ := exists_cutoffCZDecomposition hd hF hFc ht
  let Xbad := ⋃ k, ball (w.center k) (10 * w.radius k)
  let G := Xbadᶜ
  have hGm : MeasurableSet G := (MeasurableSet.iUnion fun _ => measurableSet_ball).compl
  let B (k : Fin w.size) := G.indicator (centeredBadIntegral i j (w.center k) (5 * w.radius k) (w.bad k))
  let Bsum (x : E d) := ∑ k, B k x
  let N := ∫ x, |F x|
  have hN : 0 ≤ N := integral_nonneg fun _ => abs_nonneg _
  have hOut (k : Fin w.size) (x : E d) (hx : x ∈ G) :
      x ∉ ball (w.center k) (2 * (5 * w.radius k)) := by
    rw [show 2 * (5 * w.radius k) = 10 * w.radius k by ring]
    exact fun hk => hx (mem_iUnion.mpr ⟨k, hk⟩)
  have hLimBad (k : Fin w.size) (x : E d) (hx : x ∈ G) :
      Tendsto (fun n => (K n ⋆[ContinuousLinearMap.mul ℝ ℝ] w.bad k) x) atTop
        (𝓝 (B k x)) := by
    have hr := mul_pos (by norm_num : (0 : ℝ) < 5) (w.radius_pos k)
    dsimp only [B]
    rw [indicator_of_mem hx, centeredBadIntegral_eq_integral hd i j (hOut k x hx)
      (w.bad_integrable k) (w.bad_support k) (w.bad_integral k)]
    exact hOff _ (w.bad_integrable k) _ _ hr (w.bad_support k) x (hOut k x hx)
  have hBm (k : Fin w.size) : Measurable (B k) := by
    apply measurable_of_tendsto_metrizable (f := fun n =>
      G.indicator (K n ⋆[ContinuousLinearMap.mul ℝ ℝ] w.bad k))
    · intro n
      exact ((hKc n).continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
        (hK n) (w.bad_integrable k).locallyIntegrable).measurable.indicator hGm
    · apply tendsto_pi_nhds.mpr
      intro x
      by_cases hx : x ∈ G
      · simp only [indicator_of_mem hx]
        exact hLimBad k x hx
      · simpa only [B, indicator_of_notMem hx] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hBad (k : Fin w.size) := abs_centeredBadIndicator_bound hd i j
    (mul_pos (by norm_num : (0 : ℝ) < 5) (w.radius_pos k)) (w.bad_integrable k)
    (fun x hx => hOut k x hx) (hBm k)
  have hBsumI : Integrable Bsum := integrable_finsetSum _ fun k _ => (hBad k).1
  let C := HolderToCK.hessianKernelTranslationConstant d * HolderToCK.euclideanSphereArea d
  have hC : 0 ≤ C := mul_nonneg (HolderToCK.hessianKernelTranslationConstant_nonneg hd)
    (HolderToCK.euclideanSphereArea_pos hd).le
  have hBmass : (∫ x, |Bsum x|) ≤ C * N := by
    calc
      _ ≤ ∫ x, ∑ k, |B k x| :=
        integral_mono hBsumI.abs (integrable_finsetSum _ fun k _ => (hBad k).1.abs)
          (fun x => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ k, (C / 2) * ∫ x, |w.bad k x| := by
        rw [integral_finsetSum _ fun k _ => (hBad k).1.abs]
        exact Finset.sum_le_sum fun k _ => (hBad k).2
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact (mul_le_mul_of_nonneg_left w.bad_mass (div_nonneg hC zero_le_two)).trans_eq (by ring)
  have hBweak : volume {x | t / 2 < |Bsum x|} ≤ ENNReal.ofReal (2 * C * N / t) :=
    (measure_superlevel_le_integral hBsumI.abs (fun _ => abs_nonneg _) (half_pos ht)).trans
      (ENNReal.ofReal_le_ofReal (calc
        _ ≤ (C * N) / (t / 2) := div_le_div_of_nonneg_right hBmass (half_pos ht).le
        _ = _ := by rw [div_div_eq_mul_div]; ring))
  let Agood := G.indicator (fun x => D x - Bsum x)
  have hAweak : volume {x | t / 2 < |Agood x|} ≤
      ENNReal.ofReal (16 * ((5 : ℝ) ^ d + 2) * N / t) := by
    apply measure_abs_superlevel_le_of_pointwise_tendsto volume
      (f := fun n => G.indicator (K n ⋆[ContinuousLinearMap.mul ℝ ℝ] w.good))
    · intro x
      by_cases hx : x ∈ G
      · simp only [Agood, indicator_of_mem hx]
        have hBadSum := tendsto_finsetSum Finset.univ (fun k _ => hLimBad k x hx)
        have h := (hLim x).sub hBadSum
        change Tendsto _ atTop (𝓝 (D x - Bsum x)) at h
        refine h.congr ?_
        intro n
        have hFsum : F = w.good + ∑ k, w.bad k := by
          ext y
          simpa only [Pi.add_apply, Finset.sum_apply] using w.sum_eq y
        have hConvEq := congrArg (fun f => (K n ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x) hFsum
        rw [hConvEq, convolution_add_finset (hK n) (hKc n) w.good_integrable w.bad_integrable,
          add_sub_cancel_right]
      · simp only [Agood, indicator_of_notMem hx]
        exact tendsto_const_nhds
    · intro n
      apply (measure_mono ?_).trans
        (convolution_abs_superlevel_bound_good w.good_integrable (hK n) (hKc n) ht
          (by positivity : 0 ≤ (5 : ℝ) ^ d + 2)
          (fun x => (w.good_bound x).trans_eq (by ring)) w.good_mass
          (hL2 n _ w.good_integrable (memLp_two_of_integrable_abs_le w.good_integrable w.good_bound)))
      intro x hx
      by_cases h : x ∈ G
      · simpa only [mem_setOf_eq, indicator_of_mem h] using hx
      · exfalso
        have hh : t / 2 < |G.indicator (K n ⋆[ContinuousLinearMap.mul ℝ ℝ] w.good) x| := hx
        rw [indicator_of_notMem h, abs_zero] at hh
        exact (not_lt_of_gt (half_pos ht)) hh
  have hsub : {x | t < |D x|} ⊆ Xbad ∪ ({x | t / 2 < |Agood x|} ∪ {x | t / 2 < |Bsum x|}) := by
    intro x hx
    by_cases he : x ∈ Xbad
    · exact Or.inl he
    · apply Or.inr
      by_cases ha : t / 2 < |Agood x|
      · exact Or.inl ha
      · apply Or.inr
        by_contra hb
        change ¬ t / 2 < |Bsum x| at hb
        have hEq : D x = Agood x + Bsum x := by
          dsimp only [Agood]
          rw [indicator_of_mem (show x ∈ G from he), sub_add_cancel]
        rw [mem_setOf_eq, hEq] at hx
        have h := (abs_add_le (Agood x) (Bsum x)).trans
          (add_le_add (not_lt.mp ha) (not_lt.mp hb))
        linarith only [h, hx]
  calc
    _ ≤ volume Xbad + (volume {x | t / 2 < |Agood x|} + volume {x | t / 2 < |Bsum x|}) :=
      (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _)))
    _ ≤ ENNReal.ofReal ((10 : ℝ) ^ d * N / t) +
        (ENNReal.ofReal (16 * ((5 : ℝ) ^ d + 2) * N / t) + ENNReal.ofReal (2 * C * N / t)) :=
      add_le_add w.exceptional_mass (add_le_add hAweak hBweak)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      dsimp only [C, N]
      ring

/-- A compactly supported smooth function has the weak (L^1) Hessian estimate
with its Laplacian as the input. The dimension determines the constant. -/
theorem measure_scalarHessian_superlevel_le_laplacian (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E d → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
      ∀ (i j : Fin d) (t : ℝ), 0 < t →
        volume {x : E d | t < |scalarHessian u x i j|} ≤
          ENNReal.ofReal (C * (∫ x, |laplacian u x|) / t) := by
  have hd0 : 0 < d := by omega
  refine ⟨(10 : ℝ) ^ d + 16 * ((5 : ℝ) ^ d + 2) +
    2 * HolderToCK.hessianKernelTranslationConstant d * HolderToCK.euclideanSphereArea d,
    add_nonneg (by positivity) (mul_nonneg
      (mul_nonneg zero_le_two (HolderToCK.hessianKernelTranslationConstant_nonneg hd0))
      (HolderToCK.euclideanSphereArea_pos hd0).le), ?_⟩
  intro u hu huc i j t ht
  obtain ⟨hLap, hLapc⟩ := smooth_compact_laplacian hu huc
  have hK (n : ℕ) := truncatedNewtonKernel_smooth_compact hd0 n
  have hH (n : ℕ) := smooth_compact_scalarHessian (hK n).1 (hK n).2 i j
  refine cutoffWeakType_of_approximants hd0 i j hLap.continuous hLapc
    (truncatedNewtonHessian i j) (fun n => (hH n).1.continuous) (fun n => (hH n).2)
    ?_
    (tendsto_truncatedNewtonHessian_convolution_laplacian hd i j hu huc)
    (fun _ hb _ _ hr hS _ hx => tendsto_truncatedNewtonHessian_convolution_off_ball hd i j hb hS hr hx)
    ht
  intro n a ha ha₂
  have hL := integral_sq_scalarHessian_convolution_le hd0 (hK n).1 (hK n).2 ha ha₂ i j
  have hLap0 : 0 ≤ ∫ x, |laplacian (truncatedNewtonKernel d n) x| :=
    integral_nonneg fun _ => abs_nonneg _
  have hL2 := pow_le_pow_left₀ hLap0 (integral_abs_laplacian_truncatedNewtonKernel_le hd0 n) 2
  exact hL.trans (mul_le_mul_of_nonneg_right
    (hL2.trans_eq (by norm_num)) (integral_nonneg fun _ => sq_nonneg _))

end SupportingAnalysis
