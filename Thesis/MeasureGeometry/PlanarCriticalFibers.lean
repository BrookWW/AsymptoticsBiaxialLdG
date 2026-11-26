module

public import Thesis.Definitions
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.RCLike.Basic

/-! The critical part of a C¹ planar scalar map has negligible level
length for almost every level. -/

public section

open Filter Function MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal NNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

private def planarBallCoverBudget (R : ℝ) : ℝ≥0∞ :=
  100 * (volume (ball (0 : Plane) 1))⁻¹ * volume (ball (0 : Plane) (R+1))

private theorem planarBallCoverBudget_lt_top (R : ℝ) : planarBallCoverBudget R < ⊤ :=
  ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by norm_num) (ENNReal.inv_lt_top.mpr (measure_ball_pos _ _ zero_lt_one)))
    measure_ball_lt_top

private theorem exists_critical_fiber_cover_with_small_integral
    {U : Set Plane} (hU : IsOpen U) (f : Plane → ℝ) (hf : ContDiffOn ℝ 1 f U)
    (R ε : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    let K := (U ∩ ball (0 : Plane) R) ∩ {x | fderiv ℝ f x = 0}
    ∃ (ι : Type) (T : ℝ → ι → Set Plane) (A : ℝ → ℝ≥0∞), Countable ι ∧ Measurable A ∧
      (∀ t i, ediam (T t i) ≤ ENNReal.ofReal (10 * ε)) ∧
      (∀ t, (K ∩ {x | f x = t}) ⊆ ⋃ i, T t i) ∧
      (∀ t, (∑' i, ediam (T t i)) ≤ A t) ∧
      (∫⁻ t, A t) ≤ planarBallCoverBudget R * ENNReal.ofReal ε := by
  classical
  let K := (U ∩ ball (0 : Plane) R) ∩ {x | fderiv ℝ f x = 0}
  have hLocal (a : K) : ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧
      ∀ x ∈ ball (a : Plane) (5*r), x ∈ U ∧ ‖fderiv ℝ f x‖ < ε := by
    have haU := a.property.1.1
    have h0 : fderiv ℝ f a = 0 := a.property.2
    have hc : ContinuousAt (fun x : Plane => ‖fderiv ℝ f x‖) a :=
      (((hf.continuousOn_fderiv_of_isOpen hU le_rfl) a haU).continuousAt (hU.mem_nhds haU)).norm
    have hNear : U ∩ {x | ‖fderiv ℝ f x‖ < ε} ∈ 𝓝 (a : Plane) := by
      apply Filter.inter_mem (hU.mem_nhds haU)
      exact hc.eventually_lt continuousAt_const (by simpa only [h0,norm_zero] using hε)
    obtain ⟨d,hd,hD⟩ := Metric.mem_nhds_iff.mp hNear
    let r := min ε (d / 5)
    have hR : 0 < r := lt_min hε (div_pos hd (by norm_num))
    refine ⟨r,hR,min_le_left _ _,?_⟩
    have hrd : 5*r ≤ d := by have := min_le_right ε (d/5); dsimp only [r]; linarith
    exact (ball_subset_ball hrd).trans hD
  choose r hr hrε hLocalBall using hLocal
  obtain ⟨I,_,hDis,hBig⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    (univ : Set K) (fun a : K => (a : Plane)) r ε (fun a _ => hrε a) 5 (by norm_num)
  let ι := ↥I
  haveI : Countable ι := (hDis.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun a _ => ⟨a,mem_ball_self (hr a)⟩)).to_subtype
  let c (i : ι) : Plane := (i.val : Plane)
  let ρ (i : ι) := r i.val
  let B (i : ι) := ball (c i) (5 * ρ i)
  let J (i : ι) := Icc (f (c i) - ε * (5*ρ i)) (f (c i) + ε * (5*ρ i))
  let T (t : ℝ) (i : ι) := if t ∈ J i then B i else ∅
  let Q (i : ι) (t : ℝ) := (J i).indicator (fun _ => ENNReal.ofReal (10 * ρ i)) t
  let A (t : ℝ) := ∑' i : ι, Q i t
  have hLeft (i : ι) : ball (c i) (ρ i) ⊆ ball (0 : Plane) (R+1) := by
    intro x hx
    have hi : c i ∈ ball (0 : Plane) R := i.val.property.1.2
    have hρ : ρ i ≤ 1 := (hrε i.val).trans hε₁
    exact mem_ball.mpr (by linarith only [dist_triangle x (c i) 0, mem_ball.mp hx, mem_ball.mp hi, hρ])
  have hMeasure₀ (i : ι) :
      volume (ball (c i) (ρ i)) = ENNReal.ofReal (ρ i ^ 2) * volume (ball (0 : Plane) 1) := by
    rw [Measure.addHaar_ball_of_pos volume _ (hr i.val)]
    simp [Plane, finrank_euclideanSpace, ρ]
  let V := volume (ball (0 : Plane) 1)
  have hV₀ : 0 < V := measure_ball_pos volume _ zero_lt_one
  have hV₁ : V < ⊤ := measure_ball_lt_top
  have hRad :
      (∑' i : ι, ENNReal.ofReal (ρ i ^ 2)) ≤ V⁻¹ * volume (ball (0 : Plane) (R+1)) := by
    have hDis' : Pairwise (Disjoint on fun i : ι => ball (c i) (ρ i)) := hDis.subtype _ _
    have hSum : (∑' i : ι, ENNReal.ofReal (ρ i ^ 2)) * V ≤ volume (ball (0 : Plane) (R+1)) := by
      change (∑' i : ι, ENNReal.ofReal (ρ i ^ 2)) * volume (ball (0 : Plane) 1) ≤ _
      rw [← ENNReal.tsum_mul_right]
      simp_rw [← hMeasure₀]
      rw [← measure_iUnion hDis' (fun _ => measurableSet_ball)]
      exact measure_mono (iUnion_subset hLeft)
    exact (ENNReal.le_div_iff_mul_le (.inl hV₀.ne') (.inl hV₁.ne)).2 hSum |>.trans_eq (by rw [ENNReal.div_eq_inv_mul])
  have hD (i : ι) : ediam (B i) ≤ ENNReal.ofReal (10 * ρ i) := by
    apply ediam_le_of_forall_dist_le
    intro x hx y hy
    linarith only [dist_triangle_right x y (c i), mem_ball.mp hx, mem_ball.mp hy]
  have hQMeas (i : ι) : Measurable (Q i) := measurable_const.indicator measurableSet_Icc
  have hA : Measurable A := Measurable.tsum hQMeas
  have hC (t : ℝ) : K ∩ {x | f x = t} ⊆ ⋃ i, T t i := by
    intro x hx
    let a : K := ⟨x,hx.1⟩
    obtain ⟨b,hb,hBigb⟩ := hBig a (mem_univ a)
    let i : ι := ⟨b,hb⟩
    have hxB : x ∈ B i := hBigb (mem_ball_self (hr a))
    have hp : c i ∈ B i := mem_ball_self (mul_pos (by norm_num) (hr i.val))
    have hLip : LipschitzOnWith ⟨ε,hε.le⟩ f (B i) := by
      apply (convex_ball _ _).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      · intro y hy
        have hyU := (hLocalBall i.val y hy).1
        exact (hf.differentiableOn (by simp) y hyU).differentiableAt (hU.mem_nhds hyU)
      · intro y hy
        exact_mod_cast (hLocalBall i.val y hy).2.le
    have hDist := hLip.dist_le_mul x hxB (c i) hp
    have hfx : f x = t := hx.2
    rw [hfx,Real.dist_eq] at hDist
    have hLim : |t - f (c i)| ≤ ε * (5 * ρ i) :=
      hDist.trans (mul_le_mul_of_nonneg_left (mem_ball.mp hxB).le hε.le)
    have hJ : t ∈ J i := by
      obtain ⟨h₁,h₂⟩ := abs_le.mp hLim
      exact ⟨by linarith,by linarith⟩
    exact mem_iUnion.mpr ⟨i,by dsimp only [T]; rw [if_pos hJ]; exact hxB⟩
  have hSum (t : ℝ) : (∑' i, ediam (T t i)) ≤ A t := by
    apply ENNReal.tsum_le_tsum
    intro i
    by_cases h : t ∈ J i
    · simpa only [T,if_pos h,Q,indicator_of_mem h] using hD i
    · simp [T,Q,h]
  refine ⟨ι,T,A,inferInstance,hA,?_,hC,hSum,?_⟩
  · intro t i
    by_cases h : t ∈ J i
    · rw [show T t i = B i from if_pos h]
      exact (hD i).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hrε i.val) (by norm_num)))
    · simp [T,h]
  have hQI (i : ι) : (∫⁻ t, Q i t) = 100 * ENNReal.ofReal ε * ENNReal.ofReal (ρ i ^ 2) := by
    have hρ : 0 < ρ i := hr i.val
    change (∫⁻ t, (J i).indicator (fun _ => ENNReal.ofReal (10 * ρ i)) t) = _
    rw [lintegral_indicator measurableSet_Icc, setLIntegral_const]
    have hJ' : volume (J i) = ENNReal.ofReal (10 * ε * ρ i) := by
      dsimp only [J]
      rw [Real.volume_Icc, show f (c i) + ε * (5*ρ i) - (f (c i) - ε * (5*ρ i)) = 10*ε*ρ i by ring]
    rw [hJ', ← ENNReal.ofReal_mul (by positivity)]
    have he : (10 * ρ i) * (10 * ε * ρ i) = 100 * ε * ρ i ^ 2 := by ring
    rw [he, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    norm_num
  change (∫⁻ t, ∑' i, Q i t) ≤ _
  rw [lintegral_tsum (fun i => (hQMeas i).aemeasurable)]
  simp_rw [hQI, ENNReal.tsum_mul_left]
  exact (mul_le_mul' le_rfl hRad).trans_eq (by dsimp only [planarBallCoverBudget,V]; ac_rfl)

private theorem ae_bounded_critical_level_hausdorffMeasure_eq_zero
    {U : Set Plane} (hU : IsOpen U) (f : Plane → ℝ) (hf : ContDiffOn ℝ 1 f U) (R : ℝ) :
    ∀ᵐ t ∂(volume : Measure ℝ), Measure.hausdorffMeasure 1
      (((U ∩ ball (0 : Plane) R) ∩ {x | fderiv ℝ f x = 0}) ∩ {x | f x = t}) = 0 := by
  classical
  let ε (n : ℕ) := (1 : ℝ) / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hε₁ (n : ℕ) : ε n ≤ 1 := by
    dsimp only [ε]
    exact (div_le_one (by positivity : 0 < (n : ℝ) + 1)).2 (by linarith only [Nat.cast_nonneg (α := ℝ) n])
  have hLim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hCover (n : ℕ) := exists_critical_fiber_cover_with_small_integral hU f hf R (ε n) (hε n) (hε₁ n)
  choose ι T A hι hMeas hDiam hCov hSum hBound using hCover
  letI (n : ℕ) : Countable (ι n) := hι n
  have hD0 : Tendsto (fun n => ENNReal.ofReal (10 * ε n)) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (hLim.const_mul 10)
  have hTop := planarBallCoverBudget_lt_top R
  have hMajor : Tendsto (fun n => planarBallCoverBudget R * ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
    have hE := ENNReal.tendsto_ofReal hLim
    rw [ENNReal.ofReal_zero] at hE
    simpa only [Function.comp_def,mul_zero] using
      (ENNReal.continuous_const_mul hTop.ne).continuousAt.tendsto.comp hE
  have hIntLim : Tendsto (fun n => ∫⁻ t, A n t) atTop (𝓝 0) :=
    ENNReal.tendsto_nhds_zero.2 fun δ hδ =>
      (ENNReal.tendsto_nhds_zero.1 hMajor δ hδ).mono fun n hn => (hBound n).trans hn
  have hFatou : (∫⁻ t : ℝ, liminf (fun n => A n t) atTop) = 0 :=
    le_antisymm ((lintegral_liminf_le hMeas).trans_eq hIntLim.liminf_eq) bot_le
  have hAe := (lintegral_eq_zero_iff (Measurable.liminf hMeas)).1 hFatou
  filter_upwards [hAe] with t ht
  apply le_antisymm _ bot_le
  have hCovering := Measure.hausdorffMeasure_le_liminf_tsum (ι := ι) 1 _ _ hD0 (fun n => T n t)
    (.of_forall fun n i => hDiam n t i) (.of_forall fun n => hCov n t)
  simp only [ENNReal.rpow_one] at hCovering
  exact (hCovering.trans (Filter.liminf_le_liminf (.of_forall fun n => hSum n t))).trans_eq ht

/-- The critical fibers of a C¹ scalar function have zero length for
almost every value, even when its critical values have positive measure. -/
theorem ae_critical_level_hausdorffMeasure_eq_zero
    {U : Set Plane} (hU : IsOpen U) (f : Plane → ℝ) (hf : ContDiffOn ℝ 1 f U) :
    ∀ᵐ t ∂(volume : Measure ℝ), Measure.hausdorffMeasure 1
      ((U ∩ {x | fderiv ℝ f x = 0}) ∩ {x | f x = t}) = 0 := by
  have hAe : ∀ᵐ t ∂(volume : Measure ℝ), ∀ n : ℕ, Measure.hausdorffMeasure 1
      (((U ∩ ball (0 : Plane) (n : ℝ)) ∩ {x | fderiv ℝ f x = 0}) ∩ {x | f x = t}) = 0 :=
    ae_all_iff.2 fun n => ae_bounded_critical_level_hausdorffMeasure_eq_zero hU f hf n
  filter_upwards [hAe] with t ht
  have hSub : (U ∩ {x | fderiv ℝ f x = 0}) ∩ {x | f x = t} ⊆
      ⋃ n : ℕ, ((U ∩ ball (0 : Plane) (n:ℝ)) ∩ {x | fderiv ℝ f x = 0}) ∩ {x | f x = t} := by
    intro x hx
    obtain ⟨n,hn⟩ := exists_nat_gt ‖x‖
    exact mem_iUnion.mpr ⟨n,⟨⟨⟨hx.1.1,mem_ball_zero_iff.mpr hn⟩,hx.1.2⟩,hx.2⟩⟩
  have hNull := measure_iUnion_null_iff.2 ht
  apply le_antisymm _ bot_le
  exact (measure_mono hSub).trans_eq hNull

end Thesis

end
