module

public import Thesis.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Compactness.Lindelof

/-! One-dimensional Hausdorff area of regular C¹ planar curves. -/

public section

open Filter Function MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal NNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem planarCurve_local_dist_and_speed
    {U : Set ℝ} (hU : IsOpen U) (γ : ℝ → Plane) (hγ : ContDiffOn ℝ 1 γ U)
    {η : ℝ} (hη : 0 < η) {x : ℝ} (hx : x ∈ U) (hk : 0 < ‖deriv γ x‖) :
    ∃ r > (0 : ℝ), ball x r ⊆ U ∧
      (∀ y ∈ ball x r,
        (1-η)*‖deriv γ x‖ ≤ ‖deriv γ y‖ ∧ ‖deriv γ y‖ ≤ (1+η)*‖deriv γ x‖) ∧
      (∀ y ∈ ball x r, ∀ z ∈ ball x r,
        ((1-η)*‖deriv γ x‖) * dist y z ≤ dist (γ y) (γ z) ∧
          dist (γ y) (γ z) ≤ ((1+η)*‖deriv γ x‖) * dist y z) := by
  let v := deriv γ x
  let k := ‖v‖
  have hCont : ContinuousAt (deriv γ) x :=
    ((hγ.continuousOn_deriv_of_isOpen hU le_rfl) x hx).continuousAt (hU.mem_nhds hx)
  have hGerm : U ∩ {y | ‖deriv γ y-v‖ < η*k} ∈ 𝓝 x := by
    apply Filter.inter_mem (hU.mem_nhds hx)
    have hN : ContinuousAt (fun y => ‖deriv γ y-v‖) x := (hCont.sub continuousAt_const).norm
    exact hN.eventually_lt continuousAt_const (by dsimp only [v,k]; rw [sub_self,norm_zero]; positivity)
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp hGerm
  have hSub : ball x r ⊆ U := hBall.trans inter_subset_left
  have hDeriv (y : ℝ) (hy : y ∈ ball x r) : ‖deriv γ y-v‖ ≤ η*k := (hBall hy).2.le
  refine ⟨r,hr,hSub,?_,?_⟩
  · intro y hy
    have hA := norm_sub_norm_le (deriv γ y) v
    have hB := norm_sub_norm_le v (deriv γ y)
    rw [norm_sub_rev v (deriv γ y)] at hB
    constructor <;> nlinarith only [hA,hB,hDeriv y hy]
  · intro y hy z hz
    let R (t : ℝ) := γ t-t • v
    have hR (t : ℝ) (ht : t ∈ ball x r) :
        HasDerivAt R (deriv γ t-v) t := by
      have hDt := (hγ.differentiableOn (by simp) t (hSub ht)).differentiableAt (hU.mem_nhds (hSub ht))
      have hV : HasDerivAt (fun u : ℝ => u • v) v t := by
        simpa only [id, one_smul] using (hasDerivAt_id t).smul_const v
      change HasDerivAt (γ - (fun u : ℝ => u • v)) (deriv γ t - v) t
      exact hDt.hasDerivAt.sub hV
    have hDiff : ‖R y-R z‖ ≤ η*k*‖y-z‖ :=
      (convex_ball x r).norm_image_sub_le_of_norm_deriv_le
        (fun t ht => (hR t ht).differentiableAt)
        (fun t ht => (hR t ht).deriv ▸ hDeriv t ht) hz hy
    have hE₁ : γ y-γ z = (y-z) • v + (R y-R z) := by dsimp only [R]; rw [sub_smul]; abel
    have hE₂ : (y-z) • v = (γ y-γ z) - (R y-R z) := by rw [hE₁]; abel
    have hHi : ‖γ y-γ z‖ ≤ ‖(y-z) • v‖+‖R y-R z‖ := by rw [hE₁]; exact norm_add_le _ _
    have hLo : ‖(y-z) • v‖ ≤ ‖γ y-γ z‖+‖R y-R z‖ := by rw [hE₂]; exact norm_sub_le _ _
    rw [norm_smul] at hHi hLo
    rw [dist_eq_norm, dist_eq_norm]
    constructor <;> nlinarith only [hHi,hLo,hDiff]

private theorem planarCurve_measure_le_of_dist_le
    (γ : ℝ → Plane) (S : Set ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ y ∈ S, ∀ z ∈ S, dist (γ y) (γ z) ≤ K * dist y z) :
    Measure.hausdorffMeasure 1 (γ '' S) ≤ ENNReal.ofReal K * volume S := by
  have hL : LipschitzOnWith (NNReal.mk K hK) γ S := LipschitzOnWith.of_dist_le_mul h
  have h' := hL.hausdorffMeasure_image_le (d := 1) (by norm_num)
  simpa only [ENNReal.rpow_one, hausdorffMeasure_real, ENNReal.ofReal_eq_coe_nnreal hK] using h'

private theorem le_planarCurve_measure_of_le_dist
    (γ : ℝ → Plane) (S : Set ℝ) (hγ : InjOn γ S) (K : ℝ) (hK : 0 < K)
    (h : ∀ y ∈ S, ∀ z ∈ S, K * dist y z ≤ dist (γ y) (γ z)) :
    ENNReal.ofReal K * volume S ≤ Measure.hausdorffMeasure 1 (γ '' S) := by
  classical
  let ι := invFunOn γ S
  have hL : LipschitzOnWith (NNReal.mk K⁻¹ (inv_nonneg.mpr hK.le)) ι (γ '' S) :=
    LipschitzOnWith.of_dist_le_mul (by
      rintro _ ⟨y,hy,rfl⟩ _ ⟨z,hz,rfl⟩
      change dist (invFunOn γ S (γ y)) (invFunOn γ S (γ z)) ≤ K⁻¹ * dist (γ y) (γ z)
      rw [hγ.leftInvOn_invFunOn hy,hγ.leftInvOn_invFunOn hz, ← div_eq_inv_mul]
      exact (le_div_iff₀ hK).2 (by simpa only [mul_comm] using h y hy z hz))
  have hIm : ι '' (γ '' S) = S := hγ.invFunOn_image subset_rfl
  have hI := hL.hausdorffMeasure_image_le (d := 1) (by norm_num)
  have hI' : volume S ≤ ENNReal.ofReal K⁻¹ * Measure.hausdorffMeasure 1 (γ '' S) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr hK.le)]
    simpa only [hIm, hausdorffMeasure_real, ENNReal.rpow_one] using hI
  calc
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal K⁻¹ * Measure.hausdorffMeasure 1 (γ '' S)) :=
      mul_le_mul' le_rfl hI' 
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hK.le, mul_inv_cancel₀ hK.ne', ENNReal.ofReal_one, one_mul]

private theorem planarCurve_measure_integral_comparison
    {U : Set ℝ} (hU : IsOpen U) (γ : ℝ → Plane) (hγ : ContDiffOn ℝ 1 γ U)
    (hInj : InjOn γ U) (hSpeed : ∀ x ∈ U, 0 < ‖deriv γ x‖)
    (hMeas : ∀ S : Set ℝ, MeasurableSet S → S ⊆ U → MeasurableSet (γ '' S))
    {S : Set ℝ} (hS : MeasurableSet S) (hSub : S ⊆ U) (δ : ℝ) (hδ : 0 < δ) :
    Measure.hausdorffMeasure 1 (γ '' S) ≤
      ENNReal.ofReal (1+δ) * (∫⁻ x in S, ENNReal.ofReal ‖deriv γ x‖) ∧
    (∫⁻ x in S, ENNReal.ofReal ‖deriv γ x‖) ≤
      ENNReal.ofReal (1+δ) * Measure.hausdorffMeasure 1 (γ '' S) := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | hUn
  · have h : S = ∅ := subset_empty_iff.mp hSub
    simp [h]
  letI : Nonempty ↥U := hUn.to_subtype
  let η := min (δ/4) (1/4)
  have hη : 0 < η := lt_min (div_pos hδ (by norm_num)) (by norm_num)
  have hη₁ : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hFact : 1+η ≤ (1+δ)*(1-η) := by
    have hηδ : η ≤ δ/4 := min_le_left _ _
    have hηQ : η ≤ 1/4 := min_le_right _ _
    nlinarith only [hηδ, mul_le_mul_of_nonneg_left hηQ hδ.le]
  have hLoc (x : U) := planarCurve_local_dist_and_speed hU γ hγ hη x.property (hSpeed x x.property)
  choose r hr hBall hSp hDist using hLoc
  let J (x : U) := ball (x : ℝ) (r x)
  have hCover : U ⊆ ⋃ x : U, J x := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (hr _)⟩
  obtain ⟨σ,hσ⟩ := (HereditarilyLindelofSpace.isLindelof U).indexed_countable_subcover
    J (fun _ => isOpen_ball) hCover
  let V (i : ℕ) := J (σ i)
  let E (i : ℕ) := disjointed V i ∩ S
  have hEJ (i : ℕ) : E i ⊆ J (σ i) :=
    inter_subset_left.trans (disjointed_subset _ _)
  have hE (i : ℕ) : MeasurableSet (E i) :=
    (MeasurableSet.disjointed (fun _ => measurableSet_ball) i).inter hS
  have hEU (i : ℕ) : E i ⊆ U := (hEJ i).trans (hBall (σ i))
  have hPair : Pairwise (Disjoint on E) :=
    pairwise_disjoint_mono (disjoint_disjointed V) (fun _ => inter_subset_left)
  have hUnion : (⋃ i, E i) = S := by
    change (⋃ i, disjointed V i ∩ S) = S
    rw [← iUnion_inter, iUnion_disjointed, inter_eq_right.mpr (hSub.trans hσ)]
  have hImPair : Pairwise (Disjoint on fun i => γ '' E i) := by
    intro i j hij
    rw [Function.onFun,Set.disjoint_left]
    rintro _ ⟨x,hxi,rfl⟩ ⟨y,hyj,hy⟩
    have hyx := hInj (hEU j hyj) (hEU i hxi) hy
    exact Set.disjoint_left.mp (hPair hij) hxi (hyx ▸ hyj)
  let I (E' : Set ℝ) := ∫⁻ x in E', ENNReal.ofReal ‖deriv γ x‖
  let H (E' : Set ℝ) := Measure.hausdorffMeasure 1 (γ '' E')
  let C := ENNReal.ofReal (1+δ)
  have hLocal (i : ℕ) :
      H (E i) ≤ C * I (E i) ∧ I (E i) ≤ C * H (E i) := by
    let x := σ i
    let k := ‖deriv γ x‖
    let lo := (1-η)*k
    let hi := (1+η)*k
    have hlo : 0 < lo := mul_pos (sub_pos.mpr hη₁) (hSpeed x x.property)
    have hhi : 0 ≤ hi := mul_nonneg (by linarith only [hη]) (norm_nonneg _)
    have hHlo : ENNReal.ofReal lo * volume (E i) ≤ H (E i) :=
      le_planarCurve_measure_of_le_dist γ (E i) (hInj.mono (hEU i)) lo hlo
        (fun y hy z hz => (hDist x y (hEJ i hy) z (hEJ i hz)).1)
    have hHhi : H (E i) ≤ ENNReal.ofReal hi * volume (E i) :=
      planarCurve_measure_le_of_dist_le γ (E i) hi hhi
        (fun y hy z hz => (hDist x y (hEJ i hy) z (hEJ i hz)).2)
    have hIlo : ENNReal.ofReal lo * volume (E i) ≤ I (E i) := by
      rw [← setLIntegral_const]
      exact setLIntegral_mono' (hE i) fun y hy => ENNReal.ofReal_le_ofReal (hSp x y (hEJ i hy)).1
    have hIhi : I (E i) ≤ ENNReal.ofReal hi * volume (E i) := by
      rw [← setLIntegral_const]
      exact setLIntegral_mono' (hE i) fun y hy => ENNReal.ofReal_le_ofReal (hSp x y (hEJ i hy)).2
    have hQ : ENNReal.ofReal hi ≤ C * ENNReal.ofReal lo := by
      rw [← ENNReal.ofReal_mul (by linarith only [hδ])]
      exact ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right hFact (norm_nonneg _)).trans_eq (by dsimp only [lo]; ring))
    have hVol : ENNReal.ofReal hi * volume (E i) ≤ C * (ENNReal.ofReal lo * volume (E i)) :=
      (mul_le_mul' hQ le_rfl).trans_eq (mul_assoc _ _ _)
    exact ⟨hHhi.trans (hVol.trans (mul_le_mul' le_rfl hIlo)),
      hIhi.trans (hVol.trans (mul_le_mul' le_rfl hHlo))⟩
  have hH : H S = ∑' i, H (E i) := by
    dsimp only [H]
    rw [← hUnion, image_iUnion, measure_iUnion hImPair (fun i => hMeas (E i) (hE i) (hEU i))]
  have hI : I S = ∑' i, I (E i) := by
    dsimp only [I]
    rw [← hUnion, lintegral_iUnion hE hPair]
  change H S ≤ C * I S ∧ I S ≤ C * H S
  rw [hH,hI,← ENNReal.tsum_mul_left,← ENNReal.tsum_mul_left]
  exact ⟨ENNReal.tsum_le_tsum fun i => (hLocal i).1, ENNReal.tsum_le_tsum fun i => (hLocal i).2⟩

private theorem le_of_forall_ennreal_mul_one_add {A B : ℝ≥0∞}
    (h : ∀ δ : ℝ, 0 < δ → A ≤ ENNReal.ofReal (1+δ)*B) : A ≤ B := by
  by_cases hB : B = ⊤
  · rw [hB]; exact le_top
  let δ (n : ℕ) := (1:ℝ)/((n:ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp only [δ]; positivity
  have hLim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hOne : Tendsto (fun n => ENNReal.ofReal (1+δ n)) atTop (𝓝 1) := by
    simpa only [add_zero, ENNReal.ofReal_one] using ENNReal.tendsto_ofReal (hLim.const_add 1)
  have hM : Tendsto (fun n => ENNReal.ofReal (1+δ n)*B) atTop (𝓝 B) := by
    simpa only [Function.comp_def, one_mul] using
      (ENNReal.continuous_mul_const hB).continuousAt.tendsto.comp hOne
  exact le_of_tendsto_of_tendsto' (f := fun _ : ℕ => A) tendsto_const_nhds hM
    (fun n => h (δ n) (hδ n))

/-- The exact Hausdorff length formula for a regular injective C¹ curve,
with its usual Lebesgue parameter and derivative. -/
theorem hausdorffMeasure_one_image_eq_speed_lintegral
    {U : Set ℝ} (hU : IsOpen U) (γ : ℝ → Plane) (hγ : ContDiffOn ℝ 1 γ U)
    (hInj : InjOn γ U) (hSpeed : ∀ x ∈ U, 0 < ‖deriv γ x‖)
    (hMeas : ∀ S : Set ℝ, MeasurableSet S → S ⊆ U → MeasurableSet (γ '' S))
    {S : Set ℝ} (hS : MeasurableSet S) (hSub : S ⊆ U) :
    Measure.hausdorffMeasure 1 (γ '' S) = ∫⁻ x in S, ENNReal.ofReal ‖deriv γ x‖ := by
  have hLocal (δ : ℝ) (hδ : 0 < δ) := planarCurve_measure_integral_comparison hU γ hγ hInj hSpeed hMeas hS hSub δ hδ
  exact le_antisymm (le_of_forall_ennreal_mul_one_add fun δ hδ => (hLocal δ hδ).1)
    (le_of_forall_ennreal_mul_one_add fun δ hδ => (hLocal δ hδ).2)

end Thesis

end
