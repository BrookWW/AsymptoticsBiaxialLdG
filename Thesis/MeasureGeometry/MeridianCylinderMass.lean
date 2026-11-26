module

public import Thesis.MeasureGeometry.CylinderEndHeights
public import Thesis.MeasureGeometry.EnergyMeasure
import Mathlib.MeasureTheory.Measure.Hausdorff

/-! Mass convergence at moving end heights along an actual constant-weight edge. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace Thesis.MeasureGeometry

private theorem translated_openCylinder_image (c e : Point) (r lo hi : ℝ) :
    translatedAxisCylinder c e r lo hi = (fun y : Point => c + y) '' openAxisCylinder e r lo hi := by
  ext x
  constructor
  · intro hx
    exact ⟨x - c, hx, by abel⟩
  · rintro ⟨y, hy, rfl⟩
    change c + y - c ∈ openAxisCylinder e r lo hi
    rwa [add_sub_cancel_left]

private theorem translated_closedCylinder_image (c e : Point) (r lo hi : ℝ) :
    translatedClosedAxisCylinder c e r lo hi = (fun y : Point => c + y) '' closedAxisCylinder e r lo hi := by
  ext x
  constructor
  · intro hx
    exact ⟨x - c, hx, by abel⟩
  · rintro ⟨y, hy, rfl⟩
    change c + y - c ∈ closedAxisCylinder e r lo hi
    rwa [add_sub_cancel_left]

private theorem isometry_translatePoint (c : Point) : Isometry (fun y : Point => c + y) := by
  apply Isometry.of_dist_eq
  intro y z
  rw [dist_eq_norm, dist_eq_norm]
  congr 1
  abel

private theorem translated_openCylinder_axis_length {e : Point} (he : ‖e‖ = 1)
    (c : Point) {r : ℝ} (hr : 0 < r) (lo hi : ℝ) :
    (HausdorffOne.restrict ((fun y : Point => c + y) ''
      ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point)))
      (translatedAxisCylinder c e r lo hi) = ENNReal.ofReal (hi - lo) := by
  let L : Set Point := (Submodule.span ℝ {e} : Submodule ℝ Point)
  have hlen := hausdorffOne_axis_openCylinder he hr lo hi
  rw [Measure.restrict_apply (isOpen_openAxisCylinder _ _ _ _).measurableSet] at hlen
  rw [Measure.restrict_apply (isOpen_translatedAxisCylinder _ _ _ _ _).measurableSet,
    translated_openCylinder_image, ← Set.image_inter (isometry_translatePoint c).injective]
  have h := (isometry_translatePoint c).hausdorffMeasure_image (d := 1) (Or.inl zero_le_one)
    (openAxisCylinder e r lo hi ∩ L)
  exact h.trans hlen

private theorem translated_closedCylinder_axis_length {e : Point} (he : ‖e‖ = 1)
    (c : Point) {r : ℝ} (hr : 0 ≤ r) (lo hi : ℝ) :
    (HausdorffOne.restrict ((fun y : Point => c + y) ''
      ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point)))
      (translatedClosedAxisCylinder c e r lo hi) = ENNReal.ofReal (hi - lo) := by
  let L : Set Point := (Submodule.span ℝ {e} : Submodule ℝ Point)
  have hlen := hausdorffOne_axis_closedCylinder he hr lo hi
  rw [Measure.restrict_apply (isClosed_closedAxisCylinder _ _ _ _).measurableSet] at hlen
  have hC : IsClosed (translatedClosedAxisCylinder c e r lo hi) :=
    (isClosed_closedAxisCylinder _ _ _ _).preimage (continuous_id.sub continuous_const)
  rw [Measure.restrict_apply hC.measurableSet, translated_closedCylinder_image,
    ← Set.image_inter (isometry_translatePoint c).injective]
  have h := (isometry_translatePoint c).hausdorffMeasure_image (d := 1) (Or.inl zero_le_one)
    (closedAxisCylinder e r lo hi ∩ L)
  exact h.trans hlen

/-- The limit measure of a constant-weight line evaluates every local
cylinder by its literal axial length, including cylinders with two closed
end faces. -/
theorem localWeightedAxis_measure_open_closed_cylinder {μ : Measure Point} {V : Set Point}
    (c e : Point) (he : ‖e‖ = 1) {b : ℝ} (hb : 0 ≤ b)
    (hLocal : μ.restrict V = (ENNReal.ofReal b • HausdorffOne.restrict
      ((fun y : Point => c + y) '' ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point))).restrict V)
    {r lo hi : ℝ} (hr : 0 < r) (_hHeight : lo ≤ hi)
    (hSub : translatedClosedAxisCylinder c e r lo hi ⊆ V) :
    (μ : Measure Point) (translatedAxisCylinder c e r lo hi) = ENNReal.ofReal (b * (hi-lo)) ∧
      (μ : Measure Point) (translatedClosedAxisCylinder c e r lo hi) = ENNReal.ofReal (b * (hi-lo)) := by
  let ν := ENNReal.ofReal b • HausdorffOne.restrict
    ((fun y : Point => c + y) '' ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point))
  have hEval (K : Set Point) (hK : MeasurableSet K) (hKV : K ⊆ V) : μ K = ν K := by
    have h := congrArg (fun m : Measure Point => m K) hLocal
    change (μ.restrict V) K = (ν.restrict V) K at h
    rwa [Measure.restrict_apply hK, Measure.restrict_apply hK, inter_eq_left.mpr hKV] at h
  have hOpen := hEval _ (isOpen_translatedAxisCylinder _ _ _ _ _).measurableSet
    ((translatedAxisCylinder_subset_closed _ _ _ _ _).trans hSub)
  have hC : IsClosed (translatedClosedAxisCylinder c e r lo hi) :=
    (isClosed_closedAxisCylinder _ _ _ _).preimage (continuous_id.sub continuous_const)
  have hClosed := hEval (translatedClosedAxisCylinder c e r lo hi) hC.measurableSet hSub
  rw [Measure.smul_apply, smul_eq_mul, translated_openCylinder_axis_length he c hr,
    ← ENNReal.ofReal_mul hb] at hOpen
  rw [Measure.smul_apply, smul_eq_mul, translated_closedCylinder_axis_length he c hr.le,
    ← ENNReal.ofReal_mul hb] at hClosed
  exact ⟨hOpen, hClosed⟩

private theorem tendsto_real_measure_axisCylinder_of_local_weight
    {ν : ℕ → FiniteMeasure Point} {μ : FiniteMeasure Point}
    (hWeak : Tendsto ν atTop (𝓝 μ))
    {c e : Point} {r lo hi b : ℝ}
    (hOpen : (μ : Measure Point) (translatedAxisCylinder c e r lo hi) = ENNReal.ofReal (b * (hi-lo)))
    (hClosed : (μ : Measure Point) (translatedClosedAxisCylinder c e r lo hi) = ENNReal.ofReal (b * (hi-lo)))
    (hb : 0 ≤ b) (hHeight : lo ≤ hi) :
    Tendsto (fun n => ((ν n : Measure Point) (translatedAxisCylinder c e r lo hi)).toReal) atTop
      (𝓝 (b * (hi-lo))) := by
  let S := translatedAxisCylinder c e r lo hi
  let C := translatedClosedAxisCylinder c e r lo hi
  have hS : IsOpen S := isOpen_translatedAxisCylinder _ _ _ _ _
  have hC : IsClosed C := (isClosed_closedAxisCylinder _ _ _ _).preimage
    (continuous_id.sub continuous_const)
  have hSC : S ⊆ C := translatedAxisCylinder_subset_closed _ _ _ _ _
  have hFront : frontier S ⊆ C \ S := by
    intro x hx
    refine ⟨closure_minimal hSC hC (frontier_subset_closure hx), ?_⟩
    exact fun h => hx.2 (hS.interior_eq.symm ▸ h)
  have hZero : (μ : Measure Point) (C \ S) = 0 := by
    rw [measure_sdiff hSC hS.measurableSet.nullMeasurableSet (measure_ne_top μ S), hOpen, hClosed, tsub_self]
  have h0 : (μ : Measure Point) (frontier S) = 0 := measure_mono_null hFront hZero
  have hMass := tendsto_measure_of_null_frontier hWeak h0
  have hR := (ENNReal.continuousAt_toReal (measure_ne_top μ S)).tendsto.comp hMass
  rw [hOpen, ENNReal.toReal_ofReal (mul_nonneg hb (sub_nonneg.mpr hHeight))] at hR
  exact hR

/-- At a fixed small physical radius, varying the two heights in the
source intervals preserves the exact constant-weight segment mass. -/
theorem tendsto_moving_heightCylinder_mass_of_local_weight
    {ν : ℕ → FiniteMeasure Point} {μ : FiniteMeasure Point}
    (hWeak : Tendsto ν atTop (𝓝 μ))
    {V : Set Point} (c e : Point) (he : ‖e‖ = 1) {b r s : ℝ} (hb : 0 ≤ b)
    (hr : 0 < r) (hs : 0 < s)
    (hLocal : μ.restrict V = (ENNReal.ofReal b • HausdorffOne.restrict
      ((fun y : Point => c + y) '' ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point))).restrict V)
    (hSub : translatedClosedAxisCylinder c e r (-(2*s)) (2*s) ⊆ V)
    {lo hi : ℕ → ℝ} {lo₀ hi₀ : ℝ}
    (hlo : Tendsto lo atTop (𝓝 lo₀)) (hhi : Tendsto hi atTop (𝓝 hi₀))
    (hlo₀ : lo₀ ∈ Icc (-s) (-(s/2))) (hhi₀ : hi₀ ∈ Icc (s/2) s) :
    Tendsto (fun n => ((ν n : Measure Point) (translatedAxisCylinder c e r (lo n) (hi n))).toReal /
      (hi n - lo n)) atTop (𝓝 b) := by
  let H := hi₀ - lo₀
  have hH : 0 < H := by dsimp only [H]; linarith only [hs, hlo₀.2, hhi₀.1]
  have hStatic (lo' hi' : ℝ) (hl : -(2*s) ≤ lo') (hu : hi' ≤ 2*s) (hlh : lo' ≤ hi') :
      Tendsto (fun n => ((ν n : Measure Point) (translatedAxisCylinder c e r lo' hi')).toReal) atTop
        (𝓝 (b * (hi'-lo'))) := by
    have hL : translatedClosedAxisCylinder c e r lo' hi' ⊆
        translatedClosedAxisCylinder c e r (-(2*s)) (2*s) := fun _ hx =>
      ⟨hx.1, hl.trans hx.2.1, hx.2.2.trans hu⟩
    obtain ⟨hO, hC⟩ := localWeightedAxis_measure_open_closed_cylinder c e he hb hLocal hr hlh (hL.trans hSub)
    exact tendsto_real_measure_axisCylinder_of_local_weight hWeak hO hC hb hlh
  have hMass : Tendsto (fun n => ((ν n : Measure Point) (translatedAxisCylinder c e r (lo n) (hi n))).toReal)
      atTop (𝓝 (b * H)) := by
    apply Metric.tendsto_nhds.mpr
    intro ξ hξ
    let γ := min (s/8) (ξ / (8*(b+1)))
    have hγ : 0 < γ := lt_min (div_pos hs (by norm_num)) (div_pos hξ (by linarith only [hb]))
    have hγs : γ ≤ s/8 := min_le_left _ _
    have hγb : 8*(b+1)*γ ≤ ξ := by
      have hh := (le_div_iff₀ (show 0 < 8*(b+1) by linarith only [hb])).mp
        (min_le_right (s/8) (ξ/(8*(b+1))))
      simpa only [γ, mul_comm γ] using hh
    have hB : 2*b*γ < ξ/2 := by nlinarith only [hγb, hγ, mul_nonneg hb hγ.le]
    have hIn := hStatic (lo₀+γ) (hi₀-γ)
      (by linarith only [hlo₀.1, hγ, hs]) (by linarith only [hhi₀.2, hγ, hs])
      (by linarith only [hlo₀.2, hhi₀.1, hγs, hs])
    have hOut := hStatic (lo₀-γ) (hi₀+γ)
      (by linarith only [hlo₀.1, hγs, hs]) (by linarith only [hhi₀.2, hγs, hs])
      (by linarith only [hlo₀.2, hhi₀.1, hγ, hs])
    have hIn' := hIn.eventually (eventually_gt_nhds (sub_lt_self _ (half_pos hξ)))
    have hOut' := hOut.eventually (eventually_lt_nhds (lt_add_of_pos_right _ (half_pos hξ)))
    have hlo' := hlo.eventually (Ioo_mem_nhds (sub_lt_self _ hγ) (lt_add_of_pos_right _ hγ))
    have hhi' := hhi.eventually (Ioo_mem_nhds (sub_lt_self _ hγ) (lt_add_of_pos_right _ hγ))
    filter_upwards [hIn', hOut', hlo', hhi'] with n hInN hOutN hloN hhiN
    let U := translatedAxisCylinder c e r (lo n) (hi n)
    let UI := translatedAxisCylinder c e r (lo₀+γ) (hi₀-γ)
    let UO := translatedAxisCylinder c e r (lo₀-γ) (hi₀+γ)
    have hUi : UI ⊆ U := fun _ hx => ⟨hx.1, hloN.2.trans hx.2.1, hx.2.2.trans hhiN.1⟩
    have hUo : U ⊆ UO := fun _ hx => ⟨hx.1, hloN.1.trans hx.2.1, hx.2.2.trans hhiN.2⟩
    have hL := ENNReal.toReal_mono (measure_ne_top (ν n) U) (measure_mono hUi)
    have hU := ENNReal.toReal_mono (measure_ne_top (ν n) UO) (measure_mono hUo)
    change dist ((ν n : Measure Point) U).toReal (b * H) < ξ
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> dsimp only [H] <;> linarith only [hL, hU, hInN, hOutN, hB]
  have hHeight : Tendsto (fun n => hi n - lo n) atTop (𝓝 H) := hhi.sub hlo
  have hRatio := hMass.div hHeight hH.ne'
  rwa [mul_div_cancel_right₀ _ hH.ne'] at hRatio

end Thesis.MeasureGeometry
