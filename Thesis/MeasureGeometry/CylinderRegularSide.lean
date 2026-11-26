module

public import Thesis.MeasureGeometry.EnergyCylinderTangent

/-! Compact regular lateral bands at almost-everywhere line blow-ups. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal RealInnerProductSpace Topology

namespace Thesis.MeasureGeometry

theorem cylinderTransverseRadius_smul_of_nonneg (e y : Point) {s : ℝ} (hs : 0 ≤ s) :
    cylinderTransverseRadius e (s • y) = s * cylinderTransverseRadius e y := by
  unfold cylinderTransverseRadius cylinderHeight
  rw [real_inner_smul_right, ← smul_smul, ← smul_sub, norm_smul, Real.norm_of_nonneg hs]

/-- At a flat blow-up of positive density, a compact band of lateral
sides can be chosen wholly in the regular region, at physical radii
strictly between `δ*s` and `2δ*s`. -/
theorem eventually_exists_compact_regular_lateral_band
    {Ω Spt : Set Point} (hΩ : IsOpen Ω) {μ : Measure Point} [IsFiniteMeasure μ] [μ.OuterRegular]
    (hLoc : LocallyFiniteIn (Ω \ μ.support) Spt) {η : ℝ} (hη : 0 < η)
    (hD : ∀ x ∈ Ω ∩ μ.support, ∃ θ ≥ η / 2, Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ))
    {x e : Point} (hx : x ∈ Ω) (he : ‖e‖ = 1) {b : ℝ}
    (hFlat : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun s => SupportingAnalysis.blownUpMeasure (d := 1) x s μ)
      (ENNReal.ofReal b • HausdorffOne.restrict ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ∃ r₀ r₁ : ℝ, δ < r₀ ∧ r₀ < r₁ ∧ r₁ < 2 * δ ∧
      let A := (fun y : Point => x + s • y) '' closedAxisAnnularCylinder e r₀ r₁ (-1) 1
      IsCompact A ∧ A ⊆ (Ω \ μ.support) \ Spt := by
  obtain ⟨d, hd, hdΩ⟩ := Metric.isOpen_iff.mp hΩ x hx
  let ξ := δ * η / 80
  have hξ : 0 < ξ := by positivity
  let A₀ := closedAxisAnnularCylinder e δ (2 * δ) (-1) 1
  have hA₀ : IsCompact A₀ := isCompact_closedAxisAnnularCylinder he _ _ _ _
  have hR : 0 < 2 * δ + 2 := by positivity
  have hFin (s : ℝ) : IsFiniteMeasureOnCompacts (SupportingAnalysis.blownUpMeasure (d := 1) x s μ) := by
    letI := SupportingAnalysis.blownUpMeasure_isFiniteMeasure (d := 1) x s μ
    infer_instance
  filter_upwards [eventually_small_annularCylinder_at_line hFin he hFlat
      (r₀ := δ) (r₁ := 2 * δ) (lo := -1) (hi := 1) hδ hξ,
    eventually_mem_positive_interval (div_pos hd hR)] with s hSmallNorm hs
  let T (y : Point) := x + s • y
  let A := T '' A₀
  have hTac : Continuous T := by dsimp only [T]; fun_prop
  have hA : IsCompact A := hA₀.image hTac
  have hAΩ : A ⊆ Ω := by
    rintro z ⟨y, hy, rfl⟩
    apply hdΩ
    have hY : ‖y‖ ≤ 2 * δ + 2 := by
      have hB := closedAxisCylinder_subset_closedBall he (2 * δ) (-1) 1 hy.1
      simpa only [mem_closedBall, dist_zero_right, abs_neg, abs_one, add_assoc, one_add_one_eq_two] using hB
    rw [mem_ball, dist_eq_norm]
    change ‖x + s • y - x‖ < d
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1.le]
    exact (mul_le_mul_of_nonneg_left hY hs.1.le).trans_lt ((lt_div_iff₀ hR).mp hs.2)
  have hSmall : ENNReal.ofReal (40 / η) * μ A < ENNReal.ofReal (2 * δ * s - δ * s) := by
    rw [oneBlowup_toReal_apply x hs.1 hA₀.isClosed.measurableSet] at hSmallNorm
    have hReal : (μ A).toReal / s < ξ := hSmallNorm
    have hScale : (μ A).toReal < ξ * s := (div_lt_iff₀ hs.1).mp hReal
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ A), ← ENNReal.ofReal_mul (by positivity)]
    apply (ENNReal.ofReal_lt_ofReal_iff (by nlinarith only [hδ, hs.1] : 0 < 2 * δ * s - δ * s)).mpr
    calc
      (40 / η) * (μ A).toReal < (40 / η) * (ξ * s) :=
        mul_lt_mul_of_pos_left hScale (div_pos (by norm_num) hη)
      _ = δ * s / 2 := by dsimp only [ξ]; field_simp [hη.ne']; ring
      _ < _ := by nlinarith only [mul_pos hδ hs.1]
  obtain ⟨p, q, hp, hpq, hq, hSide⟩ :=
    exists_closed_axisRadius_interval_avoiding_lineSupport μ hA hAΩ hη hD x he hSmall
  let f (y : Point) := cylinderTransverseRadius e (y - x)
  have hf : Continuous f := (continuous_cylinderTransverseRadius e).comp (continuous_id.sub continuous_const)
  let B := A ∩ f ⁻¹' Icc p q
  have hB : IsCompact B := hA.inter_right (isClosed_Icc.preimage hf)
  have hBW : B ⊆ Ω \ μ.support := fun y hy => ⟨hAΩ hy.1, hSide y hy.1 hy.2⟩
  let J := Spt ∩ B
  have hJ : J.Finite := hLoc B hB hBW
  letI : NullSingletonClass HausdorffOne :=
    Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  have hJlen : HausdorffOne J < ENNReal.ofReal (q - p) := by
    rw [hJ.countable.measure_zero HausdorffOne]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hpq)
  obtain ⟨p', q', hp', hpq', hq', hNo⟩ := exists_closed_axisRadius_interval_avoiding_compact hJ.isCompact x he hJlen
  have hRad₀ : δ < p' / s := (lt_div_iff₀ hs.1).mpr (hp.trans hp')
  have hRad₁ : q' / s < 2 * δ := (div_lt_iff₀ hs.1).mpr (hq'.trans hq)
  have hRad : p' / s < q' / s := div_lt_div_of_pos_right hpq' hs.1
  refine ⟨p' / s, q' / s, hRad₀, hRad, hRad₁,
    (isCompact_closedAxisAnnularCylinder he _ _ _ _).image hTac, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hz₀ : z ∈ A₀ := by
    refine ⟨⟨hz.1.1.trans (le_of_lt hRad₁), hz.1.2⟩, hRad₀.le.trans hz.2⟩
  have hA' : T z ∈ A := ⟨z, hz₀, rfl⟩
  have hMap : f (T z) = s * cylinderTransverseRadius e z := by
    dsimp only [f, T]
    rw [add_sub_cancel_left, cylinderTransverseRadius_smul_of_nonneg e z hs.1.le]
  have hMem : f (T z) ∈ Icc p' q' := by
    rw [hMap]
    exact ⟨by
      simpa only [mul_comm s] using (div_le_iff₀ hs.1).mp hz.2, by
      simpa only [mul_comm s] using (le_div_iff₀ hs.1).mp hz.1.1⟩
  have hBZ : T z ∈ B := ⟨hA', hp'.le.trans hMem.1, hMem.2.trans hq'.le⟩
  refine ⟨hBW hBZ, fun hSing => ?_⟩
  exact (disjoint_left.mp hNo) hMem ⟨T z, ⟨hSing, hBZ⟩, rfl⟩

end Thesis.MeasureGeometry
