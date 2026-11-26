module

public import Thesis.Variational.FlatWallPoissonComparison
public import Thesis.Upstream.EuclideanGradientTransform
public import Thesis.Variational.EllipticPatchGeometry

/-! Small perturbation of the weak metric in a tangent-frame wall chart. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal RealInnerProductSpace

namespace Thesis

private theorem axis_norm_weakSlope (j : Fin 3) : ‖axis j‖ = 1 := by simp [axis]

private theorem sum_isometry_coordinate_products (Q : Point ≃ₗᵢ[ℝ] Point) (i j : Fin 3) :
    (∑ k : Fin 3, (Q (axis k)) i*(Q (axis k)) j) = if i = j then 1 else 0 := by
  classical
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).map Q
  have hbi (k : Fin 3) : b k = Q (axis k) := by
    rw [OrthonormalBasis.map_apply,EuclideanSpace.basisFun_apply]
    rfl
  have hInner (k : Fin 3) (v : Point) : inner ℝ (axis k) v = v k := by
    simp [axis,EuclideanSpace.inner_single_left]
  have hInnerR (k : Fin 3) (v : Point) : inner ℝ v (axis k) = v k :=
    (real_inner_comm _ _).trans (hInner k v)
  have h := b.sum_inner_mul_inner (axis i) (axis j)
  simp only [hInner,hInnerR,hbi] at h
  rw [show axis j i = if i = j then 1 else 0 from by simp [axis,PiLp.single_apply]] at h
  exact h

private theorem ambientMetricEntry_perturbation {K : Point →L[ℝ] Point}
    (Q : Point ≃ₗᵢ[ℝ] Point) {η : ℝ} (hη : 0 ≤ η)
    (hClose : ∀ v : Point, ‖K v-Q v‖ ≤ η*‖v‖)
    (hN : ∀ v : Point, ‖K v‖ ≤ (1+η)*‖v‖) (i j : Fin 3) :
    |(if i = j then 1 else 0) - ambientGradientMetricEntry K j i| ≤ 3*η*(2+η) := by
  classical
  have hΔ (k l : Fin 3) : |(K (axis k)) l-(Q (axis k)) l| ≤ η := by
    have h := (PiLp.norm_apply_le (K (axis k)-Q (axis k)) l).trans (hClose (axis k))
    simpa only [axis_norm_weakSlope,mul_one,PiLp.sub_apply,Real.norm_eq_abs] using h
  have hK₁ (k l : Fin 3) : |(K (axis k)) l| ≤ 1+η := by
    have h := (PiLp.norm_apply_le (K (axis k)) l).trans (hN (axis k))
    simpa only [axis_norm_weakSlope,mul_one,Real.norm_eq_abs] using h
  have hQ₁ (k l : Fin 3) : |(Q (axis k)) l| ≤ 1 := by
    simpa only [Real.norm_eq_abs,LinearIsometryEquiv.norm_map,axis_norm_weakSlope] using
      PiLp.norm_apply_le (Q (axis k)) l
  have hTerm (k : Fin 3) :
      |(K (axis k)) j*(K (axis k)) i - (Q (axis k)) j*(Q (axis k)) i| ≤ η*(2+η) := by
    rw [show (K (axis k)) j*(K (axis k)) i - (Q (axis k)) j*(Q (axis k)) i =
      ((K (axis k)) j-(Q (axis k)) j)*(K (axis k)) i +
        (Q (axis k)) j*((K (axis k)) i-(Q (axis k)) i) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul,abs_mul]
    calc
      _ ≤ η*(1+η)+1*η := add_le_add
        (mul_le_mul (hΔ k j) (hK₁ k i) (abs_nonneg _) hη)
        (mul_le_mul (hQ₁ k j) (hΔ k i) (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  have he : (∑ k : Fin 3, (Q (axis k)) j*(Q (axis k)) i) = if i = j then 1 else 0 := by
    simpa only [eq_comm] using sum_isometry_coordinate_products Q j i
  rw [abs_sub_comm,← he,ambientGradientMetricEntry,← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun k _ => hTerm k).trans_eq ?_
  simp only [Fin.sum_univ_three]
  ring

/-- A fixed wall point has a smooth measure-preserving chart on a true
half-ball whose actual weak metric is as close to the Euclidean matrix
as prescribed. -/
theorem IsSmoothDomain.exists_weakSmallSlopeGraphPatch {U : Set Point} (hU : IsSmoothDomain U)
    {a : Point} (ha : a ∈ frontier U) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (P : RegularWallGraphPatch U) (R : ℝ), P.center = a ∧ ContDiff ℝ ∞ P.height ∧
      0 < R ∧ ball (0 : Point) R ⊆ P.flatBox ∧
      ∀ i j x, x ∈ ball (0 : Point) R →
        |(if i = j then 1 else 0)-ambientGradientMetricEntry
          (fderiv ℝ P.flatChart.symm (P.flatChart x)) j i| ≤ δ := by
  let η := min 1 (δ/9)
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  obtain ⟨P,hPa,hP,hSlope⟩ := hU.exists_graphPatch_small_slope ha hη
  have hP₂ : ContDiff ℝ 2 P.height := hP.of_le (WithTop.coe_le_coe.mpr le_top)
  have h0 : (0 : Point) ∈ P.flatBox := by
    change planeLinePlacement.symm (0 : Point) ∈ P.box
    rw [map_zero]
    exact ⟨mem_ball_self P.baseRadius_pos,neg_neg_of_pos P.halfHeight_pos,P.halfHeight_pos⟩
  obtain ⟨R,hR,hB⟩ := Metric.isOpen_iff.mp P.flatBox_isOpen _ h0
  refine ⟨P,R,hPa,hP,hR,hB,?_⟩
  intro i j x hx
  refine (ambientMetricEntry_perturbation P.frame.repr hη.le
    (P.derivative_flatChart_symm_close hP₂ hη.le hSlope (hB hx))
    (P.derivative_flatChart_symm_norm_le hP₂ hη.le hSlope (hB hx)) i j).trans ?_
  have hη₁ : η ≤ 1 := min_le_left _ _
  have hηδ : η ≤ δ/9 := min_le_right _ _
  calc
    _ ≤ 3*η*3 := mul_le_mul_of_nonneg_left (by linarith only [hη₁]) (by positivity)
    _ ≤ _ := by linarith only [hηδ]

/-- The corresponding global chart and its exact volume and wall data. -/
theorem IsSmoothDomain.exists_weakSmallSlopeWallChart {U : Set Point} (hU : IsSmoothDomain U)
    {a : Point} (ha : a ∈ frontier U) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (F : Point ≃ₜ Point) (R : ℝ), 0 < R ∧ F 0 = a ∧
      ContDiff ℝ ∞ (F : Point → Point) ∧ ContDiff ℝ ∞ (F.symm : Point → Point) ∧
      MeasurePreserving F (volume : Measure Point) volume ∧
      (∀ x ∈ ball (0 : Point) R, F x ∈ U ↔ x ∈ upperCoordinateHalfSpace.val) ∧
      (∀ i j x, x ∈ ball (0 : Point) R →
        |(if i = j then 1 else 0)-ambientGradientMetricEntry (fderiv ℝ F.symm (F x)) j i| ≤ δ) := by
  obtain ⟨P,R,hPa,hP,hR,hB,hClose⟩ := hU.exists_weakSmallSlopeGraphPatch ha hδ
  refine ⟨P.flatChart,R,hR,?_,P.flatChart_contDiff hP,P.flatChart_symm_contDiff hP,P.flatChart_volume,
    fun x hx => P.flatChart_mem_domain (hB hx),hClose⟩
  rw [P.flatChart_apply,map_zero,P.height_zero,zero_smul,add_zero,map_zero,add_zero,hPa]

end Thesis
