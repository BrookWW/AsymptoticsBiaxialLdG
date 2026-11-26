module

public import Thesis.MeasureGeometry.WeightedSegmentNetwork
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Hausdorff

/-! Arclength and the fundamental theorem of calculus on an actual edge. -/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped ContDiff ENNReal RealInnerProductSpace Topology

namespace Thesis.MeasureGeometry

@[expose] def segmentDirection (p q : Point) : Point := ‖q - p‖⁻¹ • (q - p)

theorem norm_segmentDirection {p q : Point} (hpq : p ≠ q) : ‖segmentDirection p q‖ = 1 := by
  have h := norm_pos_iff.2 (sub_ne_zero.2 hpq.symm)
  unfold segmentDirection
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 h.le), inv_mul_cancel₀ h.ne']

theorem segmentDirection_reverse (p q : Point) : segmentDirection q p = -segmentDirection p q := by
  unfold segmentDirection
  rw [show p - q = -(q - p) by abel, norm_neg, smul_neg]

theorem length_smul_segmentDirection {p q : Point} (hpq : p ≠ q) :
    ‖q - p‖ • segmentDirection p q = q - p := by
  have h := norm_pos_iff.2 (sub_ne_zero.2 hpq.symm)
  rw [segmentDirection, smul_smul, mul_inv_cancel₀ h.ne', one_smul]

/-- The normalized affine parameter pushes arclength forward with its
exact constant length. -/
theorem hausdorffOne_restrict_segment_eq_map (p q : Point) :
    HausdorffOne.restrict (segment ℝ p q) =
      (nndist p q) • Measure.map (AffineMap.lineMap p q : ℝ → Point)
        (volume.restrict (Icc (0 : ℝ) 1)) := by
  let F : ℝ → Point := AffineMap.lineMap p q
  have hF : Continuous F := by
    change Continuous (fun s : ℝ => AffineMap.lineMap p q s)
    simp only [AffineMap.lineMap_apply_module']
    fun_prop
  ext V hV
  have hImage : F '' (F ⁻¹' V ∩ Icc 0 1) = V ∩ segment ℝ p q := by
    rw [segment_eq_image_lineMap]
    ext z
    constructor
    · rintro ⟨t, ⟨htV, htI⟩, rfl⟩
      exact ⟨htV, ⟨t, htI, rfl⟩⟩
    · rintro ⟨hz, ⟨t, ht, rfl⟩⟩
      exact ⟨t, ⟨hz, ht⟩, rfl⟩
  change HausdorffOne.restrict (segment ℝ p q) V = ((nndist p q) •
    Measure.map F (volume.restrict (Icc (0 : ℝ) 1))) V
  rw [Measure.restrict_apply hV, Measure.smul_apply, Measure.map_apply hF.measurable hV,
    Measure.restrict_apply (hF.measurable hV), ← hImage]
  change HausdorffOne ((AffineMap.lineMap p q : ℝ → Point) '' (F ⁻¹' V ∩ Icc 0 1)) = _
  rw [hausdorffMeasure_lineMap_image, hausdorffMeasure_real]

theorem integral_hausdorffOne_segment {f : Point → ℝ} (hf : Continuous f) (p q : Point) :
    (∫ z in segment ℝ p q, f z ∂HausdorffOne) =
      ‖q - p‖ * ∫ t in Icc (0 : ℝ) 1, f (AffineMap.lineMap p q t) := by
  let F : ℝ → Point := AffineMap.lineMap p q
  have hF : Continuous F := by
    change Continuous (fun s : ℝ => AffineMap.lineMap p q s)
    simp only [AffineMap.lineMap_apply_module']
    fun_prop
  rw [hausdorffOne_restrict_segment_eq_map, integral_smul_nnreal_measure,
    integral_map hF.measurable.aemeasurable hf.aestronglyMeasurable]
  change dist p q * (∫ t in Icc (0 : ℝ) 1, f (AffineMap.lineMap p q t)) = _
  rw [dist_comm, dist_eq_norm]

private theorem sum_smul_axis_eq (v : Point) : (∑ i : Fin 3, v i • axis i) = v := by
  apply PiLp.ext
  intro j
  fin_cases j <;> simp [axis, Fin.sum_univ_three]

private theorem coord_contraction_eq_inner (X : Point → Point) (v z : Point) :
    (∑ i : Fin 3, ∑ j : Fin 3, (v i * v j) * coordDeriv i X z j) =
      inner ℝ v (fderiv ℝ X z v) := by
  let D := fderiv ℝ X z
  have h : D v = ∑ i : Fin 3, v i • D (axis i) := by
    conv_lhs => rw [← sum_smul_axis_eq v]
    simp only [map_sum, map_smul]
  change (∑ i : Fin 3, ∑ j : Fin 3, (v i * v j) * D (axis i) j) = inner ℝ v (D v)
  rw [h, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right, PiLp.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change _ = v i * ((D (axis i) j) * v j)
  ring

/-- A single straight segment tests stationary tangential divergence by
the corresponding signed boundary flux. -/
theorem integral_segment_tangentialDivergence {X : Point → Point} (hX : ContDiff ℝ 1 X)
    {p q : Point} (hpq : p ≠ q) :
    let v := segmentDirection p q
    (∫ z in segment ℝ p q, (∑ i : Fin 3, ∑ j : Fin 3, (v i * v j) * coordDeriv i X z j) ∂HausdorffOne) =
      inner ℝ v (X q - X p) := by
  intro v
  let F : ℝ → Point := AffineMap.lineMap p q
  let g (z : Point) := inner ℝ v (fderiv ℝ X z v)
  let γ (t : ℝ) := inner ℝ v (X (F t))
  let ℓ := ‖q - p‖
  have hF : Continuous F := by
    change Continuous (fun t : ℝ => AffineMap.lineMap p q t)
    simp only [AffineMap.lineMap_apply_module']
    fun_prop
  have hg : Continuous g :=
    (continuous_const : Continuous (fun _ : Point => v)).inner
      ((hX.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hγ (t : ℝ) : HasDerivAt γ (ℓ * g (F t)) t := by
    have hXf := (hX.differentiable (by norm_num) (F t)).hasFDerivAt
    have hIn : HasDerivAt (X ∘ F) (fderiv ℝ X (F t) (q - p)) t :=
      hXf.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap
    have hL := (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt t hIn
    have hCoeff : inner ℝ v (fderiv ℝ X (F t) (q - p)) = ℓ * g (F t) := by
      rw [← length_smul_segmentDirection hpq, map_smul, real_inner_smul_right]
    exact hCoeff ▸ hL
  have hInt : IntervalIntegrable (fun t => ℓ * g (F t)) volume 0 1 :=
    (continuous_const.mul (hg.comp hF)).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hγ t) hInt
  simp only [γ, F, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at hFTC
  calc
    _ = ∫ z in segment ℝ p q, g z ∂HausdorffOne := integral_congr_ae
      (Filter.Eventually.of_forall (coord_contraction_eq_inner X v))
    _ = ℓ * ∫ t in Icc (0 : ℝ) 1, g (F t) := integral_hausdorffOne_segment hg p q
    _ = ∫ t in (0 : ℝ)..1, ℓ * g (F t) := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc, integral_const_mul]
    _ = _ := hFTC.trans (inner_sub_right _ _ _).symm

end Thesis.MeasureGeometry
