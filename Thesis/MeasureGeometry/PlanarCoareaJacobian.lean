module

public import Thesis.Definitions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Basic

/-! The exact Cartesian Jacobian and level-curve speed of a planar scalar chart. -/

public section

noncomputable section

open scoped RealInnerProductSpace

namespace Thesis

private abbrev planeAxis (i : Fin 2) : Plane := EuclideanSpace.single i 1

private theorem planar_clm_eq_sum_columns {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Plane →L[ℝ] E) (v : Plane) :
    D v = v 0 • D (planeAxis 0) + v 1 • D (planeAxis 1) := by
  have hSum : (∑ i : Fin 2, v i • planeAxis i) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v
  exact (congrArg D hSum).symm.trans (by rw [map_sum, Fin.sum_univ_two, map_smul, map_smul])

private theorem planar_scalar_chart_det
    (j : Fin 2) (D : Plane →L[ℝ] ℝ) (C : Plane →L[ℝ] Plane)
    (hC : ∀ v, (C v) 0 = D v ∧ (C v) 1 = v j) :
    C.det = if j = 0 then -D (planeAxis 1) else D (planeAxis 0) := by
  let e := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hMat : C.det = (LinearMap.toMatrix e e C.toLinearMap).det := by
    exact (LinearMap.det_toMatrix e C.toLinearMap).symm
  have hM (i k : Fin 2) : LinearMap.toMatrix e e C.toLinearMap i k = (C (planeAxis k)) i := by
    rw [LinearMap.toMatrix_apply]
    simp only [e, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, ContinuousLinearMap.coe_coe]
  rw [hMat, Matrix.det_fin_two, hM, hM, hM, hM, (hC _).1, (hC _).2, (hC _).1, (hC _).2]
  fin_cases j <;> simp [planeAxis]

/-- Some Cartesian coordinate completes the nonzero scalar derivative
to an invertible planar chart. -/
theorem exists_planar_scalar_chart_nondegenerate_coordinate
    (D : Plane →L[ℝ] ℝ) (hD : D ≠ 0) :
    ∃ j : Fin 2, ∀ C : Plane →L[ℝ] Plane, (∀ v, (C v) 0 = D v ∧ (C v) 1 = v j) → C.det ≠ 0 := by
  by_cases h : D (planeAxis 0) = 0
  · have h₁ : D (planeAxis 1) ≠ 0 := by
      intro h₁
      apply hD
      ext v
      rw [planar_clm_eq_sum_columns, h, h₁, smul_zero, smul_zero, add_zero, zero_apply]
    refine ⟨0, fun C hC => ?_⟩
    rw [planar_scalar_chart_det 0 D C hC, if_pos rfl, neg_ne_zero]
    exact h₁
  · refine ⟨1, fun C hC => ?_⟩
    rw [planar_scalar_chart_det 1 D C hC, if_neg (by decide)]
    exact h

private theorem norm_planar_scalar_clm_of_columns (D : Plane →L[ℝ] ℝ) :
    ‖D‖ = Real.sqrt (D (planeAxis 0) ^ 2 + D (planeAxis 1) ^ 2) := by
  let v : Plane := WithLp.toLp 2 ![D (planeAxis 0), D (planeAxis 1)]
  have hv0 : v 0 = D (planeAxis 0) := rfl
  have hv1 : v 1 = D (planeAxis 1) := rfl
  have hD (x : Plane) : D x = inner ℝ v x := by
    rw [planar_clm_eq_sum_columns, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    unfold dotProduct
    rw [Fin.sum_univ_two, hv0, hv1, smul_eq_mul, smul_eq_mul]
  have hnorm : ‖D‖ = ‖v‖ := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro x
      rw [hD x]
      exact norm_inner_le_norm _ _
    · by_cases hz : v = 0
      · rw [hz, norm_zero]
        exact ContinuousLinearMap.opNorm_nonneg _
      · have hpos : 0 < ‖v‖ := norm_pos_iff.2 hz
        have hOp := D.le_opNorm v
        rw [hD v, real_inner_self_eq_norm_sq, Real.norm_of_nonneg (sq_nonneg _), pow_two] at hOp
        exact le_of_mul_le_mul_right hOp hpos
  rw [hnorm, EuclideanSpace.norm_eq, Fin.sum_univ_two, hv0, hv1]
  simp only [Real.norm_eq_abs, sq_abs]

/-- On the inverse chart the column along a level set has speed
equal to the original scalar gradient norm divided by the chart Jacobian. -/
theorem planar_scalar_chart_jacobian_speed
    (j : Fin 2) (D : Plane →L[ℝ] ℝ) (C B : Plane →L[ℝ] Plane)
    (hC : ∀ v, (C v) 0 = D v ∧ (C v) 1 = v j) (hBC : ∀ v, B (C v) = v) :
    |C.det| * ‖B (EuclideanSpace.single (1 : Fin 2) 1)‖ = ‖D‖ := by
  let v : Plane := WithLp.toLp 2 ![-D (planeAxis 1), D (planeAxis 0)]
  have hv0 : v 0 = -D (planeAxis 1) := rfl
  have hv1 : v 1 = D (planeAxis 0) := rfl
  have hCv : C v = C.det • planeAxis 1 := by
    apply PiLp.ext
    intro k
    fin_cases k
    · change (C v) (0 : Fin 2) = (C.det • planeAxis 1) (0 : Fin 2)
      rw [(hC v).1, planar_clm_eq_sum_columns, hv0, hv1]
      simp [planeAxis, PiLp.smul_apply]
      ring
    · change (C v) (1 : Fin 2) = (C.det • planeAxis 1) (1 : Fin 2)
      rw [(hC v).2, planar_scalar_chart_det j D C hC]
      fin_cases j <;> simp [planeAxis, PiLp.smul_apply, hv0, hv1]
  have hv : v = C.det • B (planeAxis 1) := by
    rw [← hBC v, hCv, map_smul]
  have hN : ‖v‖ = |C.det| * ‖B (planeAxis 1)‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using congrArg (fun z : Plane => ‖z‖) hv
  rw [← hN, norm_planar_scalar_clm_of_columns, EuclideanSpace.norm_eq, Fin.sum_univ_two, hv0, hv1]
  simp only [Real.norm_eq_abs, abs_neg, sq_abs, add_comm]

end Thesis
