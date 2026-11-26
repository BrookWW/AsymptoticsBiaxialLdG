module

public import Thesis.StressEnergy
public import Thesis.Foundation.BulkGeometry
public import Thesis.Foundation.Frobenius
public import Thesis.MeasureGeometry.EnergyMeasure

/-! Pointwise bounds for the stress matrix driving the line-defect measure. -/

public section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace Thesis

/-- The Gram matrix of the three displayed gradient columns. -/
noncomputable def gradientGram (D : Gradient) : Tensor := fun i j => frobeniusS0 (D i) (D j)

/-- The stress matrix defined using the actual gradient columns. -/
noncomputable def elasticStress (a : BulkCoefficients) (ε : ElasticScale) (A : S0)
    (D : Gradient) : Tensor :=
  (energyDensity a ε A D) • (1 : Tensor) - gradientGram D

theorem elasticStress_classicalGradient (a : BulkCoefficients) (ε : ElasticScale)
    (Q : Point → S0) (x : Point) :
    elasticStress a ε (Q x) (ClassicalGradient Q x) = stressTensor a ε Q x := by
  ext i j
  by_cases h : i = j
  · simp [elasticStress, stressTensor, gradientGram, ClassicalGradient, h]
    rfl
  · simp [elasticStress, stressTensor, gradientGram, ClassicalGradient, h]

/-- The spatial quadratic form of an ambient matrix. -/
@[expose] def tensorQuadratic (T : Tensor) (v : Point) : ℝ :=
  ∑ i, ∑ j, v i * v j * T i j

theorem gradientGram_transpose (D : Gradient) : (gradientGram D)ᵀ = gradientGram D := by
  ext i j
  exact frobenius_comm (D j : Tensor) (D i : Tensor)

theorem gradientGram_trace (D : Gradient) : (gradientGram D).trace = gradientNormSq D := by
  simp only [Matrix.trace, Matrix.diag_apply, gradientGram, gradientNormSq]

theorem gradientGram_quadratic (D : Gradient) (v : Point) :
    tensorQuadratic (gradientGram D) v = ‖∑ i, v i • D i‖ ^ 2 := by
  rw [← frobeniusCoordinateEquiv.norm_map, ← real_inner_self_eq_norm_sq]
  simp only [tensorQuadratic, gradientGram, map_sum, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, frobeniusCoordinateEquiv_inner,
    mul_assoc]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [show frobeniusS0 (D i) (D j) = frobeniusS0 (D j) (D i) from
      frobenius_comm (D i : Tensor) (D j : Tensor)]

theorem gradientGram_norm_sq_le (D : Gradient) : ‖gradientGram D‖ ^ 2 ≤ gradientNormSq D ^ 2 := by
  rw [norm_sq_eq_frobenius, frobenius_eq_sum, gradientNormSq_eq_sum_norm_sq, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  change frobeniusS0 (D i) (D j) * frobeniusS0 (D i) (D j) ≤ ‖D i‖ ^ 2 * ‖D j‖ ^ 2
  have h := abs_real_inner_le_norm (frobeniusCoordinateEquiv (D i)) (frobeniusCoordinateEquiv (D j))
  rw [frobeniusCoordinateEquiv_inner, frobeniusCoordinateEquiv.norm_map,
    frobeniusCoordinateEquiv.norm_map] at h
  have hs := (sq_le_sq₀ (abs_nonneg (frobeniusS0 (D i) (D j)))
    (mul_nonneg (norm_nonneg (D i)) (norm_nonneg (D j)))).2 h
  rw [sq_abs, mul_pow] at hs
  simpa only [pow_two] using hs

theorem elasticStress_transpose (a : BulkCoefficients) (ε : ElasticScale) (A : S0) (D : Gradient) :
    (elasticStress a ε A D)ᵀ = elasticStress a ε A D := by
  simp [elasticStress, Matrix.transpose_sub, Matrix.transpose_smul, gradientGram_transpose]

theorem elasticStress_trace (a : BulkCoefficients) (ε : ElasticScale) (A : S0) (D : Gradient) :
    (elasticStress a ε A D).trace = 3 * energyDensity a ε A D - gradientNormSq D := by
  simp only [elasticStress, Matrix.trace_sub, Matrix.trace_smul, gradientGram_trace, smul_eq_mul]
  have h : (1 : Tensor).trace = 3 := by simp
  rw [h, mul_comm (energyDensity a ε A D) 3]

theorem elasticStress_quadratic (a : BulkCoefficients) (ε : ElasticScale) (A : S0) (D : Gradient)
    (v : Point) :
    tensorQuadratic (elasticStress a ε A D) v =
      energyDensity a ε A D * ‖v‖ ^ 2 - ‖∑ i, v i • D i‖ ^ 2 := by
  rw [← gradientGram_quadratic, EuclideanSpace.real_norm_sq_eq]
  simp only [tensorQuadratic, elasticStress, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum, pow_two]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem elasticStress_norm_sq (a : BulkCoefficients) (ε : ElasticScale) (A : S0) (D : Gradient) :
    ‖elasticStress a ε A D‖ ^ 2 = 3 * energyDensity a ε A D ^ 2 -
      2 * energyDensity a ε A D * gradientNormSq D + ‖gradientGram D‖ ^ 2 := by
  rw [norm_sq_eq_frobenius, frobenius, elasticStress_transpose, norm_sq_eq_frobenius, frobenius,
    gradientGram_transpose]
  have h : (1 : Tensor).trace = 3 := by simp
  simp only [elasticStress, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one, Matrix.trace_sub, Matrix.trace_smul, h, gradientGram_trace, smul_eq_mul]
  ring

/-- The symmetric stress obeys the exact trace and directional lower or
upper bounds, and has Frobenius norm at most twice the energy density. -/
theorem elasticStress_bounds (a : BulkCoefficients) (ε : ElasticScale) (A : S0) (D : Gradient) :
    (elasticStress a ε A D)ᵀ = elasticStress a ε A D ∧
    energyDensity a ε A D ≤ (elasticStress a ε A D).trace ∧
    ‖elasticStress a ε A D‖ ≤ 2 * energyDensity a ε A D ∧
    ∀ v : Point, tensorQuadratic (elasticStress a ε A D) v ≤ energyDensity a ε A D * ‖v‖ ^ 2 := by
  let e := energyDensity a ε A D
  let g := gradientNormSq D
  have hg : 0 ≤ g := by
    rw [show g = gradientNormSq D from rfl, gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he : g ≤ 2 * e := by
    have hp := mul_nonneg (sq_nonneg ((ε : ℝ)⁻¹)) (bulkPotential_nonneg a A)
    simp only [e, g, energyDensity]
    linarith only [hp]
  have he0 : 0 ≤ e := by linarith only [he, hg]
  refine ⟨elasticStress_transpose a ε A D, ?_, ?_, ?_⟩
  · rw [elasticStress_trace]
    linarith only [he]
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) he0)).1
    rw [elasticStress_norm_sq]
    have hng := mul_nonpos_of_nonneg_of_nonpos hg (sub_nonpos.mpr he)
    nlinarith only [gradientGram_norm_sq_le D, hng, sq_nonneg e]
  · intro v
    rw [elasticStress_quadratic]
    exact sub_le_self _ (sq_nonneg _)

/-- Stress with exactly the logarithmic normalization of the energy measure. -/
noncomputable def normalizedElasticStress (a : BulkCoefficients) (ε : ElasticScale)
    (A : S0) (D : Gradient) : Tensor :=
  (Real.log (1 / (ε : ℝ)))⁻¹ • elasticStress a ε A D

theorem normalizedElasticStress_bounds (a : BulkCoefficients) (ε : ElasticScale) (A : S0)
    (D : Gradient) :
    let T := normalizedElasticStress a ε A D
    let e := energyDensity a ε A D / Real.log (1 / (ε : ℝ))
    Tᵀ = T ∧ e ≤ T.trace ∧ ‖T‖ ≤ 2 * e ∧
      ∀ v : Point, tensorQuadratic T v ≤ e * ‖v‖ ^ 2 := by
  let L := Real.log (1 / (ε : ℝ))
  have hL : 0 ≤ L⁻¹ := inv_nonneg.mpr (log_inv_scale_pos ε).le
  obtain ⟨hSym, hTrace, hNorm, hQuad⟩ := elasticStress_bounds a ε A D
  dsimp only [normalizedElasticStress]
  change (L⁻¹ • elasticStress a ε A D)ᵀ = _ ∧ _
  refine ⟨by rw [Matrix.transpose_smul, hSym], ?_, ?_, ?_⟩
  · rw [Matrix.trace_smul, smul_eq_mul, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hTrace hL
  · rw [norm_smul, Real.norm_of_nonneg hL, div_eq_inv_mul, mul_left_comm 2]
    exact mul_le_mul_of_nonneg_left hNorm hL
  · intro v
    have hhom (k : ℝ) (T : Tensor) : tensorQuadratic (k • T) v = k * tensorQuadratic T v := by
      simp only [tensorQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hhom]
    change L⁻¹ * tensorQuadratic (elasticStress a ε A D) v ≤
      (energyDensity a ε A D / L) * ‖v‖ ^ 2
    rw [div_eq_inv_mul _ L, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hQuad v) hL

end Thesis

end
