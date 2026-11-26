module

public import Thesis.Definitions

/-! The Frobenius metric and the trace-free symmetric projection on the tensor space. -/

@[expose] public section

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius
open MeasureTheory Set

namespace Thesis

theorem frobenius_eq_sum (A B : Tensor) :
    frobenius A B = ∑ i, ∑ j, A i j * B i j := by
  simp only [frobenius, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  exact Finset.sum_comm

theorem norm_sq_eq_frobenius (A : Tensor) : ‖A‖ ^ 2 = frobenius A A := by
  have hnorm := Matrix.frobenius_norm_def A
  simp_rw [← Real.sqrt_eq_rpow, Real.rpow_two, Real.norm_eq_abs, sq_abs] at hnorm
  have h : 0 ≤ (∑ i, ∑ j, (A i j) ^ 2) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hnorm, Real.sq_sqrt h, frobenius_eq_sum]
  simp only [pow_two]

theorem norm_sq_eq_frobeniusS0 (A : S0) : ‖A‖ ^ 2 = frobeniusS0 A A :=
  norm_sq_eq_frobenius (A : Tensor)

theorem frobenius_comm (A B : Tensor) : frobenius A B = frobenius B A := by
  simp only [frobenius_eq_sum, mul_comm]

theorem frobenius_add_left (A B C : Tensor) :
    frobenius (A + B) C = frobenius A C + frobenius B C := by
  simp only [frobenius, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add]

theorem frobenius_add_right (A B C : Tensor) :
    frobenius A (B + C) = frobenius A B + frobenius A C := by
  simp only [frobenius, Matrix.mul_add, Matrix.trace_add]

theorem traceFreeSymmetricPart_of_S0 (A : S0) :
    traceFreeSymmetricPart (A : Tensor) = A := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • ((A : Tensor) + (A : Tensor)ᵀ) -
    ((A : Tensor).trace / 3) • (1 : Tensor) = (A : Tensor)
  rw [A.transpose_eq, A.trace_eq_zero, zero_div, zero_smul, sub_zero, ← two_smul ℝ,
    smul_smul]
  norm_num

theorem frobenius_traceFreeSymmetricPart (A : Tensor) (B : S0) :
    frobenius (traceFreeSymmetricPart A) B = frobenius A B := by
  have hs : Matrix.trace (A * (B : Tensor)) = Matrix.trace (Aᵀ * (B : Tensor)) := by
    calc
      _ = Matrix.trace ((A * (B : Tensor))ᵀ) := (Matrix.trace_transpose _).symm
      _ = Matrix.trace ((B : Tensor) * Aᵀ) := by rw [Matrix.transpose_mul, B.transpose_eq]
      _ = _ := Matrix.trace_mul_comm _ _
  change frobenius
    ((1 / 2 : ℝ) • (A + Aᵀ) - (A.trace / 3) • (1 : Tensor)) (B : Tensor) = _
  simp [frobenius, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_add,
    Matrix.sub_mul, Matrix.add_mul, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_smul, B.trace_eq_zero, hs, smul_eq_mul]
  ring

theorem frobenius_sub_traceFreeSymmetricPart (A : Tensor) (B : S0) :
    frobenius (A - (traceFreeSymmetricPart A : Tensor)) (B : Tensor) = 0 := by
  rw [show frobenius (A - (traceFreeSymmetricPart A : Tensor)) (B : Tensor) =
      frobenius A (B : Tensor) - frobenius (traceFreeSymmetricPart A : Tensor) (B : Tensor) by
    simp [frobenius, Matrix.transpose_sub, Matrix.sub_mul, Matrix.trace_sub]]
  rw [frobenius_traceFreeSymmetricPart, sub_self]

/-- The orthogonal projection with codomain restricted to the tensor subspace. -/
noncomputable def traceFreeSymmetricPartLinear : Tensor →ₗ[ℝ] S0 where
  toFun := traceFreeSymmetricPart
  map_add' A B := by
    apply Subtype.ext
    ext i j
    simp [traceFreeSymmetricPart, Matrix.trace_add, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    ring
  map_smul' c A := by
    apply Subtype.ext
    ext i j
    simp [traceFreeSymmetricPart, Matrix.trace_smul, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    ring

@[simp] theorem traceFreeSymmetricPartLinear_apply (A : Tensor) :
    traceFreeSymmetricPartLinear A = traceFreeSymmetricPart A := rfl

theorem traceFreeSymmetricPartLinear_comp_subtype :
    traceFreeSymmetricPartLinear.comp symmetricTraceless.subtype = LinearMap.id :=
  LinearMap.ext fun A => traceFreeSymmetricPart_of_S0 A

theorem traceFreeSymmetricPart_eq_zero_iff (A : Tensor) :
    traceFreeSymmetricPart A = 0 ↔ ∀ B : S0, frobenius A (B : Tensor) = 0 := by
  constructor
  · intro h B
    rw [← frobenius_traceFreeSymmetricPart A B, h]
    simp [frobenius]
  · intro h
    have hnorm : ‖traceFreeSymmetricPart A‖ ^ 2 = 0 := by
      rw [norm_sq_eq_frobeniusS0]
      exact (frobenius_traceFreeSymmetricPart A (traceFreeSymmetricPart A)).trans (h _)
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hnorm)

theorem frobenius_projection_norm_sq (A : Tensor) :
    ‖A‖ ^ 2 = ‖traceFreeSymmetricPart A‖ ^ 2 +
      ‖A - (traceFreeSymmetricPart A : Tensor)‖ ^ 2 := by
  let P := traceFreeSymmetricPart A
  have horth : frobenius (A - (P : Tensor)) (P : Tensor) = 0 :=
    frobenius_sub_traceFreeSymmetricPart A P
  have horth' : frobenius (P : Tensor) (A - (P : Tensor)) = 0 :=
    (frobenius_comm (P : Tensor) (A - (P : Tensor))).trans horth
  have hdecomp : A = (A - (P : Tensor)) + (P : Tensor) := (sub_add_cancel _ _).symm
  calc
    ‖A‖ ^ 2 = ‖(A - (P : Tensor)) + (P : Tensor)‖ ^ 2 := congrArg (fun B : Tensor => ‖B‖ ^ 2) hdecomp
    _ = _ := by
      change ‖(A - (P : Tensor)) + (P : Tensor)‖ ^ 2 =
        ‖(P : Tensor)‖ ^ 2 + ‖A - (P : Tensor)‖ ^ 2
      simp only [norm_sq_eq_frobenius, frobenius_add_left, frobenius_add_right,
        horth, horth', zero_add, add_zero]
      exact add_comm (frobenius (A - (P : Tensor)) (A - (P : Tensor))) (frobenius P P)

theorem norm_traceFreeSymmetricPart_le (A : Tensor) : ‖traceFreeSymmetricPart A‖ ≤ ‖A‖ := by
  nlinarith only [frobenius_projection_norm_sq A,
    sq_nonneg ‖A - (traceFreeSymmetricPart A : Tensor)‖,
    norm_nonneg A, norm_nonneg (traceFreeSymmetricPart A)]

/-- The continuous form of the Frobenius projection. -/
noncomputable def traceFreeSymmetricPartCLM : Tensor →L[ℝ] S0 :=
  traceFreeSymmetricPartLinear.mkContinuous 1 fun A => by
    simpa only [one_mul, traceFreeSymmetricPartLinear_apply] using norm_traceFreeSymmetricPart_le A

@[simp] theorem traceFreeSymmetricPartCLM_apply (A : Tensor) :
    traceFreeSymmetricPartCLM A = traceFreeSymmetricPart A := rfl

theorem traceFreeSymmetricPartCLM_comp_subtypeL :
    traceFreeSymmetricPartCLM.comp symmetricTraceless.subtypeL = ContinuousLinearMap.id ℝ S0 :=
  ContinuousLinearMap.ext fun A => traceFreeSymmetricPart_of_S0 A

/-- Pointwise projection preserves every test taking values in the tensor subspace. -/
theorem traceFreeSymmetricPart_test {X : Type*} (P : X → S0) :
    (fun x => traceFreeSymmetricPart (P x : Tensor)) = P :=
  funext fun x => traceFreeSymmetricPart_of_S0 (P x)

theorem S0.apply_comm (A : S0) (i j : Fin 3) : (A : Tensor) i j = (A : Tensor) j i :=
  (congrArg (fun M : Tensor => M i j) A.transpose_eq).symm

theorem S0.last_diagonal (A : S0) :
    (A : Tensor) 2 2 = -((A : Tensor) 0 0 + (A : Tensor) 1 1) := by
  have h := A.trace_eq_zero
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  change (A : Tensor) 0 0 + ((A : Tensor) 1 1 + (A : Tensor) 2 2) = 0 at h
  linarith

/-- Coordinates in the two diagonal and three symmetric off-diagonal unit tensors. -/
noncomputable def frobeniusCoordinates : S0 →ₗ[ℝ] EuclideanSpace ℝ (Fin 5) where
  toFun A := WithLp.toLp 2 ![
    Real.sqrt 2 / 2 * ((A : Tensor) 0 0 - (A : Tensor) 1 1),
    Real.sqrt 6 / 6 * ((A : Tensor) 0 0 + (A : Tensor) 1 1 - 2 * (A : Tensor) 2 2),
    Real.sqrt 2 * (A : Tensor) 0 1,
    Real.sqrt 2 * (A : Tensor) 0 2,
    Real.sqrt 2 * (A : Tensor) 1 2]
  map_add' A B := by
    ext i
    fin_cases i <;> simp [Matrix.add_apply] <;> ring
  map_smul' c A := by
    ext i
    fin_cases i <;> simp [Matrix.smul_apply, smul_eq_mul] <;> ring

/-- Reconstruct a tensor from its coefficients in the Frobenius basis. -/
noncomputable def s0OfCoordinates (x : EuclideanSpace ℝ (Fin 5)) : S0 :=
  let d := Real.sqrt 2 / 2 * x 0
  let t := Real.sqrt 6 / 6 * x 1
  let u := Real.sqrt 2 / 2 * x 2
  let v := Real.sqrt 2 / 2 * x 3
  let w := Real.sqrt 2 / 2 * x 4
  ⟨!![d + t, u, v; u, -d + t, w; v, w, -2 * t], by
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · simp [Matrix.trace, Fin.sum_univ_succ]
      ring⟩

theorem s0OfCoordinates_frobeniusCoordinates (A : S0) :
    s0OfCoordinates (frobeniusCoordinates A) = A := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s0OfCoordinates, frobeniusCoordinates, S0.last_diagonal,
      A.apply_comm 1 0, A.apply_comm 2 0, A.apply_comm 2 1] <;>
    ring_nf <;> norm_num [Real.sq_sqrt] <;> ring

theorem frobeniusCoordinates_s0OfCoordinates (x : EuclideanSpace ℝ (Fin 5)) :
    frobeniusCoordinates (s0OfCoordinates x) = x := by
  ext i
  fin_cases i <;> simp [frobeniusCoordinates, s0OfCoordinates] <;>
    ring_nf <;> norm_num [Real.sq_sqrt] <;> ring

theorem frobenius_s0OfCoordinates (x y : EuclideanSpace ℝ (Fin 5)) :
    frobeniusS0 (s0OfCoordinates x) (s0OfCoordinates y) = inner ℝ x y := by
  rw [frobeniusS0, frobenius_eq_sum, EuclideanSpace.inner_eq_star_dotProduct]
  simp [s0OfCoordinates, dotProduct, Fin.sum_univ_succ]
  ring_nf
  norm_num [Real.sq_sqrt]
  ring

theorem inner_frobeniusCoordinates (A B : S0) :
    inner ℝ (frobeniusCoordinates A) (frobeniusCoordinates B) = frobeniusS0 A B := by
  rw [← frobenius_s0OfCoordinates]
  simp only [s0OfCoordinates_frobeniusCoordinates]

/-- The Euclidean realization of the space of symmetric traceless tensors. -/
noncomputable def frobeniusCoordinateEquiv : S0 ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 5) where
  toLinearEquiv := { frobeniusCoordinates with
    invFun := s0OfCoordinates
    left_inv := s0OfCoordinates_frobeniusCoordinates
    right_inv := frobeniusCoordinates_s0OfCoordinates }
  norm_map' A := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖frobeniusCoordinates A‖ ^ 2 = ‖A‖ ^ 2
    rw [← real_inner_self_eq_norm_sq, inner_frobeniusCoordinates, norm_sq_eq_frobeniusS0]

@[simp] theorem frobeniusCoordinateEquiv_apply (A : S0) :
    frobeniusCoordinateEquiv A = frobeniusCoordinates A := rfl

@[simp] theorem frobeniusCoordinateEquiv_symm_apply (x : EuclideanSpace ℝ (Fin 5)) :
    frobeniusCoordinateEquiv.symm x = s0OfCoordinates x := rfl

theorem frobeniusCoordinateEquiv_inner (A B : S0) :
    inner ℝ (frobeniusCoordinateEquiv A) (frobeniusCoordinateEquiv B) = frobeniusS0 A B :=
  inner_frobeniusCoordinates A B

/-- The two trace-free diagonal and three symmetric off-diagonal unit tensors form a basis. -/
noncomputable def frobeniusBasis : Module.Basis (Fin 5) ℝ S0 :=
  (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis.map frobeniusCoordinateEquiv.symm.toLinearEquiv

theorem frobeniusBasis_apply (i : Fin 5) :
    frobeniusBasis i = frobeniusCoordinateEquiv.symm (EuclideanSpace.single i 1) := by
  simp [frobeniusBasis, EuclideanSpace.basisFun_apply]

theorem frobeniusS0_frobeniusBasis (i j : Fin 5) :
    frobeniusS0 (frobeniusBasis i) (frobeniusBasis j) = if i = j then 1 else 0 := by
  rw [← frobeniusCoordinateEquiv_inner, frobeniusBasis_apply, frobeniusBasis_apply]
  simp only [LinearIsometryEquiv.apply_symm_apply]
  simp [EuclideanSpace.inner_single_left]

theorem frobeniusCoordinateEquiv_integral_comp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → S0) :
    (∫ x, frobeniusCoordinateEquiv (f x) ∂μ) = frobeniusCoordinateEquiv (∫ x, f x ∂μ) :=
  frobeniusCoordinateEquiv.toLinearIsometry.integral_comp_comm f

theorem isWeakGradient_iff_frobeniusCoordinates (U : Set Point) (u : Point → S0)
    (D : Point → Gradient) :
    IsWeakGradient U u D ↔
      ∀ (j : Fin 3) (φ : Point → ℝ), SmoothTest U φ →
        (∫ x in U, coordDeriv j φ x • frobeniusCoordinateEquiv (u x)) =
          -(∫ x in U, φ x • frobeniusCoordinateEquiv (D x j)) := by
  constructor
  · intro h j φ hφ
    simp_rw [← map_smul frobeniusCoordinateEquiv, frobeniusCoordinateEquiv_integral_comp,
      ← map_neg frobeniusCoordinateEquiv]
    rw [h j φ hφ]
  · intro h j φ hφ
    apply frobeniusCoordinateEquiv.injective
    have he := h j φ hφ
    simp_rw [← map_smul frobeniusCoordinateEquiv, frobeniusCoordinateEquiv_integral_comp,
      ← map_neg frobeniusCoordinateEquiv] at he
    exact he

theorem frobeniusCoordinateEquiv_memLp_iff {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ENNReal) (f : X → S0) :
    MemLp (fun x => frobeniusCoordinateEquiv (f x)) p μ ↔ MemLp f p μ := by
  constructor
  · intro h
    have hc := h.continuousLinearMap_comp
      frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
    change MemLp (fun x => frobeniusCoordinateEquiv.symm (frobeniusCoordinateEquiv (f x))) p μ at hc
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hc
  · intro h
    exact h.continuousLinearMap_comp frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap

theorem h1Deviation_frobeniusCoordinates (U : Set Point) (u v : Point → S0)
    (D G : Point → Gradient) :
    h1Deviation U u v D G =
      ∫⁻ x in U, ENNReal.ofReal (‖frobeniusCoordinateEquiv (u x) -
        frobeniusCoordinateEquiv (v x)‖ ^ 2 +
        ∑ j, ‖frobeniusCoordinateEquiv (D x j) - frobeniusCoordinateEquiv (G x j)‖ ^ 2) := by
  simp_rw [h1Deviation, ← map_sub frobeniusCoordinateEquiv,
    LinearIsometryEquiv.norm_map]

theorem gradientNormSq_eq_sum_norm_sq (D : Gradient) :
    gradientNormSq D = ∑ j, ‖D j‖ ^ 2 := by
  simp_rw [gradientNormSq, norm_sq_eq_frobeniusS0]

end Thesis
end
end
