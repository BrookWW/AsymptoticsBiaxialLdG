module

public import Thesis.Foundation.ModifiedSpectralGap

/-! Frobenius splitting of the derivative of the modified gap and vacuum projection. -/

@[expose] public section

noncomputable section

open Filter Set Topology
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace Thesis

private def eigenbasisColumns (A : S0) : Tensor := fun i j => orderedEigenbasis A j i

private theorem eigenbasisColumns_transpose_mul (A : S0) :
    (eigenbasisColumns A)ᵀ * eigenbasisColumns A = 1 := by
  ext i j
  have h := orthonormal_iff_ite.mp (orderedEigenbasis A).orthonormal j i
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct] at h
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, eigenbasisColumns, Matrix.one_apply, eq_comm] using h

private theorem eigenbasisColumns_mul_transpose (A : S0) :
    eigenbasisColumns A * (eigenbasisColumns A)ᵀ = 1 :=
  mul_eq_one_comm.mp (eigenbasisColumns_transpose_mul A)

private def tensorInEigenbasis (A : S0) (H : Tensor) : Tensor :=
  (eigenbasisColumns A)ᵀ * H * eigenbasisColumns A

private theorem tensorInEigenbasis_add (A : S0) (B C : Tensor) :
    tensorInEigenbasis A (B + C) = tensorInEigenbasis A B + tensorInEigenbasis A C := by
  simp only [tensorInEigenbasis, Matrix.mul_add, Matrix.add_mul]

private theorem tensorInEigenbasis_sub (A : S0) (B C : Tensor) :
    tensorInEigenbasis A (B - C) = tensorInEigenbasis A B - tensorInEigenbasis A C := by
  simp only [tensorInEigenbasis, Matrix.mul_sub, Matrix.sub_mul]

private theorem tensorInEigenbasis_smul (A : S0) (c : ℝ) (B : Tensor) :
    tensorInEigenbasis A (c • B) = c • tensorInEigenbasis A B := by
  simp only [tensorInEigenbasis, Matrix.mul_smul, Matrix.smul_mul]

private theorem tensorInEigenbasis_mul (A : S0) (B C : Tensor) :
    tensorInEigenbasis A (B * C) = tensorInEigenbasis A B * tensorInEigenbasis A C := by
  let V := eigenbasisColumns A
  have hV : V * Vᵀ = 1 := eigenbasisColumns_mul_transpose A
  change Vᵀ * (B * C) * V = (Vᵀ * B * V) * (Vᵀ * C * V)
  rw [show (Vᵀ * B * V) * (Vᵀ * C * V) = Vᵀ * B * (V * Vᵀ) * C * V by
    simp only [mul_assoc], hV, mul_one]
  simp only [mul_assoc]

private theorem tensorInEigenbasis_norm_sq (A : S0) (H : Tensor) :
    ‖tensorInEigenbasis A H‖ ^ 2 = ‖H‖ ^ 2 := by
  let V := eigenbasisColumns A
  have hV : V * Vᵀ = 1 := eigenbasisColumns_mul_transpose A
  rw [norm_sq_eq_frobenius, norm_sq_eq_frobenius, frobenius, frobenius]
  change Matrix.trace ((Vᵀ * H * V)ᵀ * (Vᵀ * H * V)) = Matrix.trace (Hᵀ * H)
  rw [show (Vᵀ * H * V)ᵀ * (Vᵀ * H * V) = (Vᵀ * Hᵀ * (V * Vᵀ) * H) * V by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, mul_assoc], hV, mul_one,
    Matrix.trace_mul_comm (Vᵀ * Hᵀ * H) V]
  rw [show V * (Vᵀ * Hᵀ * H) = V * Vᵀ * (Hᵀ * H) by simp only [mul_assoc], hV, one_mul]

private def eigenMask (i j : Fin 3) : ℝ := if j = i then 1 else 0

private def eigenMaskMatrix (i : Fin 3) : Tensor := Matrix.diagonal (eigenMask i)

private theorem eigenbasisColumns_mul_eigenvalues (A : S0) :
    (A : Tensor) * eigenbasisColumns A = eigenbasisColumns A * Matrix.diagonal (orderedEigenvalue A) := by
  ext i j
  rw [Matrix.mul_diagonal]
  have h := congrFun (orderedEigenbasis_mulVec A j) i
  change ((A : Tensor) * eigenbasisColumns A) i j = orderedEigenvalue A j * eigenbasisColumns A i j at h
  simpa only [mul_comm] using h

private theorem tensorInEigenbasis_tensor (A : S0) :
    tensorInEigenbasis A (A : Tensor) = Matrix.diagonal (orderedEigenvalue A) := by
  rw [tensorInEigenbasis, mul_assoc, eigenbasisColumns_mul_eigenvalues, ← mul_assoc,
    eigenbasisColumns_transpose_mul, one_mul]

private theorem eigenlineProjector_mulVec_eigenbasis (A : S0) (i j : Fin 3) :
    orderedEigenlineProjector A i *ᵥ (orderedEigenbasis A j).ofLp =
      eigenMask i j • (orderedEigenbasis A j).ofLp := by
  rw [orderedEigenlineProjector, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  have horth := orthonormal_iff_ite.mp (orderedEigenbasis A).orthonormal j i
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at horth
  change ((orderedEigenbasis A i).ofLp ⬝ᵥ (orderedEigenbasis A j).ofLp) •
      (orderedEigenbasis A i).ofLp = _
  rw [horth]
  by_cases h : j = i
  · subst j
    simp [eigenMask]
  · simp [eigenMask, h]

private theorem tensorInEigenbasis_eigenlineProjector (A : S0) (i : Fin 3) :
    tensorInEigenbasis A (orderedEigenlineProjector A i) = eigenMaskMatrix i := by
  have hmul : orderedEigenlineProjector A i * eigenbasisColumns A =
      eigenbasisColumns A * eigenMaskMatrix i := by
    ext j k
    rw [eigenMaskMatrix, Matrix.mul_diagonal]
    have h := congrFun (eigenlineProjector_mulVec_eigenbasis A i k) j
    change (orderedEigenlineProjector A i * eigenbasisColumns A) j k =
      eigenMask i k * eigenbasisColumns A j k at h
    simpa only [mul_comm] using h
  rw [tensorInEigenbasis, mul_assoc, hmul, ← mul_assoc, eigenbasisColumns_transpose_mul, one_mul]

private theorem tensor_mul_eigenlineProjector (A : S0) (i : Fin 3) :
    (A : Tensor) * orderedEigenlineProjector A i = orderedEigenvalue A i • orderedEigenlineProjector A i := by
  rw [orderedEigenlineProjector, Matrix.mul_vecMulVec]
  change Matrix.vecMulVec ((A : Tensor) *ᵥ (orderedEigenbasis A i).ofLp)
    (orderedEigenbasis A i).ofLp = _
  rw [orderedEigenbasis_mulVec]
  ext j k
  simp [Matrix.vecMulVec_apply, mul_assoc]

private theorem eigenlineProjector_mul_tensor (A : S0) (i : Fin 3) :
    orderedEigenlineProjector A i * (A : Tensor) = orderedEigenvalue A i • orderedEigenlineProjector A i := by
  have H := congrArg Matrix.transpose (tensor_mul_eigenlineProjector A i)
  simpa only [Matrix.transpose_mul, Matrix.transpose_smul, orderedEigenlineProjector,
    Matrix.transpose_vecMulVec, A.transpose_eq] using H

private theorem eigenlineProjector_idempotent (A : S0) (i : Fin 3) :
    orderedEigenlineProjector A i * orderedEigenlineProjector A i =
      orderedEigenlineProjector A i := by
  have h := orthonormal_iff_ite.mp (orderedEigenbasis A).orthonormal i i
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, if_pos rfl] at h
  simp only [orderedEigenlineProjector, Matrix.vecMulVec_mul_vecMulVec, show
    ((fun j => orderedEigenbasis A i j) ⬝ᵥ fun j => orderedEigenbasis A i j) = 1 from h, one_smul]

private theorem fin3_cases_num (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> decide

private theorem orderedEigenvalue_ne_of_simple {A : S0} (hA : A ∈ simpleSpectrumLocus)
    {j k : Fin 3} (hjk : j ≠ k) : orderedEigenvalue A j ≠ orderedEigenvalue A k := by
  have h₁ : orderedEigenvalue A 1 < orderedEigenvalue A 0 := hA.1
  have h₂ : orderedEigenvalue A 2 < orderedEigenvalue A 1 := hA.2
  intro he
  rcases fin3_cases_num j with rfl | rfl | rfl <;>
    rcases fin3_cases_num k with rfl | rfl | rfl <;> try contradiction
  all_goals linarith only [h₁, h₂, he]

private theorem contDiffAt_eigenlineProjector_of_simple (A : S0) (hA : A ∈ simpleSpectrumLocus) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun B => orderedEigenlineProjector B i) A := by
  have hOn : ContDiffOn ℝ ∞ (fun B => orderedEigenlineProjector B i) simpleSpectrumLocus :=
    (contDiffOn_orderedEigenlineProjector i).mono fun B hB j hj => orderedEigenvalue_ne_of_simple hB hj
  exact (hOn A hA).contDiffAt (isOpen_simpleSpectrumLocus.mem_nhds hA)

private theorem eigenprojector_derivative_equations (A : S0) (hA : A ∈ simpleSpectrumLocus)
    (H : S0) (i : Fin 3) :
    let P := orderedEigenlineProjector A i
    let dP := fderiv ℝ (fun B => orderedEigenlineProjector B i) A H
    let dl := fderiv ℝ (fun B => orderedEigenvalue B i) A H
    ((H : Tensor) * P + (A : Tensor) * dP = dl • P + orderedEigenvalue A i • dP) ∧
    ((H : Tensor) * P + (A : Tensor) * dP = dP * (A : Tensor) + P * (H : Tensor)) ∧
      (dP * P + P * dP = dP) := by
  intro P dP dl
  let C (t : ℝ) := A + t • H
  have hC : HasDerivAt C H 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add A
    change HasDerivAt C ((1 : ℝ) • H) 0 at h
    rwa [one_smul] at h
  have hC₀ : C 0 = A := by simp [C]
  have hAt : simpleSpectrumLocus ∈ 𝓝 A := isOpen_simpleSpectrumLocus.mem_nhds hA
  have hEigenSmooth : ContDiffAt ℝ ∞ (fun B => orderedEigenvalue B i) A :=
    (contDiffOn_orderedEigenvalue i A hA).contDiffAt hAt
  have hPsmooth : ContDiffAt ℝ ∞ (fun B => orderedEigenlineProjector B i) A :=
    contDiffAt_eigenlineProjector_of_simple A hA i
  have hEigenF : HasFDerivAt (fun B => orderedEigenvalue B i)
      (fderiv ℝ (fun B => orderedEigenvalue B i) A) A :=
    (hEigenSmooth.differentiableAt (by decide)).hasFDerivAt
  have hPF : HasFDerivAt (fun B => orderedEigenlineProjector B i)
      (fderiv ℝ (fun B => orderedEigenlineProjector B i) A) A :=
    (hPsmooth.differentiableAt (by decide)).hasFDerivAt
  have hEigen : HasDerivAt (fun t => orderedEigenvalue (C t) i) dl 0 :=
    hEigenF.comp_hasDerivAt_of_eq (f := C) 0 hC hC₀.symm
  have hP : HasDerivAt (fun t => orderedEigenlineProjector (C t) i) dP 0 :=
    hPF.comp_hasDerivAt_of_eq (f := C) 0 hC hC₀.symm
  have hsubtype : HasFDerivAt (⇑symmetricTraceless.subtypeL) symmetricTraceless.subtypeL A :=
    symmetricTraceless.subtypeL.hasFDerivAt
  have hTensor : HasDerivAt (fun t => (C t : Tensor)) (H : Tensor) 0 :=
    hsubtype.comp_hasDerivAt_of_eq (f := C) (l := ⇑symmetricTraceless.subtypeL)
      (l' := symmetricTraceless.subtypeL) 0 hC hC₀.symm
  have hAP := hTensor.fun_mul hP
  have hPA := hP.fun_mul hTensor
  have hEigenP := hEigen.smul hP
  have hEigenP' : HasDerivAt (fun t => (C t : Tensor) * orderedEigenlineProjector (C t) i) _ 0 :=
    hEigenP.congr_of_eventuallyEq (Eventually.of_forall fun t => tensor_mul_eigenlineProjector (C t) i)
  have hPA' : HasDerivAt (fun t => (C t : Tensor) * orderedEigenlineProjector (C t) i) _ 0 :=
    hPA.congr_of_eventuallyEq (Eventually.of_forall fun t =>
      (tensor_mul_eigenlineProjector (C t) i).trans (eigenlineProjector_mul_tensor (C t) i).symm)
  have hPP := hP.fun_mul hP
  have hP' : HasDerivAt (fun t => orderedEigenlineProjector (C t) i *
      orderedEigenlineProjector (C t) i) dP 0 :=
    hP.congr_of_eventuallyEq (Eventually.of_forall fun t => eigenlineProjector_idempotent (C t) i)
  exact ⟨by simpa only [hC₀, add_comm] using hAP.unique hEigenP',
    by simpa only [hC₀] using hAP.unique hPA', by simpa only [hC₀] using hPP.unique hP'⟩

private theorem eigenprojector_derivative_coordinates (A : S0) (hA : A ∈ simpleSpectrumLocus)
    (H : S0) (i : Fin 3) :
    let B := tensorInEigenbasis A (H : Tensor)
    let P := tensorInEigenbasis A (fderiv ℝ (fun U => orderedEigenlineProjector U i) A H)
    (fderiv ℝ (fun U => orderedEigenvalue U i) A H = B i i) ∧
    (∀ j, P j j = 0) ∧
    (∀ j k, (orderedEigenvalue A j - orderedEigenvalue A k) * P j k =
      (eigenMask i j - eigenMask i k) * B j k) := by
  intro B P
  obtain ⟨hEig, hComm, hId⟩ := eigenprojector_derivative_equations A hA H i
  have hBasisEig := congrArg (tensorInEigenbasis A) hEig
  have hBasisComm := congrArg (tensorInEigenbasis A) hComm
  have hBasisId := congrArg (tensorInEigenbasis A) hId
  simp only [tensorInEigenbasis_add, tensorInEigenbasis_mul, tensorInEigenbasis_smul,
    tensorInEigenbasis_tensor, tensorInEigenbasis_eigenlineProjector] at hBasisEig hBasisComm hBasisId
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (fun T : Tensor => T i i) hBasisEig
    simp only [Matrix.add_apply, eigenMaskMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq, eigenMask, if_true, mul_one] at h
    change fderiv ℝ (fun U => orderedEigenvalue U i) A H = tensorInEigenbasis A (H : Tensor) i i
    linarith only [h]
  · intro j
    have h := congrArg (fun T : Tensor => T j j) hBasisId
    simp only [Matrix.add_apply, eigenMaskMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    change tensorInEigenbasis A (fderiv ℝ (fun U => orderedEigenlineProjector U i) A H) j j = 0
    by_cases hj : j = i
    · simp only [eigenMask, if_pos hj, mul_one, one_mul] at h
      linarith only [h]
    · simp only [eigenMask, if_neg hj, mul_zero, zero_mul, zero_add] at h
      exact h.symm
  · intro j k
    have h := congrArg (fun T : Tensor => T j k) hBasisComm
    simp only [Matrix.add_apply, eigenMaskMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    change (orderedEigenvalue A j - orderedEigenvalue A k) *
        tensorInEigenbasis A (fderiv ℝ (fun U => orderedEigenlineProjector U i) A H) j k =
      (eigenMask i j - eigenMask i k) * tensorInEigenbasis A (H : Tensor) j k
    linarith only [h]

private def eigenSign (i : Fin 3) : ℝ := eigenMask 0 i - eigenMask 2 i

private theorem projection_derivative_coord (a : BulkCoefficients) (A : S0)
    (hA : A ∈ simpleSpectrumLocus) (H : S0) :
    let W := tensorInEigenbasis A
      (fderiv ℝ (fun B => ((spectralVacuumPoint a B).val : Tensor)) A H)
    let B := tensorInEigenbasis A (H : Tensor)
    (∀ j, W j j = 0) ∧
      ∀ j k, (orderedEigenvalue A j - orderedEigenvalue A k) * W j k =
        vacuumRadius a * (eigenSign j - eigenSign k) * B j k := by
  intro W B
  let P (i : Fin 3) := tensorInEigenbasis A (fderiv ℝ (fun U => orderedEigenlineProjector U i) A H)
  have hP₀ (i : Fin 3) : HasFDerivAt (fun B => orderedEigenlineProjector B i)
      (fderiv ℝ (fun B => orderedEigenlineProjector B i) A) A :=
    ((contDiffAt_eigenlineProjector_of_simple A hA i).differentiableAt (by decide)).hasFDerivAt
  have hproj := ((hP₀ 0).sub (hP₀ 2)).const_smul (vacuumRadius a)
  have hproj' : HasFDerivAt (fun B => ((spectralVacuumPoint a B).val : Tensor)) _ A :=
    hproj.congr_of_eventuallyEq (Eventually.of_forall (spectralVacuumPoint_coe_eq_projectors a))
  have hv := congrArg (fun L : S0 →L[ℝ] Tensor => L H) hproj'.fderiv
  change fderiv ℝ (fun B => ((spectralVacuumPoint a B).val : Tensor)) A H =
    vacuumRadius a • (fderiv ℝ (fun B => orderedEigenlineProjector B 0) A H -
      fderiv ℝ (fun B => orderedEigenlineProjector B 2) A H) at hv
  have hv' : W = vacuumRadius a • (P 0 - P 2) := by
    change tensorInEigenbasis A
      (fderiv ℝ (fun B => ((spectralVacuumPoint a B).val : Tensor)) A H) = _
    rw [show fderiv ℝ (fun B => ((spectralVacuumPoint a B).val : Tensor)) A H = _ from hv,
      tensorInEigenbasis_smul, tensorInEigenbasis_sub]
  obtain ⟨_, hz₀, hc₀⟩ := eigenprojector_derivative_coordinates A hA H 0
  obtain ⟨_, hz₂, hc₂⟩ := eigenprojector_derivative_coordinates A hA H 2
  refine ⟨?_, ?_⟩
  · intro j
    rw [hv', Matrix.smul_apply, Matrix.sub_apply, show P 0 j j = 0 from hz₀ j,
      show P 2 j j = 0 from hz₂ j, sub_self, smul_zero]
  · intro j k
    have h₀ : (orderedEigenvalue A j - orderedEigenvalue A k) * P 0 j k =
        (eigenMask 0 j - eigenMask 0 k) * B j k := hc₀ j k
    have h₂ : (orderedEigenvalue A j - orderedEigenvalue A k) * P 2 j k =
        (eigenMask 2 j - eigenMask 2 k) * B j k := hc₂ j k
    rw [hv', Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    unfold eigenSign
    calc
      _ = vacuumRadius a * ((orderedEigenvalue A j - orderedEigenvalue A k) * P 0 j k -
          (orderedEigenvalue A j - orderedEigenvalue A k) * P 2 j k) := by ring
      _ = _ := by rw [h₀, h₂]; ring

private theorem eigenSign_gap_comparison (A : S0) (j k : Fin 3) :
    min (orderedEigenvalue A 0 - orderedEigenvalue A 1)
        (orderedEigenvalue A 1 - orderedEigenvalue A 2) * |eigenSign j - eigenSign k| ≤
      |orderedEigenvalue A j - orderedEigenvalue A k| := by
  have hL := min_le_left (orderedEigenvalue A 0 - orderedEigenvalue A 1)
    (orderedEigenvalue A 1 - orderedEigenvalue A 2)
  have hR := min_le_right (orderedEigenvalue A 0 - orderedEigenvalue A 1)
    (orderedEigenvalue A 1 - orderedEigenvalue A 2)
  have s₀ : eigenSign 0 = 1 := by norm_num [eigenSign, eigenMask, Fin.ext_iff]
  have s₁ : eigenSign 1 = 0 := by norm_num [eigenSign, eigenMask, Fin.ext_iff]
  have s₂ : eigenSign 2 = -1 := by norm_num [eigenSign, eigenMask, Fin.ext_iff]
  rcases fin3_cases_num j with rfl | rfl | rfl
  · rcases fin3_cases_num k with rfl | rfl | rfl
    · simp only [sub_self, abs_zero, mul_zero, le_refl]
    · rw [s₀, s₁, sub_zero, abs_one, mul_one]
      exact hL.trans (le_abs_self _)
    · rw [s₀, s₂, show |(1 : ℝ) - (-1)| = 2 by norm_num]
      linarith only [hL, hR, le_abs_self (orderedEigenvalue A 0 - orderedEigenvalue A 2)]
  · rcases fin3_cases_num k with rfl | rfl | rfl
    · rw [s₁, s₀, zero_sub, abs_neg, abs_one, mul_one, abs_sub_comm]
      exact hL.trans (le_abs_self _)
    · simp only [sub_self, abs_zero, mul_zero, le_refl]
    · rw [s₁, s₂, zero_sub, neg_neg, abs_one, mul_one]
      exact hR.trans (le_abs_self _)
  · rcases fin3_cases_num k with rfl | rfl | rfl
    · rw [s₂, s₀, show |(-1 : ℝ) - 1| = 2 by norm_num, abs_sub_comm]
      linarith only [hL, hR, le_abs_self (orderedEigenvalue A 0 - orderedEigenvalue A 2)]
    · rw [s₂, s₁, sub_zero, abs_neg, abs_one, mul_one, abs_sub_comm]
      exact hR.trans (le_abs_self _)
    · simp only [sub_self, abs_zero, mul_zero, le_refl]

private theorem spectral_projection_entry_bound (a : BulkCoefficients) (τ : GapSmoothingParameter)
    (A : S0) (hA : A ∈ simpleSpectrumLocus) (H : S0) (j k : Fin 3) (hjk : j ≠ k) :
    let W := tensorInEigenbasis A (fderiv ℝ (fun B => ((spectralVacuumPoint a B).val : Tensor)) A H)
    modifiedSpectralGap a τ A * |W j k| ≤ |tensorInEigenbasis A (H : Tensor) j k| := by
  intro W
  let m := modifiedSpectralGap a τ A
  let R := vacuumRadius a
  let B := tensorInEigenbasis A (H : Tensor)
  let d := |orderedEigenvalue A j - orderedEigenvalue A k|
  have hm : 0 ≤ m := ((modifiedSpectralGap_pos_iff a τ A).2 hA).le
  have hR : 0 < R := vacuumRadius_pos a
  have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr (orderedEigenvalue_ne_of_simple hA hjk))
  have hComp := mul_le_mul_of_nonneg_right (modifiedSpectralGap_comparison a τ A).2 hR.le
  have hmGap : m * R ≤ min (orderedEigenvalue A 0 - orderedEigenvalue A 1)
      (orderedEigenvalue A 1 - orderedEigenvalue A 2) := by
    unfold normalizedSpectralGap at hComp
    calc
      _ ≤ (R⁻¹ * min (orderedEigenvalue A 0 - orderedEigenvalue A 1)
        (orderedEigenvalue A 1 - orderedEigenvalue A 2)) * R := hComp
      _ = _ := by field_simp [hR.ne']
  have hGap := (mul_le_mul_of_nonneg_right hmGap (abs_nonneg _)).trans (eigenSign_gap_comparison A j k)
  obtain ⟨_, hW⟩ := projection_derivative_coord a A hA H
  have hEq : d * |W j k| = R * |eigenSign j - eigenSign k| * |B j k| := by
    have h := congrArg abs (hW j k)
    simpa only [d, abs_mul, abs_of_pos (vacuumRadius_pos a)] using h
  change m * |W j k| ≤ |B j k|
  apply (mul_le_mul_iff_right₀ hd).mp
  calc
    _ = m * (d * |W j k|) := by ring
    _ = (m * R * |eigenSign j - eigenSign k|) * |B j k| := by rw [hEq]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hGap (abs_nonneg _)

private theorem scalarDerivative_along_tensor_line {f : S0 → ℝ} {A H : S0}
    (h : HasFDerivAt f (fderiv ℝ f A) A) :
    HasDerivAt (fun t : ℝ => f (A + t • H)) (fderiv ℝ f A H) 0 := by
  let C (t : ℝ) := A + t • H
  have hC : HasDerivAt C H 0 := by
    have D := ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add A
    change HasDerivAt C ((1 : ℝ) • H) 0 at D
    rwa [one_smul] at D
  have hC₀ : A = C 0 := by simp [C]
  exact h.comp_hasDerivAt_of_eq (f := C) 0 hC hC₀

private theorem modifiedGap_derivative_formula (a : BulkCoefficients) (τ : GapSmoothingParameter)
    (A : S0) (hA : A ∈ simpleSpectrumLocus) (H : S0) :
    let s := orderedEigenvalue A 0 - orderedEigenvalue A 2
    let t := orderedEigenvalue A 1 - orderedEigenvalue A 2
    let r := t / s
    let ds := fderiv ℝ (fun B => orderedEigenvalue B 0) A H -
      fderiv ℝ (fun B => orderedEigenvalue B 2) A H
    let dt := fderiv ℝ (fun B => orderedEigenvalue B 1) A H -
      fderiv ℝ (fun B => orderedEigenvalue B 2) A H
    fderiv ℝ (modifiedSpectralGap a τ) A H =
      (vacuumRadius a)⁻¹ * ((spectralGapProfile τ r - r * deriv (spectralGapProfile τ) r) * ds +
        deriv (spectralGapProfile τ) r * dt) := by
  intro s t r ds dt
  let C (w : ℝ) := A + w • H
  let sC (w : ℝ) := orderedEigenvalue (C w) 0 - orderedEigenvalue (C w) 2
  let tC (w : ℝ) := orderedEigenvalue (C w) 1 - orderedEigenvalue (C w) 2
  have hC₀ : C 0 = A := by simp [C]
  have hs₀ : sC 0 = s := by simp only [sC, hC₀, s]
  have ht₀ : tC 0 = t := by simp only [tC, hC₀, t]
  have hs : 0 < s := sub_pos.mpr (hA.2.trans hA.1)
  have hAt := isOpen_simpleSpectrumLocus.mem_nhds hA
  have hEig (i : Fin 3) : HasDerivAt (fun w => orderedEigenvalue (C w) i)
      (fderiv ℝ (fun B => orderedEigenvalue B i) A H) 0 :=
    scalarDerivative_along_tensor_line
      ((((contDiffOn_orderedEigenvalue i A hA).contDiffAt hAt).differentiableAt (by decide)).hasFDerivAt)
  have hS : HasDerivAt sC ds 0 := (hEig 0).sub (hEig 2)
  have hT : HasDerivAt tC dt 0 := (hEig 1).sub (hEig 2)
  have hratio : HasDerivAt (fun w => tC w / sC w) ((dt * s - t * ds) / s ^ 2) 0 := by
    have hu := hT.div hS (show sC 0 ≠ 0 by rw [hs₀]; exact hs.ne')
    change HasDerivAt (fun w => tC w / sC w) ((dt * sC 0 - tC 0 * ds) / sC 0 ^ 2) 0 at hu
    rwa [hs₀, ht₀] at hu
  have hprofAt : HasDerivAt (spectralGapProfile τ) (deriv (spectralGapProfile τ) r) (tC 0 / sC 0) := by
    rw [hs₀, ht₀]
    exact ((contDiff_spectralGapProfile τ).differentiable (by decide) r).hasDerivAt
  have hprof : HasDerivAt (fun w => spectralGapProfile τ (tC w / sC w))
      (deriv (spectralGapProfile τ) r * ((dt * s - t * ds) / s ^ 2)) 0 :=
    hprofAt.comp (h := fun w => tC w / sC w) (h₂ := spectralGapProfile τ) 0 hratio
  have hForm := (hS.fun_mul hprof).const_mul ((vacuumRadius a)⁻¹)
  have hCcts : Continuous C := by dsimp only [C]; fun_prop
  have hCN : ∀ᶠ w in 𝓝 (0 : ℝ), C w ∈ simpleSpectrumLocus :=
    hCcts.continuousAt (hC₀.symm ▸ hAt)
  have hForm' : HasDerivAt (fun w => modifiedSpectralGap a τ (C w)) _ 0 :=
    hForm.congr_of_eventuallyEq (hCN.mono fun w hw => by
      have hne : C w ≠ 0 := by
        intro hz
        have hpos := (modifiedSpectralGap_pos_iff a τ (C w)).2 hw
        simp [hz, modifiedSpectralGap] at hpos
      change modifiedSpectralGap a τ (C w) =
        (vacuumRadius a)⁻¹ * (sC w * spectralGapProfile τ (tC w / sC w))
      rw [modifiedSpectralGap, if_neg hne])
  have hActual := scalarDerivative_along_tensor_line (A := A) (H := H)
    ((((contDiffOn_modifiedSpectralGap a τ A hA).contDiffAt hAt).differentiableAt (by decide)).hasFDerivAt)
  calc
    _ = (vacuumRadius a)⁻¹ *
        (ds * spectralGapProfile τ r + s * (deriv (spectralGapProfile τ) r * ((dt * s - t * ds) / s ^ 2))) := by
      simpa only [hs₀, ht₀] using hActual.unique hForm'
    _ = _ := by
      dsimp only [r]
      field_simp [hs.ne']
      ring

private def diagonalFrobeniusEnergy (H : Tensor) : ℝ := ∑ i : Fin 3, (H i i) ^ 2

private theorem gap_derivative_sq_bound_diagonal (a : BulkCoefficients) (τ : GapSmoothingParameter)
    (A : S0) (hA : A ∈ simpleSpectrumLocus) (H : S0) :
    vacuumRadius a ^ 2 / 18 * (fderiv ℝ (modifiedSpectralGap a τ) A H) ^ 2 ≤
      diagonalFrobeniusEnergy (tensorInEigenbasis A (H : Tensor)) := by
  let B := tensorInEigenbasis A (H : Tensor)
  let D := diagonalFrobeniusEnergy B
  let s := orderedEigenvalue A 0 - orderedEigenvalue A 2
  let t := orderedEigenvalue A 1 - orderedEigenvalue A 2
  let r := t / s
  let ds := B 0 0 - B 2 2
  let dt := B 1 1 - B 2 2
  let c := spectralGapProfile τ r
  let v := deriv (spectralGapProfile τ) r
  let u := c - r * v
  have hs : 0 < s := sub_pos.mpr (hA.2.trans hA.1)
  have hr : r ∈ Icc 0 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hA.2.le) hs.le, (div_le_one hs).2 (by dsimp [s, t]; linarith [hA.1])⟩
  have hEq : fderiv ℝ (modifiedSpectralGap a τ) A H = (vacuumRadius a)⁻¹ * (u * ds + v * dt) := by
    have h₀ := (eigenprojector_derivative_coordinates A hA H 0).1
    have h₁ := (eigenprojector_derivative_coordinates A hA H 1).1
    have h₂ := (eigenprojector_derivative_coordinates A hA H 2).1
    have he := modifiedGap_derivative_formula a τ A hA H
    dsimp only at he
    rw [h₀, h₁, h₂] at he
    exact he
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hDS : ds ^ 2 ≤ 2 * D := by
    dsimp only [ds, D, diagonalFrobeniusEnergy]
    rw [Fin.sum_univ_three]
    nlinarith only [sq_nonneg (B 0 0 + B 2 2), sq_nonneg (B 1 1)]
  have hDT : dt ^ 2 ≤ 2 * D := by
    dsimp only [dt, D, diagonalFrobeniusEnergy]
    rw [Fin.sum_univ_three]
    nlinarith only [sq_nonneg (B 1 1 + B 2 2), sq_nonneg (B 0 0)]
  obtain ⟨hlo, hhi⟩ := spectralGapProfile_comparison τ hr
  have hc₀ : 0 ≤ c := (mul_nonneg (spectralGapSmoothingFactor_pos τ).le
    (le_min hr.1 (sub_nonneg.mpr hr.2))).trans hlo
  have hc : c ≤ 1 / 2 := by
    have h₁ := hhi.trans (min_le_left _ _)
    have h₂ := hhi.trans (min_le_right _ _)
    exact (show spectralGapProfile τ r ≤ 1 / 2 by linarith only [h₁, h₂])
  have hv : |v| ≤ 1 := abs_deriv_spectralGapProfile_le τ r
  have hu : |u| ≤ (3 / 2 : ℝ) := by
    have hrv : r * |v| ≤ 1 := (mul_le_mul_of_nonneg_right hr.2 (abs_nonneg _)).trans
      (by rwa [one_mul])
    calc
      _ ≤ |c| + |r * v| := abs_sub _ _
      _ = c + r * |v| := by rw [abs_of_nonneg hc₀, abs_mul, abs_of_nonneg hr.1]
      _ ≤ (1 / 2 : ℝ) + 1 := add_le_add hc hrv
      _ = _ := by norm_num
  have huSq : u ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg u) (by norm_num)).2 hu
  have hvSq : v ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg v) zero_le_one).2 hv
  have hBound : (u * ds + v * dt) ^ 2 ≤ 18 * D := by
    calc
      _ ≤ 2 * (u ^ 2 * ds ^ 2 + v ^ 2 * dt ^ 2) := by nlinarith only [sq_nonneg (u * ds - v * dt)]
      _ ≤ 2 * ((3 / 2 : ℝ) ^ 2 * (2 * D) + 1 * (2 * D)) := by
        gcongr
      _ ≤ _ := by nlinarith only [hD]
  change vacuumRadius a ^ 2 / 18 * (fderiv ℝ (modifiedSpectralGap a τ) A H) ^ 2 ≤ D
  calc
    _ = (u * ds + v * dt) ^ 2 / 18 := by
      rw [hEq]
      field_simp [(vacuumRadius_pos a).ne']
    _ ≤ _ := by linarith only [hBound]

private def offDiagonalFrobeniusEnergy (H : Tensor) : ℝ :=
  ∑ i : Fin 3, ∑ j ∈ Finset.univ.erase i, (H i j) ^ 2

private theorem frobenius_norm_sq_split (H : Tensor) :
    ‖H‖ ^ 2 = diagonalFrobeniusEnergy H + offDiagonalFrobeniusEnergy H := by
  rw [norm_sq_eq_frobenius, frobenius_eq_sum, diagonalFrobeniusEnergy, offDiagonalFrobeniusEnergy,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [pow_two]
  exact (Finset.add_sum_erase (Finset.univ : Finset (Fin 3))
    (fun j => H i j * H i j) (Finset.mem_univ i)).symm

private theorem projected_derivative_sq_bound_offDiagonal (a : BulkCoefficients)
    (τ : GapSmoothingParameter) (A : S0) (hA : A ∈ simpleSpectrumLocus) (H : S0) :
    (modifiedSpectralGap a τ A) ^ 2 *
      ‖fderiv ℝ (fun B => ((spectralVacuumPoint a B).val : Tensor)) A H‖ ^ 2 ≤
      offDiagonalFrobeniusEnergy (tensorInEigenbasis A (H : Tensor)) := by
  let W := tensorInEigenbasis A (fderiv ℝ (fun B => ((spectralVacuumPoint a B).val : Tensor)) A H)
  let B := tensorInEigenbasis A (H : Tensor)
  let m := modifiedSpectralGap a τ A
  have hm : 0 ≤ m := ((modifiedSpectralGap_pos_iff a τ A).2 hA).le
  have hDiag : ∀ j, W j j = 0 := (projection_derivative_coord a A hA H).1
  have hD0 : diagonalFrobeniusEnergy W = 0 := by
    simp [diagonalFrobeniusEnergy, hDiag]
  change m ^ 2 * ‖fderiv ℝ (fun C => ((spectralVacuumPoint a C).val : Tensor)) A H‖ ^ 2 ≤ _
  rw [← tensorInEigenbasis_norm_sq A, show tensorInEigenbasis A
    (fderiv ℝ (fun C => ((spectralVacuumPoint a C).val : Tensor)) A H) = W from rfl,
    frobenius_norm_sq_split, hD0, zero_add]
  change m ^ 2 * offDiagonalFrobeniusEnergy W ≤ offDiagonalFrobeniusEnergy B
  unfold offDiagonalFrobeniusEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hne : i ≠ j := (Finset.mem_erase.mp hj).1.symm
  have he : m * |W i j| ≤ |B i j| := spectral_projection_entry_bound a τ A hA H i j hne
  have hsq := (sq_le_sq₀ (mul_nonneg hm (abs_nonneg _)) (abs_nonneg _)).2 he
  simpa only [mul_pow, sq_abs] using hsq

/-- The actual Frobenius derivative split. After division by two its first
coefficient is the manuscript's r_*²/36 and the projection keeps its gap-squared weight. -/
theorem modifiedGap_spectralProjection_derivative_split (a : BulkCoefficients)
    (τ : GapSmoothingParameter) (A : S0) (hA : A ∈ simpleSpectrumLocus) (H : S0) :
    vacuumRadius a ^ 2 / 18 * (fderiv ℝ (modifiedSpectralGap a τ) A H) ^ 2 +
      (modifiedSpectralGap a τ A) ^ 2 *
        ‖fderiv ℝ (fun B => ((spectralVacuumPoint a B).val : Tensor)) A H‖ ^ 2 ≤ ‖H‖ ^ 2 := by
  calc
    _ ≤ diagonalFrobeniusEnergy (tensorInEigenbasis A (H : Tensor)) +
        offDiagonalFrobeniusEnergy (tensorInEigenbasis A (H : Tensor)) :=
      add_le_add (gap_derivative_sq_bound_diagonal a τ A hA H)
        (projected_derivative_sq_bound_offDiagonal a τ A hA H)
    _ = _ := (frobenius_norm_sq_split _).symm.trans (tensorInEigenbasis_norm_sq _ _)

end Thesis
