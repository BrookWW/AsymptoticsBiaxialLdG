module

public import Thesis.Upstream.AmbientGradientHilbert
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Euclidean changes of weak gradient columns and the elliptic metric coefficient. -/

public section

noncomputable section

open Function HarmonicMaps
open scoped BigOperators ContDiff ENNReal RealInnerProductSpace InnerProduct

namespace Thesis

private def ambientGradientProjection {n q : ℕ} (i : Fin n) :
    AmbientGradientHilbert n q →L[ℝ] Ambient q :=
  (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => Ambient q)).toContinuousLinearMap

private def ambientGradientInsertion {n q : ℕ} (i : Fin n) :
    Ambient q →L[ℝ] AmbientGradientHilbert n q :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => Ambient q)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin n => Ambient q) i)

private def euclideanOperatorEntry {n : ℕ} (i j : Fin n) :
    (Domain n →L[ℝ] Domain n) →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp (ContinuousLinearMap.apply ℝ (Domain n) (EuclideanSpace.single i 1))

/-- Precomposition by a Euclidean derivative acts on the actual finite
gradient coordinates as a continuous linear function of that derivative. -/
def ambientGradientPrecompose (n q : ℕ) :
    (Domain n →L[ℝ] Domain n) →L[ℝ] (AmbientGradientHilbert n q →L[ℝ] AmbientGradientHilbert n q) :=
  ∑ i : Fin n, ∑ j : Fin n, (euclideanOperatorEntry i j).smulRight
    ((ambientGradientInsertion i).comp (ambientGradientProjection j))

theorem ambientGradientPrecompose_apply {n q : ℕ} (K : Domain n →L[ℝ] Domain n)
    (D : AmbientGradientHilbert n q) (i : Fin n) :
    ambientGradientPrecompose n q K D i =
      ∑ j : Fin n, (K (EuclideanSpace.single i 1)) j • D j := by
  change ambientGradientProjection i (ambientGradientPrecompose n q K D) = _
  simp only [ambientGradientPrecompose,sum_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,ContinuousLinearMap.comp_apply,map_sum,map_smul,euclideanOperatorEntry]
  have h (k j : Fin n) :
      ambientGradientProjection i (ambientGradientInsertion k (ambientGradientProjection j D)) =
        if i = k then D j else 0 := by
    simp only [ambientGradientProjection,ambientGradientInsertion,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,PiLp.continuousLinearEquiv_apply,PiLp.continuousLinearEquiv_symm_apply,
      ContinuousLinearMap.proj_apply,ContinuousLinearMap.single_apply,Pi.single_apply]
  simp_rw [h,smul_ite,smul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rfl

private def ambientLinearMapOfGradient {n q : ℕ} (D : AmbientGradientHilbert n q) :
    Domain n →L[ℝ] Ambient q :=
  ∑ j : Fin n, (EuclideanSpace.proj j).smulRight (D j)

private theorem ambientLinearMapOfGradient_apply {n q : ℕ} (D : AmbientGradientHilbert n q)
    (y : Domain n) :
    ambientLinearMapOfGradient D y = ∑ j : Fin n, y j • D j := by
  simp only [ambientLinearMapOfGradient,sum_apply,ContinuousLinearMap.smulRight_apply]
  rfl

private theorem ambientLinearMapOfGradient_axis {n q : ℕ} (D : AmbientGradientHilbert n q)
    (j : Fin n) : ambientLinearMapOfGradient D (EuclideanSpace.single j 1) = D j := by
  rw [ambientLinearMapOfGradient_apply]
  simp only [PiLp.single_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true]

private theorem ambientLinearMapOfGradient_precompose {n q : ℕ}
    (K : Domain n →L[ℝ] Domain n) (D : AmbientGradientHilbert n q) :
    ambientLinearMapOfGradient (ambientGradientPrecompose n q K D) = (ambientLinearMapOfGradient D).comp K := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : (∑ j : Fin n, v j • EuclideanSpace.single j 1) = v := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  calc
    _ = ∑ j : Fin n, v j • ambientLinearMapOfGradient D (K (EuclideanSpace.single j 1)) := by
      rw [ambientLinearMapOfGradient_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [ambientGradientPrecompose_apply,ambientLinearMapOfGradient_apply]
    _ = ambientLinearMapOfGradient D (K (∑ j : Fin n, v j • EuclideanSpace.single j 1)) := by
      simp only [map_sum,map_smul]
    _ = _ := by rw [hv]; rfl

theorem ambientGradientPrecompose_comp {n q : ℕ}
    (A B : Domain n →L[ℝ] Domain n) (D : AmbientGradientHilbert n q) :
    ambientGradientPrecompose n q A (ambientGradientPrecompose n q B D) =
      ambientGradientPrecompose n q (B.comp A) D := by
  apply PiLp.ext
  intro j
  rw [← ambientLinearMapOfGradient_axis _ j, ← ambientLinearMapOfGradient_axis _ j]
  rw [ambientLinearMapOfGradient_precompose,ambientLinearMapOfGradient_precompose,
    ambientLinearMapOfGradient_precompose,ContinuousLinearMap.comp_assoc]

theorem ambientGradientPrecompose_id {n q : ℕ} (D : AmbientGradientHilbert n q) :
    ambientGradientPrecompose n q (ContinuousLinearMap.id ℝ (Domain n)) D = D := by
  apply PiLp.ext
  intro i
  rw [ambientGradientPrecompose_apply,ContinuousLinearMap.id_apply]
  simp only [PiLp.single_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem ambientGradientPrecompose_derivative_columns {n q : ℕ}
    (K : Domain n →L[ℝ] Domain n) (A : Domain n →L[ℝ] Ambient q) :
    ambientGradientPrecompose n q K (packAmbientGradient (fun j => A (EuclideanSpace.single j 1))) =
      packAmbientGradient (fun j => A (K (EuclideanSpace.single j 1))) := by
  apply PiLp.ext
  intro i
  rw [ambientGradientPrecompose_apply]
  simp only [packAmbientGradient_apply,← map_smul]
  rw [← map_sum]
  have h : (∑ j : Fin n, (K (EuclideanSpace.single i 1)) j • EuclideanSpace.single j 1) =
      K (EuclideanSpace.single i 1) := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (K (EuclideanSpace.single i 1))
  rw [h]

/-- The derivative of the inverse chart is the inverse of the original
derivative at the actual corresponding point. -/
theorem fderiv_symm_comp_fderiv_homeomorph {n : ℕ} (F : Domain n ≃ₜ Domain n)
    (hF : ContDiff ℝ ∞ (F : Domain n → Domain n))
    (hInv : ContDiff ℝ ∞ (F.symm : Domain n → Domain n)) (x : Domain n) :
    (fderiv ℝ F.symm (F x)).comp (fderiv ℝ F x) = ContinuousLinearMap.id ℝ (Domain n) := by
  have h := ((hInv.differentiable (by simp) (F x)).hasFDerivAt.comp x
    ((hF.differentiable (by simp) x).hasFDerivAt)).fderiv
  have he : (F.symm : Domain n → Domain n) ∘ F = id := funext F.symm_apply_apply
  rw [he,fderiv_id] at h
  exact h.symm

/-- The elliptic coefficient after changing Euclidean coordinates, in the
Hilbert product of the original displayed gradient columns. -/
def ambientGradientMetric (n q : ℕ) (K : Domain n →L[ℝ] Domain n) :
    AmbientGradientHilbert n q →L[ℝ] AmbientGradientHilbert n q :=
  (ambientGradientPrecompose n q K).adjoint.comp (ambientGradientPrecompose n q K)

theorem inner_ambientGradientMetric {n q : ℕ} (K : Domain n →L[ℝ] Domain n)
    (X Y : AmbientGradientHilbert n q) :
    inner ℝ (ambientGradientMetric n q K X) Y =
      inner ℝ (ambientGradientPrecompose n q K X) (ambientGradientPrecompose n q K Y) :=
  (ambientGradientPrecompose n q K).adjoint_inner_left Y (ambientGradientPrecompose n q K X)

theorem contDiff_ambientGradientMetric {n q : ℕ} {p : ℕ∞ω} :
    ContDiff ℝ p (ambientGradientMetric n q) := by
  letI := (inferInstance : FiniteDimensional ℝ (AmbientGradientHilbert n q))
  let D := AmbientGradientHilbert n q
  let L := ambientGradientPrecompose n q
  let Adj : (D →L[ℝ] D) →L[ℝ] (D →L[ℝ] D) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := D) (F := D)).toContinuousLinearEquiv.toContinuousLinearMap
  exact (ContinuousLinearMap.compL ℝ D D D).isBoundedBilinearMap.contDiff.comp
    ((Adj.contDiff.comp L.contDiff).prodMk L.contDiff)

/-- The entries of the scalar elliptic matrix in the actual coordinates. -/
@[expose] def ambientGradientMetricEntry {n : ℕ} (K : Domain n →L[ℝ] Domain n)
    (i j : Fin n) : ℝ :=
  ∑ k : Fin n, (K (EuclideanSpace.single k 1)) i * (K (EuclideanSpace.single k 1)) j

theorem contDiff_ambientGradientMetricEntry {n : ℕ} (i j : Fin n) {p : ℕ∞ω} :
    ContDiff ℝ p (fun K : Domain n →L[ℝ] Domain n => ambientGradientMetricEntry K i j) := by
  apply ContDiff.sum
  intro k _
  exact (euclideanOperatorEntry k i).contDiff.mul (euclideanOperatorEntry k j).contDiff

theorem ambientGradientMetric_apply_column {n q : ℕ} (K : Domain n →L[ℝ] Domain n)
    (G : AmbientGradientHilbert n q) (i : Fin n) :
    ambientGradientMetric n q K G i = ∑ j : Fin n, ambientGradientMetricEntry K i j • G j := by
  apply ext_inner_right ℝ
  intro y
  let Y := ambientGradientInsertion i y
  have hY (j : Fin n) : Y j = if j = i then y else 0 := by
    simp only [Y,ambientGradientInsertion,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      PiLp.continuousLinearEquiv_symm_apply,ContinuousLinearMap.single_apply,Pi.single_apply]
  have hKY (j : Fin n) : ambientGradientPrecompose n q K Y j =
      (K (EuclideanSpace.single j 1)) i • y := by
    rw [ambientGradientPrecompose_apply]
    simp only [hY,smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have hL : inner ℝ (ambientGradientMetric n q K G) Y = inner ℝ (ambientGradientMetric n q K G i) y := by
    rw [PiLp.inner_apply]
    have he (j : Fin n) : inner ℝ (ambientGradientMetric n q K G j) (Y j) =
        if j = i then inner ℝ (ambientGradientMetric n q K G j) y else 0 := by
      by_cases hj : j = i <;> simp only [hY,hj,if_true,if_false,inner_zero_right]
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [← hL,inner_ambientGradientMetric,PiLp.inner_apply]
  simp only [hKY,ambientGradientPrecompose_apply,real_inner_smul_right,sum_inner,real_inner_smul_left,
    ambientGradientMetricEntry,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem ambientGradientMetricEntry_diag_pos_of_rightInverse {n : ℕ}
    (K L : Domain n →L[ℝ] Domain n) (hKL : K.comp L = ContinuousLinearMap.id ℝ (Domain n))
    (i : Fin n) : 0 < ambientGradientMetricEntry K i i := by
  have hEq : (K (L (EuclideanSpace.single i 1))) i = 1 := by
    have h := congrArg (fun A : Domain n →L[ℝ] Domain n => A (EuclideanSpace.single i 1) i) hKL
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,PiLp.single_apply,
      if_true] using h
  let y := L (EuclideanSpace.single i 1)
  have hBasis : (∑ j : Fin n, y j • EuclideanSpace.single j 1) = y := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr y
  have hpos : ∃ k : Fin n, (K (EuclideanSpace.single k 1)) i ≠ 0 := by
    by_contra! h
    have hz : (K y) i = 0 := by
      change (EuclideanSpace.proj i) (K y) = 0
      rw [← hBasis,map_sum,map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [map_smul,map_smul,show (EuclideanSpace.proj i) (K (EuclideanSpace.single j 1)) = 0 from h j,
        smul_zero]
    exact zero_ne_one (hz.symm.trans hEq)
  obtain ⟨k,hk⟩ := hpos
  simp only [ambientGradientMetricEntry,← pow_two]
  exact (sq_pos_of_ne_zero hk).trans_le
    (Finset.single_le_sum (f := fun j : Fin n => ((K (EuclideanSpace.single j 1)) i)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ k))

end Thesis
