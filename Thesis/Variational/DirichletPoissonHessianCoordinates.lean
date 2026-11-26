module

public import Thesis.External.DirichletPoissonHolder
import Thesis.Variational.BoundaryPoissonEstimate
import Thesis.Foundation.Frobenius

/-! Transfer of the scalar Dirichlet Hessian bound through the fixed Frobenius coordinates. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

/-- The scalar Dirichlet Hessian estimate in the same domain and norm convention. -/
@[expose] def ScalarGlobalDirichletPoissonSecondDerivativeLp : Prop :=
  ∀ (U : Set Point), IsSmoothDomain U → ∀ p : ℝ, 1 < p →
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Point → ℝ), ContDiffOn ℝ 2 v (closure U) →
      EqOn v (fun _ => 0) (frontier U) → ∀ M F : ℝ, 0 ≤ M → 0 ≤ F →
      (∀ x ∈ U, ‖v x‖ ≤ M) → (∀ x ∈ U, ‖laplacian v x‖ ≤ F) →
      MemLp (fun x => ‖iteratedFDeriv ℝ 2 v x‖) (ENNReal.ofReal p) (volume.restrict U) ∧
        eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 v x‖) (ENNReal.ofReal p) (volume.restrict U) ≤
          ENNReal.ofReal (C*(M+F))

private def scalarFrobeniusCoordinate (i : Fin 5) : S0 →L[ℝ] ℝ :=
  (EuclideanSpace.proj i).comp frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap

private theorem norm_scalarFrobeniusCoordinate_le (i : Fin 5) (x : S0) :
    ‖scalarFrobeniusCoordinate i x‖ ≤ ‖x‖ := by
  change ‖frobeniusCoordinateEquiv x i‖ ≤ ‖x‖
  rw [← frobeniusCoordinateEquiv.norm_map x]
  exact PiLp.norm_apply_le (frobeniusCoordinateEquiv x) i

private theorem norm_le_sum_scalarFrobeniusCoordinate (x : S0) :
    ‖x‖ ≤ ∑ i : Fin 5, ‖scalarFrobeniusCoordinate i x‖ := by
  let y := frobeniusCoordinateEquiv x
  have hY : (∑ i : Fin 5, y i • EuclideanSpace.single i 1) = y := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 5) ℝ).sum_repr y
  calc
    _ = ‖y‖ := (frobeniusCoordinateEquiv.norm_map x).symm
    _ = ‖∑ i : Fin 5, y i • EuclideanSpace.single i 1‖ := congrArg norm hY.symm
    _ ≤ ∑ i : Fin 5, ‖y i • EuclideanSpace.single i 1‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      change ‖y i • EuclideanSpace.single i (1:ℝ)‖ = ‖y i‖
      rw [norm_smul, show ‖(EuclideanSpace.single i (1:ℝ) : EuclideanSpace ℝ (Fin 5))‖ = 1 by simp,
        mul_one]

private theorem norm_tensorHessian_le_sum_scalarHessian {v : Point → S0} {x : Point}
    (hv : ContDiffAt ℝ 2 v x) :
    ‖iteratedFDeriv ℝ 2 v x‖ ≤ ∑ i : Fin 5, ‖iteratedFDeriv ℝ 2 (scalarFrobeniusCoordinate i ∘ v) x‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro m
  refine (norm_le_sum_scalarFrobeniusCoordinate _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have hE := DFunLike.congr_fun ((scalarFrobeniusCoordinate i).iteratedFDeriv_comp_left hv (i := 2) le_rfl) m
  change iteratedFDeriv ℝ 2 (scalarFrobeniusCoordinate i ∘ v) x m =
    scalarFrobeniusCoordinate i (iteratedFDeriv ℝ 2 v x m) at hE
  rw [← hE]
  exact (iteratedFDeriv ℝ 2 (scalarFrobeniusCoordinate i ∘ v) x).le_opNorm m

/-- The scalar quantitative estimate gives the original tensor proposition. -/
theorem globalDirichletPoissonSecondDerivativeLp_of_scalar
    (h : ScalarGlobalDirichletPoissonSecondDerivativeLp) : External.GlobalDirichletPoissonSecondDerivativeLp := by
  intro U hU p hp
  obtain ⟨C,hC,hBound⟩ := h U hU p hp
  refine ⟨5*C,mul_pos (by norm_num) hC,?_⟩
  intro v hv hz M F hM hF hV hLV
  let μ := (volume : Measure Point).restrict U
  let q := ENNReal.ofReal p
  let v₁ (i : Fin 5) := scalarFrobeniusCoordinate i ∘ v
  let H₁ (i : Fin 5) (x : Point) := ‖iteratedFDeriv ℝ 2 (v₁ i) x‖
  let H (x : Point) := ‖iteratedFDeriv ℝ 2 v x‖
  have hUO := hU.1.1
  have hvO : ContDiffOn ℝ 2 v U := hv.mono subset_closure
  have hq : 1 ≤ q := by
    change 1 ≤ ENNReal.ofReal p
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have h₁ (i : Fin 5) : MemLp (H₁ i) q μ ∧ eLpNorm (H₁ i) q μ ≤ ENNReal.ofReal (C*(M+F)) := by
    have hv₁ : ContDiffOn ℝ 2 (v₁ i) (closure U) :=
      (scalarFrobeniusCoordinate i).contDiff.comp_contDiffOn hv
    have hz₁ : EqOn (v₁ i) (fun _ => 0) (frontier U) := fun x hx => by
      change scalarFrobeniusCoordinate i (v x) = 0
      rw [hz hx,map_zero]
    have hRange : ∀ x ∈ U, ‖v₁ i x‖ ≤ M := fun x hx =>
      (norm_scalarFrobeniusCoordinate_le i (v x)).trans (hV x hx)
    have hLap : ∀ x ∈ U, ‖laplacian (v₁ i) x‖ ≤ F := by
      intro x hx
      have he : laplacian (v₁ i) x = scalarFrobeniusCoordinate i (laplacian v x) :=
        laplacian_compCLM hUO hvO hx (scalarFrobeniusCoordinate i)
      rw [he]
      exact (norm_scalarFrobeniusCoordinate_le i (laplacian v x)).trans (hLV x hx)
    exact hBound (v₁ i) hv₁ hz₁ M F hM hF hRange hLap
  have hHC : ContinuousOn H U :=
    ((hvO.continuousOn_iteratedFDerivWithin (m := 2) (by norm_num) hUO.uniqueDiffOn).congr
      (fun x hx => (iteratedFDerivWithin_of_isOpen 2 hUO hx).symm)).norm
  have hN : eLpNorm H q μ ≤ ENNReal.ofReal ((5*C)*(M+F)) := by
    have hE : eLpNorm H q μ ≤ eLpNorm (∑ i : Fin 5, H₁ i) q μ := by
      apply eLpNorm_mono_ae
      filter_upwards [ae_restrict_mem hUO.measurableSet] with x hx
      change ‖H x‖ ≤ ‖(∑ i : Fin 5, H₁ i) x‖
      rw [Finset.sum_apply,Real.norm_of_nonneg (norm_nonneg _),
        Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
      exact norm_tensorHessian_le_sum_scalarHessian ((hvO x hx).contDiffAt (hUO.mem_nhds hx))
    refine hE.trans ((eLpNorm_sum_le (fun i _ => (h₁ i).1.1) hq).trans ?_)
    refine (Finset.sum_le_sum fun i _ => (h₁ i).2).trans_eq ?_
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
    rw [mul_assoc, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5), ENNReal.ofReal_ofNat]
  exact ⟨⟨hHC.aestronglyMeasurable hUO.measurableSet,hN.trans_lt ENNReal.ofReal_lt_top⟩,hN⟩

end Thesis

end
