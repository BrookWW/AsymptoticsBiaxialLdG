module

public import Thesis.Variational.WeakCorrectionPairing
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Module.DoubleDual

/-! The actual weak Dirichlet adjoint on the frozen zero-trace graph. -/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.Frobenius

namespace Thesis

local instance dirichletAdjointDualNormed (U : Set Point) : NormedAddCommGroup (HMinusOne U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance dirichletAdjointDualSpace (U : Set Point) : NormedSpace ℝ (HMinusOne U) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

private abbrev CoordinateL2 (U : Set Point) :=
  Lp (EuclideanSpace ℝ (Fin 5)) 2 (volume.restrict U)

private def tensorL2Equiv (U : Set Point) : Lp S0 2 (volume.restrict U) ≃L[ℝ] CoordinateL2 U := by
  let e := frobeniusCoordinateEquiv.toContinuousLinearEquiv
  let A := e.toContinuousLinearMap.compLpL 2 (volume.restrict U)
  let B := e.symm.toContinuousLinearMap.compLpL 2 (volume.restrict U)
  refine ContinuousLinearEquiv.equivOfInverse A B ?_ ?_
  · intro f
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL e.symm.toContinuousLinearMap (A f),
      ContinuousLinearMap.coeFn_compLpL e.toContinuousLinearMap f] with x hB hA
    change B (A f) x = f x
    rw [hB,hA]
    exact e.symm_apply_apply _
  · intro g
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL e.toContinuousLinearMap (B g),
      ContinuousLinearMap.coeFn_compLpL e.symm.toContinuousLinearMap g] with x hA hB
    change A (B g) x = g x
    rw [hA,hB]
    exact e.apply_symm_apply _

private abbrev HilbertGraph (U : Set Point) :=
  WithLp 2 (CoordinateL2 U × PiLp 2 (fun _ : Fin 3 => CoordinateL2 U))

private def hilbertGraphEquiv (U : Set Point) : H1Graph U ≃L[ℝ] HilbertGraph U :=
  ((tensorL2Equiv U).prodCongr
    ((ContinuousLinearEquiv.piCongrRight (fun _ : Fin 3 => tensorL2Equiv U)).trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => CoordinateL2 U)).symm)).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ (CoordinateL2 U)
      (PiLp 2 (fun _ : Fin 3 => CoordinateL2 U))).symm

private theorem exists_evaluation_of_equiv_hilbert {B K : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (E : B ≃L[ℝ] K) (Λ : (B →L[ℝ] ℝ) →L[ℝ] ℝ) :
    ∃ w : B, ‖w‖ ≤ ‖Λ‖ ∧ ∀ v : B →L[ℝ] ℝ, Λ v = v w := by
  let R₀ := (InnerProductSpace.toDual ℝ K).toContinuousLinearEquiv.toContinuousLinearMap
  let R : K →L[ℝ] (K →L[ℝ] ℝ) :=
    { toFun := R₀
      map_add' := R₀.map_add
      map_smul' := fun c x => by simpa only [starRingEnd_apply, star_trivial, RingHom.id_apply] using R₀.map_smulₛₗ c x
      cont := R₀.continuous }
  let P₀ : (K →L[ℝ] ℝ) →ₗ[ℝ] (B →L[ℝ] ℝ) :=
    { toFun := fun L => L.comp E.toContinuousLinearMap
      map_add' := fun L₁ L₂ => ContinuousLinearMap.add_comp L₁ L₂ _
      map_smul' := fun c L => ContinuousLinearMap.smul_comp c L _ }
  have hP₀ (b : K →L[ℝ] ℝ) : ‖P₀ b‖ ≤ ‖E.toContinuousLinearMap‖ * ‖b‖ := by
    change ‖b.comp E.toContinuousLinearMap‖ ≤ ‖E.toContinuousLinearMap‖ * ‖b‖
    exact (ContinuousLinearMap.opNorm_comp_le b E.toContinuousLinearMap).trans_eq (mul_comm _ _)
  let P : (K →L[ℝ] ℝ) →L[ℝ] (B →L[ℝ] ℝ) :=
    ⟨P₀, AddMonoidHomClass.continuous_of_bound P₀ ‖E.toContinuousLinearMap‖ hP₀⟩
  let L : K →L[ℝ] ℝ := Λ.comp (P.comp R)
  let z : K := (InnerProductSpace.toDual ℝ K).symm L
  let w := E.symm z
  have hEval (v : (B →L[ℝ] ℝ)) : Λ v = v w := by
    let b : K →L[ℝ] ℝ := v.comp E.symm.toContinuousLinearMap
    let y : K := (InnerProductSpace.toDual ℝ K).symm b
    have hRy : R y = b := (InnerProductSpace.toDual ℝ K).apply_symm_apply b
    have hPy : P (R y) = v := by
      rw [hRy]
      apply ContinuousLinearMap.ext
      intro a
      change v (E.symm (E a)) = v a
      rw [E.symm_apply_apply]
    calc
      Λ v = L y := by
        change Λ v = Λ (P (R y))
        rw [hPy]
      _ = inner ℝ z y := InnerProductSpace.toDual_symm_apply.symm
      _ = inner ℝ y z := real_inner_comm _ _
      _ = b z := InnerProductSpace.toDual_symm_apply
      _ = v w := rfl
  refine ⟨w, NormedSpace.norm_le_dual_bound ℝ w (norm_nonneg Λ) (fun v => ?_), hEval⟩
  rw [← hEval]
  exact Λ.le_opNorm v

private theorem exists_H10_of_dual_functional (U : Set Point) (Λ : HMinusOne U →L[ℝ] ℝ) :
    ∃ w : H10 U, ‖w‖ ≤ ‖Λ‖ ∧ ∀ v : HMinusOne U, Λ v = v w := by
  let e := hilbertGraphEquiv U
  let K := (h10Submodule U).map e.toLinearMap
  let E : H10 U ≃L[ℝ] K := e.submoduleMap (h10Submodule U)
  have hClosed₀ : IsClosed (h10Submodule U : Set (H1Graph U)) := isClosed_closure
  have hClosed : IsClosed (K : Set (HilbertGraph U)) := e.toHomeomorph.isClosedMap _ hClosed₀
  letI : CompleteSpace K := hClosed.isComplete.completeSpace_coe
  letI : InnerProductSpace ℝ K := inferInstance
  exact exists_evaluation_of_equiv_hilbert (B := H10 U) (K := K) E Λ

private theorem H10.eq_of_dual_evaluation {U : Set Point} {z w : H10 U}
    (h : ∀ v : HMinusOne U, v z = v w) : z = w := by
  let E := NormedSpace.inclusionInDoubleDualLi ℝ (E := H10 U)
  have hEq : E z = E w := ContinuousLinearMap.ext h
  exact E.injective hEq

/-- The adjoint of an invertible weak Dirichlet operator is invertible
on the same zero-trace graph. The given forcing is evaluated by the
actual (L^2) pairing, and the bound is in the original graph norm. -/
theorem exists_unique_dirichletAdjoint_of_forcing
    {U : Set Point} (P : H10 U ≃L[ℝ] HMinusOne U) (F : HMinusOne U) :
    ∃ w : H10 U,
      ‖w‖ ≤ ‖P.symm.toContinuousLinearMap‖ * ‖F‖ ∧
      (∀ v : H10 U, P v w = F v) ∧
      ∀ z : H10 U, (∀ v : H10 U, P v z = F v) → z = w := by
  let Λ := F.comp P.symm.toContinuousLinearMap
  obtain ⟨w,hw,hW⟩ := exists_H10_of_dual_functional U Λ
  have hApply (v : H10 U) : P v w = F v := by
    rw [← hW]
    change F (P.symm (P v)) = F v
    rw [P.symm_apply_apply]
  have hNorm : ‖Λ‖ ≤ ‖F‖ * ‖P.symm.toContinuousLinearMap‖ :=
    ContinuousLinearMap.opNorm_comp_le F P.symm.toContinuousLinearMap
  refine ⟨w, hw.trans (hNorm.trans_eq (mul_comm _ _)), hApply, fun z hz => ?_⟩
  apply H10.eq_of_dual_evaluation
  intro v
  obtain ⟨a,rfl⟩ := P.surjective v
  exact (hz a).trans (hApply a).symm

theorem exists_dirichletAdjoint_of_memLp {U : Set Point}
    (P : H10 U ≃L[ℝ] HMinusOne U) (f : Lp S0 2 (volume.restrict U)) :
    ∃ w : H10 U, ∀ v : H10 U, P v w = ∫ x in U, frobeniusS0 (h10Value v x) (f x) := by
  obtain ⟨F,hF⟩ := exists_H10_forcingFunctional_of_memLp (Lp.memLp f)
  obtain ⟨w,_,hw,_⟩ := exists_unique_dirichletAdjoint_of_forcing P F
  refine ⟨w,fun v => (hw v).trans ((hF v).2.trans ?_)⟩
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => frobenius_comm (f x : Tensor) (h10Value v x : Tensor)

end Thesis
