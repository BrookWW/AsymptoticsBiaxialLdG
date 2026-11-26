module

public import Thesis.External.DirichletPoissonRegularity
import Thesis.Variational.WeakDirichletContinuity
import Thesis.Variational.H10StrongApproximation
import Thesis.Variational.BoundaryLimit
import Thesis.Variational.ScaledDefects
import Thesis.Upstream.WeakPoissonCoordinates
import HolderToCK.Analysis.ClassicalEquation

/-! Classical smooth-forcing solvability from the weak Dirichlet inverse
and boundary regularity of the existing continuous weak solution. -/

public section

noncomputable section

open Filter HarmonicMaps HolderToCK MeasureTheory Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

local instance smoothForcingContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

/-- At a classical representative, the weak Poisson equation holds
pointwise with its actual symmetric trace-free forcing. -/
theorem laplacian_eq_projected_forcing_of_weak
    {U : Set Point} (hU : IsOpen U) {u : Point → S0} {F : Point → Tensor} {D : Point → Gradient}
    (hu : MemH1 U u D) (hu₂ : ContDiffOn ℝ 2 u U) (hF₀ : ContinuousOn F U)
    (hP : IsWeakPoisson U D F) :
    ∀ x ∈ U, laplacian u x = traceFreeSymmetricPart (F x) := by
  let f := traceFreeSymmetricPartCLM ∘ F
  have hf : ContinuousOn f U := traceFreeSymmetricPartCLM.continuous.comp_continuousOn hF₀
  let O : OpenDomain 3 := ⟨U,hU⟩
  let L : S0 →L[ℝ] Ambient 5 := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨hNative,hEq⟩ := hP.to_frobenius hU hu.memH1Loc
  have hC : ContDiffOn ℝ 2 (frobeniusField u) O.val := L.contDiff.comp_contDiffOn hu₂
  have hF : ContinuousOn (frobeniusField f) O.val := L.continuous.comp_continuousOn hf
  have hEq' : WeakPoissonOn O (frobeniusGradient D) (frobeniusField f) := by
    exact hEq
  have hPoint := hEq'.laplacian_eq_of_contDiffOn_two hNative.1 hC hF
  intro x hx
  apply frobeniusCoordinateEquiv.injective
  change L (laplacian u x) = L (f x)
  have hAt := (hC x hx).contDiffAt (hU.mem_nhds hx)
  calc
    _ = laplacian (frobeniusField u) x := (laplacian_compCLM hU hu₂ hx L).symm
    _ = Laplacian.laplacian (frobeniusField u) x :=
      (laplacian_eq_coordinateSum_of_contDiffAt_two (frobeniusField u) x hAt).symm
    _ = _ := hPoint x hx

private theorem exists_classical_smooth_dirichlet_pure
    (hStep : External.GlobalDirichletPoissonSchauderStep)
    {U : Set Point} (hU : IsSmoothDomain U) {f : Point → S0} (hf : ContDiff ℝ ∞ f) :
    ∃ v : Point → S0, ContDiffOn ℝ 2 v (closure U) ∧ EqOn v (fun _ => 0) (frontier U) ∧
      ∀ x ∈ U, laplacian v x = f x := by
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  obtain ⟨M,hM⟩ := hU.1.2.2.isCompact_closure.exists_bound_of_continuousOn hf.continuous.continuousOn
  let K := max M 0
  have hK : 0 ≤ K := le_max_right _ _
  have hFB : ∀ᵐ x ∂μ, ‖f x‖ ≤ K :=
    (ae_restrict_mem hU.1.1.measurableSet).mono fun x hx => (hM x (subset_closure hx)).trans (le_max_left _ _)
  have hF2 : MemLp f 2 μ := MemLp.of_bound hf.continuous.aestronglyMeasurable K hFB
  obtain ⟨w,hW,_⟩ := exists_unique_H10_dirichletPoisson_of_memLp hU.1.1.measurableSet hU.1.2.2 hF2
  have hPrincipal (z : H10 U) : h10PrincipalPart U w z = ∫ x in U, frobeniusS0 (f x) (h10Value z x) :=
    (h10PrincipalPart_apply w z).trans (hW z)
  obtain ⟨v,hVal,hC,hWall⟩ := exists_continuousOn_closure_of_bounded_weakDirichlet hU w hF2 hPrincipal hK hFB
  have hP := isWeakPoisson_of_H10_pairing hU.1.1 hF2 hW
  have hZero := (H10.hasZeroTrace hU.1.1 w).congr_ae hVal EventuallyEq.rfl
  have hTrace : SameTrace U v (fun _ => 0) (h10Gradient w) (ClassicalGradient fun _ => 0) := by
    have hG : (ClassicalGradient (fun _ : Point => (0 : S0))) = 0 := by
      funext x j
      simp [ClassicalGradient,coordDeriv]
    unfold SameTrace
    rw [hG,sub_zero,show (fun _ : Point => (0 : S0)) = 0 from rfl,sub_zero]
    exact hZero
  have hF₁ : ContDiffOn ℝ 1 (fun x => (f x : Tensor)) (closure U) :=
    (symmetricTraceless.subtypeL.contDiff.comp (hf.of_le (WithTop.coe_le_coe.mpr le_top))).contDiffOn
  have hv₂ : ContDiffOn ℝ 2 v (closure U) := by
    exact hStep 0 hU contDiff_const hZero.1 hTrace hP (contDiffOn_zero.mpr hC) hF₁
  refine ⟨v,hv₂,hWall,fun x hx => ?_⟩
  have hFC : ContinuousOn (fun y => (f y : Tensor)) U :=
    symmetricTraceless.subtypeL.continuous.comp_continuousOn hf.continuous.continuousOn
  exact (laplacian_eq_projected_forcing_of_weak hU.1.1 hZero.1
    (hv₂.mono subset_closure) hFC hP x hx).trans (traceFreeSymmetricPart_of_S0 _)

/-- The existence clause for the classical Dirichlet problem follows
from the pure weak inverse and the closure Schauder step. -/
theorem classicalDirichletPoissonRegularity_of_schauder
    (hStep : External.GlobalDirichletPoissonSchauderStep) : External.ClassicalDirichletPoissonRegularity := by
  refine ⟨?_,?_⟩
  · intro U hU f hf
    exact exists_classical_smooth_dirichlet_pure hStep hU hf
  · intro n hn U u b D F hU hb hu hT hP hV hF
    cases n with
    | zero => exact (Nat.lt_irrefl 0 hn).elim
    | succ n =>
      have hLow : ContDiffOn ℝ n u (closure U) :=
        hV.of_le (by exact_mod_cast Nat.le_succ n)
      exact hStep n hU hb hu hT hP hLow hF

end Thesis
