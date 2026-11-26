module

public import Thesis.Variational.SmoothDomainTraceOperator
public import Thesis.Variational.WeakCorrectionGreen
import Thesis.Variational.BoundaryPoissonEstimate

/-! The actual weak graph of a classical Dirichlet field on a smooth closure. -/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

local instance classicalDirichletContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

local instance classicalDirichletPseudoMetrizable : TopologicalSpace.PseudoMetrizableSpace S0 := by
  let metric := (inferInstance : NormedAddCommGroup S0).toMetricSpace
  letI : TopologicalSpace S0 := metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace S0)

private theorem memLp_two_of_continuousOn_smooth_closure
    {U : Set Point} (hU : IsSmoothDomain U) {f : Point → S0}
    (hf : ContinuousOn f (closure U)) : MemLp f 2 (volume.restrict U) := by
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  obtain ⟨M,hM⟩ := hU.1.2.2.isCompact_closure.exists_bound_of_continuousOn hf
  exact MemLp.of_bound ((hf.mono subset_closure).aestronglyMeasurable hU.1.1.measurableSet) M
    ((ae_restrict_mem hU.1.1.measurableSet).mono fun x hx => hM x (subset_closure hx))

/-- The actual displayed classical columns form a finite weak graph on
the entire bounded smooth domain. -/
theorem IsSmoothDomain.memH1_of_contDiffOn_closure_two
    {U : Set Point} (hU : IsSmoothDomain U) {v : Point → S0}
    (hv : ContDiffOn ℝ 2 v (closure U)) : MemH1 U v (ClassicalGradient v) := by
  refine ⟨memLp_two_of_continuousOn_smooth_closure hU hv.continuousOn, ?_,
    isWeakGradient_of_contDiffOn hU.1.1 ((hv.mono subset_closure).of_le (by norm_num))⟩
  intro j
  have hCont := continuousOn_closureGradient_column hU.uniqueDiffOn_closure (hv.of_le (by norm_num)) j
  apply (memLp_two_of_continuousOn_smooth_closure hU hCont).ae_eq
  filter_upwards [ae_restrict_mem hU.1.1.measurableSet] with x hx
  exact congrFun (closureGradient_eq_classicalGradient hU.1.1 hv hx) j

/-- A classical solution with zero boundary values is represented by a
genuine Dirichlet graph and satisfies the original pure weak pairing. -/
theorem exists_H10_of_classical_zeroTrace_Poisson {U : Set Point} (hU : IsSmoothDomain U)
    {v f : Point → S0} (hv : ContDiffOn ℝ 2 v (closure U))
    (hvB : EqOn v (fun _ => 0) (frontier U))
    (hf : MemLp f 2 (volume.restrict U)) (hEq : ∀ x ∈ U, laplacian v x = f x) :
    ∃ w : H10 U, h10Value w =ᵐ[volume.restrict U] v ∧
      h10Gradient w =ᵐ[volume.restrict U] ClassicalGradient v ∧
      ∀ z : H10 U, h10PrincipalPart U w z = ∫ x in U, frobeniusS0 (f x) (h10Value z x) := by
  have hZero := hU.hasZeroTrace_of_continuousOn_zero_frontier
    (hU.memH1_of_contDiffOn_closure_two hv) hv.continuousOn hvB
  obtain ⟨w,hVal,hGrad⟩ := hZero.exists_H10_with_ae_data hU.1.1
  let A : Point → (S0 × Gradient) →L[ℝ] S0 := 0
  have hPair (a b : H10 U) : h10PrincipalPart U a b = weakCorrectionPairing U A a b := by
    rw [h10PrincipalPart_apply,weakCorrectionPairing]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp [A,frobeniusS0,frobenius]
  refine ⟨w,hVal,hGrad,?_⟩
  apply h10_weakEquation_of_classical_weakCorrectionPairing hU.1.1 A (h10PrincipalPart U) hPair
    (hv.mono subset_closure) hf w hVal hGrad
  intro x hx
  simpa only [A, Pi.zero_apply, zero_apply, add_zero] using hEq x hx

end Thesis
