module

public import Thesis.Variational.WeakDirichletC1
import Thesis.Variational.WeakPoissonH10
import Thesis.Variational.GlobalDirichletPoissonFromSmooth
import Thesis.Variational.WeakZeroTraceGraph
import Thesis.Variational.DirichletPoissonWeak
import Thesis.Variational.H10StrongApproximation
import Thesis.Variational.ClassicalDirichletFromSchauder
import Thesis.Variational.BoundaryLimit
import Thesis.Upstream.InteriorPoissonRegularity

/-! The physical wall second derivative estimate for the pure zero-trace
Poisson equation supplies the closed regularity of a general fixed lift. -/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

/-- Regularity of an existing actual zero-trace weak solution with a
continuously differentiable force on the closed domain. -/
@[expose] def WeakZeroTracePoissonClosureTwo : Prop :=
  ∀ {U : Set Point}, IsSmoothDomain U → ∀ (w : H10 U) {f : Point → S0},
    ContDiffOn ℝ 1 f (closure U) →
    (∀ z : H10 U, h10PrincipalPart U w z = ∫ x in U, frobeniusS0 (f x) (h10Value z x)) →
    ∀ {v : Point → S0}, h10Value w =ᵐ[volume.restrict U] v →
      ContinuousOn v (closure U) → ContDiffOn ℝ 2 v (closure U)

private theorem contDiff_laplacian_of_smooth_lift {b : Point → S0} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (laplacian b) := by
  have hCol {g : Point → S0} (hg : ContDiff ℝ ∞ g) (i : Fin 3) :
      ContDiff ℝ ∞ (coordDeriv i g) :=
    (hg.fderiv_right (by simp)).clm_apply contDiff_const
  unfold laplacian
  exact ContDiff.sum fun i _ => hCol (hCol hb i) i

/-- A pure zero-wall result and the native weak C¹ representative theorem
give the two closed-domain estimates used by the original variational problem. -/
theorem globalDirichletPoissonClosureC2_of_zeroTrace
    (hTwo : WeakZeroTracePoissonClosureTwo) : External.GlobalDirichletPoissonClosureC2 := by
  refine ⟨?_,?_⟩
  · intro U u b D F hU hb hu hTr hP hBound
    exact exists_closedC1_representative_of_weakPoisson hU hb hu hTr hP hBound
  · intro U u b D F hU hb hu hTr hP huC hFC
    have hBound : ∃ M : ℝ, ∀ᵐ x ∂volume.restrict U, ‖F x‖ ≤ M := by
      obtain ⟨M,hM⟩ := hU.1.2.2.isCompact_closure.exists_bound_of_continuousOn hFC.continuousOn
      exact ⟨M,(ae_restrict_mem hU.1.1.measurableSet).mono fun x hx => hM x (subset_closure hx)⟩
    obtain ⟨_,_,hForce,_⟩ := exists_bounded_projected_lift_forcing hU hb hP hBound
    obtain ⟨w,hVal,hGrad⟩ := hTr.exists_H10_with_ae_data hU.1.1
    have hPair := h10PrincipalPart_eq_forcing_of_weakPoisson_lift hU.1.1 hu hP hb hForce w hGrad
    have hP₁ : ContDiffOn ℝ 1 (fun x => traceFreeSymmetricPart (F x) - laplacian b x) (closure U) :=
      (traceFreeSymmetricPartCLM.contDiff.comp_contDiffOn hFC).sub
        ((contDiff_laplacian_of_smooth_lift hb).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
    have hTwoWall := hTwo hU w hP₁ hPair hVal (huC.continuousOn.sub hb.continuous.continuousOn)
    simpa only [Pi.sub_apply,sub_add_cancel] using hTwoWall.add
      ((hb.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn : ContDiffOn ℝ 2 b (closure U))

local instance weakDirichletC2ContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

/-- The interior equation, actual trace and closed C¹ representative
are native. It suffices to prove the second derivative locally at each
physical wall point. -/
theorem weakZeroTracePoissonClosureTwo_of_wall
    (hWall : ∀ {U : Set Point}, IsSmoothDomain U → ∀ (w : H10 U) {f v : Point → S0},
      ContDiffOn ℝ 1 f (closure U) → MemLp f 2 (volume.restrict U) →
      (∀ z : H10 U, h10PrincipalPart U w z = ∫ x in U, frobeniusS0 (f x) (h10Value z x)) →
      h10Value w =ᵐ[volume.restrict U] v →
      ContDiffOn ℝ 1 v (closure U) → ContDiffOn ℝ 2 v U →
      EqOn v (fun _ => 0) (frontier U) → (∀ x ∈ U, laplacian v x = f x) →
      ∀ x ∈ frontier U, ContDiffWithinAt ℝ 2 v (closure U) x) :
    WeakZeroTracePoissonClosureTwo := by
  intro U hU w f hf hPair v hv hvc
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  obtain ⟨M,hM⟩ := hU.1.2.2.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  let K := max M 0
  have hK : 0 ≤ K := le_max_right _ _
  have hFb : ∀ᵐ x ∂μ, ‖f x‖ ≤ K :=
    (ae_restrict_mem hU.1.1.measurableSet).mono fun x hx => (hM x (subset_closure hx)).trans (le_max_left _ _)
  letI : TopologicalSpace.PseudoMetrizableSpace S0 := by
    let metric := (inferInstance : NormedAddCommGroup S0).toMetricSpace
    letI : TopologicalSpace S0 := metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    exact inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace S0)
  have hC := hf.continuousOn.mono (subset_closure : U ⊆ closure U)
  have hF₂ : MemLp f 2 μ := MemLp.of_bound (hC.aestronglyMeasurable hU.1.1.measurableSet) K hFb
  obtain ⟨v',hv',hv'₁,hWall'⟩ := exists_contDiffOn_one_of_bounded_weakDirichlet hU w hF₂ hPair hK hFb
  have hSame := Measure.eqOn_open_of_ae_eq (hv.symm.trans hv') hU.1.1 (hvc.mono subset_closure)
    (hv'₁.continuousOn.mono subset_closure)
  have hVal : EqOn v v' (closure U) :=
    hSame.of_subset_closure hvc hv'₁.continuousOn subset_closure Subset.rfl
  have hv₁ : ContDiffOn ℝ 1 v (closure U) := hv'₁.congr hVal
  have hZero : EqOn v (fun _ => 0) (frontier U) := (hVal.mono frontier_subset_closure).trans hWall'
  have hSob := (H10.hasZeroTrace hU.1.1 w).1.congr_ae hv EventuallyEq.rfl
  have hP := isWeakPoisson_of_H10_pairing hU.1.1 hF₂
    (fun z => (h10PrincipalPart_apply w z).symm.trans (hPair z))
  have hFcon : ContDiffOn ℝ 1 (fun x => (f x : Tensor)) U :=
    symmetricTraceless.subtypeL.contDiff.comp_contDiffOn (hf.mono subset_closure)
  have hv₂ : ContDiffOn ℝ 2 v U :=
    interiorPoissonRegularity.contDiffOn_succ 1 hU.1.1 hSob.memH1Loc hP (hvc.mono subset_closure) hFcon
  have hEq (x : Point) (hx : x ∈ U) : laplacian v x = f x :=
    (laplacian_eq_projected_forcing_of_weak hU.1.1 hSob hv₂ hFcon.continuousOn hP x hx).trans
      (traceFreeSymmetricPart_of_S0 _)
  intro x hx
  by_cases hInside : x ∈ U
  · exact ((hv₂ x hInside).contDiffAt (hU.1.1.mem_nhds hInside)).contDiffWithinAt
  · have hxWall : x ∈ frontier U := by rw [frontier, hU.1.1.interior_eq]; exact ⟨hx,hInside⟩
    exact hWall hU w hf hF₂ hPair hv hv₁ hv₂ hZero hEq x hxWall

end Thesis
