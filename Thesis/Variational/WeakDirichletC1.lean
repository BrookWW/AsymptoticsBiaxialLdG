module

public import Thesis.Variational.ContinuousWeakColumns
public import Thesis.External.DirichletPoissonRegularity
public import Thesis.Variational.WeakCorrectionPairing
import Thesis.Variational.DirichletPoissonW24
import Thesis.Variational.WeakDirichletContinuity
import Thesis.Variational.H10StrongApproximation
import Thesis.Variational.GlobalDirichletPoissonFromSmooth
import Thesis.Variational.WeakPoissonH10
import Thesis.Variational.BoundaryLimit

/-! Weak solutions with bounded forcing are C¹ on the actual closed domain. -/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

local instance weakDirichletC1ContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

/-- Bounded forcing gives a classical first derivative on the closed
zero-trace Dirichlet graph. -/
theorem exists_contDiffOn_one_of_bounded_weakDirichlet
    {U : Set Point} (hU : IsSmoothDomain U)
    (w : H10 U) {f : Point → S0} (hf : MemLp f 2 (volume.restrict U))
    (hPair : ∀ z : H10 U, h10PrincipalPart U w z = ∫ x in U, frobeniusS0 (f x) (h10Value z x))
    {M : ℝ} (hM : 0 ≤ M) (hBound : ∀ᵐ x ∂volume.restrict U, ‖f x‖ ≤ M) :
    ∃ v : Point → S0, h10Value w =ᵐ[volume.restrict U] v ∧
      ContDiffOn ℝ 1 v (closure U) ∧ EqOn v (fun _ => 0) (frontier U) := by
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  obtain ⟨v,hV,hC,hWall⟩ := exists_continuousOn_closure_of_bounded_weakDirichlet hU w hf hPair hM hBound
  let g := hf.toLp f
  have hg : MemLp (fun x => g x) 4 μ :=
    (MemLp.of_bound hf.1 M hBound).ae_eq hf.coeFn_toLp.symm
  have hEq (z : H10 U) : h10PrincipalPart U w z = ∫ x in U, frobeniusS0 (g x) (h10Value z x) := by
    rw [hPair]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    change g x = f x at hx
    rw [hx]
  obtain ⟨K,hK⟩ := exists_H10_dirichletPoisson_secondWeakGradient_four hU w g hg hEq
  have hSob := (H10.hasZeroTrace hU.1.1 w).1.congr_ae hV EventuallyEq.rfl
  have hSecond := hU.contDiffOn_one_of_tensor_weak_secondColumnsLp (p := 4) (by norm_num) hSob hC
    (fun j => (hK j).1) (fun j i => by simpa only [ENNReal.ofReal_ofNat] using (hK j).2 i)
  exact ⟨v,hV,hSecond,hWall⟩

/-- The bounded weak Poisson equation with a smooth lift has a C¹
representative with the prescribed wall values. -/
theorem exists_closedC1_representative_of_weakPoisson
    {U : Set Point} (hU : IsSmoothDomain U) {u b : Point → S0} {D : Point → Gradient}
    {F : Point → Tensor} (hb : ContDiff ℝ ∞ b) (hu : MemH1 U u D)
    (hTr : SameTrace U u b D (ClassicalGradient b)) (hW : IsWeakPoisson U D F)
    (hBound : ∃ M : ℝ, ∀ᵐ x ∂volume.restrict U, ‖F x‖ ≤ M) :
    ∃ v : Point → S0, u =ᵐ[volume.restrict U] v ∧
      ContDiffOn ℝ 1 v (closure U) ∧ EqOn v b (frontier U) := by
  obtain ⟨M,hM,hFmem,hFBd⟩ := exists_bounded_projected_lift_forcing hU hb hW hBound
  obtain ⟨w,hVal,hGrad⟩ := hTr.exists_H10_with_ae_data hU.1.1
  have hPair := h10PrincipalPart_eq_forcing_of_weakPoisson_lift hU.1.1 hu hW hb hFmem w hGrad
  obtain ⟨v,hvAE,hv,hvB⟩ := exists_contDiffOn_one_of_bounded_weakDirichlet hU w hFmem hPair hM hFBd
  refine ⟨v+b,?_,hv.add (hb.contDiffOn.of_le (by simp)),?_⟩
  · filter_upwards [hVal,hvAE] with x hx hy
    exact sub_eq_iff_eq_add.1 (hx.symm.trans hy)
  · intro x hx
    change v x + b x = b x
    rw [hvB hx,zero_add]

end Thesis
