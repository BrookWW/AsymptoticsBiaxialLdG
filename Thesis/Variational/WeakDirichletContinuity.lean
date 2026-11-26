module

public import Thesis.Variational.DirichletPoissonWeak
import Thesis.Variational.H10StrongApproximation
import Thesis.Variational.WeakDirichletComparison
import Thesis.Variational.WeakDirichletExteriorBarrier
import Thesis.Upstream.InteriorPoissonRepresentative

/-! Boundary continuity of the original zero-trace weak Dirichlet solution
with bounded forcing. -/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius RealInnerProductSpace

namespace Thesis

private theorem norm_le_supersolution_of_boundedForce {U : Set Point} (hU : IsBoundedDomain U)
    (w : H10 U) {f : Point → S0} (hf : MemLp f 2 (volume.restrict U))
    (hW : ∀ z : H10 U, h10PrincipalPart U w z = ∫ x in U, frobeniusS0 (f x) (h10Value z x))
    {M : ℝ} (hF : ∀ᵐ x ∂volume.restrict U, ‖f x‖ ≤ M)
    {v : Point → S0} (hv : h10Value w =ᵐ[volume.restrict U] v) (hvC : ContinuousOn v U)
    {B : Point → ℝ} (hB : ContDiffOn ℝ ∞ B U) (hPos : ∀ x ∈ U, 0 ≤ B x)
    (hBL : ∀ x ∈ U, laplacian B x ≤ -M) :
    ∀ x ∈ U, ‖v x‖ ≤ B x := by
  have hWeak (e : S0) (he : ‖e‖ = 1) :
      ∀ᵐ y ∂volume.restrict U, frobeniusS0 e (v y) ≤ B y := by
    have hSup : ∀ᵐ y ∂volume.restrict U, laplacian B y ≤ frobeniusS0 e (f y) := by
      filter_upwards [hF,ae_restrict_mem hU.1.measurableSet] with y hy hIn
      have hCS : -(‖e‖*‖f y‖) ≤ frobeniusS0 e (f y) := by
        rw [← frobeniusCoordinateEquiv_inner, ← frobeniusCoordinateEquiv.norm_map e,
          ← frobeniusCoordinateEquiv.norm_map (f y)]
        exact (neg_le_neg (abs_real_inner_le_norm _ _)).trans (neg_abs_le _)
      rw [he,one_mul] at hCS
      exact (hBL y hIn).trans ((neg_le_neg hy).trans hCS)
    have h := h10_weakDirichlet_component_le_smooth_supersolution hU e he w hf hW hB hPos hSup
    filter_upwards [h,hv] with y hy hy'
    simpa only [hy'] using hy
  have hPoint (e : S0) (he : ‖e‖ = 1) (x : Point) (hx : x ∈ U) : frobeniusS0 e (v x) ≤ B x := by
    let u (y : Point) := frobeniusS0 e (v y)
    have hUcont : ContinuousOn u U := by
      have hConst : ContinuousOn (fun _ : Point => frobeniusCoordinateEquiv e) U := continuousOn_const
      have hV := frobeniusCoordinateEquiv.continuous.comp_continuousOn hvC
      simpa only [Function.comp_apply,frobeniusCoordinateEquiv_inner] using hConst.inner (𝕜 := ℝ) hV
    have hEq : u =ᵐ[volume.restrict U] fun y => min (u y) (B y) :=
      (hWeak e he).mono fun y hy => (min_eq_left hy).symm
    exact (Measure.eqOn_open_of_ae_eq hEq hU.1 hUcont (hUcont.inf hB.continuousOn) hx).trans_le
      (min_le_right _ _)
  intro x hx
  by_cases hz : v x = 0
  · rw [hz,norm_zero]
    exact hPos x hx
  · let e := ‖v x‖⁻¹ • v x
    have hN : 0 < ‖v x‖ := norm_pos_iff.mpr hz
    have he : ‖e‖ = 1 := by
      dsimp only [e]
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hN.le),inv_mul_cancel₀ hN.ne']
    have hEq : frobeniusS0 e (v x) = ‖v x‖ := by
      rw [← frobeniusCoordinateEquiv_inner]
      dsimp only [e]
      rw [map_smul,real_inner_smul_left,real_inner_self_eq_norm_sq,frobeniusCoordinateEquiv.norm_map,
        pow_two,← mul_assoc,inv_mul_cancel₀ hN.ne',one_mul]
    exact hEq ▸ hPoint e he x hx

/-- Every weak zero-trace Dirichlet solution with bounded forcing has a
continuous representative on the actual closure with zero wall values. -/
theorem exists_continuousOn_closure_of_bounded_weakDirichlet {U : Set Point} (hU : IsSmoothDomain U)
    (w : H10 U) {f : Point → S0} (hf : MemLp f 2 (volume.restrict U))
    (hW : ∀ z : H10 U, h10PrincipalPart U w z = ∫ x in U, frobeniusS0 (f x) (h10Value z x))
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ᵐ x ∂volume.restrict U, ‖f x‖ ≤ M) :
    ∃ v : Point → S0, h10Value w =ᵐ[volume.restrict U] v ∧
      ContinuousOn v (closure U) ∧ EqOn v (fun _ => 0) (frontier U) := by
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  have hTrace := H10.hasZeroTrace hU.1.1 w
  have hPair (v : H10 U) :
      (∫ x in U, -(∑ j : Fin 3, frobeniusS0 (h10Gradient w x j) (h10Gradient v x j))) =
        ∫ x in U, frobeniusS0 (f x) (h10Value v x) :=
    (h10PrincipalPart_apply w v).symm.trans (hW v)
  have hEq := isWeakPoisson_of_H10_pairing hU.1.1 hf hPair
  obtain ⟨v,hV,hVC⟩ := hEq.exists_continuousRepresentative_of_bounded hU.1.1 hTrace.1.memH1Loc
    ⟨M,hF⟩
  let u := U.indicator v
  have hAE : h10Value w =ᵐ[volume.restrict U] u :=
    hV.trans ((ae_restrict_mem hU.1.1.measurableSet).mono fun x hx => (indicator_of_mem hx v).symm)
  have hFrontier : frontier U = closure U \ U := by rw [frontier,hU.1.1.interior_eq]
  refine ⟨u,hAE,?_,fun x hx => indicator_of_notMem (hFrontier ▸ hx).2 v⟩
  obtain ⟨_,_,hBarriers⟩ := hU.exists_exterior_tangent_scalar_barrier M hM
  intro p hp
  by_cases hP : p ∈ U
  · have hEq : u =ᶠ[𝓝 p] v := by
      filter_upwards [hU.1.1.mem_nhds hP] with y hy
      exact indicator_of_mem hy v
    exact (((hVC p hP).continuousAt (hU.1.1.mem_nhds hP)).congr hEq.symm).continuousWithinAt
  · have hpFront : p ∈ frontier U := hFrontier.symm ▸ (show p ∈ closure U \ U from ⟨hp,hP⟩)
    obtain ⟨B,hB,hBp,hBounds,hLap,_,_,_⟩ := hBarriers p hpFront
    have hNorm := norm_le_supersolution_of_boundedForce hU.1 w hf hW hF hV hVC
      (hB.mono subset_closure) (fun x hx => (hBounds x (subset_closure hx)).1) hLap
    have hNorm' (x : Point) (hx : x ∈ closure U) : ‖u x‖ ≤ B x := by
      by_cases hxU : x ∈ U
      · rw [show u x = v x from indicator_of_mem hxU v]
        exact hNorm x hxU
      · rw [show u x = 0 from indicator_of_notMem hxU v,norm_zero]
        exact (hBounds x hx).1
    change Tendsto u (𝓝[closure U] p) (𝓝 (u p))
    rw [show u p = 0 from indicator_of_notMem hP v]
    apply (tendsto_zero_iff_norm_tendsto_zero (f := u)).2
    have hLim : Tendsto B (𝓝[closure U] p) (𝓝 0) := by rw [← hBp]; exact hB.continuousOn p hp
    have hEventually : ∀ᶠ x in 𝓝[closure U] p, x ∈ closure U := self_mem_nhdsWithin
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLim
      (Eventually.of_forall fun _ => norm_nonneg _) (hEventually.mono hNorm')

end Thesis
