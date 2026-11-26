module

public import Thesis.Variational.BoundaryBarrier
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! A scalar comparison bounds the Frobenius norm of the actual
zero-trace classical Dirichlet solution. -/

public section

noncomputable section

open Set MeasureTheory Metric Topology
open scoped ContDiff Matrix.Norms.Frobenius

namespace Thesis

/-- The amplitude of a classical zero-trace field is bounded by the
amplitude of its original Laplacian, with a domain-only constant. -/
theorem exists_global_zeroTrace_laplacian_sup_bound {U : Set Point} (hU : IsBoundedDomain U) :
    ∃ C : ℝ, 0 < C ∧ ∀ {v : Point → S0}, ContDiffOn ℝ 2 v (closure U) →
      EqOn v (fun _ => 0) (frontier U) → ∀ {M : ℝ}, 0 ≤ M →
      (∀ x ∈ U, ‖laplacian v x‖ ≤ M) → ∀ x ∈ closure U, ‖v x‖ ≤ C*M := by
  obtain ⟨R,hR,hSub⟩ := hU.2.2.subset_ball_lt 0 (0 : Point)
  refine ⟨R^2/6, by positivity,?_⟩
  intro v hv hZero M hM hLap x hx
  obtain ⟨L,hL,hEval⟩ := exists_dual_vector'' ℝ (v x)
  let b (y : Point) := (M/6) • ((R^2 : ℝ) - ‖y - (0 : Point)‖^2)
  let g (y : Point) := L (v y) - b y
  have hQ : ContDiff ℝ 2 (fun y : Point => ‖y - (0 : Point)‖^2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hb : ContDiff ℝ 2 b := (contDiff_const.sub hQ).const_smul _
  have hg : ContDiffOn ℝ 2 g (closure U) := (L.contDiff.comp_contDiffOn hv).sub hb.contDiffOn
  have hCl : closure U ⊆ closedBall (0 : Point) R :=
    closure_minimal (hSub.trans ball_subset_closedBall) isClosed_closedBall
  have hEq (z : Point) (hz : z ∈ U) : laplacian b z = -M := by
    have hCoord (i : Fin 3) : coordDeriv i (fun _ : Point => (R^2 : ℝ)) = fun _ => 0 := by
      funext y
      exact DFunLike.congr_fun (hasFDerivAt_const (R^2 : ℝ) y).fderiv (axis i)
    have hC : laplacian (fun _ : Point => (R^2 : ℝ)) z = 0 := by simp [laplacian,hCoord,coordDeriv]
    change laplacian (fun y : Point => (M/6) • ((R^2 : ℝ) - ‖y - (0 : Point)‖^2)) z = -M
    rw [laplacian_const_smul hU.1 ((contDiff_const.sub hQ).contDiffOn) hz,
      laplacian_sub_of_contDiffOn hU.1 contDiffOn_const hQ.contDiffOn hz,
      hC,laplacian_norm_sub_sq]
    change (M/6) * (0-6) = -M
    ring
  have hNonneg (z : Point) (hz : z ∈ U) : 0 ≤ laplacian g z := by
    change 0 ≤ laplacian (fun y => (L ∘ v) y - b y) z
    rw [laplacian_sub_of_contDiffOn hU.1
      (L.contDiff.comp_contDiffOn (hv.mono subset_closure)) hb.contDiffOn hz]
    change 0 ≤ laplacian (fun y => L (v y)) z - laplacian b z
    rw [laplacian_compCLM hU.1 (hv.mono subset_closure) hz L,hEq z hz]
    have hO := (L.le_opNorm (laplacian v z)).trans
      (mul_le_mul hL (hLap z hz) (norm_nonneg _) zero_le_one)
    rw [Real.norm_eq_abs,one_mul] at hO
    linarith [neg_le_abs (L (laplacian v z))]
  have hFront (y : Point) (hy : y ∈ frontier U) : g y ≤ 0 := by
    change L (v y) - b y ≤ _
    rw [hZero hy,map_zero,zero_sub,neg_nonpos]
    have hDist : ‖y - (0 : Point)‖ ≤ R := by
      simpa only [mem_closedBall,dist_eq_norm] using hCl (frontier_subset_closure hy)
    exact mul_nonneg (div_nonneg hM (by norm_num))
      (sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hDist 2))
  have hMax := nonpos_of_laplacian_nonneg_on_ball_subset hU.1 hSub hg.continuousOn
    (hg.mono subset_closure) hNonneg hFront x hx
  have hxLE : ‖v x‖ ≤ b x := by
    apply sub_nonpos.mp
    change L (v x) = ‖v x‖ at hEval
    rw [← hEval]
    exact hMax
  apply hxLE.trans
  change (M/6) * ((R^2 : ℝ) - ‖x - (0 : Point)‖^2) ≤ (R^2/6)*M
  calc
    _ ≤ (M/6) * (R^2 : ℝ) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) (div_nonneg hM (by norm_num))
    _ = _ := by ring

end Thesis
