module

public import Thesis.Upstream.PoissonL4Interior
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Thesis.Variational.BoundarySmallEnergy
import Thesis.Variational.ScaledDefects

/-! Classical cutoff calculus and quantitative source localization on a physical cap. -/

public section

noncomputable section

open Filter Metric Set
open scoped ContDiff Topology

namespace Thesis

private theorem coordDeriv_mul_scalar {u v : Point → ℝ} {x : Point}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) (j : Fin 3) :
    coordDeriv j (u * v) x = u x * coordDeriv j v x + coordDeriv j u x * v x := by
  have h := hu.hasFDerivAt.mul hv.hasFDerivAt
  change (fderiv ℝ (u * v) x) (axis j) = _
  rw [h.fderiv]
  simp only [coordDeriv, add_apply, smul_apply, smul_eq_mul, mul_comm]

/-- The cutoff product rule with the actual coordinate Laplacian and gradient. -/
theorem laplacian_mul_scalar {U : Set Point} (hU : IsOpen U) {u v : Point → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U) {x : Point} (hx : x ∈ U) :
    laplacian (u * v) x = u x * laplacian v x + v x * laplacian u x +
      2 * ∑ j, coordDeriv j u x * coordDeriv j v x := by
  have huD (y : Point) (hy : y ∈ U) : DifferentiableAt ℝ u y :=
    ((hu y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt two_ne_zero
  have hvD (y : Point) (hy : y ∈ U) : DifferentiableAt ℝ v y :=
    ((hv y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt two_ne_zero
  have hC (j : Fin 3) :
      coordDeriv j (coordDeriv j (u * v)) x =
        u x * coordDeriv j (coordDeriv j v) x + v x * coordDeriv j (coordDeriv j u) x +
          2 * (coordDeriv j u x * coordDeriv j v x) := by
    have he : coordDeriv j (u*v) =ᶠ[𝓝 x] u * coordDeriv j v + coordDeriv j u * v := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact coordDeriv_mul_scalar (huD y hy) (hvD y hy) j
    have huJ := differentiableAt_coordDeriv_of_contDiffAt ((hu x hx).contDiffAt (hU.mem_nhds hx)) j
    have hvJ := differentiableAt_coordDeriv_of_contDiffAt ((hv x hx).contDiffAt (hU.mem_nhds hx)) j
    change (fderiv ℝ (coordDeriv j (u*v)) x) (axis j) = _
    rw [he.fderiv_eq, fderiv_add ((huD x hx).mul hvJ) (huJ.mul (hvD x hx)), add_apply]
    change coordDeriv j (u * coordDeriv j v) x + coordDeriv j (coordDeriv j u * v) x = _
    rw [coordDeriv_mul_scalar (huD x hx) hvJ, coordDeriv_mul_scalar huJ (hvD x hx)]
    ring
  unfold laplacian
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => hC j

/-- A function constant near a point has zero coordinate Laplacian there. -/
theorem laplacian_eq_zero_of_eventuallyEq_const {u : Point → ℝ} {x : Point} {c : ℝ}
    (h : u =ᶠ[𝓝 x] fun _ => c) : laplacian u x = 0 := by
  unfold laplacian
  apply Finset.sum_eq_zero
  intro j _
  have he : coordDeriv j u =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [eventually_eventually_nhds.mpr h] with y hy
    change u =ᶠ[𝓝 y] (fun _ => c) at hy
    exact DFunLike.congr_fun (hy.fderiv_eq.trans (hasFDerivAt_const c y).fderiv) (axis j)
  exact DFunLike.congr_fun (he.fderiv_eq.trans (hasFDerivAt_const (0 : ℝ) x).fderiv) (axis j)

/-- On any physical ball a single smooth cutoff has uniform first and
second derivative bounds after spatial scaling. -/
theorem exists_boundaryL4_cutoff :
    ∃ A : ℝ, 0 < A ∧ ∀ (c : Point) {r : ℝ}, 0 < r →
      ∃ χ : Point → ℝ, ContDiff ℝ ∞ χ ∧
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
        EqOn χ (fun _ => 1) (closedBall c (r/2)) ∧
        tsupport χ ⊆ closedBall c (3*r/4) ∧
        ∀ x, ‖fderiv ℝ χ x‖ ≤ A/r ∧ |laplacian χ x| ≤ A/r^2 := by
  let b : ContDiffBump (0 : Point) := ⟨1/2, 3/4, by norm_num, by norm_num⟩
  let B : Point → ℝ := b
  have hB : ContDiff ℝ ∞ B := b.contDiff
  have hSupp : tsupport B ⊆ closedBall (0 : Point) (3/4) := b.tsupport_eq.subset
  have hLPCont : Continuous (laplacian B) := by
    classical
    unfold laplacian
    apply continuous_finsetSum Finset.univ
    intro i _
    have hD {f : Point → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (coordDeriv i f) :=
      (ContinuousLinearMap.apply ℝ ℝ (axis i)).contDiff.comp (hf.fderiv_right (by simp))
    exact (hD (hD hB)).continuous
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : Point) (3/4)).exists_bound_of_continuousOn
    (hB.continuous_fderiv (by simp)).continuousOn
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Point) (3/4)).exists_bound_of_continuousOn hLPCont.continuousOn
  let A := 1 + max L 0 + max M 0
  have hL' : L ≤ A := by dsimp only [A]; linarith only [le_max_left L 0, le_max_right M 0]
  have hM' : M ≤ A := by dsimp only [A]; linarith only [le_max_left M 0, le_max_right L 0]
  have hA : 0 < A := by dsimp only [A]; positivity
  have hDer (x : Point) : ‖fderiv ℝ B x‖ ≤ A := by
    by_cases hx : x ∈ closedBall (0 : Point) (3/4)
    · exact (hL x hx).trans hL'
    · rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := B) (fun h => hx (hSupp h)), norm_zero]
      exact hA.le
  have hLap (x : Point) : |laplacian B x| ≤ A := by
    by_cases hx : x ∈ closedBall (0 : Point) (3/4)
    · exact (hM x hx).trans hM'
    · have hxN : x ∉ tsupport B := fun h => hx (hSupp h)
      have hNear : B =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport B).isOpen_compl.mem_nhds hxN] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      rw [laplacian_eq_zero_of_eventuallyEq_const hNear, abs_zero]
      exact hA.le
  refine ⟨A, hA, ?_⟩
  intro c r hr
  let Z (x : Point) := (-r⁻¹ • c) + r⁻¹ • x
  let χ := B ∘ Z
  have hZR (x : Point) : Z x = r⁻¹ • (x-c) := by
    dsimp only [Z]
    rw [smul_sub, neg_smul, add_comm, sub_eq_add_neg]
  have hNorm (x : Point) : ‖Z x‖ = r⁻¹ * dist x c := by
    rw [hZR, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), dist_eq_norm]
  have hZ : ContDiff ℝ ∞ Z := contDiff_const.add (contDiff_id.const_smul _)
  refine ⟨χ, hB.comp hZ, fun x => ⟨b.nonneg, b.le_one⟩, ?_, ?_, ?_⟩
  · intro x hx
    apply b.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff]
    change ‖Z x‖ ≤ 1/2
    rw [hNorm]
    have h := mul_le_mul_of_nonneg_left (mem_closedBall.1 hx) (inv_nonneg.mpr hr.le)
    exact h.trans_eq (by field_simp)
  · apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    have hBad : 3/4 < ‖Z x‖ := by
      have hd : 3*r/4 < dist x c := lt_of_not_ge (fun h => hn (mem_closedBall.2 h))
      rw [hNorm]
      have h := mul_lt_mul_of_pos_left hd (inv_pos.mpr hr)
      exact (show r⁻¹*(3*r/4)=3/4 by field_simp) ▸ h
    have hz : Z x ∉ tsupport B := fun h => (not_le_of_gt hBad) (mem_closedBall_zero_iff.1 (hSupp h))
    exact hx (show χ x = 0 from image_eq_zero_of_notMem_tsupport (f := B) hz)
  · intro x
    have hDE : fderiv ℝ χ x = r⁻¹ • fderiv ℝ B (Z x) :=
      fderiv_affine_dilation _ _ (hB.differentiable (by simp) _)
    have hLE : laplacian χ x = (r⁻¹)^2 • laplacian B (Z x) :=
      laplacian_affine_dilation isOpen_univ
        ((hB.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn) _ _ (mem_univ _)
    refine ⟨?_, ?_⟩
    · rw [hDE, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), div_eq_mul_inv, mul_comm A]
      exact mul_le_mul_of_nonneg_left (hDer _) (inv_nonneg.mpr hr.le)
    · rw [hLE, smul_eq_mul, abs_mul, abs_of_nonneg (sq_nonneg _), div_eq_mul_inv, mul_comm A, inv_pow]
      exact mul_le_mul_of_nonneg_left (hLap _) (inv_nonneg.mpr (sq_nonneg _))

/-- The derivative terms of the cutoff forcing vanish on the inner ball. -/
theorem boundaryL4_cutoff_derivatives_zero {χ : Point → ℝ} {c : Point} {r : ℝ}
    (hχ : EqOn χ (fun _ => 1) (closedBall c (r/2))) {x : Point} (hx : x ∈ ball c (r/2)) :
    fderiv ℝ χ x = 0 ∧ laplacian χ x = 0 := by
  have he : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hx) (fun _ hy => hχ (ball_subset_closedBall hy))
  exact ⟨he.fderiv_eq.trans (hasFDerivAt_const (1 : ℝ) x).fderiv, laplacian_eq_zero_of_eventuallyEq_const he⟩

end Thesis

end
