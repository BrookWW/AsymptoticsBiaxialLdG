module

public import Thesis.Variational.ClassicalDirichletHessianGlobal
import Thesis.Variational.BoundaryL4Cutoff
import Thesis.Variational.FlatWallCoordinates
import Thesis.Variational.LocalWallHessian
import Thesis.Variational.OddWallHessianEstimate

/-! The cutoff wall cap and the global classical Dirichlet Hessian estimate. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace Thesis

private theorem scalar_dirichlet_cutoff_gradient_bound {U : Set Point} (hU : IsOpen U)
    {χ u : Point → ℝ} (hχ : ContDiffOn ℝ 2 χ U) (hu : ContDiffOn ℝ 2 u U)
    {x : Point} (hx : x ∈ U) {s L M F G : ℝ} (hs : 0 < s) (hL : 0 ≤ L)
    (hF : 0 ≤ F) (hG : 0 ≤ G) (hχ₀ : |χ x| ≤ 1) (hχD : ‖fderiv ℝ χ x‖ ≤ L/s)
    (huB : ‖u x‖ ≤ M) (hGrad : ‖fderiv ℝ u x‖ ≤ G) :
    ‖fderiv ℝ (χ*u) x‖ ≤ (1+L/s)*(M+F+G) := by
  have hχAt := ((hχ x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt two_ne_zero
  have huAt := ((hu x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt two_ne_zero
  rw [fderiv_mul hχAt huAt]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul,Real.norm_eq_abs]
  have ha : |χ x| * ‖fderiv ℝ u x‖ ≤ G :=
    (mul_le_mul hχ₀ hGrad (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hb : |u x| * ‖fderiv ℝ χ x‖ ≤ M*(L/s) := by
    rw [← Real.norm_eq_abs]
    exact mul_le_mul huB hχD (norm_nonneg _) ((norm_nonneg _).trans huB)
  refine (add_le_add ha hb).trans ?_
  have hM : 0 ≤ M := (norm_nonneg _).trans huB
  have h₁ : G ≤ M+F+G := le_add_of_nonneg_left (add_nonneg hM hF)
  have h₂ : M*(L/s) ≤ (M+F+G)*(L/s) :=
    mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right hF).trans (le_add_of_nonneg_right hG)) (by positivity)
  simp only [div_eq_mul_inv] at h₂ ⊢
  nlinarith only [h₁,h₂]

/-- A fixed wall-centered cutoff transfers the small-slope estimate to a physical cap. -/
theorem exists_classicalDirichletHessian_boundary_patch
    {U : Set Point} (hU : IsSmoothDomain U) (p : ℝ) (hp : 1 < p)
    {a : Point} (ha : a ∈ frontier U) : HasScalarDirichletHessianCapBound U p a := by
  obtain ⟨W,hW,hHalf⟩ := exists_halfSpace_scalarPoissonHessianLp p hp
  let η := (18*(W+1))⁻¹
  have hη : 0 < η := inv_pos.mpr (by positivity)
  have hη₁ : η ≤ 1 := by
    dsimp only [η]
    exact inv_le_one_of_one_le₀ (by linarith only [hW])
  have hSmall : W*(9*η) ≤ 1/2 := by
    have hE : W*(9*η) = W/(2*(W+1)) := by
      dsimp only [η]
      field_simp
      ring
    rw [hE]
    apply (div_le_iff₀ (by positivity : 0 < 2*(W+1))).2
    linarith
  obtain ⟨P,hPa,hP,hSlope⟩ := hU.exists_graphPatch_two_small_slope ha hη
  have haN : a ∈ P.neighborhood := hPa ▸ P.center_mem_neighborhood
  obtain ⟨s,hs,hS⟩ := Metric.isOpen_iff.1 P.isOpen_neighborhood a haN
  obtain ⟨L,hL,hCut⟩ := exists_boundaryL4_cutoff
  obtain ⟨χ,hχ,hχN,hχInner,hχSupport,hχDer⟩ := hCut a hs
  obtain ⟨A,hA,hBound⟩ := P.exists_localHessian_bound_of_small_slope hU hP hp hW hHalf hη.le hη₁ hSmall hSlope
  let KF := 1+6*L/s+L/s^2
  let KG := 1+L/s
  let C := A*(KF+KG)
  have hKF : 0 ≤ KF := by dsimp only [KF]; positivity
  have hKG : 0 ≤ KG := by dsimp only [KG]; positivity
  have hC : 0 ≤ C := mul_nonneg hA (add_nonneg hKF hKG)
  have hχS : HasCompactSupport χ := (isCompact_closedBall a (3*s/4)).of_isClosed_subset
    (isClosed_tsupport χ) hχSupport
  have hχP : tsupport χ ⊆ P.neighborhood := hχSupport.trans
    ((closedBall_subset_ball (by linarith only [hs])).trans hS)
  refine ⟨s/2,C,half_pos hs,hC,?_⟩
  intro u M F G hM hF hG hu hz hv hf hGrad
  let v := χ*u
  have hχ₂ : ContDiff ℝ 2 χ := hχ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hv₂ : ContDiffOn ℝ 2 v (closure U) := hχ₂.contDiffOn.mul hu
  have hvz : EqOn v 0 (frontier U) := fun x hx => by
    change χ x*u x=0
    rw [hz hx,mul_zero]
  have hvC : HasCompactSupport v := hχS.mul_right
  have hvP : tsupport v ⊆ P.neighborhood := tsupport_mul_subset_left.trans hχP
  have hT : 0 ≤ M+F+G := add_nonneg (add_nonneg hM hF) hG
  have hχabs (x : Point) : |χ x| ≤ 1 := by rw [abs_of_nonneg (hχN x).1]; exact (hχN x).2
  have hvF (x : Point) (hx : x ∈ U) : ‖laplacian v x‖ ≤ KF*(M+F+G) :=
    scalar_dirichlet_cutoff_laplacian_bound hU.1.1 hχ₂.contDiffOn (hu.mono subset_closure)
      hs hL.le hM hF hG hx (hχabs x) (hχDer x).1 (hχDer x).2 (hv x hx) (hf x hx) (hGrad x hx)
  have hvG (x : Point) (hx : x ∈ U) : ‖fderiv ℝ v x‖ ≤ KG*(M+F+G) :=
    scalar_dirichlet_cutoff_gradient_bound hU.1.1 hχ₂.contDiffOn (hu.mono subset_closure)
      hx hs hL.le hF hG (hχabs x) (hχDer x).1 (hv x hx) (hGrad x hx)
  have hEst := hBound hv₂ hvz hvC hvP (mul_nonneg hKF hT) (mul_nonneg hKG hT) hvF hvG
  let D := U∩ball a (s/2)
  have hSub : D ⊆ U∩P.neighborhood := inter_subset_inter_right _
    ((ball_subset_ball (half_le_self hs.le)).trans hS)
  have hvEq : EqOn v u (ball a (s/2)) := fun x hx => by
    change χ x*u x=u x
    rw [hχInner (ball_subset_closedBall hx),one_mul]
  have hEq : (fun x => ‖iteratedFDeriv ℝ 2 v x‖) =ᵐ[volume.restrict D]
      (fun x => ‖iteratedFDeriv ℝ 2 u x‖) :=
    (ae_restrict_mem (hU.1.1.inter isOpen_ball).measurableSet).mono fun _ hx =>
      congrArg norm (iteratedFDeriv_two_eqOn_open_of_eqOn isOpen_ball hvEq hx.2)
  rw [← eLpNorm_congr_ae hEq]
  refine (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hSub)).trans (hEst.trans_eq ?_)
  congr 1
  dsimp only [C]
  ring

/-- The classical global Dirichlet (W^{2,p}) estimate on the original tensor field. -/
theorem globalDirichletPoissonSecondDerivativeLp : External.GlobalDirichletPoissonSecondDerivativeLp :=
  globalDirichletPoissonSecondDerivativeLp_of_scalar
    (scalarGlobalDirichletPoissonSecondDerivativeLp_of_caps
      (fun _ hU p hp _ ha => exists_classicalDirichletHessian_interior_patch hU.1.1 p hp ha)
      (fun _ hU p hp _ ha => exists_classicalDirichletHessian_boundary_patch hU p hp ha))

end Thesis

end
