module

public import Thesis.Variational.ProjectedHarmonicRemainder
public import Thesis.Variational.ScreenedExponential
public import Thesis.Variational.InteriorBiaxialBootstrap
import Thesis.Variational.EnergyEstimate
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The defect remainder near the physical boundary. -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance boundaryRemainderTensorForceNormed :
    NormedAddCommGroup ((ℝ × S0 × ScalarDefectPair) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

theorem infDist_frontier_eq_infDist_complement {U : Set Point} (hU : IsBoundedDomain U)
    {x : Point} (hx : x ∈ U) : Metric.infDist x (frontier U) = Metric.infDist x Uᶜ := by
  have hProper : U ≠ Set.univ := fun h => NormedSpace.unbounded_univ ℝ Point (h ▸ hU.2.2)
  obtain ⟨y, hy, hDist⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hProper
  have hFront : frontier U ⊆ Uᶜ := by
    rw [frontier, hU.1.interior_eq]
    exact fun y hy => hy.2
  exact le_antisymm ((Metric.infDist_le_dist_of_mem hy).trans_eq hDist.symm)
    (Metric.infDist_le_infDist_of_subset hFront ⟨y, hy⟩)

theorem infDist_frontier_pos_of_mem_domain {U : Set Point} (hU : IsBoundedDomain U)
    {x : Point} (hx : x ∈ U) : 0 < Metric.infDist x (frontier U) := by
  rw [infDist_frontier_eq_infDist_complement hU hx]
  have hProper : U ≠ Set.univ := fun h => NormedSpace.unbounded_univ ℝ Point (h ▸ hU.2.2)
  exact (hU.1.isClosed_compl.notMem_iff_infDist_pos (nonempty_compl.mpr hProper)).1 (by simpa using hx)

theorem ball_infDist_frontier_subset_domain {U : Set Point} (hU : IsBoundedDomain U)
    {x : Point} (hx : x ∈ U) : Metric.ball x (Metric.infDist x (frontier U)) ⊆ U := by
  rw [infDist_frontier_eq_infDist_complement hU hx]
  exact Metric.ball_infDist_compl_subset

theorem exists_infDist_frontier_upper_bound (U : Set Point) (hU : IsBoundedDomain U) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, Metric.infDist x (frontier U) ≤ R := by
  have hProper : U ≠ Set.univ := fun h => NormedSpace.unbounded_univ ℝ Point (h ▸ hU.2.2)
  obtain ⟨y, hy⟩ := nonempty_frontier_iff.2 ⟨hU.2.1.1, hProper⟩
  let R := Metric.diam (closure U) + 1
  have hR : 0 < R := add_pos_of_nonneg_of_pos Metric.diam_nonneg zero_lt_one
  refine ⟨R, hR, fun x hx => (Metric.infDist_le_dist_of_mem hy).trans ?_⟩
  exact (Metric.dist_le_diam_of_mem hU.2.2.closure (subset_closure hx) (frontier_subset_closure hy)).trans
    (le_add_of_nonneg_right zero_le_one)

private theorem norm_classicalGradient_column_le_sqrt (D : Gradient) (j : Fin 3) :
    ‖D j‖ ≤ Real.sqrt (gradientNormSq D) := by
  apply Real.le_sqrt_of_sq_le
  rw [gradientNormSq_eq_sum_norm_sq]
  exact Finset.single_le_sum (f := fun i : Fin 3 => ‖D i‖^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

private theorem norm_coordDeriv_le_first_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : Point → E) (x : Point) (j : Fin 3) :
    ‖coordDeriv j u x‖ ≤ ‖iteratedFDeriv ℝ 1 u x‖ := by
  have h := (iteratedFDeriv ℝ 1 u x).le_opNorm (fun _ => axis j)
  have hAxis : ‖axis j‖ = 1 := by simp [axis]
  simpa only [coordDeriv, iteratedFDeriv_one_apply, hAxis, Finset.prod_const_one, mul_one] using! h

private theorem coordDeriv_tuple_pair {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u : Point → E} {v : Point → F} {x : Point}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) (j : Fin 3) :
    coordDeriv j (fun y => (u y, v y)) x = (coordDeriv j u x, coordDeriv j v x) :=
  DFunLike.congr_fun (hu.hasFDerivAt.prodMk hv.hasFDerivAt).fderiv (axis j)

private theorem coordDeriv_scalarDefectPair_apply
    (a : BulkCoefficients) (ε : ElasticScale) {Q : Point → S0} {x : Point}
    (hQ : DifferentiableAt ℝ Q x) (i : Fin 3) (j : Fin 2) :
    (coordDeriv i (scalarDefectPair a ε ∘ Q) x) j =
      if j = 0 then coordDeriv i (scaledNormDefect a ε ∘ Q) x
      else coordDeriv i (scaledCubicTrace a ε ∘ Q) x := by
  have hD := ((contDiff_scalarDefectPair a ε).differentiable (by simp)).differentiableAt.comp x hQ
  have h := coordDeriv_compCLM (ContinuousLinearMap.proj j : ScalarDefectPair →L[ℝ] ℝ) hD i
  fin_cases j
  · change (coordDeriv i (scalarDefectPair a ε ∘ Q) x) 0 = coordDeriv i (scaledNormDefect a ε ∘ Q) x
    exact h.symm
  · change (coordDeriv i (scalarDefectPair a ε ∘ Q) x) 1 = coordDeriv i (scaledCubicTrace a ε ∘ Q) x
    exact h.symm

/-- The actual gradient of the matrix Laplacian grows at most like the
inverse distance to the physical wall, under the uniform zeroth-order
defect and gradient bounds. -/
theorem exists_coordDeriv_laplacian_bound_by_wall_distance
    (a : BulkCoefficients) (hEstimate : InteriorPoissonGradientEstimate) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C > (0 : ℝ), ∀ (ε : ElasticScale) {U : Set Point}, IsBoundedDomain U →
      ∀ Q : Point → S0, ContDiffOn ℝ ∞ Q U →
      (∀ x ∈ U, (ε : ℝ)^2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) →
      (∀ x ∈ U, ‖Q x‖ ≤ M ∧ |scaledNormDefect a ε (Q x)| ≤ M ∧ |scaledCubicTrace a ε (Q x)| ≤ M ∧
        Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ M) →
      ∀ x ∈ U, ∀ j : Fin 3,
        ‖coordDeriv j (laplacian Q) x‖ ≤ C * (1 + (Metric.infDist x (frontier U))⁻¹) := by
  let A := biaxialTensorForce a
  have hA : ContDiff ℝ ∞ A := contDiff_biaxialTensorForce a
  let M' := max 1 M
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ℝ × S0 × ScalarDefectPair) M').exists_bound_of_continuousOn
    (hA.continuous_fderiv (by simp)).continuousOn
  let B := max 1 L
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨T, hT, hInt⟩ := exists_interior_classical_biaxial_derivative_bound a hEstimate 1 M hM
  let C := B * (M + 4*T)
  have hC : 0 < C := mul_pos hB (add_pos_of_nonneg_of_pos hM (by positivity))
  refine ⟨C, hC, ?_⟩
  intro ε U hU Q hQ hEq hBase x hx j
  let d := Metric.infDist x (frontier U)
  let r := d/2
  let ρ := d/4
  have hd : 0 < d := infDist_frontier_pos_of_mem_domain hU hx
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hρr : ρ < r := by dsimp only [r, ρ]; linarith only [hd]
  have hBU : Metric.ball x r ⊆ U :=
    (Metric.ball_subset_ball (by dsimp only [r]; linarith only [hd])).trans
      (ball_infDist_frontier_subset_domain hU hx)
  have hHigh := hInt ε x r ρ hρ hρr Q (hQ.mono hBU)
    (fun y hy => hEq y (hBU hy)) (fun y hy => (hBase y (hBU hy)).2) x (Metric.mem_ball_self hρ)
  let f (y : Point) := ((ε : ℝ)^2, Q y, scalarDefectPair a ε (Q y))
  have hf : ContDiffOn ℝ ∞ f U := contDiffOn_const.prodMk
    (hQ.prodMk ((contDiff_scalarDefectPair a ε).comp_contDiffOn hQ))
  have hQd : DifferentiableAt ℝ Q x := ((hQ x hx).contDiffAt (hU.1.mem_nhds hx)).differentiableAt (by simp)
  have hFd : DifferentiableAt ℝ (scalarDefectPair a ε ∘ Q) x :=
    (((contDiff_scalarDefectPair a ε).differentiable (by simp)).differentiableAt).comp x hQd
  have hfx : ‖f x‖ ≤ M' := by
    rw [show f x = ((ε : ℝ)^2, Q x, scalarDefectPair a ε (Q x)) from rfl, Prod.norm_def, Prod.norm_def]
    apply max_le
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hε₂ : (ε : ℝ)^2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ ε.2.1.le ε.2.2.le 2
      exact hε₂.trans (le_max_left _ _)
    · apply max_le ((hBase x hx).1.trans (le_max_right _ _))
      apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans (le_max_left _ _))).mpr
      intro i
      fin_cases i
      · exact (show |scaledNormDefect a ε (Q x)| ≤ M from (hBase x hx).2.1).trans (le_max_right _ _)
      · exact (show |scaledCubicTrace a ε (Q x)| ≤ M from (hBase x hx).2.2.1).trans (le_max_right _ _)
  have hPair (i : Fin 2) :
      ‖(coordDeriv j (scalarDefectPair a ε ∘ Q) x) i‖ ≤ T * (1 + (r-ρ)⁻¹) := by
    rw [coordDeriv_scalarDefectPair_apply a ε hQd]
    fin_cases i
    · change ‖coordDeriv j (scaledNormDefect a ε ∘ Q) x‖ ≤ _
      exact (norm_coordDeriv_le_first_fderiv _ x j).trans (by
        simpa only [pow_one] using (le_add_of_nonneg_right (norm_nonneg _)).trans
          ((le_add_of_nonneg_right (norm_nonneg _)).trans hHigh))
    · change ‖coordDeriv j (scaledCubicTrace a ε ∘ Q) x‖ ≤ _
      exact (norm_coordDeriv_le_first_fderiv _ x j).trans (by
        simpa only [pow_one] using (le_add_of_nonneg_left (norm_nonneg _)).trans
          ((le_add_of_nonneg_right (norm_nonneg _)).trans hHigh))
  have hDfx : ‖coordDeriv j f x‖ ≤ M + T * (1 + (r-ρ)⁻¹) := by
    have hScalar := coordDeriv_tuple_pair (u := fun _ : Point => (ε : ℝ)^2)
      (v := fun y => (Q y, (scalarDefectPair a ε ∘ Q) y)) (differentiableAt_const ((ε : ℝ)^2)) (hQd.prodMk hFd) j
    have hRight := coordDeriv_tuple_pair hQd hFd j
    change coordDeriv j f x = _ at hScalar
    rw [hScalar, hRight, Prod.norm_def, Prod.norm_def]
    apply max_le
    · simp only [coordDeriv, fderiv_const_apply, zero_apply, norm_zero]
      positivity
    · apply max_le
      · exact (norm_classicalGradient_column_le_sqrt (ClassicalGradient Q x) j).trans
          ((hBase x hx).2.2.2.trans (le_add_of_nonneg_right (by positivity)))
      · exact ((pi_norm_le_iff_of_nonneg (by positivity)).mpr hPair).trans (le_add_of_nonneg_left hM)
  have hEq' : laplacian Q =ᶠ[𝓝 x] A ∘ f := by
    filter_upwards [hU.1.mem_nhds hx] with y hy
    exact (classical_biaxial_poisson_screened_system a ε hU.1
      (hQ.of_le (WithTop.coe_le_coe.mpr le_top)) hy (hEq y hy)).1
  have hAop : ‖fderiv ℝ A (f x)‖ ≤ B :=
    (hL (f x) (mem_closedBall_zero_iff.mpr hfx)).trans (le_max_right _ _)
  have hDerivative := ((hA.differentiable (by simp) (f x)).hasFDerivAt.comp x
    (((hf x hx).contDiffAt (hU.1.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt).fderiv
  have hDer : coordDeriv j (laplacian Q) x = (fderiv ℝ A (f x)) (coordDeriv j f x) :=
    DFunLike.congr_fun (hEq'.fderiv_eq.trans hDerivative) (axis j)
  rw [hDer]
  refine (ContinuousLinearMap.le_opNorm _ _).trans
    ((mul_le_mul hAop hDfx (norm_nonneg _) hB.le).trans ?_)
  have hR : (r-ρ)⁻¹ = 4*d⁻¹ := by
    dsimp only [r, ρ]
    field_simp [hd.ne']
    ring
  rw [hR]
  dsimp only [C]
  nlinarith only [mul_nonneg hB.le (mul_nonneg hM (inv_nonneg.mpr hd.le)), mul_nonneg hB.le hT.le]

private theorem smooth_coordDeriv_field
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q U) (i : Fin 3) :
    ContDiffOn ℝ ∞ (coordDeriv i Q) U :=
  (ContinuousLinearMap.apply ℝ S0 (axis i)).contDiff.comp_contDiffOn
    (hQ.fderiv_of_isOpen hU (le_of_eq (by simp)))

/-- A uniform half-Hölder bound on the actual gradient and the first
derivative of the Poisson source sharpen the interior estimate for the
square of every second derivative at the wall distance. -/
theorem exists_coordDeriv_twice_sq_bound_by_wall_distance
    (hEstimate : InteriorPoissonGradientEstimate)
    {U : Set Point} (hU : IsBoundedDomain U) (H A : ℝ) (hH : 0 ≤ H) (hA : 0 ≤ A) :
    ∃ C > (0 : ℝ), ∀ Q : Point → S0, ContDiffOn ℝ ∞ Q U →
      (∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin 3,
        ‖coordDeriv i Q x - coordDeriv i Q y‖ ≤ H * Real.sqrt (dist x y)) →
      (∀ x ∈ U, ∀ i : Fin 3,
        ‖coordDeriv i (laplacian Q) x‖ ≤ A * (1 + (Metric.infDist x (frontier U))⁻¹)) →
      ∀ x ∈ U, ∀ i j : Fin 3,
        ‖coordDeriv j (coordDeriv i Q) x‖ ^ 2 ≤ C * (1 + (Metric.infDist x (frontier U))⁻¹) := by
  obtain ⟨P, hP, hPoisson⟩ := hEstimate
  obtain ⟨R, hR, hWallR⟩ := exists_infDist_frontier_upper_bound U hU
  let C := 1 + (4*(P*H)^2 + 2*(P*A*(R+1))^2)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Q hQ hHold hSource x hx i j
  let d (y : Point) := Metric.infDist y (frontier U)
  let r := d x / 2
  have hd : 0 < d x := infDist_frontier_pos_of_mem_domain hU hx
  have hr : 0 < r := half_pos hd
  have hrR : r ≤ R := (half_lt_self hd).le.trans (hWallR x hx)
  have hBU : Metric.ball x r ⊆ U :=
    (Metric.ball_subset_ball (half_lt_self hd).le).trans (ball_infDist_frontier_subset_domain hU hx)
  let v (y : Point) := coordDeriv i Q y - coordDeriv i Q x
  let F (y : Point) : Tensor := (↑(coordDeriv i (laplacian Q) y) : Tensor)
  have hv : ContDiffOn ℝ 2 v (Metric.ball x r) :=
    (((smooth_coordDeriv_field hU.1 hQ i).of_le (WithTop.coe_le_coe.mpr le_top)).mono hBU).sub
      contDiffOn_const
  have hEq (y : Point) (hy : y ∈ Metric.ball x r) : (↑(laplacian v y) : Tensor) = F y := by
    change (↑(laplacian (fun z => coordDeriv i Q z - coordDeriv i Q x) y) : Tensor) =
      (↑(coordDeriv i (laplacian Q) y) : Tensor)
    rw [laplacian_sub_const, laplacian_coordDeriv_comm hU.1 hQ (hBU hy)]
  have hVal (y : Point) (hy : y ∈ Metric.ball x r) : ‖v y‖ ≤ H * Real.sqrt r :=
    (hHold y (hBU hy) x hx i).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hy.le) hH)
  have hForce (y : Point) (hy : y ∈ Metric.ball x r) : ‖F y‖ ≤ A * (1 + r⁻¹) := by
    have hDist : d x ≤ d y + dist x y := Metric.infDist_le_infDist_add_dist
    have hBall : dist x y < r := (dist_comm y x) ▸ hy
    have h : r ≤ d y := by dsimp only [r] at *; linarith only [hDist, hBall]
    exact (hSource y (hBU hy) i).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl ((inv_le_inv₀ (hr.trans_le h) hr).2 h)) hA)
  have hEst := hPoisson x r hr v F (H * Real.sqrt r) (A * (1 + r⁻¹)) hv hEq hVal hForce
  have hD : coordDeriv j v x = coordDeriv j (coordDeriv i Q) x :=
    DFunLike.congr_fun (fderiv_sub_const (𝕜 := ℝ) (x := x) (f := coordDeriv i Q) (coordDeriv i Q x)) (axis j)
  let k := ‖coordDeriv j (coordDeriv i Q) x‖
  have hk : 0 ≤ k := norm_nonneg _
  have hSmall : r * k ≤ P * (H * Real.sqrt r + r^2 * (A * (1 + r⁻¹))) := by
    apply (mul_le_mul_of_nonneg_left ?_ hr.le).trans hEst
    change ‖coordDeriv j (coordDeriv i Q) x‖ ≤ _
    rw [← hD]
    exact norm_classicalGradient_column_le_sqrt (ClassicalGradient v x) j
  have hRe : r^2 * (A * (1 + r⁻¹)) = A * (r+1) * r := by
    field_simp [hr.ne']
  rw [hRe] at hSmall
  have hRoot : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hRootSq : (Real.sqrt r)^2 = r := Real.sq_sqrt hr.le
  have hk' : k ≤ P*H / Real.sqrt r + P*A*(r+1) := by
    apply le_of_mul_le_mul_left _ hr
    have hs : r * (P*H / Real.sqrt r) = P*H*Real.sqrt r := by
      calc
        _ = (Real.sqrt r)^2 * (P*H / Real.sqrt r) :=
          congrArg (fun t : ℝ => t * (P*H / Real.sqrt r)) hRootSq.symm
        _ = _ := by field_simp [hRoot.ne']
    rw [mul_add, hs]
    nlinarith only [hSmall]
  have hMain := hk'.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (add_le_add hrR le_rfl) (mul_nonneg hP.le hA)))
  have hSq := pow_le_pow_left₀ hk hMain 2
  have h1 : (P*H / Real.sqrt r)^2 = (P*H)^2 / r := by rw [div_pow, hRootSq]
  have h2 : (P*H)^2 / r = 2*(P*H)^2 * (d x)⁻¹ := by
    dsimp only [r]
    field_simp [hd.ne']
  have hExpand : ((P*H / Real.sqrt r) + P*A*(R+1))^2 ≤
      2*(P*H / Real.sqrt r)^2 + 2*(P*A*(R+1))^2 := by
    nlinarith only [sq_nonneg (P*H / Real.sqrt r - P*A*(R+1))]
  have hAll := hSq.trans hExpand
  rw [h1, h2] at hAll
  change k^2 ≤ C * (1+(d x)⁻¹)
  dsimp only [C]
  nlinarith only [hAll, inv_nonneg.mpr hd.le, sq_nonneg (P*H), sq_nonneg (P*A*(R+1)),
    mul_nonneg (sq_nonneg (P*A*(R+1))) (inv_nonneg.mpr hd.le)]

private theorem exists_norm_laplacian_comp_bound_on_range
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F)
    (hf : ContDiff ℝ ∞ f) (M : ℝ) :
    ∃ L > (0 : ℝ), ∀ {U : Set Point}, IsOpen U → ∀ {g : Point → E},
      ContDiffOn ℝ 2 g U → ∀ x ∈ U, ‖g x‖ ≤ M →
        ‖laplacian (f ∘ g) x‖ ≤ L * (‖laplacian g x‖ + ∑ j, ‖coordDeriv j g x‖^2) := by
  letI : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)
  letI : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)
  let K := Metric.closedBall (0 : E) M
  have hg₁ : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hg₂ : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := (↑(⊤ : ℕ∞) : ℕ∞ω)) (by simp)).continuous_fderiv (by simp)
  obtain ⟨L₁, hL₁⟩ := (isCompact_closedBall (0 : E) M).exists_bound_of_continuousOn hg₁.continuousOn
  obtain ⟨L₂, hL₂⟩ := (isCompact_closedBall (0 : E) M).exists_bound_of_continuousOn hg₂.continuousOn
  let L := max 1 (max L₁ L₂)
  have hL : 0 < L := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨L, hL, ?_⟩
  intro U hU g hg x hx hRange
  have hxK : g x ∈ K := mem_closedBall_zero_iff.mpr hRange
  have h₁ : ‖fderiv ℝ f (g x)‖ ≤ L :=
    (hL₁ _ hxK).trans ((le_max_left _ _).trans (le_max_right _ _))
  have h₂ : ‖fderiv ℝ (fderiv ℝ f) (g x)‖ ≤ L :=
    (hL₂ _ hxK).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hPoint (j : Fin 3) :
      ‖(fderiv ℝ (fderiv ℝ f) (g x) (coordDeriv j g x)) (coordDeriv j g x)‖ ≤ L * ‖coordDeriv j g x‖^2 := by
    let B := fderiv ℝ (fderiv ℝ f) (g x)
    let v := coordDeriv j g x
    have hB : ‖B v‖ ≤ L*‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h₂ (norm_nonneg _))
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul_of_nonneg_right hB (norm_nonneg _)).trans_eq (by ring))
  rw [laplacian_comp_smooth_map hf hU hg hx]
  have hFirst : ‖(fderiv ℝ f (g x)) (laplacian g x)‖ ≤ L * ‖laplacian g x‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h₁ (norm_nonneg _))
  have hSecond : ‖∑ j, ((fderiv ℝ (fderiv ℝ f) (g x)) (coordDeriv j g x)) (coordDeriv j g x)‖ ≤
      L * (∑ j, ‖coordDeriv j g x‖^2) :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hPoint j)).trans_eq (Finset.mul_sum _ _ _).symm)
  exact ((norm_add_le _ _).trans (add_le_add hFirst hSecond)).trans_eq (mul_add _ _ _).symm

private theorem smooth_classicalGradient_field {U : Set Point} (hU : IsOpen U)
    {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q U) :
    ContDiffOn ℝ ∞ (ClassicalGradient Q) U := by
  rw [contDiffOn_pi]
  exact fun j => smooth_coordDeriv_field hU hQ j

private theorem laplacian_biaxialGradientSource_bound
    {U : Set Point} (hU : IsOpen U) {M A B : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C > (0 : ℝ), ∀ Q : Point → S0, ContDiffOn ℝ ∞ Q U →
      (∀ x ∈ U, ‖Q x‖ ≤ M ∧ ‖laplacian Q x‖ ≤ M ∧ Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ M) →
      ∀ x ∈ U, ∀ H : ℝ, 1 ≤ H →
      (∀ i, ‖coordDeriv i (laplacian Q) x‖ ≤ A * H) →
      (∀ i j, ‖coordDeriv j (coordDeriv i Q) x‖^2 ≤ B * H) →
      ‖laplacian (fun y => biaxialGradientSource (Q y, ClassicalGradient Q y)) x‖ ≤ C * H := by
  obtain ⟨L, hL, hComp⟩ := exists_norm_laplacian_comp_bound_on_range
    biaxialGradientSource contDiff_biaxialGradientSource M
  let C := L * (1 + M + A + 3*(M^2 + B))
  have hC : 0 < C := mul_pos hL (by positivity)
  refine ⟨C, hC, ?_⟩
  intro Q hQ hBase x hx H hH hPoi hSec
  let Y (y : Point) := (Q y, ClassicalGradient Q y)
  have hG : ContDiffOn ℝ ∞ (ClassicalGradient Q) U := smooth_classicalGradient_field hU hQ
  have hY : ContDiffOn ℝ ∞ Y U := hQ.prodMk hG
  have hY₂ : ContDiffOn ℝ 2 Y U := hY.of_le (WithTop.coe_le_coe.mpr le_top)
  have hYval : ‖Y x‖ ≤ M := by
    rw [Prod.norm_def]
    apply max_le (hBase x hx).1
    exact (pi_norm_le_iff_of_nonneg hM).2 fun j =>
      (norm_classicalGradient_column_le_sqrt (ClassicalGradient Q x) j).trans (hBase x hx).2.2
  have hLap₁ : (laplacian Y x).1 = laplacian Q x :=
    (laplacian_compCLM hU hY₂ hx (ContinuousLinearMap.fst ℝ S0 Gradient)).symm
  have hLap₂ (i : Fin 3) : (laplacian Y x).2 i = coordDeriv i (laplacian Q) x := by
    let L := (ContinuousLinearMap.proj i : Gradient →L[ℝ] S0).comp
      (ContinuousLinearMap.snd ℝ S0 Gradient)
    exact (laplacian_compCLM hU hY₂ hx L).symm.trans (laplacian_coordDeriv_comm hU hQ hx i)
  have hD₁ (j : Fin 3) : (coordDeriv j Y x).1 = coordDeriv j Q x :=
    (coordDeriv_compCLM (ContinuousLinearMap.fst ℝ S0 Gradient)
      (((hY x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) j).symm
  have hD₂ (i j : Fin 3) : (coordDeriv j Y x).2 i = coordDeriv j (coordDeriv i Q) x := by
    let L := (ContinuousLinearMap.proj i : Gradient →L[ℝ] S0).comp
      (ContinuousLinearMap.snd ℝ S0 Gradient)
    exact (coordDeriv_compCLM L
      (((hY x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) j).symm
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hLnorm : ‖laplacian Y x‖ ≤ M + A*H := by
    rw [Prod.norm_def, hLap₁]
    apply max_le ((hBase x hx).2.1.trans (le_add_of_nonneg_right (mul_nonneg hA hH₀)))
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ M + A*H)).2
    intro i
    rw [hLap₂]
    exact (hPoi i).trans (le_add_of_nonneg_left hM)
  have hS (j : Fin 3) : ‖coordDeriv j Y x‖^2 ≤ M^2 + B*H := by
    have hR : 0 ≤ M^2+B*H := by positivity
    have hZ : ‖coordDeriv j Y x‖ ≤ Real.sqrt (M^2+B*H) := by
      rw [Prod.norm_def,hD₁]
      apply max_le
      · apply Real.le_sqrt_of_sq_le
        have hJ := (norm_classicalGradient_column_le_sqrt (ClassicalGradient Q x) j).trans (hBase x hx).2.2
        exact (pow_le_pow_left₀ (norm_nonneg _) hJ 2).trans (le_add_of_nonneg_right (mul_nonneg hB hH₀))
      · apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
        intro i
        rw [hD₂]
        exact Real.le_sqrt_of_sq_le ((hSec i j).trans (le_add_of_nonneg_left (sq_nonneg M)))
    exact (pow_le_pow_left₀ (norm_nonneg _) hZ 2).trans_eq (Real.sq_sqrt hR)
  have hSum : (∑ j : Fin 3, ‖coordDeriv j Y x‖^2) ≤ 3*(M^2+B*H) :=
    (Finset.sum_le_sum (fun j _ => hS j)).trans_eq (by simp [mul_add])
  change ‖laplacian (biaxialGradientSource ∘ Y) x‖ ≤ _
  refine (hComp hU hY₂ x hx hYval).trans
    ((mul_le_mul_of_nonneg_left (add_le_add hLnorm hSum) hL.le).trans ?_)
  dsimp only [C]
  rw [mul_assoc L (1+M+A+3*(M^2+B)) H]
  apply mul_le_mul_of_nonneg_left _ hL.le
  nlinarith only [hH, hH₀, mul_le_mul_of_nonneg_left hH hM,
    mul_le_mul_of_nonneg_left hH (sq_nonneg M)]

private theorem biaxial_gradient_source_scalar_components {U : Set Point} (hU : IsOpen U)
    {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q U) :
    let G := fun y => gradientNormSq (ClassicalGradient Q y)
    let S := fun y => cubicGradientContraction (Q y) (ClassicalGradient Q y)
    let Z := fun y => biaxialGradientSource (Q y, ClassicalGradient Q y)
    ContDiffOn ℝ ∞ G U ∧ ContDiffOn ℝ ∞ S U ∧
      ∀ x ∈ U, |laplacian G x| ≤ ‖laplacian Z x‖ ∧ |laplacian S x| ≤ ‖laplacian Z x‖ := by
  intro G S Z
  let L₁ : ScalarDefectPair →L[ℝ] ℝ := (-1/2 : ℝ) • ContinuousLinearMap.proj 0
  let L₂ : ScalarDefectPair →L[ℝ] ℝ := (-1/6 : ℝ) • ContinuousLinearMap.proj 1
  have hZ : ContDiffOn ℝ ∞ Z U :=
    contDiff_biaxialGradientSource.comp_contDiffOn (hQ.prodMk (smooth_classicalGradient_field hU hQ))
  have hZ₂ : ContDiffOn ℝ 2 Z U := hZ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hG : G = fun x => L₁ (Z x) := by
    funext x
    change gradientNormSq (ClassicalGradient Q x) = (-1/2 : ℝ) * (-2 * gradientNormSq (ClassicalGradient Q x))
    ring
  have hS : S = fun x => L₂ (Z x) := by
    funext x
    change cubicGradientContraction (Q x) (ClassicalGradient Q x) =
      (-1/6 : ℝ) * (-6 * cubicGradientContraction (Q x) (ClassicalGradient Q x))
    ring
  rw [hG, hS]
  refine ⟨L₁.contDiff.comp_contDiffOn hZ, L₂.contDiff.comp_contDiffOn hZ, ?_⟩
  intro x hx
  rw [laplacian_compCLM hU hZ₂ hx L₁, laplacian_compCLM hU hZ₂ hx L₂]
  constructor
  · change |(-1/2 : ℝ) * laplacian Z x 0| ≤ ‖laplacian Z x‖
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (by norm_num : |(-1/2 : ℝ)| ≤ 1) (abs_nonneg _)).trans
      (by simpa only [one_mul, Real.norm_eq_abs] using norm_le_pi_norm (laplacian Z x) 0)
  · change |(-1/6 : ℝ) * laplacian Z x 1| ≤ ‖laplacian Z x‖
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (by norm_num : |(-1/6 : ℝ)| ≤ 1) (abs_nonneg _)).trans
      (by simpa only [one_mul, Real.norm_eq_abs] using norm_le_pi_norm (laplacian Z x) 1)

private theorem scaled_defects_and_gradient_adjusted_bounds
    (a : BulkCoefficients) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C > (0 : ℝ), ∀ (ε : ElasticScale) (Q : Point → S0) (x : Point),
      ‖Q x‖ ≤ M → |scaledNormDefect a ε (Q x)| ≤ M → |scaledCubicTrace a ε (Q x)| ≤ M →
      Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ M →
      |adjustedNormDefect a ε Q x| ≤ C ∧ |adjustedCubicDefect a ε Q x| ≤ C := by
  obtain ⟨T, hT⟩ := (isCompact_closedBall (0 : S0 × Gradient) M).exists_bound_of_continuousOn
    contDiff_biaxialGradientSource.continuous.continuousOn
  let k := 1/(2*bulkRadialCoefficient a*vacuumRadius a^2)
  let j := 3/(a.a6'*vacuumRadius a^4)
  let D := max T 0
  refine ⟨1 + M + (|k| + |j|) * D, by dsimp only [D]; positivity, ?_⟩
  intro ε Q x hQ hNorm hTrace hGrad
  let Y := (Q x, ClassicalGradient Q x)
  have hG : ‖ClassicalGradient Q x‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).2 fun i =>
    (norm_classicalGradient_column_le_sqrt (ClassicalGradient Q x) i).trans hGrad
  have hY : Y ∈ Metric.closedBall (0 : S0 × Gradient) M :=
    mem_closedBall_zero_iff.mpr (max_le hQ hG)
  have hSrc : ‖biaxialGradientSource Y‖ ≤ D := (hT Y hY).trans (le_max_left _ _)
  have h0 : |-2 * gradientNormSq (ClassicalGradient Q x)| ≤ D :=
    (norm_le_pi_norm (biaxialGradientSource Y) 0).trans hSrc
  have h1 : |-6 * cubicGradientContraction (Q x) (ClassicalGradient Q x)| ≤ D :=
    (norm_le_pi_norm (biaxialGradientSource Y) 1).trans hSrc
  rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h0
  rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)] at h1
  have hG' : |gradientNormSq (ClassicalGradient Q x)| ≤ D := by linarith only [h0, abs_nonneg (gradientNormSq (ClassicalGradient Q x))]
  have hS' : |cubicGradientContraction (Q x) (ClassicalGradient Q x)| ≤ D := by
    linarith only [h1, abs_nonneg (cubicGradientContraction (Q x) (ClassicalGradient Q x))]
  constructor
  · change |scaledNormDefect a ε (Q x) + k * gradientNormSq (ClassicalGradient Q x)| ≤ _
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    exact (add_le_add hNorm (mul_le_mul_of_nonneg_left hG' (abs_nonneg k))).trans
      (by nlinarith only [mul_nonneg (abs_nonneg j) (le_max_right T 0)])
  · change |scaledCubicTrace a ε (Q x) + j * cubicGradientContraction (Q x) (ClassicalGradient Q x)| ≤ _
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    exact (add_le_add hTrace (mul_le_mul_of_nonneg_left hS' (abs_nonneg j))).trans
      (by nlinarith only [mul_nonneg (abs_nonneg k) (le_max_right T 0)])

/-- The exact adjusted scalar forcings grow at most as the inverse wall
distance. The half-Hölder bound is used only for the second derivative
terms and the \(C^1\) interior defect bound controls the other terms. -/
theorem exists_adjusted_sources_bound_by_wall_distance
    (a : BulkCoefficients) (hEstimate : InteriorPoissonGradientEstimate)
    {U : Set Point} (hU : IsBoundedDomain U) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H) :
    ∃ C > (0 : ℝ), ∀ (ε : ElasticScale) (Q : Point → S0), ContDiffOn ℝ ∞ Q U →
      (∀ x ∈ U, (ε : ℝ)^2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) →
      (∀ x ∈ U, ‖Q x‖ ≤ M ∧ ‖laplacian Q x‖ ≤ M ∧ |scaledNormDefect a ε (Q x)| ≤ M ∧
        |scaledCubicTrace a ε (Q x)| ≤ M ∧ Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ M) →
      (∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin 3,
        ‖coordDeriv i Q x - coordDeriv i Q y‖ ≤ H * Real.sqrt (dist x y)) →
      ∀ x ∈ U,
        |adjustedNormDefectSource a ε Q x| ≤ C * (1 + (Metric.infDist x (frontier U))⁻¹) ∧
        |adjustedCubicDefectSource a ε Q x| ≤ C * (1 + (Metric.infDist x (frontier U))⁻¹) := by
  obtain ⟨A, hA, hDX⟩ := exists_coordDeriv_laplacian_bound_by_wall_distance a hEstimate M hM
  obtain ⟨B, hB, hDX₂⟩ := exists_coordDeriv_twice_sq_bound_by_wall_distance hEstimate hU H A hH hA.le
  obtain ⟨L, hL, hBound⟩ := laplacian_biaxialGradientSource_bound hU.1 hM hA.le hB.le
  let R := max 1 M
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℝ × ScalarDefectPair) R).exists_bound_of_continuousOn
    (contDiff_biaxialDefectCorrection a).continuous.continuousOn
  let C₁ := max C₀ 0
  let k := 1/(2*bulkRadialCoefficient a*vacuumRadius a^2)
  let j := 3/(a.a6'*vacuumRadius a^4)
  let C := 1 + (|k| + |j|) * L + C₁
  refine ⟨C, by dsimp only [C,C₁]; positivity, ?_⟩
  intro ε Q hQ hEq hData hHolder x hx
  let d := Metric.infDist x (frontier U)
  let X := 1 + d⁻¹
  have hX : 1 ≤ X := le_add_of_nonneg_right (inv_nonneg.mpr Metric.infDist_nonneg)
  have hX₀ : 0 ≤ X := zero_le_one.trans hX
  have hLapD := hDX ε hU Q hQ hEq
    (fun y hy => ⟨(hData y hy).1, (hData y hy).2.2⟩)
  have hGrad₂ := hDX₂ Q hQ hHolder hLapD
  have hSource := hBound Q hQ
    (fun y hy => ⟨(hData y hy).1, (hData y hy).2.1, (hData y hy).2.2.2.2⟩)
    x hx X hX (hLapD x hx) (hGrad₂ x hx)
  obtain ⟨_, _, hGL⟩ := biaxial_gradient_source_scalar_components hU.1 hQ
  let Z := ((ε : ℝ)^2, scalarDefectPair a ε (Q x))
  have hZ : Z ∈ Metric.closedBall (0 : ℝ × ScalarDefectPair) R := by
    apply mem_closedBall_zero_iff.mpr
    rw [Prod.norm_def]
    apply max_le
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hE : (ε : ℝ)^2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ ε.2.1.le ε.2.2.le 2
      exact hE.trans (le_max_left _ _)
    · apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans (le_max_left _ _))).2
      intro i
      fin_cases i
      · exact (hData x hx).2.2.1.trans (le_max_right _ _)
      · exact (hData x hx).2.2.2.1.trans (le_max_right _ _)
  have hCorr (i : Fin 2) : |biaxialDefectCorrection a Z i| ≤ C₁ :=
    (norm_le_pi_norm (biaxialDefectCorrection a Z) i).trans ((hC₀ Z hZ).trans (le_max_left _ _))
  have hNormDef : adjustedNormDefectSource a ε Q x =
      -k * laplacian (fun y => gradientNormSq (ClassicalGradient Q y)) x + biaxialDefectCorrection a Z 0 := by
    let h := scaledNormDefect a ε (Q x)
    let t := scaledCubicTrace a ε (Q x)
    let E := (ε : ℝ)^2
    let L := laplacian (fun y => gradientNormSq (ClassicalGradient Q y)) x
    let b := 2 * bulkRadialCoefficient a + 4 * a.a6 * vacuumRadius a ^ 2
    change 0-k*L-b*h^2-2*a.a6*E*h^3-2*a.a6'*t^2 =
      -k*L + -(b*h^2+2*a.a6*E*h^3+2*a.a6'*t^2)
    ring
  have hCubeDef : adjustedCubicDefectSource a ε Q x =
      -j * laplacian (fun y => cubicGradientContraction (Q y) (ClassicalGradient Q y)) x +
        biaxialDefectCorrection a Z 1 := by
    let h := scaledNormDefect a ε (Q x)
    let t := scaledCubicTrace a ε (Q x)
    let E := (ε : ℝ)^2
    let L := laplacian (fun y => cubicGradientContraction (Q y) (ClassicalGradient Q y)) x
    let b := 3 * bulkRadialCoefficient a + 2 * a.a6' * vacuumRadius a ^ 2
    let b' := 3 * a.a6 + a.a6' / 2
    change 0-j*L-b*h*t-E*b'*h^2*t = -j*L + -(b*h*t+E*b'*h^2*t)
    ring
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  constructor
  · rw [hNormDef]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_neg]
    refine (add_le_add (mul_le_mul_of_nonneg_left ((hGL x hx).1.trans hSource) (abs_nonneg _)) (hCorr 0)).trans ?_
    dsimp only [C]
    nlinarith only [hX, mul_le_mul_of_nonneg_left hX hC₁, mul_nonneg (abs_nonneg j) (mul_nonneg hL.le hX₀)]
  · rw [hCubeDef]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_neg]
    refine (add_le_add (mul_le_mul_of_nonneg_left ((hGL x hx).2.trans hSource) (abs_nonneg _)) (hCorr 1)).trans ?_
    dsimp only [C]
    nlinarith only [hX, mul_le_mul_of_nonneg_left hX hC₁, mul_nonneg (abs_nonneg k) (mul_nonneg hL.le hX₀)]

private theorem exists_screened_solution_bound_by_wall_profile
    {U : Set Point} (hU : IsBoundedDomain U) (m D M : ℝ)
    (hm : 0 < m) (hD : 0 ≤ D) (hM : 0 ≤ M) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ∀ (w F : Point → ℝ), ContDiffOn ℝ 2 w U →
      (∀ x ∈ U, |w x| ≤ M) →
      (∀ x ∈ U, -ε^2 * laplacian w x + m*w x = ε^2 * F x) →
      (∀ x ∈ U, |F x| ≤ D * (1 + (Metric.infDist x (frontier U))⁻¹)) →
      ∀ x ∈ U, |w x| ≤ C * (ε^2 / Metric.infDist x (frontier U) +
        Real.exp (-c * Metric.infDist x (frontier U) / ε)) := by
  obtain ⟨ℓ, B, hℓ, hB, hScreened⟩ := exists_exponential_center_bound_for_screened_equation m hm
  obtain ⟨R, hR, hRbound⟩ := exists_infDist_frontier_upper_bound U hU
  let c := ℓ / 2
  let K := D*(R+2)/m
  let C := 1 + K + B*M
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨c, C, half_pos hℓ, by dsimp only [C]; positivity, ?_⟩
  intro ε hε w F hw hW hEq hForce x hx
  let d (y : Point) := Metric.infDist y (frontier U)
  let r := d x / 2
  have hd : 0 < d x := infDist_frontier_pos_of_mem_domain hU hx
  have hr : 0 < r := half_pos hd
  have hCl : closure (Metric.ball x r) ⊆ U := by
    rw [closure_ball x hr.ne']
    exact (Metric.closedBall_subset_ball (half_lt_self hd)).trans (ball_infDist_frontier_subset_domain hU hx)
  have hBU : Metric.ball x r ⊆ U := subset_closure.trans hCl
  have hF (y : Point) (hy : y ∈ Metric.ball x r) : |F y| ≤ D*(1+r⁻¹) := by
    have hDxy : d x ≤ d y + dist x y := Metric.infDist_le_infDist_add_dist
    have hDist : dist x y < r := (dist_comm y x) ▸ hy
    have hRxy : r ≤ d y := by dsimp only [r] at *; linarith only [hDxy, hDist]
    exact (hForce y (hBU hy)).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl ((inv_le_inv₀ (hr.trans_le hRxy) hr).2 hRxy)) hD)
  have hScreen := hScreened ε r (D*(1+r⁻¹)) M hε hr (by positivity) hM x w
    (hw.mono hBU) (hw.continuousOn.mono hCl) (fun y hy => hW y (hCl hy)) (fun y hy => by
      rw [hEq y (hBU hy), abs_mul, abs_of_nonneg (sq_nonneg ε)]
      exact mul_le_mul_of_nonneg_left (hF y hy) (sq_nonneg ε))
  have hForceTerm : ε^2*(D*(1+r⁻¹))/m ≤ K * (ε^2 / d x) := by
    have hInv : r⁻¹ = 2 * (d x)⁻¹ := by dsimp only [r]; field_simp [hd.ne']
    have hD' : 1 + r⁻¹ ≤ (R+2)*(d x)⁻¹ := by
      rw [hInv]
      have hD₀ := mul_le_mul_of_nonneg_right (hRbound x hx) (inv_nonneg.mpr hd.le)
      rw [show d x * (d x)⁻¹ = 1 from mul_inv_cancel₀ hd.ne'] at hD₀
      nlinarith only [hD₀]
    calc
      _ ≤ ε^2 * (D*((R+2)*(d x)⁻¹)) / m := by
        gcongr
      _ = _ := by dsimp only [K]; ring
  have hExp : Real.exp (-ℓ*r/ε) = Real.exp (-c*d x/ε) :=
    congrArg Real.exp (by dsimp only [r,c]; ring)
  rw [hExp] at hScreen
  refine hScreen.trans ((add_le_add hForceTerm le_rfl).trans ?_)
  rw [mul_add C]
  exact add_le_add (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith only [mul_nonneg hB.le hM])
    (div_nonneg (sq_nonneg ε) hd.le)) (mul_le_mul_of_nonneg_right
      (by dsimp only [C]; linarith only [hK]) (Real.exp_nonneg _))

/-- The projected residual used in the first correction satisfies the
inverse wall distance and exponential boundary-layer bound, with uniform
material, domain, and gradient data. -/
theorem exists_projectedHarmonicRemainder_wall_profile
    (a : BulkCoefficients) (hEstimate : InteriorPoissonGradientEstimate)
    {U : Set Point} (hU : IsBoundedDomain U) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ε : ElasticScale) (Q : Point → S0), ContDiffOn ℝ ∞ Q U →
      (∀ x ∈ U, (ε : ℝ)^2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) →
      (∀ x ∈ U, ‖Q x‖ ≤ M ∧ ‖laplacian Q x‖ ≤ M ∧ |scaledNormDefect a ε (Q x)| ≤ M ∧
        |scaledCubicTrace a ε (Q x)| ≤ M ∧ Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ M) →
      (∀ x ∈ U, ∀ y ∈ U, ∀ i : Fin 3,
        ‖coordDeriv i Q x - coordDeriv i Q y‖ ≤ H * Real.sqrt (dist x y)) →
      ∀ x ∈ U, ‖projectedHarmonicRemainder a ε Q x‖ ≤ C * ((ε : ℝ)^2 / Metric.infDist x (frontier U) +
        Real.exp (-c * Metric.infDist x (frontier U) / ε)) := by
  obtain ⟨D, hD, hSource⟩ := exists_adjusted_sources_bound_by_wall_distance a hEstimate hU M H hM hH
  obtain ⟨E, hE, hAdjusted⟩ := scaled_defects_and_gradient_adjusted_bounds a M hM
  obtain ⟨c₁, C₁, hc₁, hC₁, hNorm⟩ := exists_screened_solution_bound_by_wall_profile hU
    (bulkRadialMass a) D E (bulkRadialMass_pos a) hD.le hE.le
  obtain ⟨c₂, C₂, hc₂, hC₂, hCube⟩ := exists_screened_solution_bound_by_wall_profile hU
    (bulkBiaxialMass a) D E (bulkBiaxialMass_pos a) hD.le hE.le
  obtain ⟨R, hR, hDist⟩ := exists_infDist_frontier_upper_bound U hU
  obtain ⟨S₀, hS₀⟩ := (isCompact_closedBall (0 : S0) M).exists_bound_of_continuousOn
    contDiff_traceFreeSquare.continuous.continuousOn
  let S := max S₀ 0
  let c := min c₁ c₂
  let C := (bulkRadialCoefficient a) * C₁ * M + a.a6 * M^3*R + a.a6'*C₂*S + 1
  have hp := bulkRadialCoefficient_pos a
  have ha6 := a.a6_pos
  have ha6' := a.a6'_pos
  have hS : 0 ≤ S := le_max_right _ _
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨c, C, lt_min hc₁ hc₂, hC, ?_⟩
  intro ε Q hQ hEq hData hHold x hx
  let d := Metric.infDist x (frontier U)
  let B := (ε : ℝ)^2/d + Real.exp (-c*d/ε)
  have hd : 0 < d := infDist_frontier_pos_of_mem_domain hU hx
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let u := adjustedNormDefect a ε Q
  let v := adjustedCubicDefect a ε Q
  let z := scalarDefectPair a ε ∘ Q
  have hZ : ContDiffOn ℝ ∞ z U := (contDiff_scalarDefectPair a ε).comp_contDiffOn hQ
  obtain ⟨hG, hK, _⟩ := biaxial_gradient_source_scalar_components hU.1 hQ
  have hh : ContDiffOn ℝ ∞ (scaledNormDefect a ε ∘ Q) U :=
    (ContinuousLinearMap.proj 0 : ScalarDefectPair →L[ℝ] ℝ).contDiff.comp_contDiffOn hZ
  have ht : ContDiffOn ℝ ∞ (scaledCubicTrace a ε ∘ Q) U :=
    (ContinuousLinearMap.proj 1 : ScalarDefectPair →L[ℝ] ℝ).contDiff.comp_contDiffOn hZ
  have hu₂ : ContDiffOn ℝ 2 u U :=
    (hh.add (contDiffOn_const.mul hG)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hv₂ : ContDiffOn ℝ 2 v U :=
    (ht.add (contDiffOn_const.mul hK)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hA (y : Point) (hy : y ∈ U) : |u y| ≤ E ∧ |v y| ≤ E :=
    hAdjusted ε Q y (hData y hy).1 (hData y hy).2.2.1 (hData y hy).2.2.2.1 (hData y hy).2.2.2.2
  have hSour := hSource ε Q hQ hEq hData hHold
  have hu := hNorm ε ε.2.1 u (adjustedNormDefectSource a ε Q) hu₂ (fun y hy => (hA y hy).1)
    (fun y hy => adjustedNormDefect_screened_equation a ε hU.1 (hQ.of_le (WithTop.coe_le_coe.mpr le_top)) hy (hEq y hy))
    (fun y hy => (hSour y hy).1) x hx
  have hv' := hCube ε ε.2.1 v (adjustedCubicDefectSource a ε Q) hv₂ (fun y hy => (hA y hy).2)
    (fun y hy => adjustedCubicDefect_screened_equation a ε hU.1 (hQ.of_le (WithTop.coe_le_coe.mpr le_top)) hy (hEq y hy))
    (fun y hy => (hSour y hy).2) x hx
  have hExp (k : ℝ) (hk : c ≤ k) : Real.exp (-k*d/ε) ≤ Real.exp (-c*d/ε) :=
    Real.exp_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (neg_le_neg hk) hd.le) ε.2.1.le)
  have huB : |u x| ≤ C₁*B := hu.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (hExp c₁ (min_le_left _ _))) hC₁.le)
  have hvB : |v x| ≤ C₂*B := hv'.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (hExp c₂ (min_le_right _ _))) hC₂.le)
  have hSq : ‖traceFreeSquare (Q x)‖ ≤ S :=
    (hS₀ _ (mem_closedBall_zero_iff.mpr (hData x hx).1)).trans (le_max_left _ _)
  have hεB : (ε : ℝ)^2 ≤ R*B := by
    calc
      _ = d*((ε : ℝ)^2/d) := by field_simp [hd.ne']
      _ ≤ R*((ε : ℝ)^2/d) := mul_le_mul_of_nonneg_right (hDist x hx) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.exp_nonneg _)) hR.le
  have hUterm : ‖(bulkRadialCoefficient a * u x) • Q x‖ ≤ (bulkRadialCoefficient a)*C₁*M*B := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hp.le]
    exact ((mul_le_mul
      (mul_le_mul_of_nonneg_left huB hp.le) (hData x hx).1 (norm_nonneg _) (by positivity))).trans_eq (by ring)
  have hVterm : ‖(a.a6' * v x) • traceFreeSquare (Q x)‖ ≤ a.a6'*C₂*S*B := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg a.a6'_pos.le]
    exact ((mul_le_mul
      (mul_le_mul_of_nonneg_left hvB a.a6'_pos.le) hSq (norm_nonneg _)
      (mul_nonneg a.a6'_pos.le (mul_nonneg hC₂.le hB)))).trans_eq (by ring)
  have hRadTerm : ‖(a.a6*(ε : ℝ)^2*(scaledNormDefect a ε (Q x))^2) • Q x‖ ≤ a.a6*M^3*R*B := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have hNorm := pow_le_pow_left₀ (abs_nonneg _) (hData x hx).2.2.1 2
    rw [sq_abs] at hNorm
    exact (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hεB a.a6_pos.le) hNorm (sq_nonneg _)
      (by positivity)) (hData x hx).1 (norm_nonneg _) (by positivity)).trans_eq (by ring)
  change ‖(bulkRadialCoefficient a*u x) • Q x +
    (a.a6*(ε : ℝ)^2*(scaledNormDefect a ε (Q x))^2) • Q x +
    (a.a6'*v x) • traceFreeSquare (Q x)‖ ≤ C*B
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hUterm hRadTerm)) hVterm) |>.trans ?_
  dsimp only [C]
  nlinarith only [hB]

end Thesis

end
