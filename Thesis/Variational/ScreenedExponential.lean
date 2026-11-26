module

public import Thesis.Variational.ScaledDefectBound
import Thesis.Variational.BoundarySubsolution
import Thesis.Variational.BoundaryBarrier

/-! A positive mass gives exponential decay from the spherical boundary. -/

public section

open Set
open scoped BigOperators ContDiff Topology RealInnerProductSpace Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem coordDeriv_radial_square (x y : Point) (j : Fin 3) :
    coordDeriv j (fun z : Point => ‖z-x‖^2) y = 2 * (y-x) j := by
  have h := ((hasFDerivAt_id y).sub_const x).norm_sq
  have hD := DFunLike.congr_fun h.fderiv (axis j)
  have h₁ : coordDeriv j (fun z : Point => ‖z-x‖^2) y = 2 * inner ℝ (y-x) (axis j) := by
    simpa only [id_eq, coordDeriv, ContinuousLinearMap.comp_id, smul_apply, innerSL_apply_apply,
      smul_eq_mul, two_nsmul, add_apply, two_mul] using hD
  rw [h₁]
  change 2 * inner ℝ (y-x) (EuclideanSpace.single j 1) = _
  rw [EuclideanSpace.inner_single_right]
  change 2 * (1 * star ((y-x) j)) = _
  rw [star_trivial, one_mul]

private theorem radial_exponential_laplacian (x y : Point) (R k : ℝ) :
    laplacian (fun z => Real.exp (k * (‖z-x‖^2 - R^2))) y =
      Real.exp (k * (‖y-x‖^2 - R^2)) * (6*k + 4*k^2*‖y-x‖^2) := by
  let p (z : Point) := ‖z-x‖^2 - R^2
  let u (z : Point) := k * p z
  have hp : ContDiff ℝ 2 p := ((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const
  have hu : ContDiff ℝ 2 u := contDiff_const.mul hp
  have hLap : laplacian u y = 6*k := by
    change laplacian (fun z => k • p z) y = _
    rw [laplacian_const_smul isOpen_univ hp.contDiffOn (mem_univ y) k, laplacian_sub_const,
      laplacian_norm_sub_sq, smul_eq_mul, mul_comm]
  have hG (j : Fin 3) : coordDeriv j u y = k * (2 * (y-x) j) := by
    have h := coordDeriv_compCLM (k • ContinuousLinearMap.id ℝ ℝ)
      (hp.differentiable two_ne_zero y) j
    have hP : coordDeriv j p y = coordDeriv j (fun z : Point => ‖z-x‖^2) y :=
      DFunLike.congr_fun (fderiv_sub_const (𝕜 := ℝ) (f := fun z : Point => ‖z - x‖^2)
        (x := y) (R^2)) (axis j)
    change coordDeriv j u y = k * coordDeriv j p y at h
    rw [h, hP, coordDeriv_radial_square]
  have hSum : (∑ j, (coordDeriv j u y)^2) = 4*k^2*‖y-x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hG]
    ring
  have h := laplacian_real_comp_smooth Real.contDiff_exp isOpen_univ hu.contDiffOn (mem_univ y)
  rw [Real.deriv_exp, Real.deriv_exp, hLap, hSum] at h
  exact h.trans (by dsimp only [u, p]; ring)

private theorem radial_exponential_is_supersolution
    {m ℓ ε R : ℝ} (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) (hMass : 10*ℓ ≤ m)
    (hε : 0 < ε) (hR : 0 < R) (hεR : ε ≤ R) (x : Point) :
    let Φ (z : Point) := Real.exp (ℓ / (ε*R) * (‖z-x‖^2 - R^2))
    ∀ y ∈ Metric.ball x R, 0 ≤ -ε^2 * laplacian Φ y + m * Φ y := by
  intro Φ y hy
  let k := ℓ/(ε*R)
  have hk : 0 ≤ k := div_nonneg hℓ.le (mul_nonneg hε.le hR.le)
  have hDist : ‖y-x‖ ≤ R := le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)
  have h₁ : ε^2 * (6*k) ≤ 6*ℓ := by
    calc
      _ = (6*ℓ) * (ε/R) := by dsimp only [k]; field_simp [hε.ne', hR.ne']
      _ ≤ (6*ℓ) * 1 := mul_le_mul_of_nonneg_left ((div_le_one hR).2 hεR) (by positivity)
      _ = _ := mul_one _
  have h₂ : ε^2 * (4*k^2*‖y-x‖^2) ≤ 4*ℓ := by
    calc
      _ ≤ ε^2 * (4*k^2*R^2) := by gcongr
      _ = 4*ℓ^2 := by dsimp only [k]; field_simp [hε.ne', hR.ne']
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hℓ₁ hℓ.le]
  have hScale : ε^2*(6*k+4*k^2*‖y-x‖^2) ≤ m := by
    rw [mul_add]
    linarith only [h₁, h₂, hMass]
  have hLp : laplacian Φ y = Φ y * (6*k+4*k^2*‖y-x‖^2) :=
    radial_exponential_laplacian x y R k
  have hΦ : 0 ≤ Φ y := Real.exp_nonneg _
  rw [hLp]
  nlinarith only [mul_le_mul_of_nonneg_right hScale hΦ]

private theorem exponential_comparison_one_side
    {m ℓ ε R F M : ℝ} (hm : 0 < m) (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) (hMass : 10*ℓ ≤ m)
    (hε : 0 < ε) (hR : 0 < R) (hεR : ε ≤ R) (hF : 0 ≤ F) (hM : 0 ≤ M)
    (x : Point) {w : Point → ℝ} (hw : ContDiffOn ℝ 2 w (Metric.ball x R))
    (hwC : ContinuousOn w (closure (Metric.ball x R)))
    (hBound : ∀ y ∈ Metric.sphere x R, w y ≤ M)
    (hEq : ∀ y ∈ Metric.ball x R, -ε^2 * laplacian w y + m*w y ≤ ε^2*F) :
    w x ≤ ε^2*F/m + M * Real.exp (-ℓ*R/ε) := by
  let k := ℓ/(ε*R)
  let Φ (y : Point) := Real.exp (k * (‖y-x‖^2 - R^2))
  let K := ε^2*F/m
  let B := Metric.ball x R
  let v (y : Point) := w y - K - M • Φ y
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hΦ₂ : ContDiff ℝ 2 Φ :=
    Real.contDiff_exp.comp (contDiff_const.mul (((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const))
  have hv₂ : ContDiffOn ℝ 2 v B := (hw.sub contDiffOn_const).sub (hΦ₂.contDiffOn.const_smul M)
  have hvC : ContinuousOn v (closure B) := (hwC.sub continuousOn_const).sub
    (hΦ₂.continuous.continuousOn.const_smul M)
  have hVwall (y : Point) (hy : y ∈ frontier B) : v y ≤ 0 := by
    have hS : y ∈ Metric.sphere x R := (frontier_ball x hR.ne') ▸ hy
    have hD : ‖y-x‖ = R := (dist_eq_norm y x).symm.trans (Metric.mem_sphere.mp hS)
    have hΦ : Φ y = 1 := by simp only [Φ, hD, sub_self, mul_zero, Real.exp_zero]
    change w y - K - M • Φ y ≤ 0
    rw [hΦ, smul_eq_mul, mul_one]
    linarith only [hBound y hS, hK]
  have hP (y : Point) (hy : y ∈ B) : -laplacian v y + (m/ε^2) * v y ≤ (m/ε^2) * 0 := by
    have hLap : laplacian v y = laplacian w y - M * laplacian Φ y := by
      change laplacian (fun z => (w z - K) - M • Φ z) y = _
      rw [laplacian_sub_of_contDiffOn Metric.isOpen_ball (hw.sub contDiffOn_const)
        (hΦ₂.contDiffOn.const_smul M) hy, laplacian_sub_const,
        laplacian_const_smul Metric.isOpen_ball hΦ₂.contDiffOn hy M, smul_eq_mul]
    have hSup := radial_exponential_is_supersolution hℓ hℓ₁ hMass hε hR hεR x y hy
    have hMul := mul_nonneg hM hSup
    have hM₁ : m * K = ε^2 * F := by dsimp only [K]; field_simp [hm.ne']
    have hV : -ε^2 * laplacian v y + m * v y ≤ 0 := by
      rw [hLap]
      change -ε^2 * (laplacian w y - M * laplacian Φ y) + m*(w y-K-M * Φ y) ≤ 0
      change 0 ≤ M * (-ε^2 * laplacian Φ y + m * Φ y) at hMul
      nlinarith only [hEq y hy, hMul, hM₁]
    have hs : ε^2 * (m / ε^2) = m := by field_simp [hε.ne']
    have hProd : ε^2 * (-laplacian v y + (m/ε^2) * v y) ≤ ε^2 * ((m/ε^2) * 0) := by
      rw [mul_add, ← mul_assoc (ε^2) (m/ε^2), hs]
      simp only [mul_zero]
      nlinarith only [hV]
    exact le_of_mul_le_mul_left hProd (sq_pos_of_pos hε)
  have hComp := screened_subsolution_le_constant Metric.isOpen_ball
    (Metric.isBounded_ball.isCompact_closure) hvC hv₂ (div_pos hm (sq_pos_of_pos hε)) hVwall hP
    x (subset_closure (Metric.mem_ball_self hR))
  have hΦx : Φ x = Real.exp (-ℓ*R/ε) := by
    unfold Φ
    rw [sub_self, norm_zero, zero_pow two_ne_zero, zero_sub]
    congr 1
    dsimp only [k]
    field_simp [hε.ne', hR.ne']
  change w x - K - M • Φ x ≤ 0 at hComp
  rw [hΦx, smul_eq_mul] at hComp
  linarith only [hComp]

/-- A bounded solution of the positive-mass scalar equation at the center
of a ball has a uniform forcing term and an exponential boundary term. -/
theorem exists_exponential_center_bound_for_screened_equation (m : ℝ) (hm : 0 < m) :
    ∃ ℓ C : ℝ, 0 < ℓ ∧ 0 < C ∧ ∀ ε R F M : ℝ, 0 < ε → 0 < R → 0 ≤ F → 0 ≤ M →
      ∀ (x : Point) (w : Point → ℝ), ContDiffOn ℝ 2 w (Metric.ball x R) →
        ContinuousOn w (closure (Metric.ball x R)) →
        (∀ y ∈ closure (Metric.ball x R), |w y| ≤ M) →
        (∀ y ∈ Metric.ball x R, |-ε^2 * laplacian w y + m*w y| ≤ ε^2 * F) →
        |w x| ≤ ε^2*F/m + C*M*Real.exp (-ℓ*R/ε) := by
  let ℓ := m/(10*(1+m))
  have hℓ : 0 < ℓ := div_pos hm (by positivity)
  have hMass : 10*ℓ ≤ m := by
    dsimp only [ℓ]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 10*(1+m))]
    nlinarith only [sq_nonneg m]
  have hℓ₁ : ℓ ≤ 1 := by
    dsimp only [ℓ]
    apply (div_le_iff₀ (by positivity : 0 < 10*(1+m))).2
    linarith only [hm]
  refine ⟨ℓ, Real.exp ℓ, hℓ, Real.exp_pos _, ?_⟩
  intro ε R F M hε hR hF hM x w hw hwC hBound hEq
  have hC : 1 ≤ Real.exp ℓ := Real.one_le_exp_iff.mpr hℓ.le
  by_cases hεR : ε ≤ R
  · have hWall (y : Point) (hy : y ∈ Metric.sphere x R) : |w y| ≤ M :=
      hBound y ((closure_ball x hR.ne').symm ▸ Metric.sphere_subset_closedBall hy)
    have hPos := exponential_comparison_one_side hm hℓ hℓ₁ hMass hε hR hεR hF hM x hw hwC
      (fun y hy => (le_abs_self _).trans (hWall y hy)) (fun y hy => (le_abs_self _).trans (hEq y hy))
    have hNeg := exponential_comparison_one_side hm hℓ hℓ₁ hMass hε hR hεR hF hM x hw.neg hwC.neg
      (fun y hy => (neg_le_abs _).trans (hWall y hy)) ?_
    · apply (abs_le.mpr ⟨by linarith only [hNeg], hPos⟩).trans
      apply add_le_add le_rfl
      have hCM : M ≤ Real.exp ℓ * M := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hM
      exact mul_le_mul_of_nonneg_right hCM (Real.exp_nonneg _)
    · intro y hy
      have hNegLap : laplacian (fun y => -w y) y = -laplacian w y := by
        have h := laplacian_const_smul Metric.isOpen_ball hw hy (-1 : ℝ)
        simpa only [neg_one_smul] using! h
      rw [hNegLap]
      linarith only [(neg_le_abs _).trans (hEq y hy)]
  · have hExp : 1 ≤ Real.exp ℓ * Real.exp (-ℓ*R/ε) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have hUnit : R/ε ≤ 1 := (div_le_one hε).2 (le_of_lt (lt_of_not_ge hεR))
      rw [mul_div_assoc]
      linarith only [mul_le_mul_of_nonneg_left hUnit hℓ.le]
    have hM' := hBound x (subset_closure (Metric.mem_ball_self hR))
    have hExpM := mul_le_mul_of_nonneg_left hExp hM
    have hN : 0 ≤ ε^2*F/m := by positivity
    linarith only [hM', hExpM, hN]

end Thesis

end
