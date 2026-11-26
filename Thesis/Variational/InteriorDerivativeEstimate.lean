module

public import Thesis.Variational.InteriorScaledDefect
public import Thesis.Variational.EulerLagrange
import Thesis.Variational.EnergyEstimate

/-! Interior Poisson interpolation for the scalar and tensor equations. -/

public section

open Filter Metric Set Topology
open scoped ContDiff Matrix.Norms.Frobenius

noncomputable section

namespace Thesis

private theorem optimized_poisson_radius (M K r : ℝ) (hM : 0 < M) (hK : 0 < K) (hr : 0 < r) :
    ∃ R : ℝ, 0 < R ∧ R ≤ r ∧ R ^ 2 * K ≤ M ∧ M / R ≤ M / r + Real.sqrt (M * K) := by
  let d := Real.sqrt (M / K)
  have hd : 0 < d := Real.sqrt_pos.mpr (div_pos hM hK)
  have hd₂ : d ^ 2 = M / K := Real.sq_sqrt (div_nonneg hM.le hK.le)
  let R := min r d
  have hR : 0 < R := lt_min hr hd
  have hRd : R ≤ d := min_le_right _ _
  have hRr : R ≤ r := min_le_left _ _
  have hStep : R ^ 2 * K ≤ M := by
    refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR.le hRd 2) hK.le).trans_eq ?_
    rw [hd₂, div_mul_cancel₀ _ hK.ne']
  refine ⟨R, hR, hRr, hStep, ?_⟩
  rcases le_total r d with h | h
  · rw [show R = r from min_eq_left h]
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  · rw [show R = d from min_eq_right h]
    have hEq : M / d = Real.sqrt (M * K) := by
      apply (div_eq_iff hd.ne').mpr
      rw [mul_comm]
      change M = Real.sqrt (M / K) * Real.sqrt (M * K)
      rw [← Real.sqrt_mul (div_nonneg hM.le hK.le)]
      have hMul : M / K * (M * K) = M ^ 2 := by field_simp
      rw [hMul, Real.sqrt_sq hM.le]
    rw [hEq]
    exact le_add_of_nonneg_left (div_nonneg hM.le hr.le)

/-- Optimizing the radius in the scaled Poisson bound gives interior
interpolation with the actual tensor Laplacian. -/
theorem exists_interior_tensor_gradient_interpolation (hEstimate : InteriorPoissonGradientEstimate) :
    ∃ C > (0 : ℝ), ∀ (x : Point) (r : ℝ), 0 < r →
      ∀ (u : Point → S0), ContDiffOn ℝ 2 u (ball x r) →
        ∀ M K : ℝ, 0 ≤ M → 0 ≤ K → (∀ y ∈ ball x r, ‖u y‖ ≤ M) →
          (∀ y ∈ ball x r, ‖laplacian u y‖ ≤ K) →
          Real.sqrt (gradientNormSq (ClassicalGradient u x)) ≤ C * (M / r + Real.sqrt (M * K)) := by
  obtain ⟨A, hA, hB⟩ := hEstimate
  refine ⟨2 * A, by positivity, ?_⟩
  intro x r hr u hu M K hM hK hU hLap
  rcases hM.eq_or_lt with hMz | hM'
  · subst M
    have h0 : u =ᶠ[𝓝 x] (fun _ : Point => (0 : S0)) := by
      filter_upwards [ball_mem_nhds x hr] with y hy
      exact norm_le_zero_iff.mp (hU y hy)
    have hD (i : Fin 3) : ClassicalGradient u x i = 0 :=
      (DFunLike.congr_fun h0.fderiv_eq (axis i)).trans (by simp)
    rw [gradientNormSq_eq_sum_norm_sq]
    simp [hD]
  rcases hK.eq_or_lt with hKz | hK'
  · subst K
    have hG := hB x r hr u (fun y => (laplacian u y).val) M 0 hu (fun _ _ => rfl) hU hLap
    have hG' : Real.sqrt (gradientNormSq (ClassicalGradient u x)) ≤ A * M / r :=
      (le_div_iff₀ hr).mpr (by linarith only [hG])
    refine hG'.trans ?_
    simp only [mul_zero, Real.sqrt_zero, add_zero, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hM hr.le)
  obtain ⟨R, hR, hRr, hRK, hRM⟩ := optimized_poisson_radius M K r hM' hK' hr
  have hSub : ball x R ⊆ ball x r := ball_subset_ball hRr
  have hG := hB x R hR u (fun y => (laplacian u y).val) M K
    (hu.mono hSub) (fun _ _ => rfl) (fun y hy => hU y (hSub hy)) (fun y hy => hLap y (hSub hy))
  have hG' := hG.trans (mul_le_mul_of_nonneg_left (add_le_add_right hRK M) hA.le)
  have hBound : Real.sqrt (gradientNormSq (ClassicalGradient u x)) ≤ (2 * A) * (M / R) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hR).mpr
    calc
      _ ≤ A * (M + M) := (mul_comm _ _).le.trans hG'
      _ = (2 * A) * M := by ring
  exact hBound.trans (mul_le_mul_of_nonneg_left hRM (by positivity))

/-- The scalar form of the same interior estimate, via an isometric
one-dimensional linear inclusion into the tensor space. -/
theorem exists_interior_scalar_gradient_interpolation (hEstimate : InteriorPoissonGradientEstimate) :
    ∃ C > (0 : ℝ), ∀ (x : Point) (r : ℝ), 0 < r →
      ∀ (f : Point → ℝ), ContDiffOn ℝ 2 f (ball x r) →
        ∀ M K : ℝ, 0 ≤ M → 0 ≤ K → (∀ y ∈ ball x r, |f y| ≤ M) →
          (∀ y ∈ ball x r, |laplacian f y| ≤ K) →
          Real.sqrt (∑ j : Fin 3, |coordDeriv j f x| ^ 2) ≤ C * (M / r + Real.sqrt (M * K)) := by
  obtain ⟨C, hC, hG⟩ := exists_interior_tensor_gradient_interpolation hEstimate
  let N : S0 := frobeniusCoordinateEquiv.symm (EuclideanSpace.single (0 : Fin 5) (1 : ℝ))
  have hN : ‖N‖ = 1 := by
    rw [show N = frobeniusCoordinateEquiv.symm (EuclideanSpace.single (0 : Fin 5) (1 : ℝ)) from rfl,
      LinearIsometryEquiv.norm_map]
    change ‖PiLp.single 2 (β := fun _ : Fin 5 => ℝ) (0 : Fin 5) (1 : ℝ)‖ = 1
    rw [PiLp.norm_single, norm_one]
  let L : ℝ →L[ℝ] S0 := (ContinuousLinearMap.id ℝ ℝ).smulRight N
  have hNorm (t : ℝ) : ‖L t‖ = |t| := by
    change ‖t • N‖ = _
    rw [norm_smul, Real.norm_eq_abs, hN, mul_one]
  refine ⟨C, hC, ?_⟩
  intro x r hr f hf M K hM hK hF hLap
  have hV (y : Point) (hy : y ∈ ball x r) : ‖(L ∘ f) y‖ ≤ M := by
    rw [Function.comp_apply, hNorm]
    exact hF y hy
  have hLap' (y : Point) (hy : y ∈ ball x r) : ‖laplacian (L ∘ f) y‖ ≤ K := by
    calc
      _ = ‖L (laplacian f y)‖ := congrArg (fun z : S0 => ‖z‖) (laplacian_compCLM isOpen_ball hf hy L)
      _ = _ := hNorm _
      _ ≤ _ := hLap y hy
  have hEst := hG x r hr (L ∘ f) (L.contDiff.comp_contDiffOn hf) M K hM hK hV hLap'
  have hDx : DifferentiableAt ℝ f x :=
    (hf.differentiableOn (by norm_num : (2 : ℕ∞ω) ≠ 0) _ (mem_ball_self hr)).differentiableAt (ball_mem_nhds _ hr)
  have hD (j : Fin 3) : coordDeriv j (L ∘ f) x = L (coordDeriv j f x) :=
    DFunLike.congr_fun (L.hasFDerivAt.comp x hDx.hasFDerivAt).fderiv (axis j)
  rw [gradientNormSq_eq_sum_norm_sq] at hEst
  change Real.sqrt (∑ j : Fin 3, ‖coordDeriv j (L ∘ f) x‖ ^ 2) ≤ _ at hEst
  simpa only [hD, hNorm] using hEst

private theorem screened_subsolution_center_min_bound
    {Ω : Set Point} {x : Point} {R L m F M : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hm : 0 < m) (hF : 0 ≤ F) (hM : 0 ≤ M)
    (hBall : closedBall x R ⊆ Ω) {w : Point → ℝ} (hw : ContDiffOn ℝ 2 w Ω)
    (hWall : ∀ y ∈ sphere x R, w y ≤ M)
    (hPde : ∀ y ∈ ball x R, -L * laplacian w y + m * w y ≤ F) :
    w x ≤ F / m + M * min 1 (6 * L / (m * R ^ 2)) := by
  let a := m / L
  have ha : 0 < a := div_pos hm hL
  have hp (y : Point) (hy : y ∈ ball x R) : -laplacian w y + a * w y ≤ F / L := by
    apply (le_div_iff₀ hL).mpr
    calc
      _ = -L * laplacian w y + m * w y := by dsimp only [a]; field_simp
      _ ≤ _ := hPde y hy
  have hC : closure (ball x R) = closedBall x R := closure_ball _ hR.ne'
  have hK : IsCompact (closure (ball x R)) := hC.symm ▸ isCompact_closedBall _ _
  have hB (y : Point) (hy : y ∈ frontier (ball x R)) : w y ≤ F / m + M := by
    rw [frontier_ball _ hR.ne'] at hy
    exact (hWall y hy).trans (le_add_of_nonneg_left (div_nonneg hF hm.le))
  have hVal : a * (F / m + M) = F / L + a * M := by
    dsimp only [a]
    field_simp
  have hSimple := screened_subsolution_le_constant isOpen_ball hK
    (hw.continuousOn.mono (hC.symm ▸ hBall)) (hw.mono (ball_subset_closedBall.trans hBall)) ha hB
    (fun y hy => (hp y hy).trans (hVal ▸ le_add_of_nonneg_right (mul_nonneg ha.le hM)))
    x (subset_closure (mem_ball_self hR))
  have hQuad := screened_subsolution_le_at_ball_center hR ha (div_nonneg hF hL.le) hM hBall hw hWall hp
  have hVal' : (F / L + 6 * M / R ^ 2) / a = F / m + M * (6 * L / (m * R ^ 2)) := by
    dsimp only [a]
    field_simp [hR.ne', hL.ne', hm.ne']
  rw [hVal'] at hQuad
  rw [mul_min_of_nonneg _ _ hM, ← min_add_add_left, mul_one]
  exact le_min hSimple hQuad

/-- Positive-mass comparison controls the absolute value at a ball center.
The boundary contribution is bounded both by its original size and by a
quadratic decay in the ratio of the elastic length to the radius. -/
theorem screened_solution_abs_le_at_ball_center
    {Ω : Set Point} (hΩ : IsOpen Ω) {x : Point} {R L m F M : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hm : 0 < m) (hF : 0 ≤ F) (hM : 0 ≤ M)
    (hBall : closedBall x R ⊆ Ω) {w : Point → ℝ} (hw : ContDiffOn ℝ 2 w Ω)
    (hWall : ∀ y ∈ sphere x R, |w y| ≤ M)
    (hPde : ∀ y ∈ ball x R, |-L * laplacian w y + m * w y| ≤ F) :
    |w x| ≤ F / m + M * min 1 (6 * L / (m * R ^ 2)) := by
  have hUpper := screened_subsolution_center_min_bound hR hL hm hF hM hBall hw
    (fun y hy => (le_abs_self _).trans (hWall y hy)) fun y hy => (le_abs_self _).trans (hPde y hy)
  have hLower := screened_subsolution_center_min_bound hR hL hm hF hM hBall hw.neg
    (fun y hy => (neg_le_abs _).trans (hWall y hy)) ?_
  · exact abs_le.mpr ⟨neg_le.mp hLower, hUpper⟩
  · intro y hy
    have hyΩ := hBall (ball_subset_closedBall hy)
    have hNeg : laplacian (fun z => -w z) y = -laplacian w y := by
      rw [show (fun z => -w z) = fun z => (-1 : ℝ) • w z from funext fun z => (neg_one_smul ℝ (w z)).symm,
        laplacian_const_smul hΩ hw hyΩ, neg_one_smul]
    change -L * laplacian (fun z => -w z) y + m * -w y ≤ F
    rw [hNeg, show -L * -laplacian w y + m * -w y = -(-L * laplacian w y + m * w y) by ring]
    exact (neg_le_abs _).trans (hPde y hy)

/-- Absorption on nested radii removes the larger-radius derivative bound.
The outer compact bound is used only to make the last geometric term vanish. -/
theorem absorb_interior_radius_bounds {s t C M : ℝ} (hst : s < t) (hC : 0 ≤ C)
    (Φ : ℝ → ℝ) (hB : ∀ r ∈ Icc s t, Φ r ≤ M)
    (hStep : ∀ r ∈ Icc s t, ∀ r' ∈ Icc s t, r < r' →
      Φ r ≤ (1 / 4 : ℝ) * Φ r' + C * (1 + (r' - r)⁻¹)) :
    Φ s ≤ 2 * (C * (1 + 2 / (t - s))) := by
  let g := t - s
  let E := C * (1 + 2 / g)
  let r (n : ℕ) := t - g * (1 / 2 : ℝ) ^ n
  have hg : 0 < g := sub_pos.mpr hst
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hp (n : ℕ) : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hp₁ (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hr (n : ℕ) : r n ∈ Icc s t := by
    have h := mul_le_mul_of_nonneg_left (hp₁ n) hg.le
    exact ⟨by dsimp only [r, g]; dsimp only [g] at h; linarith, sub_le_self _ (mul_nonneg hg.le (hp n).le)⟩
  have hGap (n : ℕ) : r (n + 1) - r n = g * (1 / 2 : ℝ) ^ n / 2 := by
    dsimp only [r]
    rw [pow_succ]
    ring
  have hrlt (n : ℕ) : r n < r (n + 1) :=
    sub_pos.mp (hGap n ▸ half_pos (mul_pos hg (hp n)))
  have hGeom (n : ℕ) : (1 / 4 : ℝ) ^ n * (C * (1 + (r (n + 1) - r n)⁻¹)) ≤
      E * (1 / 2 : ℝ) ^ n := by
    let q := (1 / 2 : ℝ) ^ n
    have hq : 0 < q := hp n
    have hq₂ : (1 / 4 : ℝ) ^ n = q ^ 2 := by
      dsimp only [q]
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    rw [hGap, hq₂]
    change q ^ 2 * (C * (1 + (g * q / 2)⁻¹)) ≤ E * q
    calc
      _ = C * (q ^ 2 + 2 / g * q) := by field_simp [hg.ne', hq.ne']
      _ ≤ C * (q + 2 / g * q) := by
        have hSq : q ^ 2 ≤ q := by nlinarith only [mul_le_mul_of_nonneg_left (hp₁ n) hq.le]
        exact mul_le_mul_of_nonneg_left (add_le_add hSq le_rfl) hC
      _ = _ := by dsimp only [E]; ring
  have hI (n : ℕ) : Φ s ≤ (1 / 4 : ℝ) ^ n * Φ (r n) + 2 * E * (1 - (1 / 2 : ℝ) ^ n) := by
    induction n with
    | zero =>
        have h0 : r 0 = s := by simp [r, g]
        simp [h0]
    | succ n ih =>
        have hS := mul_le_mul_of_nonneg_left (hStep _ (hr n) _ (hr (n + 1)) (hrlt n))
          (pow_nonneg (by norm_num : 0 ≤ (1 / 4 : ℝ)) n)
        refine ih.trans ?_
        rw [mul_add] at hS
        have hS' := hS.trans (add_le_add le_rfl (hGeom n))
        rw [pow_succ, pow_succ]
        linarith only [hS']
  have hFinal (n : ℕ) : Φ s ≤ (1 / 4 : ℝ) ^ n * M + 2 * E := by
    refine (hI n).trans (add_le_add (mul_le_mul_of_nonneg_left (hB _ (hr n)) (by positivity)) ?_)
    exact mul_le_of_le_one_right (by positivity) (sub_le_self _ (hp n).le)
  have hLimit : Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ n * M + 2 * E) atTop (𝓝 (2 * E)) := by
    have hPow : Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [zero_mul, zero_add] using (hPow.mul_const M).add tendsto_const_nhds
  exact ge_of_tendsto hLimit (Eventually.of_forall hFinal)

end Thesis

end
