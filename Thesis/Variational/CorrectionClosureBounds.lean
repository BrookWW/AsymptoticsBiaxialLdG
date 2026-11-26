module

public import Thesis.Variational.RegularClosureConvergence
public import Thesis.Variational.BoundaryRemainder

/-! The uniform zeroth-order data for the smooth-limit correction. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance correctionClosureTraceNorm : Norm (Tensor →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ)

theorem closureGradient_eq_classical_on_interior
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0} (hQ : ContDiffOn ℝ 1 Q (closure U))
    {x : Point} (hx : x ∈ U) :
    (fun j : Fin 3 => fderivWithin ℝ Q (closure U) x (axis j)) = ClassicalGradient Q x := by
  have hNear := mem_of_superset (hU.mem_nhds hx) subset_closure
  have hd := ((hQ x (subset_closure hx)).contDiffAt hNear).differentiableAt one_ne_zero
  funext j
  exact DFunLike.congr_fun (fderivWithin_eq_fderiv (uniqueDiffWithinAt_of_mem_nhds hNear) hd) (axis j)

private theorem norm_sub_le_toReal_seminorm_mul {α : ℝ} (hα : 0 < α) {K : Set Point}
    {g : Point → Gradient} {A : ℝ≥0∞}
    (hA : A < ⊤) (hg : holderSeminorm α K g ≤ A)
    (x : Point) (hx : x ∈ K) (y : Point) (hy : y ∈ K) :
    ‖g x - g y‖ ≤ A.toReal * dist x y ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, dist_self, Real.zero_rpow hα.ne', mul_zero, le_refl]
  have hDen : 0 < dist x y^α := Real.rpow_pos_of_pos (dist_pos.mpr hxy) _
  have hRatio : ENNReal.ofReal (‖g x - g y‖ / dist x y^α) ≤ A :=
    (le_iSup₂ (f := fun a b : K =>
      ENNReal.ofReal (‖g a - g b‖ / (dist (a : Point) (b : Point) ^ α))) ⟨x,hx⟩ ⟨y,hy⟩).trans hg
  have hReal := ENNReal.toReal_mono hA.ne hRatio
  rw [ENNReal.toReal_ofReal (div_nonneg (norm_nonneg _) hDen.le)] at hReal
  exact (div_le_iff₀ hDen).1 hReal

private theorem eventual_halfHolder_and_uniform_gradient_bounds
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U) {Q : ℕ → Point → S0} {q : Point → S0}
    (hVac : MapsTo q U (vacuum a)) (hConv : ConvergesC1HolderLoc (1/2) U ∅ Q q)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M H : ℝ, 0 ≤ M ∧ 0 ≤ H ∧ ∀ᶠ n in atTop,
      (∀ x ∈ U, Q n x ∈ vacuumTube a δ ∧ ‖Q n x‖ ≤ M ∧ Real.sqrt (gradientNormSq (ClassicalGradient (Q n) x)) ≤ M) ∧
      ∀ x ∈ U, ∀ y ∈ U, ∀ j : Fin 3,
        ‖coordDeriv j (Q n) x - coordDeriv j (Q n) y‖ ≤ H * Real.sqrt (dist x y) := by
  let K := closure U
  let D (v : Point → S0) (x : Point) (j : Fin 3) := fderivWithin ℝ v K x (axis j)
  have hK : IsCompact K := hU.1.2.2.isCompact_closure
  simp only [ConvergesC1HolderLoc, Set.sdiff_empty] at hConv
  obtain ⟨_, hFinite, hValues, hGrad, hHolder⟩ := hConv.2.2 K hK subset_rfl
  have hD : ContinuousOn (D q) K := by
    apply continuousOn_pi.mpr
    intro j
    exact (ContinuousLinearMap.apply ℝ S0 (axis j)).continuous.comp_continuousOn
      (hConv.2.1.continuousOn_fderivWithin hU.uniqueDiffOn_closure le_rfl)
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn hConv.2.1.continuousOn
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hD
  let A := max B 0 + 1
  let H₀ := holderSeminorm (1/2) K (D q) + 1
  let M := max (max L 0 + 1) (3*A)
  have hA : 0 ≤ A := add_nonneg (le_max_right _ _) zero_le_one
  have hHolderFin : H₀ < ⊤ := ENNReal.add_lt_top.2 ⟨hFinite, by simp⟩
  have hM : 0 ≤ M := (add_nonneg (le_max_right _ _) zero_le_one).trans (le_max_left _ _)
  refine ⟨M, H₀.toReal, hM, ENNReal.toReal_nonneg, ?_⟩
  have hδ' : 0 < min δ 1 := lt_min hδ zero_lt_one
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hValues (min δ 1) hδ',
    Metric.tendstoUniformlyOn_iff.mp hGrad 1 zero_lt_one, ENNReal.tendsto_nhds_zero.mp hHolder 1 zero_lt_one]
    with n hV hG hHoldern
  have hHolderN : holderSeminorm (1/2) K (D (Q n)) ≤ H₀ := by
    have hEq : D (Q n) = D q + (D (Q n) - D q) := by
      funext x
      change D (Q n) x = D q x + (D (Q n) x - D q x)
      abel
    rw [hEq]
    exact (holderSeminorm_add_le (1/2) K (D q) (D (Q n) - D q)).trans
      (add_le_add le_rfl hHoldern)
  have hCol (x : Point) (hx : x ∈ U) : D (Q n) x = ClassicalGradient (Q n) x :=
    closureGradient_eq_classical_on_interior hU.1.1 (hConv.1 n) hx
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxK : x ∈ K := subset_closure hx
    have hVX : dist (Q n x) (q x) < min δ 1 := (dist_comm (q x) (Q n x)) ▸ hV x hxK
    have hDX : dist (D (Q n) x) (D q x) < 1 := (dist_comm (D q x) (D (Q n) x)) ▸ hG x hxK
    have hTube : Q n x ∈ vacuumTube a δ :=
      (Metric.infDist_le_dist_of_mem (hVac hx)).trans_lt (hVX.trans_le (min_le_left _ _))
    have hQcap : ‖Q n x‖ ≤ M := by
      have hT := dist_triangle (Q n x) (q x) 0
      rw [dist_zero_right, dist_zero_right] at hT
      exact (hT.trans (add_le_add (hVX.le.trans (min_le_right _ _))
        ((hL x hxK).trans (le_max_left _ _)))).trans (by
        dsimp only [M]
        rw [add_comm]
        exact le_max_left _ _)
    have hDcap : ‖ClassicalGradient (Q n) x‖ ≤ A := by
      have hT := dist_triangle (D (Q n) x) (D q x) 0
      rw [dist_zero_right, dist_zero_right, hCol x hx] at hT
      rw [hCol x hx] at hDX
      exact hT.trans (by dsimp only [A]; linarith only [hDX, (hB x hxK).trans (le_max_left B 0)])
    refine ⟨hTube, hQcap, ?_⟩
    have hGsq : gradientNormSq (ClassicalGradient (Q n) x) ≤ 3*A^2 := by
      rw [gradientNormSq_eq_sum_norm_sq]
      refine (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _)
        ((norm_le_pi_norm (ClassicalGradient (Q n) x) j).trans hDcap) 2).trans_eq ?_
      simp
    have hGroot : Real.sqrt (gradientNormSq (ClassicalGradient (Q n) x)) ≤ 3*A := by
      apply (Real.sqrt_le_iff).2
      refine ⟨mul_nonneg (by norm_num) hA, ?_⟩
      exact hGsq.trans (by nlinarith only [sq_nonneg A])
    exact hGroot.trans (le_max_right _ _)
  · intro x hx y hy j
    have h := norm_sub_le_toReal_seminorm_mul (by norm_num : (0 : ℝ) < 1/2) hHolderFin hHolderN
      x (subset_closure hx) y (subset_closure hy)
    rw [← Real.sqrt_eq_rpow, hCol x hx, hCol y hy] at h
    exact (norm_le_pi_norm (ClassicalGradient (Q n) x - ClassicalGradient (Q n) y) j).trans h

/-- Closure convergence and the prescribed vacuum trace bound both
scaled defects, the full gradient and the Laplacian on the actual domain. -/
theorem exists_eventual_smoothLimit_biaxial_data
    (a : BulkCoefficients)
    {U : Set Point} (hU : IsSmoothDomain U) {ε : ℕ → ElasticScale}
    {Q : ℕ → Point → S0} {q : Point → S0}
    (hQ : ∀ n, ContDiffOn ℝ 2 (Q n) (closure U))
    (hWall : ∀ n, MapsTo (Q n) (frontier U) (vacuum a))
    (hVac : MapsTo q U (vacuum a))
    (hEq : ∀ n, ∀ x ∈ U, (ε n : ℝ)^2 • (↑(laplacian (Q n) x) : Tensor) = bulkGradient a (Q n x))
    (hConv : ConvergesC1HolderLoc (1/2) U ∅ Q q) :    ∃ B H : ℝ, 0 ≤ B ∧ 0 ≤ H ∧ ∀ᶠ n in atTop,
      (∀ x ∈ U, ‖Q n x‖ ≤ B ∧ ‖laplacian (Q n) x‖ ≤ B ∧
        |scaledNormDefect a (ε n) (Q n x)| ≤ B ∧ |scaledCubicTrace a (ε n) (Q n x)| ≤ B ∧
        Real.sqrt (gradientNormSq (ClassicalGradient (Q n) x)) ≤ B) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ j : Fin 3,
        ‖coordDeriv j (Q n) x - coordDeriv j (Q n) y‖ ≤ H * Real.sqrt (dist x y)) := by
  obtain ⟨δ, L, hδ, hL, hDefect⟩ := exists_uniform_scaledDefect_bound_of_vacuum_boundary a
  obtain ⟨M, H, hM, hH, hBounds⟩ := eventual_halfHolder_and_uniform_gradient_bounds a hU hVac hConv hδ
  let B := max M (max 1 ‖tensorTraceCLM‖ * (L*M^2))
  have hB : 0 ≤ B := hM.trans (le_max_left _ _)
  refine ⟨B,H,hB,hH,?_⟩
  filter_upwards [hBounds] with n hn
  have hGrad (x : Point) (hx : x ∈ U) : gradientNormSq (ClassicalGradient (Q n) x) ≤ M^2 := by
    have h₀ : 0 ≤ gradientNormSq (ClassicalGradient (Q n) x) := by
      rw [gradientNormSq_eq_sum_norm_sq]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hn.1 x hx).2.2 2
    rwa [Real.sq_sqrt h₀] at hh
  have hDef := hDefect (ε n) U hU.1 (Q n) ((hQ n).mono subset_closure) (hQ n).continuousOn
    (hWall n) (fun x hx => (hn.1 x hx).1) (hEq n) (M^2) (sq_nonneg M) hGrad
  refine ⟨?_, hn.2⟩
  intro x hx
  have hd := hDef x hx
  have h1 : 0 ≤ ((ε n : ℝ)^2)⁻¹ * Real.sqrt (bulkPotential a (Q n x)) := by positivity
  have h2 : ‖laplacian (Q n) x‖ ≤ L*M^2 := by
    linarith only [hd, h1, abs_nonneg (scaledNormDefect a (ε n) (Q n x)),
      norm_nonneg (scaledCubicDefect a (ε n) (Q n x))]
  have hh : |scaledNormDefect a (ε n) (Q n x)| ≤ L*M^2 := by
    linarith only [hd, h1, norm_nonneg (laplacian (Q n) x), norm_nonneg (scaledCubicDefect a (ε n) (Q n x))]
  have hY : ‖scaledCubicDefect a (ε n) (Q n x)‖ ≤ L*M^2 := by
    linarith only [hd, h1, norm_nonneg (laplacian (Q n) x), abs_nonneg (scaledNormDefect a (ε n) (Q n x))]
  have hY₂ : |scaledCubicTrace a (ε n) (Q n x)| ≤ max 1 ‖tensorTraceCLM‖*(L*M^2) := by
    change ‖tensorTraceCLM (scaledCubicDefect a (ε n) (Q n x))‖ ≤ _
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (le_max_right _ _) hY (norm_nonneg _) (zero_le_one.trans (le_max_left _ _)))
  have hB₀ : L*M^2 ≤ max 1 ‖tensorTraceCLM‖*(L*M^2) := by
    have h₀ := mul_le_mul_of_nonneg_right (le_max_left 1 ‖tensorTraceCLM‖) (mul_nonneg hL.le (sq_nonneg M))
    simpa only [one_mul] using h₀
  have hB₂ : L*M^2 ≤ B := hB₀.trans (le_max_right _ _)
  exact ⟨(hn.1 x hx).2.1.trans (le_max_left _ _), h2.trans hB₂, hh.trans hB₂,
    hY₂.trans (le_max_right _ _), (hn.1 x hx).2.2.trans (le_max_left _ _)⟩

/-- Smooth-limit closed-domain convergence and the fixed physical trace
give the actual wall profile for the projected correction remainder. -/
theorem exists_eventual_projectedHarmonicRemainder_wall_profile_of_global_C1Holder
    (a : BulkCoefficients) (hEstimate : InteriorPoissonGradientEstimate)
    {U : Set Point} (hU : IsSmoothDomain U) {ε : ℕ → ElasticScale}
    {Q : ℕ → Point → S0} {q : Point → S0}
    (hQ : ∀ n, ContDiffOn ℝ 2 (Q n) (closure U))
    (hQOpen : ∀ n, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (Q n) U)
    (hWall : ∀ n, MapsTo (Q n) (frontier U) (vacuum a))
    (hVac : MapsTo q U (vacuum a))
    (hEq : ∀ n, ∀ x ∈ U, (ε n : ℝ)^2 • (↑(laplacian (Q n) x) : Tensor) = bulkGradient a (Q n x))
    (hConv : ConvergesC1HolderLoc (1/2) U ∅ Q q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n in atTop, ∀ x ∈ U,
      ‖projectedHarmonicRemainder a (ε n) (Q n) x‖ ≤ C * ((ε n : ℝ)^2/Metric.infDist x (frontier U) +
        Real.exp (-c*Metric.infDist x (frontier U)/ε n)) := by
  obtain ⟨B,H,hB,hH,hBounds⟩ := exists_eventual_smoothLimit_biaxial_data a hU hQ hWall hVac hEq hConv
  obtain ⟨c,C,hc,hC,hR⟩ := exists_projectedHarmonicRemainder_wall_profile a hEstimate hU.1 B H hB hH
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hBounds] with n hn
  exact hR (ε n) (Q n) (hQOpen n) (hEq n) hn.1 hn.2

/-- The same closure convergence yields a common bound for the states
and Laplacians of the approximating fields and the smooth limit. -/
theorem exists_eventual_smoothLimit_state_laplacian_bounds
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U) {ε : ℕ → ElasticScale}
    {Q : ℕ → Point → S0} {q : Point → S0}
    (hQ : ∀ n, ContDiffOn ℝ 2 (Q n) (closure U)) (hq : ContDiffOn ℝ 2 q (closure U))
    (hWall : ∀ n, MapsTo (Q n) (frontier U) (vacuum a))
    (hVac : MapsTo q U (vacuum a))
    (hEq : ∀ n, ∀ x ∈ U, (ε n : ℝ)^2 • (↑(laplacian (Q n) x) : Tensor) = bulkGradient a (Q n x))
    (hConv : ConvergesC1HolderLoc (1/2) U ∅ Q q) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x ∈ U, ‖q x‖ ≤ M ∧ ‖laplacian q x‖ ≤ M ∧
      Real.sqrt (gradientNormSq (ClassicalGradient q x)) ≤ M) ∧
      ∀ᶠ n in atTop, ∀ x ∈ U, ‖Q n x‖ ≤ M ∧ ‖laplacian (Q n) x‖ ≤ M ∧
        Real.sqrt (gradientNormSq (ClassicalGradient (Q n) x)) ≤ M := by
  obtain ⟨δ, L, hδ, hL, hDefect⟩ := exists_uniform_scaledDefect_bound_of_vacuum_boundary a
  obtain ⟨M, _, hM, _, hBounds⟩ := eventual_halfHolder_and_uniform_gradient_bounds a hU hVac hConv hδ
  obtain ⟨A, F, hA, hF, hqValue, hqLap⟩ := exists_value_laplacian_bound_of_contDiffOn_closure hU hq
  let D (x : Point) (j : Fin 3) := fderivWithin ℝ q (closure U) x (axis j)
  have hq₁ : ContDiffOn ℝ 1 q (closure U) := hq.of_le (by norm_num)
  have hD : ContinuousOn D (closure U) := by
    apply continuousOn_pi.mpr
    intro j
    exact (ContinuousLinearMap.apply ℝ S0 (axis j)).continuous.comp_continuousOn
      (hq₁.continuousOn_fderivWithin hU.uniqueDiffOn_closure le_rfl)
  obtain ⟨B,hB⟩ := hU.1.2.2.isCompact_closure.exists_bound_of_continuousOn hD
  let C := max (max M (L*M^2)) (A+F+3*max B 0)
  have hC : 0 ≤ C := hM.trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨C, hC, ?_, ?_⟩
  · intro x hx
    have hC₀ : A+F+3*max B 0 ≤ C := le_max_right _ _
    have hS : Real.sqrt (gradientNormSq (ClassicalGradient q x)) ≤ 3*max B 0 := by
      apply (Real.sqrt_le_iff).2
      refine ⟨mul_nonneg (by norm_num) (le_max_right _ _), ?_⟩
      have hDq : ‖ClassicalGradient q x‖ ≤ max B 0 := by
        have h := hB x (subset_closure hx)
        have hEq := closureGradient_eq_classical_on_interior hU.1.1 hq₁ hx
        change D x = ClassicalGradient q x at hEq
        rw [hEq] at h
        exact h.trans (le_max_left _ _)
      rw [gradientNormSq_eq_sum_norm_sq]
      have hPow := (Finset.sum_le_sum (s := Finset.univ) fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm (ClassicalGradient q x) j).trans hDq) 2)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hPow
      exact hPow.trans (by nlinarith only [sq_nonneg (max B 0)])
    exact ⟨(hqValue x hx).trans (by linarith only [hC₀, hF, le_max_right B 0]),
      (hqLap x hx).trans (by nlinarith only [hC₀,hA,le_max_right B 0]),
      hS.trans (by linarith only [hC₀,hA,hF])⟩
  · filter_upwards [hBounds] with n hn x hx
    have hGrad (y : Point) (hy : y ∈ U) : gradientNormSq (ClassicalGradient (Q n) y) ≤ M^2 := by
      have h₀ : 0 ≤ gradientNormSq (ClassicalGradient (Q n) y) := by
        rw [gradientNormSq_eq_sum_norm_sq]
        exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hn.1 y hy).2.2 2
      rwa [Real.sq_sqrt h₀] at hh
    have hDef := hDefect (ε n) U hU.1 (Q n) ((hQ n).mono subset_closure) (hQ n).continuousOn
      (hWall n) (fun y hy => (hn.1 y hy).1) (hEq n) (M^2) (sq_nonneg M) hGrad x hx
    have hL₂ : ‖laplacian (Q n) x‖ ≤ L*M^2 := by
      have hPot : 0 ≤ ((ε n : ℝ)^2)⁻¹ * Real.sqrt (bulkPotential a (Q n x)) := by positivity
      linarith only [hDef,hPot,abs_nonneg (scaledNormDefect a (ε n) (Q n x)),
        norm_nonneg (scaledCubicDefect a (ε n) (Q n x))]
    have hCM : M ≤ C := (le_max_left _ _).trans (le_max_left _ _)
    exact ⟨(hn.1 x hx).2.1.trans hCM, hL₂.trans ((le_max_right _ _).trans (le_max_left _ _)),
      (hn.1 x hx).2.2.trans hCM⟩

end Thesis

end
