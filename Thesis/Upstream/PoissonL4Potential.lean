module

public import Thesis.Upstream.PoissonL4Kernel
public import HolderToCK.Analysis.Poisson.HolderPotential

/-! Finite-difference and potential estimates for an actual compact (L^4) source. -/

public section

noncomputable section

open Filter HarmonicMaps HolderToCK MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace Thesis

theorem poissonInversePower_one (x : Point) : poissonInversePower 1 x = ‖x‖⁻¹ := by
  rw [poissonInversePower, Real.rpow_neg (norm_nonneg x), Real.rpow_one]

theorem poissonInversePower_two (x : Point) : poissonInversePower 2 x = (‖x‖⁻¹) ^ 2 := by
  rw [poissonInversePower, Real.rpow_neg (norm_nonneg x), Real.rpow_two, inv_pow]

/-- The negative sign of the fundamental solution in dimension three. -/
theorem fundamentalPowerExpression_three (z : Point) :
    fundamentalPowerExpression z = -(euclideanSphereArea 3)⁻¹ * poissonInversePower 1 z := by
  unfold fundamentalPowerExpression poissonInversePower
  have h : ((2 : ℝ) - (↑(3 : ℕ) : ℝ)) = -1 := by norm_num
  rw [h, ← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul (norm_nonneg z)]
  norm_num

private theorem abs_inv_sub_inv_le_half_sq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    |a⁻¹ - b⁻¹| ≤ |a - b| * ((a⁻¹)^2 + (b⁻¹)^2) / 2 := by
  rw [inv_sub_inv ha.ne' hb.ne', abs_div, abs_of_pos (mul_pos ha hb), abs_sub_comm b a]
  have h : (a*b)⁻¹ ≤ (a⁻¹ ^ 2 + b⁻¹ ^ 2) / 2 := by
    rw [mul_inv]
    nlinarith only [sq_nonneg (a⁻¹-b⁻¹)]
  calc
    _ = |a-b| * (a*b)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ |a-b| * ((a⁻¹)^2 + (b⁻¹)^2) / 2 := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- The finite difference of two inverse radii costs the distance times
the sum of the two inverse-square kernels. -/
theorem abs_poissonInversePower_one_sub_le (x z y : Point) (hx : x ≠ y) (hz : z ≠ y) :
    |poissonInversePower 1 (x-y) - poissonInversePower 1 (z-y)| ≤
      dist x z * (poissonInversePower 2 (x-y) + poissonInversePower 2 (z-y)) / 2 := by
  rw [poissonInversePower_one, poissonInversePower_one, poissonInversePower_two, poissonInversePower_two]
  have hxN : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.mpr hx)
  have hzN : 0 < ‖z - y‖ := norm_pos_iff.2 (sub_ne_zero.mpr hz)
  apply (abs_inv_sub_inv_le_half_sq _ _ hxN hzN).trans
  have h := abs_norm_sub_norm_le (x-y) (z-y)
  rw [sub_sub_sub_cancel_right, ← dist_eq_norm] at h
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity)) zero_le_two

theorem realHolderConjugate_four : (4 : ℝ).HolderConjugate (4 / 3 : ℝ) :=
  Real.holderConjugate_iff.mpr (by norm_num)

theorem integrable_poissonL4_smul {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}
    {f : X → E} {g : X → ℝ} (hf : MemLp f 4 μ) (hg : MemLp g poissonL4Conjugate μ) :
    Integrable (fun x => g x • f x) μ := by
  haveI : ENNReal.HolderConjugate 4 poissonL4Conjugate := by
    simpa only [ENNReal.ofReal_ofNat] using realHolderConjugate_four.ennrealOfReal
  exact memLp_one_iff_integrable.1 (hf.smul (r := 1) hg)

theorem integral_poissonL4_product_le {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {f : X → E} {g : X → ℝ}
    (hf : MemLp f 4 μ) (hg : MemLp g poissonL4Conjugate μ) (hNN : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (∫ x, g x * ‖f x‖ ∂μ) ≤ (eLpNorm g poissonL4Conjugate μ).toReal * (eLpNorm f 4 μ).toReal := by
  have h := integral_norm_mul_le_realLp_mul realHolderConjugate_four.symm hg
    (by simpa only [ENNReal.ofReal_ofNat] using hf)
  rwa [integral_congr_ae (hNN.mono fun x hx => by rw [Real.norm_of_nonneg hx]), ENNReal.ofReal_ofNat] at h

/-- The literal convolution may be integrated in the source variable on its support. -/
theorem newtonianPotential_ball_source {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (c x : Point) (r : ℝ) (g : Point → E)
    (hSupp : ∀ y ∉ ball c r, g y = 0) :
    newtonianPotential (by decide : 2 ≤ 3) g x =
      ∫ y in ball c r, (-(euclideanSphereArea 3)⁻¹ * poissonInversePower 1 (x-y)) • g y := by
  rw [newtonianPotential_eq_power (by decide : 3 ≤ 3)]
  let F (y : Point) := x-y
  have hF : MeasurePreserving F volume volume := (volume : Measure Point).measurePreserving_sub_left x
  have hIso : Isometry F := by
    apply Isometry.of_dist_eq
    intro a b
    change dist (x-a) (x-b) = dist a b
    rw [dist_eq_norm, sub_sub_sub_cancel_left, norm_sub_rev, ← dist_eq_norm]
  have hComp := hF.integral_comp hIso.isClosedEmbedding.measurableEmbedding
    (fun z => fundamentalPowerExpression z • g (x-z))
  have hEq : (fun y => fundamentalPowerExpression (x-y) • g (x-(x-y))) =
      fun y => (-(euclideanSphereArea 3)⁻¹ * poissonInversePower 1 (x-y)) • g y := by
    funext y
    rw [sub_sub_cancel, fundamentalPowerExpression_three]
  change (∫ z, fundamentalPowerExpression z • g (x-z)) = _
  rw [← hComp]
  change (∫ y, fundamentalPowerExpression (x-y) • g (x-(x-y))) = _
  rw [hEq]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [hSupp y hy, smul_zero]

/-- A compact (L^4) force gives both the scaled Newtonian value bound
and a pointwise Lipschitz bound on the closed source ball. -/
theorem exists_newtonianPotential_L4_ball_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} (c : Point) {r : ℝ}, 0 < r →
      ∀ (g : Point → Ambient q), MemLp g 4 (volume.restrict (ball c r)) →
      (∀ y ∉ ball c r, g y = 0) →
      let P := newtonianPotential (by decide : 2 ≤ 3) g
      let F := (eLpNorm g 4 (volume.restrict (ball c r))).toReal
      (∀ x ∈ closedBall c r, ‖P x‖ ≤ C * r ^ (5/4 : ℝ) * F) ∧
      ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
        ‖P x - P y‖ ≤ C * r ^ (1/4 : ℝ) * F * dist x y := by
  obtain ⟨C₁, hC₁, hK₁⟩ := exists_poissonInversePower_conjugate_bound 1 (by norm_num)
  obtain ⟨C₂, hC₂, hK₂⟩ := exists_poissonInversePower_conjugate_bound 2 (by norm_num)
  let κ := (euclideanSphereArea 3)⁻¹
  have hκ : 0 < κ := inv_pos.mpr (euclideanSphereArea_pos (by decide))
  let C := 1 + κ * (C₁ + C₂)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro q c r hr g hg hSupp P F
  let μ := volume.restrict (ball c r)
  let K (s : ℝ) (x y : Point) := poissonInversePower s (x-y)
  let Ψ (x y : Point) := (-κ * K 1 x y) • g y
  have hInt (x : Point) (hx : x ∈ closedBall c r) : Integrable (Ψ x) μ := by
    have h := integrable_poissonL4_smul hg ((hK₁ c x r hr hx).1.const_mul (-κ))
    exact h
  have hP (x : Point) : P x = ∫ y, Ψ x y ∂μ := newtonianPotential_ball_source c x r g hSupp
  have hE₁ (x : Point) (hx : x ∈ closedBall c r) :
      (∫ y, K 1 x y * ‖g y‖ ∂μ) ≤ C₁ * r ^ (5/4 : ℝ) * F := by
    have h := hK₁ c x r hr hx
    have hK := integral_poissonL4_product_le hg h.1
      (Eventually.of_forall fun _ => poissonInversePower_nonneg _ _)
    have he : (9 / 4 : ℝ) - 1 = 5 / 4 := by norm_num
    rw [he] at h
    exact hK.trans (mul_le_mul_of_nonneg_right h.2 ENNReal.toReal_nonneg)
  have hE₂ (x : Point) (hx : x ∈ closedBall c r) :
      (∫ y, K 2 x y * ‖g y‖ ∂μ) ≤ C₂ * r ^ (1/4 : ℝ) * F := by
    have h := hK₂ c x r hr hx
    have hK := integral_poissonL4_product_le hg h.1
      (Eventually.of_forall fun _ => poissonInversePower_nonneg _ _)
    have he : (9 / 4 : ℝ) - 2 = 1 / 4 := by norm_num
    rw [he] at h
    exact hK.trans (mul_le_mul_of_nonneg_right h.2 ENNReal.toReal_nonneg)
  have hBound₁ : κ * C₁ ≤ C := by
    dsimp only [C]
    linarith only [mul_nonneg hκ.le hC₂]
  have hBound₂ : κ * C₂ ≤ C := by
    dsimp only [C]
    linarith only [mul_nonneg hκ.le hC₁]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hP x]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hNorm (y : Point) : ‖Ψ x y‖ = κ * (K 1 x y * ‖g y‖) := by
      rw [show Ψ x y = (-κ * K 1 x y) • g y from rfl, norm_smul, Real.norm_eq_abs, abs_mul,
        abs_neg, abs_of_nonneg hκ.le, abs_of_nonneg (poissonInversePower_nonneg _ _), mul_assoc]
    simp_rw [hNorm, integral_const_mul]
    have h := mul_le_mul_of_nonneg_left (hE₁ x hx) hκ.le
    exact h.trans (((by ring : κ * (C₁ * r ^ (5 / 4 : ℝ) * F) =
      (κ * C₁) * r ^ (5 / 4 : ℝ) * F)).le.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBound₁ (by positivity)) ENNReal.toReal_nonneg))
  · intro x hx y hy
    have hA (z : Point) (hz : z ∈ closedBall c r) :
        Integrable (fun t => K 2 z t * ‖g t‖) μ := by
      exact integrable_poissonL4_smul hg.norm (hK₂ c z r hr hz).1
    have hB : Integrable (fun t => (κ * dist x y / 2) * (K 2 x t * ‖g t‖ + K 2 y t * ‖g t‖)) μ :=
      ((hA x hx).add (hA y hy)).const_mul _
    rw [hP x, hP y, ← integral_sub (hInt x hx) (hInt y hy)]
    apply (norm_integral_le_of_norm_le hB ?_).trans
    · rw [integral_const_mul, integral_add (hA x hx) (hA y hy)]
      have h := mul_le_mul_of_nonneg_left (add_le_add (hE₂ x hx) (hE₂ y hy))
        (div_nonneg (mul_nonneg hκ.le (show 0 ≤ dist x y from dist_nonneg)) zero_le_two)
      refine h.trans ((le_of_eq ?_).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBound₂ (by positivity))
          ENNReal.toReal_nonneg) dist_nonneg))
      ring
    · filter_upwards [((volume : Measure Point).ae_ne x).filter_mono (ae_mono Measure.restrict_le_self),
        ((volume : Measure Point).ae_ne y).filter_mono (ae_mono Measure.restrict_le_self)] with t ht₁ ht₂
      have hEq : Ψ x t - Ψ y t = (-κ * (K 1 x t - K 1 y t)) • g t := by
        change (-κ * K 1 x t) • g t - (-κ * K 1 y t) • g t = _
        rw [← sub_smul, mul_sub]
      rw [hEq, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hκ.le]
      have hD := abs_poissonInversePower_one_sub_le x y t ht₁.symm ht₂.symm
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hκ.le) (norm_nonneg (g t))
      exact h.trans_eq (by dsimp only [K]; ring)

end Thesis

end
