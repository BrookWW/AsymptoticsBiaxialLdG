module

public import Thesis.Variational.BoundaryMonotonicity
import Thesis.Interpolation.PenalizedEdge
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Uniform approach to the vacuum on regular boundary collars. -/

public section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance boundaryBulkPotentialDerivativeNorm : Norm (S0 →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ) (E := S0) (F := ℝ)

local instance boundaryFieldDerivativeNorm : Norm (Point →L[ℝ] S0) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ) (E := Point) (F := S0)

private theorem fderiv_bulkPotential_eq_zero_of_mem_vacuum
    (a : BulkCoefficients) {q : S0} (hq : q ∈ vacuum a) :
    fderiv ℝ (bulkPotential a) q = 0 := by
  apply IsLocalMin.hasFDerivAt_eq_zero
    (hf := ((contDiff_bulkPotential a).differentiable (by simp) q).hasFDerivAt)
  filter_upwards [] with z
  rw [(bulkPotential_eq_zero_iff a q).mpr hq]
  exact bulkPotential_nonneg a z

/-- The zero extension of the scaled bulk potential is globally Lipschitz.
The constant uses the fixed range and scaled gradient bounds. -/
theorem exists_lipschitzWith_scaled_zeroExtended_bulkPotential
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U)
    {M B : ℝ} (hB : 0 ≤ B) :
    ∃ L : ℝ≥0, ∀ (ε : ElasticScale) (Q : Point → S0),
      ContDiffOn ℝ 2 Q (closure U) →
      (∀ x ∈ frontier U, Q x ∈ vacuum a) →
      (∀ x ∈ U, ‖Q x‖ ≤ M) →
      (∀ x ∈ U, (ε : ℝ) * Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ B) →
      LipschitzWith L (fun x => (ε : ℝ) * U.indicator (fun y => bulkPotential a (Q y)) x) := by
  have hPot := contDiff_bulkPotential a
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : S0) M).exists_bound_of_continuousOn
    (hPot.continuous_fderiv (by simp)).continuousOn
  let L : ℝ≥0 := ⟨max K 0 * B, mul_nonneg (le_max_right _ _) hB⟩
  refine ⟨L, fun ε Q hQ hWall hRange hGrad => ?_⟩
  let f (x : Point) := (ε : ℝ) * bulkPotential a (Q x)
  let F (x : Point) := (ε : ℝ) * U.indicator (fun y => bulkPotential a (Q y)) x
  let D (x : Point) : Point →L[ℝ] ℝ := (ε : ℝ) •
    (fderiv ℝ (bulkPotential a) (Q x)).comp (fderivWithin ℝ Q (closure U) x)
  have hFOn : EqOn F f (closure U) := by
    intro x hx
    by_cases hxU : x ∈ U
    · simp only [F, f, Set.indicator_of_mem hxU]
    · have hxW : x ∈ frontier U := by rw [frontier, hU.interior_eq]; exact ⟨hx, hxU⟩
      simp only [F, f, Set.indicator_of_notMem hxU, (bulkPotential_eq_zero_iff a _).mpr (hWall x hxW)]
  have hFZero : EqOn F (fun _ => 0) Uᶜ := by
    intro x hx
    simp only [F, Set.indicator_of_notMem (show x ∉ U from hx), mul_zero]
  have hDWithin (x : Point) (hx : x ∈ closure U) : HasFDerivWithinAt F (D x) (closure U) x := by
    have hDQ := ((hQ x hx).differentiableWithinAt (by norm_num : (2 : ℕ∞ω) ≠ 0)).hasFDerivWithinAt
    have hDP := (hPot.differentiable (by simp) (Q x)).hasFDerivAt
    have hD' : HasFDerivWithinAt f (D x) (closure U) x := (hDP.comp_hasFDerivWithinAt x hDQ).const_mul _
    exact hD'.congr' hFOn hx
  have hInterior (x : Point) (hx : x ∈ U) : HasFDerivAt F (D x) x :=
    (hDWithin x (subset_closure hx)).hasFDerivAt (mem_of_superset (hU.mem_nhds hx) subset_closure)
  have hExterior (x : Point) (hx : x ∉ U) : HasFDerivAt F (0 : Point →L[ℝ] ℝ) x := by
    have hZero : HasFDerivWithinAt F (0 : Point →L[ℝ] ℝ) Uᶜ x :=
      (hasFDerivWithinAt_const (c := (0 : ℝ)) x Uᶜ).congr' hFZero hx
    by_cases hxC : x ∈ closure U
    · have hxW : x ∈ frontier U := by rw [frontier, hU.interior_eq]; exact ⟨hxC, hx⟩
      have hDz : D x = 0 := by
        change (ε : ℝ) • (fderiv ℝ (bulkPotential a) (Q x)).comp
          (fderivWithin ℝ Q (closure U) x) = 0
        rw [fderiv_bulkPotential_eq_zero_of_mem_vacuum a (hWall x hxW), ContinuousLinearMap.zero_comp,
          smul_zero]
      have hBoth := ((hDWithin x hxC).congr_fderiv hDz).union hZero
      have hAll : closure U ∪ Uᶜ = univ := by
        apply Set.eq_univ_of_forall
        intro y
        by_cases hy : y ∈ U
        · exact Or.inl (subset_closure hy)
        · exact Or.inr hy
      rwa [hAll, hasFDerivWithinAt_univ] at hBoth
    · exact hZero.hasFDerivAt (mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hxC)
        (compl_subset_compl.mpr subset_closure))
  have hDiff (x : Point) : DifferentiableAt ℝ F x := by
    by_cases hx : x ∈ U
    · exact (hInterior x hx).differentiableAt
    · exact (hExterior x hx).differentiableAt
  change LipschitzWith L F
  apply lipschitzWith_of_nnnorm_fderiv_le hDiff
  intro x
  by_cases hx : x ∈ U
  · rw [(hInterior x hx).fderiv]
    have hP : ‖fderiv ℝ (bulkPotential a) (Q x)‖ ≤ max K 0 :=
      (hK _ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hRange x hx)).trans (le_max_left _ _)
    have hQ' : ‖fderivWithin ℝ Q (closure U) x‖ ≤ Real.sqrt (gradientNormSq (ClassicalGradient Q x)) := by
      apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
      intro v
      have hBridge := gradientFromColumns_closureGradient U Q x v
      rw [closureGradient_eq_classicalGradient hU hQ hx] at hBridge
      exact (congrArg (fun z : S0 => ‖z‖) hBridge).symm.le.trans
        ((norm_gradientFromColumns_le (ClassicalGradient Q x) v).trans_eq (mul_comm _ _))
    have hε : 0 ≤ (ε : ℝ) := ε.2.1.le
    change ‖D x‖ ≤ max K 0 * B
    calc
      _ ≤ (ε : ℝ) * (max K 0 * Real.sqrt (gradientNormSq (ClassicalGradient Q x))) := by
        change ‖(ε : ℝ) • (fderiv ℝ (bulkPotential a) (Q x)).comp
          (fderivWithin ℝ Q (closure U) x)‖ ≤ _
        rw [norm_smul, Real.norm_of_nonneg hε]
        apply mul_le_mul_of_nonneg_left _ hε
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hP hQ' (norm_nonneg _) (le_max_right _ _))
      _ = max K 0 * ((ε : ℝ) * Real.sqrt (gradientNormSq (ClassicalGradient Q x))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hGrad x hx) (le_max_right _ _)
  · rw [(hExterior x hx).fderiv, nnnorm_zero]
    exact zero_le

private theorem microscopic_ball_bulk_lower
    (a : BulkCoefficients) (ε : ElasticScale) {U : Set Point} {Q : Point → S0}
    {L : ℝ≥0}
    (hLip : LipschitzWith L (fun x => (ε : ℝ) * U.indicator (fun y => bulkPotential a (Q y)) x))
    {x : Point} (hx : x ∈ U) {d : ℝ} (hd : 0 < d) (hPeak : d ≤ bulkPotential a (Q x)) :
    let c := d / (2 * ((L : ℝ) + 1))
    Metric.ball x (c * (ε : ℝ)) ⊆ U ∩ {y | d / 2 ≤ bulkPotential a (Q y)} := by
  let c := d / (2 * ((L : ℝ) + 1))
  have hL₁ : 0 < (L : ℝ) + 1 := by positivity
  have hc : 0 < c := div_pos hd (mul_pos (by norm_num) hL₁)
  have hε : 0 < (ε : ℝ) := ε.2.1
  change Metric.ball x (c * (ε : ℝ)) ⊆ U ∩ {y | d / 2 ≤ bulkPotential a (Q y)}
  intro y hy
  let P (z : Point) := U.indicator (fun t => bulkPotential a (Q t)) z
  have hPx : P x = bulkPotential a (Q x) := indicator_of_mem hx _
  have hy' : dist y x < c * (ε : ℝ) := Metric.mem_ball.mp hy
  have hDist := hLip.dist_le_mul y x
  change dist ((ε : ℝ) * P y) ((ε : ℝ) * P x) ≤ (L : ℝ) * dist y x at hDist
  rw [Real.dist_eq, hPx] at hDist
  have hComp : (L : ℝ) * dist y x ≤ (ε : ℝ) * (d / 2) := calc
    _ ≤ ((L : ℝ) + 1) * (c * (ε : ℝ)) :=
      mul_le_mul (le_add_of_nonneg_right zero_le_one) hy'.le dist_nonneg hL₁.le
    _ = _ := by dsimp only [c]; field_simp
  have hDiff := (neg_le_neg (hDist.trans hComp)).trans
    (neg_abs_le ((ε : ℝ) * P y - (ε : ℝ) * bulkPotential a (Q x)))
  have hStart := mul_le_mul_of_nonneg_left hPeak hε.le
  have hyLow : d / 2 ≤ P y := by
    apply (mul_le_mul_iff_right₀ hε).mp
    linarith only [hDiff, hStart]
  have hyMem : y ∈ U := by
    by_contra hn
    have hy0 : P y = 0 := indicator_of_notMem hn _
    linarith only [hyLow, hy0, hd]
  refine ⟨hyMem, ?_⟩
  simpa only [P, Set.indicator_of_mem hyMem, mem_setOf_eq] using hyLow

/-- At a positive bulk peak the whole microscopic ball lies in the domain.
Its normalized energy has a scale-independent positive lower bound. -/
theorem normalized_energy_microscopic_ball_lower_of_bulk_peak
    (a : BulkCoefficients) (ε : ElasticScale) {U : Set Point} {Q : Point → S0}
    {L : ℝ≥0}
    (hLip : LipschitzWith L (fun x => (ε : ℝ) * U.indicator (fun y => bulkPotential a (Q y)) x))
    {x : Point} (hx : x ∈ U) {d : ℝ} (hd : 0 < d) (hPeak : d ≤ bulkPotential a (Q x)) :
    let c := d / (2 * ((L : ℝ) + 1))
    let r := c * (ε : ℝ)
    ENNReal.ofReal ((d / 2) * (Real.pi * 4 / 3) * c ^ 2) ≤ ENNReal.ofReal (r⁻¹) *
      energy a ε (U ∩ Metric.ball x r) Q (ClassicalGradient Q) := by
  let c := d / (2 * ((L : ℝ) + 1))
  let r := c * (ε : ℝ)
  let b := (ε : ℝ)⁻¹ ^ 2 * (d / 2)
  have hε : 0 < (ε : ℝ) := ε.2.1
  have hc : 0 < c := by dsimp only [c]; positivity
  have hr : 0 < r := mul_pos hc hε
  have hb : 0 ≤ b := mul_nonneg (sq_nonneg _) (half_pos hd).le
  have hBall := microscopic_ball_bulk_lower a ε hLip hx hd hPeak
  have hSub : Metric.ball x r ⊆ U := fun y hy => (hBall hy).1
  have hEq : U ∩ Metric.ball x r = Metric.ball x r := inter_eq_right.mpr hSub
  have hElow : ENNReal.ofReal b * volume (Metric.ball x r) ≤
      energy a ε (U ∩ Metric.ball x r) Q (ClassicalGradient Q) := by
    rw [hEq, energy, ← Measure.restrict_apply_univ, ← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
    apply ENNReal.ofReal_le_ofReal
    have hB : d / 2 ≤ bulkPotential a (Q y) := (hBall hy).2
    have hG : 0 ≤ gradientNormSq (ClassicalGradient Q y) := by
      rw [gradientNormSq_eq_sum_norm_sq]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    unfold energyDensity
    exact (mul_le_mul_of_nonneg_left hB (sq_nonneg _)).trans
      (le_add_of_nonneg_left (mul_nonneg (by norm_num) hG))
  calc
    ENNReal.ofReal ((d / 2) * (Real.pi * 4 / 3) * c ^ 2) =
        ENNReal.ofReal r⁻¹ * (ENNReal.ofReal b * volume (Metric.ball x r)) := by
      rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hr.le,
        ← ENNReal.ofReal_mul (pow_nonneg hr.le 3), ← ENNReal.ofReal_mul hb,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
      congr 1
      change (d / 2) * (Real.pi * 4 / 3) * c ^ 2 =
        (c * (ε : ℝ))⁻¹ * ((ε : ℝ)⁻¹ ^ 2 * (d / 2) * ((c * (ε : ℝ)) ^ 3 * (Real.pi * 4 / 3)))
      field_simp [hc.ne', hε.ne']
    _ ≤ _ := mul_le_mul_right hElow _

/-- The collar energy estimate and a uniform scaled gradient bound exclude
microscopic bulk peaks. The same fixed collar approaches the vacuum uniformly. -/
theorem eventually_uniform_bulk_and_vacuum_small_of_collar_energy
    (a : BulkCoefficients) {U K : Set Point} (hU : IsOpen U)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    {M B : ℝ} (hB : 0 ≤ B)
    (hClose : ∀ n, ContDiffOn ℝ 2 (Q n) (closure U))
    (hVac : ∀ n, ∀ x ∈ frontier U, Q n x ∈ vacuum a)
    (hRange : ∀ n, ∀ x ∈ U, ‖Q n x‖ ≤ M)
    (hGrad : ∀ n, ∀ x ∈ U, (ε n : ℝ) * Real.sqrt (gradientNormSq (ClassicalGradient (Q n) x)) ≤ B)
    (hSmall : ∀ τ : ℝ, 0 < τ → ∃ R > (0 : ℝ), ∀ᶠ n in atTop, ∀ x ∈ U ∩ K, ∀ s ∈ Ioc 0 R,
      ENNReal.ofReal (s⁻¹) * energy a (ε n) (U ∩ Metric.ball x s) (Q n) (ClassicalGradient (Q n)) <
        ENNReal.ofReal τ) :
    (∀ d : ℝ, 0 < d → ∀ᶠ n in atTop, ∀ x ∈ U ∩ K, bulkPotential a (Q n x) < d) ∧
    (∀ d : ℝ, 0 < d → ∀ᶠ n in atTop, ∀ x ∈ U ∩ K, Metric.infDist (Q n x) (vacuum a) < d) := by
  obtain ⟨L, hL⟩ := exists_lipschitzWith_scaled_zeroExtended_bulkPotential a hU (M := M) hB
  have hBulk : ∀ d : ℝ, 0 < d → ∀ᶠ n in atTop, ∀ x ∈ U ∩ K, bulkPotential a (Q n x) < d := by
    intro d hd
    let c := d / (2 * ((L : ℝ) + 1))
    let τ := (d / 2) * (Real.pi * 4 / 3) * c ^ 2
    have hc : 0 < c := by dsimp only [c]; positivity
    have hτ : 0 < τ := by dsimp only [τ]; positivity
    obtain ⟨R, hR, hEnergy⟩ := hSmall τ hτ
    have hRad : Tendsto (fun n => c * (ε n : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hε
    have hMicro : ∀ᶠ n in atTop, c * (ε n : ℝ) < R := hRad (Iio_mem_nhds hR)
    filter_upwards [hEnergy, hMicro] with n hnEnergy hnRad x hx
    by_contra hNot
    have hs : c * (ε n : ℝ) ∈ Ioc 0 R := ⟨mul_pos hc (ε n).2.1, hnRad.le⟩
    have hLip := hL (ε n) (Q n) (hClose n) (hVac n) (hRange n) (hGrad n)
    have hLB := normalized_energy_microscopic_ball_lower_of_bulk_peak a (ε n) hLip hx.1 hd (le_of_not_gt hNot)
    exact (not_lt_of_ge hLB) (hnEnergy x hx _ hs)
  refine ⟨hBulk, ?_⟩
  obtain ⟨C, hC, hDist⟩ := vacuumDistance_sq_le_bulkPotential_of_norm_le a M
  intro d hd
  filter_upwards [hBulk (d ^ 2 / C) (div_pos (sq_pos_of_pos hd) hC)] with n hn x hx
  have hUp := hDist (Q n x) (hRange n x hx.1)
  have hDown := mul_lt_mul_of_pos_left (hn x hx) hC
  have hCancel : C * (d ^ 2 / C) = d ^ 2 := by field_simp [hC.ne']
  rw [hCancel] at hDown
  exact (sq_lt_sq₀ Metric.infDist_nonneg hd.le).mp (hUp.trans_lt hDown)

/-- The actual penalized solutions approach the vacuum uniformly on a fixed
regular compact collar. The scaled gradient bound is the input from the
classical Dirichlet gradient estimate. -/
theorem eventually_uniform_bulk_and_vacuum_small_of_strongH1_on_boundary_collar
    (hGG : External.LipschitzGaussGreen) (hSard : External.MorseSardPlaneToReal)
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    {b : Point → S0} (hb : ContDiffOn ℝ 1 b (closure U)) (hVac : ∀ x ∈ frontier U, b x ∈ vacuum a)
    {V K : Set Point} (hV : IsOpen V) (hK : IsCompact K) (hKsub : K ⊆ closure U ∩ V)
    {q : Point → S0} {G : Point → Gradient} (hq : ContDiffOn ℝ 2 q (closure U ∩ V))
    (hGrad : G =ᵐ[volume.restrict U] ClassicalGradient q)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hStrong : StrongH1 U Q (fun n => ClassicalGradient (Q n)) q G)
    (hBulkLp : ∀ n, MemLp (fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n x)) 1 (volume.restrict U))
    (hBulk : Tendsto (fun n => eLpNorm (fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n x))
      1 (volume.restrict U)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (Q n) U)
    (hClose : ∀ n, ContDiffOn ℝ 2 (Q n) (closure U))
    (hTrace : ∀ n, EqOn (Q n) b (frontier U))
    (hEuler : ∀ n, ∀ x ∈ U, (ε n : ℝ) ^ 2 • (↑(laplacian (Q n) x) : Tensor) = bulkGradient a (Q n x))
    {C₀ R₁ M B : ℝ} (hC₀ : 0 ≤ C₀) (hR₁ : 0 < R₁) (hB : 0 ≤ B)
    (hCap : ∀ n, energy a (ε n) U (Q n) (ClassicalGradient (Q n)) ≤ ENNReal.ofReal C₀)
    (hBound : ∀ n, ∀ x ∈ U, ‖Q n x‖ ≤ M)
    (hScaled : ∀ n, ∀ x ∈ U, (ε n : ℝ) * Real.sqrt (gradientNormSq (ClassicalGradient (Q n) x)) ≤ B) :
    (∀ d : ℝ, 0 < d → ∀ᶠ n in atTop, ∀ x ∈ U ∩ K, bulkPotential a (Q n x) < d) ∧
    (∀ d : ℝ, 0 < d → ∀ᶠ n in atTop, ∀ x ∈ U ∩ K, Metric.infDist (Q n x) (vacuum a) < d) := by
  apply eventually_uniform_bulk_and_vacuum_small_of_collar_energy a hU.1.1 ε Q hε hB hClose
    (fun n x hx => by rw [hTrace n hx]; exact hVac x hx) hBound hScaled
  intro τ hτ
  obtain ⟨R, hR, hEnergy⟩ := exists_boundary_collar_uniform_small_normalized_energy
    hGG hSard a hU hb hVac hV hK hKsub hq hGrad ε Q hStrong hBulkLp hBulk
    hQ hClose hTrace hEuler hC₀ hR₁ hτ hCap
  exact ⟨R, hR.1, hEnergy⟩

end Thesis

end
