module

public import Thesis.Variational.InteriorBulkSmall
public import Thesis.Variational.InteriorScaledDefect
import Thesis.Variational.InteriorDerivativeAlgebra

/-! Quantitative regular-ball bounds in terms of the actual essential
gradient bound of the strong limit. -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

noncomputable section

namespace Thesis

local instance interiorTensorTraceNorm : Norm (Tensor →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ) (E := Tensor) (F := ℝ)

private theorem classicalGradientNormSq_nonneg (q : Point → S0) (x : Point) :
    0 ≤ gradientNormSq (ClassicalGradient q x) := by
  rw [gradientNormSq_eq_sum_norm_sq]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- On a regular ball the essential supremum of the actual gradient controls
the pointwise gradient of the same smooth representative. -/
theorem classicalGradient_le_eLpNorm_top_on_regular_ball {Ω : Set Point} (hΩ : IsOpen Ω)
    {q : Point → S0} (hq : ContDiffOn ℝ ∞ q Ω) {c : Point} {r : ℝ}
    (hClosed : closedBall c r ⊆ Ω) :
    let g (y : Point) := Real.sqrt (gradientNormSq (ClassicalGradient q y))
    ∀ x ∈ ball c r, g x ≤ (eLpNorm g ⊤ (volume.restrict (ball c r))).toReal := by
  let g (y : Point) := Real.sqrt (gradientNormSq (ClassicalGradient q y))
  let B := ball c r
  let μ := (volume : Measure Point).restrict B
  let L := (eLpNorm g ⊤ μ).toReal
  have hCont : ContinuousOn g Ω := by
    have h : ContinuousOn (fun y => ∑ i : Fin 3, ‖coordDeriv i q y‖ ^ 2) Ω :=
      continuousOn_finsetSum _ fun i _ => ((contDiffOn_coordDeriv_infty hΩ hq i).continuousOn.norm).pow 2
    have h' : ContinuousOn (fun x => gradientNormSq (ClassicalGradient q x)) Ω := by
      simpa only [gradientNormSq_eq_sum_norm_sq, ClassicalGradient] using h
    exact h'.sqrt
  obtain ⟨C, hC⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn (hCont.mono hClosed)
  have hAE : ∀ᵐ x ∂μ, ‖g x‖ ≤ C := (ae_restrict_mem isOpen_ball.measurableSet).mono
    fun x hx => hC x (ball_subset_closedBall hx)
  have hFin : eLpNorm g ⊤ μ ≠ ⊤ := by
    rw [eLpNorm_exponent_top]
    exact ((eLpNormEssSup_le_of_ae_bound hAE).trans_lt ENNReal.ofReal_lt_top).ne
  have h₁ : ∀ᵐ x ∂μ, g x ≤ L := by
    filter_upwards [enorm_ae_le_eLpNormEssSup g μ] with x hx
    have hL : 0 ≤ L := ENNReal.toReal_nonneg
    apply (ENNReal.ofReal_le_ofReal_iff hL).mp
    change ENNReal.ofReal (g x) ≤ ENNReal.ofReal ((eLpNorm g ⊤ μ).toReal)
    rw [ENNReal.ofReal_toReal hFin, eLpNorm_exponent_top]
    rwa [← ofReal_norm, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hx
  have hEq : g =ᵐ[μ] fun x => min (g x) L := h₁.mono fun _ h => (min_eq_left h).symm
  have hCB := hCont.mono (ball_subset_closedBall.trans hClosed)
  have hOn := Measure.eqOn_open_of_ae_eq hEq isOpen_ball hCB (hCB.inf continuousOn_const)
  exact fun x hx => (hOn hx).trans_le (min_le_right _ _)

private theorem normalized_regular_ball_energy_bound (a : BulkCoefficients) (ε : ElasticScale)
    {W : Set Point} {c : Point} {R L : ℝ} (hR : 0 < R)
    (hBall : ball c R ⊆ W) (Q q : Point → S0)
    (hQ₀ : ∀ x ∈ ball c R, Real.sqrt (gradientNormSq (ClassicalGradient q x)) ≤ L)
    (hG : ∀ j, MemLp (fun x => ClassicalGradient q x j) 2 (volume.restrict W)) :
    ENNReal.ofReal R⁻¹ * energy a ε (ball c R) Q (ClassicalGradient Q) ≤
      ENNReal.ofReal R⁻¹ * energyDensityDefect a ε W Q (ClassicalGradient Q) (ClassicalGradient q) +
        ENNReal.ofReal ((L ^ 2 / 2) * (Real.pi * 4 / 3) * R ^ 2) := by
  have hGrad (x : Point) (hx : x ∈ ball c R) : gradientNormSq (ClassicalGradient q x) ≤ L ^ 2 := by
    have hSq := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hQ₀ x hx) 2
    rwa [Real.sq_sqrt (classicalGradientNormSq_nonneg q x)] at hSq
  have hD : dirichletEnergy (ball c R) (ClassicalGradient q) ≤
      ENNReal.ofReal (L ^ 2 / 2) * volume (ball c R) := by
    rw [dirichletEnergy, ← Measure.restrict_apply_univ, ← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    apply ENNReal.ofReal_le_ofReal
    linarith only [hGrad x hx]
  have hX := energy_le_dirichletEnergy_add_energyDensityDefect a ε Q (ClassicalGradient Q) (ClassicalGradient q) hBall hG
  refine (mul_le_mul_right (hX.trans (add_le_add hD le_rfl)) _).trans_eq ?_
  rw [mul_add, add_comm, EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hR.le,
    ← ENNReal.ofReal_mul (pow_nonneg hR.le 3), ← ENNReal.ofReal_mul (by positivity : 0 ≤ L ^ 2 / 2),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hR.le)]
  congr 2
  field_simp

/-- The regular-ball zeroth-order inputs for the interior derivative
estimate are uniform in the regular sequence, once the radius and the
limiting gradient bound are fixed. -/
theorem exists_eventual_interior_biaxial_orderZero_bound (a : BulkCoefficients)
    (hEstimate : InteriorPoissonGradientEstimate) (hMean : External.ClassicalScalarSubsolutionMeanValue)
    (r ρ L : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) (hL : 0 ≤ L) :
    ∃ C > (0 : ℝ), ∀ (c : Point) (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (q : Point → S0),
      Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
      (∀ n, ContDiffOn ℝ ∞ (Q n) (ball c r)) → ContDiffOn ℝ 2 q (ball c r) →
      (∀ n x, x ∈ ball c r → (ε n : ℝ) ^ 2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x)) →
      BddAbove ((fun p : ℕ × Point => ‖Q p.1 p.2‖) '' (univ ×ˢ ball c r)) →
      (∀ x ∈ ball c r, Real.sqrt (gradientNormSq (ClassicalGradient q x)) ≤ L) →
      StrongH1Loc (ball c r) Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q) →
      ConvergesScaledPotentialLoc a (ball c r) ε Q →
      ∀ᶠ n in atTop, ∀ x ∈ ball c ρ,
        |scaledNormDefect a (ε n) (Q n x)| ≤ C ∧ |scaledCubicTrace a (ε n) (Q n x)| ≤ C ∧
          Real.sqrt (gradientNormSq (ClassicalGradient (Q n) x)) ≤ C := by
  obtain ⟨δ₀, E₀, hδ₀, hE₀, hSmall⟩ := exists_interior_smallEnergy_density_bound a hMean
  obtain ⟨δ₁, D, hδ₁, hD, hDef⟩ := exists_uniform_scaledDefect_bound_on_interior_ball a
  let g := (r - ρ) / 8
  let J := (L ^ 2 / 2) * (Real.pi * 4 / 3)
  let R := min (g / 2) (Real.sqrt (E₀ / (4 * (J + 1))))
  let G := 512 / R ^ 2
  let C₀ := D * (G + g⁻¹ ^ 2)
  let C := 1 + C₀ + ‖tensorTraceCLM‖ * C₀ + Real.sqrt G
  have hg : 0 < g := div_pos (sub_pos.mpr hρr) (by norm_num)
  have hJ : 0 ≤ J :=
    mul_nonneg (div_nonneg (pow_nonneg hL _) (by norm_num)) (by positivity)
  have hJR : 0 < 4 * (J + 1) := by positivity
  have hR : 0 < R := lt_min (half_pos hg) (Real.sqrt_pos.mpr (div_pos hE₀ hJR))
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hnC : 0 ≤ ‖tensorTraceCLM‖ * C₀ := mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hC₀
  have hC : 0 < C := by dsimp only [C]; linarith only [hC₀, hnC, Real.sqrt_nonneg G]
  refine ⟨C, hC, ?_⟩
  intro c ε Q q hε hQ hq hEuler hBdd hqGrad hStrong hBulk
  let Ω := ball c r
  let W := ball c (ρ + 4 * g)
  let K := closedBall c (ρ + 3 * g)
  let δ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  have hKΩ : K ⊆ Ω := fun x hx => mem_ball.mpr (by
    have h := mem_closedBall.mp hx
    dsimp only [g] at h
    linarith only [h, hρr])
  have hrW : 0 < ρ + 4 * g := by positivity
  have hWΩ : CompactlyContained W Ω := by
    rw [CompactlyContained, show closure W = closedBall c (ρ + 4 * g) from closure_ball _ hrW.ne']
    refine ⟨isCompact_closedBall _ _, fun x hx => mem_ball.mpr ?_⟩
    have h := mem_closedBall.mp hx
    dsimp only [g] at h
    linarith only [h, hρr]
  have hRsmall : R ≤ g / 2 := min_le_left _ _
  have hB (x : Point) (hx : x ∈ closedBall c (ρ + 2 * g)) :
      ball x R ⊆ K := fun y hy => mem_closedBall.mpr (by
    linarith only [mem_ball.mp hy, mem_closedBall.mp hx, dist_triangle y x c, hRsmall, hg])
  have hSubKW : K ⊆ W := fun x hx => mem_ball.mpr (by linarith only [mem_closedBall.mp hx, hg])
  obtain ⟨M, hM⟩ := hBdd
  have hRange (n : ℕ) (x : Point) (hx : x ∈ Ω) : ‖Q n x‖ ≤ max 0 M :=
    (show ‖Q n x‖ ≤ M from hM ⟨(n, x), ⟨mem_univ _, hx⟩, rfl⟩).trans (le_max_right _ _)
  have hNear := (eventually_uniform_interior_bulk_and_vacuum_small a isOpen_ball (isCompact_closedBall _ _)
    hKΩ hEstimate hq ε Q hε hQ hEuler hRange hStrong (fun V hV hVΩ => (hBulk V hV hVΩ).1)
    (fun V hV hVΩ => (hBulk V hV hVΩ).2)).2 δ hδ
  have hStrongW := hStrong W isOpen_ball hWΩ
  have hDefect := tendsto_energyDensityDefect_zero_of_strongH1 a ε hStrongW
    (hBulk W isOpen_ball hWΩ).1 (hBulk W isOpen_ball hWΩ).2
  have hJsmall : J * R ^ 2 ≤ E₀ / 4 := by
    have hRR := pow_le_pow_left₀ hR.le (min_le_right (g / 2) (Real.sqrt (E₀ / (4 * (J + 1))))) 2
    rw [Real.sq_sqrt (div_nonneg hE₀.le hJR.le)] at hRR
    have h := (le_div_iff₀ hJR).mp hRR
    nlinarith only [h, sq_nonneg R]
  have hPos : 0 < ENNReal.ofReal (R * (E₀ / 4)) := by positivity
  filter_upwards [hNear, hDefect (Iio_mem_nhds hPos)] with n hnNear hnDef
  have hErr : ENNReal.ofReal R⁻¹ * energyDensityDefect a (ε n) W (Q n) (ClassicalGradient (Q n))
      (ClassicalGradient q) ≤ ENNReal.ofReal (E₀ / 4) := by
    refine (mul_le_mul_right hnDef.le _).trans_eq ?_
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hR.le), ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  have hGrad (x : Point) (hx : x ∈ closedBall c (ρ + 2 * g)) : gradientNormSq (ClassicalGradient (Q n) x) ≤ G := by
    have hBX := hB x hx
    have hEW := normalized_regular_ball_energy_bound a (ε n) hR (hBX.trans hSubKW) (Q n) q
      (fun y hy => hqGrad y (hKΩ (hBX hy))) hStrongW.2.1.2.1
    have hE : ENNReal.ofReal R⁻¹ * energy a (ε n) (ball x R) (Q n) (ClassicalGradient (Q n)) < ENNReal.ofReal E₀ :=
      (hEW.trans (add_le_add hErr (ENNReal.ofReal_le_ofReal hJsmall))).trans_lt (by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact (ENNReal.ofReal_lt_ofReal_iff hE₀).mpr (by linarith only [hE₀]))
    have hEn := hSmall (ε n) x R hR (Q n) ((hQ n).mono (hBX.trans hKΩ))
      (fun y hy => hEuler n y (hKΩ (hBX hy)))
      (fun y hy => (hnNear y (hBX hy)).trans_le (min_le_left _ _)) hE x (mem_ball_self (half_pos hR))
    have hPot : 0 ≤ (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n x) :=
      mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _)
    have hE' : energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ 256 / R ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hR)).mpr ((mul_comm _ _).le.trans hEn)
    unfold energyDensity at hE'
    change gradientNormSq (ClassicalGradient (Q n) x) ≤ 512 / R ^ 2
    rw [show (512 : ℝ) / R ^ 2 = 2 * (256 / R ^ 2) by ring]
    linarith only [hE', hPot]
  intro x hx
  have hBX : ball x g ⊆ closedBall c (ρ + 2 * g) := fun y hy => mem_closedBall.mpr
    (by linarith only [mem_ball.mp hy, mem_ball.mp hx, dist_triangle y x c, hg])
  have hK' : closedBall c (ρ + 2 * g) ⊆ K := closedBall_subset_closedBall (by linarith)
  have hLift := hDef (ε n) x g hg (Q n) (((contDiffOn_infty.mp (hQ n)) 2).mono (hBX.trans (hK'.trans hKΩ)))
    (fun y hy => (hnNear y (hK' (hBX hy))).trans_le (min_le_right _ _))
    (fun y hy => hEuler n y (hKΩ (hK' (hBX hy)))) G hG (fun y hy => hGrad y (hBX hy))
    x (mem_ball_self (half_pos hg))
  have hPot : 0 ≤ ((ε n : ℝ) ^ 2)⁻¹ * Real.sqrt (bulkPotential a (Q n x)) := by positivity
  have hH : |scaledNormDefect a (ε n) (Q n x)| ≤ C₀ := by
    nlinarith only [hLift, hPot, norm_nonneg (laplacian (Q n) x), norm_nonneg (scaledCubicDefect a (ε n) (Q n x))]
  have hY : ‖scaledCubicDefect a (ε n) (Q n x)‖ ≤ C₀ := by
    nlinarith only [hLift, hPot, norm_nonneg (laplacian (Q n) x), abs_nonneg (scaledNormDefect a (ε n) (Q n x))]
  have hT : |scaledCubicTrace a (ε n) (Q n x)| ≤ ‖tensorTraceCLM‖ * C₀ :=
    (tensorTraceCLM.le_opNorm (scaledCubicDefect a (ε n) (Q n x))).trans
      (mul_le_mul_of_nonneg_left hY (ContinuousLinearMap.opNorm_nonneg _))
  have hQ₀ : Real.sqrt (gradientNormSq (ClassicalGradient (Q n) x)) ≤ Real.sqrt G :=
    Real.sqrt_le_sqrt (hGrad x (hBX (mem_ball_self hg)))
  exact ⟨hH.trans (by dsimp only [C]; linarith only [hnC, Real.sqrt_nonneg G]),
    hT.trans (by dsimp only [C]; linarith only [hC₀, Real.sqrt_nonneg G]),
    hQ₀.trans (by dsimp only [C]; linarith only [hC₀, hnC])⟩

end Thesis

end
