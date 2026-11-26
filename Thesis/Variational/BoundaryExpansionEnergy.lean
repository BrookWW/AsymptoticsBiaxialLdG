module

public import Thesis.Variational.BoundarySmallEnergyAssembly
public import Thesis.Variational.BoundaryScaledGradient

/-! Uniform energy density on a regular wall collar for the expansion. -/

public section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem energy_mass_le_of_normalized_le {r E : ℝ} (hr : 0 < r) {e : ℝ≥0∞}
    (h : ENNReal.ofReal r⁻¹ * e ≤ ENNReal.ofReal E) : e ≤ ENNReal.ofReal (E * r) := by
  have hEq : ENNReal.ofReal r * ENNReal.ofReal r⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one]
  calc
    e = ENNReal.ofReal r * (ENNReal.ofReal r⁻¹ * e) := by rw [← mul_assoc, hEq, one_mul]
    _ ≤ ENNReal.ofReal r * ENNReal.ofReal E := mul_le_mul_right h _
    _ = _ := by rw [← ENNReal.ofReal_mul hr.le, mul_comm]

/-- The regular fixed collar has a uniform classical energy density bound
for the sequence used in the expansion. The radius is chosen from the
limit collar and fixed trace before taking the sequence tail. -/
theorem exists_eventual_energyDensity_bound_on_regular_wall_collar
    (hGG : External.LipschitzGaussGreen) (hSard : External.MorseSardPlaneToReal)
    (hPoisson : External.ZeroTraceBoundaryPoissonL4GradientEstimate)
    (hMean : External.ClassicalScalarSubsolutionMeanValue)
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    {b : Point → S0} (hb : ContDiff ℝ 2 b) (hVac : ∀ y ∈ frontier U, b y ∈ vacuum a)
    {V : Set Point} (hV : IsOpen V) {q : Point → S0} {G : Point → Gradient}
    (hq : ContDiffOn ℝ 2 q (closure U ∩ V)) (hGrad : G =ᵐ[volume.restrict U] ClassicalGradient q)
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
    (hRange : ∀ n, ∀ x ∈ U, ‖Q n x‖ ≤ M)
    (hScaled : ∀ n, ∀ x ∈ U, (ε n : ℝ) * Real.sqrt (gradientNormSq (ClassicalGradient (Q n) x)) ≤ B)
    {c : Point} (hc : c ∈ frontier U ∩ V) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ Metric.closedBall c r ⊆ V ∧
      ∀ᶠ n in atTop, ∀ x ∈ U ∩ Metric.ball c (r / 2),
        energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ L := by
  obtain ⟨R, δ₀, E₀, C, hR, hδ₀, hE₀, hC, hReg⟩ := exists_boundary_classical_smallEnergy_bound hPoisson hMean a hU
  obtain ⟨rV, hrV, hBallV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hc.2)
  let K := closure U ∩ Metric.closedBall c (rV / 2)
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_left isClosed_closure
  have hKV : K ⊆ closure U ∩ V := fun x hx =>
    ⟨hx.1, hBallV (Metric.closedBall_subset_ball (half_lt_self hrV) hx.2)⟩
  have hb₁ : ContDiffOn ℝ 1 b (closure U) := (hb.of_le (by norm_num)).contDiffOn
  let E := E₀ / 2
  let d := δ₀ / 2
  have hE : 0 < E := half_pos hE₀
  have hd : 0 < d := half_pos hδ₀
  obtain ⟨rM, hrM, hMorrey⟩ := exists_boundary_collar_uniform_small_normalized_energy
    hGG hSard a hU hb₁ hVac hV hK hKV hq hGrad ε Q hStrong hBulkLp hBulk
    hQ hClose hTrace hEuler hC₀ hR₁ hE hCap
  have hNear := (eventually_uniform_bulk_and_vacuum_small_of_strongH1_on_boundary_collar
    hGG hSard a hU hb₁ hVac hV hK hKV hq hGrad ε Q hε hStrong hBulkLp hBulk hQ hClose hTrace hEuler
    hC₀ hR₁ hB hCap hRange hScaled).2 d hd
  obtain ⟨_, B₁, B₂, _, hB₁, hB₂, _, hData, hLap⟩ := exists_compact_trace_bounds hU hb
  let r := min (R / 2) (min rM (rV / 2))
  have hr : 0 < r := lt_min (half_pos hR) (lt_min hrM.1 (half_pos hrV))
  have hrr : r < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hrM' : r ≤ rM := (min_le_right _ _).trans (min_le_left _ _)
  have hrV' : r ≤ rV / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hKBall : U ∩ Metric.ball c r ⊆ U ∩ K := fun x hx =>
    ⟨hx.1, subset_closure hx.1, Metric.ball_subset_closedBall ((Metric.ball_subset_ball hrV') hx.2)⟩
  let L := C * ((B₁ + r * B₂) ^ 2 + r⁻¹ ^ 2 * (E + d ^ 2))
  have hL : 0 ≤ L := mul_nonneg hC.le (add_nonneg (sq_nonneg _)
    (mul_nonneg (sq_nonneg _) (add_nonneg hE.le (sq_nonneg _))))
  refine ⟨r, L, hr, hL, (Metric.closedBall_subset_ball (hrV'.trans_lt (half_lt_self hrV))).trans hBallV, ?_⟩
  filter_upwards [hMorrey, hNear] with n hnMorrey hnNear x hx
  have hEnergy (y : Point) (hy : y ∈ U ∩ Metric.ball c r) (s : ℝ) (hs : s ∈ Ioo 0 r) :
      energy a (ε n) (U ∩ Metric.ball y s) (Q n) (ClassicalGradient (Q n)) ≤ ENNReal.ofReal (E * s) :=
    energy_mass_le_of_normalized_le hs.1 (hnMorrey y (hKBall hy) s ⟨hs.1, hs.2.le.trans hrM'⟩).le
  have hDistance (y : Point) (hy : y ∈ U ∩ Metric.ball c r) :
      Metric.infDist (Q n y) (vacuum a) ≤ d := (hnNear y (hKBall hy)).le
  exact hReg c hc.1 r ⟨hr, hrr⟩ (ε n) (Q n) b B₁ B₂ E d hB₁ hB₂ hE.le (half_lt_self hE₀)
    hd.le (half_lt_self hδ₀) (hQ n) (hClose n) hb.contDiffOn (hTrace n) hVac (hEuler n)
    hDistance hEnergy (fun y hy v => hData y hy.1 v)
    (fun y hy => hLap y (subset_closure hy.1)) x hx


/-- The regular wall collar bound uses the uniform scaled gradient
produced by the fixed-trace Poisson estimates. -/
theorem exists_eventual_energyDensity_bound_on_regular_wall_collar_from_poisson
    (hGG : External.LipschitzGaussGreen) (hSard : External.MorseSardPlaneToReal)
    (hPoisson : External.ZeroTraceBoundaryPoissonL4GradientEstimate)
    (hMean : External.ClassicalScalarSubsolutionMeanValue) (hInterior : InteriorPoissonGradientEstimate)
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    {b : Point → S0} (hb : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) b) (hVac : ∀ y ∈ frontier U, b y ∈ vacuum a)
    {V : Set Point} (hV : IsOpen V) {q : Point → S0} {G : Point → Gradient}
    (hq : ContDiffOn ℝ 2 q (closure U ∩ V)) (hGrad : G =ᵐ[volume.restrict U] ClassicalGradient q)
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
    {C₀ R₁ M : ℝ} (hC₀ : 0 ≤ C₀) (hR₁ : 0 < R₁) (hM : 0 ≤ M)
    (hCap : ∀ n, energy a (ε n) U (Q n) (ClassicalGradient (Q n)) ≤ ENNReal.ofReal C₀)
    (hRange : ∀ n, ∀ x ∈ U, ‖Q n x‖ ≤ M)
    {c : Point} (hc : c ∈ frontier U ∩ V) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ Metric.closedBall c r ⊆ V ∧
      ∀ᶠ n in atTop, ∀ x ∈ U ∩ Metric.ball c (r / 2),
        energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ L := by
  obtain ⟨B, hB, hScaled⟩ := exists_uniform_scaledGradient_bound_on_smoothDomain
    hGG hPoisson hInterior a hU hb hM
  have hb₂ : ContDiff ℝ 2 b := hb.of_le (WithTop.coe_le_coe.mpr le_top)
  exact exists_eventual_energyDensity_bound_on_regular_wall_collar hGG hSard hPoisson hMean a hU
    hb₂ hVac hV hq hGrad ε Q hε hStrong hBulkLp hBulk hQ hClose hTrace hEuler hC₀ hR₁ hB.le hCap
    hRange (fun n => hScaled (ε n) (Q n) (hQ n) (hClose n) (hTrace n) (hRange n) (hEuler n)) hc

end Thesis

end
