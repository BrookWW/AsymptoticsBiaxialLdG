module

public import Thesis.MeasureGeometry.EnergyCylinderTangent

/-! The final comparison of normalized cylinder energy and axial density. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace Thesis.MeasureGeometry

/-- The logarithm in the radius-scaled planar energy is asymptotic to the
ambient logarithm, uniformly over a fixed positive range of radii. -/
theorem eventually_log_radius_ratio_close {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hLim : Tendsto ε atTop (𝓝 0))
    {a b ξ : ℝ} (ha : 0 < a) (_hab : a ≤ b) (hξ : 0 < ξ) :
    ∀ᶠ n : ℕ in atTop, ∀ r ∈ Icc a b,
      |Real.log (r / ε n) / Real.log (1 / ε n) - 1| < ξ := by
  let M := max |Real.log a| |Real.log b|
  have hM : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  have hInv : Tendsto (fun n => (ε n)⁻¹) atTop atTop := by
    apply tendsto_inv_nhdsGT_zero.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨hLim, Eventually.of_forall hε⟩
  have hLog : Tendsto (fun n => Real.log (1 / ε n)) atTop atTop := by
    simpa only [Function.comp_def, one_div] using Real.tendsto_log_atTop.comp hInv
  filter_upwards [(tendsto_atTop.1 hLog) ((M + 1) / ξ)] with n hn
  have hLn : 0 < Real.log (1 / ε n) := (div_pos (by linarith only [hM]) hξ).trans_le hn
  intro r hr
  have hr₀ : 0 < r := ha.trans_le hr.1
  have hLogs : Real.log a ≤ Real.log r ∧ Real.log r ≤ Real.log b :=
    ⟨Real.log_le_log ha hr.1, Real.log_le_log hr₀ hr.2⟩
  have hAbs : |Real.log r| ≤ M := by
    apply abs_le.mpr
    constructor
    · have hLeft : -Real.log a ≤ M := (neg_le_abs _).trans (le_max_left _ _)
      linarith only [hLeft, hLogs.1]
    · exact hLogs.2.trans ((le_abs_self _).trans (le_max_right _ _))
  rw [Real.log_div hr₀.ne' (hε n).ne', one_div, Real.log_inv]
  have hL' : 0 < -Real.log (ε n) := by simpa only [one_div, Real.log_inv] using hLn
  have hNorm : (Real.log r - Real.log (ε n)) / (-Real.log (ε n)) - 1 =
      Real.log r / (-Real.log (ε n)) := by
    have hne : Real.log (ε n) ≠ 0 := by linarith only [hL']
    field_simp [hne]
    ring
  rw [hNorm, abs_div, abs_of_pos hL', div_lt_iff₀ hL']
  have hLarge := (div_le_iff₀ hξ).mp hn
  simp only [one_div, Real.log_inv] at hLarge
  linarith only [hAbs, hLarge]

/-- A uniform comparison with the three exact splitting costs forces the
positive ball density to be one of the two nonzero costs. The cylinder
length in the comparison is the physical height `s*(hi-lo)`. -/
theorem axialDensity_mem_quantized_of_cylinder_comparison
    {Ω : Set Point} {ν : ℕ → Measure Point} {μ : Measure Point} {x e : Point}
    (hνfin : ∀ n, IsFiniteMeasure (ν n))
    (hν : ∀ n, ν n (closure Ω)ᶜ = 0) (hμ : μ (closure Ω)ᶜ = 0)
    (hWeak : WeakStarOnClosure Ω ν μ)
    (he : ‖e‖ = 1) {b : ℝ} (hb : 0 < b)
    (hFlat : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun s => SupportingAnalysis.blownUpMeasure (d := 1) x s μ)
      (ENNReal.ofReal b • HausdorffOne.restrict ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point)))
    (a : BulkCoefficients) {C δ₀ : ℝ} (hC : 0 ≤ C) (hδ₀ : 0 < δ₀)
    (hComparison : ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∃ r ∈ Icc δ (2 * δ), ∃ lo ∈ Icc (-1 : ℝ) (-1 / 2), ∃ hi ∈ Icc (1 / 2 : ℝ) 1,
        ∃ k ∈ ({0, kappaStar a, 2 * kappaStar a} : Set ℝ),
          |(ν n ((fun z : Point => x + s • z) '' openAxisCylinder e r lo hi)).toReal / (s * (hi - lo)) - k| ≤ C * δ) :
    b = kappaStar a ∨ b = 2 * kappaStar a := by
  let K : Set ℝ := {0, kappaStar a, 2 * kappaStar a}
  have hK : IsClosed K := (Set.finite_singleton (2 * kappaStar a)).insert (kappaStar a) |>.insert 0 |>.isClosed
  have hB : b ∈ closure K := by
    apply Metric.mem_closure_iff.mpr
    intro ξ hξ
    obtain ⟨δ, hδ, hδs⟩ := exists_between (show (0 : ℝ) < min δ₀ (ξ / (4 * (C + 1))) from
      lt_min hδ₀ (div_pos hξ (by positivity)))
    have hδ₀' : δ < δ₀ := hδs.trans_le (min_le_left _ _)
    have hδ' : δ < ξ / (4 * (C + 1)) := hδs.trans_le (min_le_right _ _)
    have hCδ : C * δ < ξ / 2 := by
      have h := (lt_div_iff₀ (show (0 : ℝ) < 4 * (C + 1) from by positivity)).mp hδ'
      nlinarith only [h, hδ, hξ]
    have hMass := eventually_uniform_weakStar_movingCylinder_mass hνfin hν hμ hWeak he hb hFlat hδ (half_pos hξ)
    obtain ⟨s, hMassS, hCompS, hS⟩ := (hMass.and ((hComparison δ ⟨hδ, hδ₀'⟩).and
      (self_mem_nhdsWithin : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s ∈ Ioi (0 : ℝ)))).exists
    obtain ⟨n, hn, r, hr, lo, hlo, hi, hhi, k, hk, hE⟩ := (hMassS.and hCompS).exists
    let m := (ν n ((fun z : Point => x + s • z) '' openAxisCylinder e r lo hi)).toReal
    let H := hi - lo
    have hH : 1 ≤ H := by dsimp only [H]; linarith only [hlo.2, hhi.1]
    have hH₀ : 0 < H := zero_lt_one.trans_le hH
    have hM : |m / s - b * H| < ξ / 2 := hn r hr lo hlo hi hhi
    have hE' : |m / (s * H) - b| < ξ / 2 := by
      have hEq : m / (s * H) - b = (m / s - b * H) / H := by
        field_simp [hS.ne', hH₀.ne']
      rw [hEq, abs_div, abs_of_pos hH₀, div_lt_iff₀ hH₀]
      exact hM.trans_le (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hH (half_pos hξ).le)
    refine ⟨k, hk, ?_⟩
    rw [Real.dist_eq]
    have h := abs_add_le (b - m / (s * H)) (m / (s * H) - k)
    rw [show (b - m / (s * H)) + (m / (s * H) - k) = b - k by ring,
      abs_sub_comm b (m / (s * H))] at h
    change |m / (s * H) - k| ≤ C * δ at hE
    linarith only [h, hE', hE, hCδ]
  rw [hK.closure_eq] at hB
  rcases hB with h0 | h1 | h2
  · exact (hb.ne' h0).elim
  · exact Or.inl h1
  · exact Or.inr h2

end Thesis.MeasureGeometry
