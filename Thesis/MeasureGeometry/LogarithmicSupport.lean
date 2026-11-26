module

public import Thesis.Variational.PenalizedClearingOut
public import Thesis.MeasureGeometry.OffSupportEnergy
public import Thesis.MeasureGeometry.StationaryVarifold
import Thesis.MeasureGeometry.EnergyMonotonicity
import Thesis.MeasureGeometry.PenalizedStressLimit

/-! Off-support energy and the interior support of an actual logarithmic limit. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius NNReal Topology

namespace Thesis.MeasureGeometry

/-- The same sequence has both the all-index local bounds and the eventual
quantitative off-support bounds. -/
theorem exists_offSupport_energy_bounds_of_projectionLayer (a : BulkCoefficients)
    (hProj : HasPenalizedProjectionLayer a) (hDense : External.SmoothVacuumSphereDensity a)
    (hP : External.QuaternionSpherePoincare 3 (by decide : 2 ≤ 3)) (M : ℝ) (hM : 0 < M) :
    ∃ C : Set Point → ℝ → ℝ, (∀ U r, 0 < C U r) ∧
      ∀ (Ω : Set Point), IsOpen Ω → ∀ (ε : ℕ → ElasticScale),
        Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        ∀ (Q : ℕ → Point → S0) (D : ℕ → Point → Gradient)
          (μ : ℕ → FiniteMeasure Point) (ν : FiniteMeasure Point),
        (∀ n, IsLocalEnergyMinimizer a (ε n) Ω (Q n) (D n)) →
        (∀ n, ∀ᵐ x ∂volume.restrict Ω, ‖Q n x‖ ≤ M) →
        (∀ n, (μ n : Measure Point) = normalizedEnergyMeasure a (ε n) Ω (Q n) (D n)) →
        Tendsto μ atTop (𝓝 ν) → (∀ n, energy a (ε n) Ω (Q n) (D n) < ⊤) →
        ∀ U : Set Point, IsOpen U → CompactlyContained U (Ω \ (ν : Measure Point).support) →
          (∃ B > (0 : ℝ), ∀ n, energy a (ε n) U (Q n) (D n) ≤ ENNReal.ofReal B) ∧
          ∀ r : ℝ, 0 < r → (∀ x ∈ closure U, closedBall x r ⊆ Ω \ (ν : Measure Point).support) →
            ∀ᶠ n in atTop, energy a (ε n) U (Q n) (D n) ≤ ENNReal.ofReal (C U r) := by
  obtain ⟨η, δ, C₀, hη, hδ, hC₀, hClear⟩ := exists_logarithmic_clearing_out_quadratic a hProj hDense hP M hM
  obtain ⟨C, hC, hOff⟩ := exists_offSupport_energy_bounds a hη hδ.1 hC₀.le
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ ε hε Q D μ ν hMin hNorm hμ hν hFin
  apply hOff Ω hΩ ε hε Q D μ ν hμ hν hFin
  intro x r hr hrΩ n hεn hEn
  exact hClear (ε n) hΩ x r hr hrΩ (Q n) (D n) (hMin n)
    (ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hrΩ) (hNorm n)) hεn hEn

/-- The actual normalized limit measure has a positive interior density at
every support point and an associated stationary rectifiable varifold. -/
theorem logarithmic_limit_rectifiable_support_of_projectionLayer (a : BulkCoefficients)
    (hProj : HasPenalizedProjectionLayer a) (hDense : External.SmoothVacuumSphereDensity a)
    (hP : External.QuaternionSpherePoincare 3 (by decide : 2 ≤ 3)) (hA19 : External.A19Prop31)
    (M : ℝ) (hM : 0 < M) :
    ∃ η : ℝ, 0 < η ∧ ∀ {Ω : Set Point} (hΩ : IsBoundedDomain Ω) {ε : ℕ → ElasticScale},
      Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
      ∀ {u v : ℕ → Point → S0} {D : ℕ → Point → Gradient},
        (∀ n, IsLocalEnergyMinimizer a (ε n) Ω (u n) (D n)) →
        (∀ n, ∀ᵐ x ∂volume.restrict Ω, ‖u n x‖ ≤ M) →
        (∀ n, u n =ᵐ[volume.restrict Ω] v n) →
        (∀ n, D n =ᵐ[volume.restrict Ω] ClassicalGradient (v n)) →
        (∀ n, ContDiffOn ℝ ∞ (v n) Ω) →
        (∀ n, ∀ x ∈ Ω, (ε n : ℝ) ^ 2 • (laplacian (v n) x : S0).val = bulkGradient a (v n x)) →
        ∀ {μ : ℕ → FiniteMeasure Point} {ν : FiniteMeasure Point},
          (∀ n, (μ n : Measure Point) = normalizedEnergyMeasure a (ε n) Ω (u n) (D n)) →
          Tendsto μ atTop (𝓝 ν) → ∀ B : ℝ≥0, (∀ n, (μ n).mass ≤ B) →
          let S := Ω ∩ (ν : Measure Point).support
          (∀ x ∈ Ω, ∃ θ : ℝ, Tendsto (oneDensity ν x) (𝓝[>] 0) (𝓝 θ) ∧
            (x ∈ (ν : Measure Point).support ↔ 0 < θ) ∧
            (x ∈ (ν : Measure Point).support ↔ η / 2 ≤ θ)) ∧
          CountablyRectifiableOne S ∧ HausdorffOne S < ⊤ ∧
          ∃ V : Measure (Point × LineProjection), IsAssociatedVarifold Ω S ν V ∧ IsStationaryVarifold Ω V := by
  obtain ⟨η, δ, C, hη, hδ, _, hClear⟩ := exists_logarithmic_clearing_out_quadratic a hProj hDense hP M hM
  refine ⟨η, hη, ?_⟩
  intro Ω hΩ ε hε u v D hMin hNorm hUV hD hSmooth hEuler μ ν hμ hν B hB
  have hDensity (x : Point) (hx : x ∈ Ω) : ∃ θ : ℝ,
      Tendsto (oneDensity ν x) (𝓝[>] 0) (𝓝 θ) ∧
      (x ∈ (ν : Measure Point).support ↔ 0 < θ) ∧
      (x ∈ (ν : Measure Point).support ↔ η / 2 ≤ θ) := by
    obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.1 hΩ.1 x hx
    let R₀ := R / 2
    have hR₀ : 0 < R₀ := half_pos hR
    have hCΩ : closedBall x R₀ ⊆ Ω := (closedBall_subset_ball (by dsimp only [R₀]; linarith)).trans hRΩ
    have hMono := oneDensity_monotoneOn_of_penalizedLimit a hΩ.1 hUV hD hSmooth hEuler hμ hν hR₀ hCΩ
    obtain ⟨θ, hθ, _⟩ := existsUnique_oneDensity_limit ν x hR₀ hMono
    refine ⟨θ, hθ, density_support_of_clearing_out ν x hR₀ hη hθ fun r hr hm => ?_⟩
    have hBall : closedBall x r ⊆ Ω := (closedBall_subset_closedBall hr.2.le).trans hCΩ
    exact (small_limitMass_eventually_bound_and_zero a hr.1 hη hδ.1 hBall ε hε u D hμ hν hm
      (fun n => hClear (ε n) hΩ.1 x r hr.1 hBall (u n) (D n) (hMin n)
        (ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hBall) (hNorm n)))).2
  obtain ⟨s, F, hs, hF, hDiv, hBounds, _⟩ :=
    exists_penalizedStress_limit a hΩ hUV hD hSmooth hEuler hν hμ B hB
  refine ⟨hDensity, stationary_rectifiable_varifold_of_A19 hA19 hΩ.1 ν F hF hDiv hBounds hη ?_⟩
  intro x hx
  obtain ⟨θ, hθ, _, hsupp⟩ := hDensity x hx.1
  exact ⟨θ, hsupp.1 hx.2, hθ⟩

end Thesis.MeasureGeometry
