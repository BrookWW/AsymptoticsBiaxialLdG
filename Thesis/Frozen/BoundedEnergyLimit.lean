module

public import Thesis.Definitions
import Thesis.Providers.BoundedEnergyLimit

/-! Theorem 1.4 of the thesis. -/

public section

open Set Filter MeasureTheory Topology
open scoped BigOperators ContDiff ENNReal NNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false

namespace Thesis

-- FROZEN_ANCHOR_PREFIX_BEGIN
theorem boundedEnergyLimit :
  ∀ (a : BulkCoefficients) (M : ℝ), 0 < M →
  ∃ C : ℕ → ℝ → ℝ → ℝ,
    (∀ j r L, 0 < r → 0 ≤ L → 0 < C j r L) ∧
    ∀ (Ω : Set Point), IsBoundedDomain Ω →
      ∀ (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient),
        (∀ ε, IsLocalEnergyMinimizer a ε Ω (Q ε) (D ε)) →
        (∀ ε, energy a ε Ω (Q ε) (D ε) ≤ ENNReal.ofReal M ∧
          eLpNorm (Q ε) ∞ (volume.restrict Ω) ≤ ENNReal.ofReal M) →
        ∃ (ε : ℕ → ElasticScale) (Q₀ : Point → S0) (D₀ : Point → Gradient)
          (S : Set Point) (Qreg : ℕ → Point → S0) (R : ℕ → Point → Tensor),
          Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧
          MemH1 Ω Q₀ D₀ ∧ TakesVacuumValues a Ω Q₀ ∧
          StrongH1Loc Ω (fun n => Q (ε n)) (fun n => D (ε n)) Q₀ D₀ ∧
          ConvergesScaledPotentialLoc a Ω ε (fun n => Q (ε n)) ∧
          IsLocalDirichletMinimizer a Ω Q₀ D₀ ∧ WeakLaplacianEq Ω D₀ (harmonicRhs a Q₀ D₀) ∧
          S ⊆ Ω ∧ LocallyFiniteIn Ω S ∧ ContDiffOn ℝ ∞ Q₀ (Ω \ S) ∧
          (∀ n, Qreg n =ᵐ[volume.restrict (Ω \ S)] Q (ε n)) ∧
          (∀ j : ℕ, ConvergesCjLoc j (Ω \ S) Qreg Q₀) ∧
          ∀ (x : Point) (r : ℝ), 0 < r → Metric.closedBall x r ⊆ Ω \ S →
            (∀ n, ContDiffOn ℝ ∞ (Qreg n) (Metric.ball x (r/2)) ∧
              ∀ y ∈ Metric.ball x (r/2), (laplacian (Qreg n) y : S0).val =
                harmonicRhs a (Qreg n) (ClassicalGradient (Qreg n)) y + R n y) ∧
            ∀ j : ℕ, ∀ᶠ n in atTop,
              let L := (eLpNorm (fun y =>
                Real.sqrt (gradientNormSq (ClassicalGradient Q₀ y))) ∞
                (volume.restrict (Metric.ball x r))).toReal
              eLpNorm (multiIndexNorm j (R n)) ∞ (volume.restrict (Metric.ball x (r/2))) ≤
                ENNReal.ofReal (C j r L * (ε n : ℝ)^2) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact Thesis.Providers.boundedEnergyLimit
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end Thesis
end
-- FROZEN_ANCHOR_SUFFIX_END
