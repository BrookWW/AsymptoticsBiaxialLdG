module

public import SupportingAnalysis.Euclidean

/-! Rectifiable-measure limits and scalar differential operators. -/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped BigOperators ContDiff NNReal ENNReal Topology

set_option autoImplicit false

namespace SupportingAnalysis

def VagueOn {m : ℕ} {ι : Type} (Ω : Set (E m)) (l : Filter ι)
    (μ : ι → Measure (E m)) (ν : Measure (E m)) : Prop :=
  ∀ φ : E m → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    Tendsto (fun j => ∫ x, φ x ∂μ j) l (𝓝 (∫ x, φ x ∂ν))

def CountablyRectifiable {m : ℕ} (d : ℕ) (S : Set (E m)) : Prop :=
  ∃ f : ℕ → E d → E m, (∀ k, ∃ K : ℝ≥0, LipschitzWith K (f k)) ∧
    μH[(d : ℝ)] (S \ ⋃ k, range (f k)) = 0

noncomputable def blownUpMeasure {m d : ℕ} (x : E m) (r : ℝ)
    (μ : Measure (E m)) : Measure (E m) :=
  ENNReal.ofReal (r ^ (-(d : ℤ))) • Measure.map (fun y => r⁻¹ • (y - x)) μ

-- Weighted rectifiable tangent planes (Simon, Ch. 3, Theorem 1.9).
abbrev External.WeightedRectifiableTangents : Prop :=
  ∀ (m d : ℕ) (S : Set (E m)) (Θ : E m → ℝ≥0∞),
    MeasurableSet S → CountablyRectifiable d S → μH[(d : ℝ)] S < ⊤ →
    Measurable Θ → (∀ᵐ x ∂μH[(d : ℝ)].restrict S, 0 < Θ x) →
    IsFiniteMeasure ((μH[(d : ℝ)].restrict S).withDensity Θ) →
    ∀ᵐ x ∂μH[(d : ℝ)].restrict S,
      ∃ (L : Submodule ℝ (E m)) (b : ℝ),
        Module.finrank ℝ L = d ∧ 0 < b ∧
        VagueOn univ (𝓝[>] (0 : ℝ))
          (fun r => @blownUpMeasure m d x r ((μH[(d : ℝ)].restrict S).withDensity Θ))
          (ENNReal.ofReal b • μH[(d : ℝ)].restrict (L : Set (E m)))

noncomputable def laplacian {m : ℕ} (w : E m → ℝ) (x : E m) : ℝ :=
  ∑ i, fderiv ℝ (fun y => fderiv ℝ w y (axis i)) x (axis i)

noncomputable def scalarHessian {m : ℕ} (w : E m → ℝ) (x : E m)
    (i j : Fin m) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ w y (axis i)) x (axis j)

noncomputable def scalarHessianNorm {m : ℕ} (w : E m → ℝ) (x : E m) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (scalarHessian w x i j) ^ 2)

end SupportingAnalysis
