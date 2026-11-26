module

public import Thesis.Definitions

/-! Independent interior linear estimates and smooth compactness. -/

@[expose] public section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis.External

local instance interiorCorrectionCoefficientNormed : NormedAddCommGroup ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance interiorCorrectionCoefficientSpace : NormedSpace ℝ ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

/-- The interior estimate for a finite-component linear system whose
principal part is the componentwise Laplacian. The standard local
Sobolev elliptic estimate and Sobolev embedding give the \(C^j\) bound
from the \(L^2\) norm and derivatives of the actual source.
See Gilbarg–Trudinger, Chapters 6 and 9
<https://doi.org/10.1007/978-3-642-61798-0>. -/
def InteriorLinearPoissonSystemDerivativeEstimate : Prop :=
  ∀ (c : Point) (r : ℝ), 0 < r → ∀ (j : ℕ) (M : ℝ), 0 ≤ M →
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : Point → (S0 × Gradient) →L[ℝ] S0) (v F : Point → S0) (E D : ℝ),
        ContDiffOn ℝ ∞ B (Metric.ball c r) → ContDiffOn ℝ ∞ v (Metric.ball c r) →
        ContDiffOn ℝ ∞ F (Metric.ball c r) → 0 ≤ E → 0 ≤ D →
        MemLp v 2 (volume.restrict (Metric.ball c r)) →
        eLpNorm v 2 (volume.restrict (Metric.ball c r)) ≤ ENNReal.ofReal E →
        (∀ y ∈ Metric.ball c r, laplacian v y + B y (v y, ClassicalGradient v y) = F y) →
        (∀ k ≤ j+2, ∀ y ∈ Metric.ball c r, ‖iteratedFDeriv ℝ k B y‖ ≤ M) →
        (∀ k ≤ j+2, ∀ y ∈ Metric.ball c r, ‖iteratedFDeriv ℝ k F y‖ ≤ D) →
        ∀ x ∈ Metric.ball c (r/2), ‖iteratedFDeriv ℝ j v x‖ ≤ C * (E+D)

/-- Arzelà–Ascoli on compact subsets, applied to the actual derivative
jets and followed by the uniform-limit derivative theorem. The
extraction preserves a single subsequence at every order. -/
def SmoothLocalJetCompactness : Prop :=
  ∀ (U : Set Point), IsOpen U → ∀ v : ℕ → Point → S0, (∀ n, ContDiffOn ℝ ∞ (v n) U) →
    (∀ (K : Set Point), IsCompact K → K ⊆ U → ∀ j : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ j (v n) x‖ ≤ C) →
      ∃ (κ : ℕ → ℕ) (w : Point → S0), StrictMono κ ∧ ContDiffOn ℝ ∞ w U ∧
        ∀ j : ℕ, 2 ≤ j → ConvergesCjLoc j U (v ∘ κ) w

end Thesis.External

end
