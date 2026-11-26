module

public import Thesis.Definitions

/-! A local mean-value estimate for scalar linear subsolutions. -/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace Thesis.External

/-- The classical three-dimensional specialization of the local
nonnegative-subsolution bound in Han and Lin, *Elliptic Partial
Differential Equations*, Lemma 4.1, as cited in the thesis appendix.
At radius at most one, the scaled zeroth-order coefficient is at most
the fixed input coefficient. The ball-average normalization is included
in the constant. -/
def ClassicalScalarSubsolutionMeanValue : Prop :=
  ∀ A : ℝ, 0 ≤ A → ∃ C : ℝ, 0 < C ∧
    ∀ (c : Point) (r : ℝ), r ∈ Ioc 0 1 →
      ∀ f : Point → ℝ, ContDiffOn ℝ 2 f (Metric.ball c r) →
        IntegrableOn f (Metric.ball c r) volume →
        (∀ x ∈ Metric.ball c r, 0 ≤ f x) →
        (∀ x ∈ Metric.ball c r, -laplacian f x ≤ A * f x) →
        f c ≤ C * r⁻¹ ^ 3 * ∫ x in Metric.ball c r, f x

end Thesis.External
