module

public import Thesis.Definitions

/-! Linear Dirichlet estimates on the physical part of smooth caps. -/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace Thesis.External

/-- The classical scalar zero-trace specialization of Nguyen and Zarnescu's
boundary gradient estimate at exponent `p = 4`. The forcing and gradient
norms are on the outer cap, and the trace condition is on its physical wall.
See [Nguyen and Zarnescu, preprint Lemma 5.11](https://arxiv.org/pdf/1006.5689)
and the smooth-domain formulation in the thesis appendix. -/
def ZeroTraceBoundaryPoissonL4GradientEstimate : Prop :=
  ∀ (U : Set Point), IsSmoothDomain U →
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧
      ∀ c ∈ frontier U, ∀ r ∈ Ioo 0 R, ∀ (u f : Point → ℝ),
        let D := U ∩ Metric.ball c r
        let K := closure U ∩ Metric.ball c r
        ContDiffOn ℝ 2 u K →
        EqOn u (fun _ => 0) (frontier U ∩ Metric.ball c r) →
        (∀ x ∈ D, laplacian u x = f x) →
        MemLp (fderiv ℝ u) 2 (volume.restrict D) →
        MemLp f 4 (volume.restrict D) →
        ∀ x ∈ closure U ∩ Metric.ball c (r / 2),
          ‖fderivWithin ℝ u K x‖ ≤
            C * (r ^ (-3 / 2 : ℝ) * (eLpNorm (fderiv ℝ u) 2 (volume.restrict D)).toReal +
              r ^ (1 / 4 : ℝ) * (eLpNorm f 4 (volume.restrict D)).toReal)

end Thesis.External
