module

public import Thesis.Definitions

/-! Boundary regularity input for the fixed-trace Dirichlet minimizer. -/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace Thesis.External

/-- The (C^2) collar consequence of Schoen–Uhlenbeck 1983, Theorem 2.7,
for smooth domains and smooth vacuum-valued Dirichlet data. -/
def SU83BoundaryRegularity : Prop :=
  ∀ (a : BulkCoefficients) (Ω : Set Point), IsSmoothDomain Ω →
    ∀ (b : frontier Ω → S0) (u : Point → S0) (D : Point → Gradient),
      IsGlobalDirichletMinimizer a Ω b u D →
      ∃ (V : Set Point) (v : Point → S0), IsOpen V ∧ frontier Ω ⊆ V ∧
        v =ᵐ[volume.restrict (Ω ∩ V)] u ∧ ContDiffOn ℝ 2 v (closure Ω ∩ V) ∧
        ∀ x : frontier Ω, v x = b x

end Thesis.External

end
