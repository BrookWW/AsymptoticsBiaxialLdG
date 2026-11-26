module

public import Thesis.Definitions

/-! Quantitative global Dirichlet regularity for the componentwise Laplacian. -/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff ENNReal Matrix Matrix.Norms.Frobenius

namespace Thesis.External

/-- The global Dirichlet \(W^{2,p}\) estimate and the Sobolev–Morrey embedding,
applied to the components in a fixed orthonormal basis. See Gilbarg–Trudinger,
Theorems 9.13 and 7.26 in the 2001 edition
<https://doi.org/10.1007/978-3-642-61798-0>. A finite \(p\) is chosen with
\(1-3/p\) above the prescribed exponent. The closed-domain columns are the
actual within derivatives of the given zero-trace classical function. -/
def GlobalDirichletPoissonGradientHolder : Prop :=
  ∀ (U : Set Point), IsSmoothDomain U → ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Point → S0), ContDiffOn ℝ 2 v (closure U) →
      EqOn v (fun _ => 0) (frontier U) → ∀ M F : ℝ, 0 ≤ M → 0 ≤ F →
      (∀ x ∈ U, ‖v x‖ ≤ M) → (∀ x ∈ U, ‖laplacian v x‖ ≤ F) →
      let D (x : Point) (j : Fin 3) := fderivWithin ℝ v (closure U) x (axis j)
      (∀ x ∈ closure U, ‖D x‖ ≤ C * (M + F)) ∧
      ∀ x ∈ closure U, ∀ y ∈ closure U,
        ‖v x - v y‖ + ‖D x - D y‖ ≤ C * (M + F) * dist x y ^ α

/-- The global Dirichlet \(W^{2,p}\) estimate for the given classical
zero-trace field, measured by the operator norm of its actual second
Fréchet derivative. See Gilbarg–Trudinger, Theorem 9.13
<https://doi.org/10.1007/978-3-642-61798-0>. -/
def GlobalDirichletPoissonSecondDerivativeLp : Prop :=
  ∀ (U : Set Point), IsSmoothDomain U → ∀ p : ℝ, 1 < p →
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Point → S0), ContDiffOn ℝ 2 v (closure U) →
      EqOn v (fun _ => 0) (frontier U) → ∀ M F : ℝ, 0 ≤ M → 0 ≤ F →
      (∀ x ∈ U, ‖v x‖ ≤ M) → (∀ x ∈ U, ‖laplacian v x‖ ≤ F) →
      MemLp (fun x => ‖iteratedFDeriv ℝ 2 v x‖) (ENNReal.ofReal p) (volume.restrict U) ∧
        eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 v x‖) (ENNReal.ofReal p) (volume.restrict U) ≤
          ENNReal.ofReal (C * (M + F))

end Thesis.External

end
