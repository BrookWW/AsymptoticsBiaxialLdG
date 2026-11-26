module

public import Thesis.Definitions
public import Mathlib.Analysis.Normed.Group.Continuity

/-! The independent geometric measure inputs for the line-defect theorem.
The statements are specialized to the dimension and matrix convention of the thesis. -/

@[expose] public section

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.External

noncomputable local instance geometricMeasureContinuousENorm : ContinuousENorm Tensor :=
  @SeminormedAddGroup.toContinuousENorm Tensor inferInstance

/-- The total variation density of the matrix measure with Radon–Nikodym density
`F` relative to `μ` in the open domain. -/
noncomputable def matrixVariation (Ω : Set Point) (μ : Measure Point)
    (F : Point → Tensor) : Measure Point :=
  (μ.restrict Ω).withDensity fun x => ENNReal.ofReal ‖F x‖

/-- The row-wise divergence of the weighted matrix measure vanishes in
distributions on the interior. -/
def RowDivergenceFree (Ω : Set Point) (μ : Measure Point) (F : Point → Tensor) : Prop :=
  ∀ X : Point → Point, ContDiff ℝ ∞ X → HasCompactSupport X → tsupport X ⊆ Ω →
    (∫ x in Ω, ∑ i : Fin 3, ∑ j : Fin 3, F x i j * coordDeriv j X x i ∂μ) = 0

noncomputable def upperOneDensity (ν : Measure Point) (x : Point) : ℝ≥0∞ :=
  (𝓝[>] (0 : ℝ)).limsup fun r => ν (closedBall x r) / ENNReal.ofReal (2 * r)

/-- Arroyo-Rabasa, De Philippis, Hirsch and Rindler, Proposition 3.1,
for the row-wise divergence constraint in dimension three and rectifiability
dimension one. The supplied conclusion is a rank-one matrix density on the
positive upper-density part. -/
def A19Prop31 : Prop :=
  ∀ (Ω : Set Point), IsOpen Ω → ∀ (μ : FiniteMeasure Point) (F : Point → Tensor),
    Integrable F ((μ : Measure Point).restrict Ω) →
    RowDivergenceFree Ω μ F →
    let ν := matrixVariation Ω μ F
    let E := {x ∈ Ω | 0 < upperOneDensity ν x}
    (∀ᵐ x ∂ν, 1 ≤ (F x).rank) →
    ν ≪ HausdorffOne ∧
      ∃ (S : Set Point) (A : Point → Tensor),
        MeasurableSet S ∧ S ⊆ E ∧ CountablyRectifiableOne S ∧
        Integrable A (HausdorffOne.restrict S) ∧
        (∀ᵐ x ∂HausdorffOne.restrict S, (A x).rank = 1) ∧
        ∀ B : Set Point, MeasurableSet B →
          (∫ x in B ∩ E, F x ∂(μ : Measure Point)) = ∫ x in B ∩ S, A x ∂HausdorffOne

/-- Allard and Almgren, local structure on p. 89, restricted to the discrete
two-weight case. The local rays and their weight enter the thesis comparison
and junction arguments, which are separate from this input. -/
def AllardAlmgrenLocalStructure : Prop :=
  ∀ (Ω : Set Point), IsOpen Ω → ∀ (ν : FiniteMeasure Point) (S : Set Point)
    (V : Measure (Point × LineProjection)) (κ : ℝ), 0 < κ →
    IsAssociatedVarifold Ω S ν V → IsStationaryVarifold Ω V →
    (∃ c > (0 : ℝ), ∀ x ∈ Ω ∩ (ν : Measure Point).support, ∃ θ ≥ c,
      Tendsto (oneDensity ν x) (𝓝[>] 0) (𝓝 θ)) →
    (∀ᵐ x ∂HausdorffOne.restrict S, ∃ θ : ℝ, (θ = κ ∨ θ = 2 * κ) ∧
      Tendsto (oneDensity ν x) (𝓝[>] 0) (𝓝 θ)) →
    ∀ x ∈ Ω ∩ (ν : Measure Point).support,
      ∃ (r : ℝ) (m : ℕ) (v : Fin m → Point) (θ : Fin m → ℝ),
        0 < r ∧ 0 < m ∧ closedBall x r ⊆ Ω ∧
        Function.Injective v ∧ (∀ i, ‖v i‖ = 1 ∧ (θ i = κ ∨ θ i = 2 * κ)) ∧
        (ν : Measure Point).support ∩ closedBall x r =
          (⋃ i, segment ℝ x (x + r • v i)) ∧
        (ν : Measure Point).restrict (closedBall x r) =
          ∑ i, ENNReal.ofReal (θ i) • HausdorffOne.restrict (segment ℝ x (x + r • v i))

end Thesis.External

end
