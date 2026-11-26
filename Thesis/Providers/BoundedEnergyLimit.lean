module

public import Thesis.Variational.BoundedEnergyClassicalLimit
public import Thesis.Variational.InteriorClassicalConvergence
public import Thesis.Variational.InteriorHarmonicRemainder
public import Thesis.Interpolation.ProjectionLayer
import Thesis.Interpolation.QuaternionSpherePoincare
import Thesis.Interpolation.SquareBoundaryAngularSobolev
import Thesis.Interpolation.PeriodicAngularSobolev
import Thesis.Interpolation.SquareDiskSobolevPushforward
import Thesis.Variational.SubsolutionMeanValue
import Thesis.Upstream.InteriorPoissonRegularity
import Thesis.MeasureGeometry.PlanarScalarCoarea

/-! Theorem 1.4 with its explicit independent analytic inputs. -/

public section

open Set Filter MeasureTheory Metric
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

/-- The full statement of the bounded-energy limit. -/
@[expose] def BoundedEnergyLimitConclusion (a : BulkCoefficients) (M : ℝ) : Prop :=
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
            ∀ (x : Point) (r : ℝ), 0 < r → closedBall x r ⊆ Ω \ S →
              (∀ n, ContDiffOn ℝ ∞ (Qreg n) (ball x (r / 2)) ∧
                ∀ y ∈ ball x (r / 2), (laplacian (Qreg n) y : S0).val =
                  harmonicRhs a (Qreg n) (ClassicalGradient (Qreg n)) y + R n y) ∧
              ∀ j : ℕ, ∀ᶠ n in atTop,
                let L := (eLpNorm (fun y => Real.sqrt (gradientNormSq (ClassicalGradient Q₀ y))) ∞
                  (volume.restrict (ball x r))).toReal
                eLpNorm (multiIndexNorm j (R n)) ∞ (volume.restrict (ball x (r / 2))) ≤
                  ENNReal.ofReal (C j r L * (ε n : ℝ) ^ 2)

/-- The bounded-energy theorem, with the actual common sequence, regular
representatives and the exact quadratic interior remainder. -/
theorem boundedEnergyLimit_of_projectionLayer
    (a : BulkCoefficients) (hProj : HasPenalizedProjectionLayer a)
    (hReg : InteriorPoissonRegularity) (hEstimate : InteriorPoissonGradientEstimate)
    (hMean : External.ClassicalScalarSubsolutionMeanValue) (M : ℝ) (hM : 0 < M) :
    BoundedEnergyLimitConclusion a M := by
  obtain ⟨C, hC, hRemainder⟩ := exists_regular_interior_harmonicRemainder_constants a hEstimate hMean
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ Q D hMin hBounds
  obtain ⟨ε, q, G, S, v, hε, hq, hVac, hStrong, hPot, hMinq, hHarm, hS, hFin,
    hOpen, hqSmooth, hv, _, hvSmooth, hvEq, hvB, hStrong', hPot'⟩ :=
      exists_boundedEnergy_classical_limit_of_projectionLayer a hProj hReg M hM hΩ Q D hMin hBounds
  let U := Ω \ S
  have hSub : U ⊆ Ω := sdiff_subset
  have hvU (n : ℕ) : ContDiffOn ℝ ∞ (v n) U := (hvSmooth n).mono hSub
  have hEq (n : ℕ) (x : Point) (hx : x ∈ U) :
      (ε n : ℝ) ^ 2 • (laplacian (v n) x : S0).val = bulkGradient a (v n x) :=
    hvEq n x (hSub hx)
  have hRange : BddAbove ((fun p : ℕ × Point => ‖v p.1 p.2‖) '' (univ ×ˢ U)) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨⟨n, x⟩, hx, rfl⟩
    exact hvB n x (hSub hx.2)
  have hCj := convergesCjLoc_of_regular_penalized_solutions a hEstimate hMean hOpen ε v q hε
    hvU hqSmooth hEq hRange hStrong' hPot'
  refine ⟨ε, q, G, S, v, (fun n => harmonicRemainder a (ε n) (v n)), hε, hq, hVac,
    hStrong, hPot, hMinq, hHarm, hS, hFin, hqSmooth, ?_, hCj, ?_⟩
  · exact fun n => ae_restrict_of_ae_restrict_of_subset hSub (hv n)
  · exact hRemainder hOpen ε v q hε hvU hqSmooth hEq hRange hStrong' hPot'

/-- The complete bounded-energy conclusion from the independent
coarea, Sobolev transport and linear interior estimates. -/
theorem boundedEnergyLimit_relative (a : BulkCoefficients)
    (hCoarea : External.PlanarScalarCoarea)
    (M : ℝ) (hM : 0 < M) :
    BoundedEnergyLimitConclusion a M :=
  boundedEnergyLimit_of_projectionLayer a
    (hasPenalizedProjectionLayer a hCoarea squareBoundaryAngularSobolev squareBoundaryAngularMeasure
      unitSquareDiskSobolevPullback unitSquareDiskSobolevPushforward
      periodicAngularSobolev quaternionSpherePoincare_two)
    interiorPoissonRegularity interiorPoissonGradientEstimate classicalScalarSubsolutionMeanValue M hM

namespace Providers

/-- The bounded-energy theorem with every analytic input supplied in Lean. -/
theorem boundedEnergyLimit : ∀ (a : BulkCoefficients) (M : ℝ), 0 < M → BoundedEnergyLimitConclusion a M :=
  fun a M hM => boundedEnergyLimit_relative a planarScalarCoarea M hM

end Providers

end Thesis
