module

public import Thesis.MeasureGeometry.LogarithmicQuantizedLimit
public import Thesis.MeasureGeometry.LogarithmicSegmentNetwork
public import Thesis.MeasureGeometry.MeridianCostAssembly
import Thesis.Interpolation.ProjectionLayer
import Thesis.Interpolation.QuaternionSpherePoincare
import Thesis.Interpolation.SmoothVacuumSphereDensity
import Thesis.Interpolation.SquareBoundaryAngularSobolev
import Thesis.Interpolation.PeriodicAngularSobolev
import Thesis.Interpolation.AmbientBiLipschitzSobolev
import Thesis.Interpolation.CylinderBoundaryTraceKernel
import Thesis.Interpolation.CylinderBoundaryChartTraceTransport
import Thesis.Interpolation.TerminalCylinderSurfaceSobolev
import Thesis.Interpolation.SquareDiskSobolevPushforward
import Thesis.Variational.SubsolutionMeanValue
import Thesis.Upstream.InteriorPoissonRegularity
import Thesis.MeasureGeometry.PlanarScalarCoarea
import Thesis.MeasureGeometry.RelativeMeridianAvoidance

/-! The logarithmic energy limit with its original finite network. -/

public section

open Set Filter MeasureTheory Topology
open scoped BigOperators ContDiff ENNReal NNReal Matrix Matrix.Norms.Frobenius

namespace Thesis

open MeasureGeometry

/-- The literal Theorem 1.6 proposition, used by the explicit-input provider. -/
@[expose] def LogarithmicEnergyLimitConclusion : Prop :=
  ∀ (a : BulkCoefficients) (M : ℝ), 0 < M →
  ∃ C : Set Point → ℝ → ℝ,
    (∀ U r, 0 < r → 0 < C U r) ∧
    ∀ (Ω : Set Point), IsBoundedDomain Ω →
      ∀ (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient),
        (∀ ε, IsLocalEnergyMinimizer a ε Ω (Q ε) (D ε)) →
        (∀ ε, energy a ε Ω (Q ε) (D ε) ≤
            ENNReal.ofReal (M * (Real.log (1 / (ε : ℝ)) + 1)) ∧
          eLpNorm (Q ε) ∞ (volume.restrict Ω) ≤ ENNReal.ofReal M) →
        ∃ (ε : ℕ → ElasticScale) (μ : Measure Point) (S : Set Point)
          (Q₀ : Point → S0) (D₀ : Point → Gradient) (Qreg : ℕ → Point → S0),
          let W := Ω \ S
          let Spts := singularSet W Q₀
          Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧
          IsFiniteMeasure μ ∧ μ (closure Ω)ᶜ = 0 ∧ IsClosed S ∧ S ⊆ closure Ω ∧
          WeakStarOnClosure Ω (fun n => normalizedEnergyMeasure a (ε n) Ω (Q (ε n)) (D (ε n))) μ ∧
          μ.support = S ∧ CountablyRectifiableOne (Ω ∩ S) ∧ HausdorffOne (Ω ∩ S) < ⊤ ∧
          (∀ U : Set Point, IsDomain U → CompactlyContained U W →
            ∃ B > (0 : ℝ), ∀ n : ℕ,
              energy a (ε n) U (Q (ε n)) (D (ε n)) ≤ ENNReal.ofReal B) ∧
          (∀ (U : Set Point) (r : ℝ), IsDomain U → CompactlyContained U W → 0 < r →
            (∀ x ∈ closure U, Metric.closedBall x r ⊆ W) →
            ∀ᶠ n in atTop, energy a (ε n) U (Q (ε n)) (D (ε n)) ≤ ENNReal.ofReal (C U r)) ∧
          IsLocalDirichletMinimizer a W Q₀ D₀ ∧
          StrongH1Loc W (fun n => Q (ε n)) (fun n => D (ε n)) Q₀ D₀ ∧
          (∀ n, Qreg n =ᵐ[volume.restrict W] Q (ε n)) ∧
          (∀ j : ℕ, 1 ≤ j → ConvergesCjLoc j (W \ Spts) Qreg Q₀) ∧
          DensityQuantized a μ (Ω ∩ S) ∧
          (∃ V : Measure (Point × LineProjection),
            IsAssociatedVarifold Ω (Ω ∩ S) μ V ∧ IsStationaryVarifold Ω V) ∧
          ∀ K : Set Point, IsOpen K → CompactlyContained K Ω →
            ∃ (U : Set Point) (m : ℕ) (p q : Fin m → Point) (θ : Fin m → ℝ),
              let L := fun i : Fin m => segment ℝ (p i) (q i)
              let κ := kappaStar a
              IsOpen U ∧ closure K ⊆ U ∧ CompactlyContained U Ω ∧
              (∀ i, p i ≠ q i ∧ (θ i = κ ∨ θ i = 2*κ)) ∧
              S ∩ closure U = ⋃ i, L i ∧
              S ∩ closure K = ⋃ i, L i ∩ closure K ∧
              (∀ i j, i ≠ j → ∀ x ∈ L i ∩ L j,
                (x = p i ∨ x = q i) ∧ (x = p j ∨ x = q j)) ∧
              μ.restrict (closure K) =
                ∑ i, ENNReal.ofReal (θ i) • HausdorffOne.restrict (L i ∩ closure K) ∧
              (∀ d : Plane → Point, IsSmoothDiskEmbedding d → d '' Disk ⊆ K →
                ∀ y ∈ Metric.ball (0 : Plane) 1, d '' Disk ∩ S = {d y} →
                  (∃ i, d y ∈ openSegment ℝ (p i) (q i) ∧
                    q i - p i ∉ LinearMap.range (fderiv ℝ d y).toLinearMap) →
                  Disjoint (d '' Metric.sphere (0 : Plane) 1) Spts →
                  (∀ z ∈ Metric.sphere (0 : Plane) 1, Q₀ (d z) ∈ vacuum a) ∧
                  ¬HasMeridianFilling a d Q₀) ∧
              ∀ x ∈ K,
                let I := incidentSegments p q x
                let v := outwardDirection p q x
                I.Nonempty →
                  2 ≤ I.card ∧ (∑ i : ↥I, θ i • v i) = 0 ∧
                  Even ((Finset.univ.filter fun i : ↥I => θ i = κ).card) ∧
                  (I.card = 2 → ∀ i j : ↥I, i ≠ j → v i = -v j) ∧
                  (I.card = 3 →
                    (∀ i : ↥I, θ i = 2*κ) ∧
                    (∃ P : Submodule ℝ Point, Module.finrank ℝ P = 2 ∧ ∀ i : ↥I, v i ∈ P) ∧
                    ∀ i j : ↥I, i ≠ j → InnerProductGeometry.angle (v i) (v j) = 2*Real.pi/3)

/-- The complete logarithmic theorem relative to the independent A-free
rectifiability and stationary one-varifold structure results. -/
theorem logarithmicEnergyLimit_relative
    (hA19 : External.A19Prop31) (hAA : External.AllardAlmgrenLocalStructure) :
    LogarithmicEnergyLimitConclusion := by
  unfold LogarithmicEnergyLimitConclusion
  intro a M hM
  let hCoarea := planarScalarCoarea
  have hProj := hasPenalizedProjectionLayer a hCoarea squareBoundaryAngularSobolev squareBoundaryAngularMeasure
    unitSquareDiskSobolevPullback unitSquareDiskSobolevPushforward periodicAngularSobolev quaternionSpherePoincare_two
  obtain ⟨C, hC, hCore⟩ := exists_logarithmic_limit_quantized_core a hProj (smoothVacuumSphereDensity a) quaternionSpherePoincare_three
    hA19 interiorPoissonRegularity interiorPoissonGradientEstimate classicalScalarSubsolutionMeanValue
    hCoarea periodicAngularSobolev
    terminalCylinderSurfaceSobolev ambientBiLipschitzSobolevPullback3 cylinderBoundaryChartTraceTransport
    cylinderBoundaryTraceKernel M hM
  refine ⟨C, fun U r _ => hC U r, ?_⟩
  intro Ω hΩ Q D hMin hBound
  obtain ⟨ε, μ, q, G, v, hε, hμ, hClosed, hSupport, hStar, hRect, hLen, hOff, hOffQuant,
    hMinq, _, hStrong, _, hLoc, hSmooth, _, hEq, _, hv, hEuler, hRange, hCj, hPositive, _,
    hEnergy, hNorm, hνfin, hVac, hDensity, hConv, hUpper, hQuant, V, hAssoc, hStat⟩ :=
    hCore Ω hΩ Q D hMin hBound
  let S := (μ : Measure Point).support
  let Spt := singularSet (Ω \ S) q
  have hSpt : Spt ⊆ Ω \ S := fun _ hx => hx.1
  have hNet := logarithmicSegmentNetwork_of_quantized_and_meridianCosts hAA a hΩ.1 μ V
    hAssoc hStat hPositive hQuant q hMinq.2.1 hLoc hSmooth (by
      intro K U hK hKU hUΩ m p t θ hWeights hUnion hMeet hMass
      have hθ (i : Fin m) : 0 ≤ θ i := by
        rcases (hWeights i).2 with hi | hi <;> rw [hi] <;> linarith only [kappaStar_pos a]
      exact meridian_boundary_cost_eq_edge_weight_of_regularCylinder_upper
        relativeAnnulusPointAvoidance hCoarea periodicAngularSobolev a
        hΩ.1 hμ hLoc hSpt hM.le ε v q hε hv hEuler hRange hEnergy hSmooth.continuousOn hVac hDensity
        hConv _ hνfin hNorm hStar hUpper hK hKU (hKU.trans (subset_closure.trans hUΩ.2))
        (fun i => (hWeights i).1) hθ hUnion hMeet hMass)
  refine ⟨ε, μ, S, q, G, v, hε, inferInstance, hμ, hClosed, hSupport, hStar,
    rfl, hRect, hLen, ?_, ?_, hMinq, hStrong, ?_, fun j _ => hCj j, hQuant, ⟨V, hAssoc, hStat⟩, hNet⟩
  · exact fun U hU hUW => hOff U hU.1 hUW
  · exact fun U r hU hUW hr hBall => hOffQuant U r hU.1 hUW hr hBall
  · exact fun n => ae_restrict_of_ae_restrict_of_subset sdiff_subset (hEq n)

end Thesis
