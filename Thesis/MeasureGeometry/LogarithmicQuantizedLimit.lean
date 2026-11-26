module

public import Thesis.MeasureGeometry.LogarithmicClassicalLimit
public import Thesis.MeasureGeometry.CylinderRegularSequence
public import Thesis.MeasureGeometry.CylinderDensityAssembly
public import Thesis.Interpolation.CylinderUpperRecovery
import Thesis.MeasureGeometry.EnergyMonotonicity

/-! Quantization and regular cylinder comparison for the same logarithmic subsequence. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

/-- The normalized upper estimate on each fixed regular lateral cylinder,
uniform over the admissible end heights and with the cap coefficient fixed
before choosing the geometry. -/
def RegularCylinderUpperRecovery (a : BulkCoefficients) (Ω R : Set Point)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (q : Point → S0) (μ : ℕ → Measure Point) : Prop :=
  ∀ cap : ℝ, 0 ≤ cap → ∃ C ≥ (0 : ℝ),
    ∀ (B : OrthonormalBasis (Fin 3) ℝ Point) (x : Point) {r s : ℝ}, 0 < r → 0 < s → r < s →
      closedBall x (2 * s) ⊆ Ω → ∀ K : Set Point, IsCompact K → K ⊆ R →
        (∀ z ∈ Icc (-s) s, ∀ w : NativeCircle, x + axisChart B (r • w.val, z) ∈ K) →
        ∀ p : C(NativeCircle, vacuum a),
          (∀ w, (p w).val = q (x + axisChart B (r • w.val, 0))) →
          ∀ ξ > 0, ∀ᶠ n : ℕ in atTop,
            ∀ lo ∈ Ioo (-s) (-(s / 2)), ∀ hi ∈ Ioo (s / 2) s,
              planarSmoothEnergy a (ε n) (cylinderSliceMap B x (Q n) lo) r +
                planarSmoothEnergy a (ε n) (cylinderSliceMap B x (Q n) hi) r ≤
                  cap * Real.log (1 / (ε n : ℝ)) →
              ((μ n) (translatedAxisCylinder x (B 2) r lo hi)).toReal / (hi - lo) ≤
                nativeVacuumCircleCost a p + C * (r / (hi - lo)) + ξ

/-- The classical representatives of the logarithmic subsequence realize the
same finite normalized measures. Its regular cylinder comparisons prove
quantization of the density of the original limit measure. -/
theorem exists_logarithmic_limit_quantized_core (a : BulkCoefficients)
    (hProj : HasPenalizedProjectionLayer a) (hDense : External.SmoothVacuumSphereDensity a)
    (hP : External.QuaternionSpherePoincare 3 (by decide : 2 ≤ 3)) (hA19 : External.A19Prop31)
    (hReg : InteriorPoissonRegularity) (hEstimate : InteriorPoissonGradientEstimate)
    (hMean : External.ClassicalScalarSubsolutionMeanValue)
    (hCoarea : External.PlanarScalarCoarea) (hPolar : External.PeriodicAngularSobolev)
    (hSurf : External.TerminalCylinderSurfaceSobolev) (hTransport : External.AmbientBiLipschitzSobolevPullback3)
    (hChart : External.CylinderBoundaryChartTraceTransport) (hKernel : External.CylinderBoundaryTraceKernel)
    (M : ℝ) (hM : 0 < M) :
    ∃ C : Set Point → ℝ → ℝ,
      (∀ U r, 0 < C U r) ∧
      ∀ (Ω : Set Point), IsBoundedDomain Ω →
      ∀ (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient),
        (∀ ε, IsLocalEnergyMinimizer a ε Ω (Q ε) (D ε)) →
        (∀ ε, energy a ε Ω (Q ε) (D ε) ≤ ENNReal.ofReal (M * (Real.log (1 / (ε : ℝ)) + 1)) ∧
          eLpNorm (Q ε) ⊤ (volume.restrict Ω) ≤ ENNReal.ofReal M) →
        ∃ (ε : ℕ → ElasticScale) (ν : FiniteMeasure Point)
          (Q₀ : Point → S0) (D₀ : Point → Gradient) (Qreg : ℕ → Point → S0),
          let S := (ν : Measure Point).support
          let W := Ω \ S
          let Spts := singularSet W Q₀
          let R := W \ Spts
          let m := fun n => normalizedEnergyMeasure a (ε n) Ω (Q (ε n)) (D (ε n))
          Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧
          (ν : Measure Point) (closure Ω)ᶜ = 0 ∧ IsClosed S ∧ S ⊆ closure Ω ∧
          WeakStarOnClosure Ω m ν ∧
          CountablyRectifiableOne (Ω ∩ S) ∧ HausdorffOne (Ω ∩ S) < ⊤ ∧
          (∀ U : Set Point, IsOpen U → CompactlyContained U W →
            ∃ B > (0 : ℝ), ∀ n, energy a (ε n) U (Q (ε n)) (D (ε n)) ≤ ENNReal.ofReal B) ∧
          (∀ (U : Set Point) (r : ℝ), IsOpen U → CompactlyContained U W → 0 < r →
            (∀ x ∈ closure U, closedBall x r ⊆ W) →
            ∀ᶠ n in atTop, energy a (ε n) U (Q (ε n)) (D (ε n)) ≤ ENNReal.ofReal (C U r)) ∧
          IsLocalDirichletMinimizer a W Q₀ D₀ ∧ WeakLaplacianEq W D₀ (harmonicRhs a Q₀ D₀) ∧
          StrongH1Loc W (Q ∘ ε) (D ∘ ε) Q₀ D₀ ∧ ConvergesScaledPotentialLoc a W ε (Q ∘ ε) ∧
          LocallyFiniteIn W Spts ∧ ContDiffOn ℝ ∞ Q₀ R ∧
          D₀ =ᵐ[volume.restrict R] ClassicalGradient Q₀ ∧
          (∀ n, Qreg n =ᵐ[volume.restrict Ω] Q (ε n)) ∧
          (∀ n, D (ε n) =ᵐ[volume.restrict Ω] ClassicalGradient (Qreg n)) ∧
          (∀ n, ContDiffOn ℝ ∞ (Qreg n) Ω) ∧
          (∀ n, ∀ x ∈ Ω, (ε n : ℝ) ^ 2 • (laplacian (Qreg n) x : S0).val = bulkGradient a (Qreg n x)) ∧
          (∀ n x, x ∈ Ω → ‖Qreg n x‖ ≤ M) ∧
          (∀ j : ℕ, ConvergesCjLoc j R Qreg Q₀) ∧
          (∃ c > (0 : ℝ), ∀ x ∈ Ω ∩ S, ∃ θ ≥ c, Tendsto (oneDensity ν x) (𝓝[>] 0) (𝓝 θ)) ∧
          (∀ n, IsLocalEnergyMinimizer a (ε n) Ω (Qreg n) (ClassicalGradient (Qreg n))) ∧
          (∀ n, energy a (ε n) Ω (Qreg n) (ClassicalGradient (Qreg n)) ≤
            ENNReal.ofReal (M * (Real.log (1 / (ε n : ℝ)) + 1))) ∧
          (∀ n, m n = normalizedEnergyMeasure a (ε n) Ω (Qreg n) (ClassicalGradient (Qreg n))) ∧
          (∀ n, IsFiniteMeasure (m n)) ∧ MapsTo Q₀ R (vacuum a) ∧
          (∀ K : Set Point, IsCompact K → K ⊆ R → ∃ B > (0 : ℝ),
            ∀ n x, x ∈ K → energyDensity a (ε n) (Qreg n x) (ClassicalGradient (Qreg n) x) ≤ B) ∧
          (∀ K : Set Point, IsCompact K → K ⊆ R → TendstoUniformlyOn Qreg Q₀ atTop K) ∧
          RegularCylinderUpperRecovery a Ω R ε Qreg Q₀ m ∧ DensityQuantized a ν (Ω ∩ S) ∧
          ∃ V : Measure (Point × LineProjection), IsAssociatedVarifold Ω (Ω ∩ S) ν V ∧ IsStationaryVarifold Ω V := by
  obtain ⟨C, hC, hCore⟩ := exists_logarithmic_limit_classical_core a hProj hDense hP hA19 hReg hEstimate hMean M hM
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ Q D hMin hBounds
  obtain ⟨ε, ν, Q₀, D₀, Qreg, hε, hν, hClosed, hSupport, hStar, hRect, hLength, hOff, hOffQuant,
    hQMin, hQHarm, hStrong, hPot, hFinite, hSmooth, hGrad, hEq, hGradReg, hRegSmooth, hEuler, hRange,
    hConverges, hDensityPositive, V, hAssoc, hStat⟩ := hCore Ω hΩ Q D hMin hBounds
  let S := (ν : Measure Point).support
  let W := Ω \ S
  let R := W \ singularSet W Q₀
  let m (n : ℕ) := normalizedEnergyMeasure a (ε n) Ω (Q (ε n)) (D (ε n))
  have hROpen : IsOpen R := isOpen_diff_singularSet (Ω := W) Q₀
  have hRW : R ⊆ W := sdiff_subset
  have hWΩ : W ⊆ Ω := sdiff_subset
  have hMinReg (n : ℕ) : IsLocalEnergyMinimizer a (ε n) Ω (Qreg n) (ClassicalGradient (Qreg n)) :=
    localEnergyMinimizer_congr_ae (hMin (ε n)) (hEq n).symm (hGradReg n)
  have hEnergy (n : ℕ) : energy a (ε n) Ω (Qreg n) (ClassicalGradient (Qreg n)) ≤
      ENNReal.ofReal (M * (Real.log (1 / (ε n : ℝ)) + 1)) := by
    rw [← energy_congr_of_ae a (ε n) (hEq n).symm (hGradReg n)]
    exact (hBounds (ε n)).1
  have hF (n : ℕ) : energy a (ε n) Ω (Qreg n) (ClassicalGradient (Qreg n)) < ⊤ :=
    (hEnergy n).trans_lt ENNReal.ofReal_lt_top
  obtain ⟨hNorm', _, hVac, hDensity, hConv⟩ := regularCylinderData_of_sameSequence a hΩ.1 hROpen hRW hWΩ
    hEstimate hMean hM.le ε (Q ∘ ε) Qreg (D ∘ ε) Q₀ D₀ hε (fun n => (hMin (ε n)).1)
    (fun n => (hBounds (ε n)).2) hRegSmooth (fun n => (hEq n).symm) hEuler hStrong hPot hSmooth
    hQMin.2.1 hGrad
  have hNorm (n : ℕ) : m n = normalizedEnergyMeasure a (ε n) Ω (Qreg n) (ClassicalGradient (Qreg n)) := hNorm' n
  have hνfin (n : ℕ) : IsFiniteMeasure (m n) := by
    constructor
    rw [hNorm n, normalizedEnergyMeasure_apply a (ε n) Ω (Qreg n) (ClassicalGradient (Qreg n))
      MeasurableSet.univ, univ_inter]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hF n)
  have hUpper : RegularCylinderUpperRecovery a Ω R ε Qreg Q₀ m :=
    exists_eventually_normalizedCylinder_upper_of_regularBand a hPolar hSurf hTransport hChart hKernel
      hΩ.1 hROpen (hRW.trans hWΩ) ε Qreg Q₀ hε hMinReg hF hRegSmooth hSmooth hVac hRange hDensity hConv m hNorm
  have hAssociatedWeight := hAssoc
  obtain ⟨f, _, hf, _, hRep, _, _, _⟩ := hAssociatedWeight
  obtain ⟨c, hc, hDensityPositive'⟩ := hDensityPositive
  have hη : 0 < 2 * c := by positivity
  have hD : ∀ x ∈ Ω ∩ S, ∃ θ ≥ (2 * c) / 2, Tendsto (oneDensity ν x) (𝓝[>] 0) (𝓝 θ) := by
    have hHalf : (2 * c) / 2 = c := by ring
    simpa only [hHalf] using hDensityPositive'
  have hQuantized : DensityQuantized a ν (Ω ∩ S) :=
    densityQuantized_of_regularCylinder_upper_recovery hCoarea hPolar a hΩ.1 hν hf hRep hRect hLength
      hη hD hFinite hM.le ε Qreg Q₀ hε hRegSmooth hEuler hRange hEnergy hSmooth.continuousOn hVac hDensity hConv
      m hνfin hNorm hStar hUpper
  exact ⟨ε, ν, Q₀, D₀, Qreg, hε, hν, hClosed, hSupport, hStar, hRect, hLength, hOff, hOffQuant, hQMin, hQHarm,
    hStrong, hPot, hFinite, hSmooth, hGrad, hEq, hGradReg, hRegSmooth, hEuler, hRange, hConverges,
    ⟨c, hc, hDensityPositive'⟩, hMinReg, hEnergy, hNorm, hνfin, hVac, hDensity, hConv, hUpper, hQuantized,
    V, hAssoc, hStat⟩

end Thesis.MeasureGeometry

end
