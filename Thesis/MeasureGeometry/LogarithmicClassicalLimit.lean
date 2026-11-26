module

public import Thesis.MeasureGeometry.LogarithmicLimitCore
public import Thesis.Variational.InteriorClassicalConvergence
import Thesis.Variational.ClassicalLimitTransfer

/-! The regular classical convergence of the actual logarithmic
subsequence, retaining the same measure and vacuum limit. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

/-- On the regular complement of the limiting support and point
singularities, the original logarithmic subsequence converges in every
classical order. The measure, support, and all local bounds use the same
sequence chosen by the logarithmic core. -/
theorem exists_logarithmic_limit_classical_core (a : BulkCoefficients)
    (hProj : HasPenalizedProjectionLayer a) (hDense : External.SmoothVacuumSphereDensity a)
    (hP : External.QuaternionSpherePoincare 3 (by decide : 2 ≤ 3)) (hA19 : External.A19Prop31)
    (hReg : InteriorPoissonRegularity) (hEstimate : InteriorPoissonGradientEstimate)
    (hMean : External.ClassicalScalarSubsolutionMeanValue) (M : ℝ) (hM : 0 < M) :
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
          Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧
          (ν : Measure Point) (closure Ω)ᶜ = 0 ∧ IsClosed S ∧ S ⊆ closure Ω ∧
          WeakStarOnClosure Ω (fun n => normalizedEnergyMeasure a (ε n) Ω (Q (ε n)) (D (ε n))) ν ∧
          CountablyRectifiableOne (Ω ∩ S) ∧ HausdorffOne (Ω ∩ S) < ⊤ ∧
          (∀ U : Set Point, IsOpen U → CompactlyContained U W →
            ∃ B > (0 : ℝ), ∀ n, energy a (ε n) U (Q (ε n)) (D (ε n)) ≤ ENNReal.ofReal B) ∧
          (∀ (U : Set Point) (r : ℝ), IsOpen U → CompactlyContained U W → 0 < r →
            (∀ x ∈ closure U, closedBall x r ⊆ W) →
            ∀ᶠ n in atTop, energy a (ε n) U (Q (ε n)) (D (ε n)) ≤ ENNReal.ofReal (C U r)) ∧
          IsLocalDirichletMinimizer a W Q₀ D₀ ∧ WeakLaplacianEq W D₀ (harmonicRhs a Q₀ D₀) ∧
          StrongH1Loc W (Q ∘ ε) (D ∘ ε) Q₀ D₀ ∧ ConvergesScaledPotentialLoc a W ε (Q ∘ ε) ∧
          LocallyFiniteIn W Spts ∧ ContDiffOn ℝ ∞ Q₀ (W \ Spts) ∧
          D₀ =ᵐ[volume.restrict (W \ Spts)] ClassicalGradient Q₀ ∧
          (∀ n, Qreg n =ᵐ[volume.restrict Ω] Q (ε n)) ∧
          (∀ n, D (ε n) =ᵐ[volume.restrict Ω] ClassicalGradient (Qreg n)) ∧
          (∀ n, ContDiffOn ℝ ∞ (Qreg n) Ω) ∧
          (∀ n, ∀ x ∈ Ω, (ε n : ℝ) ^ 2 • (laplacian (Qreg n) x : S0).val = bulkGradient a (Qreg n x)) ∧
          (∀ n x, x ∈ Ω → ‖Qreg n x‖ ≤ M) ∧
          (∀ j : ℕ, ConvergesCjLoc j (W \ Spts) Qreg Q₀) ∧
          (∃ c > (0 : ℝ), ∀ x ∈ Ω ∩ S, ∃ θ ≥ c, Tendsto (oneDensity ν x) (𝓝[>] 0) (𝓝 θ)) ∧
          ∃ V : Measure (Point × LineProjection), IsAssociatedVarifold Ω (Ω ∩ S) ν V ∧ IsStationaryVarifold Ω V := by
  obtain ⟨C, hC, hCore⟩ := exists_logarithmic_limit_core a hProj hDense hP hA19 hReg M hM
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ Q D hMin hBounds
  obtain ⟨ε, ν, Q₀, D₀, Qreg, hε, hν, hClosed, hSupport, hStar, hRect, hLength, hOff, hOffQuant,
    hQMin, hQHarm, hStrong, hPot, hFinite, hSmooth, hGrad, hEq, hRegSmooth, hEuler, hDensity, V, hAssoc, hStat⟩ :=
    hCore Ω hΩ Q D hMin hBounds
  let S := (ν : Measure Point).support
  let W := Ω \ S
  let U := W \ singularSet W Q₀
  have hU : IsOpen U := isOpen_diff_singularSet (Ω := W) Q₀
  have hUW : U ⊆ W := sdiff_subset
  have hUΩ : U ⊆ Ω := hUW.trans sdiff_subset
  have hGradReg (n : ℕ) : D (ε n) =ᵐ[volume.restrict Ω] ClassicalGradient (Qreg n) :=
    (hMin (ε n)).1.ae_eq_classicalGradient hΩ.1 ((contDiffOn_infty.mp (hRegSmooth n)) 1) (hEq n).symm
  have hValues (n : ℕ) : (Q ∘ ε) n =ᵐ[volume.restrict U] Qreg n :=
    ae_restrict_of_ae_restrict_of_subset hUΩ (hEq n).symm
  have hCols (n : ℕ) : (D ∘ ε) n =ᵐ[volume.restrict U] ClassicalGradient (Qreg n) :=
    ae_restrict_of_ae_restrict_of_subset hUΩ (hGradReg n)
  have hStrong' : StrongH1Loc U Qreg (fun n => ClassicalGradient (Qreg n)) Q₀ (ClassicalGradient Q₀) :=
    hStrong.congr_ae_on_subset hUW hValues hCols (EventuallyEq.rfl) hGrad
  have hPot' : ConvergesScaledPotentialLoc a U ε Qreg := hPot.congr_ae_on_subset hUW hValues
  have hRange (n : ℕ) (x : Point) (hx : x ∈ Ω) : ‖Qreg n x‖ ≤ M := by
    have hOrig : ∀ᵐ y ∂volume.restrict Ω, ‖Q (ε n) y‖ ≤ M := by
      filter_upwards [enorm_ae_le_eLpNormEssSup (Q (ε n)) (volume.restrict Ω)] with y hy
      apply (ENNReal.ofReal_le_ofReal_iff hM.le).mp
      rw [ofReal_norm]
      exact hy.trans (by simpa only [eLpNorm_exponent_top] using (hBounds (ε n)).2)
    have hAE : ∀ᵐ y ∂volume.restrict Ω, ‖Qreg n y‖ ≤ M := by
      filter_upwards [hEq n, hOrig] with y hy hB
      rwa [hy]
    have hNormEq : (fun y => ‖Qreg n y‖) =ᵐ[volume.restrict Ω] fun y => min ‖Qreg n y‖ M :=
      hAE.mono fun _ hy => (min_eq_left hy).symm
    have hCont := (hRegSmooth n).continuousOn.norm
    exact (Measure.eqOn_open_of_ae_eq hNormEq hΩ.1 hCont (hCont.inf continuousOn_const) hx).trans_le
      (min_le_right _ _)
  have hRangeU : BddAbove ((fun p : ℕ × Point => ‖Qreg p.1 p.2‖) '' (univ ×ˢ U)) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨⟨n, x⟩, hx, rfl⟩
    exact hRange n x (hUΩ hx.2)
  have hConverges := convergesCjLoc_of_regular_penalized_solutions a hEstimate hMean hU ε Qreg Q₀ hε
    (fun n => (hRegSmooth n).mono hUΩ) hSmooth (fun n x hx => hEuler n x (hUΩ hx)) hRangeU hStrong' hPot'
  exact ⟨ε, ν, Q₀, D₀, Qreg, hε, hν, hClosed, hSupport, hStar, hRect, hLength, hOff, hOffQuant,
    hQMin, hQHarm, hStrong, hPot, hFinite, hSmooth, hGrad, hEq, hGradReg, hRegSmooth, hEuler, hRange,
    hConverges, hDensity, V, hAssoc, hStat⟩

end Thesis.MeasureGeometry

end
