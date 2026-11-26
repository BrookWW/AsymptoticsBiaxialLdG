module

public import SupportingAnalysis.Poisson.LineKernel
public import SupportingAnalysis.Poisson.RadialAverage
public import SupportingAnalysis.Poisson.PublicEstimates

/-! The canonical compact Newtonian correction in every positive dimension. -/

@[expose] public section

open MeasureTheory Metric Set InnerProductSpace
open scoped ContDiff

set_option autoImplicit false

namespace SupportingAnalysis

/-- The Newtonian kernel with the positive distributional Laplacian convention. -/
noncomputable def canonicalNewtonian (d : ℕ) (x : E d) : ℝ :=
  if h : d = 1 then newtonianOne (cast (congrArg E h) x)
  else if h : d = 2 then HolderToCK.fundamentalLogExpression (cast (congrArg E h) x)
  else HolderToCK.fundamentalPowerExpression x

/-- The Euclidean vector representative of the weak gradient of the Newtonian kernel. -/
noncomputable def canonicalNewtonianGradient (d : ℕ) (x : E d) : E d :=
  if h : d = 1 then cast (congrArg E h.symm) (newtonianOneGradient (cast (congrArg E h) x))
  else holderNewtonianGradient x


theorem canonicalNewtonian_one : canonicalNewtonian 1 = newtonianOne := by
  funext x
  simp [canonicalNewtonian]

theorem canonicalNewtonian_two :
    canonicalNewtonian 2 = HolderToCK.fundamentalLogExpression := by
  funext x
  simp [canonicalNewtonian]

theorem canonicalNewtonian_of_three_le {d : ℕ} (hd : 3 ≤ d) :
    canonicalNewtonian d = HolderToCK.fundamentalPowerExpression := by
  have h₁ : d ≠ 1 := by omega
  have h₂ : d ≠ 2 := by omega
  funext x
  simp [canonicalNewtonian, h₁, h₂]

theorem canonicalNewtonianGradient_one : canonicalNewtonianGradient 1 = newtonianOneGradient := by
  funext x
  simp [canonicalNewtonianGradient]

theorem canonicalNewtonianGradient_of_ne_one {d : ℕ} (hd : d ≠ 1) :
    canonicalNewtonianGradient d = holderNewtonianGradient := by
  funext x
  simp [canonicalNewtonianGradient, hd]

theorem harmonic_radial_probability_mean {d : ℕ} (hd : 0 < d)
    (u : E d → ℝ) (a : E d) (r : ℝ) (ρ : E d → ℝ)
    (hr : 0 < r) (hu : HarmonicOnNhd u (closedBall a r)) (hρ : Continuous ρ)
    (hRad : ∃ profile : ℝ → ℝ, ∀ y, ρ y = profile ‖y‖)
    (hNonneg : ∀ y, 0 ≤ ρ y) (hSupp : Function.support ρ ⊆ ball 0 r)
    (hMass : (∫ y, ρ y) = 1) : (∫ y, ρ y * u (a - y)) = u a := by
  by_cases h : d = 1
  · subst d
    exact oneDimensional_harmonic_radial_probability_mean u a r ρ hr hu hρ hRad hNonneg hSupp hMass
  · exact holder_harmonic_radial_probability_mean (by omega) u a r ρ hr hu hρ hRad hNonneg hSupp hMass

/-- Compact support, the two scaled L¹ bounds, and the distributional gradient for the
canonical kernel in any positive dimension. -/
theorem compactPotential_canonical {d : ℕ} (hd : 0 < d) (k : RadialProbabilityDensity d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r > (0 : ℝ),
      tsupport (potentialCorrection (canonicalNewtonian d) k r) ⊆ closedBall 0 r ∧
      tsupport (potentialCorrection (canonicalNewtonianGradient d) k r) ⊆ closedBall 0 r ∧
      Integrable (potentialCorrection (canonicalNewtonian d) k r) ∧
      Integrable (potentialCorrection (canonicalNewtonianGradient d) k r) ∧
      (∫ x, ‖potentialCorrection (canonicalNewtonian d) k r x‖) ≤ r ^ 2 * C ∧
      (∫ x, ‖potentialCorrection (canonicalNewtonianGradient d) k r x‖) ≤ r * C ∧
      ∀ (i : Fin d) (φ : E d → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
        (∫ y, potentialCorrection (canonicalNewtonian d) k r y * fderiv ℝ φ y (axis i)) =
          -∫ y, (potentialCorrection (canonicalNewtonianGradient d) k r y) i * φ y := by
  by_cases h₁ : d = 1
  · subst d
    simpa only [canonicalNewtonian_one, canonicalNewtonianGradient_one] using
      compactPotential_with_gradient newtonianOne newtonianOneGradient (by decide)
        newtonianOne_locallyIntegrable newtonianOneGradient_locallyIntegrable
        newtonianOne_harmonicOffZero (fun _ hx => newtonianOne_classicalGradient hx)
        newtonianOne_testDerivative
        (fun r hr => ⟨0, fun x _ => by simpa only [add_zero, Nat.cast_one] using newtonianOne_dilate hr x⟩)
        oneDimensional_harmonic_radial_probability_mean k
  · by_cases h₂ : d = 2
    · subst d
      simpa only [canonicalNewtonian_two, canonicalNewtonianGradient_of_ne_one h₁] using compactPotential_with_gradient HolderToCK.fundamentalLogExpression
        holderNewtonianGradient (by decide) HolderToCK.fundamentalLog_locallyIntegrable
        (holderNewtonianGradient_locallyIntegrable (by decide)) holderLog_harmonicOffZero
        (fun _ hx => holderLog_classicalGradient hx) holderLog_testDerivative
        (fun r hr => ⟨_, fun _ hx => holderLog_dilate hr hx⟩)
        (holder_harmonic_radial_probability_mean (by decide)) k
    · have hd₃ : 3 ≤ d := by omega
      simpa only [canonicalNewtonian_of_three_le hd₃, canonicalNewtonianGradient_of_ne_one h₁] using
        compactPotential_with_gradient HolderToCK.fundamentalPowerExpression holderNewtonianGradient
          hd (HolderToCK.fundamentalPower_locallyIntegrable hd₃)
          (holderNewtonianGradient_locallyIntegrable hd) holderPower_harmonicOffZero
          (fun _ hx => holderPower_classicalGradient hd₃ hx) (holderPower_testDerivative hd₃)
          (fun r hr => ⟨0, fun x _ => by simpa only [add_zero] using holderPower_dilate hr x⟩)
          (holder_harmonic_radial_probability_mean (by omega)) k

theorem canonicalNewtonian_locallyIntegrable {d : ℕ} (hd : 0 < d) :
    LocallyIntegrable (canonicalNewtonian d) volume := by
  by_cases h₁ : d = 1
  · subst d
    simpa only [canonicalNewtonian_one] using newtonianOne_locallyIntegrable
  · by_cases h₂ : d = 2
    · subst d
      simpa only [canonicalNewtonian_two] using
        HolderToCK.fundamentalLog_locallyIntegrable
    · simpa only [canonicalNewtonian_of_three_le (by omega : 3 ≤ d)] using
        HolderToCK.fundamentalPower_locallyIntegrable (by omega : 3 ≤ d)

theorem canonicalNewtonian_distributionPairing {d : ℕ} (hd : 0 < d)
    (φ : E d → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, canonicalNewtonian d x * laplacian φ x) = φ 0 := by
  by_cases h₁ : d = 1
  · subst d
    simpa only [canonicalNewtonian_one] using
      newtonianOne_distributionPairing φ
        (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hφc
  · by_cases h₂ : d = 2
    · subst d
      simpa only [canonicalNewtonian_two] using
        holderLog_distributionPairing φ hφ hφc
    · simpa only [canonicalNewtonian_of_three_le (by omega : 3 ≤ d)] using
        holderPower_distributionPairing (by omega : 3 ≤ d) φ hφ hφc

theorem compactPotential_canonical_laplacianPairing {d : ℕ} (hd : 0 < d)
    (k : RadialProbabilityDensity d) {r : ℝ} (hr : 0 < r)
    (φ : E d → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, potentialCorrection (canonicalNewtonian d) k r x * laplacian φ x) =
      φ 0 - ∫ x, k.scaled r x * φ x :=
  potentialCorrection_laplacianPairing (canonicalNewtonian d) (canonicalNewtonian_locallyIntegrable hd)
    (canonicalNewtonian_distributionPairing hd) k hr φ hφ hφc

end SupportingAnalysis
