module

public import SupportingAnalysis.Euclidean

/-! The integral and Plancherel Fourier transforms agree on their common domain. -/

public section

open MeasureTheory SchwartzMap
open scoped ContDiff ENNReal FourierTransform

set_option autoImplicit false

namespace SupportingAnalysis

/-- The integral and L² Fourier transforms agree almost everywhere on L¹ ∩ L². -/
theorem fourier_toLp_two_ae_eq {d : ℕ} {f : E d → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    (⇑(𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure (E d)))) =ᵐ[volume] 𝓕 f := by
  let p : Lp ℂ 2 (volume : Measure (E d)) := hf₂.toLp f
  let Fp : Lp ℂ 2 (volume : Measure (E d)) := 𝓕 p
  have hlp : LocallyIntegrable (⇑Fp) volume :=
    (Lp.memLp Fp).locallyIntegrable (by norm_num)
  have hcont : Continuous (𝓕 f) := by
    simpa using! VectorFourier.fourierIntegral_continuous (L := innerₗ (E d))
      Real.continuous_fourierChar continuous_inner hf₁
  have hpoint : LocallyIntegrable (𝓕 f) volume := hcont.locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hlp hpoint (fun φ hφ hφc => ?_)
  let ψ : 𝓢(E d, ℂ) := (hφc.comp_left (g := Complex.ofReal) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ)
  have hψ (x : E d) : ψ x = (φ x : ℂ) := rfl
  have hpair := congrArg (fun T : 𝓢'(E d, ℂ) => T ψ)
    (Lp.fourier_toTemperedDistribution_eq p)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hpair
  exact calc
    (∫ x, φ x • Fp x) = ∫ x, ψ x • Fp x := by
      simp only [hψ, Complex.real_smul, smul_eq_mul]
    _ = ∫ x, (𝓕 ψ) x • p x := hpair.symm
    _ = ∫ x, (𝓕 ψ) x • f x := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx
      rw [show p x = f x from hx]
    _ = ∫ x, ψ x • (𝓕 f) x := by
      simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := innerₗ (E d)) Real.continuous_fourierChar continuous_inner ψ.integrable hf₁
    _ = ∫ x, φ x • (𝓕 f) x := by
      simp only [hψ, Complex.real_smul, smul_eq_mul]

end SupportingAnalysis
