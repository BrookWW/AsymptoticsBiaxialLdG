module

public import SupportingAnalysis.Poisson.Derivatives

/-! Coordinate Hessian and Laplacian symbols in Mathlib's Fourier normalization. -/

public section

open MeasureTheory
open scoped BigOperators ContDiff FourierTransform

set_option autoImplicit false

namespace SupportingAnalysis

private theorem fourier_coordinateDerivative {d : ℕ} {f : E d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (i : Fin d) (ξ : E d) :
    𝓕 (fun x => fderiv ℝ f x (axis i)) ξ =
      (2 * (Real.pi : ℂ) * Complex.I) * (ξ.ofLp i : ℂ) * 𝓕 f ξ := by
  have hif : Integrable f := hf.continuous.integrable_of_hasCompactSupport hcf
  have hi : Integrable (fderiv ℝ f) :=
    (hf.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hcf.fderiv ℝ)
  rw [← Real.fourier_continuousLinearMap_apply (a := axis i) hi,
    Real.fourier_fderiv hif (hf.differentiable (by simp)) hi]
  have hcoord : innerSL ℝ ξ (axis i) = ξ.ofLp i := by
    change inner ℝ ξ (EuclideanSpace.single i 1) = ξ.ofLp i
    rw [EuclideanSpace.inner_single_right]
    simp
  simp only [VectorFourier.fourierSMulRight_apply, neg_apply, hcoord,
    Complex.real_smul, smul_eq_mul, Complex.ofReal_neg]
  ring

private theorem fourier_ofReal_coordinateDerivative {d : ℕ} {f : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (i : Fin d) (ξ : E d) :
    𝓕 (fun x => Complex.ofReal (fderiv ℝ f x (axis i))) ξ =
      (2 * (Real.pi : ℂ) * Complex.I) * (ξ.ofLp i : ℂ) *
        𝓕 (fun x => Complex.ofReal (f x)) ξ := by
  have hderiv (x : E d) :
      Complex.ofReal (fderiv ℝ f x (axis i)) =
        fderiv ℝ (Complex.ofRealCLM ∘ f) x (axis i) := by
    rw [fderiv_comp x (Complex.ofRealCLM.differentiable _) (hf.differentiable (by simp) x),
      Complex.ofRealCLM.fderiv]
    rfl
  simp_rw [hderiv]
  exact fourier_coordinateDerivative
    (Complex.ofRealCLM.contDiff.comp hf) (hcf.comp_left (map_zero Complex.ofRealCLM)) i ξ

/-- The coordinate Hessian symbol carries the same common factor as the Laplacian. -/
theorem fourier_ofReal_scalarHessian {d : ℕ} {f : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (i j : Fin d) (ξ : E d) :
    𝓕 (fun x => Complex.ofReal (scalarHessian f x i j)) ξ =
      (2 * (Real.pi : ℂ) * Complex.I)^2 * (ξ.ofLp i : ℂ) * (ξ.ofLp j : ℂ) *
        𝓕 (fun x => Complex.ofReal (f x)) ξ := by
  let P := ContinuousLinearMap.apply ℝ ℝ (axis i)
  have hdiff : ContDiff ℝ ∞ (fun x => fderiv ℝ f x (axis i)) :=
    P.contDiff.comp (hf.fderiv_right (by simp))
  have hcomp : HasCompactSupport (fun x => fderiv ℝ f x (axis i)) :=
    (hcf.fderiv ℝ).comp_left (g := P) (map_zero P)
  unfold scalarHessian
  rw [fourier_ofReal_coordinateDerivative hdiff hcomp j ξ,
    fourier_ofReal_coordinateDerivative hf hcf i ξ]
  ring

/-- The Laplacian symbol in the same Fourier normalization as the coordinate Hessian. -/
theorem fourier_ofReal_laplacian {d : ℕ} {f : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (ξ : E d) :
    𝓕 (fun x => Complex.ofReal (laplacian f x)) ξ =
      (2 * (Real.pi : ℂ) * Complex.I)^2 * ((‖ξ‖ ^ 2 : ℝ) : ℂ) *
        𝓕 (fun x => Complex.ofReal (f x)) ξ := by
  have hsum :
      (fun x => Complex.ofReal (laplacian f x)) =
        fun x => ∑ i : Fin d, Complex.ofReal (scalarHessian f x i i) := by
    funext x
    simp only [laplacian, scalarHessian, Complex.ofReal_sum]
  have hFourier_sum :
      𝓕 (fun x => ∑ i : Fin d, Complex.ofReal (scalarHessian f x i i)) ξ =
        ∑ i : Fin d, 𝓕 (fun x => Complex.ofReal (scalarHessian f x i i)) ξ := by
    simp only [Real.fourier_eq, Finset.smul_sum]
    refine integral_finsetSum Finset.univ (fun i _ => (Real.fourierIntegral_convergent_iff ξ).mpr ?_)
    obtain ⟨hi, hci⟩ := smooth_compact_scalarHessian hf hcf i i
    exact Complex.ofRealCLM.integrable_comp (hi.continuous.integrable_of_hasCompactSupport hci)
  rw [hsum, hFourier_sum]
  simp_rw [fourier_ofReal_scalarHessian hf hcf]
  have hnorm : (∑ i : Fin d, (ξ.ofLp i : ℂ)^2) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [EuclideanSpace.real_norm_sq_eq, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun i _ => (Complex.ofReal_pow (ξ.ofLp i) 2).symm)
  rw [← Finset.sum_mul]
  simp_rw [mul_assoc, ← pow_two]
  rw [← Finset.mul_sum, hnorm, mul_assoc]

end SupportingAnalysis
