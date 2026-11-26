module

public import SupportingAnalysis.Poisson.Derivatives
import SupportingAnalysis.Poisson.Equation
public import SupportingAnalysis.Poisson.Convolution

/-! Transfer of a compact Poisson Hessian estimate to smooth cutoff convolutions. -/

public section

open MeasureTheory
open scoped Convolution ContDiff ENNReal

set_option autoImplicit false

namespace SupportingAnalysis

private theorem real_convolution_comm {d : ℕ} (f g : E d → ℝ) :
    f ⋆[ContinuousLinearMap.mul ℝ ℝ] g = g ⋆[ContinuousLinearMap.mul ℝ ℝ] f := by
  funext x
  rw [convolution_mul_swap, convolution_mul]
  exact integral_congr_ae (.of_forall fun _ => mul_comm _ _)

theorem scalarHessian_convolution_cutoff {d : ℕ}
    {χ g : E d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hg : Integrable g) (i j : Fin d) (x : E d) :
    scalarHessian (χ ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x i j =
      ((fun y => scalarHessian χ y i j) ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x := by
  let dχ (y : E d) := fderiv ℝ χ y (axis i)
  have hdχ : ContDiff ℝ ∞ dχ :=
    (ContinuousLinearMap.apply ℝ ℝ (axis i)).contDiff.comp (hχ.fderiv_right (by simp))
  rw [real_convolution_comm χ g, real_convolution_comm (fun y => scalarHessian χ y i j) g]
  have hFirst : (fun y => fderiv ℝ (g ⋆[ContinuousLinearMap.mul ℝ ℝ] χ) y (axis i)) =
      g ⋆[ContinuousLinearMap.mul ℝ ℝ] dχ :=
    funext fun y => convolution_fderiv_right_apply g hg.locallyIntegrable hχ hχc y (axis i)
  unfold scalarHessian
  rw [hFirst, convolution_fderiv_right_apply g hg.locallyIntegrable hdχ
    (hχc.fderiv_apply ℝ (axis i)) x (axis j)]

private theorem laplacian_convolution_cutoff {d : ℕ}
    {χ g : E d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hg : Integrable g) :
    laplacian (χ ⋆[ContinuousLinearMap.mul ℝ ℝ] g) =
      (laplacian χ ⋆[ContinuousLinearMap.mul ℝ ℝ] g) := by
  funext x
  rw [real_convolution_comm χ g, real_convolution_comm (laplacian χ) g,
    laplacian_convolution g hg.locallyIntegrable hχ hχc, convolution_mul]

/-- A dimension-dependent Hessian weak bound for compact smooth functions implies
the weak bound for their cutoff Hessian kernels against arbitrary integrable data. -/
theorem kernelWeakHessian_of_compact_laplacian_bound {d : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hWeak : ∀ u : E d → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      ∀ (i j : Fin d) (ell : ℝ), 0 < ell →
        volume {x : E d | ell < |scalarHessian u x i j|} ≤
          ENNReal.ofReal (C * (∫ x, |laplacian u x|) / ell))
    (χ : E d → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (i j : Fin d) :
    WeakScalarConvolutionBound (fun p => scalarHessian χ p i j)
      (C * ∫ p, |laplacian χ p|) := by
  have hD := smooth_compact_scalarHessian hχ hχc i j
  have hD₁ : Integrable (fun p => scalarHessian χ p i j) :=
    hD.1.continuous.integrable_of_hasCompactSupport hD.2
  have hL₁ : Integrable (laplacian χ) := by
    unfold laplacian
    simpa only [scalarHessian] using
      integrable_finsetSum (μ := volume) Finset.univ fun i _ => by
        have h := smooth_compact_scalarHessian hχ hχc i i
        exact h.1.continuous.integrable_of_hasCompactSupport h.2
  apply weakScalarConvolutionBound_of_compact_input hD₁ hD.2
    (mul_nonneg hC (integral_nonneg fun x => abs_nonneg _))
  intro g hg hgc ell hell
  let u := χ ⋆[ContinuousLinearMap.mul ℝ ℝ] g
  have hu : ContDiff ℝ ∞ u :=
    hχc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hχ hg.locallyIntegrable
  have huc : HasCompactSupport u := hχc.convolution (ContinuousLinearMap.mul ℝ ℝ) hgc
  have h := hWeak u hu huc i j ell hell
  have hDeriv : (fun x => scalarHessian u x i j) =
      (fun x => scalarHessian χ x i j) ⋆[ContinuousLinearMap.mul ℝ ℝ] g :=
    funext (scalarHessian_convolution_cutoff hχ hχc hg i j)
  have hLap : laplacian u = laplacian χ ⋆[ContinuousLinearMap.mul ℝ ℝ] g :=
    laplacian_convolution_cutoff hχ hχc hg
  have hL : (∫ x, |laplacian u x|) ≤ (∫ x, |laplacian χ x|) * (∫ x, |g x|) := by
    rw [hLap]
    simpa only [Real.norm_eq_abs] using integral_norm_scalarConvolution_le hL₁ hg
  rw [← hDeriv]
  exact h.trans (ENNReal.ofReal_le_ofReal <| div_le_div_of_nonneg_right
    ((mul_le_mul_of_nonneg_left hL hC).trans_eq (mul_assoc _ _ _).symm) hell.le)

end SupportingAnalysis
