module

public import SupportingAnalysis.Basics

/-! The one-dimensional weak bound for convolution with the Hessian of a cutoff. -/

public section

open MeasureTheory Set
open scoped Convolution ContDiff ENNReal

set_option autoImplicit false

namespace SupportingAnalysis

private theorem smooth_compact_partial {d : ℕ} {f : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (i : Fin d) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x (axis i)) ∧
      HasCompactSupport (fun x => fderiv ℝ f x (axis i)) := by
  let P := ContinuousLinearMap.apply ℝ ℝ (axis i)
  exact ⟨P.contDiff.comp (hf.fderiv_right (by simp)),
    (hcf.fderiv ℝ).comp_left (g := P) (map_zero P)⟩

/-- Coordinate Hessians of smooth compactly supported functions have the same regularity. -/
theorem smooth_compact_scalarHessian {d : ℕ} {f : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (i j : Fin d) :
    ContDiff ℝ ∞ (fun x => scalarHessian f x i j) ∧
      HasCompactSupport (fun x => scalarHessian f x i j) := by
  obtain ⟨h₁, h₂⟩ := smooth_compact_partial hf hcf i
  exact smooth_compact_partial h₁ h₂ j

/-- Young's L¹ inequality for the usual scalar convolution on Euclidean space. -/
theorem integral_norm_scalarConvolution_le {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {f g : E d → 𝕜} (hf : Integrable f) (hg : Integrable g) :
    (∫ x, ‖(f ⋆[ContinuousLinearMap.mul 𝕜 𝕜] g) x‖) ≤
      (∫ x, ‖f x‖) * (∫ x, ‖g x‖) := by
  calc
    _ ≤ ∫ x, (((fun y => ‖f y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        (fun y => ‖g y‖)) x) := by
      refine integral_mono
        (hf.integrable_convolution (ContinuousLinearMap.mul 𝕜 𝕜) hg).norm
        (hf.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hg.norm) ?_
      intro x
      simp only [convolution_mul, ← norm_mul]
      exact norm_integral_le_integral_norm _
    _ = _ := integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf.norm hg.norm

/-- The weak L¹ estimate with constant one for the convolution of L¹ scalar kernels. -/
theorem measure_scalarConvolution_superlevel_le {d : ℕ} {f g : E d → ℝ}
    (hf : Integrable f) (hg : Integrable g) {ell : ℝ} (hell : 0 < ell) :
    volume {x : E d | ell < |(f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x|} ≤
      ENNReal.ofReal (((∫ x, |f x|) * (∫ x, |g x|)) / ell) := by
  let u := f ⋆[ContinuousLinearMap.mul ℝ ℝ] g
  have hu : Integrable u := hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hg
  have hsubset : {x : E d | ell < |u x|} ⊆ {x : E d | ENNReal.ofReal ell ≤ ENNReal.ofReal ‖u x‖} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using (show ell < |u x| from hx).le)
  calc
    _ ≤ volume {x : E d | ENNReal.ofReal ell ≤ ENNReal.ofReal ‖u x‖} :=
      measure_mono hsubset
    _ ≤ (∫⁻ x, ENNReal.ofReal ‖u x‖) / ENNReal.ofReal ell :=
      meas_ge_le_lintegral_div hu.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
        (ENNReal.ofReal_pos.mpr hell).ne' ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((∫ x, ‖u x‖) / ell) := by
      rw [ENNReal.ofReal_div_of_pos hell,
        ofReal_integral_eq_lintegral_ofReal hu.norm
          (Filter.Eventually.of_forall (fun x => norm_nonneg (u x)))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (by simpa only [Real.norm_eq_abs] using integral_norm_scalarConvolution_le hf hg) hell.le)

/-- The Hessian convolution bound for d = 1, with the constant C₁ equal to one. -/
theorem kernelWeakHessian_one {cutoff g : E 1 → ℝ}
    (hcutoff : ContDiff ℝ ∞ cutoff) (hcompact : HasCompactSupport cutoff)
    (hg : Integrable g) (i j : Fin 1) {ell : ℝ} (hell : 0 < ell) :
    volume {x : E 1 | ell < |((fun y => scalarHessian cutoff y i j)
      ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x|} ≤
      ENNReal.ofReal (((∫ x, |laplacian cutoff x|) * (∫ x, |g x|)) / ell) := by
  have heq : (fun x => scalarHessian cutoff x i j) = laplacian cutoff := by
    funext x
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    simp only [laplacian, scalarHessian, Fin.sum_univ_one]
  obtain ⟨hsmooth, hsupport⟩ := smooth_compact_scalarHessian hcutoff hcompact i j
  rw [← heq]
  exact measure_scalarConvolution_superlevel_le
    (hsmooth.continuous.integrable_of_hasCompactSupport hsupport) hg hell

end SupportingAnalysis
