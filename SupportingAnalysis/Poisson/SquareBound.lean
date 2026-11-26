module

public import SupportingAnalysis.Poisson.Fourier
public import SupportingAnalysis.Poisson.Plancherel

/-! The Plancherel bound for convolution with a coordinate Hessian of a cutoff. -/

public section

open MeasureTheory
open scoped BigOperators ContDiff Convolution ENNReal FourierTransform

set_option autoImplicit false

namespace SupportingAnalysis

theorem smooth_compact_laplacian {d : ℕ} {f : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    ContDiff ℝ ∞ (laplacian f) ∧ HasCompactSupport (laplacian f) := by
  have hparts (i : Fin d) := smooth_compact_scalarHessian hf hcf i i
  constructor
  · exact ContDiff.sum (s := Finset.univ) (fun i _ => (hparts i).1)
  · have heq : laplacian f = ∑ i : Fin d, fun x => scalarHessian f x i i := by
      funext x
      simp only [Finset.sum_apply, scalarHessian, laplacian]
    rw [heq]
    exact HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => (hparts i).2)

private theorem memLp_two_of_integrable_of_bounded {d : ℕ} {f : E d → ℂ}
    (hf : Integrable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) : MemLp f 2 := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  have hmeas : AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) volume :=
    (continuous_id.pow 2).comp_aestronglyMeasurable hf.aestronglyMeasurable.norm
  refine (hf.norm.const_mul C).mono' hmeas (Filter.Eventually.of_forall (fun x => ?_))
  rw [Real.norm_of_nonneg (sq_nonneg ‖f x‖), pow_two]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- A bounded continuous compact kernel convolved with L¹ belongs to L². -/
theorem memLp_two_scalarConvolution_of_compact {d : ℕ} {f g : E d → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) (hg : Integrable g) :
    MemLp (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) 2 := by
  obtain ⟨B, hB⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hcf.norm
  have hf₁ : Integrable f := hf.integrable_of_hasCompactSupport hcf
  refine memLp_two_of_integrable_of_bounded
    (hf₁.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg)
    (B * ∫ t, ‖g t‖) (fun x => ?_)
  rw [convolution_mul_swap]
  refine (norm_integral_le_of_norm_le (hg.norm.const_mul B)
    (Filter.Eventually.of_forall (fun t => ?_))).trans_eq (integral_const_mul _ _)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB ⟨x - t, rfl⟩) (norm_nonneg _)

private theorem ofReal_scalarConvolution {d : ℕ} (f g : E d → ℝ) (x : E d) :
    Complex.ofReal ((f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x) =
      (((fun y => Complex.ofReal (f y)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun y => Complex.ofReal (g y))) x) := by
  simp only [convolution_mul, ← Complex.ofReal_mul, integral_complex_ofReal]

private theorem fourier_hessian_convolution_symbol {d : ℕ}
    {cutoff : E d → ℝ} (hcutoff : ContDiff ℝ ∞ cutoff)
    (hcompact : HasCompactSupport cutoff) {g : E d → ℂ} (hg : Integrable g)
    (i j : Fin d) (ξ : E d) (hξ : ξ ≠ 0) :
    𝓕 ((fun y => Complex.ofReal (scalarHessian cutoff y i j))
        ⋆[ContinuousLinearMap.mul ℂ ℂ] g) ξ =
      (((ξ.ofLp i * ξ.ofLp j / ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        𝓕 ((fun y => Complex.ofReal (laplacian cutoff y))
          ⋆[ContinuousLinearMap.mul ℂ ℂ] g) ξ) := by
  obtain ⟨hLdiff, hLcomp⟩ := smooth_compact_laplacian hcutoff hcompact
  obtain ⟨hHdiff, hHcomp⟩ := smooth_compact_scalarHessian hcutoff hcompact i j
  have hL₁ : Integrable (fun y => Complex.ofReal (laplacian cutoff y)) :=
    Complex.ofRealCLM.integrable_comp (hLdiff.continuous.integrable_of_hasCompactSupport hLcomp)
  have hH₁ : Integrable (fun y => Complex.ofReal (scalarHessian cutoff y i j)) :=
    Complex.ofRealCLM.integrable_comp (hHdiff.continuous.integrable_of_hasCompactSupport hHcomp)
  rw [Real.fourier_mul_convolution_eq hH₁ hg, Real.fourier_mul_convolution_eq hL₁ hg,
    fourier_ofReal_scalarHessian hcutoff hcompact i j ξ, fourier_ofReal_laplacian hcutoff hcompact ξ]
  push_cast
  have hnorm : (‖ξ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hξ)
  field_simp [hnorm]

private theorem integral_sq_norm_eq_toLp_sq {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    {f : E d → 𝕜} (hf : MemLp f 2) :
    (∫ x, ‖f x‖ ^ 2) = ‖hf.toLp f‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := 𝕜) (hf.toLp f) (hf.toLp f))]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]

private theorem norm_secondRiesz_symbol_le {d : ℕ} (i j : Fin d) (ξ : E d) (hξ : ξ ≠ 0) :
    ‖((ξ.ofLp i * ξ.ofLp j / ‖ξ‖ ^ 2 : ℝ) : ℂ)‖ ≤ 1 := by
  have hi : |ξ.ofLp i| ≤ ‖ξ‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ i
  have hj : |ξ.ofLp j| ≤ ‖ξ‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ j
  have hden : 0 < ‖ξ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hξ) 2
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hden, abs_mul,
    div_le_iff₀ hden, one_mul, pow_two]
  exact mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)

/-- Plancherel and the coordinate Hessian symbol bound the ordinary convolution in (L^2).
The operator constant is the (L^1) norm of the cutoff's Laplacian. -/
theorem integral_sq_scalarHessian_convolution_le {d : ℕ} (hd : 0 < d)
    {cutoff g : E d → ℝ} (hcutoff : ContDiff ℝ ∞ cutoff)
    (hcompact : HasCompactSupport cutoff) (hg : Integrable g) (hg₂ : MemLp g 2) (i j : Fin d) :
    (∫ x, |((fun y => scalarHessian cutoff y i j) ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x| ^ 2) ≤
      (∫ x, |laplacian cutoff x|) ^ 2 * ∫ x, |g x| ^ 2 := by
  let L : E d → ℝ := laplacian cutoff
  let H : E d → ℝ := fun x => scalarHessian cutoff x i j
  let Lc : E d → ℂ := fun x => Complex.ofReal (L x)
  let Hc : E d → ℂ := fun x => Complex.ofReal (H x)
  let Gc : E d → ℂ := fun x => Complex.ofReal (g x)
  let v : E d → ℂ := Hc ⋆[ContinuousLinearMap.mul ℂ ℂ] Gc
  obtain ⟨hLdiff, hLcomp⟩ := smooth_compact_laplacian hcutoff hcompact
  obtain ⟨hHdiff, hHcomp⟩ := smooth_compact_scalarHessian hcutoff hcompact i j
  have hHc : Continuous Hc := Complex.continuous_ofReal.comp hHdiff.continuous
  have hHccomp : HasCompactSupport Hc := hHcomp.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hGc : Integrable Gc := Complex.ofRealCLM.integrable_comp hg
  have hGc₂ : MemLp Gc 2 := Complex.ofRealCLM.comp_memLp' hg₂
  have hLc₁ : Integrable Lc :=
    Complex.ofRealCLM.integrable_comp (hLdiff.continuous.integrable_of_hasCompactSupport hLcomp)
  have hHc₁ : Integrable Hc := hHc.integrable_of_hasCompactSupport hHccomp
  have hv₁ : Integrable v := hHc₁.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hGc
  have hv₂ : MemLp v 2 := memLp_two_scalarConvolution_of_compact hHc hHccomp hGc
  let M := ∫ x, ‖Lc x‖
  have hM : 0 ≤ M := integral_nonneg fun x => norm_nonneg (Lc x)
  let v₂ : Lp ℂ 2 (volume : Measure (E d)) := hv₂.toLp v
  let g₂ : Lp ℂ 2 (volume : Measure (E d)) := hGc₂.toLp Gc
  haveI : NeZero d := ⟨hd.ne'⟩
  have hne : ∀ᵐ ξ ∂(volume : Measure (E d)), ξ ≠ 0 := ae_iff.mpr (by simp)
  have hbound : ‖v₂‖ ≤ M * ‖g₂‖ := by
    rw [← Lp.norm_fourier_eq v₂, ← Lp.norm_fourier_eq g₂]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hne, fourier_toLp_two_ae_eq hv₁ hv₂, fourier_toLp_two_ae_eq hGc hGc₂]
      with ξ hξ hvξ hgξ
    change ‖(𝓕 (hv₂.toLp v) : Lp ℂ 2 (volume : Measure (E d))) ξ‖ ≤
      M * ‖(𝓕 (hGc₂.toLp Gc) : Lp ℂ 2 (volume : Measure (E d))) ξ‖
    rw [hvξ, hgξ]
    have hs : 𝓕 v ξ = (((ξ.ofLp i * ξ.ofLp j / ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        𝓕 (Lc ⋆[ContinuousLinearMap.mul ℂ ℂ] Gc) ξ) :=
      fourier_hessian_convolution_symbol hcutoff hcompact hGc i j ξ hξ
    rw [hs, Real.fourier_mul_convolution_eq hLc₁ hGc]
    simp only [norm_mul, ← mul_assoc]
    have hLξ : ‖𝓕 Lc ξ‖ ≤ M :=
      VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ (E d)) Lc ξ
    exact mul_le_mul_of_nonneg_right (by
      simpa only [one_mul] using mul_le_mul (norm_secondRiesz_symbol_le i j ξ hξ) hLξ
        (norm_nonneg _) zero_le_one) (norm_nonneg _)
  have hSquare := pow_le_pow_left₀ (norm_nonneg v₂) hbound 2
  rw [mul_pow] at hSquare
  change ‖hv₂.toLp v‖ ^ 2 ≤ M ^ 2 * ‖hGc₂.toLp Gc‖ ^ 2 at hSquare
  rw [← integral_sq_norm_eq_toLp_sq hv₂, ← integral_sq_norm_eq_toLp_sq hGc₂] at hSquare
  simpa only [M, Lc, L, Gc, v, Hc, H, ← ofReal_scalarConvolution,
    Complex.norm_real, Real.norm_eq_abs] using hSquare

end SupportingAnalysis
