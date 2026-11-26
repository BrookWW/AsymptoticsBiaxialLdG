module

public import SupportingAnalysis.Poisson.Potential
public import SupportingAnalysis.Basics

/-! The signed Laplacian of the compact Newtonian correction. -/

public section

open MeasureTheory Metric Set
open scoped BigOperators Convolution ContDiff Topology

set_option autoImplicit false

namespace SupportingAnalysis

variable {d : ℕ}

private theorem contDiff_partial {f : E d → ℝ} (hf : ContDiff ℝ ∞ f) (v : E d) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x v) :=
  (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp (hf.fderiv_right (by simp))

theorem convolution_fderiv_right_apply (Γ : E d → ℝ)
    (hΓ : LocallyIntegrable Γ volume) {ρ : E d → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (x v : E d) :
    fderiv ℝ (Γ ⋆[ContinuousLinearMap.mul ℝ ℝ] ρ) x v =
      (Γ ⋆[ContinuousLinearMap.mul ℝ ℝ] fun y => fderiv ℝ ρ y v) x := by
  rw [(hρc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hΓ
    (hρ.of_le (by simp)) x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hΓ (hρc.fderiv ℝ)
    (hρ.continuous_fderiv (by simp)) x v

private theorem integrable_mul_reflected_of_compact (Γ : E d → ℝ) (hΓ : LocallyIntegrable Γ volume)
    {f : E d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (x : E d) :
    Integrable (fun y => Γ y * f (x - y)) := by
  have hC : Continuous (fun y => f (x - y)) := by fun_prop
  simpa only [smul_eq_mul] using hΓ.integrable_smul_right_of_hasCompactSupport
    hC (hfc.comp_homeomorph (Homeomorph.subLeft x))

theorem laplacian_convolution (Γ : E d → ℝ) (hΓ : LocallyIntegrable Γ volume)
    {ρ : E d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (x : E d) :
    laplacian (Γ ⋆[ContinuousLinearMap.mul ℝ ℝ] ρ) x =
      ∫ y, Γ y * laplacian ρ (x - y) := by
  classical
  unfold laplacian
  have hInt (i : Fin d) : Integrable (fun y =>
      Γ y * fderiv ℝ (fun z => fderiv ℝ ρ z (axis i)) (x - y) (axis i)) :=
    integrable_mul_reflected_of_compact Γ hΓ
      (contDiff_partial (contDiff_partial hρ (axis i)) (axis i)).continuous
      ((hρc.fderiv_apply ℝ (axis i)).fderiv_apply ℝ (axis i)) x
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hInt i)]
  apply Finset.sum_congr rfl
  intro i _
  have hFirst :
      (fun y => fderiv ℝ (Γ ⋆[ContinuousLinearMap.mul ℝ ℝ] ρ) y (axis i)) =
        Γ ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun y => fderiv ℝ ρ y (axis i)) :=
    funext (fun y => convolution_fderiv_right_apply Γ hΓ hρ hρc y (axis i))
  rw [hFirst, convolution_fderiv_right_apply Γ hΓ (contDiff_partial hρ (axis i))
    (hρc.fderiv_apply ℝ (axis i)), convolution_mul]

private theorem fderiv_reflect {f : E d → ℝ} (hf : ContDiff ℝ ∞ f) (x y v : E d) :
    fderiv ℝ (fun z => f (x - z)) y v = -(fderiv ℝ f (x - y) v) := by
  have h : HasFDerivAt (fun z => f (x - z))
      (fderiv ℝ f (x - y) ∘L (-ContinuousLinearMap.id ℝ (E d))) y :=
    (hf.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub x)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply, map_neg]

theorem laplacian_reflect {f : E d → ℝ} (hf : ContDiff ℝ ∞ f) (x y : E d) :
    laplacian (fun z => f (x - z)) y = laplacian f (x - y) := by
  classical
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i _
  have hfirst :
      (fun z => fderiv ℝ (fun t => f (x - t)) z (axis i)) =
        -fun z => fderiv ℝ f (x - z) (axis i) :=
    funext (fun z => fderiv_reflect hf x z (axis i))
  rw [hfirst, fderiv_neg, neg_apply]
  rw [fderiv_reflect (contDiff_partial hf (axis i)) x y (axis i), neg_neg]

private theorem integral_mul_fderiv_of_contDiff_compact {f g : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (v : E d) :
    (∫ x, f x * fderiv ℝ g x v) = -∫ x, fderiv ℝ f x v * g x := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact ((contDiff_partial hf v).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      hgc.mul_left
  · exact (hf.continuous.mul (contDiff_partial hg v).continuous).integrable_of_hasCompactSupport
      (hgc.fderiv_apply ℝ v).mul_left
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  · intro x _
    exact hf.differentiable (by simp) x
  · intro x _
    exact hg.differentiable (by simp) x

theorem integral_mul_laplacian_comm {f g : E d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ x, f x * laplacian g x) = ∫ x, laplacian f x * g x := by
  classical
  unfold laplacian
  have hleft (i : Fin d) : Integrable (fun x =>
      f x * fderiv ℝ (fun y => fderiv ℝ g y (axis i)) x (axis i)) :=
    (hf.continuous.mul
      (contDiff_partial (contDiff_partial hg (axis i)) (axis i)).continuous).integrable_of_hasCompactSupport
      ((hgc.fderiv_apply ℝ (axis i)).fderiv_apply ℝ (axis i)).mul_left
  have hright (i : Fin d) : Integrable (fun x =>
      fderiv ℝ (fun y => fderiv ℝ f y (axis i)) x (axis i) * g x) :=
    ((contDiff_partial (contDiff_partial hf (axis i)) (axis i)).continuous.mul
      hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hleft i), integral_finsetSum _ (fun i _ => hright i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_mul_fderiv_of_contDiff_compact hf (contDiff_partial hg (axis i))
    (hgc.fderiv_apply ℝ (axis i)) (axis i),
    integral_mul_fderiv_of_contDiff_compact (contDiff_partial hf (axis i)) hg hgc (axis i), neg_neg]

/-- Distributional pairing with the positive-signed coordinate Laplacian. -/
theorem potentialCorrection_laplacianPairing (Γ : E d → ℝ) (hΓ : LocallyIntegrable Γ volume)
    (hFundamental : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, Γ x * laplacian φ x) = φ 0)
    (k : RadialProbabilityDensity d) {r : ℝ} (hr : 0 < r)
    (φ : E d → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, potentialCorrection Γ k r x * laplacian φ x) = φ 0 - ∫ x, k.scaled r x * φ x := by
  let ρ := k.scaled r
  let K := Γ ⋆[ContinuousLinearMap.mul ℝ ℝ] ρ
  have hρ : ContDiff ℝ ∞ ρ := k.scaled_smooth r
  have hρc : HasCompactSupport ρ := k.scaled_hasCompactSupport hr
  have hK : ContDiff ℝ ∞ K := hρc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hΓ hρ
  have hK_ρ (x : E d) : laplacian K x = ρ x := by
    rw [laplacian_convolution Γ hΓ hρ hρc x]
    have hΦ : ContDiff ℝ ∞ (fun z => ρ (x - z)) := by fun_prop
    have ht : (∫ y, Γ y * laplacian (fun z => ρ (x - z)) y) = ρ (x - 0) :=
      hFundamental _ hΦ (hρc.comp_homeomorph (Homeomorph.subLeft x))
    simp only [laplacian_reflect hρ, sub_zero] at ht
    exact ht
  have hCorrection (x : E d) : potentialCorrection Γ k r x = Γ x - K x := by
    unfold potentialCorrection K
    rw [convolution_lsmul_swap, convolution_mul]
    exact congrArg (fun c : ℝ => Γ x - c) (integral_congr_ae
      (Filter.Eventually.of_forall fun y => by simp only [ρ, smul_eq_mul, mul_comm]))
  have hΔcont : Continuous (laplacian φ) := by
    unfold laplacian
    exact continuous_finsetSum Finset.univ (fun i _ =>
      (contDiff_partial (contDiff_partial hφ (axis i)) (axis i)).continuous)
  have hΔsupport : HasCompactSupport (laplacian φ) := by
    unfold laplacian
    let g : Fin d → E d → ℝ := fun i x =>
      fderiv ℝ (fun y => fderiv ℝ φ y (axis i)) x (axis i)
    change HasCompactSupport (fun x => ∑ i, g i x)
    have heq : (∑ i, g i) = (fun x => ∑ i, g i x) := by
      funext x
      rw [Finset.sum_apply]
    rw [← heq]
    exact HasCompactSupport.finset_sum (fun i _ =>
      (hφc.fderiv_apply ℝ (axis i)).fderiv_apply ℝ (axis i))
  have hLeft : Integrable (fun x => Γ x * laplacian φ x) := by
    simpa only [smul_eq_mul] using hΓ.integrable_smul_right_of_hasCompactSupport hΔcont hΔsupport
  have hRight : Integrable (fun x => K x * laplacian φ x) :=
    (hK.continuous.mul hΔcont).integrable_of_hasCompactSupport hΔsupport.mul_left
  simp_rw [hCorrection, sub_mul]
  rw [integral_sub hLeft hRight, hFundamental _ hφ hφc, integral_mul_laplacian_comm hK hφ hφc]
  simp only [hK_ρ, ρ]

end SupportingAnalysis
