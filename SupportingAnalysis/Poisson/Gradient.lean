module

public import SupportingAnalysis.Poisson.Potential

/-! Distributional derivatives of the compact Newtonian correction. -/

public section

open MeasureTheory Metric Filter Set InnerProductSpace
open scoped Convolution ContDiff ENNReal Topology

set_option autoImplicit false

namespace SupportingAnalysis

variable {d : ℕ}

/-- Differentiation of the potential average, computed on the smooth density and then moved to
the locally integrable weak derivative of the kernel. -/
theorem fderiv_radialAverage_apply (Γ DΓ : E d → ℝ) (hΓ : LocallyIntegrable Γ volume)
    (i : Fin d) (hWeak : ∀ φ : E d → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ y, Γ y * fderiv ℝ φ y (axis i)) =
        -∫ y, DΓ y * φ y)
    (k : RadialProbabilityDensity d) {r : ℝ} (hr : 0 < r)
    (x : E d) :
    fderiv ℝ (k.scaled r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] Γ) x (axis i) =
      (k.scaled r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] DΓ) x := by
  let ρ := k.scaled r
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hρ : ContDiff ℝ 1 ρ := (k.scaled_smooth r).of_le (by simp)
  have hρc : HasCompactSupport ρ := k.scaled_hasCompactSupport hr
  have hflip : ρ ⋆[L] Γ = Γ ⋆[L.flip] ρ :=
    (convolution_flip (f := ρ) (g := Γ) L).symm
  have hFlip : ρ ⋆[L] DΓ = DΓ ⋆[L.flip] ρ :=
    (convolution_flip (f := ρ) (g := DΓ) L).symm
  change fderiv ℝ (ρ ⋆[L] Γ) x (axis i) = (ρ ⋆[L] DΓ) x
  rw [hflip, hFlip, (hρc.hasFDerivAt_convolution_right L.flip hΓ hρ x).fderiv,
    convolution_precompR_apply L.flip hΓ (hρc.fderiv ℝ)
      (hρ.continuous_fderiv one_ne_zero)]
  let φ : E d → ℝ := fun y => ρ (x - y)
  have hφ : ContDiff ℝ 1 φ := hρ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hφd (y : E d) : fderiv ℝ φ y (axis i) = -fderiv ℝ ρ (x - y) (axis i) := by
    have hsub : HasFDerivAt (fun z : E d => x - z)
        (-ContinuousLinearMap.id ℝ (E d)) y := by
      exact (hasFDerivAt_id y).const_sub x
    have h : HasFDerivAt φ
        (fderiv ℝ ρ (x - y) ∘L (-ContinuousLinearMap.id ℝ (E d))) y :=
      (hρ.differentiable one_ne_zero (x - y)).hasFDerivAt.comp y hsub
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply, map_neg]
  have hw := hWeak φ hφ hφc
  simp_rw [hφd, mul_neg, integral_neg] at hw
  simp only [convolution_def, L, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]
  simpa only [φ, neg_inj, mul_comm] using hw


theorem radialAverage_component (G : E d → E d) (hG : LocallyIntegrable G volume)
    (k : RadialProbabilityDensity d) {r : ℝ} (hr : 0 < r) (x : E d) (i : Fin d) :
    ((k.scaled r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) x) i =
      (k.scaled r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] fun y => G y i) x := by
  let L : E d →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin d => ℝ) i
  have hInt := integrable_potentialCorrection_integrand G hG k hr x
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
  calc
    _ = L (∫ y, k.scaled r y • G (x - y)) := rfl
    _ = ∫ y, L (k.scaled r y • G (x - y)) := (L.integral_comp_comm hInt).symm
    _ = _ := by simp only [map_smul, L, PiLp.proj_apply]

/-- Differentiation preserves the cancellation off the closed dilation ball. -/
theorem potentialCorrectionGradient_eq_zero_off_closedBall (Γ : E d → ℝ) (G : E d → E d)
    (hΓ : LocallyIntegrable Γ volume) (hG : LocallyIntegrable G volume)
    (hClassical : ∀ x ≠ 0, ∀ i : Fin d, fderiv ℝ Γ x (axis i) = G x i)
    (hWeak : ∀ (i : Fin d) (φ : E d → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ y, Γ y * fderiv ℝ φ y (axis i)) = -∫ y, G y i * φ y)
    (k : RadialProbabilityDensity d) {r : ℝ} (hr : 0 < r)
    (hzero : ∀ x ∉ closedBall (0 : E d) r, potentialCorrection Γ k r x = 0)
    (x : E d) (hx : x ∉ closedBall 0 r) :
    potentialCorrection G k r x = 0 := by
  have hLocal : Γ =ᶠ[𝓝 x] (k.scaled r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] Γ) := by
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
    exact sub_eq_zero.mp (hzero y hy)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (mem_closedBall_self hr.le)
  ext i
  change G x i - ((k.scaled r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) x) i = 0
  rw [radialAverage_component G hG k hr x i, ← hClassical x hx0 i, hLocal.fderiv_eq,
    fderiv_radialAverage_apply Γ (fun y => G y i) hΓ i (hWeak i) k hr x, sub_self]

/-- The correction of the fundamental gradient is the weak gradient of the correction
of the fundamental solution. -/
theorem potentialCorrection_testDerivative (Γ : E d → ℝ) (G : E d → E d)
    (hΓ : LocallyIntegrable Γ volume) (hG : LocallyIntegrable G volume)
    (hWeak : ∀ (i : Fin d) (φ : E d → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ y, Γ y * fderiv ℝ φ y (axis i)) = -∫ y, G y i * φ y)
    (k : RadialProbabilityDensity d) {r : ℝ} (hr : 0 < r)
    (i : Fin d) (φ : E d → ℝ) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ y, potentialCorrection Γ k r y * fderiv ℝ φ y (axis i)) =
      -∫ y, (potentialCorrection G k r y) i * φ y := by
  let K := k.scaled r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] Γ
  let J := k.scaled r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y => G y i)
  let D := fun y => fderiv ℝ φ y (axis i)
  let L : E d →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin d => ℝ) i
  have hGi : LocallyIntegrable (fun y => G y i) volume := by
    intro y
    exact L.integrableAtFilter_comp (hG y)
  have hKC : ContDiff ℝ 1 K :=
    (k.scaled_hasCompactSupport hr).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      ((k.scaled_smooth r).of_le (by simp)) hΓ
  have hJC : Continuous J :=
    (k.scaled_hasCompactSupport hr).continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (k.scaled_smooth r).continuous hGi
  have hDC : Continuous D := (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDc : HasCompactSupport D := hφc.fderiv_apply ℝ (axis i)
  have hΓD : Integrable (fun y => Γ y * D y) := by
    simpa only [smul_eq_mul] using hΓ.integrable_smul_right_of_hasCompactSupport hDC hDc
  have hKD : Integrable (fun y => K y * D y) :=
    (hKC.continuous.mul hDC).integrable_of_hasCompactSupport hDc.mul_left
  have hGφ : Integrable (fun y => G y i * φ y) := by
    simpa only [smul_eq_mul] using hGi.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  have hJφ : Integrable (fun y => J y * φ y) :=
    (hJC.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have hfderiv (x : E d) : fderiv ℝ K x (axis i) = J x :=
    fderiv_radialAverage_apply Γ (fun y => G y i) hΓ i (hWeak i) k hr x
  have hDerivInt : Integrable (fun y => fderiv ℝ K y (axis i) * φ y) := by
    simpa only [hfderiv] using hJφ
  have hKWeak : (∫ y, K y * D y) = -∫ y, J y * φ y := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      hDerivInt hKD ((hKC.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left)
      (fun x _ => hKC.differentiable one_ne_zero x) (fun x _ => hφ.differentiable one_ne_zero x)
    simpa only [hfderiv] using h
  have hcomp (y : E d) : (potentialCorrection G k r y) i = G y i - J y := by
    change G y i - ((k.scaled r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) y) i = G y i - J y
    rw [radialAverage_component G hG k hr y i]
  simp_rw [hcomp, potentialCorrection, sub_mul]
  change (∫ y, Γ y * D y - K y * D y) = -∫ y, G y i * φ y - J y * φ y
  rw [integral_sub hΓD hKD, integral_sub hGφ hJφ, hKWeak]
  change (∫ y, Γ y * fderiv ℝ φ y (axis i)) - (-∫ y, J y * φ y) =
    -((∫ y, G y i * φ y) - ∫ y, J y * φ y)
  rw [hWeak i φ hφ hφc]
  abel


/-- Differentiating the affine dilation law removes its additive constant. -/
theorem fundamentalGradient_dilate (Γ : E d → ℝ) (G : E d → E d)
    (hDiff : ∀ x ≠ 0, DifferentiableAt ℝ Γ x)
    (hClassical : ∀ x ≠ 0, ∀ i : Fin d, fderiv ℝ Γ x (axis i) = G x i)
    (s : ℤ) (c : ℝ) {r : ℝ} (hr : 0 < r)
    (hScale : ∀ x ≠ 0, Γ (r • x) = r ^ s * Γ x + c) (x : E d) (hx : x ≠ 0) :
    G (r • x) = r ^ (s - 1) • G x := by
  let L : E d →L[ℝ] E d := ContinuousLinearMap.lsmul ℝ ℝ r
  have hrx : r • x ≠ 0 := smul_ne_zero hr.ne' hx
  have hLeft : HasFDerivAt (fun y => Γ (r • y)) (fderiv ℝ Γ (r • x) ∘L L) x :=
    (hDiff _ hrx).hasFDerivAt.comp x L.hasFDerivAt
  have hRight : HasFDerivAt (fun y => r ^ s * Γ y + c) (r ^ s • fderiv ℝ Γ x) x :=
    ((hDiff x hx).hasFDerivAt.const_smul (r ^ s)).add_const c
  have hEq : (fun y => Γ (r • y)) =ᶠ[𝓝 x] (fun y => r ^ s * Γ y + c) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds
      (show x ∈ ({0}ᶜ : Set (E d)) from hx)] with y hy
    exact hScale y hy
  have hCLM := hLeft.fderiv.symm.trans (hEq.fderiv_eq.trans hRight.fderiv)
  ext i
  change G (r • x) i = r ^ (s - 1) * G x i
  have hCoord := congrArg (fun D : E d →L[ℝ] ℝ => D (axis i)) hCLM
  change fderiv ℝ Γ (r • x) (r • axis i) = r ^ s • fderiv ℝ Γ x (axis i) at hCoord
  simp only [map_smul, hClassical _ hrx i, hClassical _ hx i, smul_eq_mul] at hCoord
  rw [zpow_sub₀ hr.ne', zpow_one, div_mul_eq_mul_div]
  exact (eq_div_iff hr.ne').2 (by simpa only [mul_comm (G (r • x) i) r] using hCoord)

/-- Compact support and both L¹ estimates, with the displayed distributional gradient. -/
theorem compactPotential_with_gradient (Γ : E d → ℝ) (G : E d → E d) (hd : 0 < d)
    (hΓI : LocallyIntegrable Γ volume) (hGI : LocallyIntegrable G volume)
    (hΓ : HarmonicOnNhd Γ ({0}ᶜ : Set (E d)))
    (hClassical : ∀ x ≠ 0, ∀ i : Fin d, fderiv ℝ Γ x (axis i) = G x i)
    (hWeak : ∀ (i : Fin d) (φ : E d → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ y, Γ y * fderiv ℝ φ y (axis i)) = -∫ y, G y i * φ y)
    (hScale : ∀ r > (0 : ℝ), ∃ c : ℝ, ∀ x ≠ 0,
      Γ (r • x) = r ^ (2 - (d : ℤ)) * Γ x + c)
    (hMean : ∀ (u : E d → ℝ) (x : E d) (r : ℝ) (ρ : E d → ℝ),
      0 < r → HarmonicOnNhd u (closedBall x r) →
      Continuous ρ → (∃ profile : ℝ → ℝ, ∀ y, ρ y = profile ‖y‖) →
      (∀ y, 0 ≤ ρ y) → Function.support ρ ⊆ ball 0 r →
      (∫ y, ρ y) = 1 → (∫ y, ρ y * u (x - y)) = u x)
    (k : RadialProbabilityDensity d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r > (0 : ℝ),
      tsupport (potentialCorrection Γ k r) ⊆ closedBall 0 r ∧
      tsupport (potentialCorrection G k r) ⊆ closedBall 0 r ∧
      Integrable (potentialCorrection Γ k r) ∧ Integrable (potentialCorrection G k r) ∧
      (∫ x, ‖potentialCorrection Γ k r x‖) ≤ r ^ 2 * C ∧
      (∫ x, ‖potentialCorrection G k r x‖) ≤ r * C ∧
      ∀ (i : Fin d) (φ : E d → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
        (∫ y, potentialCorrection Γ k r y * fderiv ℝ φ y (axis i)) =
          -∫ y, (potentialCorrection G k r y) i * φ y := by
  obtain ⟨C₁, hC₁, hScalar⟩ := compactPotential_scalar Γ hd hΓI hΓ hScale hMean k
  let C₂ := ∫ x, ‖potentialCorrection G k 1 x‖
  refine ⟨max C₁ C₂, hC₁.trans (le_max_left _ _), fun r hr => ?_⟩
  obtain ⟨hSΓ, hIntΓ, hBoundΓ⟩ := hScalar r hr
  have hZeroΓ := potentialCorrection_eq_zero_off_closedBall Γ hΓ hMean k hr
  have hZeroG := potentialCorrectionGradient_eq_zero_off_closedBall Γ G
    hΓI hGI hClassical hWeak k hr hZeroΓ
  have hSG : tsupport (potentialCorrection G k r) ⊆ closedBall 0 r :=
    closure_minimal (Function.support_subset_iff'.mpr hZeroG) isClosed_closedBall
  have hIntG := integrable_potentialCorrection_of_zero_off_closedBall G hGI k hr hZeroG
  have hDiff (x : E d) (hx : x ≠ 0) : DifferentiableAt ℝ Γ x :=
    (hΓ x hx).1.differentiableAt (by norm_num)
  obtain ⟨c, hDilation⟩ := hScale r hr
  have hNormG := integral_norm_potentialCorrection_dilate G hGI k hd
    (2 - (d : ℤ) - 1) 0 hr (fun x hx => by
      rw [add_zero]
      exact fundamentalGradient_dilate Γ G hDiff hClassical (2 - (d : ℤ)) c hr hDilation x hx)
  have hExp : (d : ℤ) + (2 - (d : ℤ) - 1) = 1 := by omega
  rw [hExp, zpow_one] at hNormG
  refine ⟨hSΓ, hSG, hIntΓ, hIntG, ?_, ?_, ?_⟩
  · rw [hBoundΓ]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg r)
  · rw [hNormG]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hr.le
  · exact potentialCorrection_testDerivative Γ G hΓI hGI hWeak k hr

end SupportingAnalysis
