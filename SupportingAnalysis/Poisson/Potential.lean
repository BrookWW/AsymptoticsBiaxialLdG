module

public import SupportingAnalysis.Euclidean

/-! Compact Newtonian corrections obtained by radial averaging. -/

@[expose] public section

open MeasureTheory Metric Filter Set InnerProductSpace
open scoped Convolution ContDiff ENNReal Topology

set_option autoImplicit false

namespace SupportingAnalysis

/-- A smooth radial probability density supported in the unit ball. -/
structure RadialProbabilityDensity (d : ℕ) where
  density : E d → ℝ
  smooth : ContDiff ℝ ∞ density
  radial : ∃ profile : ℝ → ℝ, ∀ x, density x = profile ‖x‖
  nonnegative : ∀ x, 0 ≤ density x
  support_subset : Function.support density ⊆ ball 0 1
  mass : (∫ x, density x) = 1

namespace RadialProbabilityDensity

variable {d : ℕ}

/-- The mass-preserving dilation of the density to radius `r`. -/
noncomputable def scaled (k : RadialProbabilityDensity d) (r : ℝ) (x : E d) : ℝ :=
  (r ^ d)⁻¹ * k.density (r⁻¹ • x)

@[simp] theorem scaled_one (k : RadialProbabilityDensity d) : k.scaled 1 = k.density := by
  funext x
  simp [scaled]

theorem scaled_smooth (k : RadialProbabilityDensity d) (r : ℝ) :
    ContDiff ℝ ∞ (k.scaled r) := by
  have hDil : ContDiff ℝ ∞ (fun x : E d => r⁻¹ • x) :=
    ((ContinuousLinearMap.lsmul ℝ ℝ r⁻¹ : E d →L[ℝ] E d)).contDiff
  exact contDiff_const.mul (k.smooth.comp hDil)

theorem scaled_nonnegative (k : RadialProbabilityDensity d) (r : ℝ) (hr : 0 < r) (x : E d) :
    0 ≤ k.scaled r x :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _)) (k.nonnegative _)

theorem scaled_radial (k : RadialProbabilityDensity d) {r : ℝ} (hr : 0 < r) :
    ∃ profile : ℝ → ℝ, ∀ x, k.scaled r x = profile ‖x‖ := by
  obtain ⟨profile, hprofile⟩ := k.radial
  refine ⟨fun t => (r ^ d)⁻¹ * profile (r⁻¹ * t), fun x => ?_⟩
  rw [scaled, hprofile, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]

theorem scaled_support_subset (k : RadialProbabilityDensity d) {r : ℝ} (hr : 0 < r) :
    Function.support (k.scaled r) ⊆ ball 0 r := by
  intro x hx
  have hp : r⁻¹ • x ∈ Function.support k.density := by
    apply Function.mem_support.mpr
    intro h
    exact (Function.mem_support.mp hx) (by simp [scaled, h])
  have hnorm : ‖r⁻¹ • x‖ < 1 := by
    simpa only [mem_ball, dist_zero_right] using k.support_subset hp
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), inv_mul_eq_div,
    div_lt_iff₀ hr, one_mul] at hnorm
  simpa only [mem_ball, dist_zero_right] using hnorm

theorem scaled_hasCompactSupport (k : RadialProbabilityDensity d) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (k.scaled r) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E d) r)
  exact (k.scaled_support_subset hr).trans ball_subset_closedBall

theorem scaled_integrable (k : RadialProbabilityDensity d) {r : ℝ} (hr : 0 < r) :
    Integrable (k.scaled r) :=
  (k.scaled_smooth r).continuous.integrable_of_hasCompactSupport (k.scaled_hasCompactSupport hr)

theorem scaled_mass (k : RadialProbabilityDensity d) {r : ℝ} (hr : 0 < r) :
    (∫ x, k.scaled r x) = 1 := by
  simp only [scaled, integral_const_mul]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume k.density hr.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, k.mass, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ hr.ne')

end RadialProbabilityDensity

section Correction

variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The difference between a function and its convolution with the scaled radial density. -/
noncomputable def potentialCorrection (f : E d → V) (k : RadialProbabilityDensity d)
    (r : ℝ) (x : E d) : V :=
  f x - (k.scaled r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x

theorem integrable_potentialCorrection_integrand (f : E d → V)
    (hf : LocallyIntegrable f volume) (k : RadialProbabilityDensity d)
    {r : ℝ} (hr : 0 < r) (x : E d) :
    Integrable (fun z => k.scaled r z • f (x - z)) :=
  ((k.scaled_hasCompactSupport hr).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (k.scaled_smooth r).continuous hf x).integrable

theorem potentialCorrection_eq_restricted (f : E d → V) (k : RadialProbabilityDensity d)
    {r : ℝ} (hr : 0 < r) (x : E d) :
    potentialCorrection f k r x = f x - ∫ z in ball 0 r, k.scaled r z • f (x - z) := by
  unfold potentialCorrection
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
  congr 1
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro z hz
  have hk : k.scaled r z = 0 :=
    Function.notMem_support.mp (mt (fun h => k.scaled_support_subset hr h) hz)
  simp only [hk, zero_smul]

theorem integrable_potentialCorrection_of_zero_off_closedBall (f : E d → V)
    (hf : LocallyIntegrable f volume) (k : RadialProbabilityDensity d)
    {r : ℝ} (hr : 0 < r)
    (hzero : ∀ x ∉ closedBall (0 : E d) r, potentialCorrection f k r x = 0) :
    Integrable (potentialCorrection f k r) := by
  apply (integrableOn_iff_integrable_of_support_subset
    (s := closedBall (0 : E d) r) (Function.support_subset_iff'.mpr hzero)).mp
  have hcont : Continuous (k.scaled r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) :=
    (k.scaled_hasCompactSupport hr).continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (k.scaled_smooth r).continuous hf
  exact (hf.integrableOn_isCompact (isCompact_closedBall _ _)).sub
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _))

private theorem scaled_convolution_dilate_eq (f : E d → V) (k : RadialProbabilityDensity d)
    {r : ℝ} (hr : 0 < r) (x : E d) :
    (k.scaled r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) (r • x) =
      ∫ z, k.density z • f (r • (x - z)) := by
  let F : E d → V := fun z => k.density z • f (r • (x - z))
  have hF (z : E d) : F (r⁻¹ • z) = k.density (r⁻¹ • z) • f (r • x - z) := by
    simp [F, smul_sub, smul_smul, mul_inv_cancel₀ hr.ne']
  calc
    _ = (r ^ d)⁻¹ • ∫ z, F (r⁻¹ • z) := by
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply, RadialProbabilityDensity.scaled,
        hF, mul_smul, integral_smul]
    _ = ∫ z, F z := by
      rw [Measure.integral_comp_inv_smul_of_nonneg volume F hr.le]
      simp only [finrank_euclideanSpace, Fintype.card_fin, smul_smul, inv_mul_cancel₀
        (pow_ne_zero _ hr.ne'), one_smul]

variable [CompleteSpace V]

/-- Affine scaling of a kernel induces homogeneous scaling of its correction.
The additive term cancels against the mass of the density. -/
theorem potentialCorrection_dilate_apply (f : E d → V) (hf : LocallyIntegrable f volume)
    (k : RadialProbabilityDensity d) (hd : 0 < d) (s : ℤ) (c : V)
    {r : ℝ} (hr : 0 < r)
    (hscale : ∀ x ≠ 0, f (r • x) = r ^ s • f x + c) {x : E d} (hx : x ≠ 0) :
    potentialCorrection f k r (r • x) = r ^ s • potentialCorrection f k 1 x := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hcov : (∫ z, k.density z • f (r • (x - z))) =
      r ^ s • (∫ z, k.density z • f (x - z)) + c := by
    have hfI : Integrable (fun z => k.density z • f (x - z)) := by
      simpa only [k.scaled_one] using
        integrable_potentialCorrection_integrand f hf k one_pos x
    have hkI : Integrable k.density := by
      simpa only [k.scaled_one] using k.scaled_integrable one_pos
    calc
      _ = ∫ z, r ^ s • (k.density z • f (x - z)) + k.density z • c := by
        apply integral_congr_ae
        filter_upwards [(volume : Measure (E d)).ae_ne x] with z hz
        rw [hscale _ (sub_ne_zero.mpr hz.symm), smul_add, smul_comm (k.density z) (r ^ s)]
      _ = _ := by
        have hI : Integrable (fun z => r ^ s • (k.density z • f (x - z))) := hfI.smul _
        rw [integral_add hI (hkI.smul_const c), integral_smul, integral_smul_const,
          k.mass, one_smul]
  simp only [potentialCorrection, k.scaled_one]
  rw [scaled_convolution_dilate_eq f k hr x, hcov, hscale x hx]
  simp only [smul_sub, convolution_def, ContinuousLinearMap.lsmul_apply]
  abel

/-- Exact L¹ scaling, including the cancellation of the additive logarithmic constant. -/
theorem integral_norm_potentialCorrection_dilate (f : E d → V) (hf : LocallyIntegrable f volume)
    (k : RadialProbabilityDensity d) (hd : 0 < d) (s : ℤ) (c : V)
    {r : ℝ} (hr : 0 < r)
    (hscale : ∀ x ≠ 0, f (r • x) = r ^ s • f x + c) :
    (∫ x, ‖potentialCorrection f k r x‖) =
      r ^ ((d : ℤ) + s) * ∫ x, ‖potentialCorrection f k 1 x‖ := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hscale_norm : (∫ x, ‖potentialCorrection f k r (r • x)‖) =
      r ^ s * ∫ x, ‖potentialCorrection f k 1 x‖ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(volume : Measure (E d)).ae_ne 0] with x hx
    rw [potentialCorrection_dilate_apply f hf k hd s c hr hscale hx, norm_smul,
      Real.norm_of_nonneg (zpow_pos hr s).le]
  have hchange := Measure.integral_comp_smul_of_nonneg (volume : Measure (E d))
    (fun x => ‖potentialCorrection f k r x‖) r (hR := hr.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hchange
  calc
    _ = r ^ d * ∫ x, ‖potentialCorrection f k r (r • x)‖ := by
      rw [hchange, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]
    _ = _ := by
      rw [hscale_norm, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ hr.ne']

end Correction

section HarmonicSupport

variable {d : ℕ}

/-- Radial mean value gives pointwise vanishing of the compact correction outside the closed ball. -/
theorem potentialCorrection_eq_zero_off_closedBall (Γ : E d → ℝ)
    (hΓ : HarmonicOnNhd Γ ({0}ᶜ : Set (E d)))
    (hMean : ∀ (u : E d → ℝ) (x : E d) (r : ℝ) (ρ : E d → ℝ),
      0 < r → HarmonicOnNhd u (closedBall x r) →
      Continuous ρ → (∃ profile : ℝ → ℝ, ∀ y, ρ y = profile ‖y‖) →
      (∀ y, 0 ≤ ρ y) → Function.support ρ ⊆ ball 0 r →
      (∫ y, ρ y) = 1 → (∫ y, ρ y * u (x - y)) = u x)
    (k : RadialProbabilityDensity d) {r : ℝ} (hr : 0 < r)
    (x : E d) (hx : x ∉ closedBall 0 r) :
    potentialCorrection Γ k r x = 0 := by
  have hsub : closedBall x r ⊆ ({0}ᶜ : Set (E d)) := by
    intro y hy
    by_contra h
    simp only [mem_compl_iff, not_not, mem_singleton_iff] at h
    subst y
    apply hx
    simpa only [mem_closedBall, dist_comm] using hy
  have hm := hMean Γ x r (k.scaled r) hr (hΓ.mono hsub)
    (k.scaled_smooth r).continuous (k.scaled_radial hr) (k.scaled_nonnegative r hr)
    (k.scaled_support_subset hr) (k.scaled_mass hr)
  simp only [potentialCorrection, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    hm, sub_self]


/-- The scalar correction is integrable with closed-ball support and scales exactly as `r²`. -/
theorem compactPotential_scalar (Γ : E d → ℝ) (hd : 0 < d)
    (hΓI : LocallyIntegrable Γ volume) (hΓ : HarmonicOnNhd Γ ({0}ᶜ : Set (E d)))
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
      Integrable (potentialCorrection Γ k r) ∧
      (∫ x, ‖potentialCorrection Γ k r x‖) = r ^ 2 * C := by
  refine ⟨∫ x, ‖potentialCorrection Γ k 1 x‖, integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro r hr
  have hzero := potentialCorrection_eq_zero_off_closedBall Γ hΓ hMean k hr
  refine ⟨closure_minimal (Function.support_subset_iff'.mpr hzero) isClosed_closedBall,
    integrable_potentialCorrection_of_zero_off_closedBall Γ hΓI k hr hzero, ?_⟩
  obtain ⟨c, hs⟩ := hScale r hr
  have hi := integral_norm_potentialCorrection_dilate Γ hΓI k hd (2 - (d : ℤ)) c hr
    (fun x hx => by simpa only [smul_eq_mul] using hs x hx)
  have hExp : (d : ℤ) + (2 - (d : ℤ)) = 2 := by omega
  rwa [hExp, zpow_ofNat] at hi

end HarmonicSupport

end SupportingAnalysis
