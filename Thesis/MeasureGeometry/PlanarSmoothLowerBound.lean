module

public import Thesis.MeasureGeometry.PlanarProjectedLevels
import Thesis.StressEnergy

/-! The logarithmic planar estimate for smooth tensor maps. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

/-- Smooth planar Landau--de Gennes density, with Frobenius derivative
columns and the manuscript's potential normalization. -/
def planarSmoothEnergyDensity (a : BulkCoefficients) (ε : ℝ) (Q : Plane → S0) (x : Plane) : ℝ :=
  planarSmoothDirichletDensity Q x + bulkPotential a (Q x) / ε ^ 2

/-- Smooth planar Landau--de Gennes energy on the centered disk. -/
def planarSmoothEnergy (a : BulkCoefficients) (ε : ℝ) (Q : Plane → S0) (R : ℝ) : ℝ :=
  ∫ x in ball (0 : Plane) R, planarSmoothEnergyDensity a ε Q x

theorem planarSmoothEnergyDensity_nonneg (a : BulkCoefficients) (ε : ℝ)
    (Q : Plane → S0) (x : Plane) : 0 ≤ planarSmoothEnergyDensity a ε Q x :=
  add_nonneg (planarSmoothDirichletDensity_nonneg Q x) (div_nonneg (bulkPotential_nonneg a _) (sq_nonneg _))

theorem continuous_planarSmoothEnergyDensity (a : BulkCoefficients) (ε : ℝ)
    {Q : Plane → S0} (hQ : ContDiff ℝ 1 Q) : Continuous (planarSmoothEnergyDensity a ε Q) := by
  exact (continuous_planarSmoothDirichletDensity hQ).add (((contDiff_bulkPotential a).continuous.comp hQ.continuous).div_const _)

private theorem continuousOn_planarScalarGradientSq {f : Plane → ℝ} {U : Set Plane}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) : ContinuousOn (planarScalarGradientSq f) U := by
  unfold planarScalarGradientSq
  exact continuousOn_finsetSum _ fun j _ =>
    ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).pow 2

private theorem measurable_planarScalarGradientSq {f : Plane → ℝ} (hf : Continuous f)
    (hf₀ : ∀ x, 0 ≤ f x) (hf' : ContDiffOn ℝ 1 f {x | 0 < f x}) :
    Measurable (planarScalarGradientSq f) := by
  classical
  let U := {x | 0 < f x}
  have hU : IsOpen U := isOpen_lt continuous_const hf
  let j := planarScalarGradientSq f
  have hMeas : Measurable (U.indicator j) :=
    (continuousOn_planarScalarGradientSq hU hf').measurable_piecewise continuousOn_const hU.measurableSet
  have hEq : U.indicator j = j := by
    funext x
    by_cases hx : x ∈ U
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      have h₀ : f x = 0 := le_antisymm (le_of_not_gt hx) (hf₀ x)
      have hMin : IsLocalMin f x := Eventually.of_forall fun y => h₀ ▸ hf₀ y
      simp only [j, planarScalarGradientSq, hMin.fderiv_eq_zero, zero_apply,
        zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
  rwa [hEq] at hMeas

private theorem continuousOn_planarProjectionGradientSq (a : BulkCoefficients) (τ : GapSmoothingParameter)
    {Q : Plane → S0} (hQ : ContDiff ℝ 1 Q) :
    ContinuousOn (planarSpectralProjectionGradientSq a Q) {x | 0 < modifiedSpectralGap a τ (Q x)} := by
  let U := {x | 0 < modifiedSpectralGap a τ (Q x)}
  have hU : IsOpen U := isOpen_lt continuous_const ((continuous_modifiedSpectralGap a τ).comp hQ.continuous)
  have hP : ContDiffOn ℝ 1 (fun x => (spectralVacuumPoint a (Q x)).val) U := by
    simpa only [univ_inter] using contDiffOn_planarSpectralProjection_pos_locus a τ
      (hQ.contDiffOn : ContDiffOn ℝ 1 Q univ)
  have h := (symmetricTraceless.subtypeL.contDiff.contDiffOn.comp hP
    (mapsTo_univ _ _)).continuousOn_fderiv_of_isOpen hU le_rfl
  unfold planarSpectralProjectionGradientSq
  exact continuousOn_finsetSum _ fun j _ =>
    ((h.clm_apply continuousOn_const).norm).pow 2

theorem nativeVacuumCircleCost_bounds_of_pos (a : BulkCoefficients)
    (p : C(NativeCircle, vacuum a)) (hp : 0 < nativeVacuumCircleCost a p) :
    kappaStar a ≤ nativeVacuumCircleCost a p ∧ nativeVacuumCircleCost a p ≤ 2 * kappaStar a := by
  obtain ⟨q, hq⟩ := vacuumQuaternionProjection_surjective a (p nativeCircleLoopBase)
  rw [nativeVacuumCircleCost_eq a p q hq, vacuumSplittingCost_eq] at hp ⊢
  let w := nativeVacuumLoopWord a p q hq
  change 0 < kappaStar a * (quaternionSplittingWeight w : ℝ) at hp
  change kappaStar a ≤ kappaStar a * (quaternionSplittingWeight w : ℝ) ∧
    kappaStar a * (quaternionSplittingWeight w : ℝ) ≤ 2 * kappaStar a
  by_cases hw : w = 1
  · simp [quaternionSplittingWeight, hw] at hp
  · by_cases hLight : IsLightQuaternion w
    · simp only [quaternionSplittingWeight, hw, hLight, if_false, if_true, Nat.cast_one, mul_one]
      exact ⟨le_rfl, by linarith only [kappaStar_pos a]⟩
    · simp only [quaternionSplittingWeight, hw, hLight, if_false, Nat.cast_ofNat]
      constructor <;> linarith only [kappaStar_pos a]

/-- The layer estimate with one fixed modified-gap profile. Its error
bound is independent of the smoothing parameter. -/
theorem planarSmoothEnergy_gap_lower_fixed (hcoarea : External.PlanarScalarCoarea)
    (a : BulkCoefficients) (τ : GapSmoothingParameter) {c g M ε r μ ℓ : ℝ} (hc : 0 < c)
    (hcPotential : ∀ (σ : GapSmoothingParameter) (A : S0),
      c * planarGapLevelWeight (spectralGapSmoothingFactor σ) (modifiedSpectralGap a σ A) ≤ bulkPotential a A)
    (hg : 0 < g) (hgM : g ≤ M) (hε : 0 < ε) (hr : 0 < r) (hℓ : 0 < ℓ) (hμ : μ ≤ r - 2 * ℓ)
    (Q : Plane → S0) (hQ : ContDiff ℝ 1 Q)
    (hGap : ∀ x : Plane, μ ≤ ‖x‖ → ‖x‖ ≤ r → g ≤ normalizedSpectralGap a (Q x))
    (hSimple : ∀ z : NativeCircle, Q (r • z.val) ∈ simpleSpectrumLocus)
    (he : 0 < nativeVacuumCircleCost a (planarSpectralCircleTrace a Q hr.le hQ.continuous.continuousOn hSimple)) :
    let e := nativeVacuumCircleCost a (planarSpectralCircleTrace a Q hr.le hQ.continuous.continuousOn hSimple)
    e * (spectralGapSmoothingFactor τ * g) ^ 2 * Real.log (1 / ε) -
      planarGapLevelLogErrorBound (kappaStar a) (vacuumRadius a * Real.sqrt c / 3) ℓ M ≤
        planarSmoothEnergy a ε Q r := by
  classical
  intro e
  let f (x : Plane) := modifiedSpectralGap a τ (Q x)
  let b := spectralGapSmoothingFactor τ
  let A := b * g
  let c' := vacuumRadius a * Real.sqrt c / 3
  let B := ball (0 : Plane) r
  let D := {x : Plane | 0 < f x}
  let d := D.indicator (planarSpectralProjectionGradientSq a Q)
  let rSub (t : ℝ) := planarCoverRadius (planarSublevelCore f r t)
  let Θ (t : ℝ) := (∫⁻ x in {x | t < f x}, ENNReal.ofReal (d x) ∂volume.restrict B).toReal
  let F₁ (t : ℝ) := (c' / ε) * Real.sqrt (planarGapLevelWeight b t) * rSub t
  let F₂ (t : ℝ) := t * Θ t
  let J₁ (x : Plane) := vacuumRadius a ^ 2 / 36 * planarScalarGradientSq f x + bulkPotential a (Q x) / ε ^ 2
  let J₂ (x : Plane) := (1 / 2 : ℝ) * f x ^ 2 * d x
  have hf : Continuous f := (continuous_modifiedSpectralGap a τ).comp hQ.continuous
  have hf₀ (x : Plane) : 0 ≤ f x := modifiedSpectralGap_nonneg a τ (Q x)
  have hb : 0 < b := spectralGapSmoothingFactor_pos τ
  have hb₁ : b ≤ 1 := spectralGapSmoothingFactor_le_one τ
  have hb₀ : (7 / 12 : ℝ) ≤ b := by
    dsimp only [b, spectralGapSmoothingFactor]
    linarith only [τ.property.2]
  have hA : 0 < A := mul_pos hb hg
  have hAM : A ≤ M := ((mul_le_mul_of_nonneg_right hb₁ hg.le).trans_eq (one_mul g)).trans hgM
  have hμr : μ ≤ r := by linarith only [hμ, hℓ]
  have hAnn (x : Plane) (hx : μ ≤ ‖x‖) (hxr : ‖x‖ ≤ r) : A ≤ f x :=
    (mul_le_mul_of_nonneg_left (hGap x hx hxr) hb.le).trans (modifiedSpectralGap_comparison a τ (Q x)).1
  have hD : IsOpen D := isOpen_lt continuous_const hf
  have hDCont := continuousOn_planarProjectionGradientSq a τ hQ
  have hd : Measurable d := hDCont.measurable_piecewise continuousOn_const hD.measurableSet
  have hd₀ (x : Plane) : 0 ≤ d x := by
    by_cases hx : x ∈ D
    · dsimp only [d]
      rw [indicator_of_mem hx]
      unfold planarSpectralProjectionGradientSq
      positivity
    · rw [show d x = 0 from indicator_of_notMem hx _]
  have hJ₁ : Measurable J₁ := by
    have hf' : ContDiffOn ℝ 1 f D := by
      simpa only [univ_inter] using contDiffOn_planarModifiedGap_pos_locus a τ
        (hQ.contDiffOn : ContDiffOn ℝ 1 Q univ)
    exact (measurable_const.mul (measurable_planarScalarGradientSq hf hf₀ hf')).add
      (((contDiff_bulkPotential a).continuous.comp hQ.continuous).measurable.div_const _)
  have hJ₁₀ (x : Plane) : 0 ≤ J₁ x := by
    exact add_nonneg (mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (div_nonneg (bulkPotential_nonneg a _) (sq_nonneg _))
  have hJ₂₀ (x : Plane) : 0 ≤ J₂ x := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (hd₀ x)
  have hSplit (x : Plane) : J₁ x + J₂ x ≤ planarSmoothEnergyDensity a ε Q x := by
    have h := planarModifiedGap_dirichlet_split a τ Q x (hQ.differentiable (by decide) x)
    have hEq : f x ^ 2 * d x = f x ^ 2 * planarSpectralProjectionGradientSq a Q x := by
      by_cases hx : x ∈ D
      · rw [show d x = _ from indicator_of_mem hx _]
      · rw [show f x = 0 from le_antisymm (le_of_not_gt hx) (hf₀ x)]
        simp
    unfold planarSmoothEnergyDensity
    change vacuumRadius a ^ 2 / 36 * planarScalarGradientSq f x + bulkPotential a (Q x) / ε ^ 2 +
      (1 / 2 : ℝ) * f x ^ 2 * d x ≤ _
    rw [mul_assoc, hEq]
    change vacuumRadius a ^ 2 / 36 * planarScalarGradientSq f x +
      (1 / 2 : ℝ) * f x ^ 2 * planarSpectralProjectionGradientSq a Q x ≤ _ at h
    linarith only [h]
  have h₁ : (∫⁻ t in Ioo 0 A, ENNReal.ofReal (F₁ t)) ≤ ∫⁻ x in B, ENNReal.ofReal (J₁ x) := by
    have h := planarModifiedGap_coarea_expense_le hcoarea a τ hQ.continuous.continuousOn hQ.contDiffOn hμr hε hc
      hAnn (fun x _ => hcPotential τ (Q x))
    dsimp only at h
    convert h using 4
    dsimp only [F₁, c', b]
    ring
  have h₂ : (∫⁻ t in Ioo 0 A, ENNReal.ofReal (F₂ t)) ≤ ∫⁻ x in B, ENNReal.ofReal (J₂ x) :=
    weighted_square_layerCake_half_truncated (volume.restrict B) f d hf.measurable hd hf₀ A
  have hF₁ : Measurable F₁ := by
    have hrM : Measurable rSub := (monotone_planarSublevelCore_radius f r).measurable
    have hw : Continuous (fun t : ℝ => Real.sqrt (planarGapLevelWeight b t)) := by
      unfold planarGapLevelWeight
      fun_prop
    exact (measurable_const.mul hw.measurable).mul hrM
  have hF₂ : Measurable F₂ :=
    measurable_id.mul (measurable_weighted_superlevel_lintegral (volume.restrict B) f d).ennreal_toReal
  have hc' : 0 < c' := div_pos (mul_pos (vacuumRadius_pos a) (Real.sqrt_pos.2 hc)) (by norm_num)
  have hF₁₀ (t : ℝ) : 0 ≤ F₁ t :=
    mul_nonneg (mul_nonneg (div_nonneg hc'.le hε.le) (Real.sqrt_nonneg _)) (planarCoverRadius_nonneg _)
  have hF₂₀ : ∀ᵐ t ∂volume.restrict (Ioo 0 A), 0 ≤ F₂ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg ht.1.le ENNReal.toReal_nonneg
  have hGL :
      (∫⁻ t in Ioo 0 A, ENNReal.ofReal (F₁ t + F₂ t)) ≤
        ∫⁻ x in B, ENNReal.ofReal (planarSmoothEnergyDensity a ε Q x) := by
    have hEq : (∫⁻ t in Ioo 0 A, ENNReal.ofReal (F₁ t + F₂ t)) =
        (∫⁻ t in Ioo 0 A, ENNReal.ofReal (F₁ t)) + ∫⁻ t in Ioo 0 A, ENNReal.ofReal (F₂ t) := by
      rw [← lintegral_add_left hF₁.ennreal_ofReal]
      apply lintegral_congr_ae
      filter_upwards [hF₂₀] with t ht
      exact ENNReal.ofReal_add (hF₁₀ t) ht
    rw [hEq]
    apply (add_le_add h₁ h₂).trans
    rw [← lintegral_add_left hJ₁.ennreal_ofReal]
    apply lintegral_mono
    intro x
    change ENNReal.ofReal (J₁ x) + ENNReal.ofReal (J₂ x) ≤ _
    rw [← ENNReal.ofReal_add (hJ₁₀ x) (hJ₂₀ x)]
    exact ENNReal.ofReal_le_ofReal (hSplit x)
  have hEInt : IntegrableOn (planarSmoothEnergyDensity a ε Q) B :=
    ((continuous_planarSmoothEnergyDensity a ε hQ).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) r)).mono_set ball_subset_closedBall
  have hELt : (∫⁻ x in B, ENNReal.ofReal (planarSmoothEnergyDensity a ε Q x)) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hEInt.1 (Eventually.of_forall (planarSmoothEnergyDensity_nonneg a ε Q))).2 hEInt
  have hFMeas : Measurable (fun t => F₁ t + F₂ t) := hF₁.add hF₂
  have hF₀ : ∀ᵐ t ∂volume.restrict (Ioo 0 A), 0 ≤ F₁ t + F₂ t :=
    hF₂₀.mono fun t ht => add_nonneg (hF₁₀ t) ht
  have hFInt : IntegrableOn (fun t => F₁ t + F₂ t) (Ioo 0 A) :=
    (lintegral_ofReal_ne_top_iff_integrable hFMeas.aestronglyMeasurable hF₀).1
      ((hGL.trans_lt (lt_top_iff_ne_top.2 hELt)).ne)
  have hEnergyBound : (∫ t in 0..A, F₁ t + F₂ t) ≤ planarSmoothEnergy a ε Q r := by
    rw [intervalIntegral.integral_of_le hA.le, ← restrict_Ioo_eq_restrict_Ioc]
    unfold planarSmoothEnergy
    rw [integral_eq_lintegral_of_nonneg_ae hF₀ hFInt.1,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (planarSmoothEnergyDensity_nonneg a ε Q)) hEInt.1]
    exact ENNReal.toReal_mono hELt hGL
  have hThetaEq (t : ℝ) (ht : 0 < t) : Θ t = planarProjectionLevelEnergy a τ Q r t := by
    let S := {x : Plane | t < f x}
    have hS : MeasurableSet S := measurableSet_lt measurable_const hf.measurable
    change (∫⁻ x, ENNReal.ofReal (d x) ∂(volume.restrict B).restrict S).toReal = _
    rw [Measure.restrict_restrict hS, inter_comm S B]
    unfold planarProjectionLevelEnergy
    have hEq : EqOn d (planarSpectralProjectionGradientSq a Q) (B ∩ S) := fun x hx =>
      indicator_of_mem (show x ∈ D from ht.trans hx.2) _
    exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hd₀) hd.aestronglyMeasurable).symm.trans
      (setIntegral_congr_fun (measurableSet_ball.inter hS) hEq)
  have hLevel : ∀ᵐ t ∂volume.restrict (Ioo 0 A),
      0 < rSub t ∧ 2 * e * Real.log (ℓ / rSub t) ≤ Θ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (ae_volume_ball_level_null (hf.continuousOn : ContinuousOn f B))] with t ht hNull
    have h := planarProjectionLevel_energy_lower a τ Q isOpen_univ (hQ.contDiffOn : ContDiffOn ℝ 1 Q univ)
      hr hℓ hμ (subset_univ _) ht hAnn hSimple hNull
    rw [hThetaEq t ht.1]
    exact ⟨h.1 he, h.2⟩
  have heBounds := nativeVacuumCircleCost_bounds_of_pos a _ he
  exact (planarGapLevel_integral_log_lower (kappaStar_pos a) hc' hℓ hε hA hAM hb₀ hb₁
    heBounds.1 heBounds.2 rSub Θ hLevel ((intervalIntegrable_iff_integrableOn_Ioo_of_le hA.le).2 hFInt)).trans hEnergyBound

/-- The smooth spectral gap estimate after removing the profile smoothing. -/
theorem exists_planarSmoothEnergy_gap_lower (hcoarea : External.PlanarScalarCoarea)
    (a : BulkCoefficients) {ℓ M : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε r μ g : ℝ} (_hε : 0 < ε) (hr : 0 < r)
      (_hμ : μ ≤ r - 2 * ℓ) (_hg : 0 < g) (_hgM : g ≤ M)
      (Q : Plane → S0) (hQ : ContDiff ℝ 1 Q)
      (_hGap : ∀ x : Plane, μ ≤ ‖x‖ → ‖x‖ ≤ r → g ≤ normalizedSpectralGap a (Q x))
      (hSimple : ∀ z : NativeCircle, Q (r • z.val) ∈ simpleSpectrumLocus),
      let e := nativeVacuumCircleCost a (planarSpectralCircleTrace a Q hr.le hQ.continuous.continuousOn hSimple)
      e * g ^ 2 * Real.log (1 / ε) - C ≤ planarSmoothEnergy a ε Q r := by
  obtain ⟨c, hc, hPot⟩ := exists_bulkPotential_ge_modifiedGapLevelWeight a
  let D := planarGapLevelLogErrorBound (kappaStar a) (vacuumRadius a * Real.sqrt c / 3) ℓ M
  refine ⟨max 1 D, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro ε r μ g hε hr hμ hg hgM Q hQ hGap hSimple e
  have he₀ : 0 ≤ e := nativeVacuumCircleCost_nonneg a _
  by_cases hZero : e = 0
  · rw [hZero, zero_mul, zero_mul, zero_sub]
    exact (neg_nonpos.mpr (zero_le_one.trans (le_max_left _ _))).trans
      (integral_nonneg (planarSmoothEnergyDensity_nonneg a ε Q))
  have he : 0 < e := lt_of_le_of_ne he₀ (Ne.symm hZero)
  let τ (n : ℕ) : GapSmoothingParameter :=
    ⟨((n : ℝ) + 3)⁻¹, inv_pos.mpr (by positivity),
      (by
        rw [← one_div]
        apply (div_lt_iff₀ (show (0 : ℝ) < (n : ℝ) + 3 by positivity)).2
        nlinarith only [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n])⟩
  have hτ : Tendsto (fun n : ℕ => (τ n).val) atTop (𝓝 0) := by
    have h := (tendsto_mul_add_inv_atTop_nhds_zero 1 3 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    change Tendsto (fun n : ℕ => ((n : ℝ) + 3)⁻¹) atTop (𝓝 0)
    exact h.congr fun n => by simp
  have hb : Tendsto (fun n : ℕ => spectralGapSmoothingFactor (τ n)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (6 : ℝ))).sub (hτ.const_mul 5)
    simpa only [spectralGapSmoothingFactor, mul_zero, sub_zero, div_self (by norm_num : (6 : ℝ) ≠ 0)]
      using (h.div_const 6)
  have hMain : Tendsto (fun n : ℕ => e * (spectralGapSmoothingFactor (τ n) * g) ^ 2 *
      Real.log (1 / ε) - D) atTop (𝓝 (e * g ^ 2 * Real.log (1 / ε) - D)) := by
    simpa only [one_mul] using ((((hb.mul_const g).pow 2).const_mul e).mul_const (Real.log (1 / ε))).sub_const D
  have hLower := le_of_tendsto' hMain (fun n =>
    planarSmoothEnergy_gap_lower_fixed hcoarea a (τ n) hc hPot hg hgM hε hr hℓ hμ Q hQ hGap hSimple he)
  exact (sub_le_sub_left (le_max_right _ _) _).trans hLower

theorem simpleSpectrum_of_normalizedSpectralGap_pos (a : BulkCoefficients) {A : S0}
    (hA : 0 < normalizedSpectralGap a A) : A ∈ simpleSpectrumLocus := by
  let τ : GapSmoothingParameter := ⟨1 / 4, by norm_num, by norm_num⟩
  exact (modifiedSpectralGap_pos_iff a τ A).1
    ((mul_pos (spectralGapSmoothingFactor_pos τ) hA).trans_le (modifiedSpectralGap_comparison a τ A).1)

theorem planar_norm_on_circle {r : ℝ} (hr : 0 ≤ r) (z : NativeCircle) :
    ‖r • z.val‖ = r := by
  rw [norm_smul, Real.norm_of_nonneg hr, mem_sphere_zero_iff_norm.mp z.property, mul_one]

/-- The smooth logarithmic bound on the manuscript's disk of radius 39/40,
with gap on the closed annulus whose inner radius is 1/40. Extended
nonnegative integration permits infinite energy at the outer boundary. -/
theorem exists_planarSmooth_annular_gap_lower (hcoarea : External.PlanarScalarCoarea)
    (a : BulkCoefficients) (C₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε g : ℝ} (hε : 0 < ε) (hg : 0 < g)
      (Q : Plane → S0) (hQ : ContDiffOn ℝ 1 Q (ball (0 : Plane) (39 / 40)))
      (hQcts : ContinuousOn Q (closedBall (0 : Plane) (39 / 40)))
      (hNorm : ∀ x ∈ ball (0 : Plane) (39 / 40), ‖Q x‖ ≤ C₀)
      (hGap : ∀ x : Plane, 1 / 40 ≤ ‖x‖ → ‖x‖ ≤ 39 / 40 → g ≤ normalizedSpectralGap a (Q x)),
      let hS : ∀ z : NativeCircle, Q ((39 / 40 : ℝ) • z.val) ∈ simpleSpectrumLocus := fun z =>
        simpleSpectrum_of_normalizedSpectralGap_pos a (hg.trans_le
          (hGap _ (by rw [planar_norm_on_circle (by norm_num)]; norm_num)
            (by rw [planar_norm_on_circle (by norm_num)])))
      let e := nativeVacuumCircleCost a (planarSpectralCircleTrace a Q (by norm_num) hQcts hS)
      ENNReal.ofReal (e * g ^ 2 * Real.log (1 / ε) - C) ≤
        ∫⁻ x in ball (0 : Plane) (39 / 40), ENNReal.ofReal (planarSmoothEnergyDensity a ε Q x) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : S0) C₀).exists_bound_of_continuousOn
    (continuous_normalizedSpectralGap a).continuousOn
  obtain ⟨C, hC, hGlobal⟩ := exists_planarSmoothEnergy_gap_lower hcoarea a (M := M)
    (show (0 : ℝ) < 19 / 80 by norm_num)
  refine ⟨C, hC, ?_⟩
  intro ε g hε hg Q hQ hQcts hNorm hGap hS e
  let r : ℝ := 1 / 2
  let R : ℝ := 39 / 40
  have hr : 0 < r := by norm_num [r]
  have hrR : r < R := by norm_num [r, R]
  have hμr : (1 / 40 : ℝ) ≤ r - 2 * (19 / 80) := by norm_num [r]
  have hK : closedBall (0 : Plane) r ⊆ ball (0 : Plane) R := closedBall_subset_ball hrR
  obtain ⟨P, hP, hNear⟩ := exists_contDiff_eq_near_compact isOpen_ball
    (isCompact_closedBall (0 : Plane) r) hK hQ
  have hBP (x : Plane) (hx : ‖x‖ ≤ r) : P x = Q x :=
    (hNear x (by simpa only [mem_closedBall, dist_zero_right] using hx)).eq_of_nhds
  have hGr (x : Plane) (hx : (1 / 40 : ℝ) ≤ ‖x‖) (hxr : ‖x‖ ≤ r) :
      g ≤ normalizedSpectralGap a (P x) := by
    rw [hBP x hxr]
    exact hGap x hx (hxr.trans hrR.le)
  have hgM : g ≤ M := by
    let x := r • nativeCircleLoopBase.val
    have hxNorm : ‖x‖ = r := planar_norm_on_circle hr.le nativeCircleLoopBase
    have hx : x ∈ ball (0 : Plane) R := by rw [mem_ball, dist_zero_right, hxNorm]; exact hrR
    have hG := hGap x (by rw [hxNorm]; norm_num [r]) (by rw [hxNorm]; exact hrR.le)
    have hQM : Q x ∈ closedBall (0 : S0) C₀ :=
      mem_closedBall.mpr (by simpa only [dist_zero_right] using hNorm x hx)
    exact (hG.trans (le_abs_self _)).trans (by simpa only [Real.norm_eq_abs] using hM (Q x) hQM)
  have hSr (z : NativeCircle) : Q (r • z.val) ∈ simpleSpectrumLocus := by
    apply simpleSpectrum_of_normalizedSpectralGap_pos a
    refine hg.trans_le (hGap _ ?_ ?_)
    · rw [planar_norm_on_circle hr.le]
      norm_num [r]
    · rw [planar_norm_on_circle hr.le]
      exact hrR.le
  have hPsimple (z : NativeCircle) : P (r • z.val) ∈ simpleSpectrumLocus := by
    rw [hBP _ (planar_norm_on_circle hr.le z).le]
    exact hSr z
  have hTrace : planarSpectralCircleTrace a P hr.le hP.continuous.continuousOn hPsimple =
      planarSpectralCircleTrace a Q hr.le (hQcts.mono (closedBall_subset_closedBall hrR.le)) hSr := by
    apply ContinuousMap.ext
    intro z
    change spectralVacuumPoint a (P (r • z.val)) = spectralVacuumPoint a (Q (r • z.val))
    rw [hBP _ (planar_norm_on_circle hr.le z).le]
  have hHom := planarSpectralCircleTrace_homotopic a Q hr.le hrR.le hQcts
    (fun x hx hxR => simpleSpectrum_of_normalizedSpectralGap_pos a
      (hg.trans_le (hGap x ((by norm_num [r] : (1 / 40 : ℝ) ≤ r).trans hx) hxR))) hSr hS
  have hCost := nativeVacuumCircleCost_homotopic a hHom
  rw [← hTrace] at hCost
  have hLower := hGlobal hε hr hμr hg hgM P hP hGr hPsimple
  dsimp only at hLower
  rw [hCost] at hLower
  have hEnergyInt : IntegrableOn (planarSmoothEnergyDensity a ε P) (ball (0 : Plane) r) :=
    ((continuous_planarSmoothEnergyDensity a ε hP).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) r)).mono_set ball_subset_closedBall
  apply (ENNReal.ofReal_le_ofReal hLower).trans
  rw [planarSmoothEnergy, ofReal_integral_eq_lintegral_ofReal hEnergyInt
    (Eventually.of_forall (planarSmoothEnergyDensity_nonneg a ε P))]
  have hEq : EqOn (planarSmoothEnergyDensity a ε P) (planarSmoothEnergyDensity a ε Q) (ball (0 : Plane) r) := by
    intro x hx
    have hN := hNear x (ball_subset_closedBall hx)
    have hD : fderiv ℝ (fun y => (P y : Tensor)) x = fderiv ℝ (fun y => (Q y : Tensor)) x :=
      (hN.fun_comp (fun A : S0 => (A : Tensor))).fderiv_eq
    unfold planarSmoothEnergyDensity planarSmoothDirichletDensity
    rw [hN.eq_of_nhds, hD]
  rw [lintegral_congr_ae ((ae_restrict_mem measurableSet_ball).mono (fun x hx =>
    congrArg ENNReal.ofReal (hEq hx)))]
  exact lintegral_mono_set (ball_subset_ball hrR.le)

end Thesis
