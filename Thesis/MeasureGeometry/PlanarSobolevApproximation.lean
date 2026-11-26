module

public import HarmonicMaps.Analysis.MollificationDistance
public import HarmonicMaps.Analysis.InteriorSobolevApproximation

/-! Guard preservation for mollification of actual planar Sobolev maps. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal

namespace Thesis

/-- In dimension two, local energy bounds the distance of the native mollification
from any set carrying the map almost everywhere. -/
theorem planar_mollification_infDist_sq_le_energy {q : ℕ}
    {u : Domain 2 → Ambient q} {Du : Domain 2 → Gradient 2 q}
    (h : PositiveRadius) (x : Domain 2)
    (hu : MemW12 (ballDomain x h.val) u Du)
    (S : Set (Ambient q)) (huS : ∀ᵐ z ∂volume.restrict (ball x h.val), u z ∈ S) :
    infDist (∫ y in ball (0 : Domain 2) 1, fixedMollifierKernel 2 y • u (x - h.val • y)) S ^ 2 ≤
      (8 * fixedMollifierKernelBound 2) * ∫ z in ball x h.val, hsNormSq (Du z) := by
  letI : IsFiniteMeasure (volume.restrict (ball x h.val)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let b := ⨍ z in ball x h.val, u z
  let f : Domain 2 → Ambient q := fun y => u (x - h.val • y)
  have hL2 : MemLp u 2 (volume.restrict (ball x h.val)) := hu.2.1
  have hf : MemLp f 2 (fixedMollifierProbability 2) :=
    mollification_sampling_memLp_probability h x hL2
  have hSf : ∀ᵐ y ∂fixedMollifierProbability 2, f y ∈ S :=
    ae_fixedMollifierProbability_of_ae_unitBall (ae_mollification_sampling_ball h x huS)
  have hb : IntegrableOn (fun z => ‖u z - b‖ ^ 2) (ball x h.val) volume :=
    (hL2.sub (memLp_const b)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hkernel := mollification_local_kernel_estimate h x hb
    (Eventually.of_forall fun z => sq_nonneg ‖u z - b‖) (fixedMollifierKernel_le_bound 2)
  have hpoincare := hu.poincare_ball h.property
  have hcoeff : 0 ≤ fixedMollifierKernelBound 2 * (h.val ^ 2)⁻¹ :=
    mul_nonneg (fixedMollifierKernelBound_pos 2).le (inv_nonneg.mpr (sq_nonneg _))
  calc
    _ = infDist (∫ y, f y ∂fixedMollifierProbability 2) S ^ 2 := by
      rw [fixedMollifierProbability_integral_eq_setIntegral]
    _ ≤ ∫ y, ‖f y - ∫ z, f z ∂fixedMollifierProbability 2‖ ^ 2 ∂fixedMollifierProbability 2 :=
      probability_infDist_sq_le_variance _ hf S hSf
    _ ≤ ∫ y, ‖f y - b‖ ^ 2 ∂fixedMollifierProbability 2 := probability_variance_le _ hf b
    _ = ∫ y in ball (0 : Domain 2) 1, fixedMollifierKernel 2 y * ‖u (x - h.val • y) - b‖ ^ 2 := by
      rw [fixedMollifierProbability_integral_eq_setIntegral]
      simp only [f, smul_eq_mul]
    _ ≤ fixedMollifierKernelBound 2 * (h.val ^ 2)⁻¹ * ∫ z in ball x h.val, ‖u z - b‖ ^ 2 :=
      hkernel.2
    _ ≤ fixedMollifierKernelBound 2 * (h.val ^ 2)⁻¹ *
        ((2 : ℝ) ^ (2 + 1) * h.val ^ 2 * ∫ z in ball x h.val, hsNormSq (Du z)) :=
      mul_le_mul_of_nonneg_left hpoincare hcoeff
    _ = _ := by field_simp [h.property.ne']; ring

/-- Planar mollifications approach their almost-everywhere carrier uniformly
in distance on compact subsets of the domain. -/
theorem exists_planar_mollification_guard_radius {q : ℕ} (Ω : OpenDomain 2)
    {u : Domain 2 → Ambient q} {Du : Domain 2 → Gradient 2 q}
    (hu : MemW12Loc Ω u Du) (hE : IntegrableOn (fun z => hsNormSq (Du z)) Ω.val)
    (S : Set (Ambient q)) (huS : ∀ᵐ z ∂volume.restrict Ω.val, u z ∈ S)
    (K : Set (Domain 2)) (hK : IsCompact K) (hKΩ : K ⊆ Ω.val) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ (h : PositiveRadius), h.val ≤ ρ → ∀ x ∈ K,
      infDist (∫ y in ball (0 : Domain 2) 1,
        fixedMollifierKernel 2 y • u (x - h.val • y)) S < ε := by
  let C := 8 * fixedMollifierKernelBound 2
  have hC : 0 < C := mul_pos (by norm_num) (fixedMollifierKernelBound_pos 2)
  let F (z : Domain 2) := hsNormSq (Du z)
  let μ := volume.restrict Ω.val
  have hNonNeg (z : Domain 2) : 0 ≤ F z := hsNormSq_nonneg _
  have hFinite : (∫⁻ z, ENNReal.ofReal (F z) ∂μ) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hE (Eventually.of_forall hNonNeg)]
    exact ENNReal.ofReal_ne_top
  have hsmall : 0 < ε ^ 2 / C := div_pos (sq_pos_of_pos hε) hC
  obtain ⟨δ, hδ, hδBound⟩ := exists_pos_setLIntegral_lt_of_measure_lt hFinite
    (ENNReal.ofReal_ne_zero_iff.mpr hsmall)
  have hvolumeCont : Continuous (fun r : ℝ => ENNReal.ofReal (r ^ 2 * Real.pi)) :=
    ENNReal.continuous_ofReal.comp ((continuous_id.pow 2).mul continuous_const)
  let G := (fun r : ℝ => ENNReal.ofReal (r ^ 2 * Real.pi)) ⁻¹' Iio δ
  have hG : IsOpen G := isOpen_Iio.preimage hvolumeCont
  have hG₀ : (0 : ℝ) ∈ G := by simp [G, hδ]
  obtain ⟨η, hη, hηSub⟩ := Metric.isOpen_iff.mp hG 0 hG₀
  obtain ⟨r, hr, hSub⟩ := hK.exists_cthickening_subset_open Ω.property hKΩ
  let ρ := min (η / 2) r
  refine ⟨ρ, lt_min (by positivity) hr, ?_⟩
  intro h hh x hx
  have hBall : closedBall x h.val ⊆ Ω.val :=
    (closedBall_subset_closedBall (hh.trans (min_le_right _ _))).trans
      ((closedBall_subset_cthickening hx r).trans hSub)
  have hOpenBall : ball x h.val ⊆ Ω.val := ball_subset_closedBall.trans hBall
  have hη' : h.val ∈ ball (0 : ℝ) η := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg h.property.le]
    exact (hh.trans (min_le_left _ _)).trans_lt (half_lt_self hη)
  have hVol : volume (ball x h.val) < δ := by
    rw [EuclideanSpace.volume_ball_fin_two, ← ENNReal.ofReal_pow h.property.le,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    exact hηSub hη'
  have hμ : μ ≤ (volume : Measure (Domain 2)) := Measure.restrict_le_self
  have hEnergy := hδBound (ball x h.val) ((hμ _).trans_lt hVol)
  change (∫⁻ z in ball x h.val, ENNReal.ofReal (F z) ∂volume.restrict Ω.val) <
    ENNReal.ofReal (ε ^ 2 / C) at hEnergy
  rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hOpenBall,
    ← ofReal_integral_eq_lintegral_ofReal (hE.mono_set hOpenBall) (Eventually.of_forall hNonNeg)] at hEnergy
  have hInt : (∫ z in ball x h.val, F z) < ε ^ 2 / C :=
    (ENNReal.ofReal_lt_ofReal_iff hsmall).1 hEnergy
  have hS : ∀ᵐ z ∂volume.restrict (ball x h.val), u z ∈ S :=
    huS.filter_mono (ae_mono (Measure.restrict_mono_set volume hOpenBall))
  have hSq := (planar_mollification_infDist_sq_le_energy h x (hu.memW12_ball hBall) S hS).trans_lt
    ((lt_div_iff₀' hC).1 hInt)
  exact (sq_lt_sq₀ infDist_nonneg hε.le).mp hSq

/-- The native domain mollification samples the original map when its sampling ball is interior. -/
theorem euclideanMollification_eq_sampling_integral {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val) (h : PositiveRadius)
    (x : Domain n) (hx : ball x h.val ⊆ Ω.val) :
    euclideanMollification Ω u hu h x =
      ∫ y in ball (0 : Domain n) 1, fixedMollifierKernel n y • u (x - h.val • y) := by
  unfold euclideanMollification
  rw [← fixedKernelAverage_eq_scaledConvolution]
  calc
    _ = ∫ y in ball (0 : Domain n) 1, fixedMollifierKernel n y • zeroExtensionOn Ω u (x - h.val • y) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [fixedMollifierKernel_zero_of_not_mem_unitBall hy, zero_smul]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      have hy' : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy
      have hs : x - h.val • y ∈ ball x h.val := by
        rw [mem_ball, dist_eq_norm]
        rw [show x - h.val • y - x = -(h.val • y) by abel]
        rw [norm_neg, norm_smul, Real.norm_of_nonneg h.property.le]
        exact mul_lt_of_lt_one_right h.property hy'
      change fixedMollifierKernel n y • (zeroExtensionOn Ω u (x - h.val • y)) =
        fixedMollifierKernel n y • u (x - h.val • y)
      rw [zeroExtensionOn, indicator_of_mem (hx hs)]

/-- Positive normalized convolution preserves the global essential norm bound. -/
theorem euclideanMollification_norm_le_essential_bound {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val) {C : ℝ} (hC : 0 ≤ C)
    (huC : ∀ᵐ x ∂volume.restrict Ω.val, ‖u x‖ ≤ C) (h : PositiveRadius) (x : Domain n) :
    ‖euclideanMollification Ω u hu h x‖ ≤ C := by
  let U := zeroExtensionOn Ω u
  have hU : ∀ᵐ y ∂(volume : Measure (Domain n)), ‖U y‖ ≤ C := by
    filter_upwards [(ae_restrict_iff' Ω.property.measurableSet).mp huC] with y hy
    by_cases hyΩ : y ∈ Ω.val
    · change ‖Ω.val.indicator u y‖ ≤ C
      rw [indicator_of_mem hyΩ]
      exact hy hyΩ
    · change ‖Ω.val.indicator u y‖ ≤ C
      rw [indicator_of_notMem hyΩ, norm_zero]
      exact hC
  have hAffine : Measure.QuasiMeasurePreserving (fun y : Domain n => x - h.val • y) volume volume :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.comp
      (Measure.quasiMeasurePreserving_smul volume h.property.ne')
  have hCU : ∀ᵐ y ∂(volume : Measure (Domain n)), ‖U (x - h.val • y)‖ ≤ C := hAffine.ae hU
  let F (y : Domain n) := fixedMollifierKernel n y • U (x - h.val • y)
  have hFmeas : AEStronglyMeasurable F volume :=
    (fixedMollifierKernel_contDiff n).continuous.aestronglyMeasurable.smul
      ((zeroExtensionOn_integrable Ω u hu).aestronglyMeasurable.comp_quasiMeasurePreserving hAffine)
  have hBound : ∀ᵐ y ∂(volume : Measure (Domain n)), ‖F y‖ ≤ C * fixedMollifierKernel n y := by
    filter_upwards [hCU] with y hy
    change ‖fixedMollifierKernel n y • U (x - h.val • y)‖ ≤ C * fixedMollifierKernel n y
    rw [norm_smul, Real.norm_of_nonneg (fixedMollifierKernel_nonneg n y), mul_comm C]
    exact mul_le_mul_of_nonneg_left hy (fixedMollifierKernel_nonneg n y)
  have hM : Integrable (fun y => C * fixedMollifierKernel n y) volume :=
    (fixedMollifierKernel_integrable n).const_mul C
  have hF : Integrable F volume := hM.mono' hFmeas hBound
  unfold euclideanMollification
  rw [← fixedKernelAverage_eq_scaledConvolution]
  calc
    _ ≤ ∫ y, ‖F y‖ := norm_integral_le_integral_norm F
    _ ≤ ∫ y, C * fixedMollifierKernel n y := integral_mono_ae hF.norm hM hBound
    _ = C := by rw [integral_const_mul, fixedMollifierKernel_integral, mul_one]

/-- Smooth approximation on an inner ball with simultaneous map and gradient
control and uniform distance to the original guard on a compact subset. -/
theorem exists_guarded_smooth_planar_approximation {q : ℕ} {c : Domain 2} {R r : ℝ}
    {u : Domain 2 → Ambient q} {Du : Domain 2 → Gradient 2 q}
    (hu : MemW12 (ballDomain c R) u Du) (hr : r < R)
    (Ω : OpenDomain 2) (hΩ : Ω.val ⊆ ball c R)
    (S : Set (Ambient q)) (hS : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ S)
    (K : Set (Domain 2)) (hK : IsCompact K) (hKΩ : K ⊆ Ω.val)
    {err : ℝ≥0∞} (herr : 0 < err) {guardErr : ℝ} (hg : 0 < guardErr) :
    ∃ m : Domain 2 → Ambient q, ∃ hm : ContDiff ℝ ∞ m,
      MemLp m 2 (volume.restrict (ball c r)) ∧
      (∀ i, MemLp (coordinateDerivative m hm i) 2 (volume.restrict (ball c r))) ∧
      eLpNorm (m - u) 2 (volume.restrict (ball c r)) < err ∧
      (∀ i, eLpNorm (fun x => coordinateDerivative m hm i x - Du x i)
        2 (volume.restrict (ball c r)) < err) ∧
      ∀ x ∈ K, infDist (m x) S < guardErr := by
  obtain ⟨ρ, hρ, hGuard⟩ := exists_planar_mollification_guard_radius Ω
    (hu.to_memW12Loc.mono hΩ) (hu.integrable_hsNormSq.mono_set hΩ) S hS K hK hKΩ hg
  obtain ⟨σ, hσ, hσSub⟩ := hK.exists_cthickening_subset_open Ω.property hKΩ
  let scales : ℕ → PositiveRadius := fun k => ⟨1 / ((k : ℝ) + 1), by positivity⟩
  let scaleFilter := comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))
  have hscale : Tendsto scales atTop scaleFilter :=
    tendsto_comap_iff.mpr tendsto_one_div_add_atTop_nhds_zero_nat
  letI : NeBot scaleFilter := hscale.neBot
  have hval : Tendsto (fun h : PositiveRadius => h.val) scaleFilter (𝓝 0) := tendsto_comap
  have hδ : 0 < min (min ρ σ) (2 * (R - r)) := lt_min (lt_min hρ hσ) (by linarith only [hr])
  have hmap := (hu.tendsto_eLpNorm_mollification_inner_ball hr).eventually_lt_const herr
  have hcol := eventually_all.mpr fun i => (hu.tendsto_eLpNorm_mollification_column_inner_ball hr i).eventually_lt_const herr
  obtain ⟨h, hMh, hDh, hh⟩ := (hmap.and (hcol.and (hval.eventually_lt_const hδ))).exists
  have hleρ : h.val ≤ ρ := (hh.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  have hleσ : h.val ≤ σ := (hh.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
  have hle : h.val ≤ 2 * (R - r) := (hh.trans_le (min_le_right _ _)).le
  refine ⟨euclideanMollification (ballDomain c R) u hu.integrable_ball h,
    euclideanMollification_contDiff (ballDomain c R) u hu.integrable_ball h,
    hu.euclideanMollification_memLp_inner_ball h, ?_, hMh, hDh, ?_⟩
  · exact fun i => hu.euclideanMollification_column_memLp_inner_ball h (by linarith only [hle]) i
  · intro x hx
    have hBall : ball x h.val ⊆ (ballDomain c R).val :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hleσ)).trans
        ((closedBall_subset_cthickening hx σ).trans (hσSub.trans hΩ))
    rw [euclideanMollification_eq_sampling_integral _ _ _ h x hBall]
    exact hGuard h hleρ x hx

/-- The same native mollification converges uniformly on compact subsets
where its actual representative is continuous. -/
theorem exists_euclideanMollification_uniform_radius {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val)
    (V : OpenDomain n) (hVΩ : V.val ⊆ Ω.val) (hC : ContinuousOn u V.val)
    (K : Set (Domain n)) (hK : IsCompact K) (hKV : K ⊆ V.val) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ (h : PositiveRadius), h.val ≤ δ → ∀ x ∈ K,
      ‖euclideanMollification Ω u hu h x - u x‖ < η := by
  obtain ⟨σ, hσ, hσV⟩ := hK.exists_cthickening_subset_open V.property hKV
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (IsCompact.uniformContinuousOn_of_continuous (hK.cthickening (r := σ)) (hC.mono hσV)) (η / 2) (half_pos hη)
  refine ⟨min σ δ, lt_min hσ hδ, ?_⟩
  intro h hh x hx
  let U := zeroExtensionOn Ω u
  let F (y : Domain n) := fixedMollifierKernel n y • U (x - h.val • y)
  let G (y : Domain n) := fixedMollifierKernel n y • u x
  have hG : Integrable G volume := (fixedMollifierKernel_integrable n).smul_const (u x)
  have hMeasure : Measure.QuasiMeasurePreserving (fun y : Domain n => x - h.val • y) volume volume :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.comp
      (Measure.quasiMeasurePreserving_smul volume h.property.ne')
  have hFmeas : AEStronglyMeasurable F volume :=
    (fixedMollifierKernel_contDiff n).continuous.aestronglyMeasurable.smul
      ((zeroExtensionOn_integrable Ω u hu).aestronglyMeasurable.comp_quasiMeasurePreserving hMeasure)
  have hBound (y : Domain n) : ‖F y - G y‖ ≤ (η / 2) * fixedMollifierKernel n y := by
    by_cases hy : y ∈ ball (0 : Domain n) 1
    · have hyNorm : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy
      have hDist : dist (x - h.val • y) x < h.val := by
        rw [dist_eq_norm, show x - h.val • y - x = -(h.val • y) by abel,
          norm_neg, norm_smul, Real.norm_of_nonneg h.property.le]
        exact mul_lt_of_lt_one_right h.property hyNorm
      have hyK : x - h.val • y ∈ cthickening σ K :=
        closedBall_subset_cthickening hx σ (mem_closedBall.mpr ((hDist.trans_le (hh.trans (min_le_left _ _))).le))
      have hxK : x ∈ cthickening σ K := self_subset_cthickening _ hx
      have hCl := hU (x - h.val • y) hyK x hxK (hDist.trans_le (hh.trans (min_le_right _ _)))
      have hEq : U (x - h.val • y) = u (x - h.val • y) :=
        indicator_of_mem (hVΩ (hσV hyK)) _
      change ‖fixedMollifierKernel n y • U (x - h.val • y) - fixedMollifierKernel n y • u x‖ ≤ _
      rw [hEq, ← smul_sub, norm_smul, Real.norm_of_nonneg (fixedMollifierKernel_nonneg n y), mul_comm (η / 2)]
      apply mul_le_mul_of_nonneg_left _ (fixedMollifierKernel_nonneg n y)
      simpa only [dist_eq_norm] using hCl.le
    · simp [F, G, fixedMollifierKernel_zero_of_not_mem_unitBall hy]
  have hMajor : Integrable (fun y => (η / 2) * fixedMollifierKernel n y) volume :=
    (fixedMollifierKernel_integrable n).const_mul _
  have hFG : Integrable (fun y => F y - G y) volume :=
    hMajor.mono' (hFmeas.sub hG.aestronglyMeasurable) (Eventually.of_forall hBound)
  have hF : Integrable F volume := by
    exact (hFG.add hG).congr (Eventually.of_forall fun y => sub_add_cancel (F y) (G y))
  have hIntG : (∫ y, G y) = u x := by
    dsimp only [G]
    rw [integral_smul_const, fixedMollifierKernel_integral, one_smul]
  have hIntF : (∫ y, F y) = euclideanMollification Ω u hu h x := by
    unfold euclideanMollification
    rw [← fixedKernelAverage_eq_scaledConvolution]
  rw [← hIntF, ← hIntG, ← integral_sub hF hG]
  calc
    _ ≤ ∫ y, ‖F y - G y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (η / 2) * fixedMollifierKernel n y :=
      integral_mono hFG.norm hMajor hBound
    _ = η / 2 := by rw [integral_const_mul, fixedMollifierKernel_integral, mul_one]
    _ < η := by linarith

end Thesis
