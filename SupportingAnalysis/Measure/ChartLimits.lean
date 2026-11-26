module

public import SupportingAnalysis.Measure.Scaling
public import SupportingAnalysis.Basics

public section

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology

set_option autoImplicit false

namespace SupportingAnalysis

private theorem chartZoom_tendsto {m d : ℕ} {f : E d → E m} {D : E d →L[ℝ] E m}
    {x : E d} (hD : HasFDerivAt f D x) (z : E d) :
    Tendsto (fun r : ℝ => r⁻¹ • (f (x + r • z) - f x)) (𝓝[>] 0) (𝓝 (D z)) :=
  (hD.hasLineDerivAt z : HasLineDerivAt ℝ f (D z) x z).tendsto_slope_zero_right

/-- The parameter density at a Lebesgue point converges in normalized coordinates
in local (L^1). -/
theorem tendsto_integral_chartDensity_error {d : ℕ} {w : E d → ℝ} {x : E d} {R : ℝ}
    (hR : 0 < R)
    (hLeb : Tendsto (fun s : ℝ => ⨍ y in closedBall x s, ‖w y - w x‖ ∂volume)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => ∫ z in closedBall (0 : E d) R, ‖w (x + r • z) - w x‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hmul : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcont : Continuous (fun r : ℝ => r * R) := by fun_prop
      simpa only [zero_mul] using hcont.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with r hr
      exact mem_Ioi.mpr (mul_pos hr hR)
  have ht := tendsto_const_nhds.mul (hLeb.comp hmul) (a := volume.real (closedBall (0 : E d) R))
  rw [mul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with r hr
  have hr₀ : 0 < r := hr
  have hpre : domainDilation x hr₀ ⁻¹' closedBall x (r * R) = closedBall (0 : E d) R := by
    ext z
    have hx : domainDilation x hr₀ 0 = x := by simp
    change dist (domainDilation x hr₀ z) x ≤ r * R ↔ dist z 0 ≤ R
    have hdist := dist_domainDilation x hr₀ z 0
    rw [hx] at hdist
    rw [hdist, mul_le_mul_iff_right₀ hr₀]
  have hco : (∫ z in closedBall (0 : E d) R, ‖w (x + r • z) - w x‖) =
      (r ^ d)⁻¹ * ∫ y in closedBall x (r * R), ‖w y - w x‖ := by
    simpa only [hpre, domainDilation_apply, smul_eq_mul] using
      integral_comp_domainDilation x hr₀ (closedBall x (r * R)) (fun y => ‖w y - w x‖)
  have hmeasure : volume.real (closedBall x (r * R)) =
      r ^ d * volume.real (closedBall (0 : E d) R) := by
    have h := congrArg (fun μ : Measure (E d) => μ.real (closedBall x (r * R)))
      (map_volume_domainDilation x hr₀)
    simp only [Measure.real, Measure.map_apply (domainDilation x hr₀).continuous.measurable
      measurableSet_closedBall, hpre, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hr₀.le _))] at h
    change (volume (closedBall x (r * R))).toReal =
      r ^ d * (volume (closedBall (0 : E d) R)).toReal
    rw [h, mul_inv_cancel_left₀ (pow_ne_zero _ hr₀.ne')]
  simp only [Function.comp_apply, setAverage_eq, smul_eq_mul, hco, hmeasure]
  have hzero : volume.real (closedBall (0 : E d) R) ≠ 0 := by
    exact (ENNReal.toReal_pos (measure_closedBall_pos volume (0 : E d) hR).ne'
      (measure_closedBall_lt_top (μ := volume)).ne).ne'
  field_simp [hzero, hr₀.ne']

/-- Lebesgue differentiation for a fixed parameter density. -/
theorem ae_chartDensity_lebesguePoint {d : ℕ} {w : E d → ℝ}
    (hw : Integrable w) :
    ∀ᵐ x ∂(volume : Measure (E d)),
      Tendsto (fun r : ℝ => ⨍ y in closedBall x r, ‖w y - w x‖ ∂volume)
        (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure (E d)) hw.locallyIntegrable 1]
    with x hx
  exact hx (fun _ => x) id tendsto_id (by
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with r hr
    simpa only [id_eq, one_mul] using mem_closedBall_self (show 0 ≤ r from le_of_lt hr))

private theorem integral_chartZoom_weighted_change {m d : ℕ} {f : E d → E m}
    (hf : Continuous f) {w : E d → ℝ} (hw : Measurable w) (hw₀ : ∀ x, 0 ≤ w x)
    (x : E d) {r : ℝ} (hr : 0 < r) {φ : E m → ℝ} (hφ : Continuous φ) :
    (∫ y, φ y ∂@blownUpMeasure m d (f x) r
        (Measure.map f ((volume : Measure (E d)).withDensity (fun y => ENNReal.ofReal (w y))))) =
      ∫ z, φ (r⁻¹ • (f (x + r • z) - f x)) * w (x + r • z) := by
  have hZ : Continuous (fun y : E m => r⁻¹ • (y - f x)) := by fun_prop
  have hm : Measurable (fun y : E d => ENNReal.ofReal (w y)) := hw.ennreal_ofReal
  have hφZ : Continuous (fun y : E m => φ (r⁻¹ • (y - f x))) := hφ.comp hZ
  unfold blownUpMeasure
  rw [integral_smul_measure, integral_map hZ.measurable.aemeasurable hφ.aestronglyMeasurable,
    integral_map hf.measurable.aemeasurable hφZ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hm
      (Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hw₀ _), smul_eq_mul, zpow_neg, zpow_natCast,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hr.le _))]
  have he := integral_comp_domainDilation x hr univ (fun y => φ (r⁻¹ • (f y - f x)) * w y)
  simp only [preimage_univ, Measure.restrict_univ, domainDilation_apply, smul_eq_mul] at he
  rw [he]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  simp only [mul_comm]


/-- At a differentiability and Lebesgue point of the parameter density, the weighted
chart has the pushforward of its linearization as its full-scale vague limit. -/
theorem vagueOn_blownUpMeasure_weightedChart {m d : ℕ} {f : E d → E m}
    (hf : Continuous f) {w : E d → ℝ} (hw : Measurable w) (hwI : Integrable w)
    (hw₀ : ∀ x, 0 ≤ w x) {D : E d →L[ℝ] E m} {x : E d} (hD : HasFDerivAt f D x)
    (K : ℝ) (hK : 0 ≤ K)
    (hLower : ∀ y, w y ≠ 0 → ‖y - x‖ ≤ K * ‖f y - f x‖)
    (hDLower : ∀ z, ‖z‖ ≤ K * ‖D z‖)
    (hLeb : Tendsto (fun s : ℝ => ⨍ y in closedBall x s, ‖w y - w x‖ ∂volume)
      (𝓝[>] 0) (𝓝 0)) :
    VagueOn univ (𝓝[>] (0 : ℝ))
      (fun r => @blownUpMeasure m d (f x) r
        (Measure.map f ((volume : Measure (E d)).withDensity (fun y => ENNReal.ofReal (w y)))))
      (ENNReal.ofReal (w x) • Measure.map D volume) := by
  intro φ hφ hφc _
  obtain ⟨M, hM, hSupp⟩ := hφc.isBounded.subset_closedBall_lt 0 (0 : E m)
  obtain ⟨B, hB⟩ := hφ.norm.bddAbove_range_of_hasCompactSupport hφc.norm
  let R := K * M + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let A : Set (E d) := closedBall 0 R
  let F (r : ℝ) (z : E d) := φ (r⁻¹ • (f (x + r • z) - f x))
  have hF (r : ℝ) : Continuous (F r) := hφ.comp (by fun_prop)
  have hFbound (r : ℝ) (z : E d) : ‖F r z‖ ≤ B := hB ⟨_, rfl⟩
  let error (r : ℝ) (z : E d) := w (x + r • z) - w x
  let linear (z : E d) := φ (D z)
  haveI : IsFiniteMeasure ((volume : Measure (E d)).restrict A) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  have hlimLinear :
      Tendsto (fun r : ℝ => ∫ z in A, F r z) (𝓝[>] 0) (𝓝 (∫ z in A, linear z)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => B)
    · exact .of_forall fun r => (hF r).aestronglyMeasurable
    · exact .of_forall fun r => .of_forall (hFbound r)
    · exact integrable_const _
    · exact .of_forall fun z => hφ.continuousAt.tendsto.comp (chartZoom_tendsto hD z)
  have hIerror (r : ℝ) (hr : 0 < r) :
      Integrable (error r) (volume.restrict A) := by
    have hmp : MemLp w 1 (volume.restrict (univ : Set (E d))) := by
      rw [Measure.restrict_univ, memLp_one_iff_integrable]
      exact hwI
    have hdil := memLp_comp_domainDilation x hr univ hmp
    rw [preimage_univ, Measure.restrict_univ, memLp_one_iff_integrable] at hdil
    have hwA : Integrable (fun z => w (x + r • z)) (volume.restrict A) :=
      hdil.integrableOn
    exact hwA.sub (integrable_const _)
  have hlimErr :
      Tendsto (fun r : ℝ => ∫ z in A, F r z * error r z) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun r : ℝ => B * ∫ z in A, ‖error r z‖) _ (𝓝 0) by
        simpa only [mul_zero] using
          (tendsto_const_nhds (x := B)).mul (tendsto_integral_chartDensity_error hR hLeb))
    · exact .of_forall fun _ => norm_nonneg _
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with r hr
      rw [← integral_const_mul]
      apply norm_integral_le_of_norm_le ((hIerror r hr).norm.const_mul B)
      exact .of_forall fun z => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hFbound r z) (norm_nonneg _)
  have hlimit :
      Tendsto (fun r : ℝ => (∫ z in A, F r z * error r z) + w x * ∫ z in A, F r z)
        (𝓝[>] 0) (𝓝 (w x * ∫ z in A, linear z)) := by
    simpa only [zero_add] using hlimErr.add ((tendsto_const_nhds (x := w x)).mul hlimLinear)
  have hTarget :
      (∫ y, φ y ∂(ENNReal.ofReal (w x) • Measure.map D volume)) =
      w x * ∫ z in A, linear z := by
    rw [integral_smul_measure, ENNReal.toReal_ofReal (hw₀ x), smul_eq_mul,
      integral_map D.continuous.measurable.aemeasurable hφ.aestronglyMeasurable]
    congr 1
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    by_contra hnon
    have hmem := hSupp (subset_tsupport φ (Function.mem_support.mpr hnon))
    have hnorm : ‖D z‖ ≤ M := by simpa [mem_closedBall, dist_zero_right] using hmem
    exact hz (by
      rw [mem_closedBall, dist_zero_right]
      exact (hDLower z).trans ((mul_le_mul_of_nonneg_left hnorm hK).trans (le_add_of_nonneg_right zero_le_one)))
  rw [hTarget]
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with r hr
  have hr₀ : 0 < r := hr
  rw [integral_chartZoom_weighted_change hf hw hw₀ x hr₀ hφ]
  have hCut : (∫ z in A, F r z * w (x + r • z)) = ∫ z, F r z * w (x + r • z) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    by_contra hnon
    have hproduct : F r z ≠ 0 ∧ w (x + r • z) ≠ 0 :=
      ⟨fun h => hnon (by rw [h, zero_mul]), fun h => hnon (by rw [h, mul_zero])⟩
    have hmem := hSupp (subset_tsupport φ (Function.mem_support.mpr hproduct.1))
    have hnorm : ‖r⁻¹ • (f (x + r • z) - f x)‖ ≤ M := by
      simpa [mem_closedBall, dist_zero_right] using hmem
    have he := hLower (x + r • z) hproduct.2
    have hsub : x + r • z - x = r • z := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hr₀] at he
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr₀, inv_mul_eq_div,
      div_le_iff₀ hr₀] at hnorm
    have hz₁ : r * ‖z‖ ≤ r * (K * M) :=
      he.trans ((mul_le_mul_of_nonneg_left hnorm hK).trans_eq (by ring))
    exact hz (by
      change dist z 0 ≤ R
      rw [dist_zero_right]
      exact ((mul_le_mul_iff_right₀ hr₀).mp hz₁).trans (le_add_of_nonneg_right zero_le_one))
  rw [← hCut, ← integral_const_mul]
  have hIE := (hIerror r hr₀).bdd_mul (hF r).aestronglyMeasurable (.of_forall (hFbound r))
  have hIX : Integrable (fun z => w x * F r z) (volume.restrict A) :=
    (Integrable.of_bound (hF r).aestronglyMeasurable B (.of_forall (hFbound r))).const_mul (w x)
  rw [← integral_add hIE hIX]
  apply integral_congr_ae
  filter_upwards with z
  dsimp only [error, Pi.add_apply]
  ring

end SupportingAnalysis
