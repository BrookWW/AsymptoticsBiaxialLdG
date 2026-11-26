module

public import SupportingAnalysis.Measure.Differentiation
public import SupportingAnalysis.Basics

/-! Vague blow-ups of the part of an energy measure singular to the reference measure. -/

public section

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology

set_option autoImplicit false

namespace SupportingAnalysis

theorem blownUpMeasure_closedBall_zero {m d : ℕ} (x : E m) {r : ℝ} (hr : 0 < r)
    (R : ℝ) (μ : Measure (E m)) :
    @blownUpMeasure m d x r μ (closedBall 0 R) =
      ENNReal.ofReal (r ^ (-(d : ℤ))) * μ (closedBall x (R * r)) := by
  have hm : Measurable (fun y : E m => r⁻¹ • (y - x)) := by fun_prop
  rw [blownUpMeasure, Measure.smul_apply, Measure.map_apply hm measurableSet_closedBall]
  rw [smul_eq_mul]
  congr 2
  ext y
  simp only [mem_preimage, mem_closedBall, dist_eq_norm, sub_zero, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  simpa only [mul_comm r R] using (inv_mul_le_iff₀ hr :
    r⁻¹ * ‖y - x‖ ≤ R ↔ ‖y - x‖ ≤ r * R)

theorem blownUpMeasure_isFiniteMeasure {m d : ℕ} (x : E m) (r : ℝ)
    (μ : Measure (E m)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (@blownUpMeasure m d x r μ) := by
  unfold blownUpMeasure
  letI := μ.isFiniteMeasure_map (fun y => r⁻¹ • (y - x))
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

theorem tendsto_const_mul_nhdsGT_zero {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [mul_zero, id_eq] using
      (tendsto_const_nhds (x := R)).mul (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos hR (show 0 < r from hr)

theorem tendsto_blownUpMeasure_closedBall_of_normalizedMass {m d : ℕ}
    (x : E m) (ρ : Measure (E m)) {R : ℝ} (hR : 0 < R)
    (hD : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-(d : ℤ))) * ρ (closedBall x r))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => @blownUpMeasure m d x r ρ (closedBall 0 R))
      (𝓝[>] 0) (𝓝 0) := by
  have hc := hD.comp (tendsto_const_mul_nhdsGT_zero hR)
  have ht : Tendsto (fun r : ℝ => ENNReal.ofReal (R ^ (d : ℤ)) *
      (ENNReal.ofReal ((R * r) ^ (-(d : ℤ))) * ρ (closedBall x (R * r))))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      ENNReal.Tendsto.const_mul hc (a := ENNReal.ofReal (R ^ (d : ℤ)))
        (Or.inr ENNReal.ofReal_ne_top)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrpos : 0 < r := hr
  have hz : (R ^ (d : ℤ)) * (R * r) ^ (-(d : ℤ)) = r ^ (-(d : ℤ)) := by
    rw [mul_zpow, ← mul_assoc, ← zpow_add₀ (ne_of_gt hR)]
    simp
  rw [blownUpMeasure_closedBall_zero x hrpos, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hz]

theorem vagueOn_blownUpMeasure_zero_of_normalizedMass {m d : ℕ}
    (x : E m) (ρ : Measure (E m)) [IsFiniteMeasure ρ]
    (hD : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-(d : ℤ))) * ρ (closedBall x r))
      (𝓝[>] 0) (𝓝 0)) :
    VagueOn univ (𝓝[>] (0 : ℝ)) (fun r => @blownUpMeasure m d x r ρ) 0 := by
  intro φ hφ hcomp _
  obtain ⟨R, hR, hRφ⟩ := hcomp.isBounded.subset_closedBall_lt 0 (0 : E m)
  obtain ⟨B, hB, hBφ⟩ :=
    (hcomp.image hφ.norm).isBounded.subset_closedBall_lt 0 (0 : ℝ)
  have hφsup : ∀ y : E m, ‖φ y‖ ≤ B := by
    intro y
    by_cases hy : y ∈ tsupport φ
    · have hb := hBφ (mem_image_of_mem _ hy)
      simpa only [mem_closedBall, Real.dist_eq, sub_zero, abs_norm] using hb
    · have hy0 : φ y = 0 := by
        by_contra hne
        exact hy (subset_tsupport _ (Function.mem_support.mpr hne))
      simp [hy0, hB.le]
  have hMt := tendsto_blownUpMeasure_closedBall_of_normalizedMass x ρ hR hD
  have hRt : Tendsto (fun r : ℝ => (@blownUpMeasure m d x r ρ (closedBall 0 R)).toReal)
      (𝓝[>] 0) (𝓝 0) := by
    change Tendsto (ENNReal.toReal ∘ fun r =>
      @blownUpMeasure m d x r ρ (closedBall 0 R)) (𝓝[>] 0) (𝓝 0)
    simpa only [ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (x := 0) ENNReal.zero_ne_top).tendsto.comp hMt
  simp only [integral_zero_measure]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
  · intro r
    let μr := @blownUpMeasure m d x r ρ
    letI := blownUpMeasure_isFiniteMeasure (d := d) x r ρ
    change ‖∫ y, φ y ∂μr‖ ≤ B * (μr (closedBall 0 R)).toReal
    have hzero (y : E m) (hy : y ∉ closedBall 0 R) : φ y = 0 := by
      by_contra hne
      exact hy (hRφ (subset_tsupport _ (Function.mem_support.mpr hne)))
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    exact norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top μr _)
      (Eventually.of_forall hφsup)
  · simpa only [mul_zero] using hRt.const_mul B

theorem eventually_bounded_normalized_closedBall_mass_of_vague_blowup {m d : ℕ}
    (x : E m) (ν : Measure (E m)) [IsFiniteMeasure ν] (τ : Measure (E m))
    (hV : VagueOn univ (𝓝[>] (0 : ℝ)) (fun r => @blownUpMeasure m d x r ν) τ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (r ^ (-(d : ℤ))) * ν (closedBall x r) ≤ C := by
  obtain ⟨φ, hφsup, hφone, hφrange⟩ := exists_tsupport_one_of_isOpen_isClosed
    (s := ball (0 : E m) 2) (t := closedBall 0 1) isOpen_ball
    (isCompact_closedBall 0 2 |>.of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall))
    isClosed_closedBall (closedBall_subset_ball (by norm_num))
  have hφc : HasCompactSupport (φ : E m → ℝ) :=
    (isCompact_closedBall 0 2).of_isClosed_subset (isClosed_tsupport _)
      (hφsup.trans ball_subset_closedBall)
  let C : ℝ := max 0 (∫ z, φ z ∂τ) + 1
  have hClt : (∫ z, φ z ∂τ) < C := by
    exact (le_max_right 0 _).trans_lt (lt_add_one _)
  have hConv := hV φ φ.continuous hφc (subset_univ _)
  have hb := (tendsto_order.1 hConv).2 C hClt
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hb] with r hr hlt
  have hrpos : 0 < r := hr
  have heq : @blownUpMeasure m d x r ν (closedBall 0 1) =
      ENNReal.ofReal (r ^ (-(d : ℤ))) * ν (closedBall x r) := by
    simpa only [one_mul] using blownUpMeasure_closedBall_zero (d := d) x hrpos 1 ν
  rw [← heq]
  let νr := @blownUpMeasure m d x r ν
  letI : IsFiniteMeasure νr := blownUpMeasure_isFiniteMeasure x r ν
  have hmass : (νr (closedBall (0 : E m) 1)).toReal ≤ ∫ z, φ z ∂νr := by
    calc
      _ = (∫ z in closedBall (0 : E m) 1, φ z ∂νr) := by
        rw [setIntegral_congr_fun measurableSet_closedBall hφone]
        simp [measureReal_def]
      _ ≤ _ := setIntegral_le_integral
        (φ.continuous.integrable_of_hasCompactSupport hφc)
        (Eventually.of_forall fun z => (hφrange z).1)
  rw [← ENNReal.ofReal_toReal (measure_lt_top νr _).ne]
  exact ENNReal.ofReal_le_ofReal (hmass.trans hlt.le)


theorem blownUpMeasure_add {m d : ℕ} (x : E m) (r : ℝ) (ρ ν : Measure (E m)) :
    @blownUpMeasure m d x r (ρ + ν) = @blownUpMeasure m d x r ρ + @blownUpMeasure m d x r ν := by
  have hm : Measurable (fun y : E m => r⁻¹ • (y - x)) := by fun_prop
  simp only [blownUpMeasure, Measure.map_add ρ ν hm, smul_add]

theorem vagueOn_blownUpMeasure_add_left_zero {m d : ℕ}
    (x : E m) (ρ ν : Measure (E m)) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (τ : Measure (E m))
    (hρ : VagueOn univ (𝓝[>] (0 : ℝ)) (fun r => @blownUpMeasure m d x r ρ) 0)
    (hν : VagueOn univ (𝓝[>] (0 : ℝ)) (fun r => @blownUpMeasure m d x r ν) τ) :
    VagueOn univ (𝓝[>] (0 : ℝ)) (fun r => @blownUpMeasure m d x r (ρ + ν)) τ := by
  intro φ hφ hcomp hsup
  have ht := (hρ φ hφ hcomp hsup).add (hν φ hφ hcomp hsup)
  simp only [integral_zero_measure, zero_add] at ht
  apply ht.congr'
  filter_upwards with r
  letI := blownUpMeasure_isFiniteMeasure (d := d) x r ρ
  letI := blownUpMeasure_isFiniteMeasure (d := d) x r ν
  rw [blownUpMeasure_add, integral_add_measure
    (hφ.integrable_of_hasCompactSupport hcomp) (hφ.integrable_of_hasCompactSupport hcomp)]

end SupportingAnalysis
