module

public import Thesis.Foundation.ModifiedSpectralGap
import Mathlib.MeasureTheory.Integral.Layercake

/-! The uniform scalar logarithmic estimate for the planar spectral-gap levels. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace Thesis

/-- The two-branch potential weight at a modified-gap level. -/
def planarGapLevelWeight (b t : ℝ) : ℝ :=
  min ((1 - t / b) ^ 2) ((1 - t) ^ 2)

private theorem planarGapLevelWeight_sqrt_pos {b t : ℝ} (hb : 0 < b)
    (htb : t ≠ b) (ht₁ : t ≠ 1) : 0 < Real.sqrt (planarGapLevelWeight b t) := by
  apply Real.sqrt_pos.2
  apply lt_min
  · apply sq_pos_of_ne_zero
    intro h
    have he : t / b = 1 := by linarith only [h]
    exact htb (by have he' := (div_eq_iff hb.ne').1 he; simpa only [one_mul] using he')
  · exact sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm ht₁))

private theorem linear_log_lower {α β s : ℝ} (hα : 0 < α) (hβ : 0 < β) (hs : 0 < s) :
    β * (1 - Real.log (β / α)) ≤ α * s - β * Real.log s := by
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (mul_pos hα hs) hβ)) hβ.le
  have hlog : Real.log (α * s / β) = Real.log s - Real.log (β / α) := by
    rw [Real.log_div (mul_ne_zero hα.ne' hs.ne') hβ.ne', Real.log_mul hα.ne' hs.ne',
      Real.log_div hβ.ne' hα.ne']
    ring
  have hmul : β * (α * s / β - 1) = α * s - β := by field_simp [hβ.ne']
  rw [hlog, hmul] at h
  linarith only [h]

/-- Pointwise logarithmic minimization at a regular nonzero level of the gap. -/
theorem planarGapLevel_log_lower {ε c e ℓ b t s Θ : ℝ}
    (hε : 0 < ε) (hc : 0 < c) (he : 0 < e) (hℓ : 0 < ℓ) (hb : 0 < b)
    (ht : 0 < t) (htb : t ≠ b) (ht₁ : t ≠ 1) (hs : 0 < s)
    (hΘ : 2 * e * Real.log (ℓ / s) ≤ Θ) :
    2 * e * t * (Real.log (1 / ε) + (1 + Real.log ℓ) -
      Real.log (2 * e * t / c) + Real.log (Real.sqrt (planarGapLevelWeight b t))) ≤
        (c / ε) * Real.sqrt (planarGapLevelWeight b t) * s + t * Θ := by
  let y := Real.sqrt (planarGapLevelWeight b t)
  have hy : 0 < y := planarGapLevelWeight_sqrt_pos hb htb ht₁
  let α := (c / ε) * y
  let β := 2 * e * t
  have hα : 0 < α := mul_pos (div_pos hc hε) hy
  have hβ : 0 < β := mul_pos (mul_pos (by norm_num) he) ht
  have hMin := linear_log_lower hα hβ hs
  have hLog : Real.log (β / α) =
      Real.log (β / c) - Real.log (1 / ε) - Real.log y := by
    rw [Real.log_div hβ.ne' hα.ne', Real.log_div hβ.ne' hc.ne',
      Real.log_div one_ne_zero hε.ne']
    have hαlog : Real.log α = Real.log c - Real.log ε + Real.log y := by
      change Real.log ((c / ε) * y) = _
      rw [Real.log_mul (div_ne_zero hc.ne' hε.ne') hy.ne', Real.log_div hc.ne' hε.ne']
    rw [hαlog, Real.log_one]
    ring
  have hθ := mul_le_mul_of_nonneg_left hΘ ht.le
  rw [Real.log_div hℓ.ne' hs.ne'] at hθ
  rw [hLog] at hMin
  change β * (Real.log (1 / ε) + (1 + Real.log ℓ) -
    Real.log (β / c) + Real.log y) ≤ α * s + t * Θ
  dsimp only [β]
  nlinarith only [hMin, hθ]

private theorem intervalIntegrable_abs_log_shift (b A : ℝ) :
    IntervalIntegrable (fun t => |Real.log (t - b)|) volume 0 A := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := -b) (b := A - b)).abs.comp_add_right (-b)
  rw [sub_self, show A - b - -b = A by ring] at h
  simpa only [sub_eq_add_neg] using h

private theorem integral_abs_log_shift_le {A M b : ℝ} (hA : 0 ≤ A) (hAM : A ≤ M)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    (∫ t in 0..A, |Real.log (t - b)|) ≤ ∫ y in (-1 : ℝ)..M, |Real.log y| := by
  have hShift : (∫ t in 0..A, |Real.log (t - b)|) =
      ∫ y in (-b)..(A - b), |Real.log y| := by
    simpa only [sub_eq_add_neg, zero_add] using
      (intervalIntegral.integral_comp_add_right (fun y : ℝ => |Real.log y|) (-b) (a := 0) (b := A))
  have hLeft : -b ≤ A - b := by linarith only [hA]
  have hRight : (-1 : ℝ) ≤ M := by linarith only [hA, hAM]
  rw [hShift, intervalIntegral.integral_of_le hLeft, intervalIntegral.integral_of_le hRight]
  apply setIntegral_mono_set ((intervalIntegral.intervalIntegrable_log' (a := -1) (b := M)).abs.1)
    (Eventually.of_forall fun _ => abs_nonneg _)
  exact Eventually.of_forall fun _ hx => ⟨(neg_le_neg hb₁).trans_lt hx.1, hx.2.trans (by linarith only [hAM, hb₀])⟩

private theorem abs_log_gapLevelWeight_le {b t : ℝ}
    (hb₀ : (7 / 12 : ℝ) ≤ b) (hb₁ : b ≤ 1) (htb : t ≠ b) :
    |Real.log (Real.sqrt (planarGapLevelWeight b t))| ≤
      |Real.log (t - b)| + |Real.log (t - 1)| + Real.log (12 / 7) := by
  have hb : 0 < b := (by norm_num : (0 : ℝ) < 7 / 12).trans_le hb₀
  have hMin : |Real.log (Real.sqrt (planarGapLevelWeight b t))| ≤
      |Real.log (1 - t / b)| + |Real.log (1 - t)| := by
    unfold planarGapLevelWeight
    by_cases h : (1 - t / b) ^ 2 ≤ (1 - t) ^ 2
    · rw [min_eq_left h, Real.sqrt_sq_eq_abs, Real.log_abs]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)), Real.sqrt_sq_eq_abs, Real.log_abs]
      exact le_add_of_nonneg_left (abs_nonneg _)
  have hbLog : |Real.log b| ≤ Real.log (12 / 7 : ℝ) := by
    rw [abs_of_nonpos (Real.log_nonpos hb.le hb₁),
      show (12 / 7 : ℝ) = (7 / 12 : ℝ)⁻¹ by norm_num, Real.log_inv]
    exact neg_le_neg (Real.log_le_log (by norm_num) hb₀)
  have hDiv : 1 - t / b = (b - t) / b := by field_simp [hb.ne']
  have hLog : Real.log (1 - t / b) = Real.log (t - b) - Real.log b := by
    rw [hDiv, Real.log_div (sub_ne_zero.mpr (Ne.symm htb)) hb.ne',
      show b - t = -(t - b) by ring, Real.log_neg_eq_log]
  have hAbs : |Real.log (1 - t / b)| ≤ |Real.log (t - b)| + |Real.log b| := by
    rw [hLog, sub_eq_add_neg, ← abs_neg (Real.log b)] 
    exact abs_add_le _ _
  rw [show 1 - t = -(t - 1) by ring, Real.log_neg_eq_log] at hMin
  linarith only [hMin, hAbs, hbLog]

private theorem abs_log_level_multiplier_le {κ c e t : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (he₀ : κ ≤ e) (he₁ : e ≤ 2 * κ) (ht : 0 < t) :
    |Real.log (2 * e * t / c)| ≤
      |Real.log t| + |Real.log (2 * κ / c)| + |Real.log (4 * κ / c)| := by
  have he : 0 < e := hκ.trans_le he₀
  have hpos : 0 < 2 * e / c := div_pos (by positivity) hc
  have hm₀ : 2 * κ / c ≤ 2 * e / c :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he₀ (by norm_num)) hc.le
  have hm₁ : 2 * e / c ≤ 4 * κ / c :=
    div_le_div_of_nonneg_right (by linarith only [he₁]) hc.le
  have hlo := Real.log_le_log (div_pos (by positivity : 0 < 2 * κ) hc) hm₀
  have hhi := Real.log_le_log hpos hm₁
  have habs : |Real.log (2 * e / c)| ≤ |Real.log (2 * κ / c)| + |Real.log (4 * κ / c)| := by
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith only [hlo, neg_abs_le (Real.log (2 * κ / c)), abs_nonneg (Real.log (4 * κ / c))]
    · linarith only [hhi, le_abs_self (Real.log (4 * κ / c)), abs_nonneg (Real.log (2 * κ / c))]
  rw [show 2 * e * t / c = (2 * e / c) * t by ring, Real.log_mul hpos.ne' ht.ne']
  linarith only [abs_add_le (Real.log (2 * e / c)) (Real.log t), habs]

/-- The level-independent summands in the logarithmic error. -/
def levelLogConstant (κ c ℓ : ℝ) : ℝ :=
  |1 + Real.log ℓ| + |Real.log (2 * κ / c)| + |Real.log (4 * κ / c)| + Real.log (12 / 7)

private theorem levelLogConstant_nonneg (κ c ℓ : ℝ) : 0 ≤ levelLogConstant κ c ℓ := by
  unfold levelLogConstant
  exact add_nonneg (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
    (Real.log_nonneg (by norm_num))

/-- An integrated error bound uniform in the smoothing parameter and the level cutoff. -/
def planarGapLevelLogErrorBound (κ c ℓ M : ℝ) : ℝ :=
  4 * κ * M * (M * levelLogConstant κ c ℓ + 3 * ∫ y in (-1 : ℝ)..M, |Real.log y|)

/-- Uniform integration of the planar level lower estimates for the actual two-branch profile. -/
theorem planarGapLevel_integral_log_lower {κ c ℓ M b e ε A : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hℓ : 0 < ℓ) (hε : 0 < ε) (hA : 0 < A) (hAM : A ≤ M)
    (hb₀ : (7 / 12 : ℝ) ≤ b) (hb₁ : b ≤ 1) (he₀ : κ ≤ e) (he₁ : e ≤ 2 * κ)
    (radius Θ : ℝ → ℝ)
    (hLevel : ∀ᵐ t ∂volume.restrict (Ioo 0 A),
      0 < radius t ∧ 2 * e * Real.log (ℓ / radius t) ≤ Θ t)
    (hInt : IntervalIntegrable (fun t =>
      (c / ε) * Real.sqrt (planarGapLevelWeight b t) * radius t + t * Θ t) volume 0 A) :
    e * A ^ 2 * Real.log (1 / ε) - planarGapLevelLogErrorBound κ c ℓ M ≤
      ∫ t in 0..A, (c / ε) * Real.sqrt (planarGapLevelWeight b t) * radius t + t * Θ t := by
  let m (t : ℝ) := ((levelLogConstant κ c ℓ + |Real.log t|) + |Real.log (t - b)|) + |Real.log (t - 1)|
  let α := 2 * e * Real.log (1 / ε)
  let β := 4 * κ * M
  have hb : 0 < b := (by norm_num : (0 : ℝ) < 7 / 12).trans_le hb₀
  have he : 0 < e := hκ.trans_le he₀
  have hM : 0 ≤ M := hA.le.trans hAM
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hm (t : ℝ) : 0 ≤ m t :=
    add_nonneg (add_nonneg (add_nonneg (levelLogConstant_nonneg _ _ _) (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _)
  have hL₀ : IntervalIntegrable (fun t => |Real.log t|) volume 0 A :=
    intervalIntegral.intervalIntegrable_log'.abs
  have hLb := intervalIntegrable_abs_log_shift b A
  have hL₁ := intervalIntegrable_abs_log_shift 1 A
  have hmInt : IntervalIntegrable m volume 0 A :=
    ((intervalIntegrable_const.add hL₀).add hLb).add hL₁
  have hLeading : IntervalIntegrable (fun t : ℝ => α * t) volume 0 A :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hEnv : IntervalIntegrable (fun t => α * t - β * m t) volume 0 A :=
    hLeading.sub (hmInt.const_mul β)
  have hAE : (fun t => α * t - β * m t) ≤ᵐ[volume.restrict (Icc 0 A)]
      fun t => (c / ε) * Real.sqrt (planarGapLevelWeight b t) * radius t + t * Θ t := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hLevel, ae_restrict_mem measurableSet_Ioo,
      (volume.ae_ne b).filter_mono ae_restrict_le, (volume.ae_ne (1 : ℝ)).filter_mono ae_restrict_le]
      with t ht hAt htb ht₁
    have hMin := planarGapLevel_log_lower hε hc he hℓ hb hAt.1 htb ht₁ ht.1 ht.2
    have hLgap := abs_log_gapLevelWeight_le hb₀ hb₁ htb
    have hLscale := abs_log_level_multiplier_le hκ hc he₀ he₁ hAt.1
    have hlow : -m t ≤ (1 + Real.log ℓ) - Real.log (2 * e * t / c) +
        Real.log (Real.sqrt (planarGapLevelWeight b t)) := by
      dsimp only [m, levelLogConstant]
      linarith only [hLgap, hLscale, neg_abs_le (1 + Real.log ℓ),
        le_abs_self (Real.log (2 * e * t / c)), neg_abs_le (Real.log (Real.sqrt (planarGapLevelWeight b t)))]
    have hRate : 2 * e * t ≤ β := by
      calc
        _ ≤ (4 * κ) * t := mul_le_mul_of_nonneg_right (by linarith only [he₁]) hAt.1.le
        _ ≤ β := mul_le_mul_of_nonneg_left (hAt.2.le.trans hAM) (by positivity)
    have hRate₀ : 0 ≤ 2 * e * t := mul_nonneg (mul_nonneg (by norm_num) he.le) hAt.1.le
    have hErr : -β * m t ≤ 2 * e * t *
        ((1 + Real.log ℓ) - Real.log (2 * e * t / c) +
          Real.log (Real.sqrt (planarGapLevelWeight b t))) := by
      calc
        _ ≤ (-(2 * e * t)) * m t := mul_le_mul_of_nonneg_right (neg_le_neg hRate) (hm t)
        _ = 2 * e * t * (-m t) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow hRate₀
    change α * t - β * m t ≤ _
    dsimp only [α]
    nlinarith only [hMin, hErr]
  have hEst := intervalIntegral.integral_mono_ae_restrict hA.le hEnv hInt hAE
  have hConst := levelLogConstant_nonneg κ c ℓ
  have hErrBound : (∫ t in 0..A, m t) ≤
      M * levelLogConstant κ c ℓ + 3 * ∫ y in (-1 : ℝ)..M, |Real.log y| := by
    let I := ∫ y in (-1 : ℝ)..M, |Real.log y|
    have hbL := integral_abs_log_shift_le hA.le hAM hb.le hb₁
    have h₁L := integral_abs_log_shift_le hA.le hAM (b := 1) zero_le_one le_rfl
    have h₀L : (∫ t in 0..A, |Real.log t|) ≤ I := by
      simpa only [sub_zero] using integral_abs_log_shift_le hA.le hAM (b := 0) le_rfl zero_le_one
    dsimp only [m]
    rw [intervalIntegral.integral_add ((intervalIntegrable_const.add hL₀).add hLb) hL₁,
      intervalIntegral.integral_add (intervalIntegrable_const.add hL₀) hLb,
      intervalIntegral.integral_add intervalIntegrable_const hL₀, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul]
    linarith only [h₀L, hbL, h₁L, mul_le_mul_of_nonneg_right hAM hConst]
  rw [intervalIntegral.integral_sub hLeading (hmInt.const_mul β),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_id, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] at hEst
  have hLead : α * (A ^ 2 / 2) = e * A ^ 2 * Real.log (1 / ε) := by dsimp only [α]; ring
  rw [hLead] at hEst
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_left hErrBound hβ) _).trans hEst

/-- The exact weighted layer-cake identity with strictly superlevel regions. -/
theorem weighted_square_layerCake {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f d : X → ℝ) (hf : Measurable f) (hd : Measurable d)
    (hf₀ : ∀ x, 0 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (f x ^ 2 * d x) ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * t) *
        ∫⁻ x in {x | t < f x}, ENNReal.ofReal (d x) ∂μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (d x))
  have htInt (t : ℝ) : IntervalIntegrable (fun s : ℝ => (2 : ℝ) * s) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have htN : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ (2 : ℝ) * s :=
    (ae_restrict_mem measurableSet_Ioi).mono fun _ hs => mul_nonneg (by norm_num) hs.le
  have h := lintegral_comp_eq_lintegral_meas_lt_mul ν (Eventually.of_forall hf₀)
    hf.aemeasurable (fun t _ => htInt t) htN
  have hInt (t : ℝ) : (∫ s in 0..t, (2 : ℝ) * s) = t ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
    ring
  simp_rw [hInt] at h
  have hleft : (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν) =
      ∫⁻ x, ENNReal.ofReal (f x ^ 2 * d x) ∂μ := by
    change (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ.withDensity (fun x => ENNReal.ofReal (d x))) = _
    rw [lintegral_withDensity_eq_lintegral_mul μ hd.ennreal_ofReal (hf.pow_const 2).ennreal_ofReal]
    apply lintegral_congr
    intro x
    change ENNReal.ofReal (d x) * ENNReal.ofReal (f x ^ 2) = ENNReal.ofReal (f x ^ 2 * d x)
    rw [ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  rw [← hleft, h]
  apply lintegral_congr
  intro t
  change (μ.withDensity (fun x => ENNReal.ofReal (d x))) {x | t < f x} * ENNReal.ofReal (2 * t) = _
  rw [withDensity_apply _ (measurableSet_lt measurable_const hf), mul_comm]

/-- Measurability of the extended nonnegative weighted superlevel integral. -/
theorem measurable_weighted_superlevel_lintegral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f d : X → ℝ) :
    Measurable (fun t : ℝ => ∫⁻ x in {x | t < f x}, ENNReal.ofReal (d x) ∂μ) := by
  apply Antitone.measurable
  intro s t hst
  exact lintegral_mono_set (fun _ hx => hst.trans_lt hx)

/-- Truncating the nonnegative square layer-cake integral at a positive
gap retains a lower bound for half the weighted volume integral. -/
theorem weighted_square_layerCake_half_truncated {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f d : X → ℝ) (hf : Measurable f) (hd : Measurable d)
    (hf₀ : ∀ x, 0 ≤ f x) (A : ℝ) :
    let Θ (t : ℝ) := (∫⁻ x in {x | t < f x}, ENNReal.ofReal (d x) ∂μ).toReal
    (∫⁻ t in Ioo 0 A, ENNReal.ofReal (t * Θ t)) ≤
      ∫⁻ x, ENNReal.ofReal ((1 / 2 : ℝ) * f x ^ 2 * d x) ∂μ := by
  intro Θ
  let J (t : ℝ) := ∫⁻ x in {x | t < f x}, ENNReal.ofReal (d x) ∂μ
  have hH : Measurable (fun t => ENNReal.ofReal (2 * t) * J t) :=
    (measurable_const.mul measurable_id).ennreal_ofReal.mul (measurable_weighted_superlevel_lintegral μ f d)
  calc
    (∫⁻ t in Ioo 0 A, ENNReal.ofReal (t * Θ t)) ≤
        ∫⁻ t in Ioo 0 A, ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (2 * t) * J t) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht₀ : 0 ≤ t := ht.1.le
      have h2t : 0 ≤ (2 : ℝ) * t := mul_nonneg (by norm_num) ht₀
      rw [ENNReal.ofReal_mul ht₀, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ)),
        show (1 / 2 : ℝ) * (2 * t) = t by ring]
      change ENNReal.ofReal t * ENNReal.ofReal (J t).toReal ≤ _
      exact mul_le_mul_right ENNReal.ofReal_toReal_le _
    _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (2 * t) * J t) :=
      lintegral_mono_set (fun _ ht => ht.1)
    _ = ENNReal.ofReal (1 / 2) *
        ∫⁻ x, ENNReal.ofReal (f x ^ 2 * d x) ∂μ := by
      rw [lintegral_const_mul _ hH, weighted_square_layerCake μ f d hf hd hf₀]
    _ = ∫⁻ x, ENNReal.ofReal ((1 / 2 : ℝ) * f x ^ 2 * d x) ∂μ := by
      have hMeas : Measurable (fun x => ENNReal.ofReal (f x ^ 2 * d x)) :=
        ((hf.pow_const 2).mul hd).ennreal_ofReal
      rw [← lintegral_const_mul _ hMeas]
      apply lintegral_congr
      intro x
      rw [mul_assoc, ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]

end Thesis
