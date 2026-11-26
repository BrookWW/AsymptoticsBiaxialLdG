module

public import Thesis.Foundation.SpectralProjection
import Thesis.StressEnergy

/-! The manuscript's polynomial smoothing of the minimum spectral gap. -/

@[expose] public section

noncomputable section

open Filter Metric Set Topology
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace Thesis

abbrev GapSmoothingParameter := Ioo (0 : ℝ) (1 / 2)

/-- The smaller consecutive eigenvalue gap in units of the vacuum radius. -/
def normalizedSpectralGap (a : BulkCoefficients) (A : S0) : ℝ :=
  (vacuumRadius a)⁻¹ * min (orderedEigenvalue A 0 - orderedEigenvalue A 1)
    (orderedEigenvalue A 1 - orderedEigenvalue A 2)

/-- The central smoothing polynomial on the ratio variable. -/
def spectralGapBeta (τ : GapSmoothingParameter) (r : ℝ) : ℝ :=
  (r - 1 / 2) ^ 6 / (24 * τ.val ^ 5) - 5 * (r - 1 / 2) ^ 2 / (8 * τ.val) +
    (6 - 5 * τ.val) / 12

/-- The piecewise smooth replacement of the minimum of a ratio and its complement. -/
def spectralGapProfile (τ : GapSmoothingParameter) (r : ℝ) : ℝ :=
  if r < 1 / 2 - τ.val then r
  else if r ≤ 1 / 2 + τ.val then spectralGapBeta τ r
  else 1 - r

/-- The coefficient comparing the modified and minimum gaps. -/
def spectralGapSmoothingFactor (τ : GapSmoothingParameter) : ℝ := (6 - 5 * τ.val) / 6

/-- The literal modified spectral gap, with the designated value at the zero tensor. -/
def modifiedSpectralGap (a : BulkCoefficients) (τ : GapSmoothingParameter) (A : S0) : ℝ :=
  if A = 0 then 0 else
    let s := orderedEigenvalue A 0 - orderedEigenvalue A 2
    let r := (orderedEigenvalue A 1 - orderedEigenvalue A 2) / s
    (vacuumRadius a)⁻¹ * (s * spectralGapProfile τ r)

theorem spectralGapSmoothingFactor_pos (τ : GapSmoothingParameter) :
    0 < spectralGapSmoothingFactor τ := by
  unfold spectralGapSmoothingFactor
  linarith [τ.property.2]

theorem spectralGapSmoothingFactor_le_one (τ : GapSmoothingParameter) :
    spectralGapSmoothingFactor τ ≤ 1 := by
  unfold spectralGapSmoothingFactor
  linarith [τ.property.1]

private theorem beta_symmetric (τ : GapSmoothingParameter) (r : ℝ) :
    spectralGapBeta τ (1 - r) = spectralGapBeta τ r := by
  unfold spectralGapBeta
  ring

private theorem beta_comparison_left (τ : GapSmoothingParameter) {z : ℝ} (hz : z ∈ Icc 0 1) :
    spectralGapSmoothingFactor τ * (1 / 2 - τ.val * z) ≤ spectralGapBeta τ (1 / 2 - τ.val * z) ∧
      spectralGapBeta τ (1 / 2 - τ.val * z) ≤ 1 / 2 - τ.val * z := by
  have ht : 0 < τ.val := τ.property.1
  have hu : τ.val < 1 / 2 := τ.property.2
  have hpoly : 0 ≤ z ^ 5 - 15 * z + 14 := by
    have hprod : 0 ≤ (1 - z) * (14 - z - z ^ 2 - z ^ 3 - z ^ 4) := by
      apply mul_nonneg (sub_nonneg.mpr hz.2)
      linarith only [hz.2, pow_le_one₀ hz.1 hz.2 (n := 2), pow_le_one₀ hz.1 hz.2 (n := 3),
        pow_le_one₀ hz.1 hz.2 (n := 4)]
    calc
      _ ≤ (1 - z) * (14 - z - z ^ 2 - z ^ 3 - z ^ 4) := hprod
      _ = _ := by ring
  have hz₀ : 0 ≤ z := hz.1
  have hzpoly : 0 ≤ z ^ 3 + 3 * z ^ 2 + 6 * z + 10 := by positivity
  constructor
  · apply sub_nonneg.mp
    have he : spectralGapBeta τ (1 / 2 - τ.val * z) -
        spectralGapSmoothingFactor τ * (1 / 2 - τ.val * z) =
      τ.val * z * (z ^ 5 - 15 * z - 20 * τ.val + 24) / 24 := by
      unfold spectralGapBeta spectralGapSmoothingFactor
      field_simp [ht.ne']
      ring
    rw [he]
    have hTerm : 0 ≤ z ^ 5 - 15 * z - 20 * τ.val + 24 := by linarith only [hpoly, hu]
    exact div_nonneg (mul_nonneg (mul_nonneg ht.le hz.1) hTerm) (by norm_num)
  · apply sub_nonneg.mp
    have he : (1 / 2 - τ.val * z) - spectralGapBeta τ (1 / 2 - τ.val * z) =
      τ.val * (1 - z) ^ 3 * (z ^ 3 + 3 * z ^ 2 + 6 * z + 10) / 24 := by
      unfold spectralGapBeta
      field_simp [ht.ne']
      ring
    rw [he]
    exact div_nonneg (mul_nonneg (mul_nonneg ht.le (pow_nonneg (sub_nonneg.mpr hz.2) _)) hzpoly) (by norm_num)

private theorem beta_comparison_central (τ : GapSmoothingParameter) {r : ℝ}
    (hL : 1 / 2 - τ.val ≤ r) (hU : r ≤ 1 / 2 + τ.val) :
    spectralGapSmoothingFactor τ * min r (1 - r) ≤ spectralGapBeta τ r ∧
      spectralGapBeta τ r ≤ min r (1 - r) := by
  have lowerSide (w : ℝ) (hw₀ : 1 / 2 - τ.val ≤ w) (hw₁ : w ≤ 1 / 2) :
      spectralGapSmoothingFactor τ * w ≤ spectralGapBeta τ w ∧ spectralGapBeta τ w ≤ w := by
    let z := (1 / 2 - w) / τ.val
    have hz : z ∈ Icc 0 1 :=
      ⟨div_nonneg (sub_nonneg.mpr hw₁) τ.property.1.le,
        (div_le_one τ.property.1).mpr (by linarith only [hw₀])⟩
    have h := beta_comparison_left τ hz
    have he : 1 / 2 - τ.val * z = w := by
      dsimp only [z]
      field_simp [τ.property.1.ne']
      ring
    rwa [he] at h
  by_cases h : r ≤ 1 / 2
  · rw [min_eq_left (by linarith only [h])]
    exact lowerSide r hL h
  · rw [min_eq_right (by linarith only [lt_of_not_ge h]), ← beta_symmetric τ r]
    exact lowerSide (1 - r) (by linarith only [hU]) (by linarith only [lt_of_not_ge h])

theorem spectralGapProfile_comparison (τ : GapSmoothingParameter) {r : ℝ} (hr : r ∈ Icc 0 1) :
    spectralGapSmoothingFactor τ * min r (1 - r) ≤ spectralGapProfile τ r ∧
      spectralGapProfile τ r ≤ min r (1 - r) := by
  unfold spectralGapProfile
  split_ifs with hL hU
  · have h : r ≤ 1 - r := by linarith [τ.property.1]
    rw [min_eq_left h]
    exact ⟨mul_le_of_le_one_left hr.1 (spectralGapSmoothingFactor_le_one τ), le_rfl⟩
  · exact beta_comparison_central τ (le_of_not_gt hL) hU
  · have h : 1 - r ≤ r := by linarith [τ.property.1, lt_of_not_ge hU]
    rw [min_eq_right h]
    exact ⟨mul_le_of_le_one_left (sub_nonneg.mpr hr.2) (spectralGapSmoothingFactor_le_one τ), le_rfl⟩

private theorem ordered_eigenvalue_zero (i : Fin 3) : orderedEigenvalue (0 : S0) i = 0 := by
  have h := (norm_sq_eq_trace_sq (0 : S0)).trans (trace_pow_eq_sum_orderedEigenvalue_pow (0 : S0) 2)
  simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Fin.sum_univ_three] at h
  have h0 : orderedEigenvalue (0 : S0) 0 = 0 := by
    nlinarith only [h, sq_nonneg (orderedEigenvalue (0 : S0) 1), sq_nonneg (orderedEigenvalue (0 : S0) 2)]
  have h1 : orderedEigenvalue (0 : S0) 1 = 0 := by
    nlinarith only [h, sq_nonneg (orderedEigenvalue (0 : S0) 0), sq_nonneg (orderedEigenvalue (0 : S0) 2)]
  have h2 : orderedEigenvalue (0 : S0) 2 = 0 := by
    nlinarith only [h, sq_nonneg (orderedEigenvalue (0 : S0) 0), sq_nonneg (orderedEigenvalue (0 : S0) 1)]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem ordered_eigenwidth_pos_of_ne_zero {A : S0} (hA : A ≠ 0) :
    0 < orderedEigenvalue A 0 - orderedEigenvalue A 2 := by
  have h₁ := orderedEigenvalue_antitone A (by decide : (0 : Fin 3) ≤ 1)
  have h₂ := orderedEigenvalue_antitone A (by decide : (1 : Fin 3) ≤ 2)
  by_contra h
  push Not at h
  have htrace := sum_orderedEigenvalue A
  simp only [Fin.sum_univ_three] at htrace
  have e₀ : orderedEigenvalue A 0 = 0 := by linarith only [h,h₁,h₂,htrace]
  have e₁ : orderedEigenvalue A 1 = 0 := by linarith only [h,h₁,h₂,htrace]
  have e₂ : orderedEigenvalue A 2 = 0 := by linarith only [h,h₁,h₂,htrace]
  have hnorm := (norm_sq_eq_trace_sq A).trans (trace_pow_eq_sum_orderedEigenvalue_pow A 2)
  simp [Fin.sum_univ_three, e₀, e₁, e₂] at hnorm
  exact hA hnorm

theorem normalizedSpectralGap_nonneg (a : BulkCoefficients) (A : S0) :
    0 ≤ normalizedSpectralGap a A :=
  mul_nonneg (inv_nonneg.mpr (vacuumRadius_pos a).le) (le_min
    (sub_nonneg.mpr (orderedEigenvalue_antitone A (by decide : (0 : Fin 3) ≤ 1)))
    (sub_nonneg.mpr (orderedEigenvalue_antitone A (by decide : (1 : Fin 3) ≤ 2))))

/-- The modified gap lies between the minimum gap and its prescribed lower multiple. -/
theorem modifiedSpectralGap_comparison (a : BulkCoefficients) (τ : GapSmoothingParameter) (A : S0) :
    spectralGapSmoothingFactor τ * normalizedSpectralGap a A ≤ modifiedSpectralGap a τ A ∧
      modifiedSpectralGap a τ A ≤ normalizedSpectralGap a A := by
  by_cases hA : A = 0
  · subst A
    simp [modifiedSpectralGap, normalizedSpectralGap, ordered_eigenvalue_zero]
  let s := orderedEigenvalue A 0 - orderedEigenvalue A 2
  let r := (orderedEigenvalue A 1 - orderedEigenvalue A 2) / s
  have hs : 0 < s := ordered_eigenwidth_pos_of_ne_zero hA
  have h₁ := orderedEigenvalue_antitone A (by decide : (0 : Fin 3) ≤ 1)
  have h₂ := orderedEigenvalue_antitone A (by decide : (1 : Fin 3) ≤ 2)
  have hr : r ∈ Icc 0 1 :=
    ⟨div_nonneg (sub_nonneg.mpr h₂) hs.le, (div_le_one hs).2 (by linarith only [h₁])⟩
  have hright : s * r = orderedEigenvalue A 1 - orderedEigenvalue A 2 := by
    dsimp only [r]
    field_simp [hs.ne']
  have hleft : s * (1 - r) = orderedEigenvalue A 0 - orderedEigenvalue A 1 := by
    rw [mul_sub, mul_one, hright]
    dsimp only [s]
    ring
  have hg : normalizedSpectralGap a A = (vacuumRadius a)⁻¹ * (s * min r (1 - r)) := by
    unfold normalizedSpectralGap
    rw [mul_min_of_nonneg _ _ hs.le, hright, hleft, min_comm]
  have hm : modifiedSpectralGap a τ A = (vacuumRadius a)⁻¹ * (s * spectralGapProfile τ r) := by
    rw [modifiedSpectralGap, if_neg hA]
  obtain ⟨hl, hu⟩ := spectralGapProfile_comparison τ hr
  have hR : 0 ≤ (vacuumRadius a)⁻¹ := inv_nonneg.mpr (vacuumRadius_pos a).le
  rw [hg, hm]
  constructor
  · calc
      _ = (vacuumRadius a)⁻¹ * (s * (spectralGapSmoothingFactor τ * min r (1 - r))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl hs.le) hR
  · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu hs.le) hR

theorem modifiedSpectralGap_pos_iff (a : BulkCoefficients) (τ : GapSmoothingParameter) (A : S0) :
    0 < modifiedSpectralGap a τ A ↔ A ∈ simpleSpectrumLocus := by
  have hbase : 0 < normalizedSpectralGap a A ↔ A ∈ simpleSpectrumLocus := by
    rw [normalizedSpectralGap, mul_pos_iff_of_pos_left (inv_pos.mpr (vacuumRadius_pos a)),
      lt_min_iff, simpleSpectrumLocus]
    simp only [mem_setOf_eq, sub_pos]
  obtain ⟨hl, hu⟩ := modifiedSpectralGap_comparison a τ A
  constructor
  · intro h
    exact hbase.mp (h.trans_le hu)
  · intro h
    exact (mul_pos (spectralGapSmoothingFactor_pos τ) (hbase.mpr h)).trans_le hl

private theorem integral_max_pow (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    (∫ x in 0..t, ((n : ℝ) + 1) * (max x 0) ^ n) = (max t 0) ^ (n + 1) := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht]
    calc
      _ = ∫ x in 0..t, ((n : ℝ) + 1) * x ^ n := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc 0 t := by rwa [uIcc_of_le ht] at hx
        change ((n : ℝ) + 1) * (max x 0) ^ n = ((n : ℝ) + 1) * x ^ n
        rw [max_eq_left hx'.1]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
        field_simp
  · rw [max_eq_right (le_of_not_ge ht), zero_pow (Nat.succ_ne_zero _)]
    calc
      _ = ∫ _x : ℝ in 0..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc t 0 := by rwa [uIcc_comm, uIcc_of_le (le_of_not_ge ht)] at hx
        change ((n : ℝ) + 1) * (max x 0) ^ n = 0
        rw [max_eq_right hx'.2, zero_pow hn, mul_zero]
      _ = _ := intervalIntegral.integral_zero

private theorem hasDerivAt_max_pow (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    HasDerivAt (fun x : ℝ => (max x 0) ^ (n + 1)) (((n : ℝ) + 1) * (max t 0) ^ n) t := by
  let g (x : ℝ) := ((n : ℝ) + 1) * (max x 0) ^ n
  have hg : Continuous g := continuous_const.mul ((continuous_id.max continuous_const).pow n)
  have hd := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun x => (integral_max_pow n hn x).symm)

private theorem contDiff_max_zero_cube : ContDiff ℝ 2 (fun x : ℝ => (max x 0) ^ 3) := by
  have hsq : ContDiff ℝ 1 (fun x : ℝ => (max x 0) ^ 2) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x => (hasDerivAt_max_pow 1 (by decide) x).differentiableAt, ?_⟩
    have he : deriv (fun x : ℝ => (max x 0) ^ 2) = fun x => 2 * max x 0 := by
      funext x
      simpa only [Nat.cast_one, one_add_one_eq_two, pow_one] using (hasDerivAt_max_pow 1 (by decide) x).deriv
    rw [he]
    exact continuous_const.mul (continuous_id.max continuous_const)
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_max_pow 2 (by decide) x).differentiableAt, by simp, ?_⟩
  have he : deriv (fun x : ℝ => (max x 0) ^ 3) = fun x => 3 * (max x 0) ^ 2 := by
    funext x
    have hx := (hasDerivAt_max_pow 2 (by decide) x).deriv
    norm_num at hx ⊢
    exact hx
  rw [he]
  exact contDiff_const.mul hsq

/-- The globally patched scalar profile is twice continuously differentiable. -/
theorem contDiff_spectralGapProfile (τ : GapSmoothingParameter) : ContDiff ℝ 2 (spectralGapProfile τ) := by
  let L (r : ℝ) := (1 / 2 - r) / τ.val
  let R (r : ℝ) := (r - 1 / 2) / τ.val
  let P (z : ℝ) := z ^ 3 + 3 * z ^ 2 + 6 * z + 10
  have hp : ContDiff ℝ 2 P := by dsimp only [P]; fun_prop
  have hl : ContDiff ℝ 2 L := (contDiff_const.sub contDiff_id).div_const _
  have hr : ContDiff ℝ 2 R := (contDiff_id.sub contDiff_const).div_const _
  have hl₃ : ContDiff ℝ 2 (fun r => (max (L r - 1) 0) ^ 3) :=
    contDiff_max_zero_cube.comp (hl.sub contDiff_const)
  have hr₃ : ContDiff ℝ 2 (fun r => (max (R r - 1) 0) ^ 3) :=
    contDiff_max_zero_cube.comp (hr.sub contDiff_const)
  have hPL : ContDiff ℝ 2 (fun r => P (L r)) := hp.comp hl
  have hPR : ContDiff ℝ 2 (fun r => P (R r)) := hp.comp hr
  have hb : ContDiff ℝ 2 (spectralGapBeta τ) := by unfold spectralGapBeta; fun_prop
  have he : spectralGapProfile τ = fun r => spectralGapBeta τ r -
      τ.val / 24 * (max (L r - 1) 0) ^ 3 * P (L r) -
      τ.val / 24 * (max (R r - 1) 0) ^ 3 * P (R r) := by
    funext r
    unfold spectralGapProfile
    split_ifs with hL hU
    · have hpL : 0 ≤ L r - 1 := sub_nonneg.mpr
        ((one_le_div τ.property.1).2 (by linarith only [hL]))
      have hpR : R r - 1 ≤ 0 := sub_nonpos.mpr
        ((div_le_one τ.property.1).2 (by linarith only [hL, τ.property.1]))
      simp only [max_eq_left hpL, max_eq_right hpR, zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero, zero_mul, sub_zero]
      dsimp only [L, P]
      unfold spectralGapBeta
      field_simp [τ.property.1.ne']
      ring
    · have hpL : L r - 1 ≤ 0 := sub_nonpos.mpr
        ((div_le_one τ.property.1).2 (by linarith only [le_of_not_gt hL]))
      have hpR : R r - 1 ≤ 0 := sub_nonpos.mpr
        ((div_le_one τ.property.1).2 (by linarith only [hU]))
      simp only [max_eq_right hpL, max_eq_right hpR, zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero, zero_mul, sub_zero]
    · have hpL : L r - 1 ≤ 0 := sub_nonpos.mpr
        ((div_le_one τ.property.1).2 (by linarith only [le_of_not_gt hL]))
      have hpR : 0 ≤ R r - 1 := sub_nonneg.mpr
        ((one_le_div τ.property.1).2 (by linarith only [lt_of_not_ge hU]))
      simp only [max_eq_right hpL, max_eq_left hpR, zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero, zero_mul, sub_zero]
      dsimp only [R, P]
      unfold spectralGapBeta
      field_simp [τ.property.1.ne']
      ring
  rw [he]
  exact (hb.sub ((contDiff_const.mul hl₃).mul hPL)).sub ((contDiff_const.mul hr₃).mul hPR)

theorem continuous_normalizedSpectralGap (a : BulkCoefficients) : Continuous (normalizedSpectralGap a) := by
  unfold normalizedSpectralGap
  exact continuous_const.mul
    (((continuous_orderedEigenvalue 0).sub (continuous_orderedEigenvalue 1)).min
      ((continuous_orderedEigenvalue 1).sub (continuous_orderedEigenvalue 2)))

theorem modifiedSpectralGap_nonneg (a : BulkCoefficients) (τ : GapSmoothingParameter) (A : S0) :
    0 ≤ modifiedSpectralGap a τ A :=
  (mul_nonneg (spectralGapSmoothingFactor_pos τ).le (normalizedSpectralGap_nonneg a A)).trans
    (modifiedSpectralGap_comparison a τ A).1

theorem continuous_modifiedSpectralGap (a : BulkCoefficients) (τ : GapSmoothingParameter) :
    Continuous (modifiedSpectralGap a τ) := by
  apply continuous_iff_continuousAt.mpr
  intro A
  by_cases hA : A = 0
  · subst A
    have hN : Tendsto (normalizedSpectralGap a) (𝓝 (0 : S0)) (𝓝 0) := by
      have h := (continuous_normalizedSpectralGap a).continuousAt (x := (0 : S0))
      simpa only [ContinuousAt, normalizedSpectralGap, ordered_eigenvalue_zero, sub_zero,
        min_self, mul_zero] using h
    have h := squeeze_zero' (Eventually.of_forall (modifiedSpectralGap_nonneg a τ))
      (Eventually.of_forall fun B => (modifiedSpectralGap_comparison a τ B).2) hN
    simpa only [ContinuousAt, modifiedSpectralGap, if_true] using h
  let s (B : S0) := orderedEigenvalue B 0 - orderedEigenvalue B 2
  let t (B : S0) := orderedEigenvalue B 1 - orderedEigenvalue B 2
  have hs : Continuous s := (continuous_orderedEigenvalue 0).sub (continuous_orderedEigenvalue 2)
  have ht : Continuous t := (continuous_orderedEigenvalue 1).sub (continuous_orderedEigenvalue 2)
  have hrat : ContinuousAt (fun B => t B / s B) A :=
    ht.continuousAt.div hs.continuousAt (ordered_eigenwidth_pos_of_ne_zero hA).ne'
  have hprof : ContinuousAt (fun B => spectralGapProfile τ (t B / s B)) A :=
    (contDiff_spectralGapProfile τ).continuous.continuousAt.comp hrat
  have h : ContinuousAt (fun B => (vacuumRadius a)⁻¹ * (s B * spectralGapProfile τ (t B / s B))) A :=
    continuousAt_const.mul (hs.continuousAt.mul hprof)
  apply h.congr_of_eventuallyEq
  filter_upwards [continuousAt_id.eventually_ne hA] with B hB
  change B ≠ 0 at hB
  rw [modifiedSpectralGap, if_neg hB]

/-- The modified tensor gap is twice continuously differentiable on its positive locus. -/
theorem contDiffOn_modifiedSpectralGap (a : BulkCoefficients) (τ : GapSmoothingParameter) :
    ContDiffOn ℝ 2 (modifiedSpectralGap a τ) simpleSpectrumLocus := by
  have hval (i : Fin 3) : ContDiffOn ℝ 2 (fun A => orderedEigenvalue A i) simpleSpectrumLocus :=
    (contDiffOn_orderedEigenvalue i).of_le (by decide)
  have hwidth : ContDiffOn ℝ 2
      (fun A => orderedEigenvalue A 0 - orderedEigenvalue A 2) simpleSpectrumLocus :=
    (hval 0).sub (hval 2)
  have hzero : (0 : S0) ∉ simpleSpectrumLocus := by
    simp [simpleSpectrumLocus, ordered_eigenvalue_zero]
  have hne (A : S0) (hA : A ∈ simpleSpectrumLocus) : A ≠ 0 := fun h => hzero (h ▸ hA)
  have hratio : ContDiffOn ℝ 2
      (fun A => (orderedEigenvalue A 1 - orderedEigenvalue A 2) /
        (orderedEigenvalue A 0 - orderedEigenvalue A 2)) simpleSpectrumLocus :=
    ((hval 1).sub (hval 2)).div hwidth (fun A hA => (ordered_eigenwidth_pos_of_ne_zero (hne A hA)).ne')
  have hpoly := (contDiff_spectralGapProfile τ).comp_contDiffOn hratio
  refine ((hwidth.mul hpoly).const_smul ((vacuumRadius a)⁻¹)).congr ?_
  intro A hA
  rw [modifiedSpectralGap, if_neg (hne A hA)]
  rfl

private theorem beta_midpoint_error (τ : GapSmoothingParameter) {r : ℝ}
    (hL : 1 / 2 - τ.val ≤ r) (hU : r ≤ 1 / 2 + τ.val) :
    0 ≤ spectralGapSmoothingFactor τ / 2 - spectralGapBeta τ r ∧
      spectralGapSmoothingFactor τ / 2 - spectralGapBeta τ r ≤ |r - 1 / 2| := by
  have hSide (w : ℝ) (hw₀ : 1 / 2 - τ.val ≤ w) (hw₁ : w ≤ 1 / 2) :
      0 ≤ spectralGapSmoothingFactor τ / 2 - spectralGapBeta τ w ∧
        spectralGapSmoothingFactor τ / 2 - spectralGapBeta τ w ≤ 1 / 2 - w := by
    let z := (1 / 2 - w) / τ.val
    have hz₀ : 0 ≤ z := div_nonneg (sub_nonneg.mpr hw₁) τ.property.1.le
    have hz₁ : z ≤ 1 := (div_le_one τ.property.1).2 (by linarith only [hw₀])
    have hs : τ.val * z = 1 / 2 - w := by dsimp only [z]; field_simp [τ.property.1.ne']
    have hw : w = 1 / 2 - τ.val * z := by linarith only [hs]
    have hFormula : spectralGapSmoothingFactor τ / 2 - spectralGapBeta τ w =
        τ.val * (5 / 8 * z ^ 2 - z ^ 6 / 24) := by
      nth_rewrite 1 [hw]
      unfold spectralGapSmoothingFactor spectralGapBeta
      field_simp [τ.property.1.ne']
      ring
    have hPow : z ^ 6 ≤ z ^ 2 := by
      rw [show z ^ 6 = z ^ 4 * z ^ 2 by ring]
      exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hz₀ hz₁)
    have hSq : z ^ 2 ≤ z := by simpa only [pow_two, one_mul] using mul_le_mul_of_nonneg_right hz₁ hz₀
    rw [hFormula, ← hs]
    constructor
    · exact mul_nonneg τ.property.1.le (by nlinarith only [hPow, sq_nonneg z])
    · exact mul_le_mul_of_nonneg_left (by nlinarith only [hSq, pow_nonneg hz₀ 6, hz₀]) τ.property.1.le
  by_cases h : r ≤ 1 / 2
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    exact hSide r hL h
  · rw [← beta_symmetric τ r, abs_of_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h)))]
    have hr := hSide (1 - r) (by linarith only [hU]) (by linarith only [lt_of_not_ge h])
    exact ⟨hr.1, hr.2.trans_eq (by ring)⟩

theorem spectralGapProfile_midpoint_error (τ : GapSmoothingParameter) (r : ℝ) :
    0 ≤ spectralGapSmoothingFactor τ / 2 - spectralGapProfile τ r ∧
      spectralGapSmoothingFactor τ / 2 - spectralGapProfile τ r ≤ |r - 1 / 2| := by
  unfold spectralGapProfile
  split_ifs with hL hU
  · rw [abs_of_nonpos (by linarith [τ.property.1]), neg_sub]
    unfold spectralGapSmoothingFactor
    constructor <;> linarith [τ.property.1]
  · exact beta_midpoint_error τ (le_of_not_gt hL) hU
  · rw [abs_of_nonneg (by linarith [τ.property.1, lt_of_not_ge hU])]
    unfold spectralGapSmoothingFactor
    constructor <;> linarith [τ.property.1, lt_of_not_ge hU]

private theorem bulkPotential_ge_quartic_norm_error (a : BulkCoefficients) (A : S0) :
    min (a.a4 / 4) (a.a6' / 6) * (‖A‖ ^ 2 - 2 * vacuumRadius a ^ 2) ^ 2 ≤
      bulkPotential a A := by
  have hAbs : |‖A‖ ^ 2 - 2 * vacuumRadius a ^ 2| ≤ vacuumInvariantError a A := by
    rw [norm_sq_eq_trace_sq]
    unfold vacuumInvariantError vacuumInvariants
    rw [Prod.norm_def]
    change |((A : Tensor) ^ 2).trace - 2 * vacuumRadius a ^ 2| ≤
      max ‖((A : Tensor) ^ 2).trace - 2 * vacuumRadius a ^ 2‖ ‖((A : Tensor) ^ 3).trace - 0‖
    simp only [Real.norm_eq_abs]
    exact le_max_left _ _
  have hm : 0 ≤ min (a.a4 / 4) (a.a6' / 6) :=
    le_min (div_nonneg a.a4_pos.le (by norm_num)) (div_nonneg a.a6'_pos.le (by norm_num))
  refine le_trans ?_ (bulkPotential_ge_invariantError_sq a A)
  apply mul_le_mul_of_nonneg_left _ hm
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hAbs 2

/-- The bulk potential controls squared vacuum distance on the whole tensor space. -/
theorem exists_bulkPotential_ge_global_vacuumDist_sq (a : BulkCoefficients) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : S0, c * infDist A (vacuum a) ^ 2 ≤ bulkPotential a A := by
  obtain ⟨cNear, δ, hcNear, hδ, hNear⟩ := exists_bulkPotential_quadratic_lower a
  obtain ⟨V, hV⟩ := vacuum_nonempty a
  let r := vacuumRadius a
  let L : ℝ := max 1 (2 * r)
  let m := min (a.a4 / 4) (a.a6' / 6)
  have hm : 0 < m := lt_min (div_pos a.a4_pos (by norm_num)) (div_pos a.a6'_pos (by norm_num))
  have hr : 0 < r := vacuumRadius_pos a
  have hInfl (A : S0) : infDist A (vacuum a) ≤ ‖A‖ + Real.sqrt 2 * r := by
    refine (infDist_le_dist_of_mem hV).trans ?_
    have hv : ‖V‖ = Real.sqrt 2 * r := vacuum_norm hV
    simpa only [dist_zero_right, dist_zero_left, hv] using dist_triangle A 0 V
  let K := closedBall (0 : S0) L ∩ {A | δ ≤ infDist A (vacuum a)}
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : S0) L).inter_right (isClosed_le continuous_const (continuous_infDist_pt (vacuum a)))
  have hLower : ∃ b : ℝ, 0 < b ∧ ∀ A ∈ K, b ≤ bulkPotential a A := by
    by_cases hne : K.Nonempty
    · obtain ⟨A₀, hA₀, hMin⟩ := hK.exists_isMinOn hne (contDiff_bulkPotential a).continuous.continuousOn
      have hPos : 0 < bulkPotential a A₀ := by
        refine lt_of_le_of_ne (bulkPotential_nonneg a A₀) (Ne.symm ?_)
        intro hzero
        have hMem := (bulkPotential_eq_zero_iff a A₀).mp hzero
        have hd : δ ≤ infDist A₀ (vacuum a) := hA₀.2
        rw [infDist_zero_of_mem hMem] at hd
        exact hδ.not_ge hd
      exact ⟨_, hPos, fun _ hA => hMin hA⟩
    · exact ⟨1, zero_lt_one, fun A hA => (hne ⟨A, hA⟩).elim⟩
  obtain ⟨b, hb, hLower⟩ := hLower
  let cMid := b / (L + Real.sqrt 2 * r) ^ 2
  let c := min cNear (min cMid (m / 16))
  have hL : 0 < L := zero_lt_one.trans_le (le_max_left _ _)
  have hscale : 0 < L + Real.sqrt 2 * r := by positivity
  have hcMid : 0 < cMid := div_pos hb (sq_pos_of_pos hscale)
  have hc : 0 < c := lt_min hcNear (lt_min hcMid (div_pos hm (by norm_num)))
  refine ⟨c, hc, ?_⟩
  intro A
  let d := infDist A (vacuum a)
  have hd : 0 ≤ d := infDist_nonneg
  by_cases hN : d < δ
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans (hNear A hN)
  by_cases hM : ‖A‖ ≤ L
  · have hA : A ∈ K := ⟨by simpa only [mem_closedBall, dist_zero_right] using hM, le_of_not_gt hN⟩
    have hdist : d ≤ L + Real.sqrt 2 * r := (hInfl A).trans (add_le_add hM le_rfl)
    calc
      _ ≤ cMid * d ^ 2 := mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (sq_nonneg _)
      _ ≤ cMid * (L + Real.sqrt 2 * r) ^ 2 := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hd hscale.le).2 hdist) hcMid.le
      _ = b := div_mul_cancel₀ _ (sq_pos_of_pos hscale).ne'
      _ ≤ _ := hLower A hA
  have hLarge : L ≤ ‖A‖ := le_of_lt (lt_of_not_ge hM)
  have hOne : 1 ≤ ‖A‖ := (le_max_left _ _).trans hLarge
  have hRad : 2 * r ≤ ‖A‖ := (le_max_right _ _).trans hLarge
  have hRoot : Real.sqrt 2 ≤ (2 : ℝ) :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp (by rw [Real.sq_sqrt (by norm_num)]; norm_num)
  have hDist : d ≤ 2 * ‖A‖ := by
    have h := (mul_le_mul_of_nonneg_right hRoot hr.le).trans hRad
    linarith only [hInfl A, h]
  have hQuartic : ‖A‖ ^ 2 / 2 ≤ ‖A‖ ^ 2 - 2 * r ^ 2 := by
    nlinarith only [(sq_le_sq₀ (by positivity) (norm_nonneg A)).2 hRad]
  calc
    _ ≤ (m / 16) * d ^ 2 := mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (sq_nonneg _)
    _ ≤ (m / 16) * (2 * ‖A‖) ^ 2 :=
      mul_le_mul_of_nonneg_left ((sq_le_sq₀ hd (by positivity)).2 hDist) (by positivity)
    _ ≤ m * (‖A‖ ^ 2 / 2) ^ 2 := by
      have hE := mul_le_mul_of_nonneg_right ((sq_le_sq₀ zero_le_one (norm_nonneg A)).2 hOne)
        (mul_nonneg hm.le (sq_nonneg ‖A‖))
      nlinarith only [hE]
    _ ≤ m * (‖A‖ ^ 2 - 2 * r ^ 2) ^ 2 := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (by positivity) ((by positivity : 0 ≤ ‖A‖ ^ 2 / 2).trans hQuartic)).2 hQuartic) hm.le
    _ ≤ _ := bulkPotential_ge_quartic_norm_error a A

private theorem abs_normalized_modifiedGap_le_vacuumDist (a : BulkCoefficients)
    (τ : GapSmoothingParameter) (A : S0) :
    |1 - modifiedSpectralGap a τ A / spectralGapSmoothingFactor τ| ≤
      (6 / vacuumRadius a) * infDist A (vacuum a) := by
  let r := vacuumRadius a
  let b := spectralGapSmoothingFactor τ
  let s := orderedEigenvalue A 0 - orderedEigenvalue A 2
  let t := orderedEigenvalue A 1 - orderedEigenvalue A 2
  let z := t / s
  let d := infDist A (vacuum a)
  let x₀ := orderedEigenvalue A 0 - r
  let x₁ := orderedEigenvalue A 1
  let x₂ := orderedEigenvalue A 2 + r
  have hr : 0 < r := vacuumRadius_pos a
  have hb : 0 < b := spectralGapSmoothingFactor_pos τ
  have hb₁ : b ≤ 1 := spectralGapSmoothingFactor_le_one τ
  have hb₂ : (1 / 2 : ℝ) ≤ b := by
    dsimp only [b, spectralGapSmoothingFactor]
    linarith only [τ.property.2]
  have hs : 0 ≤ s := sub_nonneg.mpr (orderedEigenvalue_antitone A (by decide : (0 : Fin 3) ≤ 2))
  have hsz : s * z = t := by
    by_cases hA : A = 0
    · subst A
      simp [s, z, t, ordered_eigenvalue_zero]
    · dsimp only [z]
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ordered_eigenwidth_pos_of_ne_zero hA).ne']
  have hMod : modifiedSpectralGap a τ A = r⁻¹ * (s * spectralGapProfile τ z) := by
    by_cases hA : A = 0
    · subst A
      simp [modifiedSpectralGap, s, ordered_eigenvalue_zero]
    · rw [modifiedSpectralGap, if_neg hA]
  have hd : 0 ≤ d := infDist_nonneg
  have hSq : d ^ 2 = x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 := infDist_vacuum_sq_eq_orderedEigenvalue a A
  have h0 : |x₀| ≤ d := (sq_le_sq₀ (abs_nonneg _) hd).mp (by
    rw [sq_abs, hSq]
    nlinarith only [sq_nonneg x₁, sq_nonneg x₂])
  have h1 : |x₁| ≤ d := (sq_le_sq₀ (abs_nonneg _) hd).mp (by
    rw [sq_abs, hSq]
    nlinarith only [sq_nonneg x₀, sq_nonneg x₂])
  have h2 : |x₂| ≤ d := (sq_le_sq₀ (abs_nonneg _) hd).mp (by
    rw [sq_abs, hSq]
    nlinarith only [sq_nonneg x₀, sq_nonneg x₁])
  have hWide : |2 * r - s| ≤ 2 * d := by
    rw [show 2 * r - s = x₂ - x₀ by dsimp only [s, x₀, x₂]; ring]
    linarith only [abs_sub x₂ x₀, h0, h2]
  have hCentered : |t - s / 2| ≤ 2 * d := by
    rw [show t - s / 2 = x₁ - (x₀ + x₂) / 2 by dsimp only [s,t,x₀,x₁,x₂]; ring]
    have hsum : |(x₀ + x₂) / 2| ≤ d := by
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith only [abs_add_le x₀ x₂, h0, h2]
    linarith only [abs_sub x₁ ((x₀ + x₂) / 2), hsum, h1]
  have hProfile := spectralGapProfile_midpoint_error τ z
  have hErr := mul_le_mul_of_nonneg_left hProfile.2 hs
  have hAbs : |b * r - s * spectralGapProfile τ z| ≤ 3 * d := by
    have heq : b * r - s * spectralGapProfile τ z =
      (b / 2) * (2 * r - s) + s * (b / 2 - spectralGapProfile τ z) := by ring
    rw [heq]
    calc
      _ ≤ |(b / 2) * (2 * r - s)| + |s * (b / 2 - spectralGapProfile τ z)| := abs_add_le _ _
      _ ≤ (b / 2) * (2 * d) + s * |z - 1 / 2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg hb.le (by norm_num)), abs_of_nonneg hs,
          abs_of_nonneg hProfile.1]
        exact add_le_add (mul_le_mul_of_nonneg_left hWide (div_nonneg hb.le (by norm_num))) hErr
      _ = b * d + |t - s / 2| := by
        have hscaled : s * |z - 1 / 2| = |s * (z - 1 / 2)| := by
          rw [abs_mul, abs_of_nonneg hs]
        rw [hscaled, show s * (z - 1 / 2) = t - s / 2 by rw [mul_sub, hsz]; ring]
        ring
      _ ≤ _ := by
        linarith only [mul_le_of_le_one_left hd hb₁, hCentered]
  have hRearrange : (b * r) * |1 - modifiedSpectralGap a τ A / b| =
      |b * r - s * spectralGapProfile τ z| := by
    calc
      _ = |(b * r) * (1 - modifiedSpectralGap a τ A / b)| := by
        rw [abs_mul, abs_of_pos (mul_pos hb hr)]
      _ = _ := congrArg abs (by rw [hMod]; field_simp [hb.ne', hr.ne'])
  have hLeft := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hb₂ hr.le) (abs_nonneg (1 - modifiedSpectralGap a τ A / b))
  rw [hRearrange] at hLeft
  calc
    _ ≤ (3 * d) / ((1 / 2 : ℝ) * r) := (le_div_iff₀' (by positivity)).2 (hLeft.trans hAbs)
    _ = _ := by dsimp only [d, r]; field_simp [(vacuumRadius_pos a).ne']; ring

/-- The actual two-branch level weight is controlled by the model bulk potential,
with a constant uniform over the smoothing parameters. -/
theorem exists_bulkPotential_ge_modifiedGapLevelWeight (a : BulkCoefficients) :
    ∃ c : ℝ, 0 < c ∧ ∀ (τ : GapSmoothingParameter) (A : S0),
      c * min ((1 - modifiedSpectralGap a τ A / spectralGapSmoothingFactor τ) ^ 2)
        ((1 - modifiedSpectralGap a τ A) ^ 2) ≤ bulkPotential a A := by
  obtain ⟨b, hb, hdist⟩ := exists_bulkPotential_ge_global_vacuumDist_sq a
  let K := 6 / vacuumRadius a
  have hK : 0 < K := div_pos (by norm_num) (vacuumRadius_pos a)
  let c := b / K ^ 2
  have hc : 0 < c := div_pos hb (sq_pos_of_pos hK)
  refine ⟨c, hc, ?_⟩
  intro τ A
  have hGap := abs_normalized_modifiedGap_le_vacuumDist a τ A
  change |1 - modifiedSpectralGap a τ A / spectralGapSmoothingFactor τ| ≤ K * infDist A (vacuum a) at hGap
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hK.le infDist_nonneg)).2 hGap
  rw [sq_abs, mul_pow] at hs
  calc
    _ ≤ c * (1 - modifiedSpectralGap a τ A / spectralGapSmoothingFactor τ) ^ 2 :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le
    _ ≤ c * (K ^ 2 * infDist A (vacuum a) ^ 2) := mul_le_mul_of_nonneg_left hs hc.le
    _ = b * infDist A (vacuum a) ^ 2 := by
      dsimp only [c]
      field_simp [hK.ne']
    _ ≤ _ := hdist A

private theorem hasDerivAt_spectralGapBeta (τ : GapSmoothingParameter) (r : ℝ) :
    let z := (r - 1 / 2) / τ.val
    HasDerivAt (spectralGapBeta τ) ((z ^ 5 - 5 * z) / 4) r := by
  have harg : HasDerivAt (fun x : ℝ => x - 1 / 2) 1 r := (hasDerivAt_id r).sub_const _
  have h₁ := (harg.pow 6).div_const (24 * τ.val ^ 5)
  have h₂ := ((harg.pow 2).const_mul 5).div_const (8 * τ.val)
  have h := (h₁.sub h₂).add_const ((6 - 5 * τ.val) / 12)
  change HasDerivAt (spectralGapBeta τ)
    ((6 : ℝ) * (r - 1 / 2) ^ 5 * 1 / (24 * τ.val ^ 5) -
      5 * ((2 : ℝ) * (r - 1 / 2) ^ 1 * 1) / (8 * τ.val)) r at h
  convert h using 1
  field_simp [τ.property.1.ne']
  ring

private theorem abs_beta_deriv_le (τ : GapSmoothingParameter) {r : ℝ}
    (hL : 1 / 2 - τ.val ≤ r) (hU : r ≤ 1 / 2 + τ.val) :
    |deriv (spectralGapBeta τ) r| ≤ 1 := by
  let z := (r - 1 / 2) / τ.val
  let b := |z|
  have hb : 0 ≤ b := abs_nonneg _
  have hb₁ : b ≤ 1 := by
    apply abs_le.2
    constructor
    · apply (le_div_iff₀ τ.property.1).2
      linarith only [hL]
    · apply (div_le_iff₀ τ.property.1).2
      linarith only [hU]
  have hPow : b ^ 4 = z ^ 4 := by
    change |z| ^ 4 = z ^ 4
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ z ^ 4)]
  have hf : z ^ 4 - 5 ≤ 0 := by
    rw [← hPow]
    linarith only [pow_le_one₀ hb hb₁ (n := 4)]
  have hfact : 0 ≤ (1 - b) ^ 2 * (b ^ 3 + 2 * b ^ 2 + 3 * b + 4) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hNum : 5 * b - b ^ 5 ≤ 4 := by nlinarith only [hfact]
  have hd : deriv (spectralGapBeta τ) r = (z ^ 5 - 5 * z) / 4 :=
    (hasDerivAt_spectralGapBeta τ r).deriv
  rw [hd, show (z ^ 5 - 5 * z) / 4 = z * (z ^ 4 - 5) / 4 by ring, abs_div, abs_mul,
    abs_of_nonpos hf, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  change b * -(z ^ 4 - 5) / 4 ≤ 1
  rw [← hPow]
  nlinarith only [hNum]

/-- The exact scalar smoothing has slope of magnitude at most one. -/
theorem abs_deriv_spectralGapProfile_le (τ : GapSmoothingParameter) (r : ℝ) :
    |deriv (spectralGapProfile τ) r| ≤ 1 := by
  let l : ℝ := 1 / 2 - τ.val
  let u : ℝ := 1 / 2 + τ.val
  have hlu : l < u := by dsimp only [l, u]; linarith [τ.property.1]
  have hder : Continuous (deriv (spectralGapProfile τ)) :=
    (contDiff_spectralGapProfile τ).continuous_deriv (by decide)
  have hLeft (x : ℝ) (hx : x < l) : deriv (spectralGapProfile τ) x = 1 := by
    apply HasDerivAt.deriv
    apply (hasDerivAt_id x).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hx] with y hy
    exact if_pos hy
  have hRight (x : ℝ) (hx : u < x) : deriv (spectralGapProfile τ) x = -1 := by
    have h := (hasDerivAt_id x).const_sub (1 : ℝ)
    apply (h.congr_of_eventuallyEq ?_).deriv
    filter_upwards [lt_mem_nhds hx] with y hy
    unfold spectralGapProfile
    rw [if_neg (not_lt_of_ge (hlu.trans hy).le), if_neg (not_le_of_gt hy)]
    rfl
  have hl : deriv (spectralGapProfile τ) l = 1 := by
    let S : Set ℝ := {x | deriv (spectralGapProfile τ) x = 1}
    have hs : IsClosed S := isClosed_eq hder continuous_const
    exact (hs.closure_subset_iff.mpr (show Iio l ⊆ S from fun x hx => hLeft x hx))
      (by rw [closure_Iio]; exact (le_rfl : l ≤ l))
  have hu : deriv (spectralGapProfile τ) u = -1 := by
    let S : Set ℝ := {x | deriv (spectralGapProfile τ) x = -1}
    have hs : IsClosed S := isClosed_eq hder continuous_const
    exact (hs.closure_subset_iff.mpr (show Ioi u ⊆ S from fun x hx => hRight x hx))
      (by rw [closure_Ioi]; exact (le_rfl : u ≤ u))
  rcases lt_trichotomy r l with h | rfl | h
  · rw [hLeft r h, abs_one]
  · rw [hl, abs_one]
  rcases lt_trichotomy r u with h' | rfl | h'
  · have he : spectralGapProfile τ =ᶠ[𝓝 r] spectralGapBeta τ := by
      filter_upwards [Ioo_mem_nhds h h'] with y hy
      unfold spectralGapProfile
      rw [if_neg (not_lt_of_ge hy.1.le), if_pos hy.2.le]
    rw [he.deriv_eq]
    exact abs_beta_deriv_le τ h.le h'.le
  · rw [hu, abs_neg, abs_one]
  · rw [hRight r h', abs_neg, abs_one]

end Thesis
