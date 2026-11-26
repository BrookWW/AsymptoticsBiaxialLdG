module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The inverse-excess estimate for a sublinear comparison on good radii. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace Thesis.MeasureGeometry

private theorem absolutelyContinuousOnInterval_of_dist_bound {f g : ℝ → ℝ} {a b K : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hK : 0 < K)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (g x) (g y) ≤ K * dist (f x) (f y)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hsum⟩ := hf (ε / K) (div_pos hε hK)
  refine ⟨δ, hδ, fun U hU hsmall => ?_⟩
  calc
    _ ≤ ∑ i ∈ Finset.range U.1, K * dist (f (U.2 i).1) (f (U.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hEnds := hU.1 i hi
      exact h _ hEnds.1 _ hEnds.2
    _ < ε := by
      rw [← Finset.mul_sum, mul_comm, ← lt_div_iff₀ hK]
      exact hsum U hU hsmall

/-- A radial density of total mass at most `r*M` has the stated good set on
the outer half-interval. -/
theorem goodRadiusSet_measureReal_ge {r M : ℝ} (hr : 0 < r) (hM : 0 < M) {g : ℝ → ℝ}
    (hg : Measurable g) (hInt : IntegrableOn g (Ioo (r / 2) r))
    (hPos : 0 ≤ᵐ[volume.restrict (Ioo (r / 2) r)] g)
    (hEnergy : (∫ t in Ioo (r / 2) r, g t) ≤ r * M) :
    r / 4 ≤ (volume : Measure ℝ).real (Ioo (r / 2) r ∩ {t | g t ≤ 4 * M}) := by
  let U := Ioo (r / 2) r
  let D := U ∩ {t | g t ≤ 4 * M}
  let B := U ∩ {t | 4 * M < g t}
  have hBm : MeasurableSet B := measurableSet_Ioo.inter (measurableSet_lt measurable_const hg)
  have hU₀ : (volume : Measure ℝ) U < ⊤ := by
    dsimp only [U]
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have hB₀ : (volume : Measure ℝ) B < ⊤ := (measure_mono inter_subset_left).trans_lt hU₀
  have hD₀ : (volume : Measure ℝ) D < ⊤ := (measure_mono inter_subset_left).trans_lt hU₀
  letI : IsFiniteMeasure (volume.restrict B) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hBad : (4 * M) * volume.real B ≤ r * M := calc
    _ = ∫ _ : ℝ in B, (4 * M) := by simp only [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ t in B, g t := by
      apply integral_mono_ae (integrable_const _) (hInt.mono_set inter_subset_left)
      filter_upwards [ae_restrict_mem hBm] with t ht
      exact ht.2.le
    _ ≤ ∫ t in U, g t := setIntegral_mono_set hInt hPos (Eventually.of_forall inter_subset_left)
    _ ≤ _ := hEnergy
  have hBV : volume.real B ≤ r / 4 := by
    rw [show r / 4 = (r * M) / (4 * M) by field_simp]
    exact (le_div_iff₀ (by positivity : 0 < 4 * M)).2 (by simpa only [mul_comm] using hBad)
  have hDisj : Disjoint D B := by
    apply Set.disjoint_left.2
    intro t ht₁ ht₂
    have hle : g t ≤ 4 * M := ht₁.2
    have hlt : 4 * M < g t := ht₂.2
    exact (not_lt_of_ge hle) hlt
  have hUnion : D ∪ B = U := by
    ext t
    change (t ∈ U ∧ g t ≤ 4 * M) ∨ (t ∈ U ∧ 4 * M < g t) ↔ t ∈ U
    exact ⟨fun h => h.elim And.left And.left, fun h =>
      (le_or_gt (g t) (4 * M)).elim (fun h' => Or.inl ⟨h, h'⟩) (fun h' => Or.inr ⟨h, h'⟩)⟩
  have hAdd := measureReal_union (μ := (volume : Measure ℝ)) hDisj hBm hD₀.ne hB₀.ne
  rw [hUnion] at hAdd
  have hU : volume.real U = r - r / 2 := Real.volume_real_Ioo_of_le (by linarith)
  rw [hU] at hAdd
  change r / 4 ≤ volume.real D
  linarith

theorem log_radius_div_le_two_log_subradius {ε r ρ : ℝ} (hε : 0 < ε)
    (hεr : ε ≤ r / 4) (hρ : r / 2 < ρ) :
    Real.log (r / ε) ≤ 2 * Real.log (ρ / ε) := by
  have hr : 0 < r := by linarith
  have hsq : r * ε ≤ ρ ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hεr hr.le
    have h2 := pow_le_pow_left₀ (by linarith : 0 ≤ r / 2) hρ.le 2
    nlinarith
  have hDiv : r / ε ≤ (ρ / ε) ^ 2 := by
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos hε)).2
    calc
      _ = r * ε := by field_simp
      _ ≤ _ := hsq
  have h := Real.log_le_log (div_pos hr hε) hDiv
  rwa [Real.log_pow, Nat.cast_ofNat] at h

/-- Sublinear comparison on at least a quarter of the original radius
interval gives the quantitative half-radius bound. -/
theorem halfRadius_energy_le_of_ae_sublinear_comparison {r C : ℝ} (hr : 0 < r) (hC : 0 < C)
    {E g : ℝ → ℝ} (hAC : AbsolutelyContinuousOnInterval E (r / 2) r)
    (hMono : MonotoneOn E (Icc (r / 2) r))
    (hDer : ∀ᵐ t ∂volume.restrict (Ioo (r / 2) r), HasDerivAt E (g t) t ∧ 0 ≤ g t)
    {D : Set ℝ} (hD : MeasurableSet D) (hSub : D ⊆ Ioo (r / 2) r)
    (hMass : r / 4 ≤ (volume : Measure ℝ).real D)
    (hGood : ∀ᵐ t ∂volume.restrict (Ioo (r / 2) r), t ∈ D → E t ≤ C * r * (Real.sqrt (g t) + 1)) :
    E (r / 2) ≤ (C + 4 * C ^ 2) * r := by
  let a := r / 2
  let B := C * r
  have ha : a < r := by dsimp only [a]; linarith
  have hB : 0 < B := mul_pos hC hr
  by_cases hEZ : E a ≤ B
  · exact hEZ.trans (by dsimp only [B]; nlinarith [mul_nonneg (sq_nonneg C) hr.le])
  let d := E a - B
  have hd : 0 < d := sub_pos.mpr (lt_of_not_ge hEZ)
  have hExcess (t : ℝ) (ht : t ∈ Icc a r) : d ≤ E t - B :=
    sub_le_sub_right (hMono ⟨le_rfl, ha.le⟩ ht ht.1) _
  let F (t : ℝ) := -((E t - B)⁻¹)
  have hF : AbsolutelyContinuousOnInterval F a r := by
    apply absolutelyContinuousOnInterval_of_dist_bound hAC (inv_pos.mpr (sq_pos_of_pos hd))
    intro x hx y hy
    rw [uIcc_of_le ha.le] at hx hy
    have hxd := hExcess x hx
    have hyd := hExcess y hy
    have hx₀ := hd.trans_le hxd
    have hy₀ := hd.trans_le hyd
    have hquot : F x - F y = (E x - E y) / ((E x - B) * (E y - B)) := by
      dsimp only [F]
      field_simp
      ring
    rw [Real.dist_eq, Real.dist_eq, hquot, abs_div, abs_of_nonneg (mul_nonneg hx₀.le hy₀.le),
      ← div_eq_inv_mul]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hd)
    rw [pow_two]
    exact mul_le_mul hxd hyd hd.le hx₀.le
  have hfd : ∀ᵐ t ∂volume.restrict (Ioo a r), deriv F t = g t / (E t - B) ^ 2 ∧ 0 ≤ g t := by
    filter_upwards [hDer, ae_restrict_mem measurableSet_Ioo] with t ht htr
    have hZ := hd.trans_le (hExcess t (Ioo_subset_Icc_self htr))
    have hF' := ((ht.1.sub_const B).inv hZ.ne').neg
    have hEq : -(fun x : ℝ => E x - B)⁻¹ = F := rfl
    rw [hEq] at hF'
    exact ⟨by simpa only [neg_neg, neg_div] using hF'.deriv, ht.2⟩
  let μ := volume.restrict (Ioo a r)
  let q := (B ^ 2)⁻¹
  letI : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top⟩
  have hPoint : D.indicator (fun _ => q) ≤ᵐ[μ] deriv F := by
    filter_upwards [hfd, ae_restrict_mem measurableSet_Ioo, hGood] with t ht htr hGoodt
    rw [ht.1]
    by_cases htD : t ∈ D
    · rw [indicator_of_mem htD]
      have ht₀ := hd.trans_le (hExcess t (Ioo_subset_Icc_self htr))
      have hs : E t - B ≤ B * Real.sqrt (g t) := by
        have this := hGoodt htD
        change E t ≤ B * (Real.sqrt (g t) + 1) at this
        linarith only [this, mul_add B (Real.sqrt (g t)) 1, mul_one B]
      have hp := pow_le_pow_left₀ ht₀.le hs 2
      rw [mul_pow, Real.sq_sqrt ht.2] at hp
      change (B ^ 2)⁻¹ ≤ g t / (E t - B) ^ 2
      rw [le_div_iff₀ (sq_pos_of_pos ht₀), ← div_eq_inv_mul, div_le_iff₀ (sq_pos_of_pos hB)]
      simpa only [mul_comm (g t)] using hp
    · rw [indicator_of_notMem htD]
      exact div_nonneg ht.2 (sq_nonneg _)
  have hIntF : Integrable (deriv F) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).1 hF.intervalIntegrable_deriv
  have hIntD : Integrable (D.indicator (fun _ => q)) μ := (integrable_const q).indicator hD
  have hI := integral_mono_ae hIntD hIntF hPoint
  have hID : (∫ t, D.indicator (fun _ => q) t ∂μ) = q * volume.real D := by
    rw [integral_indicator hD]
    change (∫ _ : ℝ, q ∂(volume.restrict (Ioo a r)).restrict D) = _
    rw [Measure.restrict_restrict hD, inter_eq_left.mpr hSub, integral_const,
      measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]
  have hIF : (∫ t, deriv F t ∂μ) = F r - F a := by
    change (∫ t in Ioo a r, deriv F t) = _
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha.le,
      hF.integral_deriv_eq_sub]
  rw [hID, hIF] at hI
  have hInv : (4 * C ^ 2 * r)⁻¹ ≤ d⁻¹ := calc
    _ = q * (r / 4) := by
      dsimp only [q, B]
      field_simp
    _ ≤ q * volume.real D := mul_le_mul_of_nonneg_left hMass (inv_nonneg.mpr (sq_nonneg _))
    _ ≤ F r - F a := hI
    _ ≤ d⁻¹ := by
      have hEnd := hd.trans_le (hExcess r ⟨ha.le, le_rfl⟩)
      change -((E r - B)⁻¹) - -(d⁻¹) ≤ d⁻¹
      linarith [inv_nonneg.mpr hEnd.le]
  have hdBound := (inv_le_inv₀ (by positivity : 0 < 4 * C ^ 2 * r) hd).1 hInv
  change E a - C * r ≤ 4 * C ^ 2 * r at hdBound
  change E a ≤ (C + 4 * C ^ 2) * r
  rw [add_mul]
  linarith

theorem halfRadius_energy_le_of_sublinear_comparison {r C : ℝ} (hr : 0 < r) (hC : 0 < C)
    {E g : ℝ → ℝ} (hAC : AbsolutelyContinuousOnInterval E (r / 2) r)
    (hMono : MonotoneOn E (Icc (r / 2) r))
    (hDer : ∀ᵐ t ∂volume.restrict (Ioo (r / 2) r), HasDerivAt E (g t) t ∧ 0 ≤ g t)
    {D : Set ℝ} (hD : MeasurableSet D) (hSub : D ⊆ Ioo (r / 2) r)
    (hMass : r / 4 ≤ (volume : Measure ℝ).real D)
    (hGood : ∀ t ∈ D, E t ≤ C * r * (Real.sqrt (g t) + 1)) :
    E (r / 2) ≤ (C + 4 * C ^ 2) * r :=
  halfRadius_energy_le_of_ae_sublinear_comparison hr hC hAC hMono hDer hD hSub hMass (ae_of_all _ hGood)

end Thesis.MeasureGeometry
