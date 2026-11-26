module

public import Thesis.Variational.H10FractionalEmbedding

/-! Intrinsic interpolation of the fractional energy by the pair separation. -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem fractionalPairEnergy_le_two_scales
    {s t δ : ℝ} (hs : 0 < s) (hst : s < t) (hδ : 0 < δ) (u : Point → S0) (z : Point × Point) :
    fractionalPairEnergy s u z ≤ ENNReal.ofReal (δ ^ (2 * (t-s))) * fractionalPairEnergy t u z +
      ENNReal.ofReal (2 / δ ^ (3 + 2 * s)) *
        (ENNReal.ofReal (‖u z.1‖^2) + ENNReal.ofReal (‖u z.2‖^2)) := by
  let a := ‖u z.1 - u z.2‖ ^ 2
  let d := dist z.1 z.2
  let p := 3 + 2 * s
  let q := 3 + 2 * t
  let w := 2 * (t - s)
  have hp : 0 ≤ p := by dsimp only [p]; linarith
  have hw : 0 ≤ w := by dsimp only [w]; linarith
  have hδp : 0 < δ ^ p := Real.rpow_pos_of_pos hδ _
  have hδw : 0 ≤ δ ^ w := Real.rpow_nonneg hδ.le _
  have hd : 0 ≤ d := dist_nonneg
  have ha : 0 ≤ a := sq_nonneg _
  let b := 2 / δ ^ p
  have hb : 0 ≤ b := div_nonneg (by norm_num) hδp.le
  have hsquare : a ≤ 2 * (‖u z.1‖ ^ 2 + ‖u z.2‖ ^ 2) := by
    calc
      _ ≤ (‖u z.1‖ + ‖u z.2‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
      _ ≤ _ := by nlinarith only [sq_nonneg (‖u z.1‖ - ‖u z.2‖)]
  have hReal : a / d ^ p ≤ δ ^ w * (a / d ^ q) + b * (‖u z.1‖ ^ 2 + ‖u z.2‖ ^ 2) := by
    by_cases hxy : z.1 = z.2
    · have ha0 : a = 0 := by dsimp only [a]; rw [hxy,sub_self,norm_zero,zero_pow (by norm_num)]
      rw [ha0, zero_div, zero_div, mul_zero, zero_add]
      positivity
    have hd' : 0 < d := dist_pos.mpr hxy
    have hDp : 0 < d ^ p := Real.rpow_pos_of_pos hd' _
    have hDq : 0 < d ^ q := Real.rpow_pos_of_pos hd' _
    by_cases hNear : d ≤ δ
    · have hExp : q = p + w := by dsimp only [q,p,w]; ring
      calc
        _ = d ^ w * (a / d ^ q) := by
          have hE : d ^ q = d ^ p * d ^ w :=
            (congrArg (fun e : ℝ => d ^ e) hExp).trans (Real.rpow_add hd' _ _)
          rw [hE]
          have hDw : 0 < d ^ w := Real.rpow_pos_of_pos hd' _
          field_simp [hDp.ne',hDw.ne']
        _ ≤ δ ^ w * (a / d ^ q) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd hNear hw) (div_nonneg ha hDq.le)
        _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hb (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    · have hOrder : δ ^ p ≤ d ^ p := Real.rpow_le_rpow hδ.le (le_of_lt (lt_of_not_ge hNear)) hp
      calc
        _ ≤ a / δ ^ p := div_le_div_of_nonneg_left ha hδp hOrder
        _ ≤ (2 * (‖u z.1‖ ^ 2 + ‖u z.2‖ ^ 2)) / δ ^ p :=
          div_le_div_of_nonneg_right hsquare hδp.le
        _ = b * (‖u z.1‖ ^ 2 + ‖u z.2‖ ^ 2) := by dsimp only [b]; ring
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hδw (div_nonneg ha hDq.le))
  change ENNReal.ofReal (a / d ^ p) ≤ ENNReal.ofReal (δ ^ w) * ENNReal.ofReal (a / d ^ q) +
    ENNReal.ofReal b * (ENNReal.ofReal (‖u z.1‖^2) + ENNReal.ofReal (‖u z.2‖^2))
  refine (ENNReal.ofReal_le_ofReal hReal).trans_eq ?_
  rw [ENNReal.ofReal_add (mul_nonneg hδw (div_nonneg ha (Real.rpow_nonneg hd _)))
      (mul_nonneg hb (add_nonneg (sq_nonneg _) (sq_nonneg _))),
    ENNReal.ofReal_mul hδw, ENNReal.ofReal_mul hb, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]

private theorem lintegral_sq_pair_sum
    {μ : Measure Point} [SFinite μ] (u : Point → S0) (hU : AEStronglyMeasurable u μ) :
    (∫⁻ z : Point × Point, ENNReal.ofReal (‖u z.1‖ ^ 2) + ENNReal.ofReal (‖u z.2‖ ^ 2) ∂μ.prod μ) =
      (2 * μ univ) * (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ) := by
  let v (x : Point) := ENNReal.ofReal (‖u x‖ ^ 2)
  have hv : AEMeasurable v μ := ENNReal.measurable_ofReal.comp_aemeasurable (hU.norm.aemeasurable.pow_const _)
  have h₁ : AEMeasurable (v ∘ Prod.fst) (μ.prod μ) := hv.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have h₂ : AEMeasurable (v ∘ Prod.snd) (μ.prod μ) := hv.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  change (∫⁻ z, (v ∘ Prod.fst) z + (v ∘ Prod.snd) z ∂μ.prod μ) = _
  rw [lintegral_add_left' h₁, lintegral_prod _ h₁, lintegral_prod _ h₂]
  simp only [Function.comp_apply, lintegral_const]
  rw [lintegral_mul_const'' _ hv]
  ring

/-- A pointwise split by the pair distance gives the quantitative lower
fractional norm in terms of the higher norm and the L² norm. -/
theorem fractionalEnergy_le_interpolation
    {U : Set Point} (u : Point → S0) (hu : AEStronglyMeasurable u (volume.restrict U))
    {s t δ : ℝ} (hs : 0 < s) (hst : s < t) (hδ : 0 < δ) :
    fractionalEnergy s U u ≤ ENNReal.ofReal (δ ^ (2 * (t-s))) * fractionalEnergy t U u +
      (1 + ENNReal.ofReal (2 / δ ^ (3 + 2 * s)) * (2 * volume U)) * eLpNorm u 2 (volume.restrict U) ^ 2 := by
  let μ := volume.restrict U
  let A := ENNReal.ofReal (δ ^ (2 * (t-s)))
  let B := ENNReal.ofReal (2 / δ ^ (3 + 2 * s))
  let L := ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ
  have hP (p : ℝ) : AEMeasurable (fractionalPairEnergy p u) (μ.prod μ) :=
    fractionalPairEnergy_aemeasurable p hu
  have hInner (p : ℝ) :
      fractionalEnergy p U u = L + ∫⁻ z, fractionalPairEnergy p u z ∂μ.prod μ := by
    rw [lintegral_prod _ (hP p)]
    rfl
  have hPoint :
      (∫⁻ z, fractionalPairEnergy s u z ∂μ.prod μ) ≤
        A * (∫⁻ z, fractionalPairEnergy t u z ∂μ.prod μ) + B * (2 * μ univ) * L := by
    have hQ : AEMeasurable (fun z => A * fractionalPairEnergy t u z) (μ.prod μ) :=
      aemeasurable_const.mul (hP t)
    calc
      _ ≤ ∫⁻ z, A * fractionalPairEnergy t u z +
          B * (ENNReal.ofReal (‖u z.1‖ ^ 2) + ENNReal.ofReal (‖u z.2‖ ^ 2)) ∂μ.prod μ :=
        lintegral_mono (fractionalPairEnergy_le_two_scales hs hst hδ u)
      _ = _ := by
        have hL : AEMeasurable (fun x => ENNReal.ofReal (‖u x‖ ^ 2)) μ :=
          ENNReal.measurable_ofReal.comp_aemeasurable (hu.norm.aemeasurable.pow_const _)
        have h₁ := hL.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
        have h₂ := hL.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
        have hM : AEMeasurable (fun z : Point × Point =>
            ENNReal.ofReal (‖u z.1‖ ^ 2) + ENNReal.ofReal (‖u z.2‖ ^ 2)) (μ.prod μ) := h₁.add h₂
        rw [lintegral_add_left' hQ, lintegral_const_mul'' _ (hP t),
          lintegral_const_mul'' _ hM, lintegral_sq_pair_sum u hu]
        change A * (∫⁻ z, fractionalPairEnergy t u z ∂μ.prod μ) + B * ((2 * μ univ) * L) =
          A * (∫⁻ z, fractionalPairEnergy t u z ∂μ.prod μ) + B * (2 * μ univ) * L
        ac_rfl
  have hL : eLpNorm u 2 μ ^ 2 = L := eLpNorm_two_sq_eq_tensor_lintegral μ u
  have hμ : μ univ = volume U := by simp [μ]
  rw [hInner s, hL, ← hμ, add_mul, one_mul]
  have htE : (∫⁻ z, fractionalPairEnergy t u z ∂μ.prod μ) ≤ fractionalEnergy t U u :=
    (self_le_add_left _ L).trans_eq (hInner t).symm
  change L + (∫⁻ z, fractionalPairEnergy s u z ∂μ.prod μ) ≤
    A * fractionalEnergy t U u + (L + (B * (2 * μ univ)) * L)
  exact (add_le_add le_rfl hPoint).trans
    ((add_le_add le_rfl (add_le_add (mul_le_mul' le_rfl htE) le_rfl)).trans_eq (by ac_rfl))

/-- Lower fractional regularity follows on a bounded domain from the
higher intrinsic energy. -/
theorem MemHs.of_exponent_lt_bounded
    {U : Set Point} (hU : IsBoundedDomain U) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    {u : Point → S0} (hu : MemHs t U u) : MemHs s U u := by
  refine ⟨hu.1,?_⟩
  have hI := fractionalEnergy_le_interpolation u hu.1 hs hst zero_lt_one
  have hL : eLpNorm u 2 (volume.restrict U) ^ 2 < ⊤ := by
    rw [eLpNorm_two_sq_eq_tensor_lintegral]
    exact (self_le_add_right _ _).trans_lt hu.2
  have hVol : volume U < ⊤ := hU.2.2.measure_lt_top
  have hB : (1 + ENNReal.ofReal (2 / (1 : ℝ) ^ (3 + 2 * s)) * (2 * volume U)) < ⊤ :=
    ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (by simp) hVol)⟩
  exact hI.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2,
    ENNReal.mul_lt_top hB hL⟩)

end Thesis

end
