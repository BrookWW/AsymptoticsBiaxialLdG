module

public import Thesis.Definitions
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! The (L^2) and (L^4) norms used in the boundary maximum argument. -/

public section

open Filter MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

theorem memLp_sqrt_two_of_lintegral_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {g : X → ℝ} {m : ℝ}
    (hg : AEStronglyMeasurable g μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hm : 0 ≤ m) (hInt : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤ ENNReal.ofReal m) :
    MemLp (fun x => Real.sqrt (g x)) 2 μ ∧
      (eLpNorm (fun x => Real.sqrt (g x)) 2 μ).toReal ≤ Real.sqrt m := by
  have hI : (∫⁻ x, ‖Real.sqrt (g x)‖ₑ ^ (2 : ℝ) ∂μ) = ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hpos] with x hx
    rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _), ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hx]
  have hN : eLpNorm (fun x => Real.sqrt (g x)) 2 μ ≤ ENNReal.ofReal (Real.sqrt m) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat]
    rw [hI, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hm (by norm_num)]
    exact ENNReal.rpow_le_rpow hInt (by norm_num)
  exact ⟨⟨Real.continuous_sqrt.comp_aestronglyMeasurable hg, hN.trans_lt ENNReal.ofReal_lt_top⟩,
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hN).trans_eq (ENNReal.toReal_ofReal (Real.sqrt_nonneg _))⟩

theorem memLp_four_of_lintegral_bound_and_ae_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {g : X → ℝ} {m M : ℝ}
    (hg : AEStronglyMeasurable g μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ M)
    (hm : 0 ≤ m) (hM : 0 ≤ M) (hInt : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤ ENNReal.ofReal m) :
    MemLp g 4 μ ∧ (eLpNorm g 4 μ).toReal ≤ (M ^ 3 * m) ^ (1 / 4 : ℝ) := by
  have hI : (∫⁻ x, ‖g x‖ₑ ^ (4 : ℝ) ∂μ) ≤ ENNReal.ofReal (M ^ 3 * m) := calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (M ^ 3) * ENNReal.ofReal (g x) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hpos] with x hx
      calc
        _ = ENNReal.ofReal (g x ^ 4) := by
          rw [Real.enorm_eq_ofReal hx.1, ENNReal.ofReal_pow hx.1 4]
          exact ENNReal.rpow_natCast _ 4
        _ ≤ _ := by
          rw [← ENNReal.ofReal_mul (pow_nonneg hM _)]
          apply ENNReal.ofReal_le_ofReal
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.1 hx.2 3) hx.1
    _ ≤ _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (pow_nonneg hM _)]
      exact mul_le_mul_right hInt _
  have hNon : 0 ≤ M ^ 3 * m := mul_nonneg (pow_nonneg hM _) hm
  have hN : eLpNorm g 4 μ ≤ ENNReal.ofReal ((M ^ 3 * m) ^ (1 / 4 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat]
    rw [← ENNReal.ofReal_rpow_of_nonneg hNon (by norm_num)]
    exact ENNReal.rpow_le_rpow hI (by norm_num)
  exact ⟨⟨hg, hN.trans_lt ENNReal.ofReal_lt_top⟩,
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hN).trans_eq
      (ENNReal.toReal_ofReal (Real.rpow_nonneg hNon _))⟩

theorem toReal_eLpNorm_mul_add_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}
    {f g : X → ℝ} (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 ≤ p)
    {a : ℝ} (ha : 0 ≤ a) :
    (eLpNorm (fun x => a * f x + g x) p μ).toReal ≤
      a * (eLpNorm f p μ).toReal + (eLpNorm g p μ).toReal := by
  have hsum := (hf.const_smul a).add hg
  rw [show (fun x => a * f x + g x) = a • f + g from rfl,
    toReal_eLpNorm hsum.1, toReal_eLpNorm hf.1, toReal_eLpNorm hg.1]
  have H := lpNorm_add_le (hf.const_smul a) (g := g) hp
  simpa only [lpNorm_const_smul, coe_nnnorm, Real.norm_of_nonneg ha] using H

theorem toReal_eLpNorm_const_le_of_measure_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ⊤)
    {m B : ℝ} (hB : 0 ≤ B) (hm : μ univ ≤ ENNReal.ofReal m) (hm₀ : 0 ≤ m) :
    (eLpNorm (fun _ : X => B) p μ).toReal ≤ B * m ^ (1 / p.toReal) := by
  rw [eLpNorm_const' B hp₀ hp, Real.enorm_eq_ofReal hB, ENNReal.toReal_mul, ENNReal.toReal_ofReal hB,
    ← ENNReal.toReal_rpow]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ENNReal.toReal_nonneg
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hm).trans_eq (ENNReal.toReal_ofReal hm₀))
    (div_nonneg zero_le_one ENNReal.toReal_nonneg)) hB

/-- The physical (L^2) gradient and (L^4) forcing bounds transfer to
the actual small-energy scale, including the two powers of the ball
radius in the boundary Poisson estimate. -/
theorem scaled_boundary_morrey_envelopes
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {G q : X → ℝ}
    {t ρ E B₁ B₂ N : ℝ} (ht : 0 < t) (hρ : 0 < ρ)
    (hE : 0 ≤ E) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hN : 0 ≤ N)
    (hG : AEStronglyMeasurable G μ) (hq : AEStronglyMeasurable q μ)
    (hGPos : ∀ᵐ x ∂μ, 0 ≤ G x ∧ G x ≤ 8 / t ^ 2)
    (hqPos : ∀ᵐ x ∂μ, 0 ≤ q x ∧ q x ≤ B₂)
    (hMass : (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ≤ ENNReal.ofReal (4 * E * (t * ρ)))
    (hVol : μ univ ≤ ENNReal.ofReal ((Real.pi * 4 / 3) * (t * ρ) ^ 3)) :
    let r := t * ρ
    let κ := Real.pi * 4 / 3
    MemLp (fun x => Real.sqrt (G x)) 2 μ ∧ MemLp G 4 μ ∧ MemLp q 4 μ ∧
      t * (r ^ (-3 / 2 : ℝ) * (eLpNorm (fun x => N * Real.sqrt (G x) + B₁) 2 μ).toReal +
        r ^ (1 / 4 : ℝ) * (eLpNorm (fun x => N * G x + q x) 4 μ).toReal) ≤
      (2 * N * Real.sqrt E / ρ + t * B₁ * κ ^ (1 / 2 : ℝ)) +
        (N * (2048 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (ρ * Real.sqrt E) + t * r * B₂ * κ ^ (1 / 4 : ℝ)) := by
  let r := t * ρ
  let κ := Real.pi * 4 / 3
  have hr : 0 < r := mul_pos ht hρ
  have hκ : 0 ≤ κ := by dsimp only [κ]; positivity
  have hm : 0 ≤ 4 * E * r := by positivity
  have hVol₀ : 0 ≤ κ * r ^ 3 := by positivity
  have hScale₀ : 0 ≤ 8 / t ^ 2 := by positivity
  haveI : IsFiniteMeasure μ := ⟨hVol.trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨hG₂, h₂⟩ := memLp_sqrt_two_of_lintegral_bound hG (hGPos.mono fun _ h => h.1) hm hMass
  obtain ⟨hG₄, h₄⟩ := memLp_four_of_lintegral_bound_and_ae_le hG hGPos hm hScale₀ hMass
  have hqBound : ∀ᵐ x ∂μ, ‖q x‖ ≤ (fun _ : X => B₂) x :=
    hqPos.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hq₄ : MemLp q 4 μ := (memLp_const B₂).mono' hq hqBound
  have hq₄' : (eLpNorm q 4 μ).toReal ≤ B₂ * (κ * r ^ 3) ^ (1 / 4 : ℝ) := by
    have h := eLpNorm_mono_ae_real (p := 4) hqBound
    have hn : (eLpNorm (fun _ : X => B₂) 4 μ) ≠ ⊤ := (memLp_const B₂).eLpNorm_ne_top
    exact (ENNReal.toReal_mono hn h).trans (by
      simpa only [ENNReal.toReal_ofNat] using toReal_eLpNorm_const_le_of_measure_le
        (p := (4 : ℝ≥0∞)) (by norm_num) (by norm_num) hB₂ hVol hVol₀)
  have hB₁' : (eLpNorm (fun _ : X => B₁) 2 μ).toReal ≤ B₁ * (κ * r ^ 3) ^ (1 / 2 : ℝ) := by
    simpa only [ENNReal.toReal_ofNat] using toReal_eLpNorm_const_le_of_measure_le
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hB₁ hVol hVol₀
  refine ⟨hG₂, hG₄, hq₄, ?_⟩
  have hGrad : (eLpNorm (fun x => N * Real.sqrt (G x) + B₁) 2 μ).toReal ≤
      N * Real.sqrt (4 * E * r) + B₁ * (κ * r ^ 3) ^ (1 / 2 : ℝ) :=
    (toReal_eLpNorm_mul_add_le hG₂ (memLp_const B₁) (by norm_num) hN).trans
      (add_le_add (mul_le_mul_of_nonneg_left h₂ hN) hB₁')
  have hForce : (eLpNorm (fun x => N * G x + q x) 4 μ).toReal ≤
      N * ((8 / t ^ 2) ^ 3 * (4 * E * r)) ^ (1 / 4 : ℝ) + B₂ * (κ * r ^ 3) ^ (1 / 4 : ℝ) :=
    (toReal_eLpNorm_mul_add_le hG₄ hq₄ (by norm_num) hN).trans
      (add_le_add (mul_le_mul_of_nonneg_left h₄ hN) hq₄')
  have hSqrt : Real.sqrt (4 * E * r) = 2 * Real.sqrt E * r ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * E), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      Real.sqrt_eq_rpow r]
  have hC₂ : (κ * r ^ 3) ^ (1 / 2 : ℝ) = κ ^ (1 / 2 : ℝ) * r ^ (3 / 2 : ℝ) := by
    rw [Real.mul_rpow hκ (pow_nonneg hr.le _), ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  have hC₄ : (κ * r ^ 3) ^ (1 / 4 : ℝ) = κ ^ (1 / 4 : ℝ) * r ^ (3 / 4 : ℝ) := by
    rw [Real.mul_rpow hκ (pow_nonneg hr.le _), ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  have hR₂ : r ^ (-3 / 2 : ℝ) * r ^ (1 / 2 : ℝ) = r⁻¹ := by
    rw [← Real.rpow_add hr, show (-3 / 2 : ℝ) + 1 / 2 = -1 by norm_num, Real.rpow_neg_one]
  have hR₂' : r ^ (-3 / 2 : ℝ) * r ^ (3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hr, show (-3 / 2 : ℝ) + 3 / 2 = 0 by norm_num, Real.rpow_zero]
  have hR₄ : r ^ (1 / 4 : ℝ) * r ^ (3 / 4 : ℝ) = r := by
    rw [← Real.rpow_add hr, show (1 / 4 : ℝ) + 3 / 4 = 1 by norm_num, Real.rpow_one]
  have hR₄' : r ^ (1 / 4 : ℝ) * r ^ (1 / 4 : ℝ) = r ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hr, show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num]
  have hT₂ : t * r⁻¹ = ρ⁻¹ := by dsimp only [r]; field_simp [ht.ne', hρ.ne']
  have hT₄ : t * (t ^ (-3 / 2 : ℝ) * r ^ (1 / 2 : ℝ)) = ρ ^ (1 / 2 : ℝ) := by
    rw [show r = t * ρ from rfl, Real.mul_rpow ht.le hρ.le]
    calc
      _ = (t ^ (1 : ℝ) * t ^ (-3 / 2 : ℝ) * t ^ (1 / 2 : ℝ)) * ρ ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one]
        ring
      _ = _ := by rw [← Real.rpow_add ht, ← Real.rpow_add ht, show (1 : ℝ) + (-3 / 2) + 1 / 2 = 0 by norm_num,
        Real.rpow_zero, one_mul]
  have hForceTerm : ((8 / t ^ 2) ^ 3 * (4 * E * r)) ^ (1 / 4 : ℝ) =
      (2048 : ℝ) ^ (1 / 4 : ℝ) * t ^ (-3 / 2 : ℝ) * E ^ (1 / 4 : ℝ) * r ^ (1 / 4 : ℝ) := by
    have hBase : (8 / t ^ 2) ^ 3 * (4 * E * r) = (2048 : ℝ) * ((t ^ 6)⁻¹) * E * r := by
      field_simp [ht.ne']
      ring
    rw [hBase, Real.mul_rpow (by positivity : 0 ≤ (2048 : ℝ) * (t ^ 6)⁻¹ * E) hr.le,
      Real.mul_rpow (by positivity : 0 ≤ (2048 : ℝ) * (t ^ 6)⁻¹) hE,
      Real.mul_rpow (by norm_num : 0 ≤ (2048 : ℝ)) (by positivity),
      Real.inv_rpow (pow_nonneg ht.le 6), ← Real.rpow_natCast, ← Real.rpow_mul ht.le,
      ← Real.rpow_neg ht.le]
    norm_num
  have hSqrt' : ρ ^ (1 / 2 : ℝ) * E ^ (1 / 4 : ℝ) = Real.sqrt (ρ * Real.sqrt E) := by
    rw [Real.sqrt_mul hρ.le, Real.sqrt_eq_rpow ρ, Real.sqrt_eq_rpow (Real.sqrt E),
      Real.sqrt_eq_rpow E, ← Real.rpow_mul hE]
    norm_num
  change t * (r ^ (-3 / 2 : ℝ) * _ + r ^ (1 / 4 : ℝ) * _) ≤ _
  refine (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hGrad (Real.rpow_nonneg hr.le _))
    (mul_le_mul_of_nonneg_left hForce (Real.rpow_nonneg hr.le _))) ht.le).trans_eq ?_
  rw [hSqrt, hC₂, hC₄, hForceTerm]
  have hL : t * (r ^ (-3 / 2 : ℝ) * (N * (2 * Real.sqrt E * r ^ (1 / 2 : ℝ)) +
      B₁ * (κ ^ (1 / 2 : ℝ) * r ^ (3 / 2 : ℝ)))) =
      2 * N * Real.sqrt E / ρ + t * B₁ * κ ^ (1 / 2 : ℝ) := by
    calc
      _ = 2 * N * Real.sqrt E * (t * (r ^ (-3 / 2 : ℝ) * r ^ (1 / 2 : ℝ))) +
          t * B₁ * κ ^ (1 / 2 : ℝ) * (r ^ (-3 / 2 : ℝ) * r ^ (3 / 2 : ℝ)) := by ring
      _ = _ := by rw [hR₂, hR₂', hT₂, div_eq_mul_inv (2 * N * Real.sqrt E) ρ, mul_one]
  have hF : t * (r ^ (1 / 4 : ℝ) * (N * ((2048 : ℝ) ^ (1 / 4 : ℝ) * t ^ (-3 / 2 : ℝ) *
      E ^ (1 / 4 : ℝ) * r ^ (1 / 4 : ℝ)) + B₂ * (κ ^ (1 / 4 : ℝ) * r ^ (3 / 4 : ℝ)))) =
      N * (2048 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (ρ * Real.sqrt E) + t * r * B₂ * κ ^ (1 / 4 : ℝ) := by
    calc
      _ = N * (2048 : ℝ) ^ (1 / 4 : ℝ) *
          ((t * (t ^ (-3 / 2 : ℝ) * (r ^ (1 / 4 : ℝ) * r ^ (1 / 4 : ℝ)))) * E ^ (1 / 4 : ℝ)) +
          t * (r ^ (1 / 4 : ℝ) * r ^ (3 / 4 : ℝ)) * B₂ * κ ^ (1 / 4 : ℝ) := by ring
      _ = _ := by rw [hR₄', hT₄, hSqrt', hR₄]
  rw [mul_add, hL, hF]

end Thesis

end
