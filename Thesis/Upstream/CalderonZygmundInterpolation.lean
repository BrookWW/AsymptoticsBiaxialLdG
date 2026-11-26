module

public import Thesis.Definitions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Prod

/-! Layer-cake interpolation of a weak first-moment and strong second-moment bound. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Thesis

private theorem lintegral_rpow_Ioo (a s : ℝ) (ha : 0 < a) (hs : -1 < s) :
    (∫⁻ t in Ioo 0 a, ENNReal.ofReal (t^s)) = ENNReal.ofReal (a^(s+1)/(s+1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegral.integrableOn_Ioo_rpow_iff ha).2 hs)
    ((ae_restrict_mem measurableSet_Ioo).mono (fun t ht => Real.rpow_nonneg ht.1.le _)),
    restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le ha.le,
    integral_rpow (Or.inl hs), Real.zero_rpow (by linarith : s+1 ≠ 0), sub_zero]

private theorem lintegral_rpow_Ici (a s : ℝ) (ha : 0 < a) (hs : s < -1) :
    (∫⁻ t in Ici a, ENNReal.ofReal (t^s)) = ENNReal.ofReal (-a^(s+1)/(s+1)) := by
  rw [← restrict_Ioi_eq_restrict_Ici,
    ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_Ioi_rpow_of_lt hs ha)
      ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht => Real.rpow_nonneg (ha.trans ht).le _)),
    integral_Ioi_rpow_of_lt hs ha]

private theorem cz_high_scalar {p : ℝ} (hp : 1 < p) {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ t in Ioi 0, (if t < a then ENNReal.ofReal a else 0) * ENNReal.ofReal (t^(p-2))) =
      ENNReal.ofReal ((p-1)⁻¹) * ENNReal.ofReal (a^p) := by
  have hp₀ : 0 < p := zero_lt_one.trans hp
  rcases ha.eq_or_lt with rfl | ha
  · simp [Real.zero_rpow hp₀.ne']
  have he : (Ioi (0:ℝ)).indicator (fun t => (if t < a then ENNReal.ofReal a else 0) *
      ENNReal.ofReal (t^(p-2))) = (Ioo 0 a).indicator (fun t =>
        ENNReal.ofReal a * ENNReal.ofReal (t^(p-2))) := by
    funext t
    by_cases h₀ : 0 < t <;> by_cases h₁ : t < a <;> simp [h₀,h₁]
  rw [← lintegral_indicator measurableSet_Ioi, he, lintegral_indicator measurableSet_Ioo,
    lintegral_const_mul _ (by fun_prop), lintegral_rpow_Ioo _ _ ha (by linarith),
    show p-2+1 = p-1 by ring, ← ENNReal.ofReal_mul ha.le,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (p-1)⁻¹)]
  congr 1
  have hPow : a*a^(p-1) = a^p := by
    calc
      _ = a^(1:ℝ)*a^(p-1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add ha, show 1+(p-1)=p by ring]
  rw [div_eq_mul_inv, ← mul_assoc, hPow, mul_comm]

private theorem cz_low_scalar {p : ℝ} (hp : 1 < p) (hq : p < 2) {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ t in Ioi 0, (if a ≤ t then ENNReal.ofReal (a^2) else 0) * ENNReal.ofReal (t^(p-3))) =
      ENNReal.ofReal ((2-p)⁻¹) * ENNReal.ofReal (a^p) := by
  have hp₀ : 0 < p := zero_lt_one.trans hp
  rcases ha.eq_or_lt with rfl | ha
  · simp [Real.zero_rpow hp₀.ne']
  have he : (Ioi (0:ℝ)).indicator (fun t => (if a ≤ t then ENNReal.ofReal (a^2) else 0) *
      ENNReal.ofReal (t^(p-3))) = (Ici a).indicator (fun t =>
        ENNReal.ofReal (a^2) * ENNReal.ofReal (t^(p-3))) := by
    funext t
    by_cases h₁ : a ≤ t
    · simp [ha.trans_le h₁,h₁]
    · simp [h₁]
  rw [← lintegral_indicator measurableSet_Ioi, he, lintegral_indicator measurableSet_Ici,
    lintegral_const_mul _ (by fun_prop), lintegral_rpow_Ici _ _ ha (by linarith),
    show p-3+1=p-2 by ring, ← ENNReal.ofReal_mul (sq_nonneg a),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2-p)⁻¹)]
  congr 1
  rw [show -(a^(p-2))/(p-2) = a^(p-2)*(2-p)⁻¹ by
    rw [neg_div, ← div_neg,show -(p-2)=2-p by ring,div_eq_mul_inv],
    ← mul_assoc, ← Real.rpow_two, ← Real.rpow_add ha, show 2+(p-2)=p by ring, mul_comm]

/-- Layer-cake integrals of the high first and low second moments. -/
theorem cz_truncated_moments {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {f : X → ℝ} (hf : Measurable f) {p : ℝ} (hp : 1 < p) (hq : p < 2) :
    (∫⁻ t in Ioi 0, (∫⁻ x, if t < |f x| then ENNReal.ofReal |f x| else 0 ∂μ) *
        ENNReal.ofReal (t^(p-2))) =
      ENNReal.ofReal ((p-1)⁻¹) * ∫⁻ x, ENNReal.ofReal (|f x|^p) ∂μ ∧
    (∫⁻ t in Ioi 0, (∫⁻ x, if |f x| ≤ t then ENNReal.ofReal (|f x|^2) else 0 ∂μ) *
        ENNReal.ofReal (t^(p-3))) =
      ENNReal.ofReal ((2-p)⁻¹) * ∫⁻ x, ENNReal.ofReal (|f x|^p) ∂μ := by
  have hF : Measurable (fun x => |f x|) := hf.abs
  let μ₀ := volume.restrict (Ioi (0:ℝ))
  constructor
  · have hm₀ (t : ℝ) : Measurable (fun x : X => if t < |f x| then ENNReal.ofReal |f x| else 0) := by
      exact Measurable.ite (measurableSet_lt measurable_const hF) hF.ennreal_ofReal measurable_const
    simp_rw [← lintegral_mul_const _ (hm₀ _)]
    let F (t : ℝ) (x : X) := (if t < |f x| then ENNReal.ofReal |f x| else 0)*ENNReal.ofReal (t^(p-2))
    have hm : Measurable (Function.uncurry F) := by
      change Measurable (fun y : ℝ × X =>
        (if y.1 < |f y.2| then ENNReal.ofReal |f y.2| else 0) * ENNReal.ofReal (y.1^(p-2)))
      exact (Measurable.ite (measurableSet_lt measurable_fst (hF.comp measurable_snd))
        (hF.comp measurable_snd).ennreal_ofReal measurable_const).mul (by fun_prop)
    rw [lintegral_lintegral_swap (μ := μ₀) (ν := μ) (f := F) hm.aemeasurable]
    dsimp only [F,μ₀]
    simp_rw [cz_high_scalar hp (abs_nonneg (f _))]
    exact lintegral_const_mul _ (by fun_prop)
  · have hm₀ (t : ℝ) : Measurable (fun x : X => if |f x| ≤ t then ENNReal.ofReal (|f x|^2) else 0) := by
      exact Measurable.ite (measurableSet_le hF measurable_const)
        (hF.pow_const (2:ℕ)).ennreal_ofReal measurable_const
    simp_rw [← lintegral_mul_const _ (hm₀ _)]
    let F (t : ℝ) (x : X) := (if |f x| ≤ t then ENNReal.ofReal (|f x|^2) else 0)*ENNReal.ofReal (t^(p-3))
    have hm : Measurable (Function.uncurry F) := by
      change Measurable (fun y : ℝ × X =>
        (if |f y.2| ≤ y.1 then ENNReal.ofReal (|f y.2|^2) else 0) * ENNReal.ofReal (y.1^(p-3)))
      exact (Measurable.ite (measurableSet_le (hF.comp measurable_snd) measurable_fst)
        ((hF.comp measurable_snd).pow_const (2:ℕ)).ennreal_ofReal measurable_const).mul (by fun_prop)
    rw [lintegral_lintegral_swap (μ := μ₀) (ν := μ) (f := F) hm.aemeasurable]
    dsimp only [F,μ₀]
    simp_rw [cz_low_scalar hp hq (abs_nonneg (f _))]
    exact lintegral_const_mul _ (by fun_prop)

/-- A distribution estimate from the first moment above the level and the
second moment below it gives the strong moment bound for `1 < p < 2`. -/
theorem cz_strong_moment_of_truncated_superlevel {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ : Measure X} [SFinite μ] {ν : Measure Y} {f : X → ℝ} {g : Y → ℝ}
    (hf : Measurable f) (hg : AEMeasurable g ν) {p : ℝ} (hp : 1 < p) (hq : p < 2)
    (A B : ℝ≥0∞)
    (hTail : ∀ t : ℝ, 0 < t → ν {y | t < |g y|} ≤
      A * ENNReal.ofReal (t⁻¹) * (∫⁻ x, if t < |f x| then ENNReal.ofReal |f x| else 0 ∂μ) +
      B * ENNReal.ofReal ((t^2)⁻¹) * (∫⁻ x, if |f x| ≤ t then ENNReal.ofReal (|f x|^2) else 0 ∂μ)) :
    (∫⁻ y, ENNReal.ofReal (|g y|^p) ∂ν) ≤
      (ENNReal.ofReal p * (A*ENNReal.ofReal ((p-1)⁻¹)+B*ENNReal.ofReal ((2-p)⁻¹))) *
        ∫⁻ x, ENNReal.ofReal (|f x|^p) ∂μ := by
  let H (t : ℝ) := ∫⁻ x, if t < |f x| then ENNReal.ofReal |f x| else 0 ∂μ
  let L (t : ℝ) := ∫⁻ x, if |f x| ≤ t then ENNReal.ofReal (|f x|^2) else 0 ∂μ
  have hH : Measurable H := by
    have hh := hf.abs.comp (measurable_snd : Measurable (Prod.snd : ℝ × X → X))
    exact (Measurable.ite (measurableSet_lt measurable_fst hh)
      hh.ennreal_ofReal measurable_const).lintegral_prod_right'
  have hL : Measurable L := by
    have hh := hf.abs.comp (measurable_snd : Measurable (Prod.snd : ℝ × X → X))
    exact (Measurable.ite (measurableSet_le hh measurable_fst)
      (hh.pow_const (2:ℕ)).ennreal_ofReal measurable_const).lintegral_prod_right'
  have hHigh : Measurable (fun t : ℝ => H t * ENNReal.ofReal (t^(p-2))) := by fun_prop
  have hLow : Measurable (fun t : ℝ => L t * ENNReal.ofReal (t^(p-3))) := by fun_prop
  have h₁ (t : ℝ) (ht : 0 < t) : ENNReal.ofReal (t⁻¹) * ENNReal.ofReal (t^(p-1)) =
      ENNReal.ofReal (t^(p-2)) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le), ← Real.rpow_neg_one, ← Real.rpow_add ht,
      show (-1 : ℝ)+(p-1)=p-2 by ring]
  have h₂ (t : ℝ) (ht : 0 < t) : ENNReal.ofReal ((t^2)⁻¹) * ENNReal.ofReal (t^(p-1)) =
      ENNReal.ofReal (t^(p-3)) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg t)), ← Real.rpow_two,
      ← Real.rpow_neg ht.le, ← Real.rpow_add ht, show (-2 : ℝ)+(p-1)=p-3 by ring]
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul ν (Eventually.of_forall fun _ => abs_nonneg _) hg.abs
    (zero_lt_one.trans hp)]
  have hTail' (t : ℝ) (ht : 0 < t) :
      ν {y | t < |g y|} * ENNReal.ofReal (t^(p-1)) ≤
      A*(H t * ENNReal.ofReal (t^(p-2))) + B*(L t * ENNReal.ofReal (t^(p-3))) := by
    have h := hTail t ht
    change ν {y | t < |g y|} ≤
      A * ENNReal.ofReal (t⁻¹) * H t + B * ENNReal.ofReal ((t^2)⁻¹) * L t at h
    refine (show ν {y | t < |g y|} * ENNReal.ofReal (t^(p-1)) ≤
      (A * ENNReal.ofReal (t⁻¹) * H t + B * ENNReal.ofReal ((t^2)⁻¹) * L t) *
        ENNReal.ofReal (t^(p-1)) from by gcongr).trans_eq ?_
    rw [add_mul, ← h₁ t ht, ← h₂ t ht]
    ac_rfl
  have hMom := cz_truncated_moments (μ := μ) hf hp hq
  change (∫⁻ t in Ioi 0, H t * ENNReal.ofReal (t^(p-2))) = _ ∧
    (∫⁻ t in Ioi 0, L t * ENNReal.ofReal (t^(p-3))) = _ at hMom
  have hBound : (∫⁻ t in Ioi 0, ν {y | t < |g y|} * ENNReal.ofReal (t^(p-1))) ≤
      ∫⁻ t in Ioi 0, A*(H t * ENNReal.ofReal (t^(p-2))) + B*(L t * ENNReal.ofReal (t^(p-3))) :=
    lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono (fun t ht => hTail' t ht))
  refine (mul_le_mul_right hBound (ENNReal.ofReal p)).trans_eq ?_
  have hAH : Measurable (fun t : ℝ => A*(H t * ENNReal.ofReal (t^(p-2)))) :=
    measurable_const.mul hHigh
  rw [lintegral_add_left hAH, lintegral_const_mul _ hHigh,
    lintegral_const_mul _ hLow, hMom.1, hMom.2]
  ring

end Thesis

end
