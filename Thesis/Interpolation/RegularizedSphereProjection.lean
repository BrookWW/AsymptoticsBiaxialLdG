module

public import Thesis.Interpolation.ShiftedSphereProjection
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecificLimits.Basic

/-! Smooth approximations to a shifted sphere projection and their energy majorant. -/

@[expose] public section

noncomputable section

open Filter
open scoped ContDiff InnerProductSpace Topology

namespace Thesis

def regularizedSphereRadius (y : QuaternionCoordinates) (δ : ℝ) (z : QuaternionCoordinates) : ℝ :=
  Real.sqrt (‖z - y‖ ^ 2 + δ ^ 2)

def regularizedSphereDirection (y : QuaternionCoordinates) (δ : ℝ)
    (z : QuaternionCoordinates) : QuaternionCoordinates :=
  (regularizedSphereRadius y δ z)⁻¹ • (z - y)

theorem regularizedSphereRadius_pos {y z : QuaternionCoordinates} {δ : ℝ}
    (h : z ≠ y ∨ δ ≠ 0) : 0 < regularizedSphereRadius y δ z := by
  apply Real.sqrt_pos.2
  rcases h with hz | hδ
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hz))) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hδ)

theorem norm_sub_le_regularizedSphereRadius (y : QuaternionCoordinates) (δ : ℝ)
    (z : QuaternionCoordinates) : ‖z - y‖ ≤ regularizedSphereRadius y δ z := by
  unfold regularizedSphereRadius
  rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
  linarith [sq_nonneg δ]

theorem abs_le_regularizedSphereRadius (y : QuaternionCoordinates) (δ : ℝ)
    (z : QuaternionCoordinates) : |δ| ≤ regularizedSphereRadius y δ z := by
  unfold regularizedSphereRadius
  rw [Real.le_sqrt (abs_nonneg _) (by positivity), sq_abs]
  linarith [sq_nonneg ‖z - y‖]

theorem norm_regularizedSphereDirection_le_one (y : QuaternionCoordinates) (δ : ℝ)
    (z : QuaternionCoordinates) : ‖regularizedSphereDirection y δ z‖ ≤ 1 := by
  by_cases h : z = y ∧ δ = 0
  · simp [regularizedSphereDirection, h.1, h.2]
  · have hs := regularizedSphereRadius_pos (y := y) (z := z) (δ := δ) (not_and_or.1 h)
    rw [regularizedSphereDirection, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg hs.le,
      ← div_eq_inv_mul, div_le_one hs]
    exact norm_sub_le_regularizedSphereRadius y δ z

theorem contDiffAt_regularizedSphereDirection {y z : QuaternionCoordinates} {δ : ℝ}
    (h : z ≠ y ∨ δ ≠ 0) : ContDiffAt ℝ ∞ (regularizedSphereDirection y δ) z := by
  have hz : ContDiffAt ℝ ∞ (fun x : QuaternionCoordinates => x - y) z :=
    contDiffAt_id.sub contDiffAt_const
  have hs := regularizedSphereRadius_pos h
  have hN : ContDiffAt ℝ ∞ (regularizedSphereRadius y δ) z :=
    ((hz.norm_sq (𝕜 := ℝ)).add contDiffAt_const).sqrt (Real.sqrt_pos.1 hs).ne'
  exact ((contDiffAt_inv ℝ hs.ne').comp z hN).smul hz

theorem contDiff_regularizedSphereDirection (y : QuaternionCoordinates) {δ : ℝ} (hδ : δ ≠ 0) :
    ContDiff ℝ ∞ (regularizedSphereDirection y δ) :=
  contDiff_iff_contDiffAt.2 fun _ => contDiffAt_regularizedSphereDirection (Or.inr hδ)

theorem fderiv_regularizedSphereDirection_apply {y z : QuaternionCoordinates} {δ : ℝ}
    (h : z ≠ y ∨ δ ≠ 0) (v : QuaternionCoordinates) :
    fderiv ℝ (regularizedSphereDirection y δ) z v =
      (regularizedSphereRadius y δ z)⁻¹ • v -
        (⟪z - y, v⟫_ℝ / (regularizedSphereRadius y δ z) ^ 3) • (z - y) := by
  let s := regularizedSphereRadius y δ z
  have hs : 0 < s := regularizedSphereRadius_pos h
  have hArg : 0 < ‖z - y‖ ^ 2 + δ ^ 2 := Real.sqrt_pos.1 hs
  have hZ : HasFDerivAt (fun x : QuaternionCoordinates => x - y)
      (ContinuousLinearMap.id ℝ QuaternionCoordinates) z :=
    (hasFDerivAt_id (𝕜 := ℝ) z).sub_const y
  have hS := (hZ.norm_sq.add_const (δ ^ 2)).sqrt hArg.ne'
  change HasFDerivAt (regularizedSphereRadius y δ)
    ((1 / (2 * s)) • (2 • (innerSL ℝ (z - y)).comp (ContinuousLinearMap.id ℝ _))) z at hS
  have hI := (hasDerivAt_inv hs.ne').comp_hasFDerivAt z hS
  have hP : HasFDerivAt (regularizedSphereDirection y δ)
      (s⁻¹ • ContinuousLinearMap.id ℝ _ +
        ((-(s ^ 2)⁻¹) • ((1 / (2 * s)) • (2 • (innerSL ℝ (z - y)).comp
          (ContinuousLinearMap.id ℝ _)))).smulRight (z - y)) z := hI.smul hZ
  rw [hP.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  change s⁻¹ • v + (-(s ^ 2)⁻¹ * ((1 / (2 * s)) * (2 * ⟪z - y, v⟫_ℝ))) • (z - y) = _
  rw [show -(s ^ 2)⁻¹ * ((1 / (2 * s)) * (2 * ⟪z - y, v⟫_ℝ)) =
    -(⟪z - y, v⟫_ℝ / s ^ 3) by field_simp, neg_smul]
  exact (sub_eq_add_neg _ _).symm

theorem norm_fderiv_regularizedSphereDirection_le {y z : QuaternionCoordinates} {δ : ℝ}
    (h : z ≠ y ∨ δ ≠ 0) :
    ‖fderiv ℝ (regularizedSphereDirection y δ) z‖ ≤ 2 / regularizedSphereRadius y δ z := by
  let s := regularizedSphereRadius y δ z
  have hs : 0 < s := regularizedSphereRadius_pos h
  have hZS : ‖z - y‖ ≤ s := norm_sub_le_regularizedSphereRadius y δ z
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [fderiv_regularizedSphereDirection_apply h]
  change ‖s⁻¹ • v - (⟪z - y, v⟫_ℝ / s ^ 3) • (z - y)‖ ≤ (2 / s) * ‖v‖
  calc
    _ ≤ ‖s⁻¹ • v‖ + ‖(⟪z - y, v⟫_ℝ / s ^ 3) • (z - y)‖ := norm_sub_le _ _
    _ ≤ s⁻¹ * ‖v‖ + ((‖z - y‖ * ‖v‖) / s ^ 3) * ‖z - y‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg hs.le, abs_div,
        abs_of_nonneg (pow_nonneg hs.le 3)]
      gcongr
      exact abs_real_inner_le_norm _ _
    _ ≤ s⁻¹ * ‖v‖ + ((s * ‖v‖) / s ^ 3) * s := by gcongr
    _ = _ := by field_simp; ring

theorem regularizedSphereDirection_zero (y z : QuaternionCoordinates) :
    regularizedSphereDirection y 0 z = shiftedSphereDirection y z := by
  simp [regularizedSphereDirection, regularizedSphereRadius, shiftedSphereDirection]

theorem continuousAt_regularizedSphereDirection_scale {y z : QuaternionCoordinates} (hz : z ≠ y) :
    ContinuousAt (fun δ : ℝ => regularizedSphereDirection y δ z) 0 := by
  have hRadius : ContinuousAt (fun δ : ℝ => regularizedSphereRadius y δ z) 0 := by
    unfold regularizedSphereRadius
    fun_prop
  have h0 := (regularizedSphereRadius_pos (δ := 0) (Or.inl hz)).ne'
  exact (hRadius.inv₀ h0).smul continuousAt_const

theorem continuousAt_fderiv_regularizedSphereDirection_scale {y z : QuaternionCoordinates}
    (hz : z ≠ y) (v : QuaternionCoordinates) :
    ContinuousAt (fun δ : ℝ => fderiv ℝ (regularizedSphereDirection y δ) z v) 0 := by
  let r : ℝ → ℝ := fun δ => regularizedSphereRadius y δ z
  let b : ℝ := ⟪z - y, v⟫_ℝ
  have hRadius : ContinuousAt r 0 := by
    dsimp only [r, regularizedSphereRadius]
    fun_prop
  have h0 : r 0 ≠ 0 := (regularizedSphereRadius_pos (δ := 0) (Or.inl hz)).ne'
  have hp : ContinuousAt (fun δ => (r δ)⁻¹ • v) 0 :=
    (hRadius.inv₀ h0).smul continuousAt_const
  have hq : ContinuousAt (fun δ => (b / (r δ) ^ 3) • (z - y)) 0 :=
    (continuousAt_const.div₀ (hRadius.pow 3) (pow_ne_zero _ h0)).smul continuousAt_const
  have heq : (fun δ : ℝ => fderiv ℝ (regularizedSphereDirection y δ) z v) =
      fun δ => (r δ)⁻¹ • v - (b / (r δ) ^ 3) • (z - y) := by
    funext δ
    exact fderiv_regularizedSphereDirection_apply (Or.inl hz) v
  rw [heq]
  exact hp.sub hq

def correctedSphereProjection (y : QuaternionCoordinates) (δ : ℝ) :
    QuaternionCoordinates → QuaternionCoordinates :=
  restoreSphereDirection y ∘ regularizedSphereDirection y δ

theorem norm_correctedSphereProjection_le_two {y : QuaternionCoordinates} (hy : ‖y‖ ≤ 1 / 4)
    (δ : ℝ) (z : QuaternionCoordinates) : ‖correctedSphereProjection y δ z‖ ≤ 2 :=
  norm_restoreSphereDirection_le_two hy (norm_regularizedSphereDirection_le_one y δ z)

theorem norm_correctedSphereProjection_zero {y z : QuaternionCoordinates} (hy : ‖y‖ ≤ 1 / 4)
    (hz : z ≠ y) : ‖correctedSphereProjection y 0 z‖ = 1 := by
  unfold correctedSphereProjection
  rw [Function.comp_apply, regularizedSphereDirection_zero]
  exact norm_restoreSphereDirection hy (norm_shiftedSphereDirection hz)

@[simp] theorem correctedSphereProjection_zero_apply_of_norm_eq_one {y z : QuaternionCoordinates}
    (hy : ‖y‖ ≤ 1 / 4) (hz : ‖z‖ = 1) : correctedSphereProjection y 0 z = z := by
  unfold correctedSphereProjection
  rw [Function.comp_apply, regularizedSphereDirection_zero]
  exact restoreSphereDirection_shiftedSphereDirection hy hz

theorem fderiv_correctedSphereProjection {y z : QuaternionCoordinates} {δ : ℝ}
    (hR : ContDiff ℝ ∞ (restoreSphereDirection y)) (hh : z ≠ y ∨ δ ≠ 0) :
    fderiv ℝ (correctedSphereProjection y δ) z =
      (fderiv ℝ (restoreSphereDirection y) (regularizedSphereDirection y δ z)).comp
        (fderiv ℝ (regularizedSphereDirection y δ) z) :=
  fderiv_comp z (hR.differentiable (by simp)).differentiableAt
    ((contDiffAt_regularizedSphereDirection hh).differentiableAt (by simp))

theorem continuousAt_correctedSphereProjection_scale {y z : QuaternionCoordinates}
    (hR : ContDiff ℝ ∞ (restoreSphereDirection y)) (hz : z ≠ y) :
    ContinuousAt (fun δ : ℝ => correctedSphereProjection y δ z) 0 :=
  hR.continuous.continuousAt.comp (continuousAt_regularizedSphereDirection_scale hz)

theorem continuousAt_fderiv_correctedSphereProjection_scale {y z : QuaternionCoordinates}
    (hR : ContDiff ℝ ∞ (restoreSphereDirection y)) (hz : z ≠ y) (v : QuaternionCoordinates) :
    ContinuousAt (fun δ : ℝ => fderiv ℝ (correctedSphereProjection y δ) z v) 0 := by
  simp only [fderiv_correctedSphereProjection hR (Or.inl hz), ContinuousLinearMap.comp_apply]
  exact (((hR.continuous_fderiv (by simp)).continuousAt).comp
    (continuousAt_regularizedSphereDirection_scale hz)).clm_apply
      (continuousAt_fderiv_regularizedSphereDirection_scale hz v)

theorem norm_fderiv_correctedSphereProjection_le {y z : QuaternionCoordinates} {δ C : ℝ}
    (hR : ContDiff ℝ ∞ (restoreSphereDirection y))
    (hDR : ∀ ξ, ‖ξ‖ ≤ 1 → ‖fderiv ℝ (restoreSphereDirection y) ξ‖ ≤ C)
    (hh : z ≠ y ∨ δ ≠ 0) :
    ‖fderiv ℝ (correctedSphereProjection y δ) z‖ ≤ 2 * C / regularizedSphereRadius y δ z := by
  rw [fderiv_correctedSphereProjection hR hh]
  have hC : 0 ≤ C := (norm_nonneg _).trans (hDR 0 (by simp))
  calc
    _ ≤ ‖fderiv ℝ (restoreSphereDirection y) (regularizedSphereDirection y δ z)‖ *
        ‖fderiv ℝ (regularizedSphereDirection y δ) z‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * (2 / regularizedSphereRadius y δ z) :=
      mul_le_mul (hDR _ (norm_regularizedSphereDirection_le_one y δ z))
        (norm_fderiv_regularizedSphereDirection_le hh) (norm_nonneg _) hC
    _ = _ := by ring

end Thesis
