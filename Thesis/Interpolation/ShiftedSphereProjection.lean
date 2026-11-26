module

public import Thesis.Definitions
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Radial projection from an interior center, corrected to fix the original sphere. -/

@[expose] public section

noncomputable section

open Metric Set
open scoped ContDiff InnerProductSpace

namespace Thesis

def shiftedSphereDirection (y z : QuaternionCoordinates) : QuaternionCoordinates :=
  ‖z - y‖⁻¹ • (z - y)

def restoreSphereDirection (y ξ : QuaternionCoordinates) : QuaternionCoordinates :=
  y + (-⟪y, ξ⟫_ℝ + Real.sqrt (⟪y, ξ⟫_ℝ ^ 2 + 1 - ‖y‖ ^ 2)) • ξ

theorem norm_shiftedSphereDirection {y z : QuaternionCoordinates} (hz : z ≠ y) :
    ‖shiftedSphereDirection y z‖ = 1 := by
  rw [shiftedSphereDirection, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (sub_ne_zero.mpr hz))

theorem norm_restoreSphereDirection {y ξ : QuaternionCoordinates} (hy : ‖y‖ ≤ 1 / 4)
    (hξ : ‖ξ‖ = 1) : ‖restoreSphereDirection y ξ‖ = 1 := by
  let b := ⟪y, ξ⟫_ℝ
  have hArg : 0 ≤ b ^ 2 + 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y, sq_nonneg b]
  let s := Real.sqrt (b ^ 2 + 1 - ‖y‖ ^ 2)
  have hs : s ^ 2 = b ^ 2 + 1 - ‖y‖ ^ 2 := Real.sq_sqrt hArg
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1
  change ‖y + (-b + s) • ξ‖ ^ 2 = 1 ^ 2
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hξ, mul_one, sq_abs]
  change ‖y‖ ^ 2 + 2 * ((-b + s) * b) + (-b + s) ^ 2 = 1 ^ 2
  nlinarith

theorem norm_restoreSphereDirection_le_two {y ξ : QuaternionCoordinates}
    (hy : ‖y‖ ≤ 1 / 4) (hξ : ‖ξ‖ ≤ 1) : ‖restoreSphereDirection y ξ‖ ≤ 2 := by
  let b := ⟪y, ξ⟫_ℝ
  have hb : |b| ≤ ‖y‖ := (abs_real_inner_le_norm y ξ).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hξ (norm_nonneg y))
  have hbsq : b ^ 2 ≤ ‖y‖ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  let s := Real.sqrt (b ^ 2 + 1 - ‖y‖ ^ 2)
  have hs : s ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show b ^ 2 + 1 - ‖y‖ ^ 2 ≤ 1 by linarith)
  have habs : |-b + s| ≤ 5 / 4 := calc
    _ ≤ |-b| + |s| := abs_add_le _ _
    _ = |b| + s := by rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ 5 / 4 := by linarith
  change ‖y + (-b + s) • ξ‖ ≤ 2
  calc
    _ ≤ ‖y‖ + ‖(-b + s) • ξ‖ := norm_add_le _ _
    _ = ‖y‖ + |-b + s| * ‖ξ‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 / 4 + (5 / 4) * 1 := by gcongr
    _ ≤ 2 := by norm_num

/-- The corrected radial projection fixes every value on the original unit sphere. -/
theorem restoreSphereDirection_shiftedSphereDirection {y z : QuaternionCoordinates}
    (hy : ‖y‖ ≤ 1 / 4) (hz : ‖z‖ = 1) :
    restoreSphereDirection y (shiftedSphereDirection y z) = z := by
  let d := ‖z - y‖
  have hd : 3 / 4 ≤ d := by
    have h := norm_add_le (z - y) y
    rw [sub_add_cancel, hz] at h
    change 3 / 4 ≤ ‖z - y‖
    linarith
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  let ξ := shiftedSphereDirection y z
  have hξ : ‖ξ‖ = 1 := norm_shiftedSphereDirection (sub_ne_zero.1 (norm_pos_iff.1 hd0))
  have hrad : d • ξ = z - y := by
    change d • (d⁻¹ • (z - y)) = z - y
    rw [smul_smul, mul_inv_cancel₀ hd0.ne', one_smul]
  have hsum : y + d • ξ = z := by rw [hrad]; abel
  let b := ⟪y, ξ⟫_ℝ
  have hb : -‖y‖ ≤ b := by
    have h := abs_real_inner_le_norm y ξ
    rw [hξ, mul_one] at h
    exact neg_le_of_abs_le h
  have hquad : ‖y‖ ^ 2 + 2 * (d * b) + d ^ 2 = 1 ^ 2 := by
    have h := congrArg (fun x : QuaternionCoordinates => ‖x‖ ^ 2) hsum
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hd0.le, hξ, mul_one, hz] at h
    exact h
  have hArg : 0 ≤ b ^ 2 + 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y, sq_nonneg b]
  have hSqrt : Real.sqrt (b ^ 2 + 1 - ‖y‖ ^ 2) = d + b :=
    (Real.sqrt_eq_iff_eq_sq hArg (by linarith)).2 (by nlinarith)
  change y + (-b + Real.sqrt (b ^ 2 + 1 - ‖y‖ ^ 2)) • ξ = z
  rw [hSqrt, show -b + (d + b) = d by ring, hsum]

theorem contDiffOn_restoreSphereDirection :
    ContDiffOn ℝ ∞ (fun p : QuaternionCoordinates × QuaternionCoordinates =>
      restoreSphereDirection p.1 p.2) {p | ‖p.1‖ < 1} := by
  intro p hp
  have hy : ‖p.1‖ < 1 := hp
  have hArg : 0 < ⟪p.1, p.2⟫_ℝ ^ 2 + 1 - ‖p.1‖ ^ 2 := by
    nlinarith [norm_nonneg p.1, sq_nonneg ⟪p.1, p.2⟫_ℝ]
  have hB : ContDiffAt ℝ ∞ (fun q : QuaternionCoordinates × QuaternionCoordinates =>
      ⟪q.1, q.2⟫_ℝ) p := contDiffAt_inner
  have hFst : ContDiffAt ℝ ∞ (fun q : QuaternionCoordinates × QuaternionCoordinates => q.1) p :=
    contDiffAt_fst
  have hN : ContDiffAt ℝ ∞ (fun q : QuaternionCoordinates × QuaternionCoordinates => ‖q.1‖ ^ 2) p :=
    hFst.norm_sq (𝕜 := ℝ)
  have hS := ((hB.pow 2).add contDiffAt_const |>.sub hN).sqrt hArg.ne'
  exact (contDiffAt_fst.add ((hB.neg.add hS).smul contDiffAt_snd)).contDiffWithinAt

/-- The trace restoration maps are smooth with a common derivative bound on the unit ball. -/
theorem exists_fderiv_restoreSphereDirection_bound : ∃ C : ℝ, 0 < C ∧
    ∀ y : QuaternionCoordinates, ‖y‖ ≤ 1 / 4 →
      ContDiff ℝ ∞ (restoreSphereDirection y) ∧
      ∀ ξ : QuaternionCoordinates, ‖ξ‖ ≤ 1 → ‖fderiv ℝ (restoreSphereDirection y) ξ‖ ≤ C := by
  let F := fun p : QuaternionCoordinates × QuaternionCoordinates => restoreSphereDirection p.1 p.2
  let U := {p : QuaternionCoordinates × QuaternionCoordinates | ‖p.1‖ < 1}
  let K := closedBall (0 : QuaternionCoordinates) (1 / 4) ×ˢ closedBall (0 : QuaternionCoordinates) 1
  have hU : IsOpen U := isOpen_lt continuous_fst.norm continuous_const
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKU : K ⊆ U := by
    intro p hp
    have hnorm : ‖p.1‖ ≤ 1 / 4 := by
      simpa only [mem_closedBall, dist_zero_right] using hp.1
    change ‖p.1‖ < 1
    linarith
  have hS : ContDiffOn ℝ ∞ F U := contDiffOn_restoreSphereDirection
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    ((hS.continuousOn_fderiv_of_isOpen hU (by simp)).mono hKU)
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro y hy
  have hyU (ξ : QuaternionCoordinates) : (y, ξ) ∈ U := by
    change ‖y‖ < 1
    linarith
  have hPair : ContDiff ℝ ∞ (fun ξ : QuaternionCoordinates => (y, ξ)) :=
    contDiff_const.prodMk contDiff_id
  have hComp : ContDiff ℝ ∞ (restoreSphereDirection y) := by
    rw [← contDiffOn_univ]
    exact hS.comp hPair.contDiffOn (fun ξ _ => hyU ξ)
  refine ⟨hComp, ?_⟩
  intro ξ hξ
  let L := ContinuousLinearMap.inr ℝ QuaternionCoordinates QuaternionCoordinates
  have hPair' : HasFDerivAt (fun ζ : QuaternionCoordinates => (y, ζ)) L ξ :=
    (hasFDerivAt_const (𝕜 := ℝ) y ξ).prodMk (hasFDerivAt_id (𝕜 := ℝ) ξ)
  have hDiff := ((hS.contDiffAt (hU.mem_nhds (hyU ξ))).differentiableAt (by simp)).hasFDerivAt
  have hDF : fderiv ℝ (restoreSphereDirection y) ξ = (fderiv ℝ F (y, ξ)).comp L :=
    (hDiff.comp ξ hPair').fderiv
  rw [hDF]
  have hp : (y, ξ) ∈ K := by
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hy,
      by simpa only [mem_closedBall, dist_zero_right] using hξ⟩
  calc
    _ ≤ ‖fderiv ℝ F (y, ξ)‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ F (y, ξ)‖ := by rw [show ‖L‖ = 1 from ContinuousLinearMap.norm_inr _ _ _, mul_one]
    _ ≤ _ := (hB _ hp).trans (le_max_right _ _)

end Thesis
