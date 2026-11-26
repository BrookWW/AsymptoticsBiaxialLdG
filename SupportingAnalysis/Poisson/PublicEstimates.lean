module

public import SupportingAnalysis.Poisson.Gradient
public import SupportingAnalysis.Poisson.Equation
public import HolderToCK.Analysis.Poisson.DistributionIdentity

/-! Coordinate adapters for the canonical Newtonian kernels from HolderToCK. -/

@[expose] public section

open MeasureTheory Metric Filter Set InnerProductSpace
open scoped Convolution ContDiff ENNReal InnerProductSpace Topology

set_option autoImplicit false

namespace SupportingAnalysis

variable {d : ℕ}

private theorem two_le_infty : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

/-- The Euclidean vector representing HolderToCK's fundamental gradient. -/
noncomputable def holderNewtonianGradient (x : E d) : E d :=
  ((HolderToCK.euclideanSphereArea d)⁻¹ * ‖x‖ ^ (-(d : ℝ))) • x

theorem holderNewtonianGradient_component (x : E d) (i : Fin d) :
    holderNewtonianGradient x i = (HolderToCK.euclideanSphereArea d)⁻¹ *
      ‖x‖ ^ (-(d : ℝ)) * x i := by
  simp [holderNewtonianGradient, mul_assoc]

theorem holderNewtonianGradient_locallyIntegrable (hd : 0 < d) :
    LocallyIntegrable (holderNewtonianGradient (d := d)) volume := by
  let L : (E d →L[ℝ] ℝ) →L[ℝ] E d :=
    (InnerProductSpace.toDual ℝ (E d)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hEq (x : E d) : L (HolderToCK.fundamentalGradientExpression x) =
      holderNewtonianGradient x := by
    apply ext_inner_right ℝ
    intro y
    change ⟪(InnerProductSpace.toDual ℝ (E d)).symm
      (HolderToCK.fundamentalGradientExpression x), y⟫_ℝ = _
    rw [InnerProductSpace.toDual_symm_apply]
    simp only [HolderToCK.fundamentalGradientExpression, holderNewtonianGradient,
      smul_apply, innerSL_apply_apply, inner_smul_left, conj_trivial, smul_eq_mul]
  intro x
  have hLoc := L.integrableAtFilter_comp (HolderToCK.fundamentalGradientExpression_locallyIntegrable hd x)
  have hFun : ((L : (E d →L[ℝ] ℝ) → E d) ∘ HolderToCK.fundamentalGradientExpression) =
      holderNewtonianGradient := funext hEq
  rwa [hFun] at hLoc

theorem holderPower_classicalGradient (hd : 3 ≤ d) {x : E d} (hx : x ≠ 0) (i : Fin d) :
    fderiv ℝ HolderToCK.fundamentalPowerExpression x (axis i) =
      holderNewtonianGradient x i := by
  simpa only [holderNewtonianGradient_component, axis] using HolderToCK.fundamentalPower_column hd x hx i

theorem holderLog_classicalGradient {x : E 2} (hx : x ≠ 0) (i : Fin 2) :
    fderiv ℝ HolderToCK.fundamentalLogExpression x (axis i) = holderNewtonianGradient x i := by
  simpa only [holderNewtonianGradient_component, axis, Nat.cast_ofNat] using HolderToCK.fundamentalLog_column x hx i

theorem holderPower_testDerivative (hd : 3 ≤ d) (i : Fin d)
    (φ : E d → ℝ) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ y, HolderToCK.fundamentalPowerExpression y * fderiv ℝ φ y (axis i)) =
      -∫ y, holderNewtonianGradient y i * φ y := by
  simpa only [holderNewtonianGradient_component, axis] using
    HolderToCK.fundamentalPower_testDerivative hd hφ hφc i

theorem holderLog_testDerivative (i : Fin 2)
    (φ : E 2 → ℝ) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ y, HolderToCK.fundamentalLogExpression y * fderiv ℝ φ y (axis i)) =
      -∫ y, holderNewtonianGradient y i * φ y := by
  simpa only [holderNewtonianGradient_component, axis, Nat.cast_ofNat] using
    HolderToCK.fundamentalLog_testDerivative hφ hφc i

theorem holderPower_harmonicOffZero : HarmonicOnNhd
    (HolderToCK.fundamentalPowerExpression (n := d)) ({0}ᶜ : Set (E d)) := by
  intro x hx
  refine ⟨(HolderToCK.fundamentalPower_contDiffAt x hx).of_le two_le_infty, ?_⟩
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx] with y hy
  let p : ℝ := (2 - (d : ℝ)) / 2
  let c : ℝ := ((2 - (d : ℝ)) * HolderToCK.euclideanSphereArea d)⁻¹
  have hL := HolderToCK.normSq_rpow_laplacian (0 : E d) p y (show y ≠ 0 from hy)
  have hC := HolderToCK.normSq_rpow_contDiffAt (0 : E d) p y (show y ≠ 0 from hy)
  simp only [sub_zero] at hL hC
  have hFormula : HolderToCK.fundamentalPowerExpression = c •
      (fun z : E d => (‖z‖ ^ 2) ^ p) := rfl
  change Laplacian.laplacian (HolderToCK.fundamentalPowerExpression (n := d)) y = (0 : ℝ)
  rw [hFormula, InnerProductSpace.laplacian_smul c (hC.of_le two_le_infty), hL]
  have hExp : (d : ℝ) + 2 * p - 2 = 0 := by dsimp [p]; ring
  simp only [hExp, mul_zero, zero_mul, smul_zero]

theorem holderLog_harmonicOffZero : HarmonicOnNhd HolderToCK.fundamentalLogExpression
    ({0}ᶜ : Set (E 2)) := by
  intro x hx
  refine ⟨(HolderToCK.fundamentalLog_contDiffAt x hx).of_le two_le_infty, ?_⟩
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx] with y hy
  let c : ℝ := (4 * Real.pi)⁻¹
  have hL := HolderToCK.normSq_log_laplacian (0 : E 2) y (show y ≠ 0 from hy)
  have hC := HolderToCK.normSq_log_contDiffAt (0 : E 2) y (show y ≠ 0 from hy)
  simp only [sub_zero] at hL hC
  have hFormula : HolderToCK.fundamentalLogExpression =
      c • (fun z : E 2 => Real.log (‖z‖ ^ 2)) := funext HolderToCK.fundamentalLog_eq_normSq
  change Laplacian.laplacian HolderToCK.fundamentalLogExpression y = (0 : ℝ)
  rw [hFormula, InnerProductSpace.laplacian_smul c (hC.of_le two_le_infty), hL]
  norm_num

theorem holderPower_dilate {r : ℝ} (hr : 0 < r) (x : E d) :
    HolderToCK.fundamentalPowerExpression (r • x) =
      r ^ (2 - (d : ℤ)) * HolderToCK.fundamentalPowerExpression x := by
  have hExp : 2 * ((2 - (d : ℝ)) / 2) = (↑((2 : ℤ) - (d : ℤ)) : ℝ) := by
    push_cast
    ring
  have hPow (y : E d) : (‖y‖ ^ 2) ^ ((2 - (d : ℝ)) / 2) = ‖y‖ ^ (2 - (d : ℤ)) := by
    rw [HolderToCK.normSq_real_rpow]
    exact (congrArg (fun q : ℝ => ‖y‖ ^ q) hExp).trans
      (Real.rpow_intCast ‖y‖ (2 - (d : ℤ)))
  unfold HolderToCK.fundamentalPowerExpression
  rw [hPow (r • x), hPow x, norm_smul, Real.norm_of_nonneg hr.le, mul_zpow]
  ring

theorem holderLog_dilate {r : ℝ} (hr : 0 < r) {x : E 2} (hx : x ≠ 0) :
    HolderToCK.fundamentalLogExpression (r • x) =
      r ^ (2 - (2 : ℤ)) * HolderToCK.fundamentalLogExpression x +
        (2 * Real.pi)⁻¹ * Real.log r := by
  simp only [HolderToCK.fundamentalLogExpression, sub_self, zpow_zero, one_mul, norm_smul,
    Real.norm_of_nonneg hr.le, Real.log_mul hr.ne' (norm_ne_zero_iff.mpr hx)]
  ring

theorem holderPower_distributionPairing (hd : 3 ≤ d)
    (φ : E d → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, HolderToCK.fundamentalPowerExpression x * laplacian φ x) = φ 0 := by
  have hEq (x : E d) : Laplacian.laplacian φ x = laplacian φ x :=
    HolderToCK.scalarLaplacian_eq_coordinateSum φ x ((hφ.of_le two_le_infty).contDiffAt)
  simpa only [hEq] using HolderToCK.fundamentalPower_distributionPairing hd
    (hφ.of_le two_le_infty) hφc

theorem holderLog_distributionPairing (φ : E 2 → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    (∫ x, HolderToCK.fundamentalLogExpression x * laplacian φ x) = φ 0 := by
  have hEq (x : E 2) : Laplacian.laplacian φ x = laplacian φ x :=
    HolderToCK.scalarLaplacian_eq_coordinateSum φ x ((hφ.of_le two_le_infty).contDiffAt)
  simpa only [hEq] using HolderToCK.fundamentalLog_distributionPairing (hφ.of_le two_le_infty) hφc

end SupportingAnalysis
