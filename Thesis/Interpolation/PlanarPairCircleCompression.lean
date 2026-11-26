module

public import Thesis.Interpolation.PlanarPairRecovery
public import Thesis.MeasureGeometry.MeridianCircleOrientation

/-! Peripheral traversals supported on the two outward semicircles. -/

public section

noncomputable section

open Metric Set StratificationTheory
open scoped Topology

namespace Thesis

abbrev planarPairCircleComplex (z : NativeCircle) : ℂ :=
  MeasureGeometry.complexPlaneCoordinates.symm z.val

private theorem norm_planarPairCircleComplex (z : NativeCircle) : ‖planarPairCircleComplex z‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map,mem_sphere_zero_iff_norm.mp z.property]

def planarPairHemisphereSign (left : Bool) : ℝ := if left then -1 else 1

def planarPairFoldedFactor (left : Bool) (z : ℂ) : ℂ :=
  ⟨planarPairHemisphereSign left*|z.re|,z.im⟩

private theorem continuous_planarPairFoldedFactor (left : Bool) : Continuous (planarPairFoldedFactor left) := by
  exact Complex.equivRealProdCLM.symm.continuous.comp
    ((continuous_const.mul Complex.continuous_re.abs).prodMk Complex.continuous_im)

private theorem norm_planarPairFoldedFactor (left : Bool) (z : ℂ) :
    ‖planarPairFoldedFactor left z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
  change (planarPairHemisphereSign left*|z.re|)*(planarPairHemisphereSign left*|z.re|)+z.im*z.im = z.re*z.re+z.im*z.im
  cases left <;> simp [planarPairHemisphereSign,← sq,sq_abs]

private theorem planarPairFoldedFactor_eq_self (left : Bool) {z : ℂ}
    (hz : if left then z.re ≤ 0 else 0 ≤ z.re) :
    planarPairFoldedFactor left z = z := by
  apply Complex.ext
  · change planarPairHemisphereSign left*|z.re| = z.re
    cases left
    · exact (one_mul _).trans (abs_of_nonneg hz)
    · simp only [planarPairHemisphereSign,ite_true,abs_of_nonpos hz,neg_one_mul,neg_neg]
  · rfl

private theorem planarPairFoldedFactor_eq_neg_conj (left : Bool) {z : ℂ}
    (hz : if left then 0 ≤ z.re else z.re ≤ 0) :
    planarPairFoldedFactor left z = -star z := by
  apply Complex.ext
  · change planarPairHemisphereSign left*|z.re| = (-star z).re
    cases left
    · simp only [planarPairHemisphereSign,Bool.false_eq_true,ite_false,one_mul,abs_of_nonpos hz,
        Complex.neg_re,Complex.star_def,Complex.conj_re]
    · simp only [planarPairHemisphereSign,ite_true,neg_one_mul,abs_of_nonneg hz,
        Complex.neg_re,Complex.star_def,Complex.conj_re]
  · simp [planarPairFoldedFactor]

/-- The native circle map which traverses the outward half-circle twice and
takes the common basepoint on the inward half-circle. -/
def planarPairHalfCircle (left : Bool) : C(NativeCircle,NativeCircle) := by
  let G (z : NativeCircle) := planarPairCircleComplex z * planarPairFoldedFactor left (planarPairCircleComplex z)
  have hG : Continuous G := by
    have hz := MeasureGeometry.complexPlaneCoordinates.symm.continuous.comp
      (continuous_subtype_val : Continuous (fun z : NativeCircle => z.val))
    exact hz.mul ((continuous_planarPairFoldedFactor left).comp hz)
  have hNorm (z : NativeCircle) : ‖G z‖ = 1 := by
    dsimp only [G]
    rw [norm_mul,norm_planarPairFoldedFactor,norm_planarPairCircleComplex,one_mul]
  let H (z : NativeCircle) := MeasureGeometry.complexPlaneCoordinates (G z)
  have hH (z : NativeCircle) : H z ∈ sphere (0 : Plane) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact (MeasureGeometry.complexPlaneCoordinates.norm_map _).trans (hNorm z)
  exact ⟨fun z => ⟨H z,hH z⟩,
    (MeasureGeometry.complexPlaneCoordinates.continuous.comp hG).subtype_mk _⟩

theorem planarPairHalfCircle_complex (left : Bool) (z : NativeCircle) :
    planarPairCircleComplex (planarPairHalfCircle left z) = planarPairCircleComplex z * planarPairFoldedFactor left (planarPairCircleComplex z) :=
  MeasureGeometry.complexPlaneCoordinates.symm_apply_apply _

theorem nativeCircleLoopBase_complex : planarPairCircleComplex nativeCircleLoopBase = -1 := by
  change MeasureGeometry.complexPlaneCoordinates.symm (circleNativeParam (-Real.pi)).val = -1
  rw [MeasureGeometry.circleNativeParam_val_eq_complexExp,LinearIsometryEquiv.symm_apply_apply,
    Complex.exp_mul_I]
  apply Complex.ext <;> simp

theorem planarPairHalfCircle_eq_base (left : Bool) (z : NativeCircle)
    (hz : if left then 0 ≤ (planarPairCircleComplex z).re else (planarPairCircleComplex z).re ≤ 0) :
    planarPairHalfCircle left z = nativeCircleLoopBase := by
  apply Subtype.ext
  apply MeasureGeometry.complexPlaneCoordinates.symm.injective
  change planarPairCircleComplex (planarPairHalfCircle left z) = planarPairCircleComplex nativeCircleLoopBase
  rw [planarPairHalfCircle_complex,planarPairFoldedFactor_eq_neg_conj left hz,
    nativeCircleLoopBase_complex,mul_neg,Complex.star_def,Complex.mul_conj,
    Complex.normSq_eq_norm_sq,norm_planarPairCircleComplex,one_pow]
  norm_num

theorem planarPairHalfCircle_eq_square (left : Bool) (z : NativeCircle)
    (hz : if left then (planarPairCircleComplex z).re ≤ 0 else 0 ≤ (planarPairCircleComplex z).re) :
    planarPairCircleComplex (planarPairHalfCircle left z) = (planarPairCircleComplex z)^2 := by
  rw [planarPairHalfCircle_complex,planarPairFoldedFactor_eq_self left hz,pow_two]

private theorem norm_planarPairHemisphereSign (left : Bool) : ‖planarPairHemisphereSign left‖ = 1 := by
  cases left <;> simp [planarPairHemisphereSign]

private theorem planarPairHemisphereSign_mul_folded_re (left : Bool) (z : ℂ) :
    (planarPairHemisphereSign left • planarPairFoldedFactor left z).re = |z.re| := by
  rw [Complex.smul_re]
  change planarPairHemisphereSign left*(planarPairHemisphereSign left*|z.re|) = _
  cases left <;> simp [planarPairHemisphereSign]

private theorem planarPairHemisphereSign_mul_self (left : Bool) (z : ℂ) :
    planarPairHemisphereSign left • (planarPairHemisphereSign left • z) = z := by
  cases left <;> simp [planarPairHemisphereSign]

/-- An explicit homotopy from the identity to each compressed peripheral
angle, through normalized combinations in a closed complex half-plane. -/
theorem exists_planarPairHalfCircle_homotopy (left : Bool) :
    (ContinuousMap.id NativeCircle).Homotopic (planarPairHalfCircle left) := by
  let V (z : NativeCircle) := planarPairHemisphereSign left • planarPairFoldedFactor left (planarPairCircleComplex z)
  let T (p : unitInterval × NativeCircle) : ℂ :=
    (1-p.1.val) • (1 : ℂ)+ p.1.val • V p.2
  have hV (z : NativeCircle) : ‖V z‖ = 1 := by
    dsimp only [V]
    rw [norm_smul,norm_planarPairHemisphereSign,norm_planarPairFoldedFactor,norm_planarPairCircleComplex,one_mul]
  have hT (p : unitInterval × NativeCircle) : T p ≠ 0 := by
    by_cases h : p.1.val = 1
    · intro h0
      have hEq : T p = V p.2 := by simp [T,h]
      have hN := hV p.2
      rw [← hEq,h0,norm_zero] at hN
      exact zero_ne_one hN
    · have ht : 0 < 1-p.1.val := sub_pos.mpr (lt_of_le_of_ne p.1.property.2 h)
      have hR : 0 < (T p).re := by
        dsimp only [T,V]
        rw [Complex.add_re,Complex.smul_re,Complex.one_re,smul_eq_mul,mul_one,
          Complex.smul_re,smul_eq_mul,planarPairHemisphereSign_mul_folded_re]
        exact ht.trans_le (le_add_of_nonneg_right (mul_nonneg p.1.property.1 (abs_nonneg _)))
      exact fun h0 => hR.ne' (by rw [h0,Complex.zero_re])
  let U (p : unitInterval × NativeCircle) := ‖T p‖⁻¹ • T p
  have hU (p : unitInterval × NativeCircle) : ‖U p‖ = 1 := by
    dsimp only [U]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hT p))]
  let θ : ℝ := if left then Real.pi else 0
  let Q (p : unitInterval × NativeCircle) :=
    planarPairCircleComplex p.2 * (Complex.exp (((θ*p.1.val : ℝ) : ℂ)*Complex.I) * U p)
  have hQ (p : unitInterval × NativeCircle) : ‖Q p‖ = 1 := by
    dsimp only [Q]
    rw [norm_mul,norm_mul,MeasureGeometry.norm_complex_circle_exp,hU,norm_planarPairCircleComplex,mul_one,mul_one]
  have hTc : Continuous T := by
    have hP := continuous_subtype_val.comp (continuous_fst : Continuous (Prod.fst : unitInterval × NativeCircle → unitInterval))
    have hZ := MeasureGeometry.complexPlaneCoordinates.symm.continuous.comp
      (continuous_subtype_val.comp (continuous_snd : Continuous (Prod.snd : unitInterval × NativeCircle → NativeCircle)))
    exact ((continuous_const.sub hP).smul continuous_const).add
      (hP.smul (((continuous_planarPairFoldedFactor left).comp hZ).const_smul (planarPairHemisphereSign left)))
  have hUc : Continuous U := (hTc.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (hT p))).smul hTc
  have hQc : Continuous Q := by
    dsimp only [Q]
    have hZ := MeasureGeometry.complexPlaneCoordinates.symm.continuous.comp
      (continuous_subtype_val.comp (continuous_snd : Continuous (Prod.snd : unitInterval × NativeCircle → NativeCircle)))
    have hParam : Continuous (fun p : unitInterval × NativeCircle => ((θ*p.1.val : ℝ) : ℂ)*Complex.I) := by fun_prop
    exact hZ.mul ((Complex.continuous_exp.comp hParam).mul hUc)
  let H (p : unitInterval × NativeCircle) := MeasureGeometry.complexPlaneCoordinates (Q p)
  have hm (p : unitInterval × NativeCircle) : H p ∈ sphere (0 : Plane) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact (MeasureGeometry.complexPlaneCoordinates.norm_map _).trans (hQ p)
  refine ⟨⟨⟨fun p => ⟨H p,hm p⟩,
    (MeasureGeometry.complexPlaneCoordinates.continuous.comp hQc).subtype_mk _⟩,?_,?_⟩⟩
  · intro z
    apply Subtype.ext
    change H (0,z) = z.val
    have hT₀ : T (0,z) = 1 := by simp [T]
    have hQ₀ : Q (0,z) = planarPairCircleComplex z := by
      change planarPairCircleComplex z * (Complex.exp (((θ*0 : ℝ) : ℂ)*Complex.I) * (‖T (0,z)‖⁻¹ • T (0,z))) = _
      rw [hT₀]
      simp
    dsimp only [H]
    rw [hQ₀,LinearIsometryEquiv.apply_symm_apply]
  · intro z
    apply Subtype.ext
    apply MeasureGeometry.complexPlaneCoordinates.symm.injective
    change MeasureGeometry.complexPlaneCoordinates.symm (H (1,z)) = planarPairCircleComplex (planarPairHalfCircle left z)
    rw [planarPairHalfCircle_complex]
    dsimp only [H]
    rw [LinearIsometryEquiv.symm_apply_apply]
    have hT₁ : T (1,z) = V z := by simp [T]
    have hExp : Complex.exp ((θ : ℂ)*Complex.I) = (planarPairHemisphereSign left : ℂ) := by
      cases left
      · simp [θ,planarPairHemisphereSign]
      · apply Complex.ext <;> simp [θ,planarPairHemisphereSign,Complex.exp_mul_I]
    change planarPairCircleComplex z*(Complex.exp (((θ*1 : ℝ) : ℂ)*Complex.I)*(‖T (1,z)‖⁻¹ • T (1,z))) = _
    rw [hT₁,hV,inv_one,one_smul,mul_one,hExp,← Complex.real_smul]
    rw [show V z = planarPairHemisphereSign left • planarPairFoldedFactor left (planarPairCircleComplex z) from rfl,
      planarPairHemisphereSign_mul_self]

end Thesis
