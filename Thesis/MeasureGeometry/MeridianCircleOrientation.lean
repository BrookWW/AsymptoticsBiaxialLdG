module

public import Thesis.MeasureGeometry.JunctionWord
import Mathlib.Analysis.Complex.Trigonometric

/-! Rotation and reversal of the actual orthogonal meridian parameter. -/

@[expose] public section

noncomputable section

open Metric Set StratificationTheory
open scoped RealInnerProductSpace

namespace Thesis.MeasureGeometry

/-- The exact complex-coordinate isometry underlying the native circle. -/
abbrev complexPlaneCoordinates : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

theorem circleNativeParam_val_eq_complexExp (t : ℝ) :
    (circleNativeParam t).val = complexPlaneCoordinates (Complex.exp ((t : ℂ) * Complex.I)) := by
  rw [circleNativeParam_coe, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ext i
  fin_cases i <;> simp [complexPlaneCoordinates, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem norm_complex_circle_exp (t : ℝ) : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := by
  have h := congrArg norm (circleNativeParam_val_eq_complexExp t)
  rw [LinearIsometryEquiv.norm_map, mem_sphere_zero_iff_norm.mp (circleNativeParam t).property] at h
  exact h.symm

/-- Multiplication by a unit complex number, with optional reversal, on
the same native circle. -/
def nativeCircle_unitComplex (w : ℂ) (hw : ‖w‖ = 1) (rev : Bool) : C(NativeCircle, NativeCircle) := by
  let v (z : NativeCircle) : ℂ :=
    if rev then star (complexPlaneCoordinates.symm z.val) else complexPlaneCoordinates.symm z.val
  have hv (z : NativeCircle) : ‖v z‖ = 1 := by
    cases rev
    · change ‖complexPlaneCoordinates.symm z.val‖ = 1
      rw [LinearIsometryEquiv.norm_map, mem_sphere_zero_iff_norm.mp z.property]
    · change ‖star (complexPlaneCoordinates.symm z.val)‖ = 1
      rw [norm_star, LinearIsometryEquiv.norm_map, mem_sphere_zero_iff_norm.mp z.property]
  have hc : Continuous v := by
    cases rev
    · exact complexPlaneCoordinates.symm.continuous.comp continuous_subtype_val
    · exact continuous_star.comp (complexPlaneCoordinates.symm.continuous.comp continuous_subtype_val)
  have hm (z : NativeCircle) : complexPlaneCoordinates (w * v z) ∈ sphere (0 : Plane) 1 := by
    rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, norm_mul, hw, hv, one_mul]
  exact ⟨fun z => ⟨complexPlaneCoordinates (w * v z), hm z⟩,
    (complexPlaneCoordinates.continuous.comp (continuous_const.mul hc)).subtype_mk hm⟩

theorem nativeCircle_unitComplex_val (w : ℂ) (hw : ‖w‖ = 1) (rev : Bool) (z : NativeCircle) :
    (nativeCircle_unitComplex w hw rev z).val =
      complexPlaneCoordinates (w *
        (if rev then star (complexPlaneCoordinates.symm z.val) else complexPlaneCoordinates.symm z.val)) := rfl

private theorem exists_complex_angle {w : ℂ} (hw : ‖w‖ = 1) : ∃ t : ℝ, w = Complex.exp ((t : ℂ) * Complex.I) := by
  let z : NativeCircle := ⟨complexPlaneCoordinates w, mem_sphere_zero_iff_norm.mpr
    ((complexPlaneCoordinates.norm_map w).trans hw)⟩
  obtain ⟨s, hs⟩ := nativeCircleLoopParam_surjective z
  refine ⟨2 * Real.pi * s.val - Real.pi, ?_⟩
  apply complexPlaneCoordinates.injective
  have h := congrArg Subtype.val hs
  rw [nativeCircleLoopParam_apply, circleNativeParam_val_eq_complexExp] at h
  exact h.symm

theorem nativeCircle_unitComplex_rotation_homotopic_id (w : ℂ) (hw : ‖w‖ = 1) :
    (nativeCircle_unitComplex w hw false).Homotopic (ContinuousMap.id NativeCircle) := by
  obtain ⟨α, hα⟩ := exists_complex_angle hw
  let G (p : unitInterval × NativeCircle) : Plane :=
    complexPlaneCoordinates (Complex.exp ((((1 - p.1.val) * α : ℝ) : ℂ) * Complex.I) *
      complexPlaneCoordinates.symm p.2.val)
  have hG : Continuous G := by dsimp only [G]; fun_prop
  have hGm (p : unitInterval × NativeCircle) : G p ∈ sphere (0 : Plane) 1 := by
    dsimp only [G]
    rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, norm_mul,
      norm_complex_circle_exp, LinearIsometryEquiv.norm_map, mem_sphere_zero_iff_norm.mp p.2.property, mul_one]
  refine ⟨⟨⟨fun p => ⟨G p, hGm p⟩, hG.subtype_mk _⟩, ?_, ?_⟩⟩
  · intro z
    apply Subtype.ext
    change G (0,z) = _
    rw [nativeCircle_unitComplex_val]
    simp [G, hα]
  · intro z
    apply Subtype.ext
    change complexPlaneCoordinates (Complex.exp ((((1 - (1 : ℝ)) * α : ℝ) : ℂ) * Complex.I) *
      complexPlaneCoordinates.symm z.val) = z.val
    simp only [sub_self, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul,
      LinearIsometryEquiv.apply_symm_apply]

private theorem nativeCircle_unitComplex_reverse_apply (t : unitInterval) :
    nativeCircle_unitComplex (1 : ℂ) (by simp) true (nativeCircleLoopParam t) =
      nativeCircleLoopParam (unitInterval.symm t) := by
  apply Subtype.ext
  rw [nativeCircle_unitComplex_val, nativeCircleLoopParam_apply, nativeCircleLoopParam_apply,
    circleNativeParam_val_eq_complexExp, circleNativeParam_val_eq_complexExp]
  simp only [if_true, one_mul, LinearIsometryEquiv.symm_apply_apply]
  apply congrArg complexPlaneCoordinates
  have hConj : star (Complex.exp (((2 * Real.pi * t.val - Real.pi : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((-(2 * Real.pi * t.val - Real.pi) : ℝ) : ℂ) * Complex.I) := by
    change (starRingEnd ℂ) (Complex.exp _) = _
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, mul_neg, neg_mul]
  have hTime : -(2 * Real.pi * t.val - Real.pi) =
      2 * Real.pi * (unitInterval.symm t).val - Real.pi := by
    change -(2 * Real.pi * t.val - Real.pi) = 2 * Real.pi * (1 - t.val) - Real.pi
    ring
  rw [hConj, hTime]

/-- The measured splitting cost is invariant under any rotation or
reversal of the actual Euclidean meridian parameter. -/
theorem nativeVacuumCircleCost_comp_unitComplex (a : BulkCoefficients)
    (b : C(NativeCircle, vacuum a)) (w : ℂ) (hw : ‖w‖ = 1) (rev : Bool) :
    nativeVacuumCircleCost a (b.comp (nativeCircle_unitComplex w hw rev)) =
      nativeVacuumCircleCost a b := by
  have hRot : nativeVacuumCircleCost a (b.comp (nativeCircle_unitComplex w hw false)) =
      nativeVacuumCircleCost a b := by
    obtain ⟨H⟩ := nativeCircle_unitComplex_rotation_homotopic_id w hw
    have h : (b.comp (nativeCircle_unitComplex w hw false)).Homotopic b := by
      refine ⟨⟨b.comp H.toContinuousMap, ?_, ?_⟩⟩
      · intro z
        exact congrArg b (H.map_zero_left z)
      · intro z
        exact congrArg b (H.map_one_left z)
    exact nativeVacuumCircleCost_homotopic a h
  cases rev
  · exact hRot
  · let f := b.comp (nativeCircle_unitComplex w hw false)
    obtain ⟨g, _, hg, hCost⟩ := exists_oriented_vacuumCircle a f true
    have hEq : b.comp (nativeCircle_unitComplex w hw true) = g := by
      apply ContinuousMap.ext
      intro z
      obtain ⟨t, rfl⟩ := nativeCircleLoopParam_surjective z
      have h := hg t
      change g (nativeCircleLoopParam t) = f (nativeCircleLoopParam (unitInterval.symm t)) at h
      rw [← nativeCircle_unitComplex_reverse_apply] at h
      have hMap : nativeCircle_unitComplex w hw false
          (nativeCircle_unitComplex (1 : ℂ) (by simp) true (nativeCircleLoopParam t)) =
          nativeCircle_unitComplex w hw true (nativeCircleLoopParam t) := by
        apply Subtype.ext
        simp only [nativeCircle_unitComplex_val, if_true, Bool.false_eq_true, if_false, one_mul,
          LinearIsometryEquiv.symm_apply_apply]
      change b (nativeCircle_unitComplex w hw true (nativeCircleLoopParam t)) = g (nativeCircleLoopParam t)
      rw [h, ← hMap]
      rfl
    rw [hEq, hCost]
    exact hRot

end Thesis.MeasureGeometry
