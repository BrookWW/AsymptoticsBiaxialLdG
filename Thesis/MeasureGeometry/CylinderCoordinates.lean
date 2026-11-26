module

public import Thesis.MeasureGeometry.CylinderMass
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Volume-preserving axial coordinates aligned with the actual tangent line. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal RealInnerProductSpace

namespace Thesis.MeasureGeometry

/-- An orthonormal frame whose third vector is the prescribed axial direction. -/
theorem exists_axis_orthonormalBasis {e : Point} (he : ‖e‖ = 1) :
    ∃ B : OrthonormalBasis (Fin 3) ℝ Point, B 2 = e := by
  classical
  let S : Set (Fin 3) := {2}
  let v : Fin 3 → Point := fun _ => e
  have hON : Orthonormal ℝ (S.restrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hEq : i = j := Subtype.ext
      ((mem_singleton_iff.mp i.property).trans (mem_singleton_iff.mp j.property).symm)
    simp only [hEq, if_true, S, v, Set.restrict, real_inner_self_eq_norm_sq, he, one_pow]
  have hCard : Module.finrank ℝ Point = Fintype.card (Fin 3) := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = _
    exact finrank_euclideanSpace
  obtain ⟨B, hB⟩ := hON.exists_orthonormalBasis_extension_of_card_eq hCard
  exact ⟨B, hB 2 (mem_singleton 2)⟩

def planeLinePack (p : WithLp 2 (Plane × ℝ)) : Point :=
  WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then p.fst 0 else if i = 1 then p.fst 1 else p.snd)

def planeLineUnpack (y : Point) : WithLp 2 (Plane × ℝ) :=
  WithLp.toLp 2 (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then y 0 else y 1), y 2)

@[simp] private theorem planeLinePack_zero (p : WithLp 2 (Plane × ℝ)) :
    planeLinePack p 0 = p.fst 0 := by simp [planeLinePack]
@[simp] private theorem planeLinePack_one (p : WithLp 2 (Plane × ℝ)) :
    planeLinePack p 1 = p.fst 1 := by simp [planeLinePack]
@[simp] private theorem planeLinePack_two (p : WithLp 2 (Plane × ℝ)) :
    planeLinePack p 2 = p.snd := by simp [planeLinePack]

/-- Packing two transverse coordinates and one axial coordinate preserves
the Euclidean product norm. -/
def planeLineEuclideanIsometry : WithLp 2 (Plane × ℝ) ≃ₗᵢ[ℝ] Point where
  toFun := planeLinePack
  invFun := planeLineUnpack
  left_inv p := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [planeLineUnpack]
    · exact planeLinePack_two p
  right_inv y := by
    ext i
    fin_cases i <;> simp [planeLineUnpack]
  map_add' p q := by
    ext i
    fin_cases i <;> simp
  map_smul' c p := by
    ext i
    fin_cases i <;> simp
  norm_map' p := by
    letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    change ‖planeLinePack p‖ = ‖p‖
    rw [WithLp.prod_norm_eq_of_nat (p := (2 : ℝ≥0∞)) 2 rfl]
    change ‖planeLinePack p‖ = (‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2) ^ (1 / (2 : ℝ))
    rw [← Real.sqrt_eq_rpow]
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity), EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    simp

/-- The unshifted chart in an actual orthonormal frame. -/
def axisChart (B : OrthonormalBasis (Fin 3) ℝ Point) (yz : Plane × ℝ) : Point :=
  B.repr.symm (planeLineEuclideanIsometry (WithLp.toLp 2 yz))

theorem continuous_axisChart (B : OrthonormalBasis (Fin 3) ℝ Point) : Continuous (axisChart B) :=
  B.repr.symm.continuous.comp (planeLineEuclideanIsometry.continuous.comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ Plane ℝ).symm.continuous)

theorem measurePreserving_axisChart (B : OrthonormalBasis (Fin 3) ℝ Point) :
    MeasurePreserving (axisChart B) ((volume : Measure Plane).prod (volume : Measure ℝ)) volume := by
  change MeasurePreserving (axisChart B) (volume : Measure (Plane × ℝ)) volume
  simpa only [axisChart, Function.comp_def] using!
    (B.repr.symm.measurePreserving.comp (planeLineEuclideanIsometry.measurePreserving.comp
      (WithLp.volume_preserving_toLp Plane ℝ)))

theorem cylinderHeight_axisChart (B : OrthonormalBasis (Fin 3) ℝ Point) (y : Plane) (z : ℝ) :
    cylinderHeight (B 2) (axisChart B (y, z)) = z := by
  rw [cylinderHeight, ← B.repr_apply_apply, axisChart, LinearIsometryEquiv.apply_symm_apply]
  exact planeLinePack_two _

theorem axisChart_add_axis (B : OrthonormalBasis (Fin 3) ℝ Point) (y : Plane) (z : ℝ) :
    axisChart B (y, z) = axisChart B (y, 0) + z • B 2 := by
  have hP : planeLineEuclideanIsometry (WithLp.toLp 2 (y, z)) =
      planeLineEuclideanIsometry (WithLp.toLp 2 (y, 0)) + z • EuclideanSpace.single 2 (1 : ℝ) := by
    change planeLinePack _ = planeLinePack _ + _
    ext i
    fin_cases i <;> simp
  rw [axisChart, hP, map_add, map_smul, B.repr_symm_single]
  rfl

theorem cylinderTransverseRadius_axisChart (B : OrthonormalBasis (Fin 3) ℝ Point) (y : Plane) (z : ℝ) :
    cylinderTransverseRadius (B 2) (axisChart B (y, z)) = ‖y‖ := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  rw [cylinderTransverseRadius, cylinderHeight_axisChart, axisChart_add_axis, add_sub_cancel_right, axisChart,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, WithLp.prod_norm_eq_of_nat (p := (2 : ℝ≥0∞)) 2 rfl]
  change (‖y‖ ^ 2 + ‖(0 : ℝ)‖ ^ 2) ^ (1 / (2 : ℝ)) = ‖y‖
  rw [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg y)]

/-- The literal product disk and height interval have the expected
oriented cylindrical image. -/
theorem preimage_openAxisCylinder_axisChart (B : OrthonormalBasis (Fin 3) ℝ Point) (r lo hi : ℝ) :
    axisChart B ⁻¹' openAxisCylinder (B 2) r lo hi = (ball (0 : Plane) r) ×ˢ Ioo lo hi := by
  ext p
  rcases p with ⟨y, z⟩
  simp only [mem_preimage, openAxisCylinder, mem_setOf_eq, cylinderHeight_axisChart,
    cylinderTransverseRadius_axisChart, mem_prod, mem_ball, dist_zero_right, mem_Ioo]

/-- The linear inclusion of a horizontal plane in the same axial chart. -/
def axisChartPlane (B : OrthonormalBasis (Fin 3) ℝ Point) : Plane →L[ℝ] Point :=
  (EuclideanSpace.proj 0).smulRight (B 0) + (EuclideanSpace.proj 1).smulRight (B 1)

theorem axisChartPlane_apply (B : OrthonormalBasis (Fin 3) ℝ Point) (y : Plane) :
    axisChartPlane B y = axisChart B (y, 0) := by
  apply B.repr.injective
  rw [axisChart, LinearIsometryEquiv.apply_symm_apply]
  change B.repr (y 0 • B 0 + y 1 • B 1) =
    planeLinePack (WithLp.toLp 2 (y, 0))
  rw [map_add, map_smul, map_smul, B.repr_self, B.repr_self]
  ext i
  fin_cases i <;> simp

theorem axisChart_eq_plane_add_axis (B : OrthonormalBasis (Fin 3) ℝ Point) (y : Plane) (z : ℝ) :
    axisChart B (y, z) = axisChartPlane B y + z • B 2 := by
  rw [axisChartPlane_apply]
  exact axisChart_add_axis B y z

theorem norm_axisChartPlane (B : OrthonormalBasis (Fin 3) ℝ Point) (y : Plane) :
    ‖axisChartPlane B y‖ = ‖y‖ := by
  have h := cylinderTransverseRadius_axisChart B y 0
  rw [cylinderTransverseRadius, cylinderHeight_axisChart, zero_smul, sub_zero, ← axisChartPlane_apply] at h
  exact h

theorem axisChartPlane_single (B : OrthonormalBasis (Fin 3) ℝ Point) (i : Fin 2) :
    axisChartPlane B (EuclideanSpace.single i 1) = B (Fin.castSucc i) := by
  change (EuclideanSpace.single i (1 : ℝ)) 0 • B 0 + (EuclideanSpace.single i (1 : ℝ)) 1 • B 1 = _
  fin_cases i <;> simp

end Thesis.MeasureGeometry
