module

public import Thesis.MeasureGeometry.CylinderCoordinates

/-! Normal and axial coordinates for the actual line through the meridian. -/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal RealInnerProductSpace

namespace Thesis.MeasureGeometry

/-- The transverse coordinates dual to the two columns of the actual
axis chart. -/
def axisChartTransverseCoordinates (B : OrthonormalBasis (Fin 3) ℝ Point) : Point →L[ℝ] Plane :=
  let P : Point →L[ℝ] Plane :=
    ((EuclideanSpace.proj (0 : Fin 3)).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) +
      ((EuclideanSpace.proj (1 : Fin 3)).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
  P.comp B.repr.toContinuousLinearMap

theorem axisChartTransverseCoordinates_apply (B : OrthonormalBasis (Fin 3) ℝ Point) (x : Point)
    (i : Fin 2) :
    axisChartTransverseCoordinates B x i = B.repr x (Fin.castSucc i) := by
  change ((B.repr x 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    (B.repr x 1 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) i = _
  fin_cases i <;> simp

theorem axisChartTransverseCoordinates_axisChart (B : OrthonormalBasis (Fin 3) ℝ Point)
    (y : Plane) (z : ℝ) :
    axisChartTransverseCoordinates B (axisChart B (y, z)) = y := by
  ext i
  rw [axisChartTransverseCoordinates_apply, axisChart, LinearIsometryEquiv.apply_symm_apply]
  change planeLinePack (WithLp.toLp 2 (y,z)) (Fin.castSucc i) = y i
  fin_cases i <;> simp [planeLinePack]

theorem axisChartTransverseCoordinates_axisChartPlane (B : OrthonormalBasis (Fin 3) ℝ Point)
    (y : Plane) : axisChartTransverseCoordinates B (axisChartPlane B y) = y := by
  rw [axisChartPlane_apply, axisChartTransverseCoordinates_axisChart]

theorem axisChart_axis_vector (B : OrthonormalBasis (Fin 3) ℝ Point) :
    axisChart B (0, 1) = B 2 := by
  rw [axisChart_eq_plane_add_axis, map_zero, zero_add, one_smul]

theorem axisChartTransverseCoordinates_axis_vector (B : OrthonormalBasis (Fin 3) ℝ Point) :
    axisChartTransverseCoordinates B (B 2) = 0 := by
  rw [← axisChart_axis_vector B, axisChartTransverseCoordinates_axisChart]

theorem axisChart_reassemble (B : OrthonormalBasis (Fin 3) ℝ Point) (x : Point) :
    axisChart B (axisChartTransverseCoordinates B x, cylinderHeight (B 2) x) = x := by
  apply B.repr.injective
  rw [axisChart, LinearIsometryEquiv.apply_symm_apply]
  ext i
  change planeLinePack (WithLp.toLp 2 (axisChartTransverseCoordinates B x, cylinderHeight (B 2) x)) i =
    B.repr x i
  fin_cases i
  · simpa [planeLinePack] using axisChartTransverseCoordinates_apply B x 0
  · simpa [planeLinePack] using axisChartTransverseCoordinates_apply B x 1
  · simp [planeLinePack, cylinderHeight, B.repr_apply_apply]

theorem axisChart_decompose (B : OrthonormalBasis (Fin 3) ℝ Point) (x : Point) :
    axisChartPlane B (axisChartTransverseCoordinates B x) + cylinderHeight (B 2) x • B 2 = x :=
  (axisChart_eq_plane_add_axis B _ _).symm.trans (axisChart_reassemble B x)

theorem axisChartTransverseCoordinates_eq_zero_iff (B : OrthonormalBasis (Fin 3) ℝ Point) (x : Point) :
    axisChartTransverseCoordinates B x = 0 ↔ x ∈ Submodule.span ℝ {B 2} := by
  constructor
  · intro h
    have h' := axisChart_decompose B x
    rw [h, map_zero, zero_add] at h'
    exact Submodule.mem_span_singleton.mpr ⟨cylinderHeight (B 2) x, h'⟩
  · intro hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, axisChartTransverseCoordinates_axis_vector, smul_zero]

theorem norm_axisChartTransverseCoordinates_eq (B : OrthonormalBasis (Fin 3) ℝ Point) (x : Point) :
    ‖axisChartTransverseCoordinates B x‖ = cylinderTransverseRadius (B 2) x := by
  calc
    _ = cylinderTransverseRadius (B 2)
        (axisChart B (axisChartTransverseCoordinates B x, cylinderHeight (B 2) x)) :=
      (cylinderTransverseRadius_axisChart B _ _).symm
    _ = _ := congrArg (cylinderTransverseRadius (B 2)) (axisChart_reassemble B x)

theorem norm_axisChart_sq (B : OrthonormalBasis (Fin 3) ℝ Point) (y : Plane) (z : ℝ) :
    ‖axisChart B (y,z)‖ ^ 2 = ‖y‖ ^ 2 + z ^ 2 := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  rw [axisChart, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map,
    WithLp.prod_norm_eq_of_nat (p := (2 : ℝ≥0∞)) 2 rfl]
  change (((‖y‖ ^ 2 + ‖z‖ ^ 2) ^ (1 / (2 : ℝ))) ^ 2) = ‖y‖ ^ 2 + z ^ 2
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity), Real.norm_eq_abs, sq_abs]

end Thesis.MeasureGeometry
