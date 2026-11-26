module

public import Thesis.Interpolation.PlanarBallSquare
public import Thesis.Interpolation.ShellCellFaceTraces
public import Thesis.Foundation.VacuumFreeHomotopy
public import Thesis.Foundation.QuaternionLoopSobolev

/-! The actual four-sided boundary in its radial circle coordinates. -/

public section

noncomputable section

open HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped Matrix.Norms.Frobenius

namespace Thesis

theorem planarSquare_one_eq_unitCellCube : planarSquare 1 = (unitCellCube 2).val := by
  ext x
  unfold planarSquare unitCellCube
  change ‖WithLp.ofLp x‖ < 1 ↔ x ∈ ⋂ i : Fin 2, (EuclideanSpace.proj i) ⁻¹' Ioo (-1 : ℝ) 1
  rw [mem_iInter]
  constructor
  · intro h i
    have hcoord : |x i| ≤ ‖WithLp.ofLp x‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.ofLp x))).1 le_rfl i
    exact abs_lt.1 (hcoord.trans_lt h)
  · intro h
    have hAbs (i : Fin 2) : |x i| < 1 := abs_lt.2 (h i)
    let m := max |x 0| |x 1|
    have hm : 0 ≤ m := (abs_nonneg _).trans (le_max_left _ _)
    have hNorm : ‖WithLp.ofLp x‖ ≤ m := by
      apply (pi_norm_le_iff_of_nonneg hm).2
      intro i
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
    exact hNorm.trans_lt (max_lt (hAbs 0) (hAbs 1))

abbrev UnitSquareBoundary := frontier ((unitCellCube 2).val)

theorem mem_unitSquareBoundary_iff (x : Plane) : x ∈ UnitSquareBoundary ↔ ‖WithLp.ofLp x‖ = 1 := by
  change x ∈ frontier (unitCellCube 2).val ↔ _
  rw [← planarSquare_one_eq_unitCellCube, frontier_planarSquare zero_lt_one]
  rfl

/-- The boundary homeomorphism is the literal restriction of the ambient
radial square-to-disk homeomorphism. -/
@[expose] def unitSquareCircleHomeomorph : UnitSquareBoundary ≃ₜ NativeCircle where
  toFun x := ⟨coordinateCubeToBall x.val, by
    rw [mem_sphere_zero_iff_norm, norm_coordinateCubeToBall]
    exact (mem_unitSquareBoundary_iff _).1 x.property⟩
  invFun x := ⟨ballToCoordinateCube x.val, by
    rw [mem_unitSquareBoundary_iff, coordinateNorm_ballToCoordinateCube]
    exact mem_sphere_zero_iff_norm.1 x.property⟩
  left_inv x := Subtype.ext (ballToCoordinateCube_coordinateCubeToBall x.val)
  right_inv x := Subtype.ext (coordinateCubeToBall_ballToCoordinateCube x.val)
  continuous_toFun := (continuous_coordinateCubeToBall.comp continuous_subtype_val).subtype_mk fun x => by
    change coordinateCubeToBall x.val ∈ sphere (0 : Plane) 1
    rw [mem_sphere_zero_iff_norm, norm_coordinateCubeToBall]
    exact (mem_unitSquareBoundary_iff _).1 x.property
  continuous_invFun := (continuous_ballToCoordinateCube.comp continuous_subtype_val).subtype_mk fun x => by
    change ballToCoordinateCube x.val ∈ UnitSquareBoundary
    rw [mem_unitSquareBoundary_iff, coordinateNorm_ballToCoordinateCube]
    exact mem_sphere_zero_iff_norm.1 x.property

theorem unitSquareSidePoint_mem_boundary (i : Fin 2) (upper : Bool) {x : Domain 1}
    (hx : x 0 ∈ Icc (-1 : ℝ) 1) : unitCellFaceSlice i x (if upper then 1 else -1) ∈ UnitSquareBoundary := by
  rw [mem_unitSquareBoundary_iff, unitCellFaceSlice_coordinates]
  have hNorm : |x 0| ≤ 1 := abs_le.2 hx
  cases upper <;> fin_cases i <;> dsimp only [Fin.isValue, ite_true, ite_false]
  all_goals
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg zero_le_one).2
      intro j
      fin_cases j <;> simp [hNorm]
    · first
      | have h := (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.ofLp (WithLp.toLp 2 ![(1 : ℝ), x 0])))).1 le_rfl (0 : Fin 2)
        simpa using h
      | have h := (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.ofLp (WithLp.toLp 2 ![(-1 : ℝ), x 0])))).1 le_rfl (0 : Fin 2)
        simpa using h
      | have h := (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.ofLp (WithLp.toLp 2 ![x 0, (1 : ℝ)])))).1 le_rfl (1 : Fin 2)
        simpa using h
      | have h := (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.ofLp (WithLp.toLp 2 ![x 0, (-1 : ℝ)])))).1 le_rfl (1 : Fin 2)
        simpa using h

@[expose] def unitSquareSideParameter (i : Fin 2) (upper : Bool) (t : ℝ) : UnitSquareBoundary :=
  let s := projIcc (-1 : ℝ) 1 (by norm_num) t
  ⟨unitCellFaceSlice i (EuclideanSpace.single 0 s.val) (if upper then 1 else -1),
    unitSquareSidePoint_mem_boundary i upper (by simpa only [PiLp.single_apply, ite_true] using s.property)⟩

theorem unitSquareSideParameter_eq (i : Fin 2) (upper : Bool) (x : Domain 1)
    (hx : x 0 ∈ Icc (-1 : ℝ) 1) :
    (unitSquareSideParameter i upper (x 0)).val = unitCellFaceSlice i x (if upper then 1 else -1) := by
  have hclamp : (projIcc (-1 : ℝ) 1 (by norm_num) (x 0)).val = x 0 :=
    congrArg Subtype.val (projIcc_of_mem (by norm_num) hx)
  have hVec : EuclideanSpace.single 0 (x 0) = x := by
    ext j
    fin_cases j
    simp
  change unitCellFaceSlice i (EuclideanSpace.single 0 (projIcc (-1 : ℝ) 1 (by norm_num) (x 0)).val)
    (if upper then 1 else -1) = _
  rw [hclamp, hVec]

/-- One angular period of the original square boundary data pulled to the circle. -/
@[expose] def squareBoundaryAngular {E : Type*} [TopologicalSpace E] (b : C(UnitSquareBoundary, E)) (t : ℝ) : E :=
  b (unitSquareCircleHomeomorph.symm (nativeCircleLoopParam (vacuumLoopParameter (2 * Real.pi) t)))

abbrev squareBoundaryAngularTensor (b : C(UnitSquareBoundary, Tensor)) := squareBoundaryAngular b

/-- The one-dimensional Sobolev change of variables between the four sides
of a square and the circle through their bi-Lipschitz boundary chart. -/
@[expose] def External.SquareBoundaryAngularSobolev : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : C(UnitSquareBoundary, E)),
    (∀ i : Fin 2, ∀ positive : Bool,
      let e := b ∘ unitSquareSideParameter i positive
      AbsolutelyContinuousOnInterval e (-1) 1 ∧
      MemLp (deriv e) 2 (volume.restrict (Ioo (-1 : ℝ) 1))) →
    AbsolutelyContinuousOnInterval (squareBoundaryAngular b) 0 (2 * Real.pi) ∧
      MemLp (deriv (squareBoundaryAngular b)) 2 (volume.restrict (Ioo 0 (2 * Real.pi))) ∧
      (∫ t in Ioo 0 (2 * Real.pi), ‖deriv (squareBoundaryAngular b) t‖ ^ 2) ≤
        C * ∑ i : Fin 2, ∑ positive : Bool,
          ∫ t in Ioo (-1 : ℝ) 1, ‖deriv (b ∘ unitSquareSideParameter i positive) t‖ ^ 2

/-- The nonnegative density change of variables for the same boundary chart.
The coordinate side parameters and the angle use ordinary Lebesgue measure. -/
@[expose] def External.SquareBoundaryAngularMeasure : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ p : C(UnitSquareBoundary, ℝ), (∀ x, 0 ≤ p x) →
    (∫ t in Ioo 0 (2 * Real.pi), squareBoundaryAngular p t) ≤
      C * ∑ i : Fin 2, ∑ positive : Bool, ∫ t in Ioo (-1 : ℝ) 1, p (unitSquareSideParameter i positive t)

end Thesis
