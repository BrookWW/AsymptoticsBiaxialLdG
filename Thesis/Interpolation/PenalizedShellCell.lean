module

public import Thesis.Interpolation.PenalizedCellSides
import StratificationTheory.Foundation.CubicalSignedFaceCoordinate
import Thesis.Foundation.VacuumTarget

/-! Assembly of the six actual faces of each selected penalized shell cell. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

variable {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}

/-- A vacuum-valued inner square with the actual projected mesh edge classes. -/
structure ProjectedCellInnerFace (G : PenalizedSphereFaces a B h v hv)
    (f : ↥(cubeBoundarySquares G.grid.level)) where
  field : Domain 2 → Ambient 5
  derivative : Domain 2 → HarmonicMaps.Gradient 2 5
  memW12 : MemW12 (tensorGridOpenParameterBox 2 h) field derivative
  vacuum_ae : ∀ᵐ x ∂volume.restrict (tensorGridOpenParameterBox 2 h).val,
    frobeniusCoordinateEquiv.symm (field x) ∈ vacuum a
  trace : NormalizedSquareTraces h field
    (fun i b t => frobeniusCoordinateEquiv (G.grid.projectedEdge (tensorSquareCoordinateEdge f i b) t))

private theorem unitCellFacePoint_coordinates (j : CellFaceIndex) (x : Domain 2) (t : ℝ) :
    unitCellFacePoint j x t =
      if j.1 = 0 then WithLp.toLp 2 ![if j.2 then t else -t, x 1, x 0]
      else if j.1 = 1 then WithLp.toLp 2 ![x 0, if j.2 then t else -t, x 1]
      else WithLp.toLp 2 ![x 0, x 1, if j.2 then t else -t] := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  have hPair : e.symm (x, EuclideanSpace.single 0 t) = WithLp.toLp 2 ![x 0, x 1, t] := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  change StratificationTheory.cubicalSignedFaceIsometry 2 j.1 j.2
    (e.symm (x, EuclideanSpace.single 0 t)) = _
  rw [hPair]
  obtain ⟨i, positive⟩ := j
  apply PiLp.ext
  intro k
  fin_cases i <;> fin_cases k <;>
    simp [StratificationTheory.cubicalSignedFaceIsometry_coordinate, Fin.last]
  all_goals rfl

private theorem unitCellEdgePoint_as_slice (j : CellFaceIndex) (i : Fin 2) (positive : Bool) (x : Domain 1) :
    unitCellEdgePoint j i positive x = unitCellFacePoint j (unitCellFaceSlice i x (if positive then 1 else -1)) 1 := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
  have hPair : e.symm (x, EuclideanSpace.single 0 1) = WithLp.toLp 2 ![x 0, 1] := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext <;> ext k <;> fin_cases k <;> rfl
  unfold unitCellEdgePoint
  apply congrArg (fun y => unitCellFacePoint j y 1)
  change StratificationTheory.cubicalSignedFaceIsometry 1 i positive (e.symm (x, EuclideanSpace.single 0 1)) = _
  rw [hPair, unitCellFaceSlice_coordinates]
  apply PiLp.ext
  intro k
  fin_cases i <;> fin_cases k <;>
    simp [StratificationTheory.cubicalSignedFaceIsometry_coordinate, Fin.last]

@[expose] def shellCellSideEdge {G : PenalizedSphereFaces a B h v hv}
    (f : ↥(cubeBoundarySquares G.grid.level)) (j : CellFaceIndex) : ↥(cubeBoundaryEdges G.grid.level) :=
  tensorSquareCoordinateEdge f (if j.1 = 0 then 0 else 1) j.2

/-- The two caps and four affine sides, each in its actual signed coordinate order. -/
@[expose] noncomputable def penalizedShellCellFace {G : PenalizedSphereFaces a B h v hv}
    {f : ↥(cubeBoundarySquares G.grid.level)} (I : ProjectedCellInnerFace G f) (j : CellFaceIndex) : Domain 2 → Ambient 5 :=
  if j.1 = 0 then G.grid.cellSide (shellCellSideEdge f j) ∘ physicalSquareSwap
  else if j.1 = 1 then G.grid.cellSide (shellCellSideEdge f j)
  else if j.2 then fun x => frobeniusCoordinateEquiv (G.face f x) else I.field

@[expose] noncomputable def penalizedShellCellFaceDerivative {G : PenalizedSphereFaces a B h v hv}
    {f : ↥(cubeBoundarySquares G.grid.level)} (I : ProjectedCellInnerFace G f) (j : CellFaceIndex) :
    Domain 2 → HarmonicMaps.Gradient 2 5 :=
  if j.1 = 0 then fun x i => ∑ k : Fin 2, (physicalSquareSwap (EuclideanSpace.single i 1)) k •
      G.grid.cellSideDerivative (shellCellSideEdge f j) (physicalSquareSwap x) k
  else if j.1 = 1 then G.grid.cellSideDerivative (shellCellSideEdge f j)
  else if j.2 then fun x i => frobeniusCoordinateEquiv (G.derivative f x i) else I.derivative

private noncomputable def penalizedShellCellFaceEdge {G : PenalizedSphereFaces a B h v hv}
    (f : ↥(cubeBoundarySquares G.grid.level)) (j : CellFaceIndex) : Fin 2 → Bool → ℝ → Ambient 5 :=
  if j.1 = 0 then fun i => G.grid.cellSideEdge (shellCellSideEdge f j) (Equiv.swap 0 1 i)
  else if j.1 = 1 then G.grid.cellSideEdge (shellCellSideEdge f j)
  else fun i positive t => frobeniusCoordinateEquiv (if j.2 then G.grid.trace (tensorSquareCoordinateEdge f i positive) t
    else G.grid.projectedEdge (tensorSquareCoordinateEdge f i positive) t)

private noncomputable def shellCellUnitEdgeValue {G : PenalizedSphereFaces a B h v hv}
    (f : ↥(cubeBoundarySquares G.grid.level)) (x : Point) : Ambient 5 :=
  let t := h / 2 + (h / 2) * x 0
  let s := h / 2 + (h / 2) * x 1
  let r := (x 2 + 1) / 2
  let u := if x 0 = -1 then G.grid.trace (tensorSquareLeftEdge f) s
    else if x 0 = 1 then G.grid.trace (tensorSquareRightEdge f) s
    else if x 1 = -1 then G.grid.trace (tensorSquareLowerEdge f) t
    else G.grid.trace (tensorSquareUpperEdge f) t
  frobeniusCoordinateEquiv (r • u + (1 - r) • (vacuumTubularProjection a).extend u)

theorem capEdge_corner_eq {G : PenalizedSphereFaces a B h v hv}
    (f : ↥(cubeBoundarySquares G.grid.level)) (b c : Bool) :
    G.grid.trace (tensorSquareCoordinateEdge f 0 b) (if c then h else 0) =
      G.grid.trace (tensorSquareCoordinateEdge f 1 c) (if b then h else 0) := by
  let s := if b then h else 0
  let t := if c then h else 0
  let x := tensorGridSquarePoint (tensorGridVertex G.grid.center h f.val.1) f.val.2 s t
  have hX₀ : x = tensorGridEdgePoint G.grid.center h (tensorSquareCoordinateEdge f 0 b).val t := by
    obtain ⟨_, _, hL, hR⟩ := tensorGridSquarePoint_boundary G.grid.center h f.val t
    cases b
    · simpa [x, s, tensorSquareCoordinateEdge, tensorSquareLeftEdge] using hL
    · simpa [x, s, tensorSquareCoordinateEdge, tensorSquareRightEdge] using hR
  have hX₁ : x = tensorGridEdgePoint G.grid.center h (tensorSquareCoordinateEdge f 1 c).val s := by
    obtain ⟨hB, hT, _, _⟩ := tensorGridSquarePoint_boundary G.grid.center h f.val s
    cases c
    · simpa [x, t, tensorSquareCoordinateEdge, tensorSquareLowerEdge] using hB
    · simpa [x, t, tensorSquareCoordinateEdge, tensorSquareUpperEdge] using hT
  exact G.grid.endpoint_value_eq (by cases c <;> simp) (by cases b <;> simp) (hX₀.symm.trans hX₁)

private theorem penalizedShellCellEdge_value {G : PenalizedSphereFaces a B h v hv}
    (f : ↥(cubeBoundarySquares G.grid.level)) (j : CellFaceIndex) (i : Fin 2) (positive : Bool)
    (x : Domain 1) (hx : x ∈ (unitCellCube 1).val) :
    penalizedShellCellFaceEdge f j i positive (unitEdgeToPhysical h x) =
      shellCellUnitEdgeValue f (unitCellEdgePoint j i positive x) := by
  have hx' := abs_lt.mp ((StratificationTheory.mem_unit_coordinate_face_iff x).mp hx 0)
  have hxn : x 0 ≠ -1 := ne_of_gt hx'.1
  have hxp : x 0 ≠ 1 := ne_of_lt hx'.2
  have hh := G.ht_pos
  have hr : (h / 2 + h / 2 * x 0) / h = (x 0 + 1) / 2 := by
    field_simp
    ring
  have hNe : (1 : ℝ) ≠ -1 := by norm_num
  have hLL : G.grid.trace (tensorSquareLowerEdge f) 0 = G.grid.trace (tensorSquareLeftEdge f) 0 := by
    simpa [tensorSquareCoordinateEdge] using (capEdge_corner_eq f false false).symm
  have hLR : G.grid.trace (tensorSquareLowerEdge f) h = G.grid.trace (tensorSquareRightEdge f) 0 := by
    simpa [tensorSquareCoordinateEdge] using (capEdge_corner_eq f true false).symm
  have hUL : G.grid.trace (tensorSquareUpperEdge f) 0 = G.grid.trace (tensorSquareLeftEdge f) h := by
    simpa [tensorSquareCoordinateEdge] using (capEdge_corner_eq f false true).symm
  have hUR : G.grid.trace (tensorSquareUpperEdge f) h = G.grid.trace (tensorSquareRightEdge f) h := by
    simpa [tensorSquareCoordinateEdge] using (capEdge_corner_eq f true true).symm
  obtain ⟨j, b⟩ := j
  fin_cases j <;> fin_cases i <;> cases b <;> cases positive <;>
    simp [penalizedShellCellFaceEdge, shellCellSideEdge, shellCellUnitEdgeValue, tensorSquareCoordinateEdge,
      PenalizedSphereGrid.cellSideEdge, PenalizedSphereGrid.projectedEdge, unitEdgeToPhysical, unitCellEdgePoint_as_slice,
      unitCellFacePoint_coordinates, unitCellFaceSlice_coordinates, hr, hNe, hxn, hxp, hLL, hLR, hUL, hUR]

/-- The original upper face, actual projected inner face and the four affine
lateral sides form one compatible physical face family. The common edge
has the same value even when read from a different incident side. -/
theorem exists_penalizedShellCellFaceFamily {G : PenalizedSphereFaces a B h v hv}
    (hB : ∀ θ, ‖v θ‖ ≤ B) {C : ℝ} (S : PenalizedCellSides G.grid C)
    {f : ↥(cubeBoundarySquares G.grid.level)} (I : ProjectedCellInnerFace G f) :
    ∃ A : CompatiblePhysicalCellFaces 5 (max B (Real.sqrt 2 * vacuumRadius a)) h,
      A.face = penalizedShellCellFace I ∧ A.derivative = penalizedShellCellFaceDerivative I := by
  classical
  have hh := G.ht_pos
  let E (j : CellFaceIndex) := shellCellSideEdge f j
  have hData (j : CellFaceIndex) : Nonempty (NormalizedSquareTraces h (penalizedShellCellFace I j)
      (penalizedShellCellFaceEdge f j)) := by
    obtain ⟨j, b⟩ := j
    fin_cases j
    · simpa [penalizedShellCellFace, penalizedShellCellFaceEdge, E] using
        (⟨(S.trace (E (0, b))).swap⟩ : Nonempty _)
    · simpa [penalizedShellCellFace, penalizedShellCellFaceEdge, E] using
        (⟨S.trace (E (1, b))⟩ : Nonempty _)
    · cases b
      · simpa [penalizedShellCellFace, penalizedShellCellFaceEdge] using (⟨I.trace⟩ : Nonempty _)
      · simpa [penalizedShellCellFace, penalizedShellCellFaceEdge] using G.exists_normalized_traces f
  let T (j : CellFaceIndex) := Classical.choice (hData j)
  have hSideBound (e : ↥(cubeBoundaryEdges G.grid.level)) :
      ∀ᵐ x ∂volume.restrict (tensorGridOpenParameterBox 2 h).val, ‖G.grid.cellSide e x‖ ≤
        max B (Real.sqrt 2 * vacuumRadius a) := by
    filter_upwards [ae_restrict_mem (tensorGridOpenParameterBox 2 h).property.measurableSet] with x hx
    exact S.side_bound e x ⟨Ioo_subset_Icc_self (mem_iInter.mp hx 0), Ioo_subset_Icc_self (mem_iInter.mp hx 1)⟩
  have hCapBound : ∀ᵐ x ∂volume.restrict (tensorGridOpenParameterBox 2 h).val,
      ‖frobeniusCoordinateEquiv (G.face f x)‖ ≤ max B (Real.sqrt 2 * vacuumRadius a) := by
    filter_upwards [ae_restrict_mem (tensorGridOpenParameterBox 2 h).property.measurableSet] with x hx
    obtain ⟨θ, _, hF⟩ := G.face_eq f x (Ioo_subset_Icc_self (mem_iInter.mp hx 0))
      (Ioo_subset_Icc_self (mem_iInter.mp hx 1))
    rw [LinearIsometryEquiv.norm_map, hF]
    exact (hB θ).trans (le_max_left _ _)
  have hInnerBound : ∀ᵐ x ∂volume.restrict (tensorGridOpenParameterBox 2 h).val,
      ‖I.field x‖ ≤ max B (Real.sqrt 2 * vacuumRadius a) := by
    filter_upwards [I.vacuum_ae] with x hx
    rw [← frobeniusCoordinateEquiv.symm.norm_map (I.field x), vacuum_norm hx]
    exact le_max_right _ _
  refine ⟨{ face := penalizedShellCellFace I
            derivative := penalizedShellCellFaceDerivative I
            face_memW12 := ?_
            face_bound := ?_
            edge := shellCellUnitEdgeValue f ∘ shellCellParameterToUnit h
            trace := fun j => (T j).curve
            trace_slice := fun j => (T j).slice
            trace_edge := ?_ }, rfl, rfl⟩
  · rintro ⟨j, b⟩
    fin_cases j
    · simpa [penalizedShellCellFace, penalizedShellCellFaceDerivative, E] using
        (memW12_physicalSquareSwap hh (S.memW12 (E (0, b)))).1
    · simpa [penalizedShellCellFace, penalizedShellCellFaceDerivative, E] using S.memW12 (E (1, b))
    · cases b
      · simpa [penalizedShellCellFace, penalizedShellCellFaceDerivative] using I.memW12
      · simpa [penalizedShellCellFace, penalizedShellCellFaceDerivative] using G.face_memW12 f
  · rintro ⟨j, b⟩
    fin_cases j
    · simpa [penalizedShellCellFace, E, Function.comp_apply] using
        (measurePreserving_physicalSquareSwap h).quasiMeasurePreserving.ae (hSideBound (E (0, b)))
    · simpa [penalizedShellCellFace, E] using hSideBound (E (1, b))
    · cases b
      · simpa [penalizedShellCellFace] using hInnerBound
      · simpa [penalizedShellCellFace] using hCapBound
  · intro j i p
    refine (T j).edge i p |>.trans ?_
    filter_upwards [ae_restrict_mem (unitCellCube 1).property.measurableSet] with x hx
    change _ = shellCellUnitEdgeValue f (shellCellParameterToUnit h
      (unitToShellCellParameter h (unitCellEdgePoint j i p x)))
    rw [shellCellParameterToUnit_unitToShellCellParameter hh]
    exact penalizedShellCellEdge_value f j i p x hx

/-- The selected cell with its own actual projected inner face has a single
filled Sobolev graph and the same six original physical face fields. -/
theorem exists_penalizedShellCell {G : PenalizedSphereFaces a B h v hv}
    (hB : ∀ θ, ‖v θ‖ ≤ B) (hSmall : h ≤ 1 / 32) {C : ℝ} (S : PenalizedCellSides G.grid C)
    {f : ↥(cubeBoundarySquares G.grid.level)} (I : ProjectedCellInnerFace G f) :
    ∃ A : CompatiblePhysicalCellFaces 5 (max B (Real.sqrt 2 * vacuumRadius a)) h,
      A.face = penalizedShellCellFace I ∧ A.derivative = penalizedShellCellFaceDerivative I ∧
      Nonempty (SphericalCellFilling (A.toUnit G.ht_pos) G.grid.center h f.val) := by
  obtain ⟨A, hFace, hDerivative⟩ := exists_penalizedShellCellFaceFamily hB S I
  have hHalf : h ≤ 1 / 2 := hSmall.trans (by norm_num)
  have hCenter (i : Fin 3) : G.grid.center i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(G.grid.offset_mem i).1, (G.grid.offset_mem i).2.le.trans hSmall⟩
  exact ⟨A, hFace, hDerivative, exists_sphericalCellFilling (A.toUnit G.ht_pos)
    G.ht_pos hHalf hCenter G.grid.radius_mem f.property⟩

/-- In either ordering of the side coordinates, the actual boundary point
is the same chart of the same projected mesh edge. -/
theorem shellCellSide_point {G : PenalizedSphereFaces a B h v hv}
    (f : ↥(cubeBoundarySquares G.grid.level)) (j : CellFaceIndex) (hj : j.1 ≠ 2) (x : Domain 2) :
    let y := unitToPhysicalCellFace h x
    normalizedShellCellPoint G.grid.center h f.val (unitCellFacePoint j x 1) =
      sphericalLateralEdge G.grid.center h (shellCellSideEdge f j).val
        (if j.1 = 0 then (y 1, 1 - h + y 0) else (y 0, 1 - h + y 1)) := by
  intro y
  let c := G.grid.center
  have h0 : h / 2 + (h / 2) * (-1) = 0 := by ring
  have h1 : h / 2 + (h / 2) * 1 = h := by ring
  obtain ⟨j, b⟩ := j
  fin_cases j
  · have hL := (sphericalCellPoint_boundary c h f.val (y 1) (y 1) (1 - h + y 0)).2.2.2.2.1
    have hR := (sphericalCellPoint_boundary c h f.val (y 1) (y 1) (1 - h + y 0)).2.2.2.2.2
    cases b
    · simpa [normalizedShellCellPoint, sphericalCellNativePoint, sphericalCellNativeParameter,
        unitToShellCellParameter, shellCellParameterCenter, shellCellParameterLower, unitCellFacePoint_coordinates,
        shellCellSideEdge, tensorSquareCoordinateEdge, tensorSquareLeftEdge, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul, add_assoc, h0, y, c, unitToPhysicalCellFace] using hL
    · simpa [normalizedShellCellPoint, sphericalCellNativePoint, sphericalCellNativeParameter,
        unitToShellCellParameter, shellCellParameterCenter, shellCellParameterLower, unitCellFacePoint_coordinates,
        shellCellSideEdge, tensorSquareCoordinateEdge, tensorSquareRightEdge, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul, add_assoc, h1, y, c, unitToPhysicalCellFace] using hR
  · have hL := (sphericalCellPoint_boundary c h f.val (y 0) (y 0) (1 - h + y 1)).2.2.1
    have hR := (sphericalCellPoint_boundary c h f.val (y 0) (y 0) (1 - h + y 1)).2.2.2.1
    cases b
    · simpa [normalizedShellCellPoint, sphericalCellNativePoint, sphericalCellNativeParameter,
        unitToShellCellParameter, shellCellParameterCenter, shellCellParameterLower, unitCellFacePoint_coordinates,
        shellCellSideEdge, tensorSquareCoordinateEdge, tensorSquareLowerEdge, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul, add_assoc, h0, y, c, unitToPhysicalCellFace] using hL
    · simpa [normalizedShellCellPoint, sphericalCellNativePoint, sphericalCellNativeParameter,
        unitToShellCellParameter, shellCellParameterCenter, shellCellParameterLower, unitCellFacePoint_coordinates,
        shellCellSideEdge, tensorSquareCoordinateEdge, tensorSquareUpperEdge, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul, add_assoc, h1, y, c, unitToPhysicalCellFace] using hR
  · exact (hj (by rfl)).elim

/-- The angular cap coordinates take a centered unit square parameter to
the original normalized lattice square. -/
@[expose] noncomputable def shellCapAngularPoint (c : Point) (h : ℝ) (f : TensorGridSquare) (x : Domain 2) : Point :=
  sphericalFaceParameterPoint c h f (unitToPhysicalCellFace h x)

/-- The linear radius of a normalized cap coordinate. -/
@[expose] noncomputable def shellCapRadius (h t : ℝ) : ℝ := 1 - h / 2 + (h / 2) * t

/-- Native normal cap slices are exactly the original radial slices of the
actual angular square. -/
theorem normalizedShellCellPoint_cap_slice (c : Point) (h : ℝ) (f : TensorGridSquare) (x : Domain 2) (t : ℝ) :
    normalizedShellCellPoint c h f (unitCellFacePoint (2, true) x t) =
      shellCapRadius h t • shellCapAngularPoint c h f x := by
  have hParam : sphericalCellNativeParameter (unitToShellCellParameter h (unitCellFacePoint (2, true) x t)) =
      (((unitToPhysicalCellFace h x) 0, (unitToPhysicalCellFace h x) 1), shellCapRadius h t) := by
    rw [unitCellFacePoint_coordinates]
    apply Prod.ext
    · apply Prod.ext
      · change 0 + h / 2 + (h / 2) * x 0 = h / 2 + (h / 2) * x 0
        rw [zero_add]
      · change 0 + h / 2 + (h / 2) * x 1 = h / 2 + (h / 2) * x 1
        rw [zero_add]
    · change 1 - h + h / 2 + (h / 2) * t = shellCapRadius h t
      unfold shellCapRadius
      ring
  rw [normalizedShellCellPoint, sphericalCellNativePoint, Function.comp_apply, hParam]
  rfl

theorem unitCellFacePoint_cap_coordinate (x : Domain 2) (t : ℝ) :
    unitCellFacePoint (2, true) x t =
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).symm (x, EuclideanSpace.single 0 t) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  have hPair : e.symm (x, EuclideanSpace.single 0 t) = WithLp.toLp 2 ![x 0, x 1, t] := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  rw [unitCellFacePoint_coordinates]
  exact hPair.symm

end Thesis
