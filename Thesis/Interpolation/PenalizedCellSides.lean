module

public import Thesis.Interpolation.ShellCellFaceTraces
public import Thesis.Interpolation.EdgeRectangle
import Thesis.Foundation.VacuumTarget

/-! The actual affine radial sides over one selected penalized mesh. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped Matrix.Norms.Frobenius ENNReal Topology

namespace Thesis

variable {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}

/-- All mesh edges use the same fixed vacuum projection. -/
@[expose] noncomputable def PenalizedSphereGrid.projectedEdge (G : PenalizedSphereGrid a B h v hv)
    (e : ↥(cubeBoundaryEdges G.level)) (t : ℝ) : S0 :=
  (vacuumTubularProjection a).extend (G.trace e t)

@[expose] noncomputable def PenalizedSphereGrid.projectedEdgeDerivative (G : PenalizedSphereGrid a B h v hv)
    (e : ↥(cubeBoundaryEdges G.level)) (t : ℝ) : S0 :=
  fderiv ℝ (vacuumTubularProjection a).extend (G.trace e t) (G.derivative e t)

/-- The radial side is the original affine interpolation from the projected
inner edge to the original outer edge. -/
@[expose] noncomputable def PenalizedSphereGrid.cellSide (G : PenalizedSphereGrid a B h v hv)
    (e : ↥(cubeBoundaryEdges G.level)) (x : Domain 2) : Ambient 5 :=
  frobeniusCoordinateEquiv (edgeRectangleField h (G.trace e) (G.projectedEdge e) x)

@[expose] noncomputable def PenalizedSphereGrid.cellSideDerivative (G : PenalizedSphereGrid a B h v hv)
    (e : ↥(cubeBoundaryEdges G.level)) : Domain 2 → HarmonicMaps.Gradient 2 5 :=
  edgeRectangleGradient h (G.trace e) (G.projectedEdge e) (G.derivative e) (G.projectedEdgeDerivative e)

/-- The four side boundaries are the two original edge traces and the two
radial segments over their shared lattice vertices. -/
@[expose] noncomputable def PenalizedSphereGrid.cellSideEdge (G : PenalizedSphereGrid a B h v hv)
    (e : ↥(cubeBoundaryEdges G.level)) (i : Fin 2) (positive : Bool) (t : ℝ) : Ambient 5 :=
  if i = 0 then
    frobeniusCoordinateEquiv ((t / h) • G.trace e (if positive then h else 0) +
      (1 - t / h) • G.projectedEdge e (if positive then h else 0))
  else frobeniusCoordinateEquiv (if positive then G.trace e t else G.projectedEdge e t)

private theorem edgeRectangleCoordinates_native (x : Domain 2) : edgeRectangleCoordinates x = (x 0, x 1) := rfl

private theorem edgeRectangleDomain_square (h : ℝ) : edgeRectangleDomain 0 h h = tensorGridOpenParameterBox 2 h := by
  apply Subtype.ext
  ext x
  change ((edgeRectangleCoordinates x).1 ∈ Ioo (0 : ℝ) h ∧ (edgeRectangleCoordinates x).2 ∈ Ioo (0 : ℝ) h) ↔
    x ∈ ⋂ i : Fin 2, (EuclideanSpace.proj i) ⁻¹' Ioo (0 : ℝ) h
  rw [edgeRectangleCoordinates_native, mem_iInter]
  constructor
  · intro hx i
    fin_cases i
    · exact hx.1
    · exact hx.2
  · exact fun hx => ⟨hx 0, hx 1⟩

private theorem cellSide_edge_value (G : PenalizedSphereGrid a B h v hv) (hh : 0 < h)
    (e : ↥(cubeBoundaryEdges G.level)) (i : Fin 2) (positive : Bool) (x : Domain 1) :
    G.cellSide e (unitCellFaceSlice i x (if positive then h else 0)) = G.cellSideEdge e i positive (x 0) := by
  fin_cases i <;> cases positive <;> simp [PenalizedSphereGrid.cellSide, PenalizedSphereGrid.cellSideEdge,
    edgeRectangleField, edgeRectangleCoordinates_native, unitCellFaceSlice_coordinates, hh.ne']

/-- Edges meeting at the same original vertex share the identical tensor
value of the selected sphere representative. -/
theorem PenalizedSphereGrid.endpoint_value_eq {G : PenalizedSphereGrid a B h v hv}
    {e f : ↥(cubeBoundaryEdges G.level)} {s t : ℝ} (hs : s ∈ ({0, h} : Set ℝ)) (ht : t ∈ ({0, h} : Set ℝ))
    (hPoint : tensorGridEdgePoint G.center h e.val s = tensorGridEdgePoint G.center h f.val t) :
    G.trace e s = G.trace f t := by
  obtain ⟨θ, hθ, hθu⟩ := G.endpoint_eq e s hs
  obtain ⟨η, hη, hηu⟩ := G.endpoint_eq f t ht
  have heq : θ = η := Subtype.ext (hθ.trans ((congrArg NormedSpace.normalize hPoint).trans hη.symm))
  exact hθu.trans (heq ▸ hηu.symm)

/-- Around a given vertex the incident radial segments coincide pointwise. -/
theorem PenalizedSphereGrid.cellSide_radial_edge_eq {G : PenalizedSphereGrid a B h v hv}
    (e f : ↥(cubeBoundaryEdges G.level)) (positive negative : Bool) (r : ℝ)
    (hPoint : tensorGridEdgePoint G.center h e.val (if positive then h else 0) =
      tensorGridEdgePoint G.center h f.val (if negative then h else 0)) :
    G.cellSideEdge e 0 positive r = G.cellSideEdge f 0 negative r := by
  have hEq := G.endpoint_value_eq (e := e) (f := f)
    (by cases positive <;> simp) (by cases negative <;> simp) hPoint
  simp [PenalizedSphereGrid.cellSideEdge, PenalizedSphereGrid.projectedEdge, hEq]

/-- The affine side is continuous on the entire closed parameter square. -/
theorem PenalizedSphereGrid.cellSide_continuousOn (G : PenalizedSphereGrid a B h v hv) (hh : 0 < h)
    (e : ↥(cubeBoundaryEdges G.level)) : ContinuousOn (G.cellSide e) (sphericalFaceParameterBox h) := by
  have hu : ContinuousOn (G.trace e) (Icc 0 h) := by
    simpa only [uIcc_of_le hh.le] using! (G.trace_ac e).continuousOn
  have hv : ContinuousOn (G.projectedEdge e) (Icc 0 h) := by
    exact (vacuumTubularProjection a).contDiff_extend.continuous.comp_continuousOn hu
  have hcoord (i : Fin 2) : Continuous (fun x : Domain 2 => x i) := (EuclideanSpace.proj i).continuous
  have h1 : MapsTo (fun x : Domain 2 => x 0) (sphericalFaceParameterBox h) (Icc 0 h) := fun _ hx => hx.1
  have h2 : Continuous (fun x : Domain 2 => x 1 / h) := (hcoord 1).div_const h
  have h3 : Continuous (fun x : Domain 2 => (1 : ℝ) - x 1 / h) := continuous_const.sub h2
  have hc := (h2.continuousOn.smul (hu.comp (hcoord 0).continuousOn h1)).add
    (h3.continuousOn.smul (hv.comp (hcoord 0).continuousOn h1))
  simpa only [PenalizedSphereGrid.cellSide, edgeRectangleField, edgeRectangleCoordinates_native, Function.comp_apply]
    using! frobeniusCoordinateEquiv.continuous.comp_continuousOn hc

/-- Weak side fields and the exact original normalized edge classes on the
same projected mesh. -/
structure PenalizedCellSides (G : PenalizedSphereGrid a B h v hv) (C : ℝ) where
  projected_vacuum : ∀ e t, t ∈ Icc (0 : ℝ) h → G.projectedEdge e t ∈ vacuum a
  memW12 : ∀ e, MemW12 (tensorGridOpenParameterBox 2 h) (G.cellSide e) (G.cellSideDerivative e)
  side_bound : ∀ e x, x ∈ sphericalFaceParameterBox h → ‖G.cellSide e x‖ ≤ max B (Real.sqrt 2 * vacuumRadius a)
  trace : ∀ e, NormalizedSquareTraces h (G.cellSide e) (G.cellSideEdge e)
  penalized_bound : ∀ (ε : ElasticScale) e,
    (∫ x in (tensorGridOpenParameterBox 2 h).val, (1 / 2 : ℝ) * hsNormSq (G.cellSideDerivative e x) +
      (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm (G.cellSide e x))) ≤
      (h / 4) * (1 + C ^ 2) * (∫ s in Ioo (0 : ℝ) h, ‖G.derivative e s‖ ^ 2) +
        ((C / 2) * h⁻¹ + (ε : ℝ)⁻¹ ^ 2 * (C * h)) * ∫ s in Ioo (0 : ℝ) h, bulkPotential a (G.trace e s)

/-- Every edge in the same vacuum tube supplies an actual radial side with
its four exact physical edge classes and the separate tangential and bulk costs. -/
theorem exists_penalizedCellSides (a : BulkCoefficients) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ (vacuumTubularProjection a).radius ∧ 0 < C ∧
      ∀ {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}
        (G : PenalizedSphereGrid a B h v hv), 0 < h →
        (∀ e t, t ∈ Icc (0 : ℝ) h → G.trace e t ∈ vacuumTube a δ) →
          Nonempty (PenalizedCellSides G C) := by
  classical
  obtain ⟨δ, C, hδ, hδp, hC, hProjection⟩ := exists_projected_edge_data a
  refine ⟨δ, C, hδ, hδp, hC, fun {B h v hv} G hh hTube => ?_⟩
  have hProjected (e : ↥(cubeBoundaryEdges G.level)) := hProjection hh (G.trace_ac e) (G.derivative_memLp e)
    (G.trace_increment e) (hTube e)
  have hU (e : ↥(cubeBoundaryEdges G.level)) : ContinuousOn (G.trace e) (Icc 0 h) := by
    simpa only [uIcc_of_le hh.le] using! (G.trace_ac e).continuousOn
  have hV (e : ↥(cubeBoundaryEdges G.level)) : ContinuousOn (G.projectedEdge e) (Icc 0 h) := by
    simpa only [uIcc_of_le hh.le] using! (hProjected e).1.continuousOn
  have hBound (e : ↥(cubeBoundaryEdges G.level)) (x : Domain 2) (hx : x ∈ sphericalFaceParameterBox h) :
      ‖G.cellSide e x‖ ≤ max B (Real.sqrt 2 * vacuumRadius a) := by
    let t := x 0
    let r := x 1
    let α := r / h
    let M := max B (Real.sqrt 2 * vacuumRadius a)
    have ht : t ∈ Icc (0 : ℝ) h := hx.1
    have hr : r ∈ Icc (0 : ℝ) h := hx.2
    have hα : 0 ≤ α := div_nonneg hr.1 hh.le
    have hα₁ : α ≤ 1 := (div_le_one hh).mpr hr.2
    have hu : ‖G.trace e t‖ ≤ M := (G.trace_bound e t ht).trans (le_max_left _ _)
    have hv : ‖G.projectedEdge e t‖ ≤ M :=
      (vacuum_norm ((hProjected e).2.2.2 t ht).1).le.trans (le_max_right _ _)
    rw [PenalizedSphereGrid.cellSide, LinearIsometryEquiv.norm_map, edgeRectangleField, edgeRectangleCoordinates_native]
    change ‖α • G.trace e t + (1 - α) • G.projectedEdge e t‖ ≤ M
    calc
      _ ≤ ‖α • G.trace e t‖ + ‖(1 - α) • G.projectedEdge e t‖ := norm_add_le _ _
      _ ≤ α * M + (1 - α) * M := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hα, Real.norm_of_nonneg (sub_nonneg.mpr hα₁)]
        exact add_le_add (mul_le_mul_of_nonneg_left hu hα) (mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr hα₁))
      _ = _ := by ring
  have hTrace (e : ↥(cubeBoundaryEdges G.level)) : Nonempty (NormalizedSquareTraces h (G.cellSide e) (G.cellSideEdge e)) := by
    obtain ⟨T⟩ := exists_physicalSquareTraces_of_continuousOn hh (G.cellSide_continuousOn hh e) (hBound e)
      (fun i p x _ => cellSide_edge_value G hh e i p x)
    exact T.exists_normalized
  refine ⟨{ projected_vacuum := fun e t ht => ((hProjected e).2.2.2 t ht).1
            memW12 := ?_
            side_bound := hBound
            trace := fun e => Classical.choice (hTrace e)
            penalized_bound := ?_ }⟩
  · intro e
    have hw := (edgeRectangle_memW12_and_gradient_energy hh hh (hU e) (hV e) (G.derivative_memLp e)
      (hProjected e).2.1 (G.trace_increment e) (hProjected e).2.2.1).1
    rw [edgeRectangleDomain_square] at hw
    exact hw
  · intro ε e
    have he := edgeRectangle_penalizedEnergy_bound a ε hh hh hC.le (hU e) (hV e)
      (G.derivative_memLp e) (hProjected e).2.1 (G.trace_increment e) (hProjected e).2.2.1
      (fun t ht => ((hProjected e).2.2.2 t ht).2.1)
      (fun t ht => ((hProjected e).2.2.2 t ht).2.2.2.2.1)
      (fun s hs => ((hProjected e).2.2.2 s hs).2.2.2.2.2)
    rw [edgeRectangleDomain_square] at he
    have hD (x : Domain 2) : G.cellSideDerivative e x = edgeRectangleGradient h (G.trace e)
        (G.projectedEdge e) (G.derivative e)
        (fun t => fderiv ℝ (vacuumTubularProjection a).extend (G.trace e t) (G.derivative e t)) x := rfl
    have hW (x : Domain 2) : frobeniusCoordinateEquiv.symm (G.cellSide e x) =
        edgeRectangleField h (G.trace e) (G.projectedEdge e) x :=
      frobeniusCoordinateEquiv.symm_apply_apply _
    simpa only [hD, hW] using! he

end Thesis
