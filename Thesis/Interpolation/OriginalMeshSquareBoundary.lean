module

public import Thesis.Interpolation.ProjectedMeshSquareBoundary
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The original unprojected trace of the same physical mesh face. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set StratificationTheory
open scoped Matrix.Norms.Frobenius Topology

namespace Thesis

variable {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}

@[expose] def meshSquareEdgeBulkEnergy (G : PenalizedSphereFaces a B h v hv)
    (f : ↥(cubeBoundarySquares G.grid.level)) : ℝ :=
  ∑ i : Fin 2, ∑ p : Bool, ∫ t in Ioo 0 h, bulkPotential a (G.grid.trace (tensorSquareCoordinateEdge f i p) t)

/-- A continuous original boundary of the selected physical face, expressed
in the centered unit-square coordinates. -/
structure OriginalMeshSquareBoundary (G : PenalizedSphereFaces a B h v hv)
    (f : ↥(cubeBoundarySquares G.grid.level)) where
  boundary : C(UnitSquareBoundary, S0)
  edge : ∀ i p t, t ∈ Icc (-1 : ℝ) 1 → boundary (unitSquareSideParameter i p t) =
    G.grid.trace (tensorSquareCoordinateEdge f i p) (normalizedEdgeParameter h t)
  edge_sobolev : ∀ i p,
    let e := boundary ∘ unitSquareSideParameter i p
    AbsolutelyContinuousOnInterval e (-1) 1 ∧ MemLp (deriv e) 2 (volume.restrict (Ioo (-1) 1))
  derivative_energy : (∑ i : Fin 2, ∑ p : Bool, ∫ t in Ioo (-1 : ℝ) 1,
    ‖deriv (boundary ∘ unitSquareSideParameter i p) t‖ ^ 2) =
      (h / 2) * meshSquareEdgeDerivativeEnergy G f
  bulk_energy : (∑ i : Fin 2, ∑ p : Bool, ∫ t in Ioo (-1 : ℝ) 1,
    bulkPotential a (boundary (unitSquareSideParameter i p t))) =
      (h / 2)⁻¹ * meshSquareEdgeBulkEnergy G f

theorem exists_originalMeshSquareBoundary (G : PenalizedSphereFaces a B h v hv)
    (f : ↥(cubeBoundarySquares G.grid.level)) : Nonempty (OriginalMeshSquareBoundary G f) := by
  letI : CompleteSpace S0 := complete_of_proper
  have hh := G.ht_pos
  let e (i : Fin 2) (p : Bool) := tensorSquareCoordinateEdge f i p
  let E (i : Fin 2) (p : Bool) : C(SquareParameterInterval, S0) :=
    ⟨fun t => G.grid.trace (e i p) (normalizedEdgeParameter h t.val), by
      have hC : ContinuousOn (G.grid.trace (e i p)) (Icc 0 h) :=
        (uIcc_of_le hh.le) ▸ (G.grid.trace_ac (e i p)).continuousOn
      exact hC.comp_continuous (by unfold normalizedEdgeParameter; fun_prop)
        (fun t => normalizedEdgeParameter_mem_closed hh t.property)⟩
  have hEnd (p : Bool) : normalizedEdgeParameter h (squareSideEndpoint p).val = if p then h else 0 := by
    cases p <;> simp only [normalizedEdgeParameter, squareSideEndpoint, squareSideSign, Bool.false_eq_true,
      ite_false, ite_true] <;> ring
  have hCorner (p q : Bool) : E 0 p (squareSideEndpoint q) = E 1 q (squareSideEndpoint p) := by
    change G.grid.trace (e 0 p) (normalizedEdgeParameter h (squareSideEndpoint q).val) =
      G.grid.trace (e 1 q) (normalizedEdgeParameter h (squareSideEndpoint p).val)
    rw [hEnd, hEnd]
    exact capEdge_corner_eq f p q
  obtain ⟨b, hb⟩ := exists_unitSquareBoundary_map E hCorner
  have hbRaw (i : Fin 2) (p : Bool) (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      b (unitSquareSideParameter i p t) = G.grid.trace (e i p) (normalizedEdgeParameter h t) :=
    hb i p ⟨t, ht⟩
  have hEdgeSob (i : Fin 2) (p : Bool) :
      let F := b ∘ unitSquareSideParameter i p
      AbsolutelyContinuousOnInterval F (-1) 1 ∧ MemLp (deriv F) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) ∧
        (∫ t in Ioo (-1 : ℝ) 1, ‖deriv F t‖ ^ 2) = (h / 2) * ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative (e i p) t‖ ^ 2 := by
    intro F
    obtain ⟨hAC, hDer, _, hEn⟩ := normalizedEdge_sobolev_data hh
      (G.grid.derivative_memLp (e i p)) (G.grid.trace_increment (e i p))
    obtain ⟨hAC', hDer', hEn'⟩ := transfer_closedEdgeSobolev (g := F)
      (fun t ht => (hbRaw i p t ht).symm) hAC hDer
    exact ⟨hAC', hDer', hEn'.trans hEn⟩
  refine ⟨⟨b, hbRaw, fun i p => ⟨(hEdgeSob i p).1, (hEdgeSob i p).2.1⟩, ?_, ?_⟩⟩
  · simp only [meshSquareEdgeDerivativeEnergy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => (hEdgeSob i p).2.2
  · simp only [meshSquareEdgeBulkEnergy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
    calc
      _ = ∫ t in Ioo (-1 : ℝ) 1, bulkPotential a (G.grid.trace (e i p) (normalizedEdgeParameter h t)) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        exact fun t ht => congrArg (bulkPotential a) (hbRaw i p t (Ioo_subset_Icc_self ht))
      _ = _ := integral_normalizedEdgeParameter hh (bulkPotential a ∘ G.grid.trace (e i p))

/-- The perimeter range and the original projected loop agree on all
points, using the actual clamped affine side parametrizations. -/
theorem OriginalMeshSquareBoundary.forall_boundary {G : PenalizedSphereFaces a B h v hv}
    {f : ↥(cubeBoundarySquares G.grid.level)}
    (D : OriginalMeshSquareBoundary G f) {P : S0 → Prop}
    (hEdges : ∀ i p t, t ∈ Icc 0 h → P (G.grid.trace (tensorSquareCoordinateEdge f i p) t)) :
    ∀ x, P (D.boundary x) := by
  intro x
  obtain ⟨i, p, t, rfl⟩ := exists_unitSquareSideParameter x
  rw [D.edge i p t.val t.property]
  exact hEdges i p _ (normalizedEdgeParameter_mem_closed G.ht_pos t.property)

end Thesis
