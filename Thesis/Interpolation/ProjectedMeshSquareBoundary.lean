module

public import Thesis.Interpolation.SquareBoundaryPasting
public import Thesis.Interpolation.SquareDiskFill
public import Thesis.Interpolation.PenalizedShellCell
public import Thesis.Interpolation.NormalizedEdgeSobolev
import Thesis.Interpolation.EdgeProjectionLayer

/-! The four original projected mesh edges as one genuine Sobolev loop. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped Matrix.Norms.Frobenius Topology

namespace Thesis

theorem transfer_closedEdgeSobolev {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} (hEq : EqOn f g (Icc (-1 : ℝ) 1))
    (hAC : AbsolutelyContinuousOnInterval f (-1) 1)
    (hD : MemLp (deriv f) 2 (volume.restrict (Ioo (-1 : ℝ) 1))) :
    AbsolutelyContinuousOnInterval g (-1) 1 ∧ MemLp (deriv g) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) ∧
      (∫ t in Ioo (-1 : ℝ) 1, ‖deriv g t‖ ^ 2) = ∫ t in Ioo (-1 : ℝ) 1, ‖deriv f t‖ ^ 2 := by
  have hDer : deriv f =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] deriv g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have h : f =ᶠ[𝓝 t] g := Filter.Eventually.mono (Icc_mem_nhds ht.1 ht.2) hEq
    exact h.deriv_eq
  refine ⟨?_, hD.ae_eq hDer, integral_congr_ae (hDer.symm.mono fun _ h => congrArg (fun x : E => ‖x‖ ^ 2) h)⟩
  rw [absolutelyContinuousOnInterval_iff] at hAC ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hAC ε hε
  refine ⟨δ, hδ, fun I hI hSmall => ?_⟩
  refine lt_of_eq_of_lt (Finset.sum_congr rfl fun i hi => ?_) (h I hI hSmall)
  have hPair := hI.1 i hi
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hPair
  rw [← hEq hPair.1, ← hEq hPair.2]

variable {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}

@[expose] def meshSquareEdgeDerivativeEnergy (G : PenalizedSphereFaces a B h v hv)
    (f : ↥(cubeBoundarySquares G.grid.level)) : ℝ :=
  ∑ i : Fin 2, ∑ p : Bool, ∫ t in Ioo 0 h,
    ‖G.grid.derivative (tensorSquareCoordinateEdge f i p) t‖ ^ 2

/-- One continuous vacuum boundary carries the actual four projected-edge
restrictions, all their Sobolev derivatives and the uniform physical cost. -/
structure ProjectedMeshSquareBoundary (G : PenalizedSphereFaces a B h v hv)
    (f : ↥(cubeBoundarySquares G.grid.level)) (C : ℝ) where
  boundary : C(UnitSquareBoundary, vacuum a)
  edge : ∀ i p t, t ∈ Icc (-1 : ℝ) 1 → (boundary (unitSquareSideParameter i p t)).val =
    G.grid.projectedEdge (tensorSquareCoordinateEdge f i p) (normalizedEdgeParameter h t)
  edge_sobolev : ∀ i p,
    let e := fun t : ℝ => ((boundary (unitSquareSideParameter i p t)).val : Tensor)
    AbsolutelyContinuousOnInterval e (-1) 1 ∧ MemLp (deriv e) 2 (volume.restrict (Ioo (-1 : ℝ) 1))
  energy : (∑ i : Fin 2, ∑ p : Bool, ∫ t in Ioo (-1 : ℝ) 1,
    ‖deriv (fun s => ((boundary (unitSquareSideParameter i p s)).val : Tensor)) t‖ ^ 2) ≤
    C * h * meshSquareEdgeDerivativeEnergy G f

/-- Close the common projected edges into a single map on each actual face boundary. -/
theorem exists_projected_meshSquareBoundary (a : BulkCoefficients) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ (vacuumTubularProjection a).radius ∧ 0 < C ∧
      ∀ {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}
        (G : PenalizedSphereFaces a B h v hv), 0 < h →
        (∀ e t, t ∈ Icc (0 : ℝ) h → G.grid.trace e t ∈ vacuumTube a δ) →
        ∀ f, Nonempty (ProjectedMeshSquareBoundary G f C) := by
  obtain ⟨δ, K, hδ, hδR, hK, hProjection⟩ := exists_projected_edge_data a
  refine ⟨δ, K ^ 2 / 2, hδ, hδR, by positivity, ?_⟩
  intro B h v hv G hh hTube f
  have hP (e : ↥(cubeBoundaryEdges G.grid.level)) := hProjection hh (G.grid.trace_ac e)
    (G.grid.derivative_memLp e) (G.grid.trace_increment e) (hTube e)
  let e (i : Fin 2) (p : Bool) := tensorSquareCoordinateEdge f i p
  let U (i : Fin 2) (p : Bool) (t : ℝ) := G.grid.projectedEdge (e i p) t
  let D (i : Fin 2) (p : Bool) (t : ℝ) := G.grid.projectedEdgeDerivative (e i p) t
  let L := symmetricTraceless.subtypeL
  have hVac (i : Fin 2) (p : Bool) (t : SquareParameterInterval) :
      U i p (normalizedEdgeParameter h t.val) ∈ vacuum a :=
    ((hP (e i p)).2.2.2 _ (normalizedEdgeParameter_mem_closed hh t.property)).1
  let E (i : Fin 2) (p : Bool) : C(SquareParameterInterval, vacuum a) :=
    ⟨fun t => ⟨U i p (normalizedEdgeParameter h t.val), hVac i p t⟩, by
      apply Continuous.subtype_mk
      have hC : ContinuousOn (U i p) (Icc 0 h) := by
        change ContinuousOn ((vacuumTubularProjection a).extend ∘ G.grid.trace (e i p)) (Icc 0 h)
        exact (uIcc_of_le hh.le) ▸ (hP (e i p)).1.continuousOn
      exact hC.comp_continuous (by unfold normalizedEdgeParameter; fun_prop)
        (fun t => normalizedEdgeParameter_mem_closed hh t.property)⟩
  have hEnd (p : Bool) : normalizedEdgeParameter h (squareSideEndpoint p).val = if p then h else 0 := by
    cases p <;> simp only [normalizedEdgeParameter, squareSideEndpoint, squareSideSign, Bool.false_eq_true,
      ite_false, ite_true] <;> ring
  have hCorner (p q : Bool) : E 0 p (squareSideEndpoint q) = E 1 q (squareSideEndpoint p) := by
    apply Subtype.ext
    change U 0 p (normalizedEdgeParameter h (squareSideEndpoint q).val) =
      U 1 q (normalizedEdgeParameter h (squareSideEndpoint p).val)
    rw [hEnd, hEnd]
    exact congrArg (vacuumTubularProjection a).extend (capEdge_corner_eq f p q)
  obtain ⟨b, hb⟩ := exists_unitSquareBoundary_map E hCorner
  have hbRaw (i : Fin 2) (p : Bool) (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      (b (unitSquareSideParameter i p t)).val = U i p (normalizedEdgeParameter h t) :=
    congrArg Subtype.val (hb i p ⟨t, ht⟩)
  have hData (i : Fin 2) (p : Bool) :
      let F := fun t : ℝ => ((b (unitSquareSideParameter i p t)).val : Tensor)
      AbsolutelyContinuousOnInterval F (-1) 1 ∧ MemLp (deriv F) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) ∧
      (∫ t in Ioo (-1 : ℝ) 1, ‖deriv F t‖ ^ 2) ≤ (K ^ 2 / 2 * h) * ∫ t in Ioo 0 h, ‖G.grid.derivative (e i p) t‖ ^ 2 := by
    intro F
    have hLp : MemLp (fun t => D i p t) 2 (volume.restrict (Ioo 0 h)) := (hP (e i p)).2.1
    have hLpT := L.comp_memLp' hLp
    have hI (s : ℝ) (hs : s ∈ Icc 0 h) (t : ℝ) (ht : t ∈ Icc 0 h) :
        L (U i p t) - L (U i p s) = ∫ x in s..t, L (D i p x) := by
      have hInt := StratificationTheory.intervalIntegrable_of_memLp_two hh.le hLp
      have hs' : s ∈ uIcc 0 h := by rwa [uIcc_of_le hh.le]
      have ht' : t ∈ uIcc 0 h := by rwa [uIcc_of_le hh.le]
      calc
        _ = L (U i p t - U i p s) := (L.map_sub _ _).symm
        _ = L (∫ x in s..t, D i p x) := congrArg L ((hP (e i p)).2.2.1 s hs t ht)
        _ = _ := (L.intervalIntegral_comp_comm (hInt.mono_set (uIcc_subset_uIcc hs' ht'))).symm
    obtain ⟨hAC, hDer, _, hEn⟩ := normalizedEdge_sobolev_data hh hLpT hI
    obtain ⟨hAC', hDer', hEn'⟩ := transfer_closedEdgeSobolev
      (f := (fun t => L (U i p t)) ∘ normalizedEdgeParameter h) (g := F)
      (fun t ht => congrArg L (hbRaw i p t ht).symm) hAC hDer
    refine ⟨hAC', hDer', ?_⟩
    have hPoint : (∫ t in Ioo (0 : ℝ) h, ‖L (D i p t)‖ ^ 2) ≤
        K ^ 2 * ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative (e i p) t‖ ^ 2 := by
      rw [← integral_const_mul]
      apply integral_mono_ae (hLpT.integrable_norm_pow (by norm_num))
        (((G.grid.derivative_memLp (e i p)).integrable_norm_pow (by norm_num)).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      change ‖D i p t‖ ^ 2 ≤ K ^ 2 * ‖G.grid.derivative (e i p) t‖ ^ 2
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((hP (e i p)).2.2.2 t (Ioo_subset_Icc_self ht)).2.1 2
    exact hEn'.le.trans (hEn.le.trans
      ((mul_le_mul_of_nonneg_left hPoint (half_pos hh).le).trans_eq (by ring)))
  refine ⟨⟨b, hbRaw, fun i p => ⟨(hData i p).1, (hData i p).2.1⟩, ?_⟩⟩
  simp only [meshSquareEdgeDerivativeEnergy, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun p _ => (hData i p).2.2

/-- A null projected cell boundary supplies the actual inner cap, including
a continuous collar of the physical square perimeter. -/
theorem exists_projectedCellInnerFace_with_collar (a : BulkCoefficients)
    (hAngle : External.SquareBoundaryAngularSobolev) (hTransport : External.UnitSquareDiskSobolevPullback)
    (hCircular : External.PeriodicAngularSobolev) (hP : External.QuaternionSpherePoincare 2 (le_refl 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}
      (G : PenalizedSphereFaces a B h v hv) (f : ↥(cubeBoundarySquares G.grid.level))
      {C : ℝ} (D : ProjectedMeshSquareBoundary G f C),
      let q := squareVacuumBoundaryLoop a D.boundary
      q.Homotopic (ContinuousMap.const NativeCircle (q nativeCircleLoopBase)) →
      ∃ I : ProjectedCellInnerFace G f,
        (∃ U : Set Plane, IsOpen U ∧ (∀ x : UnitSquareBoundary, unitToPhysicalCellFace h x.val ∈ U) ∧
          ContinuousOn I.field U ∧ ∀ i p (x : Domain 1), x 0 ∈ Icc (-1 : ℝ) 1 →
            I.field (unitToPhysicalCellFace h (unitCellFaceSlice i x (if p then 1 else -1))) =
              frobeniusCoordinateEquiv (G.grid.projectedEdge (tensorSquareCoordinateEdge f i p) (unitEdgeToPhysical h x))) ∧
        (∫ x in (tensorGridOpenParameterBox 2 h).val, hsNormSq (I.derivative x)) ≤
          K * C * h * meshSquareEdgeDerivativeEnergy G f := by
  obtain ⟨K, hK, hFill⟩ := exists_physicalSquare_vacuum_fill_of_null_boundary a hAngle hTransport hCircular hP
  refine ⟨K, hK, ?_⟩
  intro B h v hv G f C D q hQ
  have hh := G.ht_pos
  let e (i : Fin 2) (p : Bool) (t : ℝ) :=
    frobeniusCoordinateEquiv (G.grid.projectedEdge (tensorSquareCoordinateEdge f i p) t)
  have hEdge (i : Fin 2) (p : Bool) (t : ℝ) (ht : t ∈ Icc 0 h) :
      e i p t = frobeniusCoordinateEquiv
        (D.boundary (unitSquareSideParameter i p ((t - h / 2) / (h / 2)))).val := by
    have hY : (t - h / 2) / (h / 2) ∈ Icc (-1 : ℝ) 1 := by
      constructor
      · apply (le_div_iff₀ (half_pos hh)).2
        linarith [ht.1]
      · apply (div_le_iff₀ (half_pos hh)).2
        linarith [ht.2]
    have hId : normalizedEdgeParameter h ((t - h / 2) / (h / 2)) = t := by
      unfold normalizedEdgeParameter
      rw [mul_comm, div_mul_cancel₀ _ (half_pos hh).ne', sub_add_cancel]
    exact congrArg frobeniusCoordinateEquiv ((D.edge i p _ hY).trans (congrArg
      (G.grid.projectedEdge (tensorSquareCoordinateEdge f i p)) hId)).symm
  obtain ⟨w, Dw, hw, hVac, ⟨T⟩, hCollar, hE⟩ := hFill h hh D.boundary D.edge_sobolev hQ e hEdge
  let I : ProjectedCellInnerFace G f := ⟨w, Dw, hw, hVac, T⟩
  refine ⟨I, hCollar, hE.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left D.energy hK.le).trans_eq (by ring)

end Thesis
