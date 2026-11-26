module

public import Thesis.Variational.RegularWallGraphPatch

/-! The oriented graph normal and its area-weighted coordinate flux. -/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal NNReal RealInnerProductSpace

namespace Thesis.RegularWallGraphPatch

variable {U : Set Point}

/-- The linear part of the actual orthonormal frame. -/
def physicalLinear (P : RegularWallGraphPatch U) : (Plane × ℝ) ≃L[ℝ] Point :=
  planeLinePlacement.trans P.frame.repr.symm.toContinuousLinearEquiv

/-- The physical wall represented by its horizontal coordinates. -/
def wallPoint (P : RegularWallGraphPatch U) (y : Plane) : Point := P.chart (y,0)

theorem chart_eq_center_add (P : RegularWallGraphPatch U) (y : Plane) (t : ℝ) :
    P.chart (y,t) = P.center + P.physicalLinear (y,P.height y + t) := rfl

theorem image_wallPoint_eq (P : RegularWallGraphPatch U) (hU : IsOpen U) :
    P.wallPoint '' P.base = frontier U ∩ P.neighborhood := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    have hp : (y,(0:ℝ)) ∈ P.box := ⟨hy, neg_neg_of_pos P.halfHeight_pos, P.halfHeight_pos⟩
    exact ⟨(P.chart_mem_frontier_iff hU hp).2 rfl,⟨(y,0), hp, rfl⟩⟩
  · rintro ⟨hxF,hxN⟩
    obtain ⟨p,hp,rfl⟩ := hxN
    have hp0 := (P.chart_mem_frontier_iff hU hp).1 hxF
    exact ⟨p.1,hp.1,by change P.chart (p.1,0) = P.chart p; rw [← hp0]⟩

/-- The pulled-back defining function has the outward sign in the graph frame. -/
def graphDefining (P : RegularWallGraphPatch U) (x : Point) : ℝ :=
  let q := P.physicalLinear.symm (x - P.center)
  P.height q.1 - q.2

theorem graphDefining_contDiff (P : RegularWallGraphPatch U) : ContDiff ℝ 1 P.graphDefining := by
  let T (x : Point) := P.physicalLinear.symm (x - P.center)
  have hC : ContDiff ℝ 1 T := P.physicalLinear.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  exact (P.height_smooth.comp hC.fst).sub hC.snd

theorem graphDefining_chart (P : RegularWallGraphPatch U) (y : Plane) (t : ℝ) :
    P.graphDefining (P.chart (y,t)) = -t := by
  rw [P.chart_eq_center_add]
  have hE : P.physicalLinear.symm
      (P.center + P.physicalLinear (y,P.height y + t) - P.center) = (y,P.height y + t) := by
    rw [add_comm P.center, add_sub_cancel_right, P.physicalLinear.symm_apply_apply]
  unfold graphDefining
  rw [hE]
  exact sub_add_cancel_left (P.height y) t

/-- The physical graph normal before normalization by the area density. -/
def graphNormalVector (P : RegularWallGraphPatch U) (y : Plane) : Point :=
  P.frame.repr.symm (planeLinePlacement
    (WithLp.toLp 2 ![fderiv ℝ P.height y (EuclideanSpace.single 0 1),
      fderiv ℝ P.height y (EuclideanSpace.single 1 1)], -1))

theorem norm_graphNormalVector (P : RegularWallGraphPatch U) (y : Plane) :
    ‖P.graphNormalVector y‖ = wallGraphAreaDensity P.height y := by
  unfold graphNormalVector wallGraphAreaDensity
  rw [P.frame.repr.symm.norm_map]
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt (by positivity), EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have h := planeLinePlacement_coordinate
    (WithLp.toLp 2 ![fderiv ℝ P.height y (EuclideanSpace.single 0 1),
      fderiv ℝ P.height y (EuclideanSpace.single 1 1)]) (-1)
  rw [h.1,h.2.1,h.2.2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem planeLinear_apply_eq (G : Plane →L[ℝ] ℝ) (z : Plane) :
    G z = G (EuclideanSpace.single 0 1) * z 0 + G (EuclideanSpace.single 1 1) * z 1 := by
  let B := EuclideanSpace.basisFun (Fin 2) ℝ
  have hRep : (∑ k : Fin 2, z k • EuclideanSpace.single k 1) = z := by
    simpa only [B, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
      using B.sum_repr z
  calc
    _ = G (∑ k : Fin 2, z k • EuclideanSpace.single k 1) := congrArg G hRep.symm
    _ = _ := by
      rw [Fin.sum_univ_two, G.map_add, G.map_smul, G.map_smul]
      simp only [smul_eq_mul]
      ring

theorem inner_graphNormalVector (P : RegularWallGraphPatch U) (y : Plane) (v : Point) :
    inner ℝ (P.graphNormalVector y) v =
      (fderiv ℝ P.height y) (P.physicalLinear.symm v).1 - (P.physicalLinear.symm v).2 := by
  let q := P.physicalLinear.symm v
  let d := fderiv ℝ P.height y
  let w : Plane := WithLp.toLp 2 ![d (EuclideanSpace.single 0 1), d (EuclideanSpace.single 1 1)]
  have hV : P.frame.repr v = planeLinePlacement q := by
    have hEq : P.physicalLinear q = v := P.physicalLinear.apply_symm_apply v
    have hEq' : P.frame.repr.symm (planeLinePlacement q) = v := hEq
    exact (congrArg P.frame.repr hEq').symm.trans (P.frame.repr.apply_symm_apply _)
  have hW := planeLinePlacement_coordinate w (-1)
  have hQ := planeLinePlacement_coordinate q.1 q.2
  calc
    _ = inner ℝ (planeLinePlacement (w,-1)) (P.frame.repr v) := by
      rw [← P.frame.repr.inner_map_map (P.graphNormalVector y) v]
      change inner ℝ (P.frame.repr (P.frame.repr.symm (planeLinePlacement (w,-1)))) (P.frame.repr v) = _
      rw [P.frame.repr.apply_symm_apply]
    _ = _ := by
      rw [hV, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
      change (planeLinePlacement q) 0 * star ((planeLinePlacement (w,-1)) 0) +
        (planeLinePlacement q) 1 * star ((planeLinePlacement (w,-1)) 1) +
        (planeLinePlacement q) 2 * star ((planeLinePlacement (w,-1)) 2) = d q.1 - q.2
      have hQ0 : (planeLinePlacement q) 0 = q.1 0 := hQ.1
      have hQ1 : (planeLinePlacement q) 1 = q.1 1 := hQ.2.1
      have hQ2 : (planeLinePlacement q) 2 = q.2 := hQ.2.2
      rw [hW.1,hW.2.1,hW.2.2,hQ0,hQ1,hQ2,planeLinear_apply_eq]
      simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one, star_trivial]
      ring

/-- The given orientation is outward for the epigraph. -/
def graphUnitNormal (P : RegularWallGraphPatch U) (y : Plane) : Point :=
  (wallGraphAreaDensity P.height y)⁻¹ • P.graphNormalVector y

theorem norm_graphUnitNormal (P : RegularWallGraphPatch U) (y : Plane) :
    ‖P.graphUnitNormal y‖ = 1 := by
  have h := wallGraph_areaDensity_pos P.height y
  rw [graphUnitNormal, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr h.le), norm_graphNormalVector,
    inv_mul_cancel₀ h.ne']

theorem area_mul_inner_graphUnitNormal (P : RegularWallGraphPatch U) (y : Plane) (v : Point) :
    wallGraphAreaDensity P.height y * inner ℝ (P.graphUnitNormal y) v =
      (fderiv ℝ P.height y) (P.physicalLinear.symm v).1 - (P.physicalLinear.symm v).2 := by
  rw [graphUnitNormal, real_inner_smul_left, ← mul_assoc,
    mul_inv_cancel₀ (wallGraph_areaDensity_pos P.height y).ne', one_mul, inner_graphNormalVector]

theorem hasFDerivAt_graphDefining_wall (P : RegularWallGraphPatch U) (y : Plane) :
    HasFDerivAt P.graphDefining
      (wallGraphAreaDensity P.height y • innerSL ℝ (P.graphUnitNormal y)) (P.wallPoint y) := by
  let T (x : Point) := P.physicalLinear.symm (x - P.center)
  let x := P.wallPoint y
  have hX : T x = (y,P.height y) := by
    change P.physicalLinear.symm (P.chart (y,0) - P.center) = _
    rw [P.chart_eq_center_add, add_zero, add_comm P.center, add_sub_cancel_right,
      P.physicalLinear.symm_apply_apply]
  have hT : HasFDerivAt T P.physicalLinear.symm.toContinuousLinearMap x :=
    P.physicalLinear.symm.toContinuousLinearMap.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const P.center)
  let A : Point →L[ℝ] Plane := (ContinuousLinearMap.fst ℝ Plane ℝ).comp P.physicalLinear.symm.toContinuousLinearMap
  let B : Point →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ Plane ℝ).comp P.physicalLinear.symm.toContinuousLinearMap
  have hTD : HasFDerivAt (fun p => (T p).1) A x :=
    (ContinuousLinearMap.fst ℝ Plane ℝ).hasFDerivAt.comp x hT
  have hTE : HasFDerivAt (fun p => (T p).2) B x :=
    (ContinuousLinearMap.snd ℝ Plane ℝ).hasFDerivAt.comp x hT
  have hH := ((P.height_smooth.differentiable one_ne_zero (T x).1).hasFDerivAt.comp x hTD).sub hTE
  have hDeq : ((fderiv ℝ P.height (T x).1).comp A) - B =
      wallGraphAreaDensity P.height y • innerSL ℝ (P.graphUnitNormal y) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [sub_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
    rw [P.area_mul_inner_graphUnitNormal, hX]
    rfl
  exact hDeq ▸ hH

theorem hasRegularOutwardNormalAt_graph (P : RegularWallGraphPatch U) (hU : IsOpen U)
    {y : Plane} (hy : y ∈ P.base) : HasRegularOutwardNormalAt U (P.wallPoint y) (P.graphUnitNormal y) := by
  let x := P.wallPoint y
  have hp : (y,(0:ℝ)) ∈ P.box := ⟨hy,neg_neg_of_pos P.halfHeight_pos, P.halfHeight_pos⟩
  have hF : x ∈ frontier U := (P.chart_mem_frontier_iff hU hp).2 rfl
  have hx : x ∈ P.neighborhood := ⟨(y,0),hp,rfl⟩
  obtain ⟨r,hr,hR⟩ := Metric.mem_nhds_iff.mp (P.isOpen_neighborhood.mem_nhds hx)
  refine ⟨hF,P.norm_graphUnitNormal y,r,P.graphDefining, wallGraphAreaDensity P.height y,
    hr,P.graphDefining_contDiff.contDiffOn,?_,wallGraph_areaDensity_pos P.height y,
    P.hasFDerivAt_graphDefining_wall y,?_⟩
  · change P.graphDefining (P.chart (y,0)) = 0
    rw [P.graphDefining_chart, neg_zero]
  · ext z
    simp only [mem_inter_iff, mem_setOf_eq]
    have hZ (hz : z ∈ ball x r) : z ∈ U ↔ P.graphDefining z < 0 := by
      obtain ⟨q,hq,rfl⟩ := hR hz
      change P.chart (q.1,q.2) ∈ U ↔ P.graphDefining (P.chart (q.1,q.2)) < 0
      rw [P.graphDefining_chart q.1 q.2, neg_lt_zero]
      exact P.mem_domain _ hq.1 _ hq.2
    exact ⟨fun hz => ⟨(hZ hz.2).1 hz.1,hz.2⟩, fun hz => ⟨(hZ hz.2).2 hz.1,hz.2⟩⟩

theorem chart_hasFDerivAt (P : RegularWallGraphPatch U) (p : Plane × ℝ) :
    let T : Plane × ℝ →L[ℝ] (Plane × ℝ) :=
      (ContinuousLinearMap.fst ℝ Plane ℝ).prod
        ((fderiv ℝ P.height p.1).comp (ContinuousLinearMap.fst ℝ Plane ℝ) +
          ContinuousLinearMap.snd ℝ Plane ℝ)
    HasFDerivAt P.chart (P.physicalLinear.toContinuousLinearMap.comp T) p := by
  let F (q : Plane × ℝ) := (q.1, P.height q.1 + q.2)
  have hH := ((P.height_smooth.differentiable one_ne_zero p.1).hasFDerivAt.comp p
    (ContinuousLinearMap.fst ℝ Plane ℝ).hasFDerivAt).add
      (ContinuousLinearMap.snd ℝ Plane ℝ).hasFDerivAt
  have hF := (ContinuousLinearMap.fst ℝ Plane ℝ).hasFDerivAt.prodMk hH
  exact (P.physicalLinear.toContinuousLinearMap.hasFDerivAt.comp p hF).const_add P.center

/-- The actual chart derivative sends the compensated coordinate direction
to its original physical vector. -/
theorem fderiv_chart_compensated (P : RegularWallGraphPatch U) (p : Plane × ℝ)
    (q : Plane × ℝ) : (fderiv ℝ P.chart p) (q.1, q.2 - fderiv ℝ P.height p.1 q.1) =
      P.physicalLinear q := by
  rw [(P.chart_hasFDerivAt p).fderiv, ContinuousLinearMap.comp_apply]
  apply congrArg P.physicalLinear
  apply Prod.ext
  · rfl
  · change fderiv ℝ P.height p.1 q.1 + (q.2 - fderiv ℝ P.height p.1 q.1) = q.2
    ring

end Thesis.RegularWallGraphPatch
