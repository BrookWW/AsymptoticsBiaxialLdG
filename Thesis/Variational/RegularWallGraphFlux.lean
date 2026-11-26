module

public import Thesis.Variational.RegularWallGraphNormal
import Thesis.Variational.HalfSpaceFlux
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Gauss–Green for a test supported in one actual regular wall chart. -/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal RealInnerProductSpace

namespace Thesis.RegularWallGraphPatch

variable {U : Set Point}

private theorem not_mem_neighborhood_of_chart_not_mem_box (P : RegularWallGraphPatch U)
    {p : Plane × ℝ} (hp : p ∉ P.box) : P.chart p ∉ P.neighborhood := by
  rintro ⟨q,hq,heq⟩
  exact hp (P.chart.injective heq ▸ hq)

private theorem chart_pullback_compact_support (P : RegularWallGraphPatch U)
    {g : Point → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (g ∘ P.chart) := by
  have hK : IsCompact (P.chart.symm '' tsupport g) := hg.image P.chart.symm.continuous
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro p hp
  exact ⟨P.chart p, subset_closure hp, P.chart.symm_apply_apply p⟩

private theorem chart_pullback_contDiffOn_half (P : RegularWallGraphPatch U) (hU : IsOpen U)
    {g : Point → ℝ} (hg : ContDiffOn ℝ 1 g (closure U)) (hs : tsupport g ⊆ P.neighborhood) :
    ContDiffOn ℝ 1 (g ∘ P.chart) flatClosedHalf := by
  intro p hp
  by_cases hpB : p ∈ P.box
  · apply (contDiffWithinAt_inter ((isOpen_ball.prod isOpen_Ioo).mem_nhds hpB)).1
    have hMaps : MapsTo P.chart (flatClosedHalf ∩ P.box) (closure U) :=
      fun q hq => P.chart_mem_closure_of_nonneg hU hq.2 hq.1.2
    exact (hg.comp P.chart_smooth.contDiffOn hMaps) p ⟨hp,hpB⟩
  · have hN : ∀ᶠ x in 𝓝 (P.chart p), x ∉ tsupport g :=
      (isClosed_tsupport g).isOpen_compl.mem_nhds
        (fun h => P.not_mem_neighborhood_of_chart_not_mem_box hpB (hs h))
    have hE : g ∘ P.chart =ᶠ[𝓝 p] (0 : Plane × ℝ → ℝ) := by
      have hN' : ∀ᶠ q in 𝓝 p, P.chart q ∉ tsupport g := P.chart.continuous.continuousAt hN
      exact hN'.mono fun q h => show g (P.chart q) = 0 from image_eq_zero_of_notMem_tsupport h
    exact (contDiffAt_const.congr_of_eventuallyEq hE).contDiffWithinAt

private theorem chart_derivative_integral_eq (P : RegularWallGraphPatch U) (hU : IsOpen U)
    {g : Point → ℝ} (hg : ContDiffOn ℝ 1 g (closure U))
    (hCap : HasCompactSupport g) (hs : tsupport g ⊆ P.neighborhood) (j : Fin 3) :
    (∫ x in U, coordDeriv j g x) =
      ∫ y, ((fderiv ℝ P.height y) (P.physicalLinear.symm (axis j)).1 -
        (P.physicalLinear.symm (axis j)).2) * g (P.wallPoint y) := by
  let G := g ∘ P.chart
  let q := P.physicalLinear.symm (axis j)
  let w (y : Plane) := q.2 - fderiv ℝ P.height y q.1
  have hG : ContDiffOn ℝ 1 G flatClosedHalf := P.chart_pullback_contDiffOn_half hU hg hs
  have hGS : HasCompactSupport G := P.chart_pullback_compact_support hCap
  have hw : Continuous w :=
    continuous_const.sub ((P.height_smooth.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hI (p : Plane × ℝ) : U.indicator (coordDeriv j g) (P.chart p) =
      flatOpenHalf.indicator (fun p => coordDeriv j g (P.chart p)) p := by
    by_cases hpB : p ∈ P.box
    · have hEq : P.chart p ∈ U ↔ p ∈ flatOpenHalf := by
        change P.chart (p.1,p.2) ∈ U ↔ p ∈ flatOpenHalf
        exact (P.mem_domain _ hpB.1 _ hpB.2).trans (by simp [flatOpenHalf])
      by_cases hh : P.chart p ∈ U
      · rw [indicator_of_mem hh, indicator_of_mem (hEq.mp hh)]
      · rw [indicator_of_notMem hh, indicator_of_notMem (fun h => hh (hEq.mpr h))]
    · have hZero : coordDeriv j g (P.chart p) = 0 := by
        unfold coordDeriv
        rw [fderiv_of_notMem_tsupport ℝ (fun h => P.not_mem_neighborhood_of_chart_not_mem_box hpB (hs h)),
          zero_apply]
      by_cases hPhys : P.chart p ∈ U <;> by_cases hFlat : p ∈ flatOpenHalf <;> simp [hPhys,hFlat,hZero]
  have hVol :
      (∫ x in U, coordDeriv j g x) = ∫ p in flatOpenHalf, coordDeriv j g (P.chart p) := by
    rw [← integral_indicator hU.measurableSet,
      ← P.chart_volume.integral_comp P.chart.isClosedEmbedding.measurableEmbedding,
      ← integral_indicator ((isOpen_univ.prod isOpen_Ioi).measurableSet)]
    exact integral_congr_ae (Eventually.of_forall hI)
  have hDirection (p : Plane × ℝ) (hp : p ∈ flatOpenHalf) :
      coordDeriv j g (P.chart p) = (fderiv ℝ G p) (q.1,0) + w p.1 * (fderiv ℝ G p) (0,1) := by
    by_cases hpB : p ∈ P.box
    · have hX : P.chart p ∈ U := (P.mem_domain _ hpB.1 _ hpB.2).mpr hp.2
      have hC := ((hg _ (subset_closure hX)).contDiffAt
        (mem_of_superset (hU.mem_nhds hX) subset_closure)).differentiableAt one_ne_zero
      have hComp : fderiv ℝ G p =
          (fderiv ℝ g (P.chart p)).comp (fderiv ℝ P.chart p) :=
        (hC.hasFDerivAt.comp p
          ((P.chart_smooth.differentiable one_ne_zero p).hasFDerivAt)).fderiv
      have hCoord : (fderiv ℝ G p) (q.1,w p.1) = coordDeriv j g (P.chart p) := by
        rw [hComp, ContinuousLinearMap.comp_apply]
        have hDer : (fderiv ℝ P.chart p) (q.1,w p.1) = axis j :=
          (P.fderiv_chart_compensated p q).trans (P.physicalLinear.apply_symm_apply _)
        rw [hDer]
        rfl
      rw [← hCoord, show ((q.1,w p.1) : Plane × ℝ) =
        (q.1,0) + w p.1 • ((0 : Plane),(1 : ℝ)) by simp,
        map_add, map_smul, smul_eq_mul]
    · have hN : P.chart p ∉ tsupport g := fun h =>
        P.not_mem_neighborhood_of_chart_not_mem_box hpB (hs h)
      have hNG : p ∉ tsupport G := by
        apply notMem_tsupport_iff_eventuallyEq.mpr
        have hh := P.chart.continuous.continuousAt
          (notMem_tsupport_iff_eventuallyEq.1 hN)
        exact hh
      rw [coordDeriv, fderiv_of_notMem_tsupport ℝ hN, fderiv_of_notMem_tsupport ℝ hNG]
      simp
  have hL := integrableOn_flat_derivative hG hGS (u := fun _ => (q.1,0)) continuous_const
  have hR := integrableOn_flat_derivative hG hGS (u := fun p => (0,w p.1))
    (continuous_const.prodMk (hw.comp continuous_fst))
  have hRw (p : Plane × ℝ) : (fderiv ℝ G p) (0,w p.1) = w p.1 * (fderiv ℝ G p) (0,1) := by
    rw [show ((0 : Plane),w p.1) = w p.1 • ((0 : Plane),(1 : ℝ)) by simp, map_smul, smul_eq_mul]
  simp_rw [hRw] at hR
  rw [hVol, setIntegral_congr_fun ((isOpen_univ.prod isOpen_Ioi).measurableSet) hDirection,
    integral_add hL hR, integral_flat_horizontal_derivative hG hGS,
    zero_add, integral_flat_vertical_derivative hG hGS hw, ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change -(w y * G (y,0)) =
      (fderiv ℝ P.height y q.1 - q.2) * g (P.wallPoint y)
    rw [← neg_mul]
    have hW : -(w y) = fderiv ℝ P.height y q.1 - q.2 := neg_sub _ _
    rw [hW]
    rfl

private theorem graphUnitNormal_continuous (P : RegularWallGraphPatch U) : Continuous P.graphUnitNormal := by
  have hd := P.height_smooth.continuous_fderiv one_ne_zero
  have h0 : Continuous (fun y => fderiv ℝ P.height y (EuclideanSpace.single 0 1)) :=
    hd.clm_apply continuous_const
  have h1 : Continuous (fun y => fderiv ℝ P.height y (EuclideanSpace.single 1 1)) :=
    hd.clm_apply continuous_const
  have hW : Continuous (fun y : Plane => WithLp.toLp 2
      ![fderiv ℝ P.height y (EuclideanSpace.single 0 1),fderiv ℝ P.height y (EuclideanSpace.single 1 1)]) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (continuous_pi fun i => by
      fin_cases i
      · exact h0
      · exact h1)
  have hVec : Continuous P.graphNormalVector :=
    P.frame.repr.symm.continuous.comp (planeLinePlacement.continuous.comp (hW.prodMk continuous_const))
  have hArea : Continuous (wallGraphAreaDensity P.height) := by
    unfold wallGraphAreaDensity
    exact ((continuous_const.add (h0.pow 2)).add (h1.pow 2)).sqrt
  exact (hArea.inv₀ (fun y => (wallGraph_areaDensity_pos P.height y).ne')).smul hVec

private theorem graph_boundary_integral_eq (P : RegularWallGraphPatch U) {ν : Point → Point}
    (hU : IsOpen U) (hν : ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure 2).restrict (frontier U),
      HasRegularOutwardNormalAt U x (ν x))
    {g : Point → ℝ} (hg : ContinuousOn g (closure U)) (hs : tsupport g ⊆ P.neighborhood)
    (j : Fin 3) :
    (∫ x in frontier U, g x * ν x j ∂(Measure.euclideanHausdorffMeasure 2)) =
      ∫ y, ((fderiv ℝ P.height y) (P.physicalLinear.symm (axis j)).1 -
        (P.physicalLinear.symm (axis j)).2) * g (P.wallPoint y) := by
  let μ : Measure Point := Measure.euclideanHausdorffMeasure 2
  let S := frontier U ∩ P.neighborhood
  let n (x : Point) := P.graphUnitNormal (P.chart.symm x).1
  have hS : MeasurableSet S := isClosed_frontier.measurableSet.inter P.isOpen_neighborhood.measurableSet
  have hnC : Continuous n := (graphUnitNormal_continuous P).comp P.chart.symm.continuous.fst
  have hRestricted :
      (∫ x in S, g x * ν x j ∂μ) = ∫ x in frontier U, g x * ν x j ∂μ := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero isClosed_frontier.measurableSet inter_subset_left
    intro x hx
    have h0 : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx.2 ⟨hx.1,hs h⟩)
    rw [h0,zero_mul]
  have hn : ∀ᵐ x ∂μ.restrict S, ν x = n x := by
    filter_upwards [hν.filter_mono (ae_mono (Measure.restrict_mono_set μ inter_subset_left)),
      ae_restrict_mem hS] with x hx hxS
    have hxI : x ∈ P.wallPoint '' P.base := (P.image_wallPoint_eq hU).symm ▸ hxS
    obtain ⟨y,hy,rfl⟩ := hxI
    have hE : n (P.wallPoint y) = P.graphUnitNormal y := by
      change P.graphUnitNormal (P.chart.symm (P.chart (y,0))).1 = _
      rw [P.chart.symm_apply_apply]
    exact (hx.unique (P.hasRegularOutwardNormalAt_graph hU hy)).trans hE.symm
  rw [← hRestricted, integral_congr_ae (hn.mono fun _ h => by rw [h])]
  let E := P.frame.repr.symm.toHomeomorph.trans (Homeomorph.addLeft P.center)
  have hIso : Isometry (E : Point → Point) := Isometry.of_dist_eq fun x y => by
    change dist (P.center + P.frame.repr.symm x) (P.center + P.frame.repr.symm y) = dist x y
    rw [dist_add_left, P.frame.repr.symm.isometry.dist_eq]
  let EI : Point ≃ᵢ Point := ⟨E.toEquiv,hIso⟩
  have hVol : MeasurePreserving E μ μ := EI.measurePreserving_euclideanHausdorffMeasure 2
  let T := wallGraph P.height '' P.base
  have hET : E '' T = S := by
    have hE (y : Plane) : E (wallGraph P.height y) = P.wallPoint y := by
      change P.center + P.frame.repr.symm (planeLinePlacement (y,P.height y)) = P.chart (y,0)
      rw [P.chart_eq_center_add,add_zero]
      rfl
    change E '' T = frontier U ∩ P.neighborhood
    rw [← P.image_wallPoint_eq hU]
    change E '' (wallGraph P.height '' P.base) = P.wallPoint '' P.base
    rw [image_image]
    exact congrArg (fun f : Plane → Point => f '' P.base) (funext hE)
  let F (z : Point) := g (E z) * n (E z) j
  have hTo : MapsTo E T (closure U) := by
    intro z hz
    have h := mem_image_of_mem E hz
    rw [hET] at h
    exact frontier_subset_closure h.1
  have hC : ContinuousOn F T :=
    (hg.comp E.continuous.continuousOn hTo).mul
      (((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp (hnC.comp E.continuous)).continuousOn)
  have hT : MeasurableSet T :=
    wallGraph_image_measurable isOpen_ball measurableSet_ball subset_rfl P.height_smooth.continuous.continuousOn
  rw [← hET, hVol.setIntegral_image_emb E.isClosedEmbedding.measurableEmbedding]
  change (∫ x in T, F x ∂μ) = _
  rw [integral_wallGraph isOpen_ball P.height_smooth.contDiffOn
    P.height_smooth.continuous.measurable (hC.aestronglyMeasurable hT)]
  have hPoint (y : Plane) : E (wallGraph P.height y) = P.wallPoint y := by
    change P.center + P.frame.repr.symm (planeLinePlacement (y,P.height y)) = P.chart (y,0)
    rw [P.chart_eq_center_add,add_zero]
    rfl
  let B (y : Plane) := ((fderiv ℝ P.height y) (P.physicalLinear.symm (axis j)).1 -
    (P.physicalLinear.symm (axis j)).2) * g (P.wallPoint y)
  calc
    _ = ∫ y in P.base, B y := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y _
      change wallGraphAreaDensity P.height y * (g (E (wallGraph P.height y)) * n (E (wallGraph P.height y)) j) = _
      rw [hPoint]
      have hnEq : n (P.wallPoint y) = P.graphUnitNormal y := by
        change P.graphUnitNormal (P.chart.symm (P.chart (y,0))).1 = _
        rw [P.chart.symm_apply_apply]
      rw [hnEq]
      have hInner : inner ℝ (P.graphUnitNormal y) (axis j) = P.graphUnitNormal y j := by
        rw [axis, EuclideanSpace.inner_single_right]
        simp
      rw [← hInner]
      unfold B
      rw [← P.area_mul_inner_graphUnitNormal]
      ring
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hB : (y,(0 : ℝ)) ∉ P.box := fun h => hy h.1
      have hSup : P.wallPoint y ∉ tsupport g := fun h =>
        P.not_mem_neighborhood_of_chart_not_mem_box hB (hs h)
      unfold B
      rw [image_eq_zero_of_notMem_tsupport hSup,mul_zero]

/-- The actual coordinate divergence and boundary flux agree for a classical
field whose support lies in a single regular graph neighborhood. -/
theorem gaussGreen_supported_graph (P : RegularWallGraphPatch U) {ν : Point → Point}
    (hU : IsOpen U) (hν : ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure 2).restrict (frontier U),
      HasRegularOutwardNormalAt U x (ν x))
    {g : Point → ℝ} (hg : ContDiffOn ℝ 1 g (closure U)) (hCap : HasCompactSupport g)
    (hs : tsupport g ⊆ P.neighborhood) (j : Fin 3) :
    (∫ x in U, coordDeriv j g x) =
      ∫ x in frontier U, g x * ν x j ∂(Measure.euclideanHausdorffMeasure 2) :=
  (P.chart_derivative_integral_eq hU hg hCap hs j).trans
    (P.graph_boundary_integral_eq hU hν hg.continuousOn hs j).symm

end Thesis.RegularWallGraphPatch
