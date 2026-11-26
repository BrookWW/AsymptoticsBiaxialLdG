module

public import Thesis.Variational.SmoothRegularWallGraphPatch
public import Thesis.Variational.SecondDerivativeCalculus

/-! Small-slope smooth charts preserving the full Lebesgue volume. -/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal NNReal RealInnerProductSpace

namespace Thesis

/-- A wall chart is chosen in its tangent frame so that its slope can be
as small as prescribed on the base of the chart. -/
theorem IsSmoothDomain.exists_graphPatch_small_slope {U : Set Point} (hU : IsSmoothDomain U)
    {a : Point} (ha : a ∈ frontier U) {η : ℝ} (hη : 0 < η) :
    ∃ P : RegularWallGraphPatch U, P.center = a ∧ ContDiff ℝ ∞ P.height ∧
      ∀ y ∈ P.base, ‖fderiv ℝ P.height y‖ ≤ η := by
  obtain ⟨r,φ,ν,s,hr,hφ,hν,hDef,hs,hD,hWall⟩ :=
    exists_local_smooth_defining_function_and_normal_field hU ha
  have hB : a ∈ ball a r := mem_ball_self hr
  have hNormal := hWall a ⟨ha,hB⟩
  have h0 : φ a = 0 := by
    rcases lt_trichotomy (φ a) 0 with hneg|heq|hpos
    · have hIn : a ∈ U ∩ ball a r := hDef.symm ▸ ⟨hneg,hB⟩
      exact (ha.2 (hU.1.1.interior_eq.symm ▸ hIn.1)).elim
    · exact heq
    · have hNear : ∀ᶠ x in 𝓝 a, 0 < φ x :=
        ((isOpen_Ioi.preimage hφ.continuous).mem_nhds hpos)
      have hBall : ∀ᶠ x in 𝓝 a, x ∈ ball a r := isOpen_ball.mem_nhds hB
      have hOut : ∀ᶠ x in 𝓝 a, x ∉ U := by
        filter_upwards [hNear,hBall] with x hx hxB
        intro hIn
        have hneg' : φ x < 0 := (show x ∈ {y | φ y < 0} ∩ ball a r from hDef ▸ ⟨hIn,hxB⟩).1
        exact lt_asymm hx hneg'
      exact ((mem_closure_iff_frequently.mp ha.1) hOut).elim
  have hDer : HasFDerivAt φ (s a • innerSL ℝ (ν a)) a := by
    rw [← hD a]
    exact (hφ.differentiable (by simp) a).hasFDerivAt
  obtain ⟨Q,hQ,hQs,hslope⟩ := exists_regularWallGraphPatch_smooth_of_defining_function
    hNormal.2.1 hr hφ h0 (zero_lt_one.trans_le (hs a)) hDer hDef
  have hC := hQs.continuous_fderiv (by simp)
  have hNear : ∀ᶠ y in 𝓝 (0 : Plane), ‖fderiv ℝ Q.height y‖ < η := by
    apply hC.norm.continuousAt.eventually_lt continuousAt_const
    rw [hslope,norm_zero]
    exact hη
  obtain ⟨b,hb,hL⟩ := Metric.mem_nhds_iff.mp hNear
  let P : RegularWallGraphPatch U :=
    { Q with baseRadius := min b Q.baseRadius
             baseRadius_pos := lt_min hb Q.baseRadius_pos
             mem_domain := fun y hy t ht => Q.mem_domain y (ball_subset_ball (min_le_right _ _) hy) t ht }
  refine ⟨P,hQ,hQs,fun y hy => ?_⟩
  exact (hL (ball_subset_ball (min_le_left _ _) hy)).le

theorem IsSmoothDomain.exists_graphPatch_two_small_slope {U : Set Point} (hU : IsSmoothDomain U)
    {a : Point} (ha : a ∈ frontier U) {η : ℝ} (hη : 0 < η) :
    ∃ P : RegularWallGraphPatch U, P.center = a ∧ ContDiff ℝ 2 P.height ∧
      ∀ y ∈ P.base, ‖fderiv ℝ P.height y‖ ≤ η := by
  obtain ⟨P,hP,hS,hSlope⟩ := hU.exists_graphPatch_small_slope ha hη
  exact ⟨P,hP,hS.of_le (WithTop.coe_le_coe.mpr le_top),hSlope⟩

/-- Orthogonal horizontal coordinates of the flattened variable. -/
def wallHorizontal : Point →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ Plane ℝ).comp planeLinePlacement.symm.toContinuousLinearMap

theorem planeLinePlacement_symm_eq_horizontal_height (z : Point) :
    planeLinePlacement.symm z = (wallHorizontal z,z 2) := by
  apply Prod.ext
  · rfl
  · have h := planeLinePlacement_coordinate (planeLinePlacement.symm z).1 (planeLinePlacement.symm z).2
    have he : planeLinePlacement ((planeLinePlacement.symm z).1,(planeLinePlacement.symm z).2) = z :=
      planeLinePlacement.apply_symm_apply z
    rw [he] at h
    exact h.2.2.symm

theorem wallHorizontal_norm_le (z : Point) : ‖wallHorizontal z‖ ≤ ‖z‖ := by
  have h := planeLinePlacement_coordinate (wallHorizontal z) (z 2)
  have hEq : planeLinePlacement (wallHorizontal z,z 2) = z := by
    rw [← planeLinePlacement_symm_eq_horizontal_height,planeLinePlacement.apply_symm_apply]
  rw [hEq] at h
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two,Fin.sum_univ_three,
    ← h.1,← h.2.1]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem planeLinePlacement_vertical :
    planeLinePlacement ((0 : Plane),(1 : ℝ)) = axis 2 := by
  ext i
  fin_cases i <;> simp [planeLinePlacement_coordinate,axis]

theorem wallHorizontal_vertical : wallHorizontal (axis 2) = 0 := by
  have he :=
    congrArg Prod.fst (planeLinePlacement.symm_apply_apply ((0 : Plane),(1 : ℝ)))
  change wallHorizontal (planeLinePlacement ((0 : Plane),(1 : ℝ))) = 0 at he
  rwa [planeLinePlacement_vertical] at he

/-- Positive and nonnegative half-spaces of the flattened coordinate. -/
def positiveWallHalf : Set Point := {z | 0 < z 2}

def closedWallHalf : Set Point := {z | 0 ≤ z 2}

theorem isOpen_positiveWallHalf : IsOpen positiveWallHalf :=
  isOpen_lt continuous_const ((EuclideanSpace.proj (𝕜 := ℝ) 2).continuous)

namespace RegularWallGraphPatch

variable {U : Set Point}

/-- The wall chart on the ordinary Euclidean three-dimensional space. -/
def flatChart (P : RegularWallGraphPatch U) : Point ≃ₜ Point :=
  planeLinePlacement.symm.toHomeomorph.trans P.chart

/-- A rectangular neighborhood in the exact Euclidean flattened coordinates. -/
def flatBox (P : RegularWallGraphPatch U) : Set Point := planeLinePlacement.symm ⁻¹' P.box

theorem flatBox_isOpen (P : RegularWallGraphPatch U) : IsOpen P.flatBox :=
  (isOpen_ball.prod isOpen_Ioo).preimage planeLinePlacement.symm.continuous

theorem flatChart_image_flatBox (P : RegularWallGraphPatch U) : P.flatChart '' P.flatBox = P.neighborhood := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨planeLinePlacement.symm z,hz,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    refine ⟨planeLinePlacement p,?_,?_⟩
    · change planeLinePlacement.symm (planeLinePlacement p) ∈ P.box
      rwa [planeLinePlacement.symm_apply_apply]
    · change P.chart (planeLinePlacement.symm (planeLinePlacement p)) = P.chart p
      rw [planeLinePlacement.symm_apply_apply]

theorem flatChart_volume (P : RegularWallGraphPatch U) :
    MeasurePreserving P.flatChart (volume : Measure Point) volume := by
  exact P.chart_volume.comp (planeLinePlacement_volume.symm
    planeLinePlacement.toHomeomorph.toMeasurableEquiv)

theorem flatChart_mem_domain (P : RegularWallGraphPatch U) {z : Point} (hz : z ∈ P.flatBox) :
    P.flatChart z ∈ U ↔ 0 < z 2 := by
  let p := planeLinePlacement.symm z
  have hp : p ∈ P.box := hz
  have h := P.mem_domain p.1 hp.1 p.2 hp.2
  change P.chart p ∈ U ↔ _
  rw [show p.2 = z 2 from congrArg Prod.snd (planeLinePlacement_symm_eq_horizontal_height z)] at h
  exact h

theorem flatChart_mem_closure (P : RegularWallGraphPatch U)
    (hU : IsOpen U) {z : Point} (hz : z ∈ P.flatBox) (h : 0 ≤ z 2) :
    P.flatChart z ∈ closure U := by
  apply P.chart_mem_closure_of_nonneg hU hz
  rw [planeLinePlacement_symm_eq_horizontal_height]
  exact h

theorem flatChart_mem_frontier (P : RegularWallGraphPatch U)
    (hU : IsOpen U) {z : Point} (hz : z ∈ P.flatBox) : P.flatChart z ∈ frontier U ↔ z 2 = 0 := by
  exact (P.chart_mem_frontier_iff hU hz).trans
    (congrArg Prod.snd (planeLinePlacement_symm_eq_horizontal_height z) ▸ Iff.rfl)

theorem flatChart_apply (P : RegularWallGraphPatch U) (z : Point) :
    P.flatChart z = P.center + P.frame.repr.symm (z + P.height (wallHorizontal z) • axis 2) := by
  change P.chart (planeLinePlacement.symm z) = _
  rw [planeLinePlacement_symm_eq_horizontal_height,P.chart_apply,P.rigid_apply]
  have he : planeLinePlacement (wallHorizontal z,P.height (wallHorizontal z) + z 2) =
      z + P.height (wallHorizontal z) • axis 2 := by
    have hp : (wallHorizontal z,P.height (wallHorizontal z) + z 2) =
        (wallHorizontal z,z 2) + P.height (wallHorizontal z) • ((0 : Plane),(1 : ℝ)) := by
      simp [add_comm]
    rw [hp,map_add,map_smul,planeLinePlacement_vertical,← planeLinePlacement_symm_eq_horizontal_height,
      planeLinePlacement.apply_symm_apply]
  rw [he]

theorem flatChart_symm_apply (P : RegularWallGraphPatch U) (x : Point) :
    P.flatChart.symm x = P.frame.repr (x-P.center) -
      P.height (wallHorizontal (P.frame.repr (x-P.center))) • axis 2 := by
  let z := P.frame.repr (x-P.center)
  let y := z - P.height (wallHorizontal z) • axis 2
  apply P.flatChart.injective
  rw [P.flatChart.apply_symm_apply,P.flatChart_apply]
  have h : wallHorizontal y = wallHorizontal z := by
    simp only [y,map_sub,map_smul,wallHorizontal_vertical,smul_zero,sub_zero]
  rw [h,show y + P.height (wallHorizontal z) • axis 2 = z from sub_add_cancel _ _]
  unfold z
  rw [P.frame.repr.symm_apply_apply,add_sub_cancel]

theorem flatChart_contDiff (P : RegularWallGraphPatch U) {k : ℕ∞ω} (hP : ContDiff ℝ k P.height) :
    ContDiff ℝ k (P.flatChart : Point → Point) := by
  have h : (P.flatChart : Point → Point) =
      fun z => P.center + P.frame.repr.symm (z + P.height (wallHorizontal z) • axis 2) :=
    funext P.flatChart_apply
  rw [h]
  exact contDiff_const.add (P.frame.repr.symm.contDiff.comp
    (contDiff_id.add ((hP.comp wallHorizontal.contDiff).smul contDiff_const)))

theorem flatChart_symm_contDiff (P : RegularWallGraphPatch U) {k : ℕ∞ω} (hP : ContDiff ℝ k P.height) :
    ContDiff ℝ k (P.flatChart.symm : Point → Point) := by
  have h : (P.flatChart.symm : Point → Point) =
      fun x => P.frame.repr (x-P.center) -
        P.height (wallHorizontal (P.frame.repr (x-P.center))) • axis 2 :=
    funext P.flatChart_symm_apply
  rw [h]
  let f (x : Point) := P.frame.repr (x-P.center)
  have hF : ContDiff ℝ k f := P.frame.repr.contDiff.comp (contDiff_id.sub contDiff_const)
  exact hF.sub (((hP.comp wallHorizontal.contDiff).comp hF).smul contDiff_const)

theorem flatChart_contDiff_two (P : RegularWallGraphPatch U) (hP : ContDiff ℝ 2 P.height) :
    ContDiff ℝ 2 (P.flatChart : Point → Point) := P.flatChart_contDiff hP

theorem flatChart_symm_contDiff_two (P : RegularWallGraphPatch U) (hP : ContDiff ℝ 2 P.height) :
    ContDiff ℝ 2 (P.flatChart.symm : Point → Point) := P.flatChart_symm_contDiff hP

theorem wallHorizontal_rigid_of_flatChart (P : RegularWallGraphPatch U) (x : Point) :
    wallHorizontal (P.frame.repr (P.flatChart x-P.center)) = wallHorizontal x := by
  rw [P.flatChart_apply,add_comm P.center,add_sub_cancel_right,P.frame.repr.apply_symm_apply,
    map_add,map_smul,wallHorizontal_vertical,smul_zero,add_zero]

theorem fderiv_flatChart_symm (P : RegularWallGraphPatch U) (hP : ContDiff ℝ 2 P.height)
    (z v : Point) :
    fderiv ℝ P.flatChart.symm (P.flatChart z) v =
      P.frame.repr v - (fderiv ℝ P.height (wallHorizontal z)) (wallHorizontal (P.frame.repr v)) • axis 2 := by
  let x := P.flatChart z
  let B := P.frame.repr.toContinuousLinearEquiv.toContinuousLinearMap
  let y (p : Point) := B (p-P.center)
  have hB : HasFDerivAt y B x := B.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const P.center)
  have hH := wallHorizontal.hasFDerivAt.comp x hB
  have hG := ((hP.differentiable two_ne_zero (wallHorizontal (y x))).hasFDerivAt.comp x hH).smul_const (axis 2)
  have hFun : (P.flatChart.symm : Point → Point) =
      fun x => y x - P.height (wallHorizontal (y x)) • axis 2 := funext P.flatChart_symm_apply
  have h := (congrArg (fun f : Point → Point => fderiv ℝ f x) hFun).trans (hB.sub hG).fderiv
  have he := DFunLike.congr_fun h v
  change fderiv ℝ P.flatChart.symm (P.flatChart z) v =
    P.frame.repr v - fderiv ℝ P.height (wallHorizontal (P.frame.repr (P.flatChart z-P.center)))
      (wallHorizontal (P.frame.repr v)) • axis 2 at he
  rwa [P.wallHorizontal_rigid_of_flatChart] at he

theorem iteratedFDeriv_two_flatChart_symm (P : RegularWallGraphPatch U) (hP : ContDiff ℝ 2 P.height)
    (z v w : Point) :
    iteratedFDeriv ℝ 2 P.flatChart.symm (P.flatChart z) ![v,w] =
      -(iteratedFDeriv ℝ 2 P.height (wallHorizontal z)
        ![wallHorizontal (P.frame.repr v),wallHorizontal (P.frame.repr w)]) • axis 2 := by
  let B := P.frame.repr.toContinuousLinearEquiv.toContinuousLinearMap
  let y (x : Point) := B (x-P.center)
  let L := wallHorizontal.comp B
  let A (x : Point) := wallHorizontal (y x)
  let g := P.height ∘ A
  let x := P.flatChart z
  have hy : ContDiff ℝ 2 y := B.contDiff.comp (contDiff_id.sub contDiff_const)
  have hA : ContDiff ℝ 2 A := wallHorizontal.contDiff.comp hy
  have hg : ContDiff ℝ 2 g := hP.comp hA
  have hyD : fderiv ℝ y = fun _ => B := funext fun x =>
    (B.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const P.center)).fderiv
  have hAD : fderiv ℝ A = fun _ => L := funext fun x => by
    exact (wallHorizontal.hasFDerivAt.comp x
      (B.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const P.center))).fderiv
  have hy2 : iteratedFDeriv ℝ 2 y x ![v,w] = 0 := by
    rw [iteratedFDeriv_two_apply,hyD]
    simp
  have hA2 : iteratedFDeriv ℝ 2 A x ![v,w] = 0 := by
    rw [iteratedFDeriv_two_apply,hAD]
    simp
  let G (x : Point) := g x • axis 2
  have hG : ContDiff ℝ 2 G := hg.smul contDiff_const
  have hF : (P.flatChart.symm : Point → Point) = y - G :=
    funext P.flatChart_symm_apply
  have hSubtract : iteratedFDeriv ℝ 2 P.flatChart.symm x =
      iteratedFDeriv ℝ 2 y x - iteratedFDeriv ℝ 2 G x :=
    (congrArg (fun f : Point → Point => iteratedFDeriv ℝ 2 f x) hF).trans
      (iteratedFDeriv_sub_apply hy.contDiffAt hG.contDiffAt)
  change iteratedFDeriv ℝ 2 P.flatChart.symm x ![v,w] = _
  rw [hSubtract,sub_apply,hy2,zero_sub]
  have hScale : iteratedFDeriv ℝ 2 G x ![v,w] = (iteratedFDeriv ℝ 2 g x ![v,w]) • axis 2 :=
    DFunLike.congr_fun (iteratedFDeriv_smul_const_apply (v := axis 2) hg.contDiffAt) ![v,w]
  rw [hScale]
  have hChain := iteratedFDeriv_two_comp_apply_of_contDiffAt (x := x) hP.contDiffAt hA.contDiffAt v w
  change iteratedFDeriv ℝ 2 g x ![v,w] = _ at hChain
  rw [hA2,map_zero,add_zero,hAD] at hChain
  rw [hChain]
  change -((iteratedFDeriv ℝ 2 P.height (wallHorizontal (P.frame.repr (P.flatChart z-P.center)))
    ![wallHorizontal (P.frame.repr v),wallHorizontal (P.frame.repr w)]) • axis 2) = _
  rw [P.wallHorizontal_rigid_of_flatChart,neg_smul]

end RegularWallGraphPatch

end Thesis
