module

public import Thesis.MeasureGeometry.PlanarCurveArea
public import Thesis.MeasureGeometry.PlanarCoareaJacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! Scalar coarea in a regular planar coordinate chart. -/

public section

open Filter Function MeasureTheory Metric Set Topology ContinuousLinearMap
open scoped ContDiff ENNReal NNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

private def levelPairEquiv : Plane ≃L[ℝ] ℝ × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

private def levelPairMeasurableEquiv : Plane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

private theorem levelPairEquiv_measurePreserving : MeasurePreserving levelPairMeasurableEquiv :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

private theorem levelPairEquiv_coordinates (z : Plane) :
    levelPairEquiv z = (z 0,z 1) := rfl

private theorem levelPairEquiv_symm_coordinates (t s : ℝ) :
    levelPairEquiv.symm (t,s) = WithLp.toLp 2 ![t,s] := rfl

private def levelChartMap (j : Fin 2) (f : Plane → ℝ) (z : Plane) : Plane :=
  levelPairEquiv.symm (f z,z j)

private def levelChartDerivative (j : Fin 2) (D : Plane →L[ℝ] ℝ) : Plane →L[ℝ] Plane :=
  levelPairEquiv.symm.toContinuousLinearMap.comp (D.prod (EuclideanSpace.proj j))

private theorem levelChartDerivative_coordinates (j : Fin 2) (D : Plane →L[ℝ] ℝ) (v : Plane) :
    (levelChartDerivative j D v) 0 = D v ∧ (levelChartDerivative j D v) 1 = v j :=
  ⟨rfl,rfl⟩

private theorem contDiffOn_levelChartMap {U : Set Plane} (j : Fin 2) {f : Plane → ℝ}
    (hf : ContDiffOn ℝ 1 f U) :
    ContDiffOn ℝ 1 (levelChartMap j f) U := by
  have hProj : ContDiffOn ℝ 1 (fun z : Plane => z j) U :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffOn
  exact levelPairEquiv.symm.contDiff.comp_contDiffOn (hf.prodMk hProj)

private theorem hasFDerivAt_levelChartMap (j : Fin 2) {f : Plane → ℝ} {z : Plane}
    (hf : DifferentiableAt ℝ f z) :
    HasFDerivAt (levelChartMap j f) (levelChartDerivative j (fderiv ℝ f z)) z := by
  let π : Plane →L[ℝ] ℝ := EuclideanSpace.proj j
  have hProj : HasFDerivAt (fun y : Plane => y j) π z := π.hasFDerivAt
  exact levelPairEquiv.symm.toContinuousLinearMap.hasFDerivAt.comp z (hf.hasFDerivAt.prodMk hProj)

private def levelChartEquivOfDetNeZero (C : Plane →L[ℝ] Plane) (hC : C.det ≠ 0) : Plane ≃L[ℝ] Plane :=
  (C.toLinearMap.equivOfDetNeZero hC).toContinuousLinearEquiv

private theorem levelChartEquivOfDetNeZero_coe (C : Plane →L[ℝ] Plane) (hC : C.det ≠ 0) :
    (levelChartEquivOfDetNeZero C hC : Plane →L[ℝ] Plane) = C := by
  apply ContinuousLinearMap.ext
  intro x
  change (C.toLinearMap.equivOfDetNeZero hC) x = C x
  unfold LinearMap.equivOfDetNeZero
  exact DFunLike.congr_fun (LinearEquiv.coe_ofIsUnitDet (f := C.toLinearMap) _) x

private theorem continuousOn_levelChartDerivative {U : Set Plane} (hU : IsOpen U)
    (j : Fin 2) {f : Plane → ℝ} (hf : ContDiffOn ℝ 1 f U) :
    ContinuousOn (fun z => levelChartDerivative j (fderiv ℝ f z)) U := by
  have hD := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  let Pj : Plane →L[ℝ] ℝ := EuclideanSpace.proj j
  let I₁ : ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.inl ℝ ℝ ℝ
  let I₂ : ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.inr ℝ ℝ ℝ
  have hE : (fun z => (fderiv ℝ f z).prod Pj) =
      (fun z => I₁.comp (fderiv ℝ f z) + I₂.comp Pj) := by
    funext z
    ext v <;> simp [I₁,I₂]
  have hPair : ContinuousOn (fun z => (fderiv ℝ f z).prod Pj) U := by
    rw [hE]
    exact (continuousOn_const.clm_comp hD).add continuousOn_const
  exact continuousOn_const.clm_comp hPair

private structure PlanarLevelChart (U : Set Plane) (f : Plane → ℝ) (x : Plane) where
  coordinate : Fin 2
  equiv : OpenPartialHomeomorph Plane Plane
  center_mem : x ∈ equiv.source
  source_subset : equiv.source ⊆ U
  forward_eq : (equiv : Plane → Plane) = levelChartMap coordinate f
  inverse_smooth : ContDiffOn ℝ 1 equiv.symm equiv.target
  forward_derivative : ∀ y ∈ equiv.source,
    HasFDerivAt equiv (levelChartDerivative coordinate (fderiv ℝ f y)) y

private theorem exists_planarLevelChart
    {U : Set Plane} (hU : IsOpen U) {f : Plane → ℝ} (hf : ContDiffOn ℝ 1 f U)
    {x : Plane} (hx : x ∈ U) (j : Fin 2) (hDet : (levelChartDerivative j (fderiv ℝ f x)).det ≠ 0) :
    Nonempty (PlanarLevelChart U f x) := by
  let F := levelChartMap j f
  let D (z : Plane) := levelChartDerivative j (fderiv ℝ f z)
  let K := U ∩ {z | (D z).det ≠ 0}
  have hF : ContDiffOn ℝ 1 F U := contDiffOn_levelChartMap j hf
  have hDiff (y : Plane) (hy : y ∈ U) : HasFDerivAt F (D y) y :=
    hasFDerivAt_levelChartMap j ((hf.differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy))
  have hAt : ContDiffAt ℝ 1 F x := (hF x hx).contDiffAt (hU.mem_nhds hx)
  let C := levelChartEquivOfDetNeZero (D x) hDet
  have hDF : HasFDerivAt F (C : Plane →L[ℝ] Plane) x := by
    unfold C
    rw [levelChartEquivOfDetNeZero_coe]
    exact hDiff x hx
  let e := hAt.toOpenPartialHomeomorph F hDF (by simp)
  have he : (e : Plane → Plane) = F := rfl
  have hxE : x ∈ e.source := hAt.mem_toOpenPartialHomeomorph_source hDF (by simp)
  have hD : ContinuousOn (fun z => (D z).det) U :=
    ContinuousLinearMap.continuous_det.comp_continuousOn (continuousOn_levelChartDerivative hU j hf)
  have hK : IsOpen K := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hAt' := (hD y hy.1).continuousAt (hU.mem_nhds hy.1)
    exact Filter.inter_mem (hU.mem_nhds hy.1) (hAt'.eventually_ne hy.2)
  let e' := e.restrOpen K hK
  have hE' : (e' : Plane → Plane) = F := he
  have hx' : x ∈ e'.source := ⟨hxE,hx,hDet⟩
  have hK' : e'.source ⊆ K := inter_subset_right
  have hU' : e'.source ⊆ U := hK'.trans inter_subset_left
  have hDer (y : Plane) (hy : y ∈ e'.source) : HasFDerivAt e' (D y) y := by
    rw [hE']
    exact hDiff y (hU' hy)
  have hInv : ContDiffOn ℝ 1 e'.symm e'.target := by
    intro z hz
    have hY : e'.symm z ∈ e'.source := e'.map_target hz
    let C' := levelChartEquivOfDetNeZero (D (e'.symm z)) (hK' hY).2
    have hd : HasFDerivAt e' (C' : Plane →L[ℝ] Plane) (e'.symm z) := by
      unfold C'
      rw [levelChartEquivOfDetNeZero_coe]
      exact hDer _ hY
    have hf' : ContDiffAt ℝ 1 e' (e'.symm z) := by
      rw [hE']
      exact (hF _ (hU' hY)).contDiffAt (hU.mem_nhds (hU' hY))
    exact (e'.contDiffAt_symm hz hd hf').contDiffWithinAt
  exact ⟨⟨j,e',hx',hU',hE',hInv,hDer⟩⟩

private theorem planarLevelChart_inverse_derivative_comp
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a)
    {y : Plane} (hy : y ∈ P.equiv.source) (v : Plane) :
    fderiv ℝ P.equiv.symm (P.equiv y) (levelChartDerivative P.coordinate (fderiv ℝ f y) v) = v := by
  have hT : P.equiv y ∈ P.equiv.target := P.equiv.map_source hy
  have hG := ((P.inverse_smooth _ hT).contDiffAt (P.equiv.open_target.mem_nhds hT)).differentiableAt (by simp)
  have hD := hG.hasFDerivAt.comp y (P.forward_derivative y hy)
  have hN : ∀ᶠ z in 𝓝 y, z ∈ P.equiv.source := P.equiv.open_source.mem_nhds hy
  have hEq : (fun z => P.equiv.symm (P.equiv z)) =ᶠ[𝓝 y] id :=
    hN.mono fun _ hz => P.equiv.left_inv hz
  have hMap := hD.fderiv.symm.trans (hEq.fderiv_eq.trans fderiv_id)
  exact DFunLike.congr_fun hMap v

private theorem measurableSet_inter_preimage_of_continuousOn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] {V : Set X} (hV : MeasurableSet V)
    {g : X → Y} (hg : ContinuousOn g V) {S : Set Y} (hS : MeasurableSet S) (b : Y) :
    MeasurableSet (V ∩ g ⁻¹' S) := by
  classical
  let F := V.piecewise g (fun _ => b)
  have hF : Measurable F := hg.measurable_piecewise continuousOn_const hV
  have hEq : V ∩ g ⁻¹' S = V ∩ F ⁻¹' S := by
    ext x
    by_cases hx : x ∈ V <;> simp [F,hx]
  rw [hEq]
  exact hV.inter (hS.preimage hF)

private theorem planarLevelChart_forward_coordinates
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a) (x : Plane) :
    (P.equiv x) 0 = f x ∧ (P.equiv x) 1 = x P.coordinate := by
  rw [P.forward_eq]
  exact ⟨rfl,rfl⟩

private theorem planarLevelChart_measurable_image
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a)
    {E : Set Plane} (hE : MeasurableSet E) (hES : E ⊆ P.equiv.source) :
    MeasurableSet (P.equiv '' E) := by
  have hEq : P.equiv '' E = P.equiv.target ∩ P.equiv.symm ⁻¹' E := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hxS := hES hx
      refine ⟨P.equiv.map_source hxS,?_⟩
      change P.equiv.symm (P.equiv x) ∈ E
      rwa [P.equiv.left_inv hxS]
    · intro hz
      exact ⟨P.equiv.symm z,hz.2,P.equiv.right_inv hz.1⟩
  rw [hEq]
  exact measurableSet_inter_preimage_of_continuousOn P.equiv.open_target.measurableSet
    P.equiv.symm.continuousOn hE (0 : Plane)

private def levelSection (t s : ℝ) : Plane := levelPairEquiv.symm (t,s)

private theorem levelSection_contDiff (t : ℝ) : ContDiff ℝ 1 (levelSection t) :=
  levelPairEquiv.symm.contDiff.comp (contDiff_const.prodMk contDiff_id)

private theorem levelSection_hasDerivAt (t s : ℝ) :
    HasDerivAt (levelSection t) (EuclideanSpace.single (1 : Fin 2) 1) s := by
  have hPair : HasDerivAt (fun r : ℝ => (t,r)) (0,1) s :=
    (hasDerivAt_const s t).prodMk (hasDerivAt_id s)
  have hD := levelPairEquiv.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s hPair
  have hE : levelPairEquiv.symm (0,1) = EuclideanSpace.single (1 : Fin 2) 1 := by
    rw [levelPairEquiv_symm_coordinates]
    ext i
    fin_cases i <;> simp
  exact hE ▸ hD

private def levelCurveDomain
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a) (t : ℝ) : Set ℝ :=
  levelSection t ⁻¹' P.equiv.target

private def levelCurve
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a) (t s : ℝ) : Plane :=
  P.equiv.symm (levelSection t s)

private theorem levelCurve_open
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a) (t : ℝ) :
    IsOpen (levelCurveDomain P t) :=
  P.equiv.open_target.preimage (levelSection_contDiff t).continuous

private theorem levelCurve_contDiffOn
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a) (t : ℝ) :
    ContDiffOn ℝ 1 (levelCurve P t) (levelCurveDomain P t) :=
  P.inverse_smooth.comp (levelSection_contDiff t).contDiffOn (fun _ h => h)

private theorem levelCurve_coordinates
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a) (t : ℝ)
    {s : ℝ} (hs : s ∈ levelCurveDomain P t) :
    levelCurve P t s ∈ P.equiv.source ∧ f (levelCurve P t s) = t ∧
      (levelCurve P t s) P.coordinate = s := by
  have hE : P.equiv (levelCurve P t s) = levelSection t s := P.equiv.right_inv hs
  have hPair := planarLevelChart_forward_coordinates P (levelCurve P t s)
  rw [hE] at hPair
  exact ⟨P.equiv.map_target hs, hPair.1.symm, hPair.2.symm⟩

private theorem levelCurve_deriv
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a) (t : ℝ)
    {s : ℝ} (hs : s ∈ levelCurveDomain P t) :
    deriv (levelCurve P t) s =
      fderiv ℝ P.equiv.symm (levelSection t s) (EuclideanSpace.single (1 : Fin 2) 1) := by
  have hT : levelSection t s ∈ P.equiv.target := hs
  have hAt := (P.inverse_smooth _ hT).contDiffAt (P.equiv.open_target.mem_nhds hT)
  exact ((hAt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s (levelSection_hasDerivAt t s)).deriv

private theorem levelCurve_image
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a) (t : ℝ)
    {S : Set ℝ} (hS : S ⊆ levelCurveDomain P t) :
    levelCurve P t '' S = (P.equiv.source ∩ {x | f x = t}) ∩ {x | x P.coordinate ∈ S} := by
  ext x
  constructor
  · rintro ⟨s,hs,rfl⟩
    obtain ⟨hSrc,hT,hCoord⟩ := levelCurve_coordinates P t (hS hs)
    refine ⟨⟨hSrc,hT⟩,?_⟩
    change (levelCurve P t s) P.coordinate ∈ S
    rwa [hCoord]
  · intro hx
    have hSrc : x ∈ P.equiv.source := hx.1.1
    have hF : f x = t := hx.1.2
    have hc : x P.coordinate ∈ S := hx.2
    refine ⟨x P.coordinate,hc,?_⟩
    have hEq : P.equiv x = levelSection t (x P.coordinate) := by
      rw [P.forward_eq]
      change levelPairEquiv.symm (f x,x P.coordinate) = _
      rw [hF]
      rfl
    change P.equiv.symm (levelSection t (x P.coordinate)) = x
    rw [← hEq, P.equiv.left_inv hSrc]

private theorem levelCurve_measurable_image
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a) (t : ℝ)
    {S : Set ℝ} (hS : MeasurableSet S) (hSub : S ⊆ levelCurveDomain P t) :
    MeasurableSet (levelCurve P t '' S) := by
  rw [levelCurve_image P t hSub]
  have hF : ContinuousOn f P.equiv.source := by
    have hP := ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.comp_continuousOn
      P.equiv.continuousOn)
    exact hP.congr (fun x _ => (planarLevelChart_forward_coordinates P x).1.symm)
  have hA : MeasurableSet (P.equiv.source ∩ f ⁻¹' {t}) :=
    measurableSet_inter_preimage_of_continuousOn P.equiv.open_source.measurableSet
      hF (measurableSet_singleton t) 0
  have hProj : Continuous (fun z : Plane => z P.coordinate) :=
    (EuclideanSpace.proj (𝕜 := ℝ) P.coordinate).continuous
  exact hA.inter (hS.preimage hProj.measurable)

private theorem levelCurve_speed_pos
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a) (t : ℝ)
    {s : ℝ} (hs : s ∈ levelCurveDomain P t) :
    0 < ‖deriv (levelCurve P t) s‖ := by
  let γ := levelCurve P t
  let π : Plane →L[ℝ] ℝ := EuclideanSpace.proj P.coordinate
  have hJ := levelCurve_open P t
  have hN : ∀ᶠ r in 𝓝 s, r ∈ levelCurveDomain P t := hJ.mem_nhds hs
  have hEq : (fun z : ℝ => π (γ z)) =ᶠ[𝓝 s] id :=
    hN.mono fun r hr => (levelCurve_coordinates P t hr).2.2
  have hγ := ((levelCurve_contDiffOn P t s hs).contDiffAt (hJ.mem_nhds hs)).differentiableAt (by simp)
  have hD := π.hasFDerivAt.comp_hasDerivAt s hγ.hasDerivAt
  have hOne : π (deriv γ s) = 1 := hD.deriv.symm.trans (hEq.deriv_eq.trans (deriv_id s))
  apply norm_pos_iff.2
  intro hZ
  change deriv γ s = 0 at hZ
  rw [hZ, map_zero] at hOne
  exact zero_ne_one hOne

private def levelSpeed
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a) (z : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal ‖fderiv ℝ P.equiv.symm z (EuclideanSpace.single (1 : Fin 2) 1)‖

private theorem levelSpeed_continuousOn
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a) :
    ContinuousOn (levelSpeed P) P.equiv.target := by
  have h := P.inverse_smooth.continuousOn_fderiv_of_isOpen P.equiv.open_target le_rfl
  have hApp := (ContinuousLinearMap.apply ℝ Plane (EuclideanSpace.single (1 : Fin 2) 1)).continuous.comp_continuousOn h
  exact ENNReal.continuous_ofReal.comp_continuousOn hApp.norm

private theorem levelFiberMeasure_eq_lintegral
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a)
    {E : Set Plane} (hE : MeasurableSet E) (hES : E ⊆ P.equiv.source) (t : ℝ) :
    Measure.hausdorffMeasure 1 (E ∩ {x | f x = t}) =
      ∫⁻ s : ℝ, (P.equiv '' E).indicator (levelSpeed P) (levelSection t s) := by
  let J := levelCurveDomain P t
  let γ := levelCurve P t
  let S := levelSection t ⁻¹' (P.equiv '' E)
  have hS : MeasurableSet S :=
    (planarLevelChart_measurable_image P hE hES).preimage (levelSection_contDiff t).continuous.measurable
  have hSJ : S ⊆ J := by
    rintro s ⟨y,hy,he⟩
    change levelSection t s ∈ P.equiv.target
    rw [← he]
    exact P.equiv.map_source (hES hy)
  have hInj : InjOn γ J := by
    intro s hs r hr h
    exact ((levelCurve_coordinates P t hs).2.2.symm.trans
      (congrArg (fun z : Plane => z P.coordinate) h)).trans (levelCurve_coordinates P t hr).2.2
  have hEq : γ '' S = E ∩ {x | f x = t} := by
    ext x
    constructor
    · rintro ⟨s,hs,rfl⟩
      have hcoord := levelCurve_coordinates P t (hSJ hs)
      obtain ⟨y,hy,hEq⟩ := hs
      refine ⟨?_,hcoord.2.1⟩
      change P.equiv.symm (levelSection t s) ∈ E
      rw [← hEq, P.equiv.left_inv (hES hy)]
      exact hy
    · intro hx
      let s := x P.coordinate
      have he : P.equiv x = levelSection t s := by
        rw [P.forward_eq]
        change levelPairEquiv.symm (f x,s) = _
        rw [show f x = t from hx.2]
        rfl
      refine ⟨s,⟨x,hx.1,he⟩,?_⟩
      change P.equiv.symm (levelSection t s) = x
      rw [← he, P.equiv.left_inv (hES hx.1)]
  calc
    _ = Measure.hausdorffMeasure 1 (γ '' S) := congrArg _ hEq.symm
    _ = ∫⁻ s in S, ENNReal.ofReal ‖deriv γ s‖ :=
      hausdorffMeasure_one_image_eq_speed_lintegral (levelCurve_open P t) γ (levelCurve_contDiffOn P t)
        hInj (fun _ hs => levelCurve_speed_pos P t hs)
        (fun A hA hAJ => levelCurve_measurable_image P t hA hAJ) hS hSJ
    _ = ∫⁻ s in S, levelSpeed P (levelSection t s) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hS] with s hs
      change ENNReal.ofReal ‖deriv (levelCurve P t) s‖ = _
      rw [levelCurve_deriv P t (hSJ hs)]
      rfl
    _ = _ := by
      rw [← lintegral_indicator hS]
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ S
      · have hs' : levelSection t s ∈ P.equiv '' E := hs
        rw [indicator_of_mem hs, indicator_of_mem hs']
      · have hs' : levelSection t s ∉ P.equiv '' E := hs
        rw [indicator_of_notMem hs, indicator_of_notMem hs']

private theorem planarLevelChart_coarea
    {U : Set Plane} {f : Plane → ℝ} {a : Plane} (P : PlanarLevelChart U f a)
    {E : Set Plane} (hE : MeasurableSet E) (hES : E ⊆ P.equiv.source) :
    AEMeasurable (fun t : ℝ => Measure.hausdorffMeasure 1 (E ∩ {y | f y = t})) volume ∧
      ∀ w : ℝ → ℝ≥0∞, Measurable w →
        (∫⁻ y in E, w (f y) * ENNReal.ofReal ‖fderiv ℝ f y‖) =
          ∫⁻ t : ℝ, w t * Measure.hausdorffMeasure 1 (E ∩ {y | f y = t}) := by
  classical
  let F := P.equiv
  let H := F '' E
  let ρ := levelSpeed P
  let Φ := H.indicator ρ
  have hH : MeasurableSet H := planarLevelChart_measurable_image P hE hES
  have hHT : H ⊆ P.equiv.target := image_subset_iff.mpr fun _ hy => P.equiv.map_source (hES hy)
  have hΦ : Measurable Φ :=
    ((levelSpeed_continuousOn P).mono hHT).measurable_piecewise continuousOn_const hH
  have hProd : Measurable (Function.uncurry (fun t s => Φ (levelSection t s))) :=
    hΦ.comp levelPairEquiv.symm.continuous.measurable
  have hLength (t : ℝ) : Measure.hausdorffMeasure 1 (E ∩ {y | f y = t}) =
      ∫⁻ s : ℝ, Φ (levelSection t s) := levelFiberMeasure_eq_lintegral P hE hES t
  constructor
  · rw [funext hLength]
    exact hProd.lintegral_prod_right.aemeasurable
  intro w hw
  have hJac := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure Plane) hE
    (fun y hy => (P.forward_derivative y (hES hy)).hasFDerivWithinAt)
    (P.equiv.injOn.mono hES) (fun z => w (z 0) * ρ z)
  have hDetSpeed (y : Plane) (hy : y ∈ E) :
      ENNReal.ofReal |(levelChartDerivative P.coordinate (fderiv ℝ f y)).det| * ρ (F y) =
        ENNReal.ofReal ‖fderiv ℝ f y‖ := by
    dsimp only [ρ,levelSpeed,F]
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    exact congrArg ENNReal.ofReal
      (planar_scalar_chart_jacobian_speed P.coordinate (fderiv ℝ f y)
        (levelChartDerivative P.coordinate (fderiv ℝ f y)) (fderiv ℝ P.equiv.symm (P.equiv y))
        (levelChartDerivative_coordinates P.coordinate (fderiv ℝ f y))
        (planarLevelChart_inverse_derivative_comp P (hES hy)))
  have hMain : (∫⁻ z in H, w (z 0) * ρ z) =
      ∫⁻ y in E, w (f y) * ENNReal.ofReal ‖fderiv ℝ f y‖ := by
    refine hJac.trans ?_
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hE] with y hy
    rw [(planarLevelChart_forward_coordinates P y).1, ← hDetSpeed y hy]
    ac_rfl
  have hMP : MeasurePreserving levelPairMeasurableEquiv.symm := levelPairEquiv_measurePreserving.symm
  have hFubini : AEMeasurable (fun z : ℝ × ℝ => w z.1 * Φ (levelSection z.1 z.2))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := (hw.comp measurable_fst).mul hProd |>.aemeasurable
  calc
    _ = ∫⁻ z in H, w (z 0) * ρ z := hMain.symm
    _ = ∫⁻ z, w (z 0) * Φ z := by
      rw [← lintegral_indicator hH]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ H
      · rw [indicator_of_mem hz, show Φ z = ρ z from indicator_of_mem hz _]
      · rw [indicator_of_notMem hz, show Φ z = 0 from indicator_of_notMem hz _, mul_zero]
    _ = ∫⁻ z : ℝ × ℝ, w z.1 * Φ (levelSection z.1 z.2) :=
      (hMP.lintegral_comp_emb levelPairMeasurableEquiv.symm.measurableEmbedding (fun z => w (z 0) * Φ z)).symm
    _ = ∫⁻ t : ℝ, ∫⁻ s : ℝ, w t * Φ (levelSection t s) := lintegral_prod _ hFubini
    _ = _ := by
      apply lintegral_congr
      intro t
      have hM : AEMeasurable (fun s : ℝ => Φ (levelSection t s)) volume :=
        (hΦ.comp (levelSection_contDiff t).continuous.measurable).aemeasurable
      rw [lintegral_const_mul'' _ hM, ← hLength]

/-- Local regular C¹ scalar coarea for any measurable subset of the
chart, including measurability of the actual Hausdorff fiber lengths. -/
theorem exists_regular_planar_coarea_chart
    {U : Set Plane} (hU : IsOpen U) (f : Plane → ℝ) (hf : ContDiffOn ℝ 1 f U)
    {x : Plane} (hx : x ∈ U) (hreg : fderiv ℝ f x ≠ 0) :
    ∃ V : Set Plane, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ E : Set Plane, MeasurableSet E → E ⊆ V →
        AEMeasurable (fun t : ℝ => Measure.hausdorffMeasure 1 (E ∩ {y | f y = t})) volume ∧
          ∀ w : ℝ → ℝ≥0∞, Measurable w →
            (∫⁻ y in E, w (f y) * ENNReal.ofReal ‖fderiv ℝ f y‖) =
              ∫⁻ t : ℝ, w t * Measure.hausdorffMeasure 1 (E ∩ {y | f y = t}) := by
  obtain ⟨j,hJ⟩ := exists_planar_scalar_chart_nondegenerate_coordinate (fderiv ℝ f x) hreg
  have hDet := hJ (levelChartDerivative j (fderiv ℝ f x))
    (levelChartDerivative_coordinates j (fderiv ℝ f x))
  obtain ⟨P⟩ := exists_planarLevelChart hU hf hx j hDet
  exact ⟨P.equiv.source, P.equiv.open_source, P.center_mem, P.source_subset,
    fun E hE hES => planarLevelChart_coarea P hE hES⟩

end Thesis

end
