module

public import Thesis.Variational.FlatWallClosedRegularity
public import Thesis.Variational.HigherWeakMorreyWallCap

/-! The original closed-domain derivatives follow from weak regularity in a wall chart. -/

public section

noncomputable section

open Function HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal

namespace Thesis

/-- The continuous original field has classical regularity at the chart
center once its actual flat representation has one further weak derivative. -/
theorem RegularWallGraphPatch.contDiffWithinAt_of_flat_weakLpDerivatives
    {U : Set Point} (P : RegularWallGraphPatch U) (k : ℕ)
    (hP : ContDiff ℝ (k : ℕ∞ω) P.height) (hCenter : P.center ∈ closure U)
    {r p : ℝ} (hr : 0 < r) (hBall : ball (0 : Point) r ⊆ P.flatBox) (hp : 3 < p)
    {q : ℕ} {u : Point → Ambient q} (huC : ContinuousOn u (closure U))
    (hu : HasWeakLpDerivatives (upperCoordinateHalfSpace.val ∩ ball (0 : Point) r) univ
      (ENNReal.ofReal p) (k+1) (u ∘ P.flatChart)) :
    ContDiffWithinAt ℝ (k : ℕ∞ω) u (closure U) P.center := by
  let V := ball (0 : Point) (r/4)
  let S := upperCoordinateHalfSpace.val ∩ V
  have hV : V ⊆ P.flatBox :=
    (ball_subset_ball (by linarith only [hr] : r/4 ≤ r)).trans hBall
  have hSub : S ⊆ P.flatPositiveBox := fun _ hx => ⟨hV hx.2,hx.1⟩
  have hMaps : MapsTo P.flatChart (closure S) (closure U) :=
    P.flatChart_mapsTo_closure_domain.mono_left (closure_mono hSub)
  have hC : ContinuousOn (u ∘ P.flatChart) (closure S) :=
    huC.comp P.flatChart.continuous.continuousOn hMaps
  have hReg := contDiffOn_closure_of_continuous_weakLpDerivatives_on_smaller_flat_cap
    (show (0 : Point) ∈ flatWall from rfl) hr hp k hC hu
  exact P.contDiffWithinAt_of_flat_wall_cap hP hCenter
    isOpen_ball (mem_ball_self (by positivity : 0 < r/4)) hV hReg

/-- Weak tangential Sobolev regularity on a flat half-ball supplies the actual
next order of the field at the original physical wall point. -/
theorem RegularWallGraphPatch.contDiffWithinAt_of_tangential_weakLpDerivatives
    {U : Set Point} (P : RegularWallGraphPatch U) (hU : IsOpen U)
    (hP : ContDiff ℝ ∞ P.height) (hCenter : P.center ∈ closure U)
    {r p : ℝ} (hr : 0 < r) (hBall : ball (0 : Point) r ⊆ P.flatBox) (hp : 3 < p) (k : ℕ)
    {q : ℕ} {u f : Point → Ambient q}
    (hu : ContDiffOn ℝ (↑(k+1) : ℕ∞ω) u (closure U))
    (huI : ContDiffOn ℝ 2 u U) (hf : ContDiffOn ℝ (k : ℕ∞ω) f (closure U))
    (hEq : EqOn (laplacian u) f U)
    (hT : ∀ j : Fin 3, j ≠ 2 →
      HasWeakLpDerivatives (upperCoordinateHalfSpace.val ∩ ball (0 : Point) r) univ
        (ENNReal.ofReal p) (k+2) (coordDeriv j (u ∘ P.flatChart))) :
    ContDiffWithinAt ℝ (↑(k+2) : ℕ∞ω) u (closure U) P.center := by
  classical
  let V := ball (0 : Point) (r/4)
  let S := upperCoordinateHalfSpace.val ∩ V
  let v := u ∘ P.flatChart
  have hS : IsOpen S := upperCoordinateHalfSpace.property.inter isOpen_ball
  have hB : V ⊆ P.flatBox :=
    (ball_subset_ball (by linarith only [hr] : r/4 ≤ r)).trans hBall
  have hSub : S ⊆ P.flatPositiveBox := fun _ hx => ⟨hB hx.2,hx.1⟩
  have hC : ContDiffOn ℝ 2 v S :=
    huI.comp (P.flatChart_contDiff (hP.of_le (WithTop.coe_le_coe.mpr le_top))).contDiffOn
      (fun _ hx => (P.flatChart_mem_domain (hSub hx).1).2 (hSub hx).2)
  have hAll (j : {j : Fin 3 // j ≠ 2}) :
      ∃ T : Point → Ambient q, ContDiffOn ℝ (↑(k+1) : ℕ∞ω) T (closure S) ∧ EqOn T (coordDeriv j v) S := by
    obtain ⟨T,hAE,hTC⟩ := exists_contDiffOn_closure_of_weakLpDerivatives_on_smaller_flat_cap
      (a := 0) (show (0 : Point) ∈ flatWall from rfl) hr hp (k+1) (hT j j.property)
    have hTOrig : ContinuousOn (coordDeriv j v) S :=
      (hC.continuousOn_fderiv_of_isOpen hS (by norm_num)).clm_apply continuousOn_const
    have hTRep : ContinuousOn T S := hTC.continuousOn.mono subset_closure
    exact ⟨T,hTC,Measure.eqOn_open_of_ae_eq hAE.symm hS hTRep hTOrig⟩
  choose T hTC hTE using hAll
  let Z (j : Fin 3) : Point → Ambient q := if h : j ≠ 2 then T ⟨j,h⟩ else 0
  have hZ (j : Fin 3) (hj : j ≠ 2) :
      ContDiffOn ℝ (↑(k+1) : ℕ∞ω) (Z j) (closure S) ∧ EqOn (Z j) (coordDeriv j v) S := by
    simpa only [Z,dif_pos hj] using And.intro (hTC ⟨j,hj⟩) (hTE ⟨j,hj⟩)
  have hConv : Convex ℝ S :=
    (convex_halfSpace_gt (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).toLinearMap.isLinear 0).inter
      (convex_ball _ _)
  have hNe : S.Nonempty := flatWall_smaller_cap_nonempty (show (0 : Point) ∈ flatWall from rfl) hr
  have hFull := P.contDiffOn_closure_of_flat_cap_tangential_regular hP hU
    hS hConv hNe hSub k hu huI hf hEq Z hZ
  exact P.contDiffWithinAt_of_flat_wall_cap (hP.of_le (WithTop.coe_le_coe.mpr le_top)) hCenter
    isOpen_ball (mem_ball_self (by positivity : 0 < r/4)) hB hFull

end Thesis
