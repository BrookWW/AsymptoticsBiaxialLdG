module

public import Thesis.Variational.RegularWallGraphPatch
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Smooth implicit graph patches in their frame at the boundary point. -/

public section

noncomputable section

open Filter Function Metric Set Topology
open scoped ContDiff RealInnerProductSpace

namespace Thesis

open MeasureGeometry

private theorem contDiffOn_infty_of_vertical_implicit_graph {S : Set Plane}
    (hS : IsOpen S) {g : Plane → ℝ} (hg : Continuous g) {f : Plane × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hEq : ∀ y ∈ S, f (y,g y) = 0)
    (hNormal : ∀ y ∈ S, fderiv ℝ f (y,g y) (0,1) ≠ 0) :
    ContDiffOn ℝ ∞ g S := by
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_infty.2
  intro k
  by_cases hk : k = 0
  · subst k
    exact contDiffAt_zero.2 ⟨univ,univ_mem,hg.continuousOn⟩
  let c := fderiv ℝ f (y,g y) (0,1)
  let D := (fderiv ℝ f (y,g y)).comp (ContinuousLinearMap.inr ℝ Plane ℝ)
  have hc : c ≠ 0 := hNormal y hy
  have hD : D = (LinearEquiv.smulOfNeZero ℝ ℝ c hc).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro t
    change fderiv ℝ f (y,g y) (0,t) = c*t
    have hV : ((0 : Plane),t) = t • ((0 : Plane),(1 : ℝ)) := by simp
    rw [hV,map_smul]
    exact mul_comm _ _
  have hI : D.IsInvertible := by
    rw [hD]
    exact ContinuousLinearMap.isInvertible_equiv
  have hk' : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast hk
  have hA : ContDiffAt ℝ (k : ℕ∞ω) f (y,g y) :=
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  let w := hA.implicitFunction hk' hI
  have hw : ContDiffAt ℝ (k : ℕ∞ω) w y := hA.contDiffAt_implicitFunction hk' hI
  have hG : ContinuousAt (fun p : Plane => (p,g p)) y := continuousAt_id.prodMk hg.continuousAt
  have hUnique := hG (hA.eventually_apply_eq_iff_implicitFunction hk' hI)
  have hNear : g =ᶠ[𝓝 y] w := by
    filter_upwards [hUnique,hS.mem_nhds hy] with p hp hpS
    exact (hp.1 ((hEq p hpS).trans (hEq y hy).symm)).symm
  exact hw.congr_of_eventuallyEq hNear

/-- A smooth defining function with regular nonzero normal derivative yields
a genuine smooth graph with exactly zero first derivative at its center. -/
theorem exists_regularWallGraphPatch_smooth_of_defining_function
    {U : Set Point} {a ν : Point} {r s : ℝ} {φ : Point → ℝ}
    (hν : ‖ν‖ = 1) (hr : 0 < r) (hφ : ContDiff ℝ ∞ φ) (hφ0 : φ a = 0)
    (hs : 0 < s) (hD : HasFDerivAt φ (s • innerSL ℝ ν) a)
    (hDef : U ∩ ball a r = {y | φ y < 0} ∩ ball a r) :
    ∃ P : RegularWallGraphPatch U, P.center = a ∧ ContDiff ℝ ∞ P.height ∧
      fderiv ℝ P.height (0 : Plane) = 0 := by
  have hk : (1 : ℕ∞ω) < (∞ : ℕ∞ω) :=
    WithTop.coe_lt_coe.mpr (ENat.coe_lt_top 1)
  obtain ⟨P,hP,hg,hgD,hEq⟩ := exists_regularWallGraphPatch_of_defining_function_with_equation
    le_rfl hk hν hr (hφ.of_le hk.le).contDiffOn hφ0 hs hD hDef
  have hR : ContDiff ℝ ∞ (P.rigid : (Plane × ℝ) → Point) := by
    rw [show (P.rigid : (Plane × ℝ) → Point) = fun p => P.center + P.frame.repr.symm (planeLinePlacement p)
      from funext P.rigid_apply]
    exact contDiff_const.add (P.frame.repr.symm.contDiff.comp planeLinePlacement.contDiff)
  have hgOn : ContDiffOn ℝ ∞ P.height P.base :=
    contDiffOn_infty_of_vertical_implicit_graph isOpen_ball hg.continuous (hφ.comp hR)
      (fun y hy => (hEq y hy).1) (fun y hy => (hEq y hy).2.ne)
  let R := P.baseRadius/2
  let b := R/2
  have hR0 : 0 < R := half_pos P.baseRadius_pos
  have hb : 0 < b := half_pos hR0
  have hSmall : b ≤ P.baseRadius := (half_lt_self hR0).le.trans (half_lt_self P.baseRadius_pos).le
  let χ : ContDiffBump (0 : Plane) := ⟨b,R,hb,half_lt_self hR0⟩
  let w (y : Plane) := χ y * P.height y
  have hw : ContDiff ℝ ∞ w := by
    apply contDiff_iff_contDiffAt.2
    intro y
    by_cases hy : y ∈ P.base
    · exact (χ.contDiff.contDiffAt).mul ((hgOn y hy).contDiffAt (isOpen_ball.mem_nhds hy))
    · have hs : y ∉ tsupport χ := by
        rw [χ.tsupport_eq]
        exact fun h => hy (closedBall_subset_ball (half_lt_self P.baseRadius_pos) h)
      have hNear : w =ᶠ[𝓝 y] (0 : Plane → ℝ) :=
        (notMem_tsupport_iff_eventuallyEq.1 hs).mono fun z hz => by simp [w,show χ z = 0 from hz]
      exact contDiffAt_const.congr_of_eventuallyEq hNear
  have hAgree : EqOn w P.height (closedBall (0 : Plane) b) := by
    intro y hy
    simp only [w,χ.one_of_mem_closedBall hy,one_mul]
  have hw0 : w 0 = 0 := (hAgree (mem_closedBall_self hb.le)).trans P.height_zero
  have hwD : fderiv ℝ w (0 : Plane) = 0 :=
    (show w =ᶠ[𝓝 (0 : Plane)] P.height from
      mem_of_superset (closedBall_mem_nhds _ hb) hAgree).fderiv_eq.trans hgD
  refine ⟨{ P with height := w
                   height_smooth := hw.of_le hk.le
                   height_zero := hw0
                   baseRadius := b
                   baseRadius_pos := hb
                   mem_domain := ?_ },hP,hw,hwD⟩
  intro y hy t ht
  change P.rigid (y,w y+t) ∈ U ↔ 0 < t
  rw [hAgree (ball_subset_closedBall hy)]
  exact P.mem_domain y (ball_subset_ball hSmall hy) t ht

end Thesis
