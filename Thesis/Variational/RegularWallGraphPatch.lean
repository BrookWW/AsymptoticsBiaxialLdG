module

public import Thesis.MeasureGeometry.SmoothGraphArea
public import Thesis.Variational.SmoothWallGeometry
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Group.Prod

/-! Flat graph coordinates at points with a regular outward normal. -/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal NNReal RealInnerProductSpace

namespace Thesis

open MeasureGeometry

def wallVerticalShear (g : Plane → ℝ) (hg : Continuous g) : (Plane × ℝ) ≃ₜ (Plane × ℝ) where
  toFun p := (p.1, g p.1 + p.2)
  invFun p := (p.1, p.2 - g p.1)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk ((hg.comp continuous_fst).add continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (hg.comp continuous_fst))

private theorem wallVerticalShear_volume (g : Plane → ℝ) (hg : Continuous g) :
    MeasurePreserving (wallVerticalShear g hg) (volume : Measure (Plane × ℝ)) volume :=
  (MeasurePreserving.id (volume : Measure Plane)).skew_product
    ((hg.measurable.comp measurable_fst).add measurable_snd)
    (Eventually.of_forall fun y => (measurePreserving_add_left volume (g y)).map_eq)

def wallRigidCoordinates (a : Point) (B : OrthonormalBasis (Fin 3) ℝ Point) :
    (Plane × ℝ) ≃ₜ Point :=
  planeLinePlacement.toHomeomorph.trans (B.repr.symm.toHomeomorph.trans (Homeomorph.addLeft a))

def wallPhysicalChart (a : Point) (B : OrthonormalBasis (Fin 3) ℝ Point)
    (g : Plane → ℝ) (hg : Continuous g) : (Plane × ℝ) ≃ₜ Point :=
  (wallVerticalShear g hg).trans (wallRigidCoordinates a B)

/-- An actual local epigraph with a (C^1) graph, in a rigid orthonormal frame.
The shear coordinates have an ordinary product Lebesgue measure. -/
structure RegularWallGraphPatch (U : Set Point) where
  center : Point
  frame : OrthonormalBasis (Fin 3) ℝ Point
  height : Plane → ℝ
  height_smooth : ContDiff ℝ 1 height
  height_zero : height 0 = 0
  baseRadius : ℝ
  baseRadius_pos : 0 < baseRadius
  halfHeight : ℝ
  halfHeight_pos : 0 < halfHeight
  mem_domain : ∀ y ∈ ball (0 : Plane) baseRadius, ∀ t ∈ Ioo (-halfHeight) halfHeight,
    wallPhysicalChart center frame height height_smooth.continuous (y,t) ∈ U ↔ 0 < t

namespace RegularWallGraphPatch

variable {U : Set Point}

/-- Rigid physical coordinates before subtracting the wall height. -/
def rigid (P : RegularWallGraphPatch U) : (Plane × ℝ) ≃ₜ Point := wallRigidCoordinates P.center P.frame

/-- The global shear with the original wall at its zero normal coordinate. -/
def chart (P : RegularWallGraphPatch U) : (Plane × ℝ) ≃ₜ Point :=
  wallPhysicalChart P.center P.frame P.height P.height_smooth.continuous

theorem rigid_apply (P : RegularWallGraphPatch U) (p : Plane × ℝ) :
    P.rigid p = P.center + P.frame.repr.symm (planeLinePlacement p) := rfl

theorem chart_apply (P : RegularWallGraphPatch U) (y : Plane) (t : ℝ) :
    P.chart (y,t) = P.rigid (y, P.height y + t) := rfl

theorem chart_volume (P : RegularWallGraphPatch U) :
    MeasurePreserving P.chart (volume : Measure (Plane × ℝ)) volume :=
  (measurePreserving_add_left (volume : Measure Point) P.center).comp
    (P.frame.repr.symm.measurePreserving.comp
      (planeLinePlacement_volume.comp (wallVerticalShear_volume P.height P.height_smooth.continuous)))

theorem chart_smooth (P : RegularWallGraphPatch U) : ContDiff ℝ 1 (P.chart : (Plane × ℝ) → Point) := by
  change ContDiff ℝ 1 (fun p : Plane × ℝ =>
    P.center + P.frame.repr.symm (planeLinePlacement (p.1, P.height p.1 + p.2)))
  exact contDiff_const.add (P.frame.repr.symm.contDiff.comp
    (planeLinePlacement.contDiff.comp (contDiff_fst.prodMk
      ((P.height_smooth.comp contDiff_fst).add contDiff_snd))))

abbrev base (P : RegularWallGraphPatch U) := ball (0 : Plane) P.baseRadius

abbrev box (P : RegularWallGraphPatch U) := P.base ×ˢ Ioo (-P.halfHeight) P.halfHeight

/-- The open physical image of the two-sided graph coordinates. -/
def neighborhood (P : RegularWallGraphPatch U) : Set Point := P.chart '' P.box

theorem isOpen_neighborhood (P : RegularWallGraphPatch U) : IsOpen P.neighborhood :=
  P.chart.isOpenMap _ (isOpen_ball.prod isOpen_Ioo)

theorem chart_zero (P : RegularWallGraphPatch U) : P.chart (0 : Plane × ℝ) = P.center := by
  change P.chart (0,0) = _
  rw [chart_apply, P.height_zero, add_zero, rigid_apply]
  change P.center + P.frame.repr.symm (planeLinePlacement 0) = P.center
  rw [map_zero, map_zero, add_zero]

theorem center_mem_neighborhood (P : RegularWallGraphPatch U) : P.center ∈ P.neighborhood :=
  ⟨0, ⟨mem_ball_self P.baseRadius_pos, neg_neg_of_pos P.halfHeight_pos, P.halfHeight_pos⟩, P.chart_zero⟩

theorem chart_mem_frontier_iff (P : RegularWallGraphPatch U) (hU : IsOpen U)
    {p : Plane × ℝ} (hp : p ∈ P.box) : P.chart p ∈ frontier U ↔ p.2 = 0 := by
  rw [frontier, hU.interior_eq]
  constructor
  · rintro ⟨hCl,hExt⟩
    have hN : p.2 ≤ 0 := not_lt.mp fun ht => hExt ((P.mem_domain _ hp.1 _ hp.2).2 ht)
    by_contra hNe
    have hNeg : p.2 < 0 := lt_of_le_of_ne hN hNe
    have hBox : ∀ᶠ q in 𝓝 (P.chart p), P.chart.symm q ∈ P.box := by
      have hp' : P.chart.symm (P.chart p) ∈ P.box := by rwa [P.chart.symm_apply_apply]
      exact P.chart.symm.continuous.continuousAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds hp')
    have hLow : ∀ᶠ q in 𝓝 (P.chart p), (P.chart.symm q).2 < 0 := by
      have hC := P.chart.symm.continuous.snd.continuousAt (x := P.chart p)
      apply hC (Iio_mem_nhds ?_)
      change (P.chart.symm (P.chart p)).2 < 0
      rwa [P.chart.symm_apply_apply]
    have hOutside : ∀ᶠ q in 𝓝 (P.chart p), q ∉ U := by
      filter_upwards [hBox,hLow] with q hq hLt
      intro hIn
      have hStep := (P.mem_domain _ hq.1 _ hq.2).1
      have hInv : P.chart ((P.chart.symm q).1, (P.chart.symm q).2) = q := P.chart.apply_symm_apply q
      exact (lt_asymm (hStep (hInv.symm ▸ hIn)) hLt)
    exact (mem_closure_iff_frequently.1 hCl) hOutside
  · intro hZero
    refine ⟨?_, fun hIn => ?_⟩
    swap
    · have hPos := (P.mem_domain _ hp.1 _ hp.2).1 hIn
      change 0 < p.2 at hPos
      rw [hZero] at hPos
      exact (lt_irrefl 0) hPos
    let F (t : ℝ) := P.chart (p.1,t)
    have hF : Continuous F := P.chart.continuous.comp (continuous_const.prodMk continuous_id)
    have hF0 : F 0 = P.chart p := by
      rw [show F 0 = P.chart (p.1,0) by rfl, ← hZero]
    have hh : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (P.chart p)) :=
      hF0 ▸ hF.continuousAt.continuousWithinAt
    apply mem_closure_of_tendsto hh
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      (Ioo_mem_nhds (neg_neg_of_pos P.halfHeight_pos) P.halfHeight_pos)] with t ht hI
    exact (P.mem_domain _ hp.1 _ hI).2 ht

theorem chart_mem_closure_of_nonneg (P : RegularWallGraphPatch U) (hU : IsOpen U)
    {p : Plane × ℝ} (hp : p ∈ P.box) (h : 0 ≤ p.2) : P.chart p ∈ closure U := by
  rcases h.eq_or_lt with hz | hpos
  · exact frontier_subset_closure ((P.chart_mem_frontier_iff hU hp).2 hz.symm)
  · exact subset_closure ((P.mem_domain _ hp.1 _ hp.2).2 hpos)

end RegularWallGraphPatch

private theorem contDiff_extension_of_germ {g : Plane → ℝ} {k : ℕ∞ω}
    (hk : k < (∞ : ℕ∞ω)) (hg : ContDiffAt ℝ k g (0 : Plane)) {r : ℝ} (hr : 0 < r) :
    ∃ s > 0, s ≤ r ∧ ∃ w : Plane → ℝ, ContDiff ℝ k w ∧ EqOn w g (closedBall 0 s) := by
  have hgNear := hg.eventually hk.ne
  obtain ⟨b,hb,hbG⟩ := Metric.mem_nhds_iff.mp hgNear
  let R := min (b / 2) r
  let s := R / 2
  have hR : 0 < R := lt_min (half_pos hb) hr
  have hs : 0 < s := half_pos hR
  have hRb : R < b := (min_le_left _ _).trans_lt (half_lt_self hb)
  let χ : ContDiffBump (0 : Plane) := ⟨s,R,hs,half_lt_self hR⟩
  let w (y : Plane) := χ y * g y
  refine ⟨s,hs,(half_lt_self hR).le.trans (min_le_right _ _),w,?_,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ ball (0 : Plane) b
    · have hχTop : ContDiff ℝ (∞ : ℕ∞ω) (χ : Plane → ℝ) := χ.contDiff
      have hχ : ContDiff ℝ k (χ : Plane → ℝ) := hχTop.of_le hk.le
      exact hχ.contDiffAt.mul (hbG hx)
    · have hOff : x ∉ tsupport χ := by
        rw [χ.tsupport_eq]
        exact fun h => hx (closedBall_subset_ball hRb h)
      have hEq : w =ᶠ[𝓝 x] (0 : Plane → ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hOff] with y hy
        simp only [w, hy, zero_mul, Pi.zero_apply]
      exact contDiffAt_const.congr_of_eventuallyEq hEq
  · intro x hx
    simp only [w, χ.one_of_mem_closedBall hx, one_mul]

/-- The implicit graph retains the equation and a strictly negative normal
derivative of the original defining function. -/
theorem exists_regularWallGraphPatch_of_defining_function_with_equation
    {U : Set Point} {a ν : Point} {r s : ℝ} {φ : Point → ℝ} {k : ℕ∞ω}
    (hk1 : 1 ≤ k) (hk : k < (∞ : ℕ∞ω)) (hν : ‖ν‖ = 1) (hr : 0 < r)
    (hφ : ContDiffOn ℝ k φ (ball a r)) (hφ0 : φ a = 0) (hs : 0 < s)
    (hD : HasFDerivAt φ (s • innerSL ℝ ν) a)
    (hDef : U ∩ ball a r = {y | φ y < 0} ∩ ball a r) :
    ∃ P : RegularWallGraphPatch U, P.center = a ∧ ContDiff ℝ k P.height ∧
      fderiv ℝ P.height (0 : Plane) = 0 ∧
      ∀ y ∈ P.base, (φ ∘ P.rigid) (y,P.height y) = 0 ∧
        fderiv ℝ (φ ∘ P.rigid) (y,P.height y) (0,1) < 0 := by
  have hk0 : k ≠ 0 := ne_of_gt (zero_lt_one.trans_le hk1)
  obtain ⟨B,hB⟩ := exists_axis_orthonormalBasis (e := -ν) (by rwa [norm_neg])
  let L := planeLinePlacement.trans B.repr.symm.toContinuousLinearEquiv
  let Q := wallRigidCoordinates a B
  have hQ (p : Plane × ℝ) : Q p = a + L p := rfl
  have hQ0 : Q (0 : Plane × ℝ) = a := by rw [hQ, map_zero, add_zero]
  have hOne : L (0,1) = -ν := by
    have he : planeLinePlacement (0,1) = axis 2 := by
      ext i
      fin_cases i <;> simp [planeLinePlacement_coordinate, axis]
    change B.repr.symm (planeLinePlacement (0,1)) = _
    rw [he, ← hB]
    exact B.repr_symm_single 2
  let f := φ ∘ Q
  let O := Q ⁻¹' ball a r
  have hO : IsOpen O := isOpen_ball.preimage Q.continuous
  have h0 : (0 : Plane × ℝ) ∈ O := by change Q 0 ∈ ball a r; rw [hQ0]; exact mem_ball_self hr
  have hCQ : ContDiff ℝ k (Q : Plane × ℝ → Point) := by
    rw [show (Q : Plane × ℝ → Point) = fun p => a + L p from funext hQ]
    exact contDiff_const.add L.contDiff
  have hCf : ContDiffOn ℝ k f O := hφ.comp hCQ.contDiffOn (fun _ h => h)
  have hF0 : f (0 : Plane × ℝ) = 0 := by change φ (Q 0) = 0; rw [hQ0,hφ0]
  have hC0 : ContDiffAt ℝ k f (0 : Plane × ℝ) := (hCf _ h0).contDiffAt (hO.mem_nhds h0)
  have hQD : HasFDerivAt Q L.toContinuousLinearMap (0 : Plane × ℝ) := by
    rw [show (Q : Plane × ℝ → Point) = fun p => a + L p from funext hQ]
    exact L.toContinuousLinearMap.hasFDerivAt.const_add a
  have hFDer : HasFDerivAt f ((s • innerSL ℝ ν).comp L.toContinuousLinearMap) (0 : Plane × ℝ) :=
    (hQ0.symm ▸ hD).comp 0 hQD
  have hPartial : (fderiv ℝ f (0 : Plane × ℝ)).comp (ContinuousLinearMap.inr ℝ Plane ℝ) =
      (LinearEquiv.smulOfNeZero ℝ ℝ (-s) (neg_ne_zero.mpr hs.ne')).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro t
    rw [hFDer.fderiv]
    have ht : L ((0 : Plane), t) = t • (-ν) := by
      rw [show ((0 : Plane), t) = t • ((0 : Plane), (1 : ℝ)) by simp, map_smul, hOne]
    change s * inner ℝ ν (L (0,t)) = -s * t
    rw [ht, real_inner_smul_right, inner_neg_right, real_inner_self_eq_norm_sq, hν, one_pow]
    ring
  have hInv : ((fderiv ℝ f (0 : Plane × ℝ)).comp (ContinuousLinearMap.inr ℝ Plane ℝ)).IsInvertible := by
    rw [hPartial]
    exact ContinuousLinearMap.isInvertible_equiv
  let g := hC0.implicitFunction hk0 hInv
  have hg0 : g (0 : Plane) = 0 := hC0.implicitFunction_apply_self hk0 hInv
  have hg : ContDiffAt ℝ k g (0 : Plane) := hC0.contDiffAt_implicitFunction hk0 hInv
  have hgφ : ∀ᶠ y in 𝓝 (0 : Plane), f (y,g y) = 0 := by
    simpa only [hF0, g] using! hC0.eventually_apply_implicitFunction hk0 hInv
  have hDCont := (((hCf.of_le hk1).continuousOn_fderiv_of_isOpen hO le_rfl) 0 h0).continuousAt (hO.mem_nhds h0)
  have hN : ∀ᶠ p in 𝓝 (0 : Plane × ℝ), (fderiv ℝ f p) (0,1) < 0 := by
    apply (hDCont.clm_apply continuousAt_const).eventually_lt continuousAt_const
    rw [hFDer.fderiv]
    change s * inner ℝ ν (L (0,1)) < 0
    rw [hOne, inner_neg_right, real_inner_self_eq_norm_sq, hν, one_pow]
    linarith
  have hIn : ∀ᶠ p in 𝓝 (0 : Plane × ℝ), p ∈ O := hO.mem_nhds h0
  obtain ⟨d,hd,hDx⟩ := Metric.mem_nhds_iff.mp (hIn.and hN)
  have hgSmall : ∀ᶠ y in 𝓝 (0 : Plane), |g y| < d / 2 := by
    have hgT := hg.continuousAt.abs.eventually_lt (continuousAt_const (y := d/2))
    exact hgT (by rw [hg0, abs_zero]; exact half_pos hd)
  obtain ⟨b,hb,hGb⟩ := Metric.mem_nhds_iff.mp (hgφ.and hgSmall)
  obtain ⟨b₁,hb₁,hb₁r,w,hw,hwg⟩ := contDiff_extension_of_germ hk hg (lt_min hb hd)
  let ρ := b₁ / 2
  have hρ : 0 < ρ := half_pos hb₁
  have hw₀ : w 0 = 0 := (hwg (mem_closedBall_self hb₁.le)).trans hg0
  have hTangential : (fderiv ℝ f (0 : Plane × ℝ)).comp (ContinuousLinearMap.inl ℝ Plane ℝ) = 0 := by
    apply ContinuousLinearMap.ext
    intro y
    rw [hFDer.fderiv]
    change s * inner ℝ ν (L (y,0)) = 0
    have he : ν = -B 2 := by rw [hB,neg_neg]
    have hu : inner ℝ (B 2) (L (y,0)) = 0 := by
      rw [← B.repr_apply_apply]
      change B.repr (B.repr.symm (planeLinePlacement (y,0))) 2 = 0
      rw [B.repr.apply_symm_apply]
      exact (planeLinePlacement_coordinate y 0).2.2
    rw [he,inner_neg_left,hu,neg_zero,mul_zero]
  have hgD : fderiv ℝ g (0 : Plane) = 0 := by
    have he := (hC0.hasStrictFDerivAt_implicitFunction hk0 hInv).hasFDerivAt.fderiv
    change fderiv ℝ g (0 : Plane) = _ at he
    rw [hTangential,ContinuousLinearMap.comp_zero] at he
    simpa only [neg_zero] using he
  have hwD : fderiv ℝ w (0 : Plane) = 0 := by
    have hE : w =ᶠ[𝓝 (0 : Plane)] g :=
      mem_of_superset (closedBall_mem_nhds _ hb₁) hwg
    exact hE.fderiv_eq.trans hgD
  have hY (y : Plane) (hy : y ∈ ball (0 : Plane) ρ) : ‖y‖ < d ∧ f (y,w y) = 0 ∧ |w y| < d / 2 := by
    have hYb₁ : ‖y‖ < b₁ := (mem_ball_zero_iff.mp hy).trans (half_lt_self hb₁)
    have hW := hwg (mem_closedBall_zero_iff.2 hYb₁.le)
    have hG := hGb (mem_ball_zero_iff.2 (hYb₁.trans_le (hb₁r.trans (min_le_left _ _))))
    rw [hW]
    exact ⟨hYb₁.trans_le (hb₁r.trans (min_le_right _ _)),hG⟩
  have hCoord (y : Plane) (hy : ‖y‖ < d) (t : ℝ) (ht : t ∈ Ioo (-d) d) :
      (y,t) ∈ ball (0 : Plane × ℝ) d := by
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff, Real.norm_eq_abs]
    exact ⟨hy, abs_lt.2 ht⟩
  refine ⟨{ center := a
            frame := B
            height := w
            height_smooth := hw.of_le hk1
            height_zero := hw₀
            baseRadius := ρ
            baseRadius_pos := hρ
            halfHeight := d / 2
            halfHeight_pos := half_pos hd
            mem_domain := ?_ }, rfl, hw, hwD, ?_⟩
  · intro y hy t ht
    obtain ⟨hyD, hZero, hwD⟩ := hY y hy
    have hAnti : StrictAntiOn (fun z : ℝ => f (y,z)) (Ioo (-d) d) := by
      have hInto : MapsTo (fun z : ℝ => (y,z)) (Ioo (-d) d) O := fun z hz => (hDx (hCoord y hyD z hz)).1
      refine strictAntiOn_of_deriv_neg (convex_Ioo _ _)
        (hCf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hInto) ?_
      intro z hz
      rw [isOpen_Ioo.interior_eq] at hz
      have hdd := (((hCf _ (hInto hz)).contDiffAt (hO.mem_nhds (hInto hz))).differentiableAt hk0).hasFDerivAt
      have hZ : HasDerivAt (fun u : ℝ => (y,u)) ((0 : Plane),1) z :=
        (hasDerivAt_const z y).prodMk (hasDerivAt_id z)
      change deriv (f ∘ fun u : ℝ => (y,u)) z < 0
      rw [(hdd.comp_hasDerivAt z hZ).deriv]
      exact (hDx (hCoord y hyD z hz)).2
    have hWIn : w y ∈ Ioo (-d) d := abs_lt.1 (hwD.trans (half_lt_self hd))
    have hTIn : w y + t ∈ Ioo (-d) d := abs_lt.1 (by
      exact (abs_add_le _ _).trans_lt (by linarith only [hwD, abs_lt.2 ht]))
    have hTB : Q (y,w y+t) ∈ ball a r := (hDx (hCoord y hyD _ hTIn)).1
    have hEq : Q (y,w y+t) ∈ U ↔ f (y,w y+t) < 0 := by
      have hE := Set.ext_iff.mp hDef (Q (y,w y+t))
      change Q (y,w y+t) ∈ U ↔ φ (Q (y,w y+t)) < 0
      simpa only [mem_inter_iff, mem_setOf_eq, hTB, and_true] using hE
    change Q (y,w y+t) ∈ U ↔ 0 < t
    rw [hEq]
    constructor
    · intro hn
      by_contra hBad
      have hle : w y + t ≤ w y := by linarith only [le_of_not_gt hBad]
      have hL := hAnti.antitoneOn hTIn hWIn hle
      change f (y,w y) ≤ f (y,w y+t) at hL
      rw [hZero] at hL
      exact not_lt_of_ge hL hn
    · intro htPos
      have hL := hAnti hWIn hTIn (lt_add_of_pos_right _ htPos)
      change f (y,w y+t) < f (y,w y) at hL
      rwa [hZero] at hL
  · intro y hy
    obtain ⟨hyD,hZero,hSmall⟩ := hY y hy
    have hV : w y ∈ Ioo (-d) d := abs_lt.1 (hSmall.trans (half_lt_self hd))
    exact ⟨hZero,(hDx (hCoord y hyD (w y) hV)).2⟩

/-- A regular defining function supplies graph coordinates of the same
finite differentiability order. The graph has zero slope at the origin. -/
theorem exists_regularWallGraphPatch_of_defining_function
    {U : Set Point} {a ν : Point} {r s : ℝ} {φ : Point → ℝ} {k : ℕ∞ω}
    (hk1 : 1 ≤ k) (hk : k < (∞ : ℕ∞ω)) (hν : ‖ν‖ = 1) (hr : 0 < r)
    (hφ : ContDiffOn ℝ k φ (ball a r)) (hφ0 : φ a = 0) (hs : 0 < s)
    (hD : HasFDerivAt φ (s • innerSL ℝ ν) a)
    (hDef : U ∩ ball a r = {y | φ y < 0} ∩ ball a r) :
    ∃ P : RegularWallGraphPatch U, P.center = a ∧ ContDiff ℝ k P.height ∧
      fderiv ℝ P.height (0 : Plane) = 0 := by
  obtain ⟨P,hC,hS,hD,_⟩ := exists_regularWallGraphPatch_of_defining_function_with_equation
    hk1 hk hν hr hφ hφ0 hs hD hDef
  exact ⟨P,hC,hS,hD⟩


/-- Every regular defining function supplies genuine local epigraph coordinates. -/
theorem HasRegularOutwardNormalAt.exists_graph_patch {U : Set Point} {a ν : Point}
    (h : HasRegularOutwardNormalAt U a ν) :
    ∃ P : RegularWallGraphPatch U, P.center = a := by
  obtain ⟨_,hν,r,φ,s,hr,hφ,hφ0,hs,hD,hDef⟩ := h
  obtain ⟨P,hP,_,_⟩ := exists_regularWallGraphPatch_of_defining_function le_rfl (by simp)
    hν hr hφ hφ0 hs hD hDef
  exact ⟨P,hP⟩

end Thesis
