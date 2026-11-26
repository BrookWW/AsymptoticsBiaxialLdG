module

public import Thesis.Definitions
import Thesis.MeasureGeometry.CylinderCoordinates
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Volume-preserving flat boxes and boundary distance in a smooth domain. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Topology

namespace Thesis

open MeasureGeometry

/-- Ordinary rectangular coordinates for the horizontal and normal directions. -/
abbrev EpigraphCoordinates := (ℝ × ℝ) × ℝ

private def horizontalPairChart : (ℝ × ℝ) ≃ₜ Plane where
  toFun p := WithLp.toLp 2 ![p.1, p.2]
  invFun y := (y 0, y 1)
  left_inv p := by rcases p with ⟨s,t⟩; rfl
  right_inv y := by apply PiLp.ext; intro i; fin_cases i <;> rfl
  continuous_toFun := (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd)
  continuous_invFun := (PiLp.continuous_apply 2 _ 0).prodMk (PiLp.continuous_apply 2 _ 1)

private theorem measurePreserving_horizontalPairChart :
    MeasurePreserving horizontalPairChart (volume : Measure (ℝ × ℝ)) (volume : Measure Plane) := by
  have h : MeasurePreserving horizontalPairChart.symm (volume : Measure Plane) (volume : Measure (ℝ × ℝ)) :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  exact h.symm horizontalPairChart.symm.toMeasurableEquiv

private def planeLineCoordinates : (Plane × ℝ) ≃L[ℝ] Point :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ Plane ℝ).symm.trans
    planeLineEuclideanIsometry.toContinuousLinearEquiv

private def planeLineChart : (Plane × ℝ) ≃ₜ Point := planeLineCoordinates.toHomeomorph

private theorem measurePreserving_planeLineChart :
    MeasurePreserving planeLineChart (volume : Measure (Plane × ℝ)) (volume : Measure Point) :=
  planeLineEuclideanIsometry.measurePreserving.comp (WithLp.volume_preserving_toLp Plane ℝ)

private theorem planeLineChart_norm_sq (y : Plane) (t : ℝ) :
    ‖planeLineChart (y,t)‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rfl

private theorem planeLineChart_norm_le (y : Plane) (t : ℝ) :
    ‖planeLineChart (y,t)‖ ≤ ‖y‖ + |t| := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (abs_nonneg _))).1
  rw [planeLineChart_norm_sq]
  nlinarith only [sq_abs t, mul_nonneg (norm_nonneg y) (abs_nonneg t)]

private theorem horizontalPairChart_norm_le (p : ℝ × ℝ) :
    ‖horizontalPairChart p‖ ≤ 2 * ‖p‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).1
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have h1 : |p.1| ≤ ‖p‖ := by rw [Prod.norm_def, ← Real.norm_eq_abs]; exact le_max_left _ _
  have h2 : |p.2| ≤ ‖p‖ := by rw [Prod.norm_def, ← Real.norm_eq_abs]; exact le_max_right _ _
  have h1' := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (abs_nonneg _) h2 2
  change p.1 ^ 2 + p.2 ^ 2 ≤ (2 * ‖p‖) ^ 2
  nlinarith only [h1', h2', sq_abs p.1, sq_abs p.2, sq_nonneg ‖p‖]

private def smoothVerticalShear (g : Plane → ℝ) (hg : Continuous g) : (Plane × ℝ) ≃ₜ (Plane × ℝ) where
  toFun p := (p.1, g p.1 + p.2)
  invFun p := (p.1, p.2 - g p.1)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk ((hg.comp continuous_fst).add continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (hg.comp continuous_fst))

private theorem measurePreserving_smoothVerticalShear (g : Plane → ℝ) (hg : Continuous g) :
    MeasurePreserving (smoothVerticalShear g hg) (volume : Measure (Plane × ℝ)) volume :=
  (MeasurePreserving.id (volume : Measure Plane)).skew_product
    ((hg.measurable.comp measurable_fst).add measurable_snd)
    (Eventually.of_forall fun y => (measurePreserving_add_left volume (g y)).map_eq)

private def epigraphPhysicalChart (a : Point) (A : Point ≃ₗᵢ[ℝ] Point)
    (g : Plane → ℝ) (hg : Continuous g) : EpigraphCoordinates ≃ₜ Point :=
  (horizontalPairChart.prodCongr (Homeomorph.refl ℝ)).trans
    ((smoothVerticalShear g hg).trans (planeLineChart.trans
      (A.symm.toHomeomorph.trans (Homeomorph.addLeft a))))

private theorem epigraphPhysicalChart_apply (a : Point) (A : Point ≃ₗᵢ[ℝ] Point)
    (g : Plane → ℝ) (hg : Continuous g) (y : ℝ × ℝ) (t : ℝ) :
    epigraphPhysicalChart a A g hg (y,t) = a +
      A.symm (planeLineChart (horizontalPairChart y, g (horizontalPairChart y) + t)) := rfl

private theorem epigraphPhysicalChart_volume (a : Point) (A : Point ≃ₗᵢ[ℝ] Point)
    (g : Plane → ℝ) (hg : Continuous g) :
    MeasurePreserving (epigraphPhysicalChart a A g hg) (volume : Measure EpigraphCoordinates) volume := by
  exact (measurePreserving_add_left (volume : Measure Point) a).comp
    (A.symm.measurePreserving.comp (measurePreserving_planeLineChart.comp
      ((measurePreserving_smoothVerticalShear g hg).comp
        (measurePreserving_horizontalPairChart.prod (MeasurePreserving.id (volume : Measure ℝ))))))

/-- A physical chart with ordinary product measure and affine normal
lines. The distance estimates hold on the closed rectangle. -/
structure SmoothDomainEpigraphBox (U : Set Point) where
  radius : ℝ
  radius_pos : 0 < radius
  chart : EpigraphCoordinates ≃ₜ Point
  chart_volume : MeasurePreserving chart (volume : Measure EpigraphCoordinates) volume
  lip : ℝ≥0
  chart_lipschitz : LipschitzOnWith lip chart (closedBall (0 : EpigraphCoordinates) radius)
  direction : Point
  direction_norm : ‖direction‖ = 1
  affineNormal : ∀ y t, chart (y,t) = chart (y,0) + t • direction
  mem_domain : ∀ p ∈ closedBall (0 : EpigraphCoordinates) radius, chart p ∈ U ↔ 0 < p.2
  wall : ∀ y, ‖y‖ ≤ radius → chart (y,0) ∈ frontier U
  distanceFactor : ℝ
  distanceFactor_pos : 0 < distanceFactor
  distance_ge : ∀ p ∈ closedBall (0 : EpigraphCoordinates) radius, 0 < p.2 →
    distanceFactor * p.2 ≤ infDist (chart p) (frontier U)
  chart_smooth : ContDiff ℝ ∞ (chart : EpigraphCoordinates → Point)
  chart_inverse_smooth : ContDiff ℝ ∞ (chart.symm : Point → EpigraphCoordinates)
  inverseLip : ℝ≥0
  chart_inverse_lipschitz :
    LipschitzOnWith inverseLip chart.symm (chart '' closedBall (0 : EpigraphCoordinates) radius)
  frontier_iff : ∀ p ∈ closedBall (0 : EpigraphCoordinates) radius, chart p ∈ frontier U ↔ p.2 = 0


private def horizontalPart (z : Point) : Plane := (planeLineCoordinates.symm z).1

private theorem horizontalPart_coordinate (z : Point) : horizontalPart z = WithLp.toLp 2 ![z 0,z 1] := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

private theorem planeLineChart_coordinates (y : Plane) (t : ℝ) :
    horizontalPart (planeLineChart (y,t)) = y ∧ (planeLineChart (y,t)) 2 = t :=
  ⟨congrArg Prod.fst (planeLineCoordinates.symm_apply_apply (y,t)), rfl⟩

private theorem horizontalPart_norm_le (z : Point) : ‖horizontalPart z‖ ≤ ‖z‖ := by
  let p := planeLineCoordinates.symm z
  have hEq : planeLineChart p = z := planeLineCoordinates.apply_symm_apply z
  have h := planeLineChart_norm_sq p.1 p.2
  rw [show planeLineChart (p.1,p.2) = z from hEq] at h
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  change ‖p.1‖ ^ 2 ≤ ‖z‖ ^ 2
  linarith only [h, sq_nonneg p.2]

private theorem horizontalPairChart_sub (x y : ℝ × ℝ) :
    horizontalPairChart (x - y) = horizontalPairChart x - horizontalPairChart y := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

private theorem epigraphPhysicalChart_affine_normal (a : Point) (A : Point ≃ₗᵢ[ℝ] Point)
    (g : Plane → ℝ) (hg : Continuous g) :
    ‖A.symm (planeLineChart (0,1))‖ = 1 ∧
      ∀ y t, epigraphPhysicalChart a A g hg (y,t) =
        epigraphPhysicalChart a A g hg (y,0) + t • A.symm (planeLineChart (0,1)) := by
  constructor
  · rw [A.symm.norm_map]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1
    rw [planeLineChart_norm_sq, norm_zero]
    norm_num
  · intro y t
    rw [epigraphPhysicalChart_apply, epigraphPhysicalChart_apply, add_zero]
    let X : Plane × ℝ := (horizontalPairChart y, g (horizontalPairChart y))
    have hEq : (horizontalPairChart y, g (horizontalPairChart y) + t) = X + t • ((0,1) : Plane × ℝ) := by
      apply Prod.ext <;> simp [X]
    rw [hEq]
    change a + A.symm (planeLineCoordinates (X + t • (0,1))) =
      (a + A.symm (planeLineCoordinates X)) + t • A.symm (planeLineCoordinates (0,1))
    rw [map_add, map_smul, map_add, map_smul, add_assoc]

private theorem epigraphChart_mem_domain_of_ball {U : Set Point} (a : Point)
    (A : Point ≃ₗᵢ[ℝ] Point) (g : Plane → ℝ) (hg : Continuous g) (R : ℝ)
    (hEpi : U ∩ ball a R =
      {x | let z := A (x - a); g (WithLp.toLp 2 ![z 0,z 1]) < z 2} ∩ ball a R)
    {p : EpigraphCoordinates} (hp : epigraphPhysicalChart a A g hg p ∈ ball a R) :
    epigraphPhysicalChart a A g hg p ∈ U ↔ 0 < p.2 := by
  let F := epigraphPhysicalChart a A g hg
  have hCoord : A (F p - a) = planeLineChart (horizontalPairChart p.1, g (horizontalPairChart p.1) + p.2) := by
    rw [show F p = a + A.symm (planeLineChart (horizontalPairChart p.1, g (horizontalPairChart p.1) + p.2)) from
      epigraphPhysicalChart_apply a A g hg p.1 p.2,
      add_comm a, add_sub_cancel_right, LinearIsometryEquiv.apply_symm_apply]
  have hP := planeLineChart_coordinates (horizontalPairChart p.1) (g (horizontalPairChart p.1) + p.2)
  have hh : F p ∈ U ↔
      g (horizontalPart (A (F p - a))) < (A (F p - a)) 2 := by
    rw [horizontalPart_coordinate]
    have h := Set.ext_iff.mp hEpi (F p)
    have hp' : F p ∈ ball a R := hp
    simpa only [mem_inter_iff, hp', and_true, mem_setOf_eq] using h
  rw [hh, hCoord, hP.1, hP.2, lt_add_iff_pos_right]

private theorem epigraphChart_mem_frontier_of_ball {U : Set Point} (hU : IsOpen U) (a : Point)
    (A : Point ≃ₗᵢ[ℝ] Point) (g : Plane → ℝ) (hg : Continuous g) (R : ℝ)
    (hEpi : U ∩ ball a R =
      {x | let z := A (x - a); g (WithLp.toLp 2 ![z 0,z 1]) < z 2} ∩ ball a R)
    {p : EpigraphCoordinates} (hp : epigraphPhysicalChart a A g hg p ∈ ball a R) :
    epigraphPhysicalChart a A g hg p ∈ frontier U ↔ p.2 = 0 := by
  let F := epigraphPhysicalChart a A g hg
  have hMem (q : EpigraphCoordinates) (hq : F q ∈ ball a R) : F q ∈ U ↔ 0 < q.2 :=
    epigraphChart_mem_domain_of_ball a A g hg R hEpi hq
  rw [frontier, hU.interior_eq]
  constructor
  · rintro ⟨hClose,hOutside⟩
    have ht : p.2 ≤ 0 := le_of_not_gt fun h => hOutside ((hMem p hp).2 h)
    by_contra hZero
    have hNeg := lt_of_le_of_ne ht hZero
    have hNbod : ∀ᶠ x in 𝓝 (F p), x ∈ ball a R :=
      isOpen_ball.mem_nhds hp
    have hNegEventually : ∀ᶠ x in 𝓝 (F p), (F.symm x).2 < 0 := by
      have hT : Tendsto (fun x => (F.symm x).2) (𝓝 (F p)) (𝓝 (F.symm (F p)).2) :=
        (F.symm.continuous.snd.continuousAt (x := F p)).tendsto
      rw [F.symm_apply_apply] at hT
      exact hT (Iio_mem_nhds hNeg)
    have hNot : ∀ᶠ x in 𝓝 (F p), x ∉ U := by
      filter_upwards [hNbod,hNegEventually] with x hx hxNeg
      have hx' : F (F.symm x) ∈ ball a R := by simpa only [F.apply_symm_apply] using hx
      have hM := hMem (F.symm x) hx'
      rw [F.apply_symm_apply] at hM
      exact fun h => (not_lt_of_gt hxNeg) (hM.1 h)
    exact (mem_closure_iff_frequently.1 hClose) hNot
  · intro ht
    refine ⟨?_, fun h => (lt_irrefl (0 : ℝ)) (ht ▸ (hMem p hp).1 h)⟩
    let P (t : ℝ) := F (p.1,t)
    have hP : Continuous P := F.continuous.comp (continuous_const.prodMk continuous_id)
    have hP0 : P 0 = F p := by rw [show P 0 = F (p.1,0) from rfl, ← ht]
    have hT : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 (F p)) :=
      hP0 ▸ hP.continuousAt.continuousWithinAt
    apply mem_closure_of_tendsto hT
    filter_upwards [hT (isOpen_ball.mem_nhds hp), self_mem_nhdsWithin] with t hPt htpos
    exact (hMem (p.1,t) hPt).2 htpos


private theorem epigraphPhysicalChart_norm_from_center (a : Point) (A : Point ≃ₗᵢ[ℝ] Point)
    (g : Plane → ℝ) (hg : Continuous g) (p : EpigraphCoordinates) :
    dist (epigraphPhysicalChart a A g hg p) a ≤
      ‖horizontalPairChart p.1‖ + |g (horizontalPairChart p.1) + p.2| := by
  rw [epigraphPhysicalChart_apply, dist_eq_norm, add_sub_cancel_left, A.symm.norm_map]
  exact planeLineChart_norm_le _ _

private theorem epigraphHorizontal_dist_le (y z : ℝ × ℝ) :
    dist (horizontalPairChart y) (horizontalPairChart z) ≤ 2 * dist y z := by
  rw [dist_eq_norm, dist_eq_norm, ← horizontalPairChart_sub]
  exact horizontalPairChart_norm_le _

private theorem epigraphPhysicalChart_lipschitzOn_box (a : Point) (A : Point ≃ₗᵢ[ℝ] Point)
    (g : Plane → ℝ) (hg : Continuous g) {R b : ℝ} {L : ℝ≥0} (hb : 2 * b < R)
    (hL : LipschitzOnWith L g (ball 0 R)) :
    LipschitzOnWith (3 + 2 * L) (epigraphPhysicalChart a A g hg)
      (closedBall (0 : EpigraphCoordinates) b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  let y := horizontalPairChart p.1
  let z := horizontalPairChart q.1
  have hy : y ∈ ball (0 : Plane) R := mem_ball_zero_iff.2
    ((horizontalPairChart_norm_le p.1).trans_lt
      ((mul_le_mul_of_nonneg_left ((norm_fst_le p).trans (mem_closedBall_zero_iff.1 hp)) (by norm_num)).trans_lt hb))
  have hz : z ∈ ball (0 : Plane) R := mem_ball_zero_iff.2
    ((horizontalPairChart_norm_le q.1).trans_lt
      ((mul_le_mul_of_nonneg_left ((norm_fst_le q).trans (mem_closedBall_zero_iff.1 hq)) (by norm_num)).trans_lt hb))
  have hG := hL.dist_le_mul y hy z hz
  have hY : dist y z ≤ 2 * dist p q :=
    (epigraphHorizontal_dist_le p.1 q.1).trans
      (mul_le_mul_of_nonneg_left ((LipschitzWith.prod_fst : LipschitzWith 1
        (Prod.fst : EpigraphCoordinates → ℝ × ℝ)).dist_le_mul p q |>.trans_eq (one_mul _)) (by norm_num))
  have hN : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hV : |(g y + p.2) - (g z + q.2)| ≤ dist (g y) (g z) + dist p.2 q.2 := by
    rw [show g y + p.2 - (g z + q.2) = (g y - g z) + (p.2-q.2) by ring, Real.dist_eq, Real.dist_eq]
    exact abs_add_le _ _
  have hEq : dist (epigraphPhysicalChart a A g hg p) (epigraphPhysicalChart a A g hg q) =
      ‖planeLineChart (y - z, (g y + p.2) - (g z + q.2))‖ := by
    rw [epigraphPhysicalChart_apply, epigraphPhysicalChart_apply, dist_add_left,
      A.symm.isometry.dist_eq, dist_eq_norm]
    change ‖planeLineCoordinates (y,g y + p.2) - planeLineCoordinates (z,g z + q.2)‖ = _
    rw [← map_sub]
    rfl
  rw [hEq]
  have hGD := hG.trans (mul_le_mul_of_nonneg_left hY L.coe_nonneg)
  have hYZ : ‖y-z‖ ≤ 2 * dist p q := by simpa only [dist_eq_norm] using hY
  have hA := (planeLineChart_norm_le (y-z) ((g y+p.2)-(g z+q.2))).trans
    (add_le_add hYZ (hV.trans (add_le_add hGD hN)))
  push_cast
  exact hA.trans_eq (by ring)

private theorem epigraphPhysicalChart_rotatedCoordinates (a : Point) (A : Point ≃ₗᵢ[ℝ] Point)
    (g : Plane → ℝ) (hg : Continuous g) (p : EpigraphCoordinates) :
    A (epigraphPhysicalChart a A g hg p - a) =
      planeLineChart (horizontalPairChart p.1, g (horizontalPairChart p.1) + p.2) := by
  rw [epigraphPhysicalChart_apply, add_comm a, add_sub_cancel_right, LinearIsometryEquiv.apply_symm_apply]

private theorem epigraphPhysicalChart_normalCoordinate (a : Point) (A : Point ≃ₗᵢ[ℝ] Point)
    (g : Plane → ℝ) (hg : Continuous g) (x : Point) :
    ((epigraphPhysicalChart a A g hg).symm x).2 =
      (A (x-a)) 2 - g (horizontalPart (A (x-a))) := by
  let F := epigraphPhysicalChart a A g hg
  let p := F.symm x
  have hP := epigraphPhysicalChart_rotatedCoordinates a A g hg p
  change A (F (F.symm x) - a) = _ at hP
  rw [F.apply_symm_apply] at hP
  have h := planeLineChart_coordinates (horizontalPairChart p.1) (g (horizontalPairChart p.1) + p.2)
  rw [hP, h.1, h.2, add_sub_cancel_left]

private theorem epigraphPhysicalChart_horizontalCoordinates (a : Point) (A : Point ≃ₗᵢ[ℝ] Point)
    (g : Plane → ℝ) (hg : Continuous g) (x : Point) :
    ((epigraphPhysicalChart a A g hg).symm x).1 = ((A (x - a)) 0, (A (x - a)) 1) := by
  let F := epigraphPhysicalChart a A g hg
  let p := F.symm x
  have hP := epigraphPhysicalChart_rotatedCoordinates a A g hg p
  change A (F (F.symm x) - a) = _ at hP
  rw [F.apply_symm_apply] at hP
  have hY := (planeLineChart_coordinates (horizontalPairChart p.1) (g (horizontalPairChart p.1) + p.2)).1
  rw [← hP, horizontalPart_coordinate] at hY
  apply Prod.ext
  · exact (congrArg (fun y : Plane => y 0) hY).symm
  · exact (congrArg (fun y : Plane => y 1) hY).symm

private theorem epigraphPhysicalChart_smooth (a : Point) (A : Point ≃ₗᵢ[ℝ] Point)
    (g : Plane → ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (epigraphPhysicalChart a A g hg.continuous : EpigraphCoordinates → Point) := by
  have hY : ContDiff ℝ ∞ (horizontalPairChart : (ℝ × ℝ) → Plane) := by
    apply (contDiff_piLp 2).2
    intro i
    fin_cases i
    · exact contDiff_fst
    · exact contDiff_snd
  have hH := hY.comp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : EpigraphCoordinates → ℝ × ℝ))
  have hV := (hg.comp hH).add (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : EpigraphCoordinates → ℝ))
  change ContDiff ℝ ∞ (fun p : EpigraphCoordinates => a +
    A.symm (planeLineCoordinates (horizontalPairChart p.1, g (horizontalPairChart p.1) + p.2)))
  exact contDiff_const.add (A.symm.contDiff.comp (planeLineCoordinates.contDiff.comp (hH.prodMk hV)))

private theorem epigraphPhysicalChart_inverse_smooth (a : Point) (A : Point ≃ₗᵢ[ℝ] Point)
    (g : Plane → ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ ((epigraphPhysicalChart a A g hg.continuous).symm : Point → EpigraphCoordinates) := by
  have hz : ContDiff ℝ ∞ (fun x : Point => A (x-a)) := A.contDiff.comp (contDiff_id.sub contDiff_const)
  have hH : ContDiff ℝ ∞ (fun x : Point => horizontalPart (A (x-a))) :=
    contDiff_fst.comp (planeLineCoordinates.symm.contDiff.comp hz)
  have hI (i : Fin 3) : ContDiff ℝ ∞ (fun x : Point => (A (x-a)) i) :=
    (contDiff_piLp_apply 2).comp hz
  have hD := ((hI 0).prodMk (hI 1)).prodMk ((hI 2).sub (hg.comp hH))
  convert hD using 1
  funext x
  exact Prod.ext (epigraphPhysicalChart_horizontalCoordinates a A g hg.continuous x)
    (epigraphPhysicalChart_normalCoordinate a A g hg.continuous x)

private theorem epigraphPhysicalChart_normalCoordinate_dist (a : Point) (A : Point ≃ₗᵢ[ℝ] Point)
    (g : Plane → ℝ) (hg : Continuous g) {R : ℝ} {L : ℝ≥0} (hL : LipschitzOnWith L g (ball 0 R))
    {x y : Point} (hx : x ∈ ball a R) (hy : y ∈ ball a R) :
    dist ((epigraphPhysicalChart a A g hg).symm x).2 ((epigraphPhysicalChart a A g hg).symm y).2 ≤
      (1 + (L : ℝ)) * dist x y := by
  let u := A (x-a)
  let v := A (y-a)
  have hu : horizontalPart u ∈ ball 0 R := mem_ball_zero_iff.2 ((horizontalPart_norm_le _).trans_lt (by
    rw [show u = A (x-a) from rfl, A.norm_map, ← dist_eq_norm]; exact hx))
  have hv : horizontalPart v ∈ ball 0 R := mem_ball_zero_iff.2 ((horizontalPart_norm_le _).trans_lt (by
    rw [show v = A (y-a) from rfl, A.norm_map, ← dist_eq_norm]; exact hy))
  have hD : ‖u-v‖ = dist x y := by
    rw [show u - v = A ((x-a)-(y-a)) from (A.map_sub _ _).symm, A.norm_map,
      show x - a - (y - a) = x - y by abel, dist_eq_norm]
  have hProj : dist (horizontalPart u) (horizontalPart v) ≤ dist x y := by
    rw [dist_eq_norm, ← show horizontalPart (u-v) = horizontalPart u - horizontalPart v from
      congrArg Prod.fst (planeLineCoordinates.symm.map_sub u v), ← hD]
    exact horizontalPart_norm_le _
  have hVertical : dist (u 2) (v 2) ≤ dist x y := by
    rw [← hD, dist_eq_norm]
    exact PiLp.norm_apply_le (u-v) 2
  have hG := (hL.dist_le_mul _ hu _ hv).trans (mul_le_mul_of_nonneg_left hProj L.coe_nonneg)
  rw [epigraphPhysicalChart_normalCoordinate, epigraphPhysicalChart_normalCoordinate]
  change dist (u 2 - g (horizontalPart u)) (v 2 - g (horizontalPart v)) ≤ _
  have he : u 2 - g (horizontalPart u) - (v 2 - g (horizontalPart v)) =
      (u 2 - v 2) - (g (horizontalPart u) - g (horizontalPart v)) := by ring
  rw [dist_eq_norm, he]
  have hVN : ‖u 2 - v 2‖ ≤ dist x y := by simpa only [dist_eq_norm] using hVertical
  have hGN : ‖g (horizontalPart u) - g (horizontalPart v)‖ ≤ (L : ℝ) * dist x y := by
    simpa only [dist_eq_norm] using hG
  exact ((norm_sub_le _ _).trans (add_le_add hVN hGN)).trans_eq (by ring)

private theorem epigraphPhysicalChart_inverse_lipschitzOn_ball (a : Point) (A : Point ≃ₗᵢ[ℝ] Point)
    (g : Plane → ℝ) (hg : Continuous g) {R : ℝ} {L : ℝ≥0} (hL : LipschitzOnWith L g (ball 0 R)) :
    LipschitzOnWith (1+L) (epigraphPhysicalChart a A g hg).symm (ball a R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hN := epigraphPhysicalChart_normalCoordinate_dist a A g hg hL hx hy
  have hR : dist x y ≤ (1 + (L : ℝ)) * dist x y := by nlinarith [L.coe_nonneg, dist_nonneg (x := x) (y := y)]
  have hCoord (i : Fin 3) : dist ((A (x-a)) i) ((A (y-a)) i) ≤ dist x y := by
    rw [dist_eq_norm, dist_eq_norm, ← A.norm_map (x-y),
      show A (x-y) = A (x-a) - A (y-a) by rw [← A.map_sub]; congr 1; abel]
    exact PiLp.norm_apply_le (A (x-a) - A (y-a)) i
  rw [NNReal.coe_add, NNReal.coe_one, Prod.dist_eq]
  apply max_le _ hN
  rw [epigraphPhysicalChart_horizontalCoordinates, epigraphPhysicalChart_horizontalCoordinates, Prod.dist_eq]
  exact (max_le (hCoord 0) (hCoord 1)).trans hR


private theorem planar_smooth_lipschitzOn_ball (g : Plane → ℝ) (hg : ContDiff ℝ ∞ g) (R : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L g (ball 0 R) := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Plane) R).exists_bound_of_continuousOn
    (hg.continuous_fderiv (by simp)).continuousOn
  let L := Real.toNNReal (max B 0)
  refine ⟨L, (convex_ball _ _).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    (fun x _ => hg.differentiable (by simp) x) ?_⟩
  intro x hx
  change ‖fderiv ℝ g x‖ ≤ (L : ℝ)
  rw [show (L : ℝ) = max B 0 from Real.coe_toNNReal _ (le_max_right _ _)]
  exact (hB x (ball_subset_closedBall hx)).trans (le_max_left _ _)

private theorem normal_height_le_boundary_distance {U : Set Point} (hU : IsOpen U)
    (a : Point) (ha : a ∈ frontier U) (A : Point ≃ₗᵢ[ℝ] Point) (g : Plane → ℝ) (hg : Continuous g)
    {R : ℝ} (hR : 0 < R) {L : ℝ≥0} (hL : LipschitzOnWith L g (ball 0 R))
    (hEpi : U ∩ ball a R =
      {x | let z := A (x-a); g (WithLp.toLp 2 ![z 0,z 1]) < z 2} ∩ ball a R)
    {p : EpigraphCoordinates} (hPos : 0 < p.2) (hSmall : p.2 ≤ R/4)
    (hP : epigraphPhysicalChart a A g hg p ∈ ball a (R/4)) :
    (1 / (1 + (L : ℝ))) * p.2 ≤ infDist (epigraphPhysicalChart a A g hg p) (frontier U) := by
  let F := epigraphPhysicalChart a A g hg
  let x := F p
  have hx : x ∈ ball a R := ball_subset_ball (by linarith only [hR]) hP
  have hL1 : 0 < 1 + (L : ℝ) := by positivity
  have hFrac : (1 / (1 + (L : ℝ))) * p.2 = p.2 / (1 + (L : ℝ)) := by ring
  rw [hFrac]
  apply (le_infDist (show (frontier U).Nonempty from ⟨a,ha⟩)).2
  intro y hy
  by_cases hY : y ∈ ball a R
  · have hY' : F (F.symm y) ∈ ball a R := by simpa only [F.apply_symm_apply] using hY
    have hy' : F (F.symm y) ∈ frontier U := by simpa only [F.apply_symm_apply] using hy
    have hz : (F.symm y).2 = 0 := (epigraphChart_mem_frontier_of_ball hU a A g hg R hEpi hY').1 hy'
    have hDist := epigraphPhysicalChart_normalCoordinate_dist a A g hg hL hx hY
    change dist (F.symm (F p)).2 (F.symm y).2 ≤ (1 + (L : ℝ)) * dist x y at hDist
    rw [F.symm_apply_apply, hz, Real.dist_eq, sub_zero, abs_of_nonneg hPos.le] at hDist
    exact (div_le_iff₀ hL1).2 (hDist.trans_eq (mul_comm _ _))
  · have hyR : R ≤ dist y a := le_of_not_gt (fun h => hY (mem_ball.2 h))
    have hxR : dist x a < R/4 := hP
    have hTri := dist_triangle_left y a x
    have hPdist : p.2 ≤ dist x y := by linarith only [hSmall, hyR, hxR, hTri, hR]
    have hDiv : p.2 / (1 + (L : ℝ)) ≤ p.2 :=
      div_le_self hPos.le (le_add_of_nonneg_right L.coe_nonneg)
    exact hDiv.trans hPdist

/-- Each point of a smooth boundary has a volume-preserving rectangular
chart whose normal coordinate controls distance in the original domain. -/
theorem IsSmoothDomain.exists_epigraph_box {U : Set Point} (hU : IsSmoothDomain U)
    {a : Point} (ha : a ∈ frontier U) :
    ∃ B : SmoothDomainEpigraphBox U, B.chart (0 : EpigraphCoordinates) = a := by
  obtain ⟨R,A,g,hR,hg,hg0,hEpi⟩ := hU.2 a ha
  obtain ⟨L,hL⟩ := planar_smooth_lipschitzOn_ball g hg R
  have hL1 : 0 < 1 + (L : ℝ) := by positivity
  let b := R / (16 * (1 + (L : ℝ)))
  have hb : 0 < b := div_pos hR (mul_pos (by norm_num) hL1)
  have hbEq : 16 * (1 + (L : ℝ)) * b = R := by
    rw [show b = R / (16 * (1 + (L : ℝ))) from rfl, mul_comm, div_mul_cancel₀ _ (by positivity)]
  have hbR : b ≤ R/4 := by nlinarith only [hbEq, mul_nonneg L.coe_nonneg hb.le, hb]
  have h2b : 2 * b < R := by linarith only [hbR, hR]
  let F := epigraphPhysicalChart a A g hg.continuous
  have hPos (p : EpigraphCoordinates) (hp : p ∈ closedBall (0 : EpigraphCoordinates) b) :
      F p ∈ ball a (R/4) := by
    let y := horizontalPairChart p.1
    have hPy : ‖y‖ ≤ 2*b := (horizontalPairChart_norm_le p.1).trans
      (mul_le_mul_of_nonneg_left ((norm_fst_le p).trans (mem_closedBall_zero_iff.1 hp)) (by norm_num))
    have hPt : |p.2| ≤ b := (show ‖p.2‖ ≤ ‖p‖ from norm_snd_le p).trans
      (mem_closedBall_zero_iff.1 hp)
    have hgB : |g y| ≤ (L : ℝ) * (2*b) := by
      have h := hL.dist_le_mul y (mem_ball_zero_iff.2 (hPy.trans_lt h2b)) 0 (mem_ball_self hR)
      rw [hg0, Real.dist_eq, sub_zero, dist_zero_right] at h
      exact h.trans (mul_le_mul_of_nonneg_left hPy L.coe_nonneg)
    apply mem_ball.2
    have h := epigraphPhysicalChart_norm_from_center a A g hg.continuous p
    have h' := (abs_add_le (g y) p.2).trans (add_le_add hgB hPt)
    have hBound := h.trans (add_le_add hPy h')
    nlinarith only [hBound, hbEq, mul_nonneg L.coe_nonneg hb.le, hb]
  have hMem (p : EpigraphCoordinates) (hp : p ∈ closedBall (0 : EpigraphCoordinates) b) :
      F p ∈ U ↔ 0 < p.2 :=
    epigraphChart_mem_domain_of_ball a A g hg.continuous R hEpi
      (ball_subset_ball (by linarith only [hR]) (hPos p hp))
  have hFront (y : ℝ × ℝ) (hy : ‖y‖ ≤ b) : F (y,0) ∈ frontier U := by
    have h0 : (y, (0 : ℝ)) ∈ closedBall (0 : EpigraphCoordinates) b :=
      mem_closedBall_zero_iff.2 (by rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]; exact hy)
    exact (epigraphChart_mem_frontier_of_ball hU.1.1 a A g hg.continuous R hEpi
      (ball_subset_ball (by linarith only [hR]) (hPos (y,0) h0))).2 rfl
  have hDist (p : EpigraphCoordinates) (hp : p ∈ closedBall (0 : EpigraphCoordinates) b)
      (hp2 : 0 < p.2) :
      (1 / (1 + (L : ℝ))) * p.2 ≤ infDist (F p) (frontier U) :=
    normal_height_le_boundary_distance hU.1.1 a ha A g hg.continuous hR hL hEpi hp2
      ((le_abs_self p.2).trans ((norm_snd_le p).trans ((mem_closedBall_zero_iff.1 hp).trans hbR)))
      (hPos p hp)
  obtain ⟨hν, hAffine⟩ := epigraphPhysicalChart_affine_normal a A g hg.continuous
  refine ⟨⟨b,hb,F,epigraphPhysicalChart_volume a A g hg.continuous, 3+2*L,
    epigraphPhysicalChart_lipschitzOn_box a A g hg.continuous h2b hL,
    A.symm (planeLineChart (0,1)),hν,hAffine,hMem,hFront,1/(1+(L:ℝ)),div_pos zero_lt_one hL1,hDist,
    epigraphPhysicalChart_smooth a A g hg, epigraphPhysicalChart_inverse_smooth a A g hg, 1+L,
    (epigraphPhysicalChart_inverse_lipschitzOn_ball a A g hg.continuous hL).mono ?_, ?_⟩,?_⟩
  · rintro _ ⟨p,hp,rfl⟩
    exact ball_subset_ball (by linarith only [hR]) (hPos p hp)
  · intro p hp
    exact epigraphChart_mem_frontier_of_ball hU.1.1 a A g hg.continuous R hEpi
      (ball_subset_ball (by linarith only [hR]) (hPos p hp))
  ·
    change F ((0 : ℝ × ℝ),(0 : ℝ)) = a
    have hY0 : horizontalPairChart (0 : ℝ × ℝ) = (0 : Plane) := by
      apply PiLp.ext
      intro i
      fin_cases i <;> rfl
    rw [epigraphPhysicalChart_apply, hY0, hg0, add_zero]
    change a + A.symm (planeLineCoordinates (0,0)) = a
    rw [show ((0 : Plane),(0 : ℝ)) = (0 : Plane × ℝ) from rfl, map_zero, map_zero, add_zero]

/-- A finite family of the actual epigraph boxes covers the entire
physical collar of sufficiently small distance from the boundary. -/
theorem IsSmoothDomain.exists_finite_epigraph_boxes {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ (B : frontier U → SmoothDomainEpigraphBox U) (I : Finset (frontier U)) (δ : ℝ), 0 < δ ∧
      ∀ x ∈ U, infDist x (frontier U) < δ →
        ∃ i ∈ I, ∃ p ∈ ball (0 : EpigraphCoordinates) (B i).radius, 0 < p.2 ∧ (B i).chart p = x := by
  classical
  have hBox (a : frontier U) := hU.exists_epigraph_box a.property
  choose B hCenter using hBox
  let W (a : frontier U) := (B a).chart '' ball (0 : EpigraphCoordinates) (B a).radius
  have hW (a : frontier U) : IsOpen (W a) := (B a).chart.isOpenMap _ isOpen_ball
  have hCover : frontier U ⊆ ⋃ a : frontier U, W a := by
    intro x hx
    let a : frontier U := ⟨x,hx⟩
    exact mem_iUnion.2 ⟨a,⟨0,mem_ball_self (B a).radius_pos,hCenter a⟩⟩
  have hFr : IsCompact (frontier U) := hU.1.2.2.isCompact_closure.of_isClosed_subset
    isClosed_frontier frontier_subset_closure
  obtain ⟨I,hI⟩ := hFr.elim_finite_subcover W hW hCover
  have hOpen : IsOpen (⋃ i ∈ I,W i) := isOpen_iUnion fun i => isOpen_iUnion fun _ => hW i
  obtain ⟨δ,hδ,hδCover⟩ := hFr.exists_thickening_subset_open hOpen hI
  have hProper : U ≠ univ := fun h => NormedSpace.unbounded_univ ℝ Point (h ▸ hU.1.2.2)
  have hNonempty : (frontier U).Nonempty := nonempty_frontier_iff.2 ⟨hU.1.2.1.1,hProper⟩
  refine ⟨B,I,δ,hδ,?_⟩
  intro x hxU hxDist
  obtain ⟨i,hi,hx⟩ := mem_iUnion₂.1 (hδCover ((mem_thickening_iff_infDist_lt hNonempty).2 hxDist))
  obtain ⟨p,hp,hpx⟩ := hx
  have hp' := (B i).mem_domain p (ball_subset_closedBall hp)
  rw [hpx] at hp'
  exact ⟨i,hi,p,hp,hp'.1 hxU,hpx⟩


/-- The max-norm closed ball is the ordinary closed rectangle in its
three scalar coordinates. -/
theorem epigraphCoordinates_mem_closedBall_iff {p : EpigraphCoordinates} {b : ℝ} :
    p ∈ closedBall (0 : EpigraphCoordinates) b ↔
      p ∈ (Icc (-b) b ×ˢ Icc (-b) b) ×ˢ Icc (-b) b := by
  simp only [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_le, mem_prod, mem_Icc]

/-- For a point on a positive normal segment, the original boundary distance
is at most its chart height. -/
theorem SmoothDomainEpigraphBox.distance_le {U : Set Point} (B : SmoothDomainEpigraphBox U)
    {p : EpigraphCoordinates} (hp : p ∈ closedBall (0 : EpigraphCoordinates) B.radius) (hPos : 0 ≤ p.2) :
    infDist (B.chart p) (frontier U) ≤ p.2 := by
  have hY : ‖p.1‖ ≤ B.radius := (norm_fst_le p).trans (mem_closedBall_zero_iff.1 hp)
  have hFront := B.wall p.1 hY
  calc
    _ ≤ dist (B.chart p) (B.chart (p.1,0)) := infDist_le_dist_of_mem hFront
    _ = _ := by
      rw [show B.chart p = B.chart (p.1,0) + p.2 • B.direction from B.affineNormal p.1 p.2,
        dist_eq_norm, add_comm, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg hPos,
        B.direction_norm, mul_one]

end Thesis
