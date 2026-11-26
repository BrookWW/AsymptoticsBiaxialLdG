module

public import Thesis.Variational.SmoothWallGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Interior balls and uniform volume density at the physical wall. -/

public section

open MeasureTheory Metric Set Topology
open scoped ENNReal NNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem exists_local_interior_ball_of_epigraph
    {U : Set Point} {a : Point} {R : ℝ} (hR : 0 < R)
    (A : Point ≃ₗᵢ[ℝ] Point) (g : Plane → ℝ) (L : ℝ≥0)
    (hL : LipschitzOnWith L g (ball 0 R))
    (hChart : U ∩ ball a R =
      {y | let z := A (y - a); g (WithLp.toLp 2 ![z 0, z 1]) < z 2} ∩ ball a R) :
    ∃ α : ℝ, 0 < α ∧ ∀ x ∈ closure U ∩ ball a (R / 4), ∀ r : ℝ, 0 < r → r ≤ R / 4 →
      ∃ y : Point, ball y (α * r) ⊆ U ∩ ball x r := by
  let E : Point ≃L[ℝ] Plane × EuclideanSpace ℝ (Fin 1) :=
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let P : Point →L[ℝ] Plane := (ContinuousLinearMap.fst ℝ Plane (EuclideanSpace ℝ (Fin 1))).comp
    E.toContinuousLinearMap
  have hP (z : Point) : P z = WithLp.toLp 2 ![z 0, z 1] := by
    ext i
    fin_cases i <;> rfl
  have hPnorm (z : Point) : ‖P z‖ ≤ ‖z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_three]
    have h0 : (P z) 0 = z 0 := congrArg (fun p : Plane => p 0) (hP z)
    have h1 : (P z) 1 = z 1 := congrArg (fun p : Plane => p 1) (hP z)
    rw [h0, h1]
    linarith only [sq_nonneg (z 2)]
  have hPaxis : P (axis 2) = 0 := by
    rw [hP]
    ext i
    fin_cases i <;> simp [axis]
  let Z (y : Point) := A (y - a)
  let F (y : Point) := g (P (Z y)) - Z y 2
  have hZ : Continuous Z := A.continuous.comp (continuous_id.sub continuous_const)
  have hPMap : MapsTo (fun y => P (Z y)) (ball a R) (ball 0 R) := by
    intro y hy
    rw [mem_ball, dist_zero_right]
    exact (hPnorm _).trans_lt (by dsimp only [Z]; rwa [A.norm_map, ← dist_eq_norm])
  have hF : ContinuousOn F (ball a R) :=
    (hL.continuousOn.comp (P.continuous.comp hZ).continuousOn hPMap).sub
      ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp hZ).continuousOn
  have hChart' (y : Point) (hy : y ∈ ball a R) : y ∈ U ↔ F y < 0 := by
    constructor
    · intro h
      have hyU : y ∈ U ∩ ball a R := ⟨h,hy⟩
      rw [hChart] at hyU
      have hE := hyU.1
      change g (WithLp.toLp 2 ![(Z y) 0,(Z y) 1]) < Z y 2 at hE
      rw [← hP (Z y)] at hE
      exact sub_neg.2 hE
    · intro h
      have hyU : y ∈ {v | let z := A (v - a); g (WithLp.toLp 2 ![z 0,z 1]) < z 2} ∩ ball a R :=
        ⟨by
          change g (WithLp.toLp 2 ![(Z y) 0,(Z y) 1]) < Z y 2
          rw [← hP (Z y)]
          exact sub_neg.1 h, hy⟩
      rw [← hChart] at hyU
      exact hyU.1
  have hClosedSide (x : Point) (hx : x ∈ closure U) (hxR : x ∈ ball a R) :
      g (P (Z x)) ≤ Z x 2 := by
    have hNx := isOpen_ball.mem_nhds hxR
    have hFx : ContinuousAt F x := (hF x hxR).continuousAt hNx
    by_contra! hPos
    have hPos' : 0 < F x := sub_pos.2 hPos
    have hEvt : ∀ᶠ y in 𝓝 x, 0 < F y := continuousAt_const.eventually_lt hFx hPos'
    obtain ⟨y,hy,hyU⟩ := mem_closure_iff_nhds.mp hx _ (Filter.inter_mem hNx hEvt)
    exact (not_lt_of_ge (le_of_lt hy.2)) ((hChart' y hy.1).1 hyU)
  let α := (4 * (1 + (L : ℝ)))⁻¹
  have hL₀ : 0 ≤ (L : ℝ) := L.coe_nonneg
  have hα : 0 < α := inv_pos.mpr (by positivity)
  have hα₁ : α ≤ 1 / 4 := by
    dsimp only [α]
    rw [one_div]
    exact (inv_le_inv₀ (by positivity) (by norm_num)).2 (by linarith only [hL₀])
  refine ⟨α,hα,?_⟩
  intro x hx r hr hrR
  have hxR : x ∈ ball a R := (ball_subset_ball (by linarith only [hR])) hx.2
  let b := A.symm (axis 2)
  let y := x + (r / 2) • b
  have hb : ‖b‖ = 1 := by simp [b, axis]
  have hyx : dist y x = r / 2 := by
    dsimp only [y]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity), hb, mul_one]
  have hyZ : Z y = Z x + (r / 2) • axis 2 := by
    dsimp only [Z, y, b]
    rw [show x + (r / 2) • A.symm (axis 2) - a = x-a+(r/2) • A.symm (axis 2) by abel,
      map_add, map_smul, A.apply_symm_apply]
  refine ⟨y,?_⟩
  intro w hw
  have hErr : ‖A (w - y)‖ < α * r := by simpa only [A.norm_map, dist_eq_norm] using (mem_ball.mp hw)
  have hwx : w ∈ ball x r := by
    apply mem_ball.mpr
    have hT := dist_triangle w y x
    rw [hyx] at hT
    have hw' := mem_ball.mp hw
    have hg : α * r ≤ r/4 := (mul_le_mul_of_nonneg_right hα₁ hr.le).trans_eq (by ring)
    linarith
  have hwR : w ∈ ball a R := by
    apply mem_ball.mpr
    linarith only [dist_triangle w x a, mem_ball.mp hwx, mem_ball.mp hx.2, hrR, hR]
  have hZErr : Z w = Z x + (r / 2) • axis 2 + A (w - y) := by
    rw [← hyZ]
    change A (w-a) = A (y-a) + A (w-y)
    rw [← map_add]
    congr 1
    abel
  have hHoriz : P (Z w) - P (Z x) = P (A (w-y)) := by
    rw [hZErr,map_add,map_add,map_smul,hPaxis,smul_zero,add_zero,add_sub_cancel_left]
  have hVert : Z w 2 = Z x 2 + r/2 + (A (w-y)) 2 := by
    rw [hZErr]
    simp [axis, smul_eq_mul]
  have hVertLower : -(α * r) < (A (w-y)) 2 := by
    have h := (PiLp.norm_apply_le (A (w-y)) (2 : Fin 3)).trans_lt hErr
    rw [Real.norm_eq_abs, abs_lt] at h
    exact h.1
  have hSlope := hL.dist_le_mul _ (hPMap hwR) _ (hPMap hxR)
  simp only [dist_eq_norm, Real.norm_eq_abs, hHoriz] at hSlope
  have hg : g (P (Z w)) - g (P (Z x)) ≤ (L : ℝ) * (α * r) :=
    (le_abs_self _).trans (hSlope.trans (mul_le_mul_of_nonneg_left ((hPnorm _).trans hErr.le) hL₀))
  have hMargin : (L : ℝ) * (α * r) + α * r = r/4 := by
    dsimp only [α]
    field_simp [show (1 + (L : ℝ)) ≠ 0 from (by positivity : (0 : ℝ) < 1 + (L : ℝ)).ne']
    ring
  have hStrict : g (P (Z w)) < Z w 2 := by
    linarith only [hClosedSide x hx.1 hxR, hg, hVert, hVertLower, hMargin, hr]
  exact ⟨(hChart' w hwR).2 (sub_neg.2 hStrict), hwx⟩

/-- Every small ball centered on the closure contains a ball of fixed
relative radius within the actual open domain. -/
theorem IsSmoothDomain.exists_uniform_interior_balls
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ α R : ℝ, 0 < α ∧ 0 < R ∧ ∀ x ∈ closure U, ∀ r : ℝ, 0 < r → r ≤ R →
      ∃ y : Point, ball y (α * r) ⊆ U ∩ ball x r := by
  classical
  have hLocal (a : closure U) : ∃ R α : ℝ, 0 < R ∧ 0 < α ∧
      ∀ x ∈ closure U ∩ ball (a : Point) R, ∀ r : ℝ, 0 < r → r ≤ R →
        ∃ y : Point, ball y (α * r) ⊆ U ∩ ball x r := by
    by_cases ha : (a : Point) ∈ U
    · obtain ⟨R,hR,hBall⟩ := Metric.isOpen_iff.mp hU.1.1 (a : Point) ha
      refine ⟨R / 2, 1/2, half_pos hR, by norm_num, ?_⟩
      intro x hx r hr hsmall
      refine ⟨x,?_⟩
      intro w hw
      have hw' := mem_ball.mp hw
      have hx' := mem_ball.mp hx.2
      exact ⟨hBall (mem_ball.mpr (by linarith only [dist_triangle w x (a : Point),hw',hx',hsmall,hR])),
        mem_ball.mpr (by linarith only [hw',hr])⟩
    · have ha' : (a : Point) ∈ frontier U := by
        rw [frontier, hU.1.1.interior_eq]
        exact ⟨a.property,ha⟩
      obtain ⟨R,A,g,L,hR,hL,_,hChart⟩ := hU.hasLocallyLipschitzBoundary a ha'
      obtain ⟨α,hα,hBalls⟩ := exists_local_interior_ball_of_epigraph hR A g L hL hChart
      exact ⟨R/4,α,div_pos hR (by norm_num),hα,hBalls⟩
  choose R α hR hα hBalls using hLocal
  let V (a : closure U) := ball (a : Point) (R a)
  have hCover : closure U ⊆ ⋃ a : closure U, V a :=
    fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (hR _)⟩
  obtain ⟨I,hI⟩ := hU.1.2.2.isCompact_closure.elim_finite_subcover V (fun _ => isOpen_ball) hCover
  have hI₀ : I.Nonempty := by
    obtain ⟨x,hx⟩ := hU.1.2.1.1
    obtain ⟨a,ha,_⟩ := mem_iUnion₂.mp (hI (subset_closure hx))
    exact ⟨a,ha⟩
  let r₀ := I.inf' hI₀ R
  let α₀ := I.inf' hI₀ α
  have hr₀ : 0 < r₀ := (Finset.lt_inf'_iff hI₀).2 fun i _ => hR i
  have hα₀ : 0 < α₀ := (Finset.lt_inf'_iff hI₀).2 fun i _ => hα i
  refine ⟨α₀,r₀,hα₀,hr₀,?_⟩
  intro x hx r hr hsmall
  obtain ⟨a,ha,hxV⟩ := mem_iUnion₂.mp (hI hx)
  obtain ⟨y,hy⟩ := hBalls a x ⟨hx,hxV⟩ r hr (hsmall.trans (Finset.inf'_le R ha))
  exact ⟨y,(ball_subset_ball (mul_le_mul_of_nonneg_right (Finset.inf'_le α ha) hr.le)).trans hy⟩

/-- Uniform lower Euclidean volume density for the bounded smooth domain. -/
theorem IsSmoothDomain.exists_uniform_volume_density
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ (C : ℝ≥0∞) (R : ℝ), 0 < C ∧ C < ⊤ ∧ 0 < R ∧
      ∀ x ∈ closure U, ∀ r : ℝ, 0 < r → r ≤ R →
        C * ENNReal.ofReal (r ^ 3) ≤ volume (U ∩ ball x r) := by
  obtain ⟨α,R,hα,hR,hBalls⟩ := hU.exists_uniform_interior_balls
  let V := volume (ball (0 : Point) 1)
  let C := ENNReal.ofReal (α^3) * V
  have hV : 0 < V := measure_ball_pos volume _ zero_lt_one
  have hC : 0 < C := ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (pow_pos hα _)).ne' hV.ne'
  have hC₁ : C < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  refine ⟨C,R,hC,hC₁,hR,?_⟩
  intro x hx r hr hsmall
  obtain ⟨y,hy⟩ := hBalls x hx r hr hsmall
  calc
    C * ENNReal.ofReal (r ^ 3) = volume (ball y (α*r)) := by
      rw [Measure.addHaar_ball_of_pos volume y (mul_pos hα hr)]
      simp only [Point, finrank_euclideanSpace, Fintype.card_fin, mul_pow]
      rw [ENNReal.ofReal_mul (show 0 ≤ α ^ 3 from pow_nonneg hα.le _)]
      dsimp only [C,V]
      ac_rfl
    _ ≤ _ := measure_mono hy

end Thesis

end
