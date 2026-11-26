module

public import Thesis.Variational.SmoothWallGeometry
import Thesis.Variational.BoundaryNormalEnergy
import Mathlib.Analysis.Calculus.MeanValue

/-! A uniform exterior tangent-ball radius for the actual smooth domain. -/

public section

noncomputable section

open Filter Metric Set
open scoped ContDiff RealInnerProductSpace Topology

namespace Thesis

local instance exteriorL4HessianNormed : NormedAddCommGroup (Point →L[ℝ] Point →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

private theorem scalar_first_order_remainder_bound {f : Point → ℝ}
    (hf : ContDiff ℝ ∞ f) {p x : Point} {M : ℝ} (hM : 0 ≤ M)
    (hDer : ∀ y ∈ closedBall p (dist x p), ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M) :
    |f x-f p - fderiv ℝ f p (x-p)| ≤ M * ‖x-p‖^2 := by
  let K := closedBall p (dist x p)
  let L := fderiv ℝ f p
  let g (y : Point) := f y - L (y-p)
  have hp : p ∈ K := mem_closedBall_self dist_nonneg
  have hx : x ∈ K := mem_closedBall.2 le_rfl
  have hnorm (y : Point) (hy : y ∈ K) : ‖fderiv ℝ f y - L‖ ≤ M * dist x p := by
    have h := (convex_closedBall p (dist x p)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z)
      hDer hp hy
    exact h.trans (mul_le_mul_of_nonneg_left (by
      rw [← dist_eq_norm]
      exact mem_closedBall.1 hy) hM)
  have hG (y : Point) : fderiv ℝ g y = fderiv ℝ f y - L := by
    have hLin : HasFDerivAt (fun x => L (x-p)) L y := by
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
        (L.hasFDerivAt (x := y-p)).comp y ((hasFDerivAt_id y).sub_const p)
    exact ((hf.differentiable (by simp) y).hasFDerivAt.sub hLin).fderiv
  have hGD (y : Point) : DifferentiableAt ℝ g y :=
    (hf.differentiable (by simp) y).sub
      (L.differentiableAt.comp y ((differentiableAt_id (x := y)).sub_const _))
  have h := (convex_closedBall p (dist x p)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hGD y) (fun y hy => by rw [hG]; exact hnorm y hy) hp hx
  have hEq : g x - g p = f x - f p - L (x-p) := by
    dsimp only [g]
    rw [sub_self, map_zero, sub_zero]
    ring
  rw [hEq, Real.norm_eq_abs, dist_eq_norm, mul_assoc, ← pow_two] at h
  exact h

/-- Every physical wall point admits exterior tangent balls of all
sufficiently small radii, with one radius for the fixed domain. -/
theorem IsSmoothDomain.exists_uniform_exterior_tangent_balls {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ R : ℝ, 0 < R ∧ ∀ p ∈ frontier U, ∃ ν : Point, ‖ν‖ = 1 ∧
      ∀ ρ ∈ Ioo 0 R,
        (∀ y ∈ closure U, ρ ≤ ‖y - (p+ρ • ν)‖) ∧
        ∀ y ∈ U, ρ < ‖y - (p+ρ • ν)‖ := by
  classical
  let K := frontier U
  have hK : IsCompact K := hU.1.2.2.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hLocal (a : K) := exists_local_smooth_defining_function_and_unit_direction hU a.property
  choose R φ n t w hR hφ hn hDef hw hDir hT hGrad hNor using hLocal
  have hCont (a : K) : Continuous (fderiv ℝ (fderiv ℝ (φ a))) :=
    ((hφ a).fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
  have hLocalM (a : K) : ∃ M₀ : ℝ,
      ∀ x ∈ closedBall (a : Point) (R a), ‖fderiv ℝ (fderiv ℝ (φ a)) x‖ ≤ M₀ :=
    (isCompact_closedBall (a : Point) (R a)).exists_bound_of_continuousOn (hCont a).continuousOn
  choose M₀ hM₀ using hLocalM
  let W (a : K) := ball (a : Point) (R a/2)
  have hCover : K ⊆ ⋃ a : K, W a := fun x hx =>
    mem_iUnion.2 ⟨⟨x,hx⟩, mem_ball_self (half_pos (hR ⟨x,hx⟩))⟩
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover W (fun _ => isOpen_ball) hCover
  have hSmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ a ∈ I, s < R a/2 :=
    (eventually_all_finset I).2 fun a _ => nhdsWithin_le_nhds (Iio_mem_nhds (half_pos (hR a)))
  have hPos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  obtain ⟨δ,hδ,hδR⟩ := (hPos.and hSmall).exists
  let M := ∑ i ∈ I, max (M₀ i) 0
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => le_max_right _ _
  let S := min (δ/4) ((4*(M+1))⁻¹)
  refine ⟨S, lt_min (by positivity) (by positivity), ?_⟩
  intro p hp
  obtain ⟨i,hi,hpI⟩ := mem_iUnion₂.1 (hI hp)
  have hpN : dist p (i : Point) < R i/2 := hpI
  have hBall : closedBall p δ ⊆ ball (i : Point) (R i) := by
    intro x hx
    apply mem_ball.2
    have hd := mem_closedBall.1 hx
    linarith only [dist_triangle x p (i : Point), hd, hpN, hδR i hi]
  have hpB : p ∈ ball (i : Point) (R i) := hBall (mem_closedBall_self hδ.le)
  let ν := n i p
  have hν : ‖ν‖ = 1 := (hNor i p ⟨hp,hpB⟩).2.1
  have hφ₀ : φ i p = 0 := localDefiningFunction_eq_zero_on_frontier hU.1.1
    (hφ i).continuous.continuousOn (hDef i) hp hpB
  have hN (x : Point) (hx : x ∈ closure U) (hxd : dist x p ≤ δ) :
      inner ℝ ν (x-p) ≤ M * ‖x-p‖^2 := by
    have hxb := hBall (mem_closedBall.2 hxd)
    have hxφ : φ i x ≤ 0 := by
      by_cases hU' : x ∈ U
      · have hU'' : x ∈ U ∩ ball (i : Point) (R i) := ⟨hU',hxb⟩
        rw [hDef i] at hU''
        exact hU''.1.le
      · have hxWall : x ∈ frontier U := by rw [frontier,hU.1.1.interior_eq]; exact ⟨hx,hU'⟩
        exact (localDefiningFunction_eq_zero_on_frontier hU.1.1
          (hφ i).continuous.continuousOn (hDef i) hxWall hxb).le
    have hReq (y : Point) (hy : y ∈ closedBall p (dist x p)) : ‖fderiv ℝ (fderiv ℝ (φ i)) y‖ ≤ M := by
      have hy' := hBall (closedBall_subset_closedBall hxd hy)
      exact ((hM₀ i y (ball_subset_closedBall hy')).trans (le_max_left _ _)).trans
        (Finset.single_le_sum (fun _ _ => le_max_right _ _) hi)
    have hRes := scalar_first_order_remainder_bound (hφ i) hM hReq
    rw [hφ₀, sub_zero] at hRes
    have hLin : fderiv ℝ (φ i) p (x-p) ≤ M * ‖x-p‖^2 := by
      have h := (abs_le.mp hRes).1
      linarith only [h,hxφ]
    rw [hGrad i p, smul_apply, smul_eq_mul, innerSL_apply_apply] at hLin
    have ht : 0 < t i p := zero_lt_one.trans_le (hT i p)
    apply (le_of_mul_le_mul_left ?_ ht)
    exact hLin.trans (le_mul_of_one_le_left (mul_nonneg hM (sq_nonneg _)) (hT i p))
  refine ⟨ν,hν,?_⟩
  intro ρ hρ
  have hρδ : ρ < δ/4 := hρ.2.trans_le (min_le_left _ _)
  have hρM : ρ < (4*(M+1))⁻¹ := hρ.2.trans_le (min_le_right _ _)
  have hProd : 4*(M+1)*ρ < 1 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4*(M+1))).1
      (show ρ < 1/(4*(M+1)) from by simpa only [one_div] using hρM)
    simpa only [mul_comm] using h
  have hPos : 0 < 1-2*ρ*M := by nlinarith only [hProd,hρ.1]
  let A := p+ρ • ν
  have hAp : dist A p = ρ := by
    change dist (p+ρ • ν) p = _
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.1.le, hν, mul_one]
  have hFar (y : Point) (hy : δ ≤ dist y p) : ρ < ‖y-A‖ := by
    rw [← dist_eq_norm]
    linarith only [dist_triangle y A p, hAp, hy, hρδ, hδ]
  have hNear (y : Point) (hy : y ∈ closure U) (hyd : dist y p ≤ δ) :
      ρ^2 + (1-2*ρ*M)*‖y-p‖^2 ≤ ‖y-A‖^2 := by
    have hX : y-A = y-p - ρ • ν := by dsimp only [A]; abel
    rw [hX, norm_sub_sq_real (y-p) (ρ • ν), real_inner_smul_right, norm_smul,
      Real.norm_of_nonneg hρ.1.le, hν, mul_one, real_inner_comm ν (y-p)]
    have h := mul_le_mul_of_nonneg_left (hN y hy hyd)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hρ.1.le)
    nlinarith only [h]
  refine ⟨fun y hy => ?_,fun y hy => ?_⟩
  · by_cases hd : dist y p ≤ δ
    · exact le_of_sq_le_sq ((le_add_of_nonneg_right (mul_nonneg hPos.le (sq_nonneg _))).trans
        (hNear y hy hd)) (norm_nonneg _)
    · exact (hFar y (le_of_lt (lt_of_not_ge hd))).le
  · by_cases hd : dist y p ≤ δ
    · have hne : y ≠ p := by
        intro he
        have hpN : p ∉ U := fun h => disjoint_left.mp ((disjoint_frontier_iff_isOpen).2 hU.1.1) hp h
        exact hpN (he ▸ hy)
      have hS : 0 < ‖y-p‖^2 := pow_pos (norm_pos_iff.2 (sub_ne_zero.mpr hne)) 2
      have h := (lt_add_of_pos_right _ (mul_pos hPos hS)).trans_le (hNear y (subset_closure hy) hd)
      exact (sq_lt_sq₀ hρ.1.le (norm_nonneg _)).1 h
    · exact hFar y (le_of_lt (lt_of_not_ge hd))

end Thesis

end
