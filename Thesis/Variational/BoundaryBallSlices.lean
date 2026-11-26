module

public import Thesis.Variational.WholeWallEnergy
import StratificationTheory.Foundation.SphereSurfaceIntegral
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Geometric data for the actual spherical and wall patches of a cut ball. -/

public section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal RealInnerProductSpace
open scoped NNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem exists_local_implicit_epigraph
    {f : Plane × ℝ → ℝ} (hf : ContDiffAt ℝ 1 f (0, 0))
    (h0 : f (0, 0) = 0) (hV : fderiv ℝ f (0, 0) (0, 1) < 0) :
    ∃ (d : ℝ) (g : Plane → ℝ) (L : ℝ≥0), 0 < d ∧
      LipschitzOnWith L g (Metric.ball 0 d) ∧ g 0 = 0 ∧
      ∀ z ∈ Metric.ball (0, 0) d, f z < 0 ↔ g z.1 < z.2 := by
  let D := fderiv ℝ f (0, 0)
  let a := D (0, 1)
  have ha : a ≠ 0 := ne_of_lt hV
  have hInr : D ∘L ContinuousLinearMap.inr ℝ Plane ℝ = a • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro t
    change D (0, t) = a * t
    rw [show (0, t) = t • ((0, 1) : Plane × ℝ) by simp, map_smul, smul_eq_mul, mul_comm]
  have hInv : (D ∘L ContinuousLinearMap.inr ℝ Plane ℝ).IsInvertible := by
    rw [hInr]
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := a⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext
      intro t
      change a * (a⁻¹ * t) = t
      rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    · apply ContinuousLinearMap.ext
      intro t
      change a⁻¹ * (a * t) = t
      rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  have hOne : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  let g := hf.implicitFunction hOne hInv
  have hg0 : g 0 = 0 := hf.implicitFunction_apply_self hOne hInv
  have hZero : ∀ᶠ p in 𝓝 0, f (p, g p) = 0 := by
    simpa only [h0] using hf.eventually_apply_implicitFunction hOne hInv
  have hgDiff := hf.hasStrictFDerivAt_implicitFunction hOne hInv
  obtain ⟨L, S, hS, hLip⟩ := hgDiff.exists_lipschitzOnWith
  have hNeg : ∀ᶠ z in 𝓝 ((0, 0) : Plane × ℝ), fderiv ℝ f z (0, 1) < 0 :=
    (hf.continuousAt_fderiv hOne).clm_apply continuousAt_const |>.eventually_lt continuousAt_const hV
  have hDiff : ∀ᶠ z in 𝓝 ((0, 0) : Plane × ℝ), DifferentiableAt ℝ f z :=
    (hf.eventually (by simp)).mono fun z hz => hz.differentiableAt hOne
  obtain ⟨R, hR, hRD⟩ := Metric.mem_nhds_iff.mp (hNeg.and hDiff)
  have hgNear : ∀ᶠ p in 𝓝 (0 : Plane), g p ∈ Metric.ball (0 : ℝ) R := by
    have hC : ContinuousAt g 0 := hgDiff.continuousAt
    apply hC.tendsto
    rw [hg0]
    exact Metric.ball_mem_nhds 0 hR
  obtain ⟨d₀, hd₀, hdS⟩ := Metric.mem_nhds_iff.mp ((hZero.and hgNear).and hS)
  let d := min d₀ R
  have hd : 0 < d := lt_min hd₀ hR
  have hdR := Metric.ball_subset_ball (x := (0 : ℝ)) (min_le_right d₀ R)
  have hdP := Metric.ball_subset_ball (x := (0 : Plane)) (min_le_right d₀ R)
  have hd₀' := Metric.ball_subset_ball (x := (0 : Plane)) (min_le_left d₀ R)
  refine ⟨d, g, L, hd, hLip.mono (fun p hp => (hdS (hd₀' hp)).2), hg0, ?_⟩
  rintro ⟨p, s⟩ hz
  have hz' : (p, s) ∈ Metric.ball (0 : Plane) d ×ˢ Metric.ball (0 : ℝ) d := by
    rwa [ball_prod_same]
  have hp : p ∈ Metric.ball (0 : Plane) R := hdP hz'.1
  have hs : s ∈ Metric.ball (0 : ℝ) R := hdR hz'.2
  have hgs := (hdS (hd₀' hz'.1)).1
  have hVert (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) R) :
      HasDerivAt (fun u : ℝ => f (p, u)) (fderiv ℝ f (p, t) (0, 1)) t ∧
        fderiv ℝ f (p, t) (0, 1) < 0 := by
    have hZ : (p, t) ∈ Metric.ball ((0, 0) : Plane × ℝ) R := by
      rw [← ball_prod_same]
      exact Set.mk_mem_prod hp ht
    have hT : HasDerivAt (fun u : ℝ => (p, u)) (0, 1) t :=
      (hasDerivAt_const t p).prodMk (hasDerivAt_id t)
    exact ⟨(hRD hZ).2.hasFDerivAt.comp_hasDerivAt t hT, (hRD hZ).1⟩
  have hAnti : StrictAntiOn (fun t : ℝ => f (p, t)) (Metric.ball (0 : ℝ) R) :=
    strictAntiOn_of_deriv_neg (convex_ball 0 R)
      (fun t ht => (hVert t ht).1.continuousAt.continuousWithinAt) fun t ht => by
        rw [Metric.isOpen_ball.interior_eq] at ht
        exact ((hVert t ht).1.deriv).symm ▸ (hVert t ht).2
  change f (p, s) < 0 ↔ g p < s
  rw [← hgs.1]
  exact StrictAntiOn.lt_iff_gt hAnti hs hgs.2

private theorem HasRegularOutwardNormalAt.exists_lipschitz_epigraph
    {U : Set Point} {a n : Point} (hn : HasRegularOutwardNormalAt U a n)
    (A : Point ≃ₗᵢ[ℝ] Point) (hA : inner ℝ n (A.symm (axis 2)) < 0) :
    ∃ (r : ℝ) (g : Plane → ℝ) (L : ℝ≥0), 0 < r ∧
      LipschitzOnWith L g (Metric.ball 0 r) ∧ g 0 = 0 ∧
      U ∩ Metric.ball a r =
        {y | let z := A (y - a); g (WithLp.toLp 2 ![z 0, z 1]) < z 2} ∩ Metric.ball a r := by
  obtain ⟨_, _, R, φ, t, hR, hφ, hφ0, ht, hD, hDef⟩ := hn
  let E : Point ≃L[ℝ] Plane × EuclideanSpace ℝ (Fin 1) :=
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let P : Point →L[ℝ] Plane :=
    (ContinuousLinearMap.fst ℝ Plane (EuclideanSpace ℝ (Fin 1))).comp E.toContinuousLinearMap
  let H : Point →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3)
  have hP (z : Point) : P z = WithLp.toLp 2 ![z 0, z 1] := by
    ext i
    fin_cases i <;> rfl
  let M := E.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ Plane (EuclideanSpace ℝ (Fin 1)))
  let B : Plane × ℝ →L[ℝ] Point :=
    A.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((M.comp (ContinuousLinearMap.fst ℝ Plane ℝ)) +
        (((ContinuousLinearMap.id ℝ ℝ).smulRight (axis 2)).comp (ContinuousLinearMap.snd ℝ Plane ℝ)))
  have hB (z : Plane × ℝ) : B z = A.symm (E.symm (z.1, 0) + z.2 • axis 2) := rfl
  have hBVert : B (0, 1) = A.symm (axis 2) := by
    rw [hB]
    simp only [Prod.mk_zero_zero, map_zero, one_smul, zero_add]
  let ψ (z : Plane × ℝ) := a + B z
  have hψ0 : ψ (0, 0) = a := by simp only [ψ, Prod.mk_zero_zero, map_zero, add_zero]
  have hψ : ContDiff ℝ 1 ψ := contDiff_const.add B.contDiff
  have hψD : HasFDerivAt ψ B (0, 0) := B.hasFDerivAt.const_add a
  let f := φ ∘ ψ
  have hφAt : ContDiffAt ℝ 1 φ a :=
    (hφ a (Metric.mem_ball_self hR)).contDiffAt (Metric.ball_mem_nhds a hR)
  have hf : ContDiffAt ℝ 1 f (0, 0) :=
    (show ContDiffAt ℝ 1 φ (ψ (0, 0)) by rwa [hψ0]).comp (0, 0) hψ.contDiffAt
  have hfD : HasFDerivAt f ((t • innerSL ℝ n).comp B) (0, 0) :=
    (show HasFDerivAt φ (t • innerSL ℝ n) (ψ (0, 0)) by rwa [hψ0]).comp (0, 0) hψD
  have hfV : fderiv ℝ f (0, 0) (0, 1) < 0 := by
    rw [hfD.fderiv, ContinuousLinearMap.comp_apply, hBVert, smul_apply, smul_eq_mul, innerSL_apply_apply]
    exact mul_neg_of_pos_of_neg ht hA
  obtain ⟨d, g, L, hd, hLip, hg0, hg⟩ := exists_local_implicit_epigraph hf
    (by simp only [f, Function.comp_apply, hψ0, hφ0]) hfV
  let T (y : Point) : Plane × ℝ := (P (A (y - a)), H (A (y - a)))
  have hT0 : T a = (0, 0) := by simp only [T, sub_self, map_zero]
  have hT : Continuous T := (P.continuous.prodMk H.continuous).comp
    (A.continuous.comp (continuous_id.sub continuous_const))
  have hBack (y : Point) : ψ (T y) = y := by
    let e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
    have hVert : E (axis 2) = (0, e) := by
      apply Prod.ext
      · ext i
        fin_cases i <;> rfl
      · ext i
        fin_cases i
        rfl
    have hZ (z : Point) : E (E.symm (P z, 0) + H z • axis 2) = E z := by
      rw [map_add, E.apply_symm_apply, map_smul, hVert]
      apply Prod.ext
      · change P z + H z • (0 : Plane) = P z
        simp only [smul_zero, add_zero]
      · ext i
        fin_cases i
        change (0 + H z • e) 0 = z 2
        simp only [zero_add, PiLp.smul_apply, e, PiLp.single_apply, if_true, smul_eq_mul, mul_one]
        rfl
    have hInv (z : Point) : E.symm (P z, 0) + H z • axis 2 = z := E.injective (hZ z)
    change a + B (T y) = y
    rw [hB]
    change a + A.symm (E.symm (P (A (y - a)), 0) + H (A (y - a)) • axis 2) = y
    rw [hInv, A.symm_apply_apply]
    abel
  have hTN : ∀ᶠ y in 𝓝 a, T y ∈ Metric.ball ((0, 0) : Plane × ℝ) d := by
    apply hT.continuousAt.tendsto
    rw [hT0]
    exact Metric.ball_mem_nhds _ hd
  obtain ⟨s, hs, hsT⟩ := Metric.mem_nhds_iff.mp hTN
  let r := min s (min d R)
  have hr : 0 < r := lt_min hs (lt_min hd hR)
  have hrs : r ≤ s := min_le_left _ _
  have hrd : r ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hrR : r ≤ R := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, g, L, hr, hLip.mono (Metric.ball_subset_ball hrd), hg0, ?_⟩
  ext y
  by_cases hy : y ∈ Metric.ball a r
  · have hyR := Metric.ball_subset_ball hrR hy
    have hyT := hsT (Metric.ball_subset_ball hrs hy)
    have hY : y ∈ U ↔ φ y < 0 := by
      have h := Set.ext_iff.mp hDef y
      simpa only [mem_inter_iff, mem_setOf_eq, hyR, and_true] using h
    have hgY := hg (T y) hyT
    change φ (ψ (T y)) < 0 ↔ g (P (A (y - a))) < (A (y - a)) 2 at hgY
    rw [hBack] at hgY
    simpa only [mem_inter_iff, hy, and_true, mem_setOf_eq, hP] using hY.trans hgY
  · simp only [mem_inter_iff, hy, and_false]

/-- Almost every concentric sphere has surface-null intersection with the
fixed smooth wall. -/
theorem IsSmoothDomain.ae_euclideanHausdorffMeasure_wall_sphere_eq_zero
    {U : Set Point} (hU : IsSmoothDomain U) (c : Point) :
    ∀ᵐ r : ℝ, (Measure.euclideanHausdorffMeasure 2 : Measure Point) (frontier U ∩ Metric.sphere c r) = 0 := by
  let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
  let μ := σ.restrict (frontier U)
  letI : IsFiniteMeasure μ := ⟨by
    change (σ.restrict (frontier U)) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact hU.frontier_euclideanHausdorffMeasure_lt_top⟩
  have hDisj : Pairwise (fun r s : ℝ => Disjoint (Metric.sphere c r) (Metric.sphere c s)) := by
    intro r s hn
    refine Set.disjoint_left.mpr fun x hxr hxs => ?_
    exact hn ((Metric.mem_sphere.mp hxr).symm.trans (Metric.mem_sphere.mp hxs))
  have hCount := Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top μ
    (fun r : ℝ => (Metric.isClosed_sphere (x := c) (ε := r)).measurableSet) hDisj (measure_ne_top μ _)
  filter_upwards [hCount.ae_notMem (volume : Measure ℝ)] with r hr
  have h0 : μ (Metric.sphere c r) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hr)
  change σ.restrict (frontier U) (Metric.sphere c r) = 0 at h0
  rwa [Measure.restrict_apply Metric.isClosed_sphere.measurableSet, inter_comm] at h0

/-- Cutting a local wall by an open set containing the point preserves its
regular outward normal there. -/
theorem HasRegularOutwardNormalAt.inter_of_mem_open
    {U V : Set Point} {a n : Point} (h : HasRegularOutwardNormalAt U a n)
    (hV : IsOpen V) (ha : a ∈ V) : HasRegularOutwardNormalAt (U ∩ V) a n := by
  obtain ⟨haU, hn, r, φ, t, hr, hφ, hφ0, ht, hD, hDef⟩ := h
  obtain ⟨R, hR, hBall⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds ha)
  let s := min r R
  have hs : 0 < s := lt_min hr hR
  have hsR : Metric.ball a s ⊆ V := (Metric.ball_subset_ball (min_le_right _ _)).trans hBall
  have hsr : Metric.ball a s ⊆ Metric.ball a r := Metric.ball_subset_ball (min_le_left _ _)
  have hFront : a ∈ frontier (U ∩ V) :=
    ⟨hV.closure_inter ⟨haU.1, ha⟩, fun hy => haU.2 (interior_mono inter_subset_left hy)⟩
  refine ⟨hFront, hn, s, φ, t, hs, hφ.mono hsr, hφ0, ht, hD, ?_⟩
  ext y
  constructor
  · intro hy
    have hY : y ∈ U ∩ Metric.ball a r := ⟨hy.1.1, hsr hy.2⟩
    rw [hDef] at hY
    exact ⟨hY.1, hy.2⟩
  · intro hy
    have hY : y ∈ {z | φ z < 0} ∩ Metric.ball a r := ⟨hy.1, hsr hy.2⟩
    rw [← hDef] at hY
    exact ⟨⟨hY.1, hsR hy.2⟩, hy.2⟩

/-- The positive-radius sphere has its usual radial outward unit normal. -/
theorem ball_hasRegularOutwardNormalAt (c : Point) {r : ℝ} (hr : 0 < r)
    {x : Point} (hx : x ∈ Metric.sphere c r) :
    HasRegularOutwardNormalAt (Metric.ball c r) x (r⁻¹ • (x - c)) := by
  have hn : ‖x - c‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  have hFront : x ∈ frontier (Metric.ball c r) := by rwa [frontier_ball c hr.ne']
  have hUnit : ‖r⁻¹ • (x - c)‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), hn, inv_mul_cancel₀ hr.ne']
  let φ (y : Point) := ‖y - c‖ ^ 2 - r ^ 2
  have hφ : ContDiff ℝ 1 φ := ((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const
  have hd' : HasFDerivAt (fun y : Point => y - c) (ContinuousLinearMap.id ℝ Point) x :=
    (hasFDerivAt_id x).sub_const c
  have hd := hd'.norm_sq.sub_const (r ^ 2)
  have hD : HasFDerivAt φ ((2 * r) • innerSL ℝ (r⁻¹ • (x - c))) x := by
    have hEq : (2 * r) • innerSL ℝ (r⁻¹ • (x - c)) = (2 : ℝ) • innerSL ℝ (x - c) := by
      ext v
      simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, real_inner_smul_left]
      rw [← mul_assoc, mul_assoc 2, mul_inv_cancel₀ hr.ne', mul_one]
    rw [hEq]
    simpa only [φ, ContinuousLinearMap.comp_id, two_nsmul, two_smul] using hd
  refine ⟨hFront, hUnit, (1 : ℝ), φ, 2 * r, zero_lt_one, hφ.contDiffOn, ?_, by positivity, hD, ?_⟩
  · simp only [φ, hn, sub_self]
  · ext y
    simp only [mem_inter_iff, Metric.mem_ball, dist_eq_norm, mem_setOf_eq, φ, sub_neg,
      sq_lt_sq₀ (norm_nonneg _) hr.le]

private theorem exists_isometry_sending_unit_vector_to_vertical {v : Point} (hv : ‖v‖ = 1) :
    ∃ A : Point ≃ₗᵢ[ℝ] Point, A.symm (axis 2) = v := by
  have hAxis : ‖axis 2‖ = 1 := by simp [axis]
  let A := Submodule.reflection (ℝ ∙ (v - axis 2))ᗮ
  have hA : A v = axis 2 := Submodule.reflection_sub (hv.trans hAxis.symm)
  exact ⟨A, A.symm_apply_eq.mpr hA.symm⟩

private theorem exists_common_inward_direction {n m : Point} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hnm : m ≠ -n) : ∃ v : Point, ‖v‖ = 1 ∧ inner ℝ n v < 0 ∧ inner ℝ m v < 0 := by
  have hNE : n + m ≠ 0 := fun h => hnm (eq_neg_of_add_eq_zero_right h)
  have hNorm : 0 < ‖n + m‖ := norm_pos_iff.mpr hNE
  have hSq : 0 < ‖n + m‖ ^ 2 := by positivity
  rw [norm_add_sq_real, hn, hm, one_pow] at hSq
  let v := ‖n + m‖⁻¹ • (-(n + m))
  refine ⟨v, ?_, ?_, ?_⟩
  · change ‖‖n + m‖⁻¹ • (-(n + m))‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hNorm.le), norm_neg,
      inv_mul_cancel₀ hNorm.ne']
  · simp only [v, real_inner_smul_right, inner_neg_right, inner_add_right,
      real_inner_self_eq_norm_sq, hn, one_pow]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hNorm) (by linarith only [hSq])
  · simp only [v, real_inner_smul_right, inner_neg_right, inner_add_right,
      real_inner_self_eq_norm_sq, hm, one_pow]
    rw [real_inner_comm n m]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hNorm) (by linarith only [hSq])

private theorem has_lipschitz_epigraph_at_of_regular_normal
    {U : Set Point} {a n : Point} (hn : HasRegularOutwardNormalAt U a n) :
    ∃ (r : ℝ) (A : Point ≃ₗᵢ[ℝ] Point) (g : Plane → ℝ) (L : ℝ≥0), 0 < r ∧
      LipschitzOnWith L g (Metric.ball 0 r) ∧ g 0 = 0 ∧
      U ∩ Metric.ball a r =
        {y | let z := A (y - a); g (WithLp.toLp 2 ![z 0, z 1]) < z 2} ∩ Metric.ball a r := by
  obtain ⟨A, hA⟩ := exists_isometry_sending_unit_vector_to_vertical
    (v := -n) (by rw [norm_neg, hn.2.1])
  obtain ⟨r, g, L, hr, hg, hg0, hChart⟩ := hn.exists_lipschitz_epigraph A (by
    rw [hA, inner_neg_right, real_inner_self_eq_norm_sq, hn.2.1, one_pow]
    norm_num)
  exact ⟨r, A, g, L, hr, hg, hg0, hChart⟩

private theorem has_lipschitz_epigraph_at_inter_of_regular_normals
    {U V : Set Point} {a n m : Point}
    (hn : HasRegularOutwardNormalAt U a n) (hm : HasRegularOutwardNormalAt V a m) (hnm : m ≠ -n) :
    ∃ (r : ℝ) (A : Point ≃ₗᵢ[ℝ] Point) (g : Plane → ℝ) (L : ℝ≥0), 0 < r ∧
      LipschitzOnWith L g (Metric.ball 0 r) ∧ g 0 = 0 ∧
      (U ∩ V) ∩ Metric.ball a r =
        {y | let z := A (y - a); g (WithLp.toLp 2 ![z 0, z 1]) < z 2} ∩ Metric.ball a r := by
  obtain ⟨v, hv, hvn, hvm⟩ := exists_common_inward_direction hn.2.1 hm.2.1 hnm
  obtain ⟨A, hA⟩ := exists_isometry_sending_unit_vector_to_vertical hv
  obtain ⟨rU, gU, LU, hrU, hLipU, hgU0, hU⟩ := hn.exists_lipschitz_epigraph A (hA.symm ▸ hvn)
  obtain ⟨rV, gV, LV, hrV, hLipV, hgV0, hV⟩ := hm.exists_lipschitz_epigraph A (hA.symm ▸ hvm)
  let r := min rU rV
  let g := fun p => max (gU p) (gV p)
  have hLipU' := hLipU.mono (Metric.ball_subset_ball (min_le_left rU rV))
  have hLipV' := hLipV.mono (Metric.ball_subset_ball (min_le_right rU rV))
  have hLip : LipschitzOnWith (max LU LV) g (Metric.ball 0 r) := by
    simpa only [g, r, Function.comp_def, one_mul] using
      lipschitzWith_max.comp_lipschitzOnWith (hLipU'.prodMk hLipV')
  refine ⟨r, A, g, max LU LV, lt_min hrU hrV, hLip, ?_, ?_⟩
  · simp only [g, hgU0, hgV0, max_self]
  · ext y
    by_cases hy : y ∈ Metric.ball a r
    · have hyU := Metric.ball_subset_ball (min_le_left rU rV) hy
      have hyV := Metric.ball_subset_ball (min_le_right rU rV) hy
      let z := A (y - a)
      let p : Plane := WithLp.toLp 2 ![z 0, z 1]
      have hYu : y ∈ U ↔ gU p < z 2 := by
        simpa only [mem_inter_iff, mem_setOf_eq, hyU, and_true] using Set.ext_iff.mp hU y
      have hYv : y ∈ V ↔ gV p < z 2 := by
        simpa only [mem_inter_iff, mem_setOf_eq, hyV, and_true] using Set.ext_iff.mp hV y
      change (y ∈ U ∧ y ∈ V) ∧ y ∈ Metric.ball a r ↔
        max (gU p) (gV p) < z 2 ∧ y ∈ Metric.ball a r
      simp only [hYu, hYv, max_lt_iff]
    · simp only [mem_inter_iff, hy, and_false]

/-- At the seam, a common inward direction makes the cut the epigraph
of the maximum of the two locally Lipschitz graphs. -/
theorem IsSmoothDomain.hasLocallyLipschitzBoundary_inter_ball_of_ne_neg_normal
    {U : Set Point} (hU : IsSmoothDomain U) {ν : Point → Point}
    (hWall : ∀ x ∈ frontier U, HasRegularOutwardNormalAt U x (ν x))
    (c : Point) {r : ℝ} (hr : 0 < r)
    (hSeam : ∀ x ∈ frontier U ∩ Metric.sphere c r, r⁻¹ • (x - c) ≠ -ν x) :
    HasLocallyLipschitzBoundary (U ∩ Metric.ball c r) := by
  intro x hx
  rcases frontier_slice_subset hU.1.1 c hr hx with (hS | hW) | hSW
  · rw [inter_comm U]
    exact has_lipschitz_epigraph_at_of_regular_normal
      ((ball_hasRegularOutwardNormalAt c hr hS.2).inter_of_mem_open hU.1.1 hS.1)
  · exact has_lipschitz_epigraph_at_of_regular_normal
      ((hWall x hW.1).inter_of_mem_open Metric.isOpen_ball hW.2)
  · exact has_lipschitz_epigraph_at_inter_of_regular_normals (hWall x hSW.1)
      (ball_hasRegularOutwardNormalAt c hr hSW.2) (hSeam x hSW)

/-- The normalized Euclidean Hausdorff measure of an actual positive-radius
sphere is finite by its native affine angular parametrization. -/
theorem euclideanHausdorffMeasure_sphere_lt_top (c : Point) {r : ℝ} (hr : 0 < r) :
    (Measure.euclideanHausdorffMeasure 2 : Measure Point) (Metric.sphere c r) < ⊤ := by
  let ρ : HarmonicMaps.PositiveRadius := ⟨r, hr⟩
  let μ := (volume : Measure Point).toSphere
  let f (θ : Metric.sphere (0 : Point) 1) : Point := c + r • θ.val
  haveI : IsFiniteMeasure (ENNReal.ofReal (r ^ 2) • μ) := Measure.smul_finite _ ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (Measure.map f (ENNReal.ofReal (r ^ 2) • μ)) := Measure.isFiniteMeasure_map _ _
  have h := StratificationTheory.map_native_unitSphere_weighted_affine (n := 3) (by decide) c ρ
  rw [StratificationTheory.euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3)] at h
  change (Measure.map f (ENNReal.ofReal (r ^ 2) • μ)) =
    (Measure.euclideanHausdorffMeasure 2 : Measure Point).restrict (Metric.sphere c r) at h
  rw [← Measure.restrict_apply_univ, ← h]
  exact measure_lt_top _ _

/-- The frontier of every positive-radius cut lies in the union of two
finite-area surfaces. -/
theorem IsSmoothDomain.euclideanHausdorffMeasure_frontier_inter_ball_lt_top
    {U : Set Point} (hU : IsSmoothDomain U) (c : Point) {r : ℝ} (hr : 0 < r) :
    (Measure.euclideanHausdorffMeasure 2 : Measure Point) (frontier (U ∩ Metric.ball c r)) < ⊤ := by
  let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
  have hSub : frontier (U ∩ Metric.ball c r) ⊆ frontier U ∪ Metric.sphere c r := by
    intro y hy
    rcases frontier_slice_subset hU.1.1 c hr hy with (hyS | hyW) | hySeam
    · exact Or.inr hyS.2
    · exact Or.inl hyW.1
    · exact Or.inl hySeam.1
  calc
    _ ≤ σ (frontier U ∪ Metric.sphere c r) := measure_mono hSub
    _ ≤ σ (frontier U) + σ (Metric.sphere c r) := measure_union_le _ _
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hU.frontier_euclideanHausdorffMeasure_lt_top,
      euclideanHausdorffMeasure_sphere_lt_top c hr⟩

/-- Once the Lipschitz graph property holds at the seam, a cut of a
smooth domain has the precise two regular patch normals for Gauss–Green. -/
theorem IsSmoothDomain.exists_piecewiseRegularBoundary_inter_ball_of_lipschitz
    {U : Set Point} (hU : IsSmoothDomain U) {ν : Point → Point} (hν : Continuous ν)
    (hWall : ∀ x ∈ frontier U, HasRegularOutwardNormalAt U x (ν x))
    (c : Point) {r : ℝ} (hr : 0 < r)
    (hLip : HasLocallyLipschitzBoundary (U ∩ Metric.ball c r))
    (hSeam : (Measure.euclideanHausdorffMeasure 2 : Measure Point) (frontier U ∩ Metric.sphere c r) = 0) :
    ∃ ν' : Point → Point, PiecewiseRegularBoundary (U ∩ Metric.ball c r) ν' ∧
      EqOn ν' (fun x => r⁻¹ • (x - c)) (U ∩ Metric.sphere c r) ∧
      EqOn ν' ν (frontier U ∩ Metric.ball c r) := by
  classical
  let X (x : Point) := r⁻¹ • (x - c)
  let ν' := U.piecewise X ν
  have hXc : Continuous X := (continuous_id.sub continuous_const).const_smul (r⁻¹)
  have hXm := hXc.measurable
  have hM : Measurable ν' := hXm.piecewise hU.1.1.measurableSet hν.measurable
  have hEqS : EqOn ν' X (U ∩ Metric.sphere c r) := fun x hx => piecewise_eq_of_mem U X ν hx.1
  have hEqW : EqOn ν' ν (frontier U ∩ Metric.ball c r) := fun x hx =>
    piecewise_eq_of_notMem U X ν (fun h => hx.1.2 (hU.1.1.interior_eq.symm ▸ h))
  refine ⟨ν', ⟨hU.1.1.inter Metric.isOpen_ball, Metric.isBounded_ball.subset inter_subset_right,
    hLip, hU.euclideanHausdorffMeasure_frontier_inter_ball_lt_top c hr, hM.aemeasurable, ?_⟩, hEqS, hEqW⟩
  have hNull : ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure 2 : Measure Point), x ∉ frontier U ∩ Metric.sphere c r := by
    rw [ae_iff]
    have hSet : {x | ¬ x ∉ frontier U ∩ Metric.sphere c r} = frontier U ∩ Metric.sphere c r :=
      Set.ext fun _ => not_not
    rwa [hSet]
  filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet, ae_restrict_of_ae hNull] with x hx hn
  rcases (frontier_slice_subset hU.1.1 c hr hx).resolve_right hn with hS | hW
  · rw [hEqS hS, inter_comm]
    exact (ball_hasRegularOutwardNormalAt c hr hS.2).inter_of_mem_open hU.1.1 hS.1
  · rw [hEqW hW]
    exact (hWall x hW.1).inter_of_mem_open Metric.isOpen_ball hW.2

/-- The planar scalar Morse–Sard theorem on an arbitrary open set. -/
@[expose] def External.MorseSardPlaneToReal : Prop :=
  ∀ (V : Set Plane) (f : Plane → ℝ), IsOpen V → ContDiffOn ℝ 2 f V →
    ∀ᵐ s : ℝ, ∀ p ∈ V, f p = s → fderiv ℝ f p ≠ 0

private theorem fderiv_distance_boundary_parametrization_eq_zero
    {U : Set Point} (hU : IsOpen U) {a c : Point} {R : ℝ} {Γ : Plane → Point}
    (hΓ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Γ)
    (hImage : ∀ y ∈ Metric.ball a R, y ∈ frontier U ↔ y ∈ range Γ)
    {p : Plane} {n : Point} (hp : Γ p ∈ Metric.ball a R)
    (hn : HasRegularOutwardNormalAt U (Γ p) n) (hNe : Γ p - c ≠ 0)
    (hParallel : ∃ s : ℝ, Γ p - c = s • n) :
    fderiv ℝ (fun q => ‖Γ q - c‖) p = 0 := by
  let J := fderiv ℝ Γ p
  have hJ : HasFDerivAt Γ J p := (hΓ.differentiable (by simp) p).hasFDerivAt
  have hOrth (z : Plane) : inner ℝ n (J z) = 0 := by
    let γ (t : ℝ) := p + t • z
    have hγ0 : γ 0 = p := by simp only [γ, zero_smul, add_zero]
    have hγ : HasDerivAt γ z 0 := by
      simpa only [γ, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add p
    have hJ' : HasFDerivAt Γ J (γ 0) := hγ0.symm ▸ hJ
    have hDeriv := hJ'.comp_hasDerivAt 0 hγ
    have hNear : ∀ᶠ t in 𝓝 0, Γ (γ t) ∈ Metric.ball a R := by
      apply hDeriv.continuousAt.tendsto
      simp only [Function.comp_apply, hγ0]
      exact Metric.isOpen_ball.mem_nhds hp
    exact hn.inner_velocity_eq_zero hU hDeriv (by simp only [Function.comp_apply, hγ0])
      (hNear.mono fun t ht => (hImage (Γ (γ t)) ht).mpr ⟨γ t, rfl⟩)
  have hSq := hJ.sub_const c |>.norm_sq
  have hSqD : HasFDerivAt (fun q => ‖Γ q - c‖ ^ 2) (0 : Plane →L[ℝ] ℝ) p := by
    have hZero : (2 : ℕ) • (innerSL ℝ (Γ p - c)).comp J = 0 := by
      obtain ⟨s, hs⟩ := hParallel
      apply ContinuousLinearMap.ext
      intro z
      simp only [two_nsmul, add_apply, ContinuousLinearMap.comp_apply,
        innerSL_apply_apply, hs, real_inner_smul_left, hOrth, mul_zero, add_zero,
        zero_apply]
    rwa [← hZero]
  have hNorm := hSqD.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hNe))
  have hD : HasFDerivAt (fun q => ‖Γ q - c‖) (0 : Plane →L[ℝ] ℝ) p := by
    simpa only [Real.sqrt_sq (norm_nonneg _), smul_zero] using hNorm
  exact hD.fderiv

/-- Planar Morse–Sard applied to the smooth wall charts excludes both
parallel orientations of their normal and the radial normal for a.e. radius. -/
theorem IsSmoothDomain.ae_ball_sphere_transverse
    (hSard : External.MorseSardPlaneToReal) {U : Set Point} (hU : IsSmoothDomain U)
    {ν : Point → Point} (hWall : ∀ x ∈ frontier U, HasRegularOutwardNormalAt U x (ν x))
    (c : Point) :
    ∀ᵐ r : ℝ, 0 < r → ∀ x ∈ frontier U ∩ Metric.sphere c r,
      r⁻¹ • (x - c) ≠ ν x ∧ r⁻¹ • (x - c) ≠ -ν x := by
  classical
  let K := frontier U
  have hK : IsCompact K := hU.1.2.2.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hLocal (a : K) := hU.exists_boundary_parametrization a.property
  choose R Γ hR hΓ _ hImage using hLocal
  let W (a : K) := Metric.ball (a : Point) (R a)
  have hCover : K ⊆ ⋃ a : K, W a := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hR ⟨y, hy⟩)⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover W (fun _ => Metric.isOpen_ball) hCover
  let V (a : K) : Set Plane := {p | Γ a p ≠ c}
  let f (a : K) (p : Plane) := ‖Γ a p - c‖
  have hOpen (a : K) : IsOpen (V a) :=
    isClosed_eq (hΓ a).continuous continuous_const |>.isOpen_compl
  have hTwo : (2 : ℕ∞ω) ≤ ↑(⊤ : ℕ∞) := by
    change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  have hF (a : K) : ContDiffOn ℝ 2 (f a) (V a) :=
    (((hΓ a).of_le hTwo).sub contDiff_const).contDiffOn.norm ℝ
      (fun p hp => sub_ne_zero.mpr hp)
  have hRegs : ∀ᵐ r : ℝ, ∀ a ∈ I, ∀ p ∈ V a, f a p = r → fderiv ℝ (f a) p ≠ 0 :=
    (ae_ball_iff I.finite_toSet.countable).mpr (fun a _ => hSard (V a) (f a) (hOpen a) (hF a))
  filter_upwards [hRegs] with r hReg hr x hx
  obtain ⟨a, ha, hxW⟩ := mem_iUnion₂.mp (hI hx.1)
  obtain ⟨p, rfl⟩ := (hImage a x hxW).mp hx.1
  have hValue : f a p = r := by simpa only [f, Metric.mem_sphere, dist_eq_norm] using hx.2
  have hNe : Γ a p - c ≠ 0 := by
    intro h
    have h0 : (0 : ℝ) = r := by simpa only [f, h, norm_zero] using hValue
    exact hr.ne' h0.symm
  have hP : p ∈ V a := sub_ne_zero.mp hNe
  have hD (hParallel : ∃ s : ℝ, Γ a p - c = s • ν (Γ a p)) : False :=
    (hReg a ha p hP hValue) (fderiv_distance_boundary_parametrization_eq_zero hU.1.1 (hΓ a)
      (hImage a) hxW (hWall (Γ a p) hx.1) hNe hParallel)
  constructor
  · intro h
    apply hD
    refine ⟨r, ?_⟩
    have h' := congrArg (fun z : Point => r • z) h
    simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using h'
  · intro h
    apply hD
    refine ⟨-r, ?_⟩
    have h' := congrArg (fun z : Point => r • z) h
    simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, smul_neg, neg_smul] using h'

/-- For almost every positive radius the actual cut domain is Lipschitz,
with the radial and wall normals on the stated patches and a surface-null seam. -/
theorem IsSmoothDomain.ae_piecewiseRegularBoundary_inter_ball
    (hSard : External.MorseSardPlaneToReal) {U : Set Point} (hU : IsSmoothDomain U)
    {ν : Point → Point} (hν : Continuous ν)
    (hWall : ∀ x ∈ frontier U, HasRegularOutwardNormalAt U x (ν x)) (c : Point) :
    ∀ᵐ r : ℝ, 0 < r →
      ∃ ν' : Point → Point, PiecewiseRegularBoundary (U ∩ Metric.ball c r) ν' ∧
        (Measure.euclideanHausdorffMeasure 2 : Measure Point) (frontier U ∩ Metric.sphere c r) = 0 ∧
        EqOn ν' (fun x => r⁻¹ • (x - c)) (U ∩ Metric.sphere c r) ∧
        EqOn ν' ν (frontier U ∩ Metric.ball c r) := by
  filter_upwards [hU.ae_ball_sphere_transverse hSard hWall c,
    hU.ae_euclideanHausdorffMeasure_wall_sphere_eq_zero c] with r hTrans hArea hr
  have hL := hU.hasLocallyLipschitzBoundary_inter_ball_of_ne_neg_normal hWall c hr
    (fun x hx => (hTrans hr x hx).2)
  obtain ⟨ν', hGeo, hRad, hPhys⟩ :=
    hU.exists_piecewiseRegularBoundary_inter_ball_of_lipschitz hν hWall c hr hL hArea
  exact ⟨ν', hGeo, hArea, hRad, hPhys⟩

end Thesis

end
