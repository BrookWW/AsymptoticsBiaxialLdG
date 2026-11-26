module

public import Thesis.Variational.BoundaryBallSlices
public import Thesis.Variational.BoundaryEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! Boundary energy quasi-monotonicity for classical Dirichlet solutions. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius RealInnerProductSpace

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem exists_quadratic_taylor_bound_on_closedBall
    {φ : Point → ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) φ) (a : Point) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Metric.closedBall a R, ∀ c ∈ Metric.closedBall a R,
      ‖φ c - φ x - (fderiv ℝ φ x) (c - x)‖ ≤ M * ‖c - x‖ ^ 2 := by
  let D := fderiv ℝ φ
  have hD : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) D := hφ.fderiv_right (by simp)
  obtain ⟨B, hB⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn
    (hD.continuous_fderiv (by simp)).continuousOn
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨M, hM, fun x hx c hc => ?_⟩
  let K := Metric.closedBall a R
  let S := segment ℝ x c
  have hSub : S ⊆ K := (convex_closedBall a R).segment_subset hx hc
  have hGrad (z : Point) (hz : z ∈ S) : ‖D z - D x‖ ≤ M * ‖c - x‖ := by
    have hGrad' := (convex_closedBall a R).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hD.differentiable (by simp) y)
      (fun y hy => (hB y hy).trans (le_max_left B 0)) hx (hSub hz)
    exact hGrad'.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hM)
  let F (y : Point) := φ y - D x (y - x)
  have hFD (z : Point) : HasFDerivAt F (D z - D x) z := by
    have hL : HasFDerivAt (fun y : Point => y - x) (ContinuousLinearMap.id ℝ Point) z :=
      (hasFDerivAt_id z).sub_const x
    simpa only [F, D, Pi.sub_def, Function.comp_def, ContinuousLinearMap.comp_id] using
      ((hφ.differentiable (by simp) z).hasFDerivAt.sub ((D x).hasFDerivAt.comp z hL))
  have hMVT := (convex_segment x c).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hFD z).hasFDerivWithinAt) hGrad
    (left_mem_segment ℝ x c) (right_mem_segment ℝ x c)
  have hEq : F c - F x = φ c - φ x - D x (c - x) := by
    simp only [F, sub_self, map_zero, sub_zero]
    ring
  rwa [hEq, mul_assoc, ← sq] at hMVT

/-- A smooth wall has a uniform quadratic lower bound for the outward
component of a chord from an interior center. -/
theorem IsSmoothDomain.exists_quadratic_lower_bound_wall_chord
    {U : Set Point} (hU : IsSmoothDomain U) {ν : Point → Point}
    (hWall : ∀ x ∈ frontier U, HasRegularOutwardNormalAt U x (ν x)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c ∈ U, ∀ (r : ℝ), 0 < r →
      ∀ x ∈ frontier U ∩ Metric.ball c r, -(M * r ^ 2) ≤ inner ℝ (x - c) (ν x) := by
  classical
  let K := frontier U
  have hK : IsCompact K := hU.1.2.2.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hLocal (a : K) := exists_local_smooth_defining_function_and_normal_field hU a.property
  choose R φ n t hR hφ _ hDef ht hD hN using hLocal
  have hTaylor (a : K) := exists_quadratic_taylor_bound_on_closedBall (hφ a) (a : Point) (R a)
  choose M hM hT using hTaylor
  let W (a : K) := Metric.ball (a : Point) (R a / 2)
  have hCover : K ⊆ ⋃ a : K, W a := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (half_pos (hR ⟨y, hy⟩))⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover W (fun _ => Metric.isOpen_ball) hCover
  have hSmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ a ∈ I, s < R a / 2 := by
    apply (eventually_all_finset I).mpr
    intro a _
    exact nhdsWithin_le_nhds (Iio_mem_nhds (half_pos (hR a)))
  have hPos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  obtain ⟨s, hs0, hsI⟩ := (hPos.and hSmall).exists
  let B := max (∑ a ∈ I, M a) s⁻¹
  have hB : 0 ≤ B := (inv_nonneg.mpr hs0.le).trans (le_max_right _ _)
  refine ⟨B, hB, fun c hc r hr x hx => ?_⟩
  have hDist : ‖x - c‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hx.2
  have hUnit : ‖ν x‖ = 1 := (hWall x hx.1).2.1
  by_cases hsmall : r < s
  · obtain ⟨a, ha, hxW⟩ := mem_iUnion₂.mp (hI hx.1)
    have hxR : x ∈ Metric.ball (a : Point) (R a) :=
      Metric.ball_subset_ball (by linarith only [hR a]) hxW
    have hcR : c ∈ Metric.ball (a : Point) (R a) := by
      have hxA : dist x (a : Point) < R a / 2 := hxW
      have hcX : dist c x < r := by simpa only [dist_comm c x, Metric.mem_ball] using hx.2
      have hsum := dist_triangle c x (a : Point)
      change dist c (a : Point) < R a
      linarith only [hsI a ha, hsmall, hxA, hcX, hsum]
    have hφx : φ a x = 0 := localDefiningFunction_eq_zero_on_frontier hU.1.1
      (hφ a).continuous.continuousOn (hDef a) hx.1 hxR
    have hφc : φ a c < 0 := (show c ∈ {y | φ a y < 0} ∩ Metric.ball (a : Point) (R a) from
      hDef a ▸ ⟨hc, hcR⟩).1
    have hnEq : n a x = ν x := (hN a x ⟨hx.1, hxR⟩).unique (hWall x hx.1)
    have hDT : fderiv ℝ (φ a) x (c - x) ≤ M a * ‖c - x‖ ^ 2 := by
      have hTaylor' := hT a x (Metric.ball_subset_closedBall hxR) c (Metric.ball_subset_closedBall hcR)
      rw [Real.norm_eq_abs] at hTaylor'
      have hLow := (neg_le_neg hTaylor').trans (neg_abs_le _)
      linarith only [hLow, hφx, hφc]
    have hMa : M a ≤ B := (Finset.single_le_sum (fun b _ => hM b) ha).trans (le_max_left _ _)
    have hSquare : ‖c - x‖ ^ 2 ≤ r ^ 2 := by
      rw [norm_sub_rev]
      exact (sq_le_sq₀ (norm_nonneg _) hr.le).mpr hDist.le
    have hDT' : t a x * inner ℝ (ν x) (c - x) ≤ B * r ^ 2 := by
      rw [hD a x, hnEq, smul_apply, smul_eq_mul, innerSL_apply_apply] at hDT
      exact hDT.trans ((mul_le_mul_of_nonneg_left hSquare (hM a)).trans
        (mul_le_mul_of_nonneg_right hMa (sq_nonneg _)))
    have hI' : inner ℝ (ν x) (c - x) ≤ B * r ^ 2 := by
      by_cases hIP : 0 ≤ inner ℝ (ν x) (c - x)
      · have hProd := mul_le_mul_of_nonneg_right (ht a x) hIP
        rw [one_mul] at hProd
        exact hProd.trans hDT'
      · exact (le_of_not_ge hIP).trans (mul_nonneg hB (sq_nonneg _))
    rw [real_inner_comm (ν x) (x - c)]
    have hOpp : inner ℝ (ν x) (c - x) = -inner ℝ (ν x) (x - c) := by
      rw [← neg_sub x c, inner_neg_right]
    rw [hOpp] at hI'
    linarith only [hI']
  · have hAbs := abs_real_inner_le_norm (x - c) (ν x)
    rw [hUnit, mul_one] at hAbs
    have hLow := (neg_le_neg (hAbs.trans hDist.le)).trans (neg_abs_le (inner ℝ (x - c) (ν x)))
    have hSr : s ≤ r := le_of_not_gt hsmall
    have hAll : r ≤ B * r ^ 2 := calc
      r = s * (s⁻¹ * r) := by rw [← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul]
      _ ≤ r * (s⁻¹ * r) := mul_le_mul_of_nonneg_right hSr (mul_nonneg (inv_nonneg.mpr hs0.le) hr.le)
      _ = s⁻¹ * r ^ 2 := by ring
      _ ≤ B * r ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
    exact (neg_le_neg hAll).trans hLow

private theorem gradientNormSq_nonneg (D : Gradient) : 0 ≤ gradientNormSq D := by
  rw [gradientNormSq_eq_sum_norm_sq]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The actual classical energy on any measurable piece of the domain
equals the integral formed with within-closure derivatives. -/
theorem energy_classical_eq_ofReal_closureEnergyDensity
    (a : BulkCoefficients) (ε : ElasticScale) {U W : Set Point} (hU : IsSmoothDomain U)
    (hWU : W ⊆ U) (hW : MeasurableSet W) {Q : Point → S0} (hQ : ContDiffOn ℝ 2 Q (closure U)) :
    energy a ε W Q (ClassicalGradient Q) = ENNReal.ofReal
      (∫ x in W, energyDensity a ε (Q x) (closureGradient U Q x)) := by
  let e (x : Point) := energyDensity a ε (Q x) (closureGradient U Q x)
  have hEc := continuousOn_closureEnergyDensity a ε hU.uniqueDiffOn_closure hQ
  have hEi : IntegrableOn e W volume :=
    (hEc.integrableOn_compact hU.1.2.2.isCompact_closure).mono_set (hWU.trans subset_closure)
  rw [ofReal_integral_eq_lintegral_ofReal hEi (Eventually.of_forall fun x => energyDensity_nonneg a ε _ _)]
  unfold energy
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hW] with x hx
  change ENNReal.ofReal (energyDensity a ε (Q x) (ClassicalGradient Q x)) =
    ENNReal.ofReal (energyDensity a ε (Q x) (closureGradient U Q x))
  rw [closureGradient_eq_classicalGradient hU.1.1 hQ (hWU hx)]

private theorem continuousOn_closureTangentialGradientNormSq
    {U : Set Point} (hUnique : UniqueDiffOn ℝ (closure U)) {b : Point → S0}
    (hb : ContDiffOn ℝ 1 b (closure U)) {ν : Point → Point} (hν : ContDiffOn ℝ 1 ν (closure U)) :
    ContinuousOn (fun x => gradientNormSq (tangentialGradientColumns (closureGradient U b x) (ν x)))
      (closure U) := by
  have hCol := continuousOn_closureGradient_column hUnique hb
  have hN := continuousOn_gradientFromColumns hCol hν
  apply continuousOn_gradientNormSq
  intro i
  have hνi : ContinuousOn (fun x => ν x i) (closure U) :=
    (EuclideanSpace.proj i).continuous.comp_continuousOn hν.continuousOn
  exact (hCol i).sub (hνi.smul hN)

private theorem integrableOn_physicalBoundaryStressCorrection
    (a : BulkCoefficients) (ε : ElasticScale) {U W : Set Point} (hU : IsSmoothDomain U)
    {Q : Point → S0} (hQ : ContDiffOn ℝ 2 Q (closure U)) {ν : Point → Point} (hν : Continuous ν)
    (hn : ∀ x ∈ frontier U, ‖ν x‖ = 1) (hVac : ∀ x ∈ frontier U, Q x ∈ vacuum a) (c : Point)
    (hW : MeasurableSet W) (hWall : W ⊆ frontier U) :
    IntegrableOn (fun x => physicalBoundaryStressCorrection (closureGradient U Q x) (x - c) (ν x))
      W (Measure.euclideanHausdorffMeasure 2) := by
  let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
  let D := closureGradient U Q
  let T (x : Point) := elasticStress a ε (Q x) (D x)
  have hCont : ContinuousOn (fun x => -centeredStressFlux T c ν x) (closure U) := by
    apply ContinuousOn.neg
    unfold centeredStressFlux
    apply continuousOn_finsetSum Finset.univ
    intro j _
    have hνj : Continuous (fun x => ν x j) := (EuclideanSpace.proj j).continuous.comp hν
    refine ContinuousOn.mul ?_ hνj.continuousOn
    apply continuousOn_finsetSum Finset.univ
    intro i _
    have hXi : Continuous (fun x : Point => (x - c) i) :=
      (EuclideanSpace.proj i).continuous.comp (continuous_id.sub continuous_const)
    exact hXi.continuousOn.mul
      (contDiffOn_closureElasticStress_entry a ε hU.uniqueDiffOn_closure hQ i j).continuousOn
  have hFin : σ W < ⊤ := (measure_mono hWall).trans_lt hU.frontier_euclideanHausdorffMeasure_lt_top
  have hI := integrableOn_of_continuousOn_compact_finite_piece
    hU.1.2.2.isCompact_closure (hWall.trans frontier_subset_closure) hW hFin hCont
  exact hI.congr_fun
    (fun x hx => neg_centeredStressFlux_elasticStress_physical a ε Q D c ν (hn x (hWall hx)) (hVac x (hWall hx))) hW

private theorem physicalBoundaryStressCorrection_integral_lower
    (a : BulkCoefficients) (ε : ElasticScale) {U : Set Point} (hU : IsSmoothDomain U)
    {b Q : Point → S0} (hb : ContDiffOn ℝ 1 b (closure U)) (hQ : ContDiffOn ℝ 2 Q (closure U))
    (hTrace : EqOn Q b (frontier U)) (hVac : ∀ x ∈ frontier U, Q x ∈ vacuum a)
    {ν : Point → Point} (hν : ContDiffOn ℝ 1 ν (closure U)) (hνc : Continuous ν)
    (hn : ∀ x ∈ frontier U, HasRegularOutwardNormalAt U x (ν x))
    {c : Point} {r R M A G N : ℝ} (hr : 0 < r) (hR : r ≤ R)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hG : 0 ≤ G)
    (hHeight : ∀ x ∈ frontier U ∩ Metric.ball c r, -(M * r ^ 2) ≤ inner ℝ (x - c) (ν x))
    (hArea : (Measure.euclideanHausdorffMeasure 2 : Measure Point) (frontier U ∩ Metric.ball c r) ≤
      ENNReal.ofReal (A * r ^ 2))
    (hTangential : ∀ x ∈ frontier U, gradientNormSq
      (tangentialGradientColumns (closureGradient U b x) (ν x)) ≤ G)
    (hNormalInt : IntegrableOn (fun x => ‖gradientFromColumns (closureGradient U Q x) (ν x)‖ ^ 2)
      (frontier U) (Measure.euclideanHausdorffMeasure 2))
    (hNormalBound : (∫ x in frontier U ∩ Metric.ball c r,
      ‖gradientFromColumns (closureGradient U Q x) (ν x)‖ ^ 2 ∂(Measure.euclideanHausdorffMeasure 2)) ≤ N) :
    let C := (M + 1) / 2 * N + (R + 1) / 2 * G * A;
    -(C * r ^ 2) ≤ ∫ x in frontier U ∩ Metric.ball c r,
      physicalBoundaryStressCorrection (closureGradient U Q x) (x - c) (ν x)
        ∂(Measure.euclideanHausdorffMeasure 2) := by
  let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
  let W := frontier U ∩ Metric.ball c r
  let p (x : Point) := ‖gradientFromColumns (closureGradient U Q x) (ν x)‖ ^ 2
  let bT (x : Point) := gradientNormSq (tangentialGradientColumns (closureGradient U b x) (ν x))
  let f (x : Point) := physicalBoundaryStressCorrection (closureGradient U Q x) (x - c) (ν x)
  let m := (M + 1) / 2
  let k := (R + 1) / 2
  have hm : 0 ≤ m := by dsimp only [m]; linarith only [hM]
  have hk : 0 ≤ k := by dsimp only [k]; linarith only [hr, hR]
  have hW : MeasurableSet W := isClosed_frontier.measurableSet.inter Metric.isOpen_ball.measurableSet
  have hAreaFin : σ W < ⊤ := hArea.trans_lt ENNReal.ofReal_lt_top
  have hAreaReal : (σ W).toReal ≤ A * r ^ 2 := by
    have h := (ENNReal.toReal_le_toReal hAreaFin.ne ENNReal.ofReal_ne_top).mpr hArea
    rwa [ENNReal.toReal_ofReal (mul_nonneg hA (sq_nonneg _))] at h
  have hbT : ContinuousOn bT (closure U) :=
    continuousOn_closureTangentialGradientNormSq hU.uniqueDiffOn_closure hb hν
  have hIb : IntegrableOn bT W σ := integrableOn_of_continuousOn_compact_finite_piece
    hU.1.2.2.isCompact_closure (inter_subset_left.trans frontier_subset_closure) hW hAreaFin hbT
  have hBp : (∫ x in W, bT x ∂σ) ≤ (G * A) * r ^ 2 := calc
    _ ≤ ∫ x in W, G ∂σ :=
      setIntegral_mono_on hIb (integrableOn_const hAreaFin.ne) hW fun x hx => hTangential x hx.1
    _ = (σ W).toReal * G := by rw [setIntegral_const, smul_eq_mul]; rfl
    _ ≤ (A * r ^ 2) * G := mul_le_mul_of_nonneg_right hAreaReal hG
    _ = _ := by ring
  have hIf : IntegrableOn f W σ := integrableOn_physicalBoundaryStressCorrection a ε hU hQ hνc
    (fun x hx => (hn x hx).2.1) hVac c hW inter_subset_left
  have hIp : IntegrableOn p W σ := hNormalInt.mono_set inter_subset_left
  have hLower (x : Point) (hx : x ∈ W) : (-m * r ^ 2) * p x + (-k) * bT x ≤ f x := by
    have hn' := hn x hx.1
    have hbEq := tangentialGradientColumns_eq_of_boundary_trace (hQ.of_le (by norm_num)) hb hTrace
      hx.1 hn'.2.1 (fun _ hv => hU.exists_boundary_curve_of_inner_eq_zero hn' hv)
    have hv : ‖x - c‖ ≤ r := (show ‖x - c‖ < r by
      simpa only [Metric.mem_ball, dist_eq_norm] using hx.2).le
    have hPoint := physicalBoundaryStressCorrection_ge (closureGradient U Q x) (x - c) (ν x)
      hn'.2.1 hv (hHeight x hx)
    dsimp only at hPoint
    rw [hbEq] at hPoint
    have hK : -k ≤ -(1 / 2 : ℝ) * (r + 1) := by
      dsimp only [k]
      linarith only [hR]
    have hCoeff : (-k) * bT x ≤ -(1 / 2 : ℝ) * (r + 1) * bT x :=
      mul_le_mul_of_nonneg_right hK (gradientNormSq_nonneg _)
    change -(1 / 2 : ℝ) * (M + 1) * r ^ 2 * p x -
      (1 / 2 : ℝ) * (r + 1) * bT x ≤ f x at hPoint
    have hSame : -m * r ^ 2 * p x = -(1 / 2 : ℝ) * (M + 1) * r ^ 2 * p x := by
      dsimp only [m]
      ring
    rw [hSame]
    linarith only [hPoint, hCoeff]
  have hInt := setIntegral_mono_on
    ((hIp.const_mul (-m * r ^ 2)).add (hIb.const_mul (-k))) hIf hW hLower
  change (∫ x in W, (-m * r ^ 2) * p x + (-k) * bT x ∂σ) ≤ ∫ x in W, f x ∂σ at hInt
  rw [integral_add (hIp.const_mul _) (hIb.const_mul _), integral_const_mul, integral_const_mul] at hInt
  have hN' : N * (-m * r ^ 2) ≤ (∫ x in W, p x ∂σ) * (-m * r ^ 2) :=
    mul_le_mul_of_nonpos_right hNormalBound (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hm) (sq_nonneg _))
  have hB' : ((G * A) * r ^ 2) * (-k) ≤ (∫ x in W, bT x ∂σ) * (-k) :=
    mul_le_mul_of_nonpos_right hBp (neg_nonpos.mpr hk)
  change -((m * N + k * G * A) * r ^ 2) ≤ ∫ x in W, f x ∂σ
  linarith only [hInt, hN', hB']

private theorem monotoneOn_add_linear_of_ae_hasDerivAt_ge {F : ℝ → ℝ} {C R : ℝ}
    (hAbs : ∀ s t, 0 < s → s ≤ t → t ≤ R → AbsolutelyContinuousOnInterval F s t)
    (hDer : ∀ᵐ r : ℝ, r ∈ Ioo 0 R → ∃ d, HasDerivAt F d r ∧ -C ≤ d) :
    MonotoneOn (fun r => F r + C * r) (Ioc 0 R) := by
  intro s hs t ht hst
  rcases hst.eq_or_lt with rfl | hlt
  · exact le_rfl
  let G (r : ℝ) := F r + C * r
  have hLine : ContDiff ℝ 1 (fun r : ℝ => C * r) := contDiff_const.mul contDiff_id
  have hG : AbsolutelyContinuousOnInterval G s t :=
    (hAbs s t hs.1 hlt.le ht.2).fun_add hLine.contDiffOn.absolutelyContinuousOnInterval
  have hNonneg : 0 ≤ᵐ[volume.restrict (Ioo s t)] deriv G := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hDer] with r hD hr
    obtain ⟨d, hd, hLower⟩ := hD ⟨hs.1.trans hr.1, hr.2.trans_le ht.2⟩
    have hLineD := (hasDerivAt_id r).const_mul C
    change 0 ≤ deriv G r
    rw [show deriv G r = d + C * 1 from (hd.add hLineD).deriv, mul_one]
    linarith only [hLower]
  change G s ≤ G t
  apply sub_nonneg.mp
  rw [← hG.integral_deriv_eq_sub, intervalIntegral.integral_of_le hlt.le,
    ← restrict_Ioo_eq_restrict_Ioc]
  exact integral_nonneg_of_ae hNonneg

/-- Boundary energy quasi-monotonicity for actual classical solutions.
The correction is `C * r`. The constant is chosen from the bulk
coefficients, domain, fixed upper radius, prescribed trace and energy cap. -/
theorem exists_uniform_normalized_boundary_energy_quasiMonotone
    (hGG : External.LipschitzGaussGreen) (hSard : External.MorseSardPlaneToReal)
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    {b : Point → S0} (hb : ContDiffOn ℝ 1 b (closure U)) (hVac : ∀ x ∈ frontier U, b x ∈ vacuum a)
    {C₀ R : ℝ} (hC₀ : 0 ≤ C₀) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ElasticScale) (Q : Point → S0),
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U → ContDiffOn ℝ 2 Q (closure U) →
      EqOn Q b (frontier U) →
      (∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) →
      energy a ε U Q (ClassicalGradient Q) ≤ ENNReal.ofReal C₀ →
      ∀ c ∈ U,
        let F (r : ℝ) := (energy a ε (U ∩ Metric.ball c r) Q (ClassicalGradient Q)).toReal / r
        (∀ s t, 0 < s → s ≤ t → t ≤ R → AbsolutelyContinuousOnInterval F s t) ∧
        (∀ᵐ r : ℝ, r ∈ Ioo 0 R → ∃ d, HasDerivAt F d r ∧ -C ≤ d) ∧
        MonotoneOn (fun r => F r + C * r) (Ioc 0 R) := by
  obtain ⟨ν, N, hN, hν, hWall, hNormal⟩ :=
    exists_uniform_boundary_normal_energy_bound_of_smoothDomain hGG a hU hb hVac hC₀
  obtain ⟨M, hM, hHeight⟩ := hU.exists_quadratic_lower_bound_wall_chord hWall
  obtain ⟨A, hA, hArea⟩ := hU.exists_euclideanHausdorffMeasure_wall_ball_le
  have hν₁ : ContDiffOn ℝ 1 ν (closure U) := (hν.of_le (by simp)).contDiffOn
  let B (x : Point) := gradientNormSq (tangentialGradientColumns (closureGradient U b x) (ν x))
  have hBc : ContinuousOn B (closure U) :=
    continuousOn_closureTangentialGradientNormSq hU.uniqueDiffOn_closure hb hν₁
  have hWallCompact : IsCompact (frontier U) :=
    hU.1.2.2.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨G₀, hG₀⟩ := hWallCompact.exists_bound_of_continuousOn (hBc.mono frontier_subset_closure)
  let G := max G₀ 0
  have hG : 0 ≤ G := le_max_right _ _
  have hTang (x : Point) (hx : x ∈ frontier U) : B x ≤ G := by
    have hB := hG₀ x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (gradientNormSq_nonneg _)] at hB
    exact hB.trans (le_max_left _ _)
  let C₁ := (M + 1) / 2 * N + (R + 1) / 2 * G * A
  let C := C₁ + 1
  have hC : 0 < C := by
    have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
    exact add_pos_of_nonneg_of_pos hC₁ zero_lt_one
  refine ⟨C, hC, ?_⟩
  intro ε Q hQ hClose hTrace hEuler hCap c hc
  have hVacQ (x : Point) (hx : x ∈ frontier U) : Q x ∈ vacuum a := by
    rw [hTrace hx]
    exact hVac x hx
  have hSliced := (hU.ae_piecewiseRegularBoundary_inter_ball hSard hν.continuous hWall c).mono
    (fun _ h (hr : _ ∈ Ioo (0 : ℝ) R) => h hr.1)
  obtain ⟨hAbs, hD⟩ := ae_hasDerivAt_normalized_boundary_energy hGG a ε hU.1.1
    hU.uniqueDiffOn_closure hQ hClose hEuler c hR ν (fun x hx => (hWall x hx).2.1) hVacQ hSliced
  obtain ⟨hNormalInt, _, hNormalBound⟩ := hNormal ε Q hQ hClose hTrace hEuler hCap
  let D := closureGradient U Q
  let E (r : ℝ) := ∫ x in U ∩ Metric.ball c r, energyDensity a ε (Q x) (D x)
  let F (r : ℝ) := (energy a ε (U ∩ Metric.ball c r) Q (ClassicalGradient Q)).toReal / r
  have hFE : F = fun r => E r / r := by
    funext r
    have hEq := energy_classical_eq_ofReal_closureEnergyDensity a ε hU
      (W := U ∩ Metric.ball c r) inter_subset_left (hU.1.1.measurableSet.inter Metric.isOpen_ball.measurableSet)
      hClose
    dsimp only [F]
    rw [hEq, ENNReal.toReal_ofReal (integral_nonneg fun x => energyDensity_nonneg a ε (Q x) (D x))]
  have hAbs' : ∀ s t, 0 < s → s ≤ t → t ≤ R → AbsolutelyContinuousOnInterval F s t := hFE.symm ▸ hAbs
  have hBound : ∀ᵐ r : ℝ, r ∈ Ioo 0 R → ∃ d, HasDerivAt F d r ∧ -C ≤ d := by
    filter_upwards [hD] with r hd hr
    have hDer := hd hr
    refine ⟨_, hFE.symm ▸ hDer, ?_⟩
    apply (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr
    have hP : 0 ≤ ∫ x in U ∩ Metric.ball c r, (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x) :=
      integral_nonneg fun x => mul_nonneg (sq_nonneg _) (bulkPotential_nonneg _ _)
    have hZ : 0 ≤ ∫ x in U ∩ Metric.sphere c r,
        ‖gradientFromColumns (D x) (x - c)‖ ^ 2 ∂(Measure.euclideanHausdorffMeasure 2) :=
      integral_nonneg fun _ => sq_nonneg _
    have hZ' := mul_nonneg (inv_nonneg.mpr hr.1.le) hZ
    have hB := physicalBoundaryStressCorrection_integral_lower a ε hU hb hClose hTrace hVacQ
      hν₁ hν.continuous hWall hr.1 hr.2.le hM hA hG (hHeight c hc r hr.1) (hArea c r hr.1)
      hTang hNormalInt (hNormalBound c r)
    change -(C₁ * r ^ 2) ≤ _ at hB
    dsimp only [C]
    linarith only [hB, hP, hZ', sq_nonneg r]
  exact ⟨hAbs', hBound, monotoneOn_add_linear_of_ae_hasDerivAt_ge hAbs' hBound⟩

/-- The exact collar estimate propagates the global density defect and
limiting gradient bound from a fixed comparison ball to every smaller one. -/
theorem exists_boundary_collar_normalized_energy_bound
    (hGG : External.LipschitzGaussGreen) (hSard : External.MorseSardPlaneToReal)
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    {b : Point → S0} (hb : ContDiffOn ℝ 1 b (closure U)) (hVac : ∀ x ∈ frontier U, b x ∈ vacuum a)
    {V K : Set Point} (hV : IsOpen V) (hK : IsCompact K) (hKsub : K ⊆ closure U ∩ V)
    {q : Point → S0} {G : Point → Gradient} (hq : ContDiffOn ℝ 2 q (closure U ∩ V))
    (hGLp : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict U))
    (hGrad : G =ᵐ[volume.restrict U] ClassicalGradient q)
    {C₀ R₁ : ℝ} (hC₀ : 0 ≤ C₀) (hR₁ : 0 < R₁) :
    ∃ R₀ M C : ℝ, 0 < R₀ ∧ R₀ ≤ R₁ ∧ 0 ≤ M ∧ 0 < C ∧
      ∀ (ε : ElasticScale) (Q : Point → S0),
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U → ContDiffOn ℝ 2 Q (closure U) →
        EqOn Q b (frontier U) →
        (∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) →
        energy a ε U Q (ClassicalGradient Q) ≤ ENNReal.ofReal C₀ →
        ∀ x ∈ U ∩ K, ∀ R ∈ Ioo 0 R₀, ∀ s ∈ Ioc 0 R,
          ENNReal.ofReal (s⁻¹) * energy a ε (U ∩ Metric.ball x s) Q (ClassicalGradient Q) ≤
            ENNReal.ofReal (R⁻¹) * energyDensityDefect a ε U Q (ClassicalGradient Q) G +
              ENNReal.ofReal ((M / 2) * (Real.pi * 4 / 3) * R ^ 2 + C * R) := by
  obtain ⟨C, hC, hMono⟩ := exists_uniform_normalized_boundary_energy_quasiMonotone hGG hSard
    a hU hb hVac hC₀ hR₁
  obtain ⟨R₀, M, hR₀, hM, hBase⟩ :=
    exists_boundary_collar_base_radius_bound hU.1.1 hV hq hK hKsub hGLp hGrad
  refine ⟨min R₀ R₁, M, C, lt_min hR₀ hR₁, min_le_right _ _, hM, hC, ?_⟩
  intro ε Q hQ hClose hTrace hEuler hCap x hx R hR s hs
  have hR₀' : R < R₀ := hR.2.trans_le (min_le_left _ _)
  have hR₁' : R < R₁ := hR.2.trans_le (min_le_right _ _)
  let A := (M / 2) * (Real.pi * 4 / 3)
  have hAR : 0 ≤ A * R ^ 2 := by dsimp only [A]; positivity
  let e (t : ℝ) := energy a ε (U ∩ Metric.ball x t) Q (ClassicalGradient Q)
  let F (t : ℝ) := (e t).toReal / t
  let η := energyDensityDefect a ε U Q (ClassicalGradient Q) G
  have hFinite (t : ℝ) : e t ≠ ⊤ := by
    change energy a ε (U ∩ Metric.ball x t) Q (ClassicalGradient Q) ≠ ⊤
    rw [energy_classical_eq_ofReal_closureEnergyDensity a ε hU inter_subset_left
      (hU.1.1.measurableSet.inter Metric.isOpen_ball.measurableSet) hClose]
    exact ENNReal.ofReal_ne_top
  have hNorm (t : ℝ) (ht : 0 < t) : ENNReal.ofReal (F t) = ENNReal.ofReal (t⁻¹) * e t := by
    change ENNReal.ofReal ((e t).toReal / t) = _
    rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (inv_nonneg.mpr ht.le), ENNReal.ofReal_toReal (hFinite t)]
  have hMono' := (hMono ε Q hQ hClose hTrace hEuler hCap x hx.1).2.2
  have hProp := hMono' (show s ∈ Ioc 0 R₁ from ⟨hs.1, hs.2.trans hR₁'.le⟩)
    (show R ∈ Ioc 0 R₁ from ⟨hR.1, hR₁'.le⟩) hs.2
  have hStep : F s ≤ F R + C * R := by
    change F s + C * s ≤ F R + C * R at hProp
    exact (le_add_of_nonneg_right (mul_nonneg hC.le hs.1.le)).trans hProp
  have hEBase := hBase x hx.2 R ⟨hR.1, hR₀'⟩ a ε Q (ClassicalGradient Q)
  change ENNReal.ofReal R⁻¹ * e R ≤ ENNReal.ofReal R⁻¹ * η + ENNReal.ofReal (A * R ^ 2) at hEBase
  rw [← hNorm R hR.1] at hEBase
  have hCR : 0 ≤ C * R := mul_nonneg hC.le hR.1.le
  have hFR : 0 ≤ F R := div_nonneg ENNReal.toReal_nonneg hR.1.le
  change ENNReal.ofReal s⁻¹ * e s ≤ ENNReal.ofReal R⁻¹ * η + ENNReal.ofReal (A * R ^ 2 + C * R)
  calc
    _ = ENNReal.ofReal (F s) := (hNorm s hs.1).symm
    _ ≤ ENNReal.ofReal (F R + C * R) := ENNReal.ofReal_le_ofReal hStep
    _ = ENNReal.ofReal (F R) + ENNReal.ofReal (C * R) := ENNReal.ofReal_add hFR hCR
    _ ≤ (ENNReal.ofReal R⁻¹ * η + ENNReal.ofReal (A * R ^ 2)) + ENNReal.ofReal (C * R) :=
      add_le_add_left hEBase _
    _ = _ := by rw [add_assoc, ← ENNReal.ofReal_add hAR hCR]

/-- The actual normalized penalized energy is uniformly small at every
positive radius up to a fixed small radius in a regular compact collar. -/
theorem exists_boundary_collar_uniform_small_normalized_energy
    (hGG : External.LipschitzGaussGreen) (hSard : External.MorseSardPlaneToReal)
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    {b : Point → S0} (hb : ContDiffOn ℝ 1 b (closure U)) (hVac : ∀ x ∈ frontier U, b x ∈ vacuum a)
    {V K : Set Point} (hV : IsOpen V) (hK : IsCompact K) (hKsub : K ⊆ closure U ∩ V)
    {q : Point → S0} {G : Point → Gradient} (hq : ContDiffOn ℝ 2 q (closure U ∩ V))
    (hGrad : G =ᵐ[volume.restrict U] ClassicalGradient q)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0)
    (hStrong : StrongH1 U Q (fun n => ClassicalGradient (Q n)) q G)
    (hBulkLp : ∀ n, MemLp (fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n x)) 1
      (volume.restrict U))
    (hBulk : Tendsto (fun n => eLpNorm (fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n x))
      1 (volume.restrict U)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (Q n) U)
    (hClose : ∀ n, ContDiffOn ℝ 2 (Q n) (closure U))
    (hTrace : ∀ n, EqOn (Q n) b (frontier U))
    (hEuler : ∀ n, ∀ x ∈ U, (ε n : ℝ) ^ 2 • (↑(laplacian (Q n) x) : Tensor) = bulkGradient a (Q n x))
    {C₀ R₁ δ : ℝ} (hC₀ : 0 ≤ C₀) (hR₁ : 0 < R₁) (hδ : 0 < δ)
    (hCap : ∀ n, energy a (ε n) U (Q n) (ClassicalGradient (Q n)) ≤ ENNReal.ofReal C₀) :
    ∃ R ∈ Ioo 0 R₁, ∀ᶠ n in atTop, ∀ x ∈ U ∩ K, ∀ s ∈ Ioc 0 R,
      ENNReal.ofReal (s⁻¹) * energy a (ε n) (U ∩ Metric.ball x s) (Q n) (ClassicalGradient (Q n)) <
        ENNReal.ofReal δ := by
  obtain ⟨R₀, M, C, hR₀, hR₀R₁, hM, hC, hBound⟩ :=
    exists_boundary_collar_normalized_energy_bound hGG hSard a hU hb hVac hV hK hKsub hq
      (fun j => hStrong.2.1.2.1 j) hGrad hC₀ hR₁
  let A := (M / 2) * (Real.pi * 4 / 3)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let p (r : ℝ) := A * r ^ 2 + C * r
  have hp : Continuous p := by dsimp only [p]; fun_prop
  have hp0 : p 0 = 0 := by simp only [p, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero]
  have hSmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), p r < δ / 2 :=
    nhdsWithin_le_nhds
      (hp.continuousAt.eventually_lt continuousAt_const (show p 0 < δ / 2 by rw [hp0]; positivity))
  have hNear : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < R₀ := nhdsWithin_le_nhds (Iio_mem_nhds hR₀)
  have hPos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨R, hR, hR₀', hRS⟩ := (hPos.and (hNear.and hSmall)).exists
  have hR₁' : R < R₁ := hR₀'.trans_le hR₀R₁
  let η (n : ℕ) := energyDensityDefect a (ε n) U (Q n) (ClassicalGradient (Q n)) G
  have hη : Tendsto η atTop (𝓝 0) := tendsto_energyDensityDefect_zero_of_strongH1 a ε hStrong hBulkLp hBulk
  have hScaled : Tendsto (fun n => ENNReal.ofReal R⁻¹ * η n) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hη (Or.inr ENNReal.ofReal_ne_top)
  refine ⟨R, ⟨hR, hR₁'⟩, ?_⟩
  have hηR : ∀ᶠ n in atTop, ENNReal.ofReal R⁻¹ * η n < ENNReal.ofReal (δ / 2) :=
    hScaled (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hδ)))
  filter_upwards [hηR] with n hn x hx s hs
  have hUpper := hBound (ε n) (Q n) (hQ n) (hClose n) (hTrace n) (hEuler n) (hCap n) x hx
    R ⟨hR, hR₀'⟩ s hs
  have hpR : 0 ≤ p R := add_nonneg (mul_nonneg hA (sq_nonneg _)) (mul_nonneg hC.le hR.le)
  have hTol : δ / 2 + p R < δ := by linarith only [hRS]
  calc
    _ ≤ ENNReal.ofReal R⁻¹ * η n + ENNReal.ofReal (p R) := hUpper
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (p R) := add_le_add_left hn.le _
    _ = ENNReal.ofReal (δ / 2 + p R) := (ENNReal.ofReal_add (half_pos hδ).le hpR).symm
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hTol

end Thesis

end
