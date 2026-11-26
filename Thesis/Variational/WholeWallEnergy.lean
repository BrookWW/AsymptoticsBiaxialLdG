module

public import Thesis.Variational.SmoothWallGeometry
public import Thesis.Variational.VacuumExtension
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! Whole-wall geometry and the uniform boundary normal-energy estimate. -/

public section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal BigOperators Pointwise Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem local_frontier_subset_lipschitz_chart_image
    {U : Set Point} (hU : IsSmoothDomain U) {a : Point} (ha : a ∈ frontier U) :
    ∃ (r : ℝ) (Γ : Plane → Point) (L : ℝ≥0) (π : Point →L[ℝ] Plane), 0 < r ∧
      LipschitzOnWith L Γ (Metric.closedBall 0 r) ∧
      (∀ z, ‖π z‖ ≤ ‖z‖) ∧
      ∀ y ∈ frontier U ∩ Metric.ball a r, π (y - a) ∈ Metric.closedBall 0 r ∧ Γ (π (y - a)) = y := by
  obtain ⟨r, A, g, hr, hg, _, hChart⟩ := hU.2 a ha
  let E : Point ≃L[ℝ] Plane × EuclideanSpace ℝ (Fin 1) :=
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let P : Point →L[ℝ] Plane := (ContinuousLinearMap.fst ℝ Plane (EuclideanSpace ℝ (Fin 1))).comp
    E.toContinuousLinearMap
  let H : Point →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3)
  have hP (z : Point) : P z = WithLp.toLp 2 ![z 0, z 1] := by
    ext i
    fin_cases i <;> rfl
  have hNormP (z : Point) : ‖P z‖ ≤ ‖z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_three]
    have h0 : (P z) 0 = z 0 := congrArg (fun p : Plane => p 0) (hP z)
    have h1 : (P z) 1 = z 1 := congrArg (fun p : Plane => p 1) (hP z)
    rw [h0, h1]
    linarith only [sq_nonneg (z 2)]
  let Y (y : Point) := A (y - a)
  let φ (y : Point) := g (P (Y y)) - H (Y y)
  have hYS : ContDiff ℝ ∞ Y := A.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
    (contDiff_id.sub contDiff_const)
  have hφ : ContDiff ℝ ∞ φ := (hg.comp (P.contDiff.comp hYS)).sub (H.contDiff.comp hYS)
  have hDef : U ∩ Metric.ball a r = {y | φ y < 0} ∩ Metric.ball a r := by
    change U ∩ Metric.ball a r = {y | g (P (Y y)) - (Y y) 2 < 0} ∩ Metric.ball a r
    simpa only [hP, Y, sub_neg] using hChart
  let e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  let Γ (p : Plane) := a + A.symm (E.symm (p, g p • e))
  have hΓ : ContDiff ℝ ∞ Γ := contDiff_const.add
    (A.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
      (E.symm.toContinuousLinearMap.contDiff.comp (contDiff_id.prodMk (hg.smul contDiff_const))))
  have hd := hΓ.differentiable (by simp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Plane) r).exists_bound_of_continuousOn
    (hΓ.continuous_fderiv (by simp)).continuousOn
  let L : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hLip : LipschitzOnWith L Γ (Metric.closedBall 0 r) := by
    apply (convex_closedBall (0 : Plane) r).lipschitzOnWith_of_nnnorm_fderiv_le (fun p _ => hd p)
    intro p hp
    change ‖fderiv ℝ Γ p‖₊ ≤ L
    exact_mod_cast (hM p hp).trans (le_max_left M 0)
  let π := P.comp A.toContinuousLinearEquiv.toContinuousLinearMap
  have hNormπ (z : Point) : ‖π z‖ ≤ ‖z‖ := (hNormP (A z)).trans (A.norm_map z).le
  refine ⟨r, Γ, L, π, hr, hLip, hNormπ, ?_⟩
  intro y hy
  let p := P (Y y)
  have hφ0 : φ y = 0 := localDefiningFunction_eq_zero_on_frontier hU.1.1
    hφ.continuous.continuousOn hDef hy.1 hy.2
  have hHeight : (Y y) 2 = g p := (sub_eq_zero.mp hφ0).symm
  have hp : p ∈ Metric.closedBall 0 r := by
    have hDist : ‖y - a‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hy.2
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      _ ≤ ‖Y y‖ := hNormP (Y y)
      _ = ‖y - a‖ := A.norm_map _
      _ ≤ r := hDist.le
  have hCoord : E (Y y) = (p, g p • e) := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i
      change (Y y) 2 = (g p • e) 0
      simp only [PiLp.smul_apply, e, PiLp.single_apply, if_true, smul_eq_mul, mul_one, hHeight]
  refine ⟨hp, ?_⟩
  change a + A.symm (E.symm (p, g p • e)) = y
  rw [← hCoord, E.symm_apply_apply]
  change a + A.symm (A (y - a)) = y
  rw [A.symm_apply_apply]
  abel

/-- The actual compact frontier has finite Euclidean two-dimensional
Hausdorff area. The proof uses locally Lipschitz two-dimensional charts. -/
theorem IsSmoothDomain.frontier_euclideanHausdorffMeasure_lt_top
    {U : Set Point} (hU : IsSmoothDomain U) :
    (Measure.euclideanHausdorffMeasure 2 : Measure Point) (frontier U) < ⊤ := by
  classical
  let K := frontier U
  have hK : IsCompact K := hU.1.2.2.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hLocal (a : K) := local_frontier_subset_lipschitz_chart_image hU a.property
  choose r Γ L π hr hLip _ hProj using hLocal
  let W (a : K) := Metric.ball (a : Point) (r a)
  have hW (a : K) : IsOpen (W a) := Metric.isOpen_ball
  have hCover : K ⊆ ⋃ a : K, W a := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hr ⟨y, hy⟩)⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover W hW hCover
  have hCover' : K ⊆ ⋃ a ∈ I, K ∩ W a := by
    intro y hy
    obtain ⟨a, ha, hY⟩ := mem_iUnion₂.mp (hI hy)
    exact mem_iUnion₂.mpr ⟨a, ha, hy, hY⟩
  let μ : Measure Point := Measure.hausdorffMeasure 2
  have hArea (a : K) : μ (K ∩ W a) < ⊤ := by
    have ht := (hLip a).hausdorffMeasure_image_le (d := (2 : ℝ)) (by norm_num)
    have hD : (Measure.hausdorffMeasure 2 : Measure Plane) (Metric.closedBall 0 (r a)) < ⊤ := by
      letI : (Measure.hausdorffMeasure 2 : Measure Plane).IsAddHaarMeasure := by
        simpa only [Plane, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] using
          (MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := Plane))
      exact (isCompact_closedBall (0 : Plane) (r a)).measure_lt_top
    have hL : (L a : ℝ≥0∞) ^ (2 : ℝ) < ⊤ := by rw [ENNReal.rpow_two]; exact ENNReal.pow_lt_top ENNReal.coe_lt_top
    have hSub : K ∩ W a ⊆ Γ a '' Metric.closedBall 0 (r a) := by
      intro y hy
      exact ⟨π a (y - (a : Point)), (hProj a y hy).1, (hProj a y hy).2⟩
    exact ((measure_mono hSub).trans ht).trans_lt (ENNReal.mul_lt_top hL hD)
  have hKArea : μ K < ⊤ := calc
    _ ≤ μ (⋃ a ∈ I, K ∩ W a) := measure_mono hCover'
    _ ≤ ∑ a ∈ I, μ (K ∩ W a) := measure_biUnion_finset_le I _
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun a _ => hArea a
  change (Measure.euclideanHausdorffMeasure 2 : Measure Point) K < ⊤
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hKArea

/-- The wall has quadratic surface-area growth, uniformly in the center
and positive radius of the ball. -/
theorem IsSmoothDomain.exists_euclideanHausdorffMeasure_wall_ball_le
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (c : Point) (r : ℝ), 0 < r →
      (Measure.euclideanHausdorffMeasure 2 : Measure Point) (frontier U ∩ Metric.ball c r) ≤
        ENNReal.ofReal (M * r ^ 2) := by
  classical
  let K := frontier U
  let μ : Measure Point := Measure.hausdorffMeasure 2
  let μP : Measure Plane := Measure.hausdorffMeasure 2
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ≥0, (Measure.euclideanHausdorffMeasure 2 : Measure Point) = θ • μ := by
    rw [Measure.euclideanHausdorffMeasure_def]
    exact ⟨_, by simp only [μ, Nat.cast_ofNat]; rfl⟩
  haveI : μP.IsAddHaarMeasure := by
    simpa only [Plane, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] using
      (MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := Plane))
  have hUnit : μP (Metric.ball 0 1) < ⊤ :=
    (measure_mono Metric.ball_subset_closedBall).trans_lt
      ((isCompact_closedBall (0 : Plane) 1).measure_lt_top (μ := μP))
  have hBall (p : Plane) {r : ℝ} (hr : 0 < r) :
      μP (Metric.ball p r) = μP (Metric.ball 0 1) * ENNReal.ofReal (r ^ 2) := by
    let E := IsometryEquiv.addLeft p
    have hTranslate : E '' Metric.ball 0 r = Metric.ball p r := by
      rw [E.image_ball]
      change Metric.ball (p + 0) r = Metric.ball p r
      rw [add_zero]
    have hScale : r • Metric.ball (0 : Plane) 1 = Metric.ball 0 r := by
      rw [smul_ball hr.ne', smul_zero, Real.norm_of_nonneg hr.le, mul_one]
    change Measure.hausdorffMeasure 2 (Metric.ball p r) = _
    rw [← hTranslate, IsometryEquiv.hausdorffMeasure_image, ← hScale,
      Measure.hausdorffMeasure_smul₀ (by norm_num : (0 : ℝ) ≤ 2) hr.ne', NNReal.rpow_two]
    change (↑(‖r‖₊ ^ 2) : ℝ≥0∞) * μP (Metric.ball 0 1) = _
    rw [mul_comm, ENNReal.coe_pow, ENNReal.ofReal_pow hr.le, Real.nnnorm_of_nonneg hr.le,
      ENNReal.ofReal_eq_coe_nnreal hr.le]
  have hK : IsCompact K := hU.1.2.2.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hLocal (a : K) := local_frontier_subset_lipschitz_chart_image hU a.property
  choose R Γ L π hR hLip hπ hProj using hLocal
  let W (a : K) := Metric.ball (a : Point) (R a)
  have hCover : K ⊆ ⋃ a : K, W a := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hR ⟨y, hy⟩)⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover W (fun _ => Metric.isOpen_ball) hCover
  let w (a : K) : ℝ≥0∞ := (L a : ℝ≥0∞) ^ (2 : ℝ) * μP (Metric.ball 0 1)
  let M := (θ : ℝ≥0∞) * ∑ a ∈ I, w a
  have hM : M ≠ ⊤ := (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (ENNReal.sum_lt_top.mpr fun a _ => by
      apply ENNReal.mul_lt_top _ hUnit
      rw [ENNReal.rpow_two]
      exact ENNReal.pow_lt_top ENNReal.coe_lt_top)).ne
  refine ⟨M.toReal, ENNReal.toReal_nonneg, fun c r hr => ?_⟩
  let Z (a : K) := Metric.closedBall (0 : Plane) (R a) ∩ Metric.ball (π a (c - (a : Point))) r
  have hBound (a : K) :
      μ ((K ∩ W a) ∩ Metric.ball c r) ≤ w a * ENNReal.ofReal (r ^ 2) := by
    have hSub : (K ∩ W a) ∩ Metric.ball c r ⊆ Γ a '' Z a := by
      intro y hy
      let p := π a (y - (a : Point))
      have hp : Γ a p = y := (hProj a y hy.1).2
      have hDiff : p - π a (c - (a : Point)) = π a (y - c) := by
        change π a (y - (a : Point)) - π a (c - (a : Point)) = π a (y - c)
        rw [← map_sub]
        congr 1
        abel
      have hpNear : p ∈ Metric.ball (π a (c - (a : Point))) r := by
        rw [Metric.mem_ball, dist_eq_norm, hDiff]
        exact (hπ a (y - c)).trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hy.2)
      exact ⟨p, ⟨(hProj a y hy.1).1, hpNear⟩, hp⟩
    calc
      _ ≤ μ (Γ a '' Z a) := measure_mono hSub
      _ ≤ (L a : ℝ≥0∞) ^ (2 : ℝ) * μP (Z a) :=
        ((hLip a).mono inter_subset_left).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ _ := by
        change _ ≤ ((L a : ℝ≥0∞) ^ (2 : ℝ) * μP (Metric.ball 0 1)) * ENNReal.ofReal (r ^ 2)
        rw [mul_assoc, ← hBall (π a (c - (a : Point))) hr]
        exact mul_le_mul_right (measure_mono inter_subset_right) _
  have hSub : K ∩ Metric.ball c r ⊆ ⋃ a ∈ I, (K ∩ W a) ∩ Metric.ball c r := by
    intro y hy
    obtain ⟨a, ha, hW⟩ := mem_iUnion₂.mp (hI hy.1)
    exact mem_iUnion₂.mpr ⟨a, ha, ⟨hy.1, hW⟩, hy.2⟩
  have hRaw : μ (K ∩ Metric.ball c r) ≤ (∑ a ∈ I, w a) * ENNReal.ofReal (r ^ 2) := by
    calc
      _ ≤ μ (⋃ a ∈ I, (K ∩ W a) ∩ Metric.ball c r) := measure_mono hSub
      _ ≤ ∑ a ∈ I, μ ((K ∩ W a) ∩ Metric.ball c r) := measure_biUnion_finset_le I _
      _ ≤ _ := by rw [Finset.sum_mul]; exact Finset.sum_le_sum fun a _ => hBound a
  change (Measure.euclideanHausdorffMeasure 2 : Measure Point) (K ∩ Metric.ball c r) ≤ _
  rw [hθ, Measure.smul_apply, ENNReal.smul_def,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hM]
  change (θ : ℝ≥0∞) * μ (K ∩ Metric.ball c r) ≤
    ((θ : ℝ≥0∞) * ∑ a ∈ I, w a) * ENNReal.ofReal (r ^ 2)
  rw [mul_assoc]
  exact mul_le_mul_right hRaw _

/-- The actual smooth bounded wall is an admissible whole-wall domain for
Gauss–Green, with the globally extended outward normal. -/
theorem IsSmoothDomain.exists_piecewiseRegularBoundary
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ X : Point → Point, ContDiff ℝ ∞ X ∧ PiecewiseRegularBoundary U X ∧
      ∀ x ∈ frontier U, HasRegularOutwardNormalAt U x (X x) := by
  obtain ⟨X, hX, hXwall⟩ := hU.exists_smooth_outward_normal_extension
  refine ⟨X, hX, ⟨hU.1.1, hU.1.2.2, hU.hasLocallyLipschitzBoundary,
    hU.frontier_euclideanHausdorffMeasure_lt_top, hX.continuous.measurable.aemeasurable, ?_⟩, hXwall⟩
  exact (ae_restrict_mem isClosed_frontier.measurableSet).mono hXwall

/-- `claimQvanu` on a smooth domain with a fixed ambient extension of the
vacuum wall datum. The normal field and bound are chosen before the scale,
solution, and ball center. -/
theorem exists_uniform_boundary_normal_energy_bound_of_smoothDomain
    (hGG : External.LipschitzGaussGreen) (a : BulkCoefficients)
    {U : Set Point} (hU : IsSmoothDomain U) {b : Point → S0}
    (hb : ContDiffOn ℝ 1 b (closure U)) (hVac : ∀ x ∈ frontier U, b x ∈ vacuum a)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ (ν : Point → Point) (C : ℝ), 0 < C ∧ ContDiff ℝ ∞ ν ∧
      (∀ x ∈ frontier U, HasRegularOutwardNormalAt U x (ν x)) ∧
      ∀ (ε : ElasticScale) (Q : Point → S0),
        ContDiffOn ℝ ∞ Q U → ContDiffOn ℝ 2 Q (closure U) → EqOn Q b (frontier U) →
        (∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) →
        energy a ε U Q (ClassicalGradient Q) ≤ ENNReal.ofReal C₀ →
        let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
        let N (x : Point) := ‖gradientFromColumns (closureGradient U Q x) (ν x)‖ ^ 2
        IntegrableOn N (frontier U) σ ∧
          (∫ x in frontier U, N x ∂σ) ≤ C ∧
          ∀ c : Point, ∀ r : ℝ,
            (∫ x in frontier U ∩ Metric.ball c r, N x ∂σ) ≤ C := by
  obtain ⟨ν, hν, hGeo, hNormal⟩ := hU.exists_piecewiseRegularBoundary
  let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
  have hCurves : ∀ᵐ x ∂(σ.restrict (frontier U)),
      ∀ v : Point, inner ℝ v (ν x) = 0 → ∃ γ : ℝ → Point,
        γ 0 = x ∧ HasDerivAt γ v 0 ∧ ∀ᶠ t in 𝓝 0, γ t ∈ frontier U :=
    (ae_restrict_mem isClosed_frontier.measurableSet).mono fun x hx v hv =>
      hU.exists_boundary_curve_of_inner_eq_zero (hNormal x hx) hv
  obtain ⟨L, hL, _, _, hBound⟩ := exists_uniform_boundary_normal_energy_bound hGG a hGeo
    hU.uniqueDiffOn_closure (hν.of_le (by simp)).contDiffOn (fun _ _ => rfl) hb hVac hCurves hC₀
  let B (x : Point) := gradientNormSq (tangentialGradientColumns (closureGradient U b x) (ν x))
  let K := (∫ x in frontier U, B x ∂σ) + 36 * L * C₀
  have hK : 0 ≤ K := by
    apply add_nonneg _ (mul_nonneg (mul_nonneg (by norm_num) hL) hC₀)
    apply integral_nonneg
    intro x
    simp only [B, gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨ν, K + 1, by linarith only [hK], hν, hNormal, ?_⟩
  intro ε Q hQ hC hTrace hEuler hE
  have hE' : energy a ε U Q (closureGradient U Q) ≤ ENNReal.ofReal C₀ := by
    refine le_trans (le_of_eq ?_) hE
    unfold energy
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hU.1.1.measurableSet] with x hx
    rw [closureGradient_eq_classicalGradient hU.1.1 hC hx]
  obtain ⟨hN, hn, hPatch⟩ := hBound ε Q hQ hC hTrace hEuler hE'
  have hUpper : K ≤ K + 1 := by linarith
  exact ⟨hN, hn.trans hUpper, fun c r => (hPatch c r).trans hUpper⟩

/-- Whole-wall normal energy for the prescribed smooth quaternion lift in
the frozen global Dirichlet problem. -/
theorem exists_uniform_boundary_normal_energy_bound_of_smoothBoundaryLift
    (hGG : External.LipschitzGaussGreen) (a : BulkCoefficients)
    {U : Set Point} (hU : IsSmoothDomain U) {b : frontier U → Sphere3}
    (hLift : IsSmoothBoundaryLift U b) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ (ν : Point → Point) (C : ℝ), 0 < C ∧ ContDiff ℝ ∞ ν ∧
      (∀ x ∈ frontier U, HasRegularOutwardNormalAt U x (ν x)) ∧
      ∀ (ε : ElasticScale) (Q : Point → S0),
        ContDiffOn ℝ ∞ Q U → ContDiffOn ℝ 2 Q (closure U) →
        (∀ x : frontier U, Q x = cover a (b x)) →
        (∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) →
        energy a ε U Q (ClassicalGradient Q) ≤ ENNReal.ofReal C₀ →
        let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
        let N (x : Point) := ‖gradientFromColumns (closureGradient U Q x) (ν x)‖ ^ 2
        IntegrableOn N (frontier U) σ ∧
          (∫ x in frontier U, N x ∂σ) ≤ C ∧
          ∀ c : Point, ∀ r : ℝ,
            (∫ x in frontier U ∩ Metric.ball c r, N x ∂σ) ≤ C := by
  obtain ⟨_, _, _, hTrace, _, _⟩ := exists_vacuum_competitor_of_smoothBoundaryLift a
    hU.1.1 hU.1.2.2 hLift
  obtain ⟨B, hB, hData, _⟩ := hTrace
  have hBVac : ∀ x ∈ frontier U, B x ∈ vacuum a := by
    intro x hx
    exact (hData ⟨x, hx⟩).symm ▸ cover_mem_vacuum a (b ⟨x, hx⟩)
  obtain ⟨ν, C, hC, hν, hNormal, hBound⟩ := exists_uniform_boundary_normal_energy_bound_of_smoothDomain
    hGG a hU (hB.of_le (by simp)).contDiffOn hBVac hC₀
  refine ⟨ν, C, hC, hν, hNormal, ?_⟩
  intro ε Q hQ hCl hTraceQ hEuler hE
  have hTraceQB : EqOn Q B (frontier U) :=
    fun x hx => (hTraceQ ⟨x, hx⟩).trans (hData ⟨x, hx⟩).symm
  exact hBound ε Q hQ hCl hTraceQB hEuler hE

end Thesis

end
