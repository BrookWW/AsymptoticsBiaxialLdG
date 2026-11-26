module

public import Thesis.MeasureGeometry.FlatStress

/-! The density and cone conditions for the one-dimensional Hausdorff carrier. -/

public section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

private theorem flat_line_ball_mass (L : Submodule ℝ Point) (hL : Module.finrank ℝ L = 1)
    (b : ℝ) (R : ℝ) :
    (ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)) (closedBall 0 R) =
      ENNReal.ofReal b * ENNReal.ofReal (2 * R) := by
  rw [Measure.smul_apply, smul_eq_mul, hausdorffOne_restrict_line_closedBall L hL]

private theorem measure_toReal_le_integral_of_eq_one {s : Set Point} (hs : MeasurableSet s)
    {μ : Measure Point} {f : Point → ℝ} (hf : Integrable f μ) (h0 : ∀ y, 0 ≤ f y)
    (h1 : ∀ y ∈ s, f y = 1) : (μ s).toReal ≤ ∫ y, f y ∂μ := by
  calc
    _ = ∫ y in s, f y ∂μ := by
      rw [setIntegral_congr_fun hs (g := fun _ => 1) h1, setIntegral_const, smul_eq_mul, mul_one]
      rfl
    _ ≤ _ := setIntegral_le_integral hf (Eventually.of_forall h0)

private theorem bump_ball_mass_bounds (χ : ContDiffBump (0 : Point)) (μ : Measure Point)
    [IsFiniteMeasureOnCompacts μ] :
    (μ (closedBall 0 χ.rIn)).toReal ≤ (∫ y, χ y ∂μ) ∧
      (∫ y, χ y ∂μ) ≤ (μ (closedBall 0 χ.rOut)).toReal := by
  have hInt := (χ.contDiff (n := 0)).continuous.integrable_of_hasCompactSupport χ.hasCompactSupport
    (μ := μ)
  constructor
  · exact measure_toReal_le_integral_of_eq_one measurableSet_closedBall hInt χ.nonneg'
      (fun _ hy => χ.one_of_mem_closedBall hy)
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall 0 χ.rOut)
      (fun y hy => image_eq_zero_of_notMem_tsupport (by rwa [χ.tsupport_eq]))]
    calc
      _ ≤ ∫ _ in closedBall (0 : Point) χ.rOut, (1 : ℝ) ∂μ :=
        setIntegral_mono_on hInt.integrableOn
          (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne)
          measurableSet_closedBall (fun _ _ => χ.le_one)
      _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_one]; rfl

/-- Vague convergence to a weighted line gives the centered closed-ball mass
at every positive test radius. The constant is the Euclidean line length. -/
theorem tendsto_flatBlowup_closedBall_mass {μ : Measure Point} [IsFiniteMeasure μ]
    {x : Point} {L : Submodule ℝ Point} (hL : Module.finrank ℝ L = 1)
    {b : ℝ} (hb : 0 < b)
    (hV : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r μ)
      (ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)))
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r : ℝ => ((SupportingAnalysis.blownUpMeasure (d := 1) x r μ)
      (closedBall 0 R)).toReal) (𝓝[>] 0) (𝓝 (b * (2 * R))) := by
  let ν (r : ℝ) := SupportingAnalysis.blownUpMeasure (d := 1) x r μ
  let τ := ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)
  letI : IsFiniteMeasureOnCompacts τ := flat_line_finite_on_compacts L hL b
  have hτmass (s : ℝ) (hs : 0 ≤ s) : (τ (closedBall 0 s)).toReal = b * (2 * s) := by
    rw [flat_line_ball_mass L hL, ENNReal.toReal_mul, ENNReal.toReal_ofReal hb.le,
      ENNReal.toReal_ofReal (mul_nonneg zero_le_two hs)]
  have h2b : 0 < 2 * b := mul_pos zero_lt_two hb
  apply tendsto_order.2
  constructor
  · intro z hz
    obtain ⟨s, hs, hsR⟩ := exists_between
      (max_lt hR ((div_lt_iff₀ h2b).2 (by linarith only [hz])) : max 0 (z / (2 * b)) < R)
    have hs0 : 0 < s := (le_max_left _ _).trans_lt hs
    let χ : ContDiffBump (0 : Point) := ⟨s, R, hs0, hsR⟩
    have hτ : z < ∫ y, χ y ∂τ := by
      have hs' := (div_lt_iff₀ h2b).1 ((le_max_right 0 _).trans_lt hs)
      refine (show z < b * (2 * s) from by linarith only [hs']).trans_le ?_
      rw [← hτmass s hs0.le]
      exact (bump_ball_mass_bounds χ τ).1
    have hConv := hV (χ : Point → ℝ) (χ.contDiff (n := 0)).continuous χ.hasCompactSupport (subset_univ _)
    filter_upwards [hConv (Ioi_mem_nhds hτ)] with r hr
    letI := SupportingAnalysis.blownUpMeasure_isFiniteMeasure (d := 1) x r μ
    exact hr.trans_le (bump_ball_mass_bounds χ (ν r)).2
  · intro z hz
    obtain ⟨s, hRs, hs⟩ := exists_between
      (((lt_div_iff₀ h2b).2 (by linarith only [hz])) : R < z / (2 * b))
    let χ : ContDiffBump (0 : Point) := ⟨R, s, hR, hRs⟩
    have hτ : (∫ y, χ y ∂τ) < z := by
      have hs' := (lt_div_iff₀ h2b).1 hs
      refine (bump_ball_mass_bounds χ τ).2.trans_lt ?_
      change (τ (closedBall 0 s)).toReal < z
      rw [hτmass s (hR.trans hRs).le]
      linarith only [hs']
    have hConv := hV (χ : Point → ℝ) (χ.contDiff (n := 0)).continuous χ.hasCompactSupport (subset_univ _)
    filter_upwards [hConv (Iio_mem_nhds hτ)] with r hr
    letI := SupportingAnalysis.blownUpMeasure_isFiniteMeasure (d := 1) x r μ
    exact (bump_ball_mass_bounds χ (ν r)).1.trans_lt hr

/-- The unweighted carrier density agrees with the positive coefficient of
its vague line tangent under the normalization by `2 * r`. -/
theorem tendsto_oneDensity_of_flatBlowup {μ : Measure Point} [IsFiniteMeasure μ]
    {x : Point} {L : Submodule ℝ Point} (hL : Module.finrank ℝ L = 1)
    {b : ℝ} (hb : 0 < b)
    (hV : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r μ)
      (ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point))) :
    Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 b) := by
  have hMass := (tendsto_flatBlowup_closedBall_mass hL hb hV zero_lt_one).div_const (2 : ℝ)
  rw [mul_one, mul_div_cancel_right₀ _ two_ne_zero] at hMass
  refine hMass.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : 0 < r := hr
  rw [oneDensity, SupportingAnalysis.blownUpMeasure_closedBall_zero x hr', one_mul, Nat.cast_one,
    zpow_neg, zpow_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hr'.le)]
  ring

private theorem measurableSet_cone_complement (Q : Point →ₗ[ℝ] Point) (δ : ℝ) :
    MeasurableSet {y | ¬ ‖Q y‖ ≤ δ * ‖y‖} :=
  (isClosed_le Q.toContinuousLinearMap.continuous.norm
    (continuous_const.mul continuous_norm)).measurableSet.compl

/-- If a linear map vanishes on the tangent line, the rescaled mass in
the unit ball on which the map exceeds a fixed cone aperture tends to zero. -/
theorem tendsto_flatBlowup_cone_complement {μ : Measure Point} [IsFiniteMeasure μ]
    {x : Point} {L : Submodule ℝ Point} (hL : Module.finrank ℝ L = 1)
    {b : ℝ} (hb : 0 < b)
    (hV : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r μ)
      (ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)))
    (Q : Point →ₗ[ℝ] Point) (hQ : ∀ y ∈ L, Q y = 0) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun r : ℝ => ((SupportingAnalysis.blownUpMeasure (d := 1) x r μ)
      (ball 0 1 \ {y | ‖Q y‖ ≤ δ * ‖y‖})).toReal) (𝓝[>] 0) (𝓝 0) := by
  let ν (r : ℝ) := SupportingAnalysis.blownUpMeasure (d := 1) x r μ
  let τ := ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)
  let A : Set Point := ball 0 1 \ {y | ‖Q y‖ ≤ δ * ‖y‖}
  have hA : MeasurableSet A := measurableSet_ball.inter (measurableSet_cone_complement Q δ)
  letI : IsFiniteMeasureOnCompacts τ := flat_line_finite_on_compacts L hL b
  apply tendsto_order.2
  constructor
  · intro z hz
    exact Eventually.of_forall fun _ => hz.trans_le ENNReal.toReal_nonneg
  intro ε hε
  let a := ε / (4 * b)
  have ha : 0 < a := div_pos hε (mul_pos (by norm_num) hb)
  let χ : ContDiffBump (0 : Point) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let φ (y : Point) := χ y * min 1 (‖Q y‖ / (δ * a))
  have hφ : Continuous φ := (χ.contDiff (n := 0)).continuous.mul
    (continuous_const.min (Q.toContinuousLinearMap.continuous.norm.div_const _))
  have hc : HasCompactSupport φ := χ.hasCompactSupport.mul_right
  have hφ0 (y : Point) : 0 ≤ φ y :=
    mul_nonneg χ.nonneg (le_min zero_le_one (div_nonneg (norm_nonneg _) (mul_nonneg hδ.le ha.le)))
  have hτ : ∫ y, φ y ∂τ = 0 := by
    have hMem : ∀ᵐ y ∂τ, y ∈ (L : Set Point) :=
      Measure.smul_absolutelyContinuous.ae_le
        (ae_restrict_mem L.closed_of_finiteDimensional.measurableSet)
    apply integral_eq_zero_of_ae
    filter_upwards [hMem] with y hy
    change φ y = 0
    simp only [φ, hQ y hy, norm_zero, zero_div, min_eq_right zero_le_one, mul_zero]
  have hTest := hV φ hφ hc (subset_univ _)
  rw [hτ] at hTest
  have hsum := (tendsto_flatBlowup_closedBall_mass hL hb hV ha).add hTest
  have hlim : b * (2 * a) + 0 < ε := by
    have heq : b * (2 * a) = ε / 2 := by
      dsimp only [a]
      field_simp
      ring
    rw [heq, add_zero]
    exact half_lt_self hε
  let K := closedBall (0 : Point) a
  have hφ1 (y : Point) (hy : y ∈ A \ K) : φ y = 1 := by
    have hχ1 : χ y = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hy.1.1)
    have hybig : a < ‖y‖ := by
      have h := hy.2
      change y ∉ closedBall (0 : Point) a at h
      rwa [mem_closedBall, dist_zero_right, not_le] at h
    have hle : δ * a ≤ ‖Q y‖ :=
      (mul_le_mul_of_nonneg_left hybig.le hδ.le).trans (lt_of_not_ge hy.1.2).le
    have hmin : 1 ≤ ‖Q y‖ / (δ * a) :=
      (le_div_iff₀ (mul_pos hδ ha)).2 (by simpa only [one_mul] using hle)
    change χ y * min 1 (‖Q y‖ / (δ * a)) = 1
    rw [hχ1, min_eq_left hmin, mul_one]
  filter_upwards [hsum (Iio_mem_nhds hlim)] with r hr
  letI := SupportingAnalysis.blownUpMeasure_isFiniteMeasure (d := 1) x r μ
  have hcover : A ⊆ K ∪ (A \ K) := by
    intro y hy
    by_cases hz : y ∈ K
    · exact Or.inl hz
    · exact Or.inr ⟨hy, hz⟩
  have hMeasures := (measure_mono (μ := ν r) hcover).trans (measure_union_le K (A \ K))
  have hKfin := measure_ne_top (ν r) K
  have hDiffFin := measure_ne_top (ν r) (A \ K)
  have hReal := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hKfin, hDiffFin⟩) hMeasures
  rw [ENNReal.toReal_add hKfin hDiffFin] at hReal
  have hSub := measure_toReal_le_integral_of_eq_one (hA.diff measurableSet_closedBall)
    (hφ.integrable_of_hasCompactSupport hc (μ := ν r)) hφ0 hφ1
  change ((ν r) K).toReal + (∫ y, φ y ∂ν r) < ε at hr
  exact (hReal.trans (add_le_add (le_refl _) hSub)).trans_lt hr

private theorem normalized_carrier_cone_zero {S : Set Point} (hfin : HausdorffOne S < ⊤)
    {x : Point} {L : Submodule ℝ Point} (hL : Module.finrank ℝ L = 1)
    {b : ℝ} (hb : 0 < b)
    (hV : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r (HausdorffOne.restrict S))
      (ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)))
    (Q : Point →ₗ[ℝ] Point) (hQ : ∀ y ∈ L, Q y = 0) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun r : ℝ => HausdorffOne ((S ∩ ball x r) \ {y | ‖Q (y - x)‖ ≤ δ * ‖y - x‖}) /
      ENNReal.ofReal (2 * r)) (𝓝[>] 0) (𝓝 0) := by
  let μ := HausdorffOne.restrict S
  letI : IsFiniteMeasure μ := by
    constructor
    simpa only [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using hfin
  let A : Set Point := ball 0 1 \ {y | ‖Q y‖ ≤ δ * ‖y‖}
  have hA : MeasurableSet A := measurableSet_ball.inter (measurableSet_cone_complement Q δ)
  let ν (r : ℝ) := SupportingAnalysis.blownUpMeasure (d := 1) x r μ
  have hReal := (tendsto_flatBlowup_cone_complement hL hb hV Q hQ hδ).div_const (2 : ℝ)
  have hMass : Tendsto (fun r => ENNReal.ofReal (((ν r) A).toReal / 2)) (𝓝[>] 0) (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto (0 / 2 : ℝ)).comp hReal
    rw [zero_div, ENNReal.ofReal_zero] at h
    exact h
  refine hMass.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : 0 < r := hr
  let P (y : Point) := r⁻¹ • (y - x)
  let B := ball x r \ {y | ‖Q (y - x)‖ ≤ δ * ‖y - x‖}
  have hP : Measurable P := by dsimp only [P]; fun_prop
  have hPre : P ⁻¹' A = B := by
    ext y
    change (r⁻¹ • (y - x) ∈ ball (0 : Point) 1 ∧
      ¬ ‖Q (r⁻¹ • (y - x))‖ ≤ δ * ‖r⁻¹ • (y - x)‖) ↔
      y ∈ ball x r ∧ ¬ ‖Q (y - x)‖ ≤ δ * ‖y - x‖
    simp only [mem_ball, dist_eq_norm, sub_zero, map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr']
    rw [inv_mul_lt_iff₀ hr', mul_one, mul_left_comm δ, mul_le_mul_iff_right₀ (inv_pos.2 hr')]
  have hB : MeasurableSet B := hPre ▸ hA.preimage hP
  have hBS : B ∩ S = (S ∩ ball x r) \ {y | ‖Q (y - x)‖ ≤ δ * ‖y - x‖} := by
    ext y
    simp only [B, mem_inter_iff, Set.mem_sdiff]
    tauto
  have hν : (ν r) A = ENNReal.ofReal (r⁻¹) * HausdorffOne (B ∩ S) := by
    change (ENNReal.ofReal (r ^ (-((1 : ℕ) : ℤ))) • Measure.map P μ) A = _
    rw [Measure.smul_apply, Measure.map_apply hP hA, hPre, Nat.cast_one, zpow_neg, zpow_one,
      smul_eq_mul, Measure.restrict_apply hB]
  have hFin : HausdorffOne (B ∩ S) ≠ ⊤ := ((measure_mono inter_subset_right).trans_lt hfin).ne
  change ENNReal.ofReal (((ν r) A).toReal / 2) =
    HausdorffOne ((S ∩ ball x r) \ {y | ‖Q (y - x)‖ ≤ δ * ‖y - x‖}) / ENNReal.ofReal (2 * r)
  rw [← hBS, hν, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hr'.le)]
  have heq : (r⁻¹ * (HausdorffOne (B ∩ S)).toReal) / 2 =
      (HausdorffOne (B ∩ S)).toReal / (2 * r) := by ring
  rw [heq, ENNReal.ofReal_div_of_pos (mul_pos zero_lt_two hr'), ENNReal.ofReal_toReal hFin]

/-- A flat carrier blow-up and its orthogonal projection satisfy the literal
density and cone clauses of `IsApproxTangentLine`. -/
theorem isApproxTangentLine_of_flatBlowup {S : Set Point} (hfin : HausdorffOne S < ⊤)
    {x : Point} {L : Submodule ℝ Point} (hL : Module.finrank ℝ L = 1)
    {b : ℝ} (hb : 0 < b)
    (hV : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r (HausdorffOne.restrict S))
      (ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)))
    (P : LineProjection) (hP : ∀ y : Point, matrixAction P.val y = L.starProjection y) :
    IsApproxTangentLine S x P := by
  let μ := HausdorffOne.restrict S
  letI : IsFiniteMeasure μ := by
    constructor
    simpa only [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using hfin
  refine ⟨⟨b, hb, tendsto_oneDensity_of_flatBlowup hL hb hV⟩, ?_⟩
  let Q : Point →ₗ[ℝ] Point := (1 - P.val).toEuclideanLin
  have hQ (y : Point) (hy : y ∈ L) : Q y = 0 := by
    change (1 - P.val).toEuclideanLin y = 0
    rw [map_sub, LinearMap.sub_apply]
    have h1 : (1 : Tensor).toEuclideanLin y = y := by
      change WithLp.toLp 2 ((1 : Tensor) *ᵥ y.ofLp) = y
      rw [Matrix.one_mulVec, WithLp.toLp_ofLp]
    change (1 : Tensor).toEuclideanLin y - matrixAction P.val y = 0
    rw [h1, hP, Submodule.starProjection_eq_self_iff.mpr hy, sub_self]
  intro δ hδ
  exact normalized_carrier_cone_zero hfin hL hb hV Q hQ hδ

noncomputable local instance approxTangentContinuousENorm : ContinuousENorm Tensor :=
  @SeminormedAddGroup.toContinuousENorm Tensor inferInstance

/-- The rank-one stress represents the approximate tangent of the same
Hausdorff carrier almost everywhere for the interior energy measure. -/
theorem ae_approxTangentLine_of_flatStress {Ω S : Set Point} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hRect : CountablyRectifiableOne S) (hfin : HausdorffOne S < ⊤)
    {μ : Measure Point} {F : Point → Tensor} (hF : Integrable F (μ.restrict Ω))
    (hDiv : External.RowDivergenceFree Ω μ F) {θ : Point → ℝ≥0∞}
    (hθ : Measurable θ) (hθfin : (∫⁻ y, θ y ∂HausdorffOne.restrict S) < ⊤)
    (hRep : μ.restrict Ω = (HausdorffOne.restrict S).withDensity θ)
    (hProj : ∀ᵐ x ∂μ.restrict Ω, (F x)ᵀ = F x ∧ F x * F x = F x ∧ (F x).rank = 1) :
    ∀ᵐ x ∂μ.restrict Ω, ∃ P : LineProjection, P.val = F x ∧ IsApproxTangentLine S x P := by
  filter_upwards [ae_flatStress_eq_starProjection hΩ hS hRect hfin hF hDiv hθ hθfin hRep hProj,
    hProj] with x hx hPx
  obtain ⟨L, b, hL, hb, hV, hProjection⟩ := hx
  exact ⟨⟨F x, hPx⟩, rfl, isApproxTangentLine_of_flatBlowup hfin hL hb hV _ hProjection⟩

private theorem lineProjection_nonempty : Nonempty LineProjection := by
  let d (i : Fin 3) : ℝ := if i = 0 then 1 else 0
  refine ⟨⟨Matrix.diagonal d, Matrix.diagonal_transpose d, ?_, ?_⟩⟩
  · rw [Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    by_cases hi : i = 0 <;> simp [d, hi]
  · rw [Matrix.rank_diagonal]
    have hcard := Fintype.card_of_subtype ({0} : Finset (Fin 3))
      (p := fun i => d i ≠ 0) (fun i => by by_cases hi : i = 0 <;> simp [d, hi])
    exact hcard.trans (Finset.card_singleton 0)

/-- An almost-everywhere rank-one projection field has a measurable
representative into the Borel space of line projections. -/
theorem exists_measurable_lineProjection_of_ae {μ : Measure Point} {F : Point → Tensor}
    (hF : AEStronglyMeasurable F μ)
    (hProj : ∀ᵐ x ∂μ, (F x)ᵀ = F x ∧ F x * F x = F x ∧ (F x).rank = 1) :
    ∃ P : Point → LineProjection, Measurable P ∧ (fun x => (P x).val) =ᵐ[μ] F := by
  classical
  borelize Tensor
  letI : TopologicalSpace.PseudoMetrizableSpace Tensor :=
    (inferInstance : TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))
  let G := hF.mk F
  have hG : Measurable G := hF.measurable_mk
  let E := {x | (G x)ᵀ = G x ∧ G x * G x = G x ∧ (G x).rank = 1}
  have hE : ∀ᵐ x ∂μ, x ∈ E := by
    filter_upwards [hF.ae_eq_mk, hProj] with x hx hPx
    change F x = G x at hx
    simpa only [E, ← hx, mem_setOf_eq] using hPx
  have hEnull : μ Eᶜ = 0 := ae_iff.1 hE
  have hEnm : NullMeasurableSet E μ := by
    simpa only [compl_compl] using (NullMeasurableSet.of_null hEnull).compl
  obtain ⟨T, hTE, hTm, hTEae⟩ := hEnm.exists_measurable_subset_ae_eq
  have hT : ∀ᵐ x ∂μ, x ∈ T := by
    filter_upwards [hTEae, hE] with x hTE' hE'
    change (x ∈ T) = (x ∈ E) at hTE'
    exact hTE'.mpr hE'
  obtain ⟨P₀⟩ := lineProjection_nonempty
  let P (x : Point) : LineProjection := if hx : x ∈ T then ⟨G x, hTE hx⟩ else P₀
  have hVal : Measurable (fun x => (P x).val) := by
    have heq : (fun x => (P x).val) = T.piecewise G (fun _ => P₀.val) := by
      funext x
      by_cases hx : x ∈ T <;> simp [P, hx]
    rw [heq]
    exact Measurable.piecewise hTm hG measurable_const
  refine ⟨P, ?_, ?_⟩
  · apply Measurable.of_comap_le
    change (borel LineProjection).comap P ≤ _
    rw [borel_comap (f := (Subtype.val : LineProjection → Tensor)), MeasurableSpace.comap_comp]
    exact measurable_iff_comap_le.1 hVal
  · filter_upwards [hT, hF.ae_eq_mk] with x hx hxG
    simp only [P, dif_pos hx]
    exact hxG.symm

/-- The measurable stress representative induces the associated varifold on
the same carrier with the original interior measure and scalar weight. -/
theorem exists_associatedVarifold_with_stress_projection {Ω S : Set Point} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hRect : CountablyRectifiableOne S) (hfin : HausdorffOne S < ⊤)
    {μ : Measure Point} {F : Point → Tensor} (hF : Integrable F (μ.restrict Ω))
    (hDiv : External.RowDivergenceFree Ω μ F) {θ : Point → ℝ≥0∞}
    (hθ : Measurable θ) (hθfin : (∫⁻ y, θ y ∂HausdorffOne.restrict S) < ⊤)
    (hRep : μ.restrict Ω = (HausdorffOne.restrict S).withDensity θ)
    (hProj : ∀ᵐ x ∂μ.restrict Ω, (F x)ᵀ = F x ∧ F x * F x = F x ∧ (F x).rank = 1) :
    ∃ P : Point → LineProjection, Measurable P ∧
      (fun x => (P x).val) =ᵐ[μ.restrict Ω] F ∧
      IsAssociatedVarifold Ω S μ (Measure.map (fun x => (x, P x)) (μ.restrict Ω)) := by
  obtain ⟨P, hP, hEq⟩ := exists_measurable_lineProjection_of_ae hF.aestronglyMeasurable hProj
  refine ⟨P, hP, hEq, θ, P, hθ, hθfin, hRep, hP.aemeasurable, ?_, rfl⟩
  filter_upwards [hEq, ae_approxTangentLine_of_flatStress hΩ hS hRect hfin hF hDiv hθ hθfin hRep
    hProj] with x hEqx hx
  obtain ⟨Q, hQ, hT⟩ := hx
  exact (Subtype.ext (hQ.trans hEqx.symm) : Q = P x) ▸ hT

end Thesis.MeasureGeometry

end
