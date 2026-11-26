module

public import Thesis.MeasureGeometry.LineTangents
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Orthogonal projection and the divergence law for the one-dimensional stress tangent. -/

public section

open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Frobenius
  Topology

namespace Thesis.MeasureGeometry

noncomputable local instance flatStressContinuousENorm : ContinuousENorm Tensor :=
  @SeminormedAddGroup.toContinuousENorm Tensor inferInstance

/-- A symmetric rank-one projection that annihilates the orthogonal
complement of a line is the orthogonal projection onto that line. -/
theorem matrixAction_eq_starProjection_of_annihilates_orthogonal (F : LineProjection)
    (L : Submodule ℝ Point) (hL : Module.finrank ℝ L = 1)
    (hOrth : ∀ u ∈ Lᗮ, matrixAction F.val u = 0) (v : Point) :
    matrixAction F.val v = L.starProjection v := by
  let T : Point →ₗ[ℝ] Point := F.val.toEuclideanLin
  have hT (u : Point) : T u = matrixAction F.val u := rfl
  have hHermitian : F.val.IsHermitian :=
    (Matrix.conjTranspose_eq_transpose_of_trivial F.val).trans F.property.1
  have hSymm : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hHermitian
  have hIdem (u : Point) : T (T u) = T u := by
    change F.val.toEuclideanLin (F.val.toEuclideanLin u) = F.val.toEuclideanLin u
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.toLin_mul_apply, F.property.2.1]
  have hRange : LinearMap.range T ≤ L := by
    rw [← Submodule.orthogonal_orthogonal L]
    rintro _ ⟨u, rfl⟩
    rw [Submodule.mem_orthogonal']
    intro w hw
    rw [hSymm u w, hT w, hOrth w hw, inner_zero_right]
  have hRank : Module.finrank ℝ (LinearMap.range T) = 1 := by
    change Module.finrank ℝ (LinearMap.range F.val.toEuclideanLin) = 1
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.rank_eq_finrank_range_toLin]
    exact F.property.2.2
  have hRangeEq := Submodule.eq_of_le_of_finrank_le hRange (by rw [hRank, hL])
  rw [← hT v]
  apply (L.eq_starProjection_of_mem_of_inner_eq_zero (hRange ⟨v, rfl⟩) ?_).symm
  intro w hw
  rw [← hRangeEq] at hw
  obtain ⟨u, rfl⟩ := hw
  rw [inner_sub_left, ← hSymm (T v) u, hIdem v, hSymm v u, sub_self]

private theorem coordDeriv_rescaled_test {X : Point → Point} (hX : ContDiff ℝ ∞ X)
    {r : ℝ} (hr : r ≠ 0) (x y : Point) (j : Fin 3) :
    coordDeriv j (fun z : Point => r • X (r⁻¹ • (z - x))) y =
      coordDeriv j X (r⁻¹ • (y - x)) := by
  let P (z : Point) := r⁻¹ • (z - x)
  have hP : HasFDerivAt P (r⁻¹ • ContinuousLinearMap.id ℝ Point) y :=
    ((hasFDerivAt_id y).sub_const x).const_smul r⁻¹
  have hXderiv := (hX.differentiable (by simp) (P y)).hasFDerivAt
  change fderiv ℝ (r • (X ∘ P)) y (axis j) = fderiv ℝ X (P y) (axis j)
  rw [((hXderiv.comp y hP).const_smul r).fderiv]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_smul, mul_inv_cancel₀ hr, one_smul]

private theorem eventually_rescaled_test_support {Ω : Set Point} (hΩ : IsOpen Ω)
    {x : Point} (hx : x ∈ Ω) {X : Point → Point} (hXc : HasCompactSupport X) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      HasCompactSupport (fun y : Point => r • X (r⁻¹ • (y - x))) ∧
        tsupport (fun y : Point => r • X (r⁻¹ • (y - x))) ⊆ Ω := by
  obtain ⟨R, hR, hRB⟩ := hXc.isBounded.subset_closedBall_lt 0 (0 : Point)
  obtain ⟨δ, hδ, hδB⟩ := Metric.isOpen_iff.1 hΩ x hx
  filter_upwards [eventually_mem_positive_interval (div_pos hδ hR)] with r hr
  let P (y : Point) := r⁻¹ • (y - x)
  have hP : Continuous P := by dsimp only [P]; fun_prop
  have hTs : tsupport (fun y : Point => r • X (P y)) ⊆ closedBall x (R * r) := by
    have hsub := (tsupport_comp_subset (g := fun v : Point => r • v)
      (smul_zero _ : r • (0 : Point) = 0) (X ∘ P)).trans (tsupport_comp_subset_preimage X hP)
    intro y hy
    have hb := hRB (hsub hy)
    change P y ∈ closedBall (0 : Point) R at hb
    rw [mem_closedBall, dist_zero_right] at hb
    simp only [P, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr.1] at hb
    rw [mem_closedBall, dist_eq_norm]
    simpa only [mul_comm r R] using (inv_mul_le_iff₀ hr.1).mp hb
  have hsmall : R * r < δ := by
    simpa only [mul_comm r R] using (lt_div_iff₀ hR).mp hr.2
  exact ⟨(isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hTs,
    hTs.trans ((closedBall_subset_ball hsmall).trans hδB)⟩

/-- A closed ball centered at the origin cuts a line through the origin in
a segment of length `2 * R`. -/
theorem hausdorffOne_restrict_line_closedBall (L : Submodule ℝ Point)
    (hL : Module.finrank ℝ L = 1) (R : ℝ) :
    (HausdorffOne.restrict (L : Set Point)) (closedBall 0 R) = ENNReal.ofReal (2 * R) := by
  haveI : Nontrivial L := Module.finrank_pos_iff.1 (hL ▸ Nat.zero_lt_one)
  obtain ⟨u, hu⟩ := exists_ne (0 : L)
  have hu' : (u : Point) ≠ 0 := fun h => hu (Subtype.ext h)
  let e : Point := ‖(u : Point)‖⁻¹ • (u : Point)
  have he_mem : e ∈ L := L.smul_mem _ u.property
  have he_norm : ‖e‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.2 hu')]
  have he_ne : e ≠ 0 := norm_ne_zero_iff.1 (he_norm ▸ one_ne_zero)
  have hspan : Submodule.span ℝ {e} = L :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem e L).2 he_mem)
      (by rw [finrank_span_singleton he_ne, hL])
  have hImage : closedBall (0 : Point) R ∩ (L : Set Point) =
      (fun t : ℝ => t • e) '' Icc (-R) R := by
    ext v
    constructor
    · rintro ⟨hvR, hvL⟩
      change v ∈ L at hvL
      rw [← hspan, Submodule.mem_span_singleton] at hvL
      obtain ⟨t, rfl⟩ := hvL
      refine ⟨t, ?_, rfl⟩
      rw [mem_closedBall, dist_zero_right, norm_smul, he_norm, mul_one, Real.norm_eq_abs] at hvR
      exact abs_le.1 hvR
    · rintro ⟨t, ht, rfl⟩
      refine ⟨?_, L.smul_mem _ he_mem⟩
      rw [mem_closedBall, dist_zero_right, norm_smul, he_norm, mul_one, Real.norm_eq_abs]
      exact abs_le.2 ht
  rw [Measure.restrict_apply measurableSet_closedBall, hImage, hausdorffMeasure_smul_right_image,
    hausdorffMeasure_real, Real.volume_Icc]
  have he_nnnorm : ‖e‖₊ = 1 := NNReal.eq he_norm
  rw [he_nnnorm, one_smul]
  congr 1
  ring

private theorem hausdorffOne_restrict_line_finite_on_compacts (L : Submodule ℝ Point)
    (hL : Module.finrank ℝ L = 1) :
    IsFiniteMeasureOnCompacts (HausdorffOne.restrict (L : Set Point)) := by
  constructor
  intro K hK
  obtain ⟨R, _, hR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : Point)
  exact (measure_mono hR).trans_lt
    ((hausdorffOne_restrict_line_closedBall L hL R).symm ▸ ENNReal.ofReal_lt_top)

private theorem continuous_coordDeriv_entry {X : Point → Point}
    (hX : ContDiff ℝ ∞ X) (i j : Fin 3) :
    Continuous (fun y => coordDeriv j X y i) := by
  let ev : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
  change Continuous (ev ∘ fun y => fderiv ℝ X y (axis j))
  exact ev.continuous.comp ((ContinuousLinearMap.apply ℝ Point (axis j)).continuous.comp
    (hX.continuous_fderiv (by simp)))

private theorem compactSupport_coordDeriv_entry {X : Point → Point}
    (hXc : HasCompactSupport X) (i j : Fin 3) :
    HasCompactSupport (fun y => coordDeriv j X y i) := by
  let ev : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i
  change HasCompactSupport (ev ∘ fun y => fderiv ℝ X y (axis j))
  exact (hXc.fderiv_apply ℝ (axis j)).comp_left (map_zero ev)

private theorem exists_bound_of_continuous_compactSupport {φ : Point → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) : ∃ M : ℝ, ∀ y, ‖φ y‖ ≤ M := by
  obtain ⟨M, hM, hSubset⟩ :=
    (hc.image hφ.norm).isBounded.subset_closedBall_lt 0 (0 : ℝ)
  refine ⟨M, fun y => ?_⟩
  by_cases hy : y ∈ tsupport φ
  · have hb := hSubset (mem_image_of_mem _ hy)
    simpa only [mem_closedBall, Real.dist_eq, sub_zero, abs_norm] using hb
  · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
    exact hM.le

private theorem integral_matrix_contract {ζ : Measure Point}
    (A : Point → Tensor) (φ : Fin 3 → Fin 3 → Point → ℝ)
    (h : ∀ i j, Integrable (fun y => A y i j * φ i j y) ζ) :
    (∫ y, ∑ i : Fin 3, ∑ j : Fin 3, A y i j * φ i j y ∂ζ) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ y, A y i j * φ i j y ∂ζ := by
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => h i j))]
  exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => h i j

private theorem rowDivergenceFree_of_rescaled_pairings {Ω : Set Point} (hΩ : IsOpen Ω)
    {μ ζ τ : Measure Point} [IsFiniteMeasureOnCompacts τ] {F : Point → Tensor}
    (hDiv : External.RowDivergenceFree Ω μ F) {θ : Point → ℝ≥0∞}
    (hθ : Measurable θ) (hθfin : ∀ᵐ y ∂ζ, θ y < ⊤) (hRep : μ.restrict Ω = ζ.withDensity θ)
    (hW : ∀ i j, Integrable (fun y => (θ y).toReal * F y i j) ζ)
    {x : Point} (hx : x ∈ Ω) (hθx : (θ x).toReal ≠ 0)
    (hPair : ∀ (i j : Fin 3) (φ : Point → ℝ), Continuous φ → HasCompactSupport φ →
      Tendsto (fun r : ℝ => r⁻¹ * ∫ y, ((θ y).toReal * F y i j) * φ (r⁻¹ • (y - x)) ∂ζ)
        (𝓝[>] 0) (𝓝 (((θ x).toReal * F x i j) * ∫ z, φ z ∂τ))) :
    External.RowDivergenceFree univ τ (fun _ => F x) := by
  intro X hX hXc _
  let φ (i j : Fin 3) (z : Point) := coordDeriv j X z i
  have hφ (i j : Fin 3) : Continuous (φ i j) := continuous_coordDeriv_entry hX i j
  have hφc (i j : Fin 3) : HasCompactSupport (φ i j) := compactSupport_coordDeriv_entry hXc i j
  let A (y : Point) := (θ y).toReal • F y
  let ψ (r : ℝ) (i j : Fin 3) (y : Point) := φ i j (r⁻¹ • (y - x))
  have hψ (r : ℝ) (i j : Fin 3) : Continuous (ψ r i j) := by
    have := hφ i j
    dsimp only [ψ]
    fun_prop
  have hEntry (r : ℝ) (i j : Fin 3) : Integrable (fun y => A y i j * ψ r i j y) ζ := by
    obtain ⟨M, hM⟩ := exists_bound_of_continuous_compactSupport (hφ i j) (hφc i j)
    exact (hW i j).mul_bdd (hψ r i j).aestronglyMeasurable (Eventually.of_forall fun _ => hM _)
  have hSum (r : ℝ) : (∑ i : Fin 3, ∑ j : Fin 3, ∫ y, A y i j * ψ r i j y ∂ζ) =
      ∫ y in Ω, ∑ i : Fin 3, ∑ j : Fin 3, F y i j * ψ r i j y ∂μ := by
    rw [← integral_matrix_contract A (ψ r) (hEntry r), hRep,
      integral_withDensity_eq_integral_toReal_smul hθ hθfin]
    apply integral_congr_ae
    filter_upwards with y
    simp only [A, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hTend := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hPair i j (φ i j) (hφ i j) (hφc i j)))
  have hZero : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (∑ i : Fin 3, ∑ j : Fin 3, r⁻¹ * ∫ y, A y i j * ψ r i j y ∂ζ) = 0 := by
    filter_upwards [self_mem_nhdsWithin, eventually_rescaled_test_support hΩ hx hXc] with r hr hSupp
    have hr' : 0 < r := hr
    have hTest : ContDiff ℝ ∞ (fun y : Point => r • X (r⁻¹ • (y - x))) := by fun_prop
    have hD := hDiv _ hTest hSupp.1 hSupp.2
    simp_rw [coordDeriv_rescaled_test hX hr'.ne' x] at hD
    simp_rw [← Finset.mul_sum]
    rw [hSum r]
    exact mul_eq_zero_of_right _ hD
  have hTend0 : Tendsto (fun r : ℝ => ∑ i : Fin 3, ∑ j : Fin 3,
      r⁻¹ * ∫ y, A y i j * ψ r i j y ∂ζ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (hZero.mono fun _ h => h.symm)
  have hLim := tendsto_nhds_unique hTend hTend0
  change (∑ i : Fin 3, ∑ j : Fin 3, ((θ x).toReal * F x i j) * ∫ z, φ i j z ∂τ) = 0 at hLim
  simp only [mul_assoc, ← Finset.mul_sum] at hLim
  have hEntries (i j : Fin 3) : Integrable (fun z => F x i j * φ i j z) τ :=
    ((hφ i j).integrable_of_hasCompactSupport (hφc i j)).const_mul _
  rw [Measure.restrict_univ, integral_matrix_contract _ φ hEntries]
  simp only [integral_const_mul]
  exact (mul_eq_zero.1 hLim).resolve_left hθx

/-- Every compact set has finite measure for a line with a finite constant weight. -/
theorem flat_line_finite_on_compacts (L : Submodule ℝ Point)
    (hL : Module.finrank ℝ L = 1) (b : ℝ) :
    IsFiniteMeasureOnCompacts (ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)) := by
  letI := hausdorffOne_restrict_line_finite_on_compacts L hL
  constructor
  intro K hK
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-- The same line and positive coefficient as the unweighted Hausdorff
carrier tangent support the constant stress density, with zero row divergence. -/
theorem ae_flatStress_divergenceFree {Ω S : Set Point} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hRect : CountablyRectifiableOne S) (hfin : HausdorffOne S < ⊤)
    {μ : Measure Point} {F : Point → Tensor} (hF : Integrable F (μ.restrict Ω))
    (hDiv : External.RowDivergenceFree Ω μ F) {θ : Point → ℝ≥0∞}
    (hθ : Measurable θ) (hθfin : (∫⁻ y, θ y ∂HausdorffOne.restrict S) < ⊤)
    (hRep : μ.restrict Ω = (HausdorffOne.restrict S).withDensity θ) :
    let ζ := HausdorffOne.restrict S
    ∀ᵐ x ∂μ.restrict Ω, ∃ (L : Submodule ℝ Point) (b : ℝ), Module.finrank ℝ L = 1 ∧ 0 < b ∧
      let τ := ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)
      SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
        (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r ζ) τ ∧
      External.RowDivergenceFree univ τ (fun _ => F x) := by
  let ζ := HausdorffOne.restrict S
  have hθae : ∀ᵐ y ∂ζ, θ y < ⊤ := ae_lt_top hθ hθfin.ne
  have hF' : Integrable F (ζ.withDensity θ) := hRep ▸ hF
  have hA : Integrable (fun y => (θ y).toReal • F y) ζ :=
    (integrable_withDensity_iff_integrable_smul' hθ hθae).1 hF'
  let w (p : Fin 3 × Fin 3) (y : Point) := (θ y).toReal * F y p.1 p.2
  have hw (p : Fin 3 × Fin 3) : Integrable (w p) ζ :=
    (Matrix.entryLinearMap ℝ ℝ p.1 p.2).toContinuousLinearMap.integrable_comp hA
  have hAc : μ.restrict Ω ≪ ζ := hRep ▸ withDensity_absolutelyContinuous ζ θ
  have hθpos : ∀ᵐ y ∂μ.restrict Ω, θ y ≠ 0 := by
    rw [hRep]
    exact (ae_withDensity_iff hθ).2 (Eventually.of_forall fun _ h => h)
  filter_upwards [hAc.ae_le (ae_flat_tangent_with_scalar_pairings hS hRect hfin hw),
    hAc.ae_le hθae, hθpos, ae_restrict_mem hΩ.measurableSet] with x hTan hθx hθne hx
  obtain ⟨L, b, hL, hb, hVague, hPair⟩ := hTan
  refine ⟨L, b, hL, hb, hVague, ?_⟩
  letI := flat_line_finite_on_compacts L hL b
  exact rowDivergenceFree_of_rescaled_pairings hΩ hDiv hθ hθae hRep (fun i j => hw (i, j))
    hx (ENNReal.toReal_pos hθne hθx.ne).ne' (fun i j => hPair (i, j))

/-- A constant tensor on a flat line with positive weight and zero row
divergence annihilates every normal vector. The test is a smooth scalar cutoff
times the normal linear function and the image of the normal vector. -/
theorem matrixAction_zero_of_flatStress_divergenceFree (L : Submodule ℝ Point)
    (hL : Module.finrank ℝ L = 1) {b : ℝ} (hb : 0 < b) (F : Tensor)
    (hDiv : External.RowDivergenceFree univ (ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point))
      (fun _ => F)) (u : Point) (hu : u ∈ Lᗮ) : matrixAction F u = 0 := by
  let τ := ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)
  letI : IsFiniteMeasureOnCompacts τ := flat_line_finite_on_compacts L hL b
  let χ : ContDiffBump (0 : Point) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let q := matrixAction F u
  let l : Point →L[ℝ] ℝ := innerSL ℝ u
  let X (y : Point) := (χ y * l y) • q
  have hχ : ContDiff ℝ ∞ (χ : Point → ℝ) := χ.contDiff
  have hX : ContDiff ℝ ∞ X := (hχ.mul l.contDiff).smul contDiff_const
  have hXc : HasCompactSupport X := (χ.hasCompactSupport.mul_right (f' := (l : Point → ℝ))).smul_right
  have hτ : ∀ᵐ y ∂τ, y ∈ (L : Set Point) :=
    Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem L.closed_of_finiteDimensional.measurableSet)
  have hDX (y : Point) (hy : y ∈ L) (j : Fin 3) :
      coordDeriv j X y = (χ y * u.ofLp j) • q := by
    have hl : l y = 0 := (Submodule.mem_orthogonal' L u).1 hu y hy
    have hDeriv := (((hχ.differentiable (by simp) y).hasFDerivAt).mul
      (l.hasFDerivAt (x := y))).smul_const q
    change HasFDerivAt X _ y at hDeriv
    rw [coordDeriv, hDeriv.fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, _root_.smul_apply, hl, zero_smul, add_zero,
      smul_eq_mul, l, innerSL_apply_apply, axis, EuclideanSpace.inner_single_right,
      RCLike.conj_to_real, one_mul]
  have hContr : (fun y => ∑ i : Fin 3, ∑ j : Fin 3, F i j * coordDeriv j X y i) =ᵐ[τ]
      fun y => χ y * ‖q‖ ^ 2 := by
    filter_upwards [hτ] with y hy
    change (∑ i : Fin 3, ∑ j : Fin 3, F i j * coordDeriv j X y i) = χ y * ‖q‖ ^ 2
    simp only [hDX y hy, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.real_norm_sq_eq]
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3, χ y * (q.ofLp i * (F i j * u.ofLp j)) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = χ y * ∑ i : Fin 3, q.ofLp i * q.ofLp i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        calc
          _ = χ y * (q.ofLp i * ∑ j : Fin 3, F i j * u.ofLp j) := by simp only [Finset.mul_sum]
          _ = _ := rfl
      _ = _ := by simp only [pow_two]
  have hZero := hDiv X hX hXc (subset_univ _)
  rw [Measure.restrict_univ, integral_congr_ae hContr, integral_mul_const] at hZero
  have hχpos : 0 < ∫ y, χ y ∂τ := by
    apply (integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall χ.nonneg')
      (hχ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport)).2
    have hSub : closedBall (0 : Point) 1 ⊆ Function.support χ := by
      intro y hy
      exact Function.mem_support.2 ((χ.one_of_mem_closedBall hy).trans_ne one_ne_zero)
    refine lt_of_lt_of_le ?_ (measure_mono hSub)
    change 0 < (ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)) (closedBall 0 1)
    rw [Measure.smul_apply, smul_eq_mul, hausdorffOne_restrict_line_closedBall L hL]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hb).ne' (ENNReal.ofReal_pos.2 (by norm_num)).ne'
  have hq : ‖q‖ ^ 2 = 0 := (mul_eq_zero.1 hZero).resolve_left hχpos.ne'
  exact norm_eq_zero.1 (by nlinarith only [hq, norm_nonneg q])

/-- The constant density on the flat stress tangent is the orthogonal
projection onto the very line supplied by the carrier tangent. -/
theorem matrixAction_eq_starProjection_of_flatStress_divergenceFree (L : Submodule ℝ Point)
    (hL : Module.finrank ℝ L = 1) {b : ℝ} (hb : 0 < b) (F : LineProjection)
    (hDiv : External.RowDivergenceFree univ (ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point))
      (fun _ => F.val)) (v : Point) : matrixAction F.val v = L.starProjection v :=
  matrixAction_eq_starProjection_of_annihilates_orthogonal F L hL
    (matrixAction_zero_of_flatStress_divergenceFree L hL hb F.val hDiv) v

/-- At almost every point of the interior energy measure, its symmetric
rank-one stress is the orthogonal projection onto the carrier tangent. -/
theorem ae_flatStress_eq_starProjection {Ω S : Set Point} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hRect : CountablyRectifiableOne S) (hfin : HausdorffOne S < ⊤)
    {μ : Measure Point} {F : Point → Tensor} (hF : Integrable F (μ.restrict Ω))
    (hDiv : External.RowDivergenceFree Ω μ F) {θ : Point → ℝ≥0∞}
    (hθ : Measurable θ) (hθfin : (∫⁻ y, θ y ∂HausdorffOne.restrict S) < ⊤)
    (hRep : μ.restrict Ω = (HausdorffOne.restrict S).withDensity θ)
    (hProj : ∀ᵐ x ∂μ.restrict Ω, (F x)ᵀ = F x ∧ F x * F x = F x ∧ (F x).rank = 1) :
    let ζ := HausdorffOne.restrict S
    ∀ᵐ x ∂μ.restrict Ω, ∃ (L : Submodule ℝ Point) (b : ℝ), Module.finrank ℝ L = 1 ∧ 0 < b ∧
      SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
        (fun r => SupportingAnalysis.blownUpMeasure (d := 1) x r ζ)
        (ENNReal.ofReal b • HausdorffOne.restrict (L : Set Point)) ∧
      ∀ v : Point, matrixAction (F x) v = L.starProjection v := by
  filter_upwards [ae_flatStress_divergenceFree hΩ hS hRect hfin hF hDiv hθ hθfin hRep,
    hProj] with x hT hP
  obtain ⟨L, b, hL, hb, hV, hFlatDiv⟩ := hT
  exact ⟨L, b, hL, hb, hV,
    matrixAction_eq_starProjection_of_flatStress_divergenceFree L hL hb ⟨F x, hP⟩ hFlatDiv⟩

end Thesis.MeasureGeometry

end
