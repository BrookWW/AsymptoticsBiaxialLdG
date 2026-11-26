module

public import Thesis.MeasureGeometry.StressAlgebra
public import Thesis.MeasureGeometry.LineDensity
public import Thesis.External.GeometricMeasureTheory
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! Application of the independent A-free rectifiability input to the
limiting stress measure. -/

public section

open Filter Matrix MeasureTheory Metric Set
open scoped BigOperators ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

noncomputable local instance rectifiableStressContinuousENorm : ContinuousENorm Tensor :=
  @SeminormedAddGroup.toContinuousENorm Tensor inferInstance

/-- The total variation of the stress and the interior energy measure are
comparable with the source constants. -/
theorem matrixVariation_comparable {Ω : Set Point} (μ : Measure Point) (F : Point → Tensor)
    (hF : ∀ᵐ x ∂μ.restrict Ω, 1 ≤ (F x).trace ∧ ‖F x‖ ≤ 2) :
    ENNReal.ofReal (Real.sqrt 3)⁻¹ • μ.restrict Ω ≤ External.matrixVariation Ω μ F ∧
      External.matrixVariation Ω μ F ≤ (2 : ℝ≥0∞) • μ.restrict Ω := by
  have hroot : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  unfold External.matrixVariation
  constructor
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hF] with x hx
    apply ENNReal.ofReal_mono
    rw [← one_div, div_le_iff₀ hroot, mul_comm]
    exact hx.1.trans (trace_le_sqrt_three_mul_norm (F x))
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hF] with x hx
    exact_mod_cast ENNReal.ofReal_mono hx.2

private theorem one_le_rank_of_symmetric_trace_pos {T : Tensor}
    (hs : Tᵀ = T) (ht : 0 < T.trace) : 1 ≤ T.rank := by
  classical
  have hT : T.IsHermitian := (Matrix.conjTranspose_eq_transpose_of_trivial T).trans hs
  have hn : ∃ i, hT.eigenvalues i ≠ 0 := by
    by_contra! he
    rw [hT.trace_eq_sum_eigenvalues] at ht
    simp [he] at ht
  obtain ⟨i, hi⟩ := hn
  rw [hT.rank_eq_card_non_zero_eigs]
  exact Fintype.card_pos_iff.2 ⟨⟨i, hi⟩⟩

private theorem upperOneDensity_pos_of_lower_measure {Ω : Set Point} (hΩ : IsOpen Ω)
    {μ ν : Measure Point} [IsFiniteMeasure μ] {c : ℝ} (hc : 0 < c)
    (hν : ENNReal.ofReal c • μ.restrict Ω ≤ ν) {x : Point} (hx : x ∈ Ω) {θ : ℝ}
    (hθ : 0 < θ) (hD : Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ)) :
    0 < External.upperOneDensity ν x := by
  obtain ⟨δ, hδ, hs⟩ := Metric.isOpen_iff.1 hΩ x hx
  have hlow : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (c * (θ / 2)) ≤ ν (closedBall x r) / ENNReal.ofReal (2 * r) := by
    filter_upwards [eventually_mem_positive_interval hδ,
      hD (Ioi_mem_nhds (half_lt_self hθ))] with r hr hden
    have hr' : 0 < 2 * r := mul_pos (by norm_num) hr.1
    have hB : closedBall x r ⊆ Ω := (closedBall_subset_ball hr.2).trans hs
    have hcomp := hν (closedBall x r)
    rw [Measure.smul_apply, Measure.restrict_apply isClosed_closedBall.measurableSet,
      inter_eq_left.mpr hB, smul_eq_mul] at hcomp
    change θ / 2 < (μ (closedBall x r)).toReal / (2 * r) at hden
    calc
      _ ≤ ENNReal.ofReal (c * ((μ (closedBall x r)).toReal / (2 * r))) :=
        ENNReal.ofReal_mono (mul_le_mul_of_nonneg_left hden.le hc.le)
      _ = (ENNReal.ofReal c * μ (closedBall x r)) / ENNReal.ofReal (2 * r) := by
        rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_div_of_pos hr',
          ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.div_eq_inv_mul,
          ENNReal.div_eq_inv_mul]
        ac_rfl
      _ ≤ _ := ENNReal.div_le_div_right hcomp _
  exact (ENNReal.ofReal_pos.2 (mul_pos hc (half_pos hθ))).trans_le
    (le_limsup_of_frequently_le' hlow.frequently)

private theorem upperOneDensity_eq_zero_of_notMem_support {Ω : Set Point}
    {μ ν : Measure Point} (hν : ν ≤ (2 : ℝ≥0∞) • μ.restrict Ω) {x : Point} (hx : x ∉ μ.support) :
    External.upperOneDensity ν x = 0 := by
  obtain ⟨δ, hδ, hB⟩ := nhds_basis_ball.notMem_measureSupport.mp hx
  have hzero : (fun r : ℝ => ν (closedBall x r) / ENNReal.ofReal (2 * r)) =ᶠ[𝓝[>] 0]
      (fun _ => 0) := by
    filter_upwards [eventually_mem_positive_interval hδ] with r hr
    have hZ : ν (closedBall x r) = 0 := by
      have hR : μ.restrict Ω (closedBall x r) = 0 := by
        apply nonpos_iff_eq_zero.mp
        calc
          _ ≤ μ (closedBall x r) := Measure.restrict_le_self _
          _ ≤ μ (ball x δ) := measure_mono (closedBall_subset_ball hr.2)
          _ = 0 := hB
      have hw := hν (closedBall x r)
      rw [Measure.smul_apply, smul_eq_mul, hR, mul_zero] at hw
      exact nonpos_iff_eq_zero.mp hw
    simp [hZ]
  exact (limsup_congr hzero).trans (limsup_const 0)

/-- A positive density on the support provides all the hypotheses needed
to apply the literal A19 specialization. The representation uses the same
interior energy and stress measures. -/
theorem rectifiable_stressCarrier_of_A19 (hA19 : External.A19Prop31)
    {Ω : Set Point} (hΩ : IsOpen Ω) (μ : FiniteMeasure Point) (F : Point → Tensor)
    (hF : Integrable F ((μ : Measure Point).restrict Ω)) (hDiv : External.RowDivergenceFree Ω μ F)
    (hB : ∀ᵐ x ∂((μ : Measure Point).restrict Ω), (F x)ᵀ = F x ∧ 1 ≤ (F x).trace ∧ ‖F x‖ ≤ 2)
    {η : ℝ} (hη : 0 < η)
    (hD : ∀ x ∈ Ω ∩ (μ : Measure Point).support,
      ∃ θ ≥ η / 2, Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ)) :
    let ν := External.matrixVariation Ω μ F
    ν ≪ HausdorffOne ∧
      ∃ (S : Set Point) (A : Point → Tensor),
        MeasurableSet S ∧ S ⊆ Ω ∩ (μ : Measure Point).support ∧
        CountablyRectifiableOne S ∧ HausdorffOne S < ⊤ ∧
        Integrable A (HausdorffOne.restrict S) ∧
        (∀ᵐ x ∂HausdorffOne.restrict S, (A x).rank = 1) ∧
        ∀ B : Set Point, MeasurableSet B →
          (∫ x in B ∩ Ω, F x ∂(μ : Measure Point)) = ∫ x in B ∩ S, A x ∂HausdorffOne := by
  let ν := External.matrixVariation Ω μ F
  obtain ⟨hlo, hhi⟩ := matrixVariation_comparable (μ : Measure Point) F (hB.mono fun _ h => h.2)
  have hac : ν ≪ (μ : Measure Point).restrict Ω := withDensity_absolutelyContinuous _ _
  have hRank : ∀ᵐ x ∂ν, 1 ≤ (F x).rank := hac.ae_le
    (hB.mono fun _ h => one_le_rank_of_symmetric_trace_pos h.1 (zero_lt_one.trans_le h.2.1))
  let E := {x ∈ Ω | 0 < External.upperOneDensity ν x}
  have hE : E = Ω ∩ (μ : Measure Point).support := by
    ext x
    constructor
    · rintro ⟨hxΩ, hx⟩
      refine ⟨hxΩ, ?_⟩
      by_contra hxs
      rw [upperOneDensity_eq_zero_of_notMem_support hhi hxs] at hx
      exact (lt_irrefl 0 hx)
    · intro hx
      obtain ⟨θ, hθ, hlim⟩ := hD x hx
      exact ⟨hx.1, upperOneDensity_pos_of_lower_measure hΩ
        (inv_pos.2 (Real.sqrt_pos.2 (by norm_num))) hlo hx.1 ((half_pos hη).trans_le hθ) hlim⟩
  obtain ⟨hν, S, A, hSm, hS, hRect, hAInt, hA, heq⟩ := hA19 Ω hΩ μ F hF hDiv hRank
  have hS' : S ⊆ Ω ∩ (μ : Measure Point).support := hE ▸ hS
  have hlen : HausdorffOne S < ⊤ :=
    (hausdorffOne_le_of_positive_oneDensity (μ : Measure Point) hS' hη hD).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
  refine ⟨hν, S, A, hSm, hS', hRect, hlen, hAInt, hA, ?_⟩
  intro B hBm
  have heq' := heq B hBm
  change (∫ x in B ∩ E, F x ∂(μ : Measure Point)) = _ at heq'
  have hrestriction : ((μ : Measure Point).restrict (B ∩ E)) = (μ : Measure Point).restrict (B ∩ Ω) := by
    apply Measure.restrict_congr_set
    filter_upwards [(μ : Measure Point).support_mem_ae] with x hx
    apply propext
    change x ∈ B ∩ E ↔ x ∈ B ∩ Ω
    simp [hE, hx]
  rw [hrestriction] at heq'
  exact heq'

private theorem rank_smul_le (c : ℝ) (T : Tensor) : (c • T).rank ≤ T.rank := by
  calc
    _ = (T * (c • (1 : Tensor))).rank := by rw [Matrix.mul_smul, mul_one]
    _ ≤ _ := Matrix.rank_mul_le_left _ _

private theorem rank_smul_of_ne_zero {c : ℝ} (hc : c ≠ 0) (T : Tensor) :
    (c • T).rank = T.rank := by
  refine le_antisymm (rank_smul_le c T) ?_
  have h := rank_smul_le c⁻¹ (c • T)
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

/-- The two representations of the stress transfer its rank-one density
to the interior energy measure. The rectifiable carrier carries all that
interior mass. -/
theorem rank_one_of_stressCarrier {Ω S : Set Point} (μ : FiniteMeasure Point)
    (F A : Point → Tensor) (hSm : MeasurableSet S) (hlen : HausdorffOne S < ⊤)
    (hF : Integrable F ((μ : Measure Point).restrict Ω))
    (hB : ∀ᵐ x ∂((μ : Measure Point).restrict Ω), 1 ≤ (F x).trace ∧ ‖F x‖ ≤ 2)
    (hac : External.matrixVariation Ω μ F ≪ HausdorffOne)
    (hA : Integrable A (HausdorffOne.restrict S))
    (hrA : ∀ᵐ x ∂HausdorffOne.restrict S, (A x).rank = 1)
    (hEq : ∀ B : Set Point, MeasurableSet B →
      (∫ x in B ∩ Ω, F x ∂(μ : Measure Point)) = ∫ x in B ∩ S, A x ∂HausdorffOne) :
    ((μ : Measure Point).restrict Ω) Sᶜ = 0 ∧
      (μ : Measure Point).restrict Ω ≪ HausdorffOne.restrict S ∧
      ∀ᵐ x ∂((μ : Measure Point).restrict Ω), (F x).rank = 1 := by
  let ξ := (μ : Measure Point).restrict Ω
  let ζ := HausdorffOne.restrict S
  let σ := ξ.restrict Sᶜ
  have hσ : Integrable F σ := hF.integrableOn
  have h0 : ∀ B : Set Point, MeasurableSet B → (∫ x in B, F x ∂σ) = 0 := by
    intro B hBm
    have h := hEq (B ∩ Sᶜ) (hBm.inter hSm.compl)
    have he : (B ∩ Sᶜ) ∩ S = ∅ := by
      ext x
      simp [and_assoc]
    rw [he, setIntegral_empty] at h
    change (∫ x, F x ∂(σ.restrict B)) = 0
    dsimp only [σ, ξ]
    rw [Measure.restrict_restrict hBm, Measure.restrict_restrict (hBm.inter hSm.compl)]
    exact h
  have hFzero := hσ.ae_eq_zero_of_forall_setIntegral_eq_zero (fun B hBm _ => h0 B hBm)
  have hσnull : σ univ = 0 := by
    have hfalse : ∀ᵐ x ∂σ, False := by
      filter_upwards [ae_restrict_of_ae hB, hFzero] with x hx hx'
      change F x = 0 at hx'
      have hf := hx.1
      rw [hx', Matrix.trace_zero] at hf
      norm_num at hf
    simpa only [ae_iff, not_false_eq_true, setOf_true] using hfalse
  have hmass : ξ Sᶜ = 0 := by
    change (ξ.restrict Sᶜ) univ = 0 at hσnull
    rwa [Measure.restrict_apply MeasurableSet.univ, univ_inter] at hσnull
  have hlo := (matrixVariation_comparable (μ : Measure Point) F hB).1
  have hdom : ξ ≪ External.matrixVariation Ω μ F := by
    intro B hZ
    have h := hlo B
    change (ENNReal.ofReal (Real.sqrt 3)⁻¹ • ξ) B ≤ _ at h
    rw [hZ, Measure.smul_apply, smul_eq_mul] at h
    have hc : ENNReal.ofReal (Real.sqrt 3)⁻¹ ≠ 0 :=
      (ENNReal.ofReal_pos.2 (inv_pos.2 (Real.sqrt_pos.2 (by norm_num)))).ne'
    exact (mul_eq_zero.mp (nonpos_iff_eq_zero.mp h)).resolve_left hc
  have hξ : ξ ≪ HausdorffOne := hdom.trans hac
  have hξS : ξ.restrict S = ξ := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact ae_iff.2 hmass
  have hAc : ξ ≪ ζ := by
    rw [← hξS]
    exact hξ.restrict S
  letI : IsFiniteMeasure ζ := by
    constructor
    simpa only [ζ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using hlen
  letI : IsFiniteMeasure ξ := inferInstanceAs (IsFiniteMeasure ((μ : Measure Point).restrict Ω))
  letI : ξ.HaveLebesgueDecomposition ζ := Measure.haveLebesgueDecomposition_of_finiteMeasure
  let p : Point → ℝ := fun x => (ξ.rnDeriv ζ x).toReal
  let G : Point → Tensor := fun x => p x • F x
  have hG : Integrable G ζ := (integrable_rnDeriv_smul_iff hAc).2 hF
  have hGA : G =ᵐ[ζ] A := Integrable.ae_eq_of_forall_setIntegral_eq _ _ hG hA (by
    intro B hBm _
    rw [show (∫ x in B, G x ∂ζ) = ∫ x in B, F x ∂ξ from setIntegral_rnDeriv_smul hAc hBm]
    dsimp only [ξ, ζ]
    rw [Measure.restrict_restrict hBm, Measure.restrict_restrict hBm]
    exact hEq B hBm)
  refine ⟨hmass, hAc, hAc.ae_le ?_⟩
  filter_upwards [hGA, hrA] with x hx hx'
  have hr : (p x • F x).rank = 1 := by rw [show p x • F x = A x from hx, hx']
  have hp : p x ≠ 0 := by
    intro hz
    rw [hz, zero_smul, Matrix.rank_zero] at hr
    omega
  rwa [rank_smul_of_ne_zero hp] at hr

/-- The interior support is itself the rectifiable carrier. The normalized
stress is a line projection almost everywhere with respect to the energy. -/
theorem rectifiable_interior_support_of_A19 (hA19 : External.A19Prop31)
    {Ω : Set Point} (hΩ : IsOpen Ω) (μ : FiniteMeasure Point) (F : Point → Tensor)
    (hF : Integrable F ((μ : Measure Point).restrict Ω)) (hDiv : External.RowDivergenceFree Ω μ F)
    (hB : ∀ᵐ x ∂((μ : Measure Point).restrict Ω), (F x)ᵀ = F x ∧ 1 ≤ (F x).trace ∧ ‖F x‖ ≤ 2 ∧
      ∀ z : Point, tensorQuadratic (F x) z ≤ ‖z‖ ^ 2)
    {η : ℝ} (hη : 0 < η)
    (hD : ∀ x ∈ Ω ∩ (μ : Measure Point).support,
      ∃ θ ≥ η / 2, Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ)) :
    let S := Ω ∩ (μ : Measure Point).support
    let ξ := (μ : Measure Point).restrict Ω
    CountablyRectifiableOne S ∧ HausdorffOne S < ⊤ ∧
      (∃ θ : Point → ℝ≥0∞, Measurable θ ∧ (∫⁻ x, θ x ∂HausdorffOne.restrict S) < ⊤ ∧
        ξ = (HausdorffOne.restrict S).withDensity θ) ∧ External.matrixVariation Ω μ F = ξ ∧
      ∀ᵐ x ∂ξ, (F x)ᵀ = F x ∧ F x * F x = F x ∧ (F x).rank = 1 ∧
        (F x).trace = 1 ∧ ‖F x‖ = 1 := by
  let S := Ω ∩ (μ : Measure Point).support
  let ξ := (μ : Measure Point).restrict Ω
  let ζ := HausdorffOne.restrict S
  obtain ⟨hac, S₀, A, hS₀m, hSsub, hS₀rect, hS₀len, hA, hrA, hEq⟩ :=
    rectifiable_stressCarrier_of_A19 hA19 hΩ μ F hF hDiv (hB.mono fun _ hx =>
      ⟨hx.1, hx.2.1, hx.2.2.1⟩) hη hD
  obtain ⟨hnull, hμac, hr⟩ := rank_one_of_stressCarrier μ F A hS₀m hS₀len hF
    (hB.mono fun _ hx => ⟨hx.2.1, hx.2.2.1⟩) hac hA hrA hEq
  have hLen (E : Set Point) (hE : E ⊆ S) :
      HausdorffOne E ≤ ENNReal.ofReal (40 / η) * (μ : Measure Point) E :=
    hausdorffOne_le_of_positive_oneDensity (μ : Measure Point) hE hη hD
  have hlen : HausdorffOne S < ⊤ := (hLen S Subset.rfl).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
  have hnullS : HausdorffOne (S \ S₀) = 0 := by
    have hm : (μ : Measure Point) (S \ S₀) = 0 := by
      have hsub : S \ S₀ ⊆ S₀ᶜ ∩ Ω := fun _ hx => ⟨hx.2, hx.1.1⟩
      apply nonpos_iff_eq_zero.mp
      calc
        _ ≤ (μ : Measure Point) (S₀ᶜ ∩ Ω) := measure_mono hsub
        _ = ξ S₀ᶜ := (Measure.restrict_apply hS₀m.compl).symm
        _ = 0 := hnull
    exact nonpos_iff_eq_zero.mp ((hLen _ sdiff_subset).trans (by rw [hm, mul_zero]))
  have hrect : CountablyRectifiableOne S := by
    obtain ⟨f, hLip, hzero⟩ := hS₀rect
    refine ⟨f, hLip, nonpos_iff_eq_zero.mp ?_⟩
    have hsub : S \ (⋃ i, range (f i)) ⊆ (S₀ \ (⋃ i, range (f i))) ∪ (S \ S₀) := by
      intro x hx
      by_cases h : x ∈ S₀
      · exact Or.inl ⟨h, hx.2⟩
      · exact Or.inr ⟨hx.1, h⟩
    calc
      _ ≤ HausdorffOne ((S₀ \ (⋃ i, range (f i))) ∪ (S \ S₀)) := measure_mono hsub
      _ ≤ HausdorffOne (S₀ \ (⋃ i, range (f i))) + HausdorffOne (S \ S₀) := measure_union_le _ _
      _ = 0 := by rw [hzero, hnullS, zero_add]
  have hAc : ξ ≪ ζ := hμac.trans (Measure.absolutelyContinuous_of_le
    (Measure.restrict_mono_set HausdorffOne hSsub))
  letI : IsFiniteMeasure ζ := by
    constructor
    simpa only [ζ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using hlen
  letI : IsFiniteMeasure ξ := inferInstanceAs (IsFiniteMeasure ((μ : Measure Point).restrict Ω))
  letI : ξ.HaveLebesgueDecomposition ζ := Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hP : ∀ᵐ x ∂ξ, (F x)ᵀ = F x ∧ F x * F x = F x ∧ (F x).rank = 1 ∧
      (F x).trace = 1 ∧ ‖F x‖ = 1 := by
    filter_upwards [hB, hr] with x hx hx'
    obtain ⟨hidem, ht, hn⟩ := isLineProjection_of_rank_one_stress (F x) hx.1 hx.2.1 hx.2.2.2 hx'
    exact ⟨hx.1, hidem, hx', ht, hn⟩
  refine ⟨hrect, hlen, ⟨ξ.rnDeriv ζ, Measure.measurable_rnDeriv _ _,
    Measure.lintegral_rnDeriv_lt_top _ _, (Measure.withDensity_rnDeriv_eq _ _ hAc).symm⟩, ?_, hP⟩
  change ξ.withDensity (fun x => ENNReal.ofReal ‖F x‖) = ξ
  have hE : (fun x => ENNReal.ofReal ‖F x‖) =ᵐ[ξ] (fun _ => (1 : ℝ≥0∞)) := hP.mono
    (fun x hx => by
      change ENNReal.ofReal ‖F x‖ = 1
      rw [hx.2.2.2.2, ENNReal.ofReal_one])
  rw [withDensity_congr_ae hE, withDensity_const, one_smul]

end Thesis.MeasureGeometry

end
