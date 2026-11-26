module

public import SupportingAnalysis.Measure.Rescaling
import SupportingAnalysis.Measure.ChartDensity
import SupportingAnalysis.Measure.ChartLimits
import SupportingAnalysis.Measure.TangentGluing
import SupportingAnalysis.Measure.Charts

/-! Flat vague tangents of finite measures with positive rectifiable weights. -/

public section

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology

set_option autoImplicit false

namespace SupportingAnalysis

private theorem ae_chartTangent {m d : ℕ} {f : E d → E m} {A : Set (E d)}
    (hA : MeasurableSet A) (hBnd : Bornology.IsBounded A)
    {K L : ℝ≥0} (hf : LipschitzWith K f) (hLower : AntilipschitzWith L (A.restrict f))
    (hDiff : ∀ x ∈ A, DifferentiableAt ℝ f x ∧ Function.Injective (fderiv ℝ f x))
    (ν : Measure (E m)) [IsFiniteMeasure ν] (hν : ν ≪ μH[(d : ℝ)])
    (hCarried : ∀ᵐ x ∂ν, x ∈ f '' A) :
    ∀ᵐ x ∂ν,
      ∃ (P : Submodule ℝ (E m)) (b : ℝ), Module.finrank ℝ P = d ∧ 0 < b ∧
        VagueOn univ (𝓝[>] (0 : ℝ)) (fun r => @blownUpMeasure m d x r ν)
          (ENNReal.ofReal b • μH[(d : ℝ)].restrict (P : Set (E m))) := by
  obtain ⟨w, hw, hwI, hw₀, hwA, hνMap⟩ := exists_chart_density hf hA hBnd ν hν hCarried
  let W (a : E d) := ENNReal.ofReal (w a)
  let γ := volume.withDensity W
  have hW : Measurable W := ENNReal.continuous_ofReal.measurable.comp hw
  have hPos : ∀ᵐ a ∂γ, 0 < w a := (ae_withDensity_iff hW).2 <|
    .of_forall fun a ha => ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr ha)
  have hMem : ∀ᵐ a ∂γ, a ∈ A := hPos.mono fun a ha => by
    by_contra hz
    exact (ne_of_gt ha) (hwA a hz)
  let p (x : E m) : Prop :=
    ∃ (P : Submodule ℝ (E m)) (b : ℝ), Module.finrank ℝ P = d ∧ 0 < b ∧
      VagueOn univ (𝓝[>] (0 : ℝ)) (fun r => @blownUpMeasure m d x r ν)
        (ENNReal.ofReal b • μH[(d : ℝ)].restrict (P : Set (E m)))
  have hp : ∀ᵐ a ∂γ, p (f a) := by
    filter_upwards [hPos, hMem, (withDensity_absolutelyContinuous volume W).ae_le
      (ae_chartDensity_lebesguePoint hwI)] with a haPos ha hLeb
    obtain ⟨haDiff, hInj⟩ := hDiff a ha
    let D := fderiv ℝ f a
    obtain ⟨L', _, hD⟩ := D.toLinearMap.injective_iff_antilipschitz.mp hInj
    let Q : ℝ := max (L : ℝ) (L' : ℝ)
    have hQ : 0 ≤ Q := (NNReal.coe_nonneg L).trans (le_max_left _ _)
    have hWLower (y : E d) (hy : w y ≠ 0) : ‖y - a‖ ≤ Q * ‖f y - f a‖ := by
      have hyA : y ∈ A := by
        by_contra hz
        exact hy (hwA y hz)
      have h := hLower.le_mul_dist (⟨y, hyA⟩ : A) (⟨a, ha⟩ : A)
      change dist y a ≤ (L : ℝ) * dist (f y) (f a) at h
      rw [dist_eq_norm, dist_eq_norm] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hDLower (z : E d) : ‖z‖ ≤ Q * ‖D z‖ := by
      have h := hD.le_mul_dist z 0
      change dist z 0 ≤ (L' : ℝ) * dist (D z) (D 0) at h
      rw [map_zero, dist_zero_right, dist_zero_right] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    have hV := vagueOn_blownUpMeasure_weightedChart hf.continuous hw hwI hw₀
      haDiff.hasFDerivAt Q hQ hWLower hDLower hLeb
    obtain ⟨c, hc, hMap⟩ := exists_map_linear_volume_eq_hausdorff D hInj
    refine ⟨D.range, w a * c, ?_, mul_pos haPos hc, ?_⟩
    · rw [LinearMap.finrank_range_of_inj hInj, finrank_euclideanSpace_fin]
    · rw [hνMap, hMap, smul_smul, ← ENNReal.ofReal_mul (hw₀ a)] at hV
      exact hV
  letI := hA.standardBorel
  have hEmb : MeasurableEmbedding (A.restrict f) :=
    (hf.continuous.measurable.comp measurable_subtype_coe).measurableEmbedding hLower.injective
  have hMap : Measure.map (A.restrict f) (γ.comap Subtype.val) = ν := by
    change Measure.map (f ∘ (Subtype.val : A → E d)) (γ.comap Subtype.val) = ν
    rw [← Measure.map_map hf.continuous.measurable measurable_subtype_coe,
      map_comap_subtype_coe hA, Measure.restrict_eq_self_of_ae_mem hMem]
    exact hνMap
  change ∀ᵐ x ∂ν, p x
  rw [← hMap, hEmb.ae_map_iff]
  exact ((MeasurableEmbedding.subtype_coe hA).ae_map_iff (p := fun a => p (f a))).mp (by
    rw [map_comap_subtype_coe hA, Measure.restrict_eq_self_of_ae_mem hMem]
    exact hp)

/-- A positive integrable weight on a countably rectifiable carrier has flat
vague tangents as the radius tends to zero through positive reals. -/
theorem rectifiableMeasureTangents : External.WeightedRectifiableTangents := by
  intro m d S Θ hS hrect _ hΘ hΘpos hν
  let η := (μH[(d : ℝ)]).restrict S
  let ν := η.withDensity Θ
  letI : IsFiniteMeasure ν := hν
  have hνη : ν ≪ η := withDensity_absolutelyContinuous η Θ
  have hνHaus : ν ≪ μH[(d : ℝ)] :=
    hνη.trans Measure.restrict_le_self.absolutelyContinuous
  have hην : η ≪ ν := withDensity_absolutelyContinuous' hΘ.aemeasurable
    (hΘpos.mono fun _ hx => hx.ne')
  obtain ⟨A, f, hA, hBnd, hBi, hDiff, hnull⟩ := hrect.exists_regular_bilipschitz_cover
  let B (n : ℕ) := f n '' A n
  have hB (n : ℕ) : MeasurableSet (B n) := by
    obtain ⟨_, _, hf, hLower⟩ := hBi n
    letI := (hA n).standardBorel
    have he : MeasurableEmbedding ((A n).restrict (f n)) :=
      (hf.continuous.measurable.comp measurable_subtype_coe).measurableEmbedding hLower.injective
    simpa only [B, Set.range_restrict] using he.measurableSet_range
  have hCover : ν (⋃ n, B n)ᶜ = 0 := by
    apply hνη
    change ((μH[(d : ℝ)]).restrict S) (⋃ n, B n)ᶜ = 0
    rw [Measure.restrict_apply' hS, inter_comm]
    exact hnull
  apply hην.ae_le
  apply ae_flatTangent_of_countable_restrict ν B hB hCover
  intro n
  obtain ⟨_, _, hf, hLower⟩ := hBi n
  exact ae_chartTangent (hA n) (hBnd n) hf hLower (hDiff n) (ν.restrict (B n))
    (Measure.restrict_le_self.absolutelyContinuous.trans hνHaus) (ae_restrict_mem (hB n))

end SupportingAnalysis
