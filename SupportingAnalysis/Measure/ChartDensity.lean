module

public import SupportingAnalysis.Basics
import Mathlib.Analysis.InnerProductSpace.NormDet

/-! Lebesgue densities of chart measures and Hausdorff measure on linear images. -/

public section

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology

set_option autoImplicit false

namespace SupportingAnalysis

/-- A finite measure carried by the image of a bounded chart and absolutely continuous
with respect to dimensional Hausdorff measure is the pushforward of a Lebesgue density. -/
theorem exists_chart_density {m d : ℕ}
    {f : E d → E m} {K : ℝ≥0} (hf : LipschitzWith K f)
    {A : Set (E d)} (hA : MeasurableSet A) (hBound : Bornology.IsBounded A)
    (ν : Measure (E m)) [IsFiniteMeasure ν]
    (hν : ν ≪ μH[(d : ℝ)]) (hCarried : ∀ᵐ x ∂ν, x ∈ f '' A) :
    ∃ w : E d → ℝ, Measurable w ∧ Integrable w ∧ (∀ x, 0 ≤ w x) ∧
      (∀ x ∉ A, w x = 0) ∧
      Measure.map f (volume.withDensity (fun x => ENNReal.ofReal (w x))) = ν := by
  let σ := Measure.map f (volume.restrict A)
  letI : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.2 hBound.measure_lt_top.ne
  letI : IsFiniteMeasure σ := inferInstanceAs (IsFiniteMeasure (Measure.map f (volume.restrict A)))
  have hfmeas := hf.continuous.measurable
  have hn : ν ≪ σ := by
    apply Measure.AbsolutelyContinuous.mk
    intro T hT hT0
    change Measure.map f (volume.restrict A) T = 0 at hT0
    rw [Measure.map_apply hfmeas hT, Measure.restrict_apply (hfmeas hT)] at hT0
    have hH : μH[(d : ℝ)] (f ⁻¹' T ∩ A) = 0 := by
      have he := hT0
      rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume d,
        Measure.euclideanHausdorffMeasure_def, Measure.smul_apply] at he
      change (↑(Measure.addHaarScalarFactor (volume : Measure (E d)) μH[(d : ℝ)]) : ℝ≥0∞) *
        μH[(d : ℝ)] (f ⁻¹' T ∩ A) = 0 at he
      exact (mul_eq_zero.mp he).resolve_left
        (ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d))
    have he : T ∩ f '' A = f '' (f ⁻¹' T ∩ A) := by
      ext z
      constructor
      · rintro ⟨hz, x, hx, rfl⟩
        exact ⟨x, ⟨hz, hx⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hxA⟩, rfl⟩
        exact ⟨hx, mem_image_of_mem _ hxA⟩
    rw [← Measure.restrict_eq_self_of_ae_mem hCarried, Measure.restrict_apply hT, he]
    apply hν
    exact nonpos_iff_eq_zero.mp ((hf.hausdorffMeasure_image_le (Nat.cast_nonneg d) _).trans_eq
      (by rw [hH, mul_zero]))
  letI : ν.HaveLebesgueDecomposition σ := Measure.haveLebesgueDecomposition_of_finiteMeasure
  let W := ν.rnDeriv σ
  have hW : Measurable W := Measure.measurable_rnDeriv _ _
  let w₀ := A.indicator (W ∘ f)
  have hw₀ : Measurable w₀ := (hW.comp hfmeas).indicator hA
  let γ := volume.withDensity w₀
  have hγ : Measure.map f γ = ν := by
    rw [← Measure.withDensity_rnDeriv_eq ν σ hn]
    ext T hT
    rw [Measure.map_apply hfmeas hT, show γ = volume.withDensity w₀ from rfl,
      show w₀ = A.indicator (W ∘ f) from rfl, withDensity_indicator hA,
      withDensity_apply _ (hfmeas hT), withDensity_apply _ hT]
    have h := lintegral_map (hW.indicator hT) hfmeas
        (μ := volume.restrict A)
    rw [lintegral_indicator hT] at h
    rw [← lintegral_indicator (hfmeas hT)]
    change (∫⁻ x, (f ⁻¹' T).indicator (W ∘ f) x ∂volume.restrict A) = ∫⁻ x in T, W x ∂σ
    rw [h]
    apply lintegral_congr_ae (.of_forall fun x => ?_)
    by_cases hx : f x ∈ T <;> simp [hx, Function.comp_def]
  letI : IsFiniteMeasure γ := ⟨by
    have h := congrArg (fun τ : Measure (E m) => τ univ) hγ
    rw [Measure.map_apply hfmeas MeasurableSet.univ, preimage_univ] at h
    rw [h]
    exact measure_lt_top ν _⟩
  have hInt : (∫⁻ x, w₀ x) ≠ ∞ := by
    have he := withDensity_apply w₀ (μ := (volume : Measure (E d))) MeasurableSet.univ
    rw [Measure.restrict_univ] at he
    rw [← he]
    exact (measure_lt_top γ _).ne
  let w (x : E d) : ℝ := (w₀ x).toReal
  refine ⟨w, hw₀.ennreal_toReal, integrable_toReal_of_lintegral_ne_top hw₀.aemeasurable hInt,
    fun _ => ENNReal.toReal_nonneg, ?_, ?_⟩
  · intro x hx
    simp [w, w₀, hx]
  · have he : (fun x => ENNReal.ofReal (w x)) =ᵐ[(volume : Measure (E d))] w₀ := by
      filter_upwards [ae_lt_top hw₀ hInt] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    rw [withDensity_congr_ae he]
    exact hγ

/-- The pushforward of Lebesgue measure by an injective linear map is a positive
multiple of Hausdorff measure on its range. -/
theorem exists_map_linear_volume_eq_hausdorff {m d : ℕ}
    (L : E d →L[ℝ] E m) (hL : Function.Injective L) :
    ∃ c : ℝ, 0 < c ∧
      Measure.map L volume = ENNReal.ofReal c • μH[(d : ℝ)].restrict L.range := by
  let D := L.toLinearMap.normDet
  have hD : 0 < D :=
    lt_of_le_of_ne (LinearMap.normDet_nonneg _) <| Ne.symm <|
      (L.toLinearMap.normDet_ne_zero_tfae.out 0 1).2 (LinearMap.ker_eq_bot.mpr hL)
  let κ := Measure.addHaarScalarFactor (volume : Measure (E d)) μH[(d : ℝ)]
  have hκ : κ ≠ 0 := by
    dsimp only [κ]
    exact Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d
  let c := (κ : ℝ) / D
  refine ⟨c, div_pos (by exact_mod_cast bot_lt_iff_ne_bot.mpr hκ) hD, ?_⟩
  ext T hT
  have hS : T ∩ (L.range : Set (E m)) = L '' (L ⁻¹' T) := by
    ext x
    constructor
    · rintro ⟨hx, z, rfl⟩
      exact ⟨z, hx, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z, rfl⟩
  rw [Measure.map_apply L.continuous.measurable hT, Measure.smul_apply, Measure.restrict_apply hT, hS]
  have he := L.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume (L ⁻¹' T)
  simp only [finrank_euclideanSpace_fin, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    ENNReal.smul_def] at he
  change (↑κ : ℝ≥0∞) * μH[(d : ℝ)] (L '' (L ⁻¹' T)) =
    ENNReal.ofReal D * volume (L ⁻¹' T) at he
  have hc : ENNReal.ofReal c * ENNReal.ofReal D = (κ : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_mul' hD.le, show c * D = κ from div_mul_cancel₀ _ hD.ne']
    exact ENNReal.ofReal_coe_nnreal
  change volume (L ⁻¹' T) = ENNReal.ofReal c * μH[(d : ℝ)] (L '' (L ⁻¹' T))
  apply (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hD).ne' ENNReal.ofReal_ne_top).mp
  rw [← he, mul_left_comm, ← mul_assoc, hc]

end SupportingAnalysis
