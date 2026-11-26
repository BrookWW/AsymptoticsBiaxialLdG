module

public import Mathlib

/-! Small-ball differentiation at a singular reference measure. -/

public section

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology MeasureTheory

set_option autoImplicit false

namespace SupportingAnalysis

theorem ae_tendsto_closedBall_mass_ratio_zero {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [HasBesicovitchCovering X]
    (ρ ν : Measure X) [IsLocallyFiniteMeasure ρ] [IsLocallyFiniteMeasure ν]
    (hSing : ρ ⟂ₘ ν) :
    ∀ᵐ x ∂ν, Tendsto (fun r => ρ (closedBall x r) / ν (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv ρ ν, hSing.rnDeriv_ae_eq_zero] with x hx hz
  change ρ.rnDeriv ν x = 0 at hz
  rwa [hz] at hx

/-- A singular numerator has vanishing normalized mass wherever the reference
    measure has bounded normalized upper density. -/
theorem ae_tendsto_normalized_closedBall_mass_zero {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [HasBesicovitchCovering X]
    (ρ ν : Measure X) [IsLocallyFiniteMeasure ρ] [IsFiniteMeasure ν]
    (hSing : ρ ⟂ₘ ν) (scale : ℝ → ℝ≥0∞)
    (hDensity : ∀ᵐ x ∂ν, ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ), scale r * ν (closedBall x r) ≤ C) :
    ∀ᵐ x ∂ν, Tendsto (fun r => scale r * ρ (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_closedBall_mass_ratio_zero ρ ν hSing, ν.support_mem_ae, hDensity]
    with x hratio hsupport hdensity
  rcases hdensity with ⟨C, hC, hbound⟩
  have hupper : Tendsto (fun r => (ρ (closedBall x r) / ν (closedBall x r)) * C)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hratio (Or.inr hC)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall fun _ => zero_le
  · filter_upwards [self_mem_nhdsWithin, hbound] with r hr hle
    have hrpos : 0 < r := hr
    have hpos : 0 < ν (closedBall x r) :=
      (Measure.mem_support_iff_forall x).mp hsupport _ (closedBall_mem_nhds x hrpos)
    have hfin : ν (closedBall x r) ≠ ∞ := (measure_lt_top ν _).ne
    calc
      scale r * ρ (closedBall x r) =
          (ρ (closedBall x r) / ν (closedBall x r)) * (scale r * ν (closedBall x r)) := by
        rw [mul_left_comm, ENNReal.div_mul_cancel hpos.ne' hfin]
      _ ≤ (ρ (closedBall x r) / ν (closedBall x r)) * C := by gcongr

theorem ae_tendsto_normalized_ball_mass_zero {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [HasBesicovitchCovering X]
    (ρ ν : Measure X) [IsLocallyFiniteMeasure ρ] [IsFiniteMeasure ν]
    (hSing : ρ ⟂ₘ ν) (scale : ℝ → ℝ≥0∞)
    (hDensity : ∀ᵐ x ∂ν, ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ), scale r * ν (closedBall x r) ≤ C) :
    ∀ᵐ x ∂ν, Tendsto (fun r => scale r * ρ (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_normalized_closedBall_mass_zero ρ ν hSing scale hDensity] with x hx
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hx
  · exact fun _ => zero_le
  · intro r
    exact mul_le_mul' le_rfl (measure_mono ball_subset_closedBall)

theorem mutuallySingular_of_absolutelyContinuous_of_null_supported {X : Type*}
    [MeasurableSpace X] (ρ σ ν : Measure X) {S : Set X} (hρ : ρ ≪ σ)
    (hS : MeasurableSet S) (hσ : σ S = 0) (hν : ν Sᶜ = 0) : ρ ⟂ₘ ν :=
  ⟨S, hS, hρ hσ, hν⟩

end SupportingAnalysis
