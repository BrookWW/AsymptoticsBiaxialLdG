module

public import SupportingAnalysis.Measure.Rescaling

/-! Vague tangents on countable covers of a finite measure. -/

public section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

set_option autoImplicit false

namespace SupportingAnalysis

/-- Almost-everywhere flat tangents on a countable measurable cover of a finite
measure also give flat tangents of the full measure. -/
theorem ae_flatTangent_of_countable_restrict {m d : ℕ}
    (ν : Measure (E m)) [IsFiniteMeasure ν]
    (S : ℕ → Set (E m)) (hS : ∀ j, MeasurableSet (S j))
    (hCover : ν (⋃ j, S j)ᶜ = 0)
    (hPiece : ∀ j, ∀ᵐ x ∂ν.restrict (S j),
      ∃ (L : Submodule ℝ (E m)) (b : ℝ),
        Module.finrank ℝ L = d ∧ 0 < b ∧
        VagueOn univ (𝓝[>] (0 : ℝ))
          (fun r => @blownUpMeasure m d x r (ν.restrict (S j)))
          (ENNReal.ofReal b • μH[(d : ℝ)].restrict (L : Set (E m)))) :
    ∀ᵐ x ∂ν, ∃ (L : Submodule ℝ (E m)) (b : ℝ),
      Module.finrank ℝ L = d ∧ 0 < b ∧
      VagueOn univ (𝓝[>] (0 : ℝ)) (fun r => @blownUpMeasure m d x r ν)
        (ENNReal.ofReal b • μH[(d : ℝ)].restrict (L : Set (E m))) := by
  have hν : ν.restrict (⋃ j, S j) = ν := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hCover)
  rw [← hν]
  apply (ae_restrict_iUnion_iff _ _).2
  intro j
  let η := ν.restrict (S j)
  let ρ := ν.restrict (S j)ᶜ
  have hEach : ∀ᵐ x ∂η, ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (r ^ (-(d : ℤ))) * η (closedBall x r) ≤ C := by
    filter_upwards [hPiece j] with x hx
    obtain ⟨L, b, _, _, hV⟩ := hx
    exact eventually_bounded_normalized_closedBall_mass_of_vague_blowup x η _ hV
  have hSing : ρ ⟂ₘ η := by
    refine ⟨S j, hS j, ?_, ?_⟩
    · rw [Measure.restrict_apply (hS j), inter_compl_self, measure_empty]
    · rw [Measure.restrict_apply (hS j).compl, compl_inter_self, measure_empty]
  have hρ := ae_tendsto_normalized_closedBall_mass_zero ρ η hSing
    (fun r => ENNReal.ofReal (r ^ (-(d : ℤ)))) hEach
  filter_upwards [hPiece j, hρ] with x hx hz
  obtain ⟨L, b, hL, hb, hV⟩ := hx
  have hSum : ρ + η = ν := Measure.restrict_compl_add_restrict (hS j)
  refine ⟨L, b, hL, hb, ?_⟩
  rw [hν, ← hSum]
  exact vagueOn_blownUpMeasure_add_left_zero x ρ η _
    (vagueOn_blownUpMeasure_zero_of_normalizedMass x ρ hz) hV

end SupportingAnalysis
