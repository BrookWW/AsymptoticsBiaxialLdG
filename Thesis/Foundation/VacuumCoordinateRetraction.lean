module

public import Thesis.Foundation.VacuumTube

/-! Smooth bounded projection in the original Frobenius coordinates. -/

public section

noncomputable section

open HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace Thesis

/-- A globally smooth bounded-derivative extension agrees with the
vacuum retraction on its open coordinate tube. -/
theorem exists_smooth_vacuumCoordinate_retraction (a : BulkCoefficients) :
    let N := vacuumCompactSmoothEmbeddedTarget a
    ∃ ρ > (0 : ℝ), ∃ Q : Ambient 5 → Ambient 5, ∃ C : ℝ,
      ContDiff ℝ ∞ Q ∧ (∀ x, ‖fderiv ℝ Q x‖ ≤ C) ∧ (∀ x ∈ N.carrierSet, Q x = x) ∧
      ∀ x, Metric.infDist x N.carrierSet < ρ → Q x ∈ N.carrierSet := by
  let N := vacuumCompactSmoothEmbeddedTarget a
  obtain ⟨ρ,hρ,_,hSub,_,_,hFix,_,_,_,_,_,_,Q,hQ,hEq,C,_,_,_,hC,_⟩ :=
    HarmonicMaps.tubularProjection_complete 5 N
  refine ⟨ρ,hρ,Q,C,hQ,hC,?_,?_⟩
  · intro x hx
    obtain ⟨hp,hpEq,_⟩ := hFix ⟨x,hx⟩
    have hd : Metric.infDist x N.carrierSet < ρ := (Metric.infDist_zero_of_mem hx) ▸ hρ
    exact (hEq ⟨x,hSub hp⟩ hd).trans (congrArg Subtype.val hpEq)
  · intro x hx
    have hT := hSub (hx.trans (by linarith only [hρ]))
    rw [hEq ⟨x,hT⟩ hx]
    exact (HarmonicMaps.tubularProjection 5 N ⟨x,hT⟩).property

end Thesis
