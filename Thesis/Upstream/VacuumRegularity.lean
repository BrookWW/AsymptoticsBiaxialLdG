module

public import Thesis.Upstream.MinimizingRegularity
public import Thesis.Foundation.VacuumTarget

/-! Interior regularity on the actual compact smooth biaxial vacuum target. -/

public section

open Filter MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace Thesis

/-- In dimension three the singular set of the given locally minimizing
vacuum-valued map is locally finite in its open domain. -/
theorem locallyFiniteIn_singularSet_of_vacuum_minimizer (a : BulkCoefficients)
    {Ω : Set Point} (hΩ : IsOpen Ω) {u : Point → S0} {D : Point → Gradient}
    (hmin : IsLocalDirichletMinimizer a Ω u D) :
    LocallyFiniteIn Ω (singularSet Ω u) := by
  let U : HarmonicMaps.OpenDomain 3 := ⟨Ω, hΩ⟩
  exact locallyFiniteIn_singularSet_of_upstreamTarget a U
    (vacuumCompactSmoothEmbeddedTarget a) (vacuumCompactSmoothEmbeddedTarget_carrierSet a) u D hmin

/-- The smooth representative on the whole regular region uses the same map
and weak gradients as the locally minimizing limit. -/
theorem vacuum_minimizer_exists_regularRepresentative (a : BulkCoefficients)
    {Ω : Set Point} (hΩ : IsOpen Ω) {u : Point → S0} {D : Point → Gradient}
    (hmin : IsLocalDirichletMinimizer a Ω u D) :
    LocallyFiniteIn Ω (singularSet Ω u) ∧
      ∃ v : Point → S0, v =ᵐ[volume.restrict Ω] u ∧ MemH1Loc Ω v D ∧
        ContDiffOn ℝ ∞ v (Ω \ singularSet Ω u) ∧
        D =ᵐ[volume.restrict (Ω \ singularSet Ω u)] ClassicalGradient v := by
  exact ⟨locallyFiniteIn_singularSet_of_vacuum_minimizer a hΩ hmin,
    hmin.1.exists_regularRepresentative hΩ⟩

end Thesis

end
