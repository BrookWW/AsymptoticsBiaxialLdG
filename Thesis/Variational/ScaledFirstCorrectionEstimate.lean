module

public import Thesis.Variational.BoundaryLayerDual
public import Thesis.Variational.WeakCorrectionGreen

/-! The uniform fractional estimate for the literal scaled forcing. -/

public section

open Filter MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

theorem exists_scaled_dirichlet_forcing_bound_of_wall_profile
    (hHardy : External.DirichletFractionalHardyAndCollar)
    {U : Set Point} (hU : IsSmoothDomain U) (s c : ℝ) (hs : 0 < s) (hs₁ : s < 1/2) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Point → S0) (D ε : ℝ), 0 ≤ D → 0 < ε →
      AEStronglyMeasurable F (volume.restrict U) →
      (∀ x ∈ U, ‖F x‖ ≤ D * (ε^2 / Metric.infDist x (frontier U) +
        Real.exp (-c * Metric.infDist x (frontier U) / ε))) →
      HasFractionalDirichletForcingBound s U (fun x => (ε^2)⁻¹ • F x) (C * D) := by
  obtain ⟨K, hK, hLayer⟩ := exists_fractional_dirichlet_forcing_bound_of_layer_profile hHardy hU s c hs hs₁ hc
  refine ⟨K, hK, ?_⟩
  intro F D ε hD hε hMeas hProfile
  have h := (hLayer F D ε hD hε hMeas hProfile).const_smul (inv_nonneg.mpr (sq_nonneg ε))
  have hs : (ε^2)⁻¹ * (K*D*ε^2) = K*D := by field_simp [hε.ne']
  rwa [hs] at h

end Thesis

end
