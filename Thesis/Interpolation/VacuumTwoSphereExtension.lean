module

public import Thesis.Interpolation.VacuumSphereSobolevLift
public import Thesis.Interpolation.VacuumSphereFill

/-! Vacuum-valued Dirichlet extension of a two-sphere trace. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped Matrix.Norms.Frobenius

namespace Thesis

/-- A two-sphere vacuum trace has a vacuum-valued unit-ball extension with
its exact trace and an energy bound linear in the boundary gradient norm. -/
theorem exists_vacuum_twoSphere_extension (a : BulkCoefficients)
    (hDense : External.SmoothVacuumSphereDensity a)
    (hP : External.QuaternionSpherePoincare 3 (by decide : 2 ≤ 3)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_base : UnitBoundarySphere 3) (Q : UnitBoundarySphere 3 → vacuum a)
      (hQ : MemSphereW12 (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (Q θ).val)),
      ∃ (b : ℝ) (hb : b < 1) (w : Point → Ambient 5)
        (Dw : Point → HarmonicMaps.Gradient 3 5) (J : VacuumBallTrace 3 b),
        0 < b ∧ MemW12 (ballDomain (0 : Point) 1) w Dw ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Point) 1), frobeniusCoordinateEquiv.symm (w x) ∈ vacuum a) ∧
        RepresentsVacuumBallTrace w J ∧
        J ⟨1, hb.le, le_rfl⟩ = hQ.1.toLp (fun θ => frobeniusCoordinateEquiv (Q θ).val) ∧
        (∫ x in ball (0 : Point) 1, hsNormSq (Dw x)) ≤
          C * Real.sqrt (vacuumSphereGradientEnergy (by decide : 2 ≤ 3) Q hQ) := by
  obtain ⟨K, hK, hFill⟩ := exists_quaternion_sphere_fill_unit (by decide : 2 ≤ 3) hP
  obtain ⟨L, hL, hCover⟩ := exists_vacuum_ball_fill_of_quaternion_fill a
  let B := 8 * vacuumRadius a ^ 2
  have hB : 0 < B := by dsimp only [B]; positivity [vacuumRadius_pos a]
  refine ⟨(L * K) / Real.sqrt B, div_pos (mul_pos hL hK) (Real.sqrt_pos.2 hB), ?_⟩
  intro base Q hQ
  obtain ⟨v, hv, hCov, hE⟩ := exists_quaternionSobolevLift_of_vacuumSphere a hDense base Q hQ
  have hUnit : ∀ᵐ θ ∂unitBoundarySurface 3, ‖(v θ).val‖ = 1 :=
    ae_of_all _ fun θ => mem_sphere_zero_iff_norm.1 (v θ).property
  obtain ⟨b, hb, u, Du, H, hb₀, hu, huV, huTrace, huB, huE⟩ := hFill _ hv hUnit
  obtain ⟨w, Dw, J, hw, hwV, hwTrace, ⟨hLp, hEnd⟩, hwE⟩ :=
    hCover (by decide : 2 ≤ 3) v hv.1 hb H hu huV huTrace huB
  have hLpEq := MemLp.toLp_congr hLp hQ.1
    (hCov.mono fun θ hθ => congrArg frobeniusCoordinateEquiv hθ)
  refine ⟨b, hb, w, Dw, J, hb₀, hw, hwV, hwTrace, hEnd.trans hLpEq, ?_⟩
  let E := vacuumSphereGradientEnergy (by decide : 2 ≤ 3) Q hQ
  have hE₀ : 0 ≤ E := by
    dsimp only [E, vacuumSphereGradientEnergy]
    exact integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSqrt : Real.sqrt (quaternionBoundaryEnergy (by decide : 2 ≤ 3) (fun θ => (v θ).val) hv) ≤
      Real.sqrt E / Real.sqrt B := by
    rw [← Real.sqrt_div hE₀]
    apply Real.sqrt_le_sqrt
    apply (le_div_iff₀ hB).2
    rw [mul_comm]
    exact hE
  calc
    _ ≤ L * (∫ x in ball (0 : Point) 1, hsNormSq (Du x)) := hwE
    _ ≤ L * (K * (Real.sqrt E / Real.sqrt B)) :=
      mul_le_mul_of_nonneg_left
        (huE.trans (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hSqrt) hK.le)) hL.le
    _ = _ := by ring

end Thesis
