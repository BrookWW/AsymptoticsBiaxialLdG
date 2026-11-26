module

public import Thesis.External.FractionalDirichlet
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Transposition for the actual bounded weak correction operator. -/

public section

open Filter MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance fracTranspositionHMinusOneNormed (U : Set Point) : NormedAddCommGroup (HMinusOne U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance fracTranspositionHMinusOneNormedSpace (U : Set Point) : NormedSpace ℝ (HMinusOne U) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

/-- A forcing estimate against the actual \(H^{2-s}\) Dirichlet tests. -/
@[expose] def HasFractionalDirichletForcingBound (s : ℝ) (U : Set Point) (F : Point → S0) (M : ℝ) : Prop :=
  0 ≤ M ∧ ∀ w : H10 U, dirichletFractionalTestEnergy s U w < ⊤ →
    |∫ x in U, frobeniusS0 (F x) (h10Value w x)| ≤ M * dirichletFractionalTestNorm s U w

/-- Transposition tests the original weak equation against the actual
adjoint solution and applies the \(H^s\) duality inequality. -/
theorem exists_dirichlet_fractional_transposition_bound
    (hAdj : External.DirichletAdjointFractionalEstimate) (hDual : External.FractionalL2NormDuality)
    {U : Set Point} (hU : IsSmoothDomain U) (s p M : ℝ) (hs : 0 < s) (hs₁ : s < 1/2)
    (hp : 3 < p) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : Point → (S0 × Gradient) →L[ℝ] S0)
      (L : H10 U ≃L[ℝ] HMinusOne U),
      HasBoundedDirichletCorrectionCoefficients U p M A →
      ‖L.symm.toContinuousLinearMap‖ ≤ M →
      (∀ v w : H10 U, L v w = weakCorrectionPairing U A v w) →
      ∀ (F : Point → S0) (N : ℝ), HasFractionalDirichletForcingBound s U F N →
        ∀ v : H10 U, (∀ w : H10 U, L v w = ∫ x in U, frobeniusS0 (F x) (h10Value w x)) →
          MemHs s U (h10Value v) ∧
            Real.sqrt ((fractionalEnergy s U (h10Value v)).toReal) ≤ C * N := by
  obtain ⟨C, hC, hReg⟩ := hAdj U hU s p M hs hs₁ hp hM
  refine ⟨C, hC, ?_⟩
  intro A L hA hL hPair F N hF v hEq
  refine hDual U hU s hs hs₁ v.val.1 (C*N) (mul_nonneg hC hF.1) ?_
  intro f B hB
  obtain ⟨w, hw, hNorm, hAdjoint⟩ := hReg A L hA hL hPair f B hB
  change |∫ x in U, frobeniusS0 (h10Value v x) (f x)| ≤ C * N * B
  rw [← hAdjoint v, hEq w]
  exact (hF.2 w hw).trans ((mul_le_mul_of_nonneg_left hNorm hF.1).trans_eq (by ring))

theorem fractionalEnergy_congr_ae {s : ℝ} {U : Set Point} {u v : Point → S0}
    (h : u =ᵐ[volume.restrict U] v) :
    fractionalEnergy s U u = fractionalEnergy s U v := by
  unfold fractionalEnergy
  congr 1
  · exact lintegral_congr_ae (h.mono fun _ hx => congrArg (fun A : S0 => ENNReal.ofReal (‖A‖^2)) hx)
  · apply lintegral_congr_ae
    filter_upwards [h] with x hx
    apply lintegral_congr_ae
    filter_upwards [h] with y hy
    exact congrArg₂ (fun A B : S0 => ENNReal.ofReal (‖A-B‖^2 / (dist x y)^(3+2*s))) hx hy

theorem MemHs.congr_ae {s : ℝ} {U : Set Point} {u v : Point → S0}
    (h : MemHs s U u) (huv : u =ᵐ[volume.restrict U] v) : MemHs s U v :=
  ⟨h.1.congr huv, (fractionalEnergy_congr_ae huv) ▸ h.2⟩

theorem HasFractionalDirichletForcingBound.const_smul
    {s : ℝ} {U : Set Point} {F : Point → S0} {N c : ℝ}
    (h : HasFractionalDirichletForcingBound s U F N) (hc : 0 ≤ c) :
    HasFractionalDirichletForcingBound s U (fun x => c • F x) (c * N) := by
  refine ⟨mul_nonneg hc h.1, ?_⟩
  intro w hw
  have hP (x : Point) : frobeniusS0 (c • F x) (h10Value w x) = c * frobeniusS0 (F x) (h10Value w x) := by
    rw [← frobeniusCoordinateEquiv_inner, map_smul, real_inner_smul_left, frobeniusCoordinateEquiv_inner]
  simp_rw [hP]
  rw [integral_const_mul, abs_mul, abs_of_nonneg hc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h.2 w hw) hc

/-- Uniform adjoint and forcing data give eventual fractional bounds for
the original representatives of the weak solutions. -/
theorem exists_eventual_Hs_bound_of_weakCorrection_data
    (hAdj : External.DirichletAdjointFractionalEstimate) (hDual : External.FractionalL2NormDuality)
    {U : Set Point} (hU : IsSmoothDomain U) (s p M N : ℝ)
    (hs : 0 < s) (hs₁ : s < 1/2) (hp : 3 < p) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (W F : ℕ → Point → S0) (A : ℕ → Point → (S0 × Gradient) →L[ℝ] S0)
    (hEq : ∀ᶠ n in atTop, ∃ (L : H10 U ≃L[ℝ] HMinusOne U) (v : H10 U),
      HasBoundedDirichletCorrectionCoefficients U p M (A n) ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ M ∧
      (∀ z w : H10 U, L z w = weakCorrectionPairing U (A n) z w) ∧
      HasFractionalDirichletForcingBound s U (F n) N ∧
      h10Value v =ᵐ[volume.restrict U] W n ∧
      (∀ w : H10 U, L v w = ∫ x in U, frobeniusS0 (F n x) (h10Value w x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, MemHs s U (W n) ∧
      Real.sqrt ((fractionalEnergy s U (W n)).toReal) ≤ C := by
  obtain ⟨C, hC, hTrans⟩ := exists_dirichlet_fractional_transposition_bound hAdj hDual hU s p M hs hs₁ hp hM
  refine ⟨C*N, mul_nonneg hC hN, ?_⟩
  filter_upwards [hEq] with n hn
  obtain ⟨L, v, hA, hL, hP, hF, hW, hLift⟩ := hn
  obtain ⟨hHs, hNorm⟩ := hTrans (A n) L hA hL hP (F n) N hF v hLift
  refine ⟨hHs.congr_ae hW, ?_⟩
  rw [← fractionalEnergy_congr_ae hW]
  exact hNorm

end Thesis

end
