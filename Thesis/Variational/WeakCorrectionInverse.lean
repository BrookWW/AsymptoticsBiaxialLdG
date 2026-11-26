module

public import Thesis.Variational.WeakCorrectionPairing

/-! Uniform weak inverse for the actual correction pairing. -/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance weakCorrectionInverseHMinusNormed (U : Set Point) : NormedAddCommGroup (HMinusOne U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance weakCorrectionInverseHMinusSpace (U : Set Point) : NormedSpace ℝ (HMinusOne U) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance weakCorrectionInverseFamilyNorm (U : Set Point) :
    NormedAddCommGroup (H10 U →L[ℝ] HMinusOne U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance weakCorrectionInverseForwardNorm (U : Set Point) :
    NormedAddCommGroup (HMinusOne U →L[ℝ] H10 U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance weakCorrectionInverseCoeffNorm : NormedAddCommGroup ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance weakCorrectionInverseCompleteTensor : CompleteSpace S0 := complete_of_proper

local instance weakCorrectionInverseCompleteH10 (U : Set Point) : CompleteSpace (H10 U) :=
  isClosed_closure.completeSpace_coe

private theorem exists_h10_inverse_of_small_operator
    (U : Set Point) (L : H10 U ≃L[ℝ] HMinusOne U) (Q : H10 U →L[ℝ] HMinusOne U)
    (hQ : ‖L.symm.toContinuousLinearMap‖ * ‖Q‖ < 1 / 2) :
    ∃ K : H10 U ≃L[ℝ] HMinusOne U, K.toContinuousLinearMap = L.toContinuousLinearMap + Q ∧
      ‖K.symm.toContinuousLinearMap‖ ≤ 2 * ‖L.symm.toContinuousLinearMap‖ := by
  exact @exists_uniform_inverse_of_small_continuousLinearMap_perturbation
    (H10 U) (HMinusOne U) inferInstance inferInstance
    (weakCorrectionInverseHMinusNormed U) (weakCorrectionInverseHMinusSpace U)
    (weakCorrectionInverseCompleteH10 U) L Q hQ

private theorem exists_h10_inverse_of_weak_pairing_increment
    (U : Set Point) (L : H10 U ≃L[ℝ] HMinusOne U) (Q : H10 U →L[ℝ] HMinusOne U)
    (B : Point → (S0 × Gradient) →L[ℝ] S0)
    (hRep : ∀ v w : H10 U, L v w + Q v w = weakCorrectionPairing U B v w)
    (hQ : ‖L.symm.toContinuousLinearMap‖ * ‖Q‖ < 1 / 2) :
    ∃ K : H10 U ≃L[ℝ] HMinusOne U, ‖K.symm.toContinuousLinearMap‖ ≤ 2 * ‖L.symm.toContinuousLinearMap‖ ∧
      ∀ v w : H10 U, K v w = weakCorrectionPairing U B v w := by
  have hP := exists_h10_inverse_of_small_operator U L Q hQ
  refine hP.imp ?_
  intro K hK
  refine ⟨hK.2, ?_⟩
  intro v w
  have hAs : K v w = L v w + Q v w :=
    congrArg (fun T : H10 U →L[ℝ] HMinusOne U => T v w) hK.1
  exact hAs.trans (hRep v w)

private theorem exists_small_coefficient_weakCorrection_inverse
    {U : Set Point} (A B : Point → (S0 × Gradient) →L[ℝ] S0)
    (hA : AEStronglyMeasurable A (volume.restrict U)) (hB : AEStronglyMeasurable B (volume.restrict U))
    (M : ℝ) (hM₀ : 0 ≤ M) (hM : ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ M)
    (L : H10 U ≃L[ℝ] HMinusOne U) (hL : ∀ v w : H10 U, L v w = weakCorrectionPairing U A v w)
    (δ : ℝ) (hδ : 0 ≤ δ) (hSub : ∀ᵐ x ∂volume.restrict U, ‖B x - A x‖ ≤ δ)
    (hSmall : ‖L.symm.toContinuousLinearMap‖ * (4 * δ) < 1/2) :
    ∃ K : H10 U ≃L[ℝ] HMinusOne U, ‖K.symm.toContinuousLinearMap‖ ≤ 2 * ‖L.symm.toContinuousLinearMap‖ ∧
      ∀ v w : H10 U, K v w = weakCorrectionPairing U B v w := by
  obtain ⟨Q, hQ, hQEq⟩ := exists_weakCorrectionPairing_coefficient_increment A B hA hB M hM₀ hM δ hδ hSub
  have hSmallQ : ‖L.symm.toContinuousLinearMap‖ * ‖Q‖ < 1/2 :=
    (mul_le_mul_of_nonneg_left hQ (norm_nonneg _)).trans_lt hSmall
  have hRep (v w : H10 U) : L v w + Q v w = weakCorrectionPairing U B v w :=
    (congrArg (· + Q v w) (hL v w)).trans (hQEq v w)
  exact exists_h10_inverse_of_weak_pairing_increment U L Q B hRep hSmallQ

/-- The weak inverse persists for all sufficiently small uniform
perturbations of the actual first-order coefficients. -/
theorem eventually_uniform_inverse_of_weakCorrectionPairing_coefficients
    {U : Set Point} (A : Point → (S0 × Gradient) →L[ℝ] S0)
    (hA : AEStronglyMeasurable A (volume.restrict U))
    (M : ℝ) (hM₀ : 0 ≤ M) (hM : ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ M)
    (hBase : ∃ L : H10 U →ₗ[ℝ] HMinusOne U, Function.Bijective L ∧
      ∀ v w : H10 U, L v w = weakCorrectionPairing U A v w)
    (B : ℕ → Point → (S0 × Gradient) →L[ℝ] S0)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hSmall : ∀ᶠ n in atTop, AEStronglyMeasurable (B n) (volume.restrict U) ∧
      0 ≤ δ n ∧ ∀ᵐ x ∂volume.restrict U, ‖B n x - A x‖ ≤ δ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∃ L : H10 U ≃L[ℝ] HMinusOne U,
      ‖L.symm.toContinuousLinearMap‖ ≤ C ∧ ∀ v w : H10 U, L v w = weakCorrectionPairing U (B n) v w := by
  obtain ⟨L, hL⟩ := exists_continuousEquiv_of_weakCorrectionPairing A hA M hM₀ hM hBase
  let C := 2 * ‖L.symm.toContinuousLinearMap‖
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (norm_nonneg L.symm.toContinuousLinearMap)
  let T : ℝ := ‖L.symm.toContinuousLinearMap‖
  have hδ₁ : Tendsto (fun n => 4 * δ n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hδ.const_mul (4 : ℝ)
  have hδ' : Tendsto (fun n => T * (4 * δ n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hδ₁.const_mul T
  refine ⟨C, hC, ?_⟩
  filter_upwards [hSmall, hδ'.eventually_lt_const (by norm_num : (0 : ℝ) < 1/2)] with n hn hnδ
  exact exists_small_coefficient_weakCorrection_inverse A (B n) hA hn.1 M hM₀ hM L hL (δ n)
    hn.2.1 hn.2.2 hnδ

end Thesis

end
