module

public import Thesis.Variational.FirstCorrectionOperator
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units

/-! Uniform inverse bounds for the weak linearized equation. -/

public section

open Filter Function Topology
open scoped ContDiff Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

/-- A perturbation whose composition with the original inverse has norm
less than one half is bijective and has a uniformly bounded inverse. -/
theorem exists_uniform_inverse_of_small_continuousLinearMap_perturbation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E]
    (L : E ≃L[ℝ] F) (B : E →L[ℝ] F)
    (hB : ‖L.symm.toContinuousLinearMap‖ * ‖B‖ < 1 / 2) :
    ∃ P : E ≃L[ℝ] F, P.toContinuousLinearMap = L.toContinuousLinearMap + B ∧
      ‖P.symm.toContinuousLinearMap‖ ≤ 2 * ‖L.symm.toContinuousLinearMap‖ := by
  let A := L.symm.toContinuousLinearMap.comp B
  have hA : ‖A‖ < 1 / 2 := (ContinuousLinearMap.opNorm_comp_le _ _).trans_lt hB
  let T := -A
  have hT : ‖T‖ < 1 := by dsimp only [T]; rw [norm_neg]; exact hA.trans (by norm_num)
  let V := ContinuousLinearEquiv.ofUnit (Units.oneSub T hT)
  let P := V.trans L
  have hV : V.toContinuousLinearMap = (1 : E →L[ℝ] E) + A := by
    change (↑(Units.oneSub T hT) : E →L[ℝ] E) = _
    rw [Units.val_oneSub]
    exact sub_neg_eq_add _ _
  have hP : P.toContinuousLinearMap = L.toContinuousLinearMap + B := by
    apply ContinuousLinearMap.ext
    intro x
    have h := DFunLike.congr_fun hV x
    change L (V x) = L x + B x
    change V x = x + L.symm (B x) at h
    rw [h, map_add, L.apply_symm_apply]
  refine ⟨P, hP, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (norm_nonneg _))
  intro y
  let z := P.symm y
  have hy : L z + B z = y := (DFunLike.congr_fun hP z).symm.trans (P.apply_symm_apply y)
  have hZ : z = L.symm y - L.symm (B z) := by
    have h := congrArg L.symm hy
    rw [map_add, L.symm_apply_apply] at h
    rw [← h]
    exact (add_sub_cancel_right _ _).symm
  have hzA : ‖L.symm (B z)‖ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖B‖ * ‖z‖ := by
    exact (ContinuousLinearMap.le_opNorm L.symm.toContinuousLinearMap (B z)).trans
      ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm B z) (norm_nonneg _)).trans_eq
        (mul_assoc _ _ _).symm)
  have hzL : ‖L.symm y‖ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖y‖ :=
    ContinuousLinearMap.le_opNorm L.symm.toContinuousLinearMap y
  have hz := (congrArg norm hZ).le.trans (norm_sub_le _ _)
  have hHalf := mul_le_mul_of_nonneg_right hB.le (norm_nonneg z)
  change ‖z‖ ≤ (2 * ‖L.symm.toContinuousLinearMap‖) * ‖y‖
  nlinarith only [hz, hzA, hzL, hHalf]

/-- One bounded inverse suffices for every sufficiently small perturbation
along a sequence of weak operators. -/
theorem eventually_uniform_inverse_of_tendsto_zero_weak_perturbation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E]
    (L : E ≃L[ℝ] F) (B : ℕ → E →L[ℝ] F)
    (hB : Tendsto (fun n => ‖B n‖) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∃ P : E ≃L[ℝ] F, P.toContinuousLinearMap = L.toContinuousLinearMap + B n ∧
      ‖P.symm.toContinuousLinearMap‖ ≤ 2 * ‖L.symm.toContinuousLinearMap‖ := by
  have h := hB.const_mul ‖L.symm.toContinuousLinearMap‖
  rw [mul_zero] at h
  exact (h.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)).mono
    fun n hn => exists_uniform_inverse_of_small_continuousLinearMap_perturbation L (B n) hn

end Thesis

end
