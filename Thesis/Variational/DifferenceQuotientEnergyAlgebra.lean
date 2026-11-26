module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Pointwise Young estimates for the elliptic cutoff difference identity. -/

public section

noncomputable section

open scoped RealInnerProductSpace

namespace Thesis

/-- Young's inequality with the parameter multiplying the first square. -/
theorem mul_le_young_sq (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    a*b ≤ t*a^2 + (4*t)⁻¹*b^2 := by
  have h4 : 0 < 4*t := by positivity
  apply (mul_le_mul_iff_of_pos_left h4).mp
  have hR : (4*t)*((4*t)⁻¹*b^2) = b^2 := by rw [← mul_assoc,mul_inv_cancel₀ h4.ne',one_mul]
  rw [mul_add,hR]
  nlinarith only [sq_nonneg (2*t*a-b)]

private theorem abs_inner_operator_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (x y : E) {R : ℝ} (hR : ‖A‖ ≤ R) :
    |inner ℝ (A x) y| ≤ (R*‖x‖)*‖y‖ :=
  (abs_real_inner_le_norm (A x) y).trans
    (mul_le_mul_of_nonneg_right ((A.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hR (norm_nonneg x))) (norm_nonneg y))

/-- After expanding the cutoff test, the leading elliptic term absorbs the
two cross terms in its gradient difference. -/
theorem half_coercivity_le_cutoff_pairing {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B : E →L[ℝ] E) (x t d : E) (χ ell M L : ℝ)
    (hell : 0 < ell) (hχ : |χ| ≤ 1) (hM : ‖A‖ ≤ M) (hL : ‖B‖ ≤ L)
    (hEll : ell*‖x‖^2 ≤ inner ℝ (A x) x) :
    (ell/2)*‖x‖^2 ≤
      inner ℝ (A x + χ • B d) (x+t) +
        (L^2/ell+1/2)*‖d‖^2 + (M^2/ell+L^2/2)*‖t‖^2 := by
  have hAT : -(M*‖t‖)*‖x‖ ≤ inner ℝ (A x) t := by
    calc
      _ = -((M*‖x‖)*‖t‖) := by ring
      _ ≤ -|inner ℝ (A x) t| := neg_le_neg (abs_inner_operator_le A x t hM)
      _ ≤ _ := neg_abs_le _
  have hBD (y : E) : -(L*‖d‖)*‖y‖ ≤ inner ℝ (χ • B d) y := by
    apply (le_trans (b := -|inner ℝ (χ • B d) y|) ?_ (neg_abs_le _))
    rw [show -(L*‖d‖)*‖y‖ = -((L*‖d‖)*‖y‖) by ring]
    apply neg_le_neg
    rw [real_inner_smul_left,abs_mul]
    exact (mul_le_mul_of_nonneg_right hχ (abs_nonneg _)).trans
      ((one_mul _).le.trans (abs_inner_operator_le B d y hL))
  have hPos : 0 < ell/4 := by positivity
  have hY (a b : ℝ) : a*b ≤ (ell/4)*a^2 + b^2/ell := by
    have h := mul_le_young_sq a b hPos
    rw [show 4*(ell/4) = ell by ring, mul_comm (ell⁻¹), ← div_eq_mul_inv] at h
    exact h
  have hYAT : M*‖t‖*‖x‖ ≤ (ell/4)*‖x‖^2 + (M^2/ell)*‖t‖^2 := by
    calc
      _ = ‖x‖*(M*‖t‖) := by ring
      _ ≤ (ell/4)*‖x‖^2 + (M*‖t‖)^2/ell := hY _ _
      _ = _ := by rw [mul_pow,div_eq_mul_inv,div_eq_mul_inv]; ring
  have hYBX : L*‖d‖*‖x‖ ≤ (ell/4)*‖x‖^2 + (L^2/ell)*‖d‖^2 := by
    calc
      _ = ‖x‖*(L*‖d‖) := by ring
      _ ≤ (ell/4)*‖x‖^2 + (L*‖d‖)^2/ell := hY _ _
      _ = _ := by rw [mul_pow,div_eq_mul_inv,div_eq_mul_inv]; ring
  have hYBT : L*‖d‖*‖t‖ ≤ (1/2)*‖d‖^2 + (L^2/2)*‖t‖^2 := by
    have h := sq_nonneg (‖d‖ - L*‖t‖)
    nlinarith only [h]
  rw [inner_add_left,inner_add_right,inner_add_right]
  linarith only [hEll,hAT,hBD x,hBD t,hYAT,hYBX,hYBT]

end Thesis
