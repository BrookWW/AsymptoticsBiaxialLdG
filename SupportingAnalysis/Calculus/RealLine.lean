module

public import SupportingAnalysis.Euclidean

/-! The isometric Lebesgue coordinate on the one-dimensional Euclidean space. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace SupportingAnalysis

/-- Read the single Euclidean coordinate by a real linear isometry. -/
noncomputable def realLineEuclideanIso : E 1 ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv :=
    (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).trans (LinearEquiv.funUnique (Fin 1) ℝ ℝ)
  norm_map' x := by
    change ‖x (default : Fin 1)‖ = ‖x‖
    rw [PiLp.norm_eq_of_L2, Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)]

theorem realLineEuclideanIso_apply (x : E 1) : realLineEuclideanIso x = x 0 := rfl

theorem realLineEuclideanIso_symm_apply (t : ℝ) :
    realLineEuclideanIso.symm t = EuclideanSpace.single (0 : Fin 1) t := by
  apply realLineEuclideanIso.injective
  rw [LinearIsometryEquiv.apply_symm_apply, realLineEuclideanIso_apply]
  simp only [EuclideanSpace.single, PiLp.single_apply, ↓reduceIte]

theorem realLineEuclideanIso_axis (i : Fin 1) : realLineEuclideanIso (axis i) = 1 := by
  rw [Fin.fin_one_eq_zero i, axis, ← realLineEuclideanIso_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem realLineEuclideanIso_norm (x : E 1) : |realLineEuclideanIso x| = ‖x‖ :=
  realLineEuclideanIso.norm_map x

end SupportingAnalysis
