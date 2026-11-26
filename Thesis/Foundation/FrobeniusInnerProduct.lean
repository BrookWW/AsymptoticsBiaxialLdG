module

public import Thesis.Foundation.Frobenius

/-! A Hilbert structure for the existing Frobenius norm on the tensor space. -/

@[expose] public section

noncomputable section

open scoped Matrix.Norms.Frobenius

namespace Thesis

/-- The real inner product with the original Frobenius norm and scalar action. -/
@[reducible] def frobeniusInnerProductSpace : InnerProductSpace ℝ S0 where
  toNormedSpace := inferInstance
  inner x y := inner ℝ (frobeniusCoordinateEquiv x) (frobeniusCoordinateEquiv y)
  norm_sq_eq_re_inner := by
    intro x
    change ‖x‖ ^ 2 = inner ℝ (frobeniusCoordinateEquiv x) (frobeniusCoordinateEquiv x)
    rw [real_inner_self_eq_norm_sq, frobeniusCoordinateEquiv.norm_map]
  conj_inner_symm x y := inner_conj_symm _ _
  add_left x y z := by
    change inner ℝ (frobeniusCoordinateEquiv (x + y)) (frobeniusCoordinateEquiv z) = _
    rw [map_add, inner_add_left]
  smul_left x y c := by
    change inner ℝ (frobeniusCoordinateEquiv (c • x)) (frobeniusCoordinateEquiv y) = _
    rw [map_smul, inner_smul_left]

local instance : InnerProductSpace ℝ S0 := frobeniusInnerProductSpace

theorem frobenius_inner_eq (x y : S0) : inner ℝ x y = frobeniusS0 x y :=
  frobeniusCoordinateEquiv_inner x y

end Thesis
