module

public import Mathlib

/-! Coordinates and basis vectors in Euclidean space. -/

@[expose] public section

set_option autoImplicit false

namespace SupportingAnalysis

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def axis {n : ℕ} (i : Fin n) : E n :=
  EuclideanSpace.single i 1

end SupportingAnalysis
