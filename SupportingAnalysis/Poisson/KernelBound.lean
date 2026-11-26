module

public import SupportingAnalysis.Poisson.Smoothing
import SupportingAnalysis.Poisson.WeakBound

/-! The dimension-dependent weak bound for compact cutoff Hessian kernels. -/

public section

open MeasureTheory
open scoped ContDiff Convolution ENNReal

set_option autoImplicit false

namespace SupportingAnalysis

/-- The weak Hessian convolution estimate in every dimension. -/
theorem kernelWeakHessian (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (cutoff g : E d → ℝ), ContDiff ℝ ∞ cutoff → HasCompactSupport cutoff →
        Integrable g → ∀ (i j : Fin d) (ell : ℝ), 0 < ell →
          volume {x : E d | ell < |((fun y => scalarHessian cutoff y i j)
            ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x|} ≤
            ENNReal.ofReal (C * ((∫ x, |laplacian cutoff x|) * (∫ x, |g x|)) / ell) := by
  by_cases hd : 2 ≤ d
  · obtain ⟨C, hC, hWeak⟩ := measure_scalarHessian_superlevel_le_laplacian d hd
    refine ⟨C, hC, fun cutoff g hcutoff hcompact hg i j ell hell => ?_⟩
    have h := kernelWeakHessian_of_compact_laplacian_bound hC hWeak cutoff hcutoff hcompact i j
    simpa only [mul_assoc] using (h g hg).2 ell hell
  have hd' : d = 0 ∨ d = 1 := by omega
  rcases hd' with rfl | rfl
  · exact ⟨1, zero_le_one, fun _ _ _ _ _ i => Fin.elim0 i⟩
  · refine ⟨1, zero_le_one, fun cutoff g hcutoff hcompact hg i j ell hell => ?_⟩
    simpa only [one_mul] using kernelWeakHessian_one hcutoff hcompact hg i j hell

end SupportingAnalysis
