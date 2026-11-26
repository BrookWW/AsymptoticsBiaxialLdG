module

public import Thesis.Foundation.Frobenius
import HolderToCK.Analysis.Poisson.PotentialRegularityMollification
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Smooth nonexpansive approximations in the actual Frobenius norm. -/

public section

noncomputable section

open HarmonicMaps HolderToCK MeasureTheory Metric Set
open scoped ContDiff Convolution Matrix.Norms.Frobenius NNReal

namespace Thesis

theorem exists_smooth_nonexpansive_approximation {F : S0 → S0} (hF : LipschitzWith 1 F) :
    ∃ G : ℕ → S0 → S0, (∀ n, ContDiff ℝ ∞ (G n)) ∧
      (∀ n, LipschitzWith 1 (G n)) ∧
      ∀ n x, dist (G n x) (F x) ≤ 1 / ((n : ℝ) + 1) := by
  let e := frobeniusCoordinateEquiv
  let f : Domain 5 → Ambient 5 := e ∘ F ∘ e.symm
  have hLf : LipschitzWith 1 f := by
    simpa only [f, mul_one] using e.isometry.lipschitz.comp (hF.comp e.symm.isometry.lipschitz)
  have hcf : Continuous f := hLf.continuous
  have hfHold : HolderBoundOn univ f 1 1 := by
    intro x _ y _
    change ‖f x - f y‖ ≤ 1 * Real.rpow (dist x y) 1
    rw [← dist_eq_norm, Real.rpow_eq_pow, Real.rpow_one]
    simpa only [NNReal.coe_one] using hLf.dist_le_mul x y
  let h := compactDataApproximationScale
  let fₙ (n : ℕ) := compactDataMollification f (h n)
  let G (n : ℕ) : S0 → S0 := e.symm ∘ fₙ n ∘ e
  refine ⟨G, ?_, ?_, ?_⟩
  · intro n
    exact e.symm.contDiff.comp ((compactDataMollification_contDiff hcf (h n)).comp e.contDiff)
  · intro n
    have hHold := compactDataMollification_holderBound (by norm_num : 0 < (1 : ℝ)) zero_le_one hfHold (h n)
    have hLn : LipschitzWith 1 (fₙ n) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      have h' := hHold x (mem_univ _) y (mem_univ _)
      change ‖fₙ n x - fₙ n y‖ ≤ 1 * Real.rpow (dist x y) 1 at h'
      simpa only [← dist_eq_norm, Real.rpow_eq_pow, Real.rpow_one, NNReal.coe_one] using h'
    simpa only [G, mul_one] using e.symm.isometry.lipschitz.comp (hLn.comp e.isometry.lipschitz)
  · intro n x
    have he : F x = e.symm (f (e x)) := by
      change F x = e.symm (e (F (e.symm (e x))))
      rw [e.symm_apply_apply, e.symm_apply_apply]
    rw [he]
    change dist (e.symm (fₙ n (e x))) (e.symm (f (e x))) ≤ _
    rw [e.symm.isometry.dist_eq]
    have hNear := compactDataMollification_dist_le zero_lt_one zero_le_one hfHold (h n) (e x)
    simpa only [fₙ, h, Real.rpow_eq_pow, Real.rpow_one, one_mul, compactDataApproximationScale] using hNear

end Thesis
