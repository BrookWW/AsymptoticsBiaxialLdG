module

public import Thesis.Variational.DirichletPoissonInverse
import Thesis.Variational.H10Poincare
import Mathlib.MeasureTheory.Function.L2Space

/-! An energy estimate for the pure weak Dirichlet problem. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Frobenius RealInnerProductSpace

namespace Thesis

local instance dirichletPoissonEnergyL2Fact : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

private theorem abs_setIntegral_frobenius_le_L2 {U : Set Point}
    (u v : Lp S0 2 (volume.restrict U)) :
    |∫ x in U, frobeniusS0 (u x) (v x)| ≤ ‖u‖*‖v‖ := by
  let μ := (volume : Measure Point).restrict U
  let fu (x : Point) := frobeniusCoordinateEquiv (u x)
  let fv (x : Point) := frobeniusCoordinateEquiv (v x)
  have hu : MemLp fu 2 μ := (frobeniusCoordinateEquiv_memLp_iff μ 2 u).2 (Lp.memLp u)
  have hv : MemLp fv 2 μ := (frobeniusCoordinateEquiv_memLp_iff μ 2 v).2 (Lp.memLp v)
  let A := hu.toLp fu
  let B := hv.toLp fv
  have hInt : inner ℝ A B = ∫ x in U, frobeniusS0 (u x) (v x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp,hv.coeFn_toLp] with x hx hy
    rw [hx,hy]
    exact frobeniusCoordinateEquiv_inner (u x) (v x)
  have hA : ‖A‖ = ‖u‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae
      (Eventually.of_forall fun x => frobeniusCoordinateEquiv.norm_map (u x)))
  have hB : ‖B‖ = ‖v‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae
      (Eventually.of_forall fun x => frobeniusCoordinateEquiv.norm_map (v x)))
  simpa only [hInt,hA,hB] using abs_real_inner_le_norm A B

/-- Testing the pure weak Dirichlet equation with the solution controls
the full gradient energy by the force and the domain Poincaré constant. -/
theorem exists_H10_dirichletPoisson_gradientBound {U : Set Point}
    (hU : MeasurableSet U) (hBound : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (w : H10 U) (g : Lp S0 2 (volume.restrict U)),
        (∀ v : H10 U,
          h10PrincipalPart U w v = ∫ x in U, frobeniusS0 (g x) (h10Value v x)) →
        ‖h10GradientCoordinates U w‖ ≤ C*‖g‖ := by
  obtain ⟨C,hC,hP⟩ := exists_H10_value_poincare hU hBound
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  refine ⟨C,hC₀,?_⟩
  intro w g hEq
  let z := h10GradientCoordinates U w
  have hWeak := hEq w
  rw [h10PrincipalPart_eq_neg_gradientCoordinate_inner,real_inner_self_eq_norm_sq] at hWeak
  have hSquare : ‖z‖^2 ≤ (C*‖g‖)*‖z‖ := by
    calc
      _ = |∫ x in U, frobeniusS0 (g x) (h10Value w x)| := by
        rw [← hWeak,abs_neg,abs_of_nonneg (sq_nonneg _)]
      _ ≤ ‖g‖*‖w.val.1‖ := abs_setIntegral_frobenius_le_L2 g w.val.1
      _ ≤ ‖g‖*(C*‖z‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [norm_h10GradientCoordinates_eq]
        exact hP w
      _ = _ := by ring
  by_cases hz : z = 0
  · change ‖z‖ ≤ _
    rw [hz,norm_zero]
    positivity
  · exact le_of_mul_le_mul_right (by simpa only [pow_two] using hSquare) (norm_pos_iff.mpr hz)

end Thesis
