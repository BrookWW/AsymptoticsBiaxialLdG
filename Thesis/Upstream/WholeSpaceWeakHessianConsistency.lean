module

public import Thesis.Upstream.JointLaplacianTestApproximation
public import Thesis.Upstream.WholeSpaceWeakHessianOperator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! The two Hessian extensions agree on common compactly supported forces. -/

public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace Thesis

local instance wholeSpaceHessianAgreementTwo : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance wholeSpaceHessianAgreementFour : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

private theorem compactSmoothScalarHessian_convergesInMeasure {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {f : Point → ℝ} (hf : MemLp f p (volume : Measure Point))
    {φ : ℕ → CompactSmoothScalar}
    (h : Tendsto (fun n => eLpNorm (laplacian (φ n).val-f) p volume) atTop (𝓝 0))
    (i j : Fin 3) (T : Lp ℝ p volume →L[ℝ] Lp ℝ p volume)
    (hT : ∀ ψ : CompactSmoothScalar,
      T (compactSmoothScalarToLp p (compactSmoothScalarLaplace ψ)) =
        compactSmoothScalarToLp p (compactSmoothScalarHess i j ψ)) :
    TendstoInMeasure volume (fun n => (compactSmoothScalarHess i j (φ n)).val) atTop (T (hf.toLp f)) := by
  let L (n : ℕ) := compactSmoothScalarToLp p (compactSmoothScalarLaplace (φ n))
  have hA : Tendsto L atTop (𝓝 (hf.toLp f)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ hf).2
    refine h.congr (fun n => ?_)
    apply eLpNorm_congr_ae
    have he : (L n : Point → ℝ) =ᵐ[volume] laplacian (φ n).val :=
      (compactSmoothScalarToLp_ae p (compactSmoothScalarLaplace (φ n))).trans
        (EventuallyEq.of_eq (compactSmoothScalarLaplace_val (φ n)))
    exact he.symm.sub EventuallyEq.rfl
  have hB : Tendsto (fun n => T (L n)) atTop (𝓝 (T (hf.toLp f))) :=
    (T.continuous.tendsto _).comp hA
  refine TendstoInMeasure.congr_left (fun n => ?_) (tendstoInMeasure_of_tendsto_Lp hB)
  change (T (compactSmoothScalarToLp p (compactSmoothScalarLaplace (φ n))) : Point → ℝ)
    =ᵐ[volume] (compactSmoothScalarHess i j (φ n)).val
  rw [hT]
  exact compactSmoothScalarToLp_ae p _

/-- Extensions with the exact compact-test Hessian values have the same
representative on a compact force belonging to both (L²) and (L⁴). -/
theorem wholeSpace_laplacianHessianOperator_consistent_of_compact {f : Point → ℝ}
    (hfc : HasCompactSupport f) (hf₂ : MemLp f 2 (volume : Measure Point)) (hf₄ : MemLp f 4 volume)
    (i j : Fin 3)
    (T₂ : Lp ℝ 2 (volume : Measure Point) →L[ℝ] Lp ℝ 2 volume)
    (T₄ : Lp ℝ 4 (volume : Measure Point) →L[ℝ] Lp ℝ 4 volume)
    (hT₂ : ∀ ψ : CompactSmoothScalar,
      T₂ (compactSmoothScalarToLp 2 (compactSmoothScalarLaplace ψ)) =
        compactSmoothScalarToLp 2 (compactSmoothScalarHess i j ψ))
    (hT₄ : ∀ ψ : CompactSmoothScalar,
      T₄ (compactSmoothScalarToLp 4 (compactSmoothScalarLaplace ψ)) =
        compactSmoothScalarToLp 4 (compactSmoothScalarHess i j ψ)) :
    (T₂ (hf₂.toLp f) : Point → ℝ) =ᵐ[volume] (T₄ (hf₄.toLp f) : Point → ℝ) := by
  obtain ⟨v,hv,h₂,h₄⟩ := exists_joint_compactSmooth_laplacian_test_approximation hfc hf₄
  let φ (n : ℕ) : CompactSmoothScalar := ⟨v n,hv n⟩
  exact tendstoInMeasure_ae_unique
    (compactSmoothScalarHessian_convergesInMeasure (φ := φ) hf₂ h₂ i j T₂ hT₂)
    (compactSmoothScalarHessian_convergesInMeasure (φ := φ) hf₄ h₄ i j T₄ hT₄)

end Thesis
