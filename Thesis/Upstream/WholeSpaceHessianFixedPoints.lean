module

public import Thesis.Upstream.WholeSpaceHessianAffinePerturbation
public import Thesis.Upstream.WholeSpaceWeakHessianConsistency
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Common fixed points of the real second-derivative perturbations. -/

public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace Thesis

local instance wholeSpaceFixedPointTwo : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance wholeSpaceFixedPointFour : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

theorem hasCompactSupport_real_finsetSum {ι : Type*}
    (s : Finset ι) {f : ι → Point → ℝ} (hf : ∀ j ∈ s, HasCompactSupport (f j)) :
    HasCompactSupport (fun x => ∑ j ∈ s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (HasCompactSupport.zero : HasCompactSupport (0 : Point → ℝ))
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

private theorem lp_eq_toLp_of_ae_eq {p : ℝ≥0∞}
    (z : WholeSpaceScalarLp p) {w : Point → ℝ} (hw : MemLp w p (volume : Measure Point))
    (hz : (z : Point → ℝ) =ᵐ[volume] w) : z = hw.toLp w :=
  Lp.ext (hz.trans hw.coeFn_toLp.symm)

theorem wholeSpaceHessianPair_agree {f : Point → ℝ} (hfc : HasCompactSupport f)
    (z₂ : WholeSpaceScalarLp 2) (z₄ : WholeSpaceScalarLp 4)
    (hz₂ : (z₂ : Point → ℝ) =ᵐ[volume] f) (hz₄ : (z₄ : Point → ℝ) =ᵐ[volume] f)
    (i j : Fin 3)
    (T₂ : WholeSpaceScalarLp 2 →L[ℝ] WholeSpaceScalarLp 2)
    (T₄ : WholeSpaceScalarLp 4 →L[ℝ] WholeSpaceScalarLp 4)
    (hT₂ : ∀ ψ : CompactSmoothScalar,
      T₂ (compactSmoothScalarToLp 2 (compactSmoothScalarLaplace ψ)) =
        compactSmoothScalarToLp 2 (compactSmoothScalarHess i j ψ))
    (hT₄ : ∀ ψ : CompactSmoothScalar,
      T₄ (compactSmoothScalarToLp 4 (compactSmoothScalarLaplace ψ)) =
        compactSmoothScalarToLp 4 (compactSmoothScalarHess i j ψ)) :
    (T₂ z₂ : Point → ℝ) =ᵐ[volume] (T₄ z₄ : Point → ℝ) := by
  have hf₂ := MemLp.ae_eq hz₂ (Lp.memLp z₂)
  have hf₄ := MemLp.ae_eq hz₄ (Lp.memLp z₄)
  rw [lp_eq_toLp_of_ae_eq z₂ hf₂ hz₂,lp_eq_toLp_of_ae_eq z₄ hf₄ hz₄]
  exact wholeSpace_laplacianHessianOperator_consistent_of_compact hfc hf₂ hf₄ i j T₂ T₄ hT₂ hT₄

/-- Compactly supported affine coefficient perturbations with the same
whole-space Hessian action have equal (L²) and (L⁴) fixed-point fields. -/
theorem scalarHessianAffine_fixedPoint_ae_eq
    (a : Fin 3 → Fin 3 → Point → ℝ) (ha : ∀ i j, HasCompactSupport (a i j))
    (f : Point → ℝ) (hfc : HasCompactSupport f)
    (T₂ : Fin 3 → Fin 3 → (WholeSpaceScalarLp 2 →L[ℝ] WholeSpaceScalarLp 2))
    (T₄ : Fin 3 → Fin 3 → (WholeSpaceScalarLp 4 →L[ℝ] WholeSpaceScalarLp 4))
    (hT₂ : ∀ i j, ∀ ψ : CompactSmoothScalar,
      T₂ i j (compactSmoothScalarToLp 2 (compactSmoothScalarLaplace ψ)) =
        compactSmoothScalarToLp 2 (compactSmoothScalarHess i j ψ))
    (hT₄ : ∀ i j, ∀ ψ : CompactSmoothScalar,
      T₄ i j (compactSmoothScalarToLp 4 (compactSmoothScalarLaplace ψ)) =
        compactSmoothScalarToLp 4 (compactSmoothScalarHess i j ψ))
    (P₂ : WholeSpaceScalarLp 2 → WholeSpaceScalarLp 2)
    (P₄ : WholeSpaceScalarLp 4 → WholeSpaceScalarLp 4)
    (hP₂ : ∀ z, (P₂ z : Point → ℝ) =ᵐ[volume] fun x => f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x*T₂ i j z x)
    (hP₄ : ∀ z, (P₄ z : Point → ℝ) =ᵐ[volume] fun x => f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x*T₄ i j z x)
    {k₂ k₄ : ℝ≥0} (hc₂ : ContractingWith k₂ P₂) (hc₄ : ContractingWith k₄ P₄) :
    ((ContractingWith.fixedPoint P₂ hc₂ : WholeSpaceScalarLp 2) : Point → ℝ) =ᵐ[volume]
      ((ContractingWith.fixedPoint P₄ hc₄ : WholeSpaceScalarLp 4) : Point → ℝ) := by
  let z₂ (n : ℕ) := P₂^[n] 0
  let z₄ (n : ℕ) := P₄^[n] 0
  let w : ℕ → Point → ℝ
    | 0 => 0
    | n+1 => fun x => f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x*T₂ i j (z₂ n) x
  have hw (n : ℕ) : HasCompactSupport (w n) := by
    cases n with
    | zero => exact HasCompactSupport.zero
    | succ n =>
      exact hfc.add (hasCompactSupport_real_finsetSum Finset.univ (fun i _ =>
        hasCompactSupport_real_finsetSum Finset.univ (fun j _ => (ha i j).mul_right)))
  have h₂ (n : ℕ) : (z₂ n : Point → ℝ) =ᵐ[volume] w n := by
    cases n with
    | zero => exact Lp.coeFn_zero ℝ 2 volume
    | succ n =>
      change (P₂^[n+1] 0 : Point → ℝ) =ᵐ[volume] w (n+1)
      rw [iterate_succ_apply']
      exact hP₂ (z₂ n)
  have h₄ (n : ℕ) : (z₄ n : Point → ℝ) =ᵐ[volume] w n := by
    induction n with
    | zero => exact Lp.coeFn_zero ℝ 4 volume
    | succ n ih =>
      change (P₄^[n+1] 0 : Point → ℝ) =ᵐ[volume] w (n+1)
      rw [iterate_succ_apply']
      refine (hP₄ (z₄ n)).trans ?_
      have hC (i j : Fin 3) : (T₂ i j (z₂ n) : Point → ℝ) =ᵐ[volume] (T₄ i j (z₄ n) : Point → ℝ) :=
        wholeSpaceHessianPair_agree (hw n) (z₂ n) (z₄ n) (h₂ n) ih i j _ _ (hT₂ i j) (hT₄ i j)
      filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hC i))] with x hx
      change f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x*T₄ i j (z₄ n) x =
        f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x*T₂ i j (z₂ n) x
      simp only [hx]
  apply tendstoInMeasure_ae_unique
    (TendstoInMeasure.congr_left h₂ (tendstoInMeasure_of_tendsto_Lp (hc₂.tendsto_iterate_fixedPoint 0)))
    (TendstoInMeasure.congr_left h₄ (tendstoInMeasure_of_tendsto_Lp (hc₄.tendsto_iterate_fixedPoint 0)))

end Thesis
