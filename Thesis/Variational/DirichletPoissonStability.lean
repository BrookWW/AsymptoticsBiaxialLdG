module

public import Thesis.Variational.DirichletPoissonInverse
public import Thesis.Foundation.FrobeniusInnerProduct
import Thesis.Variational.H10WeakGreen
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Strong stability of the actual pure Dirichlet inverse for square
integrable forcing. -/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix.Norms.Frobenius

namespace Thesis

local instance dirichletStabilityFrobenius : InnerProductSpace ℝ S0 := frobeniusInnerProductSpace

local instance dirichletStabilityDualNormed (U : Set Point) : NormedAddCommGroup (HMinusOne U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance dirichletStabilityDualSpace (U : Set Point) : NormedSpace ℝ (HMinusOne U) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

private theorem norm_h10_forcingFunctional_le {U : Set Point} {f : Point → S0}
    (hf : MemLp f 2 (volume.restrict U)) (F : HMinusOne U)
    (hEq : ∀ v : H10 U, F v = ∫ x in U, frobeniusS0 (f x) (h10Value v x)) :
    ‖F‖ ≤ (eLpNorm f 2 (volume.restrict U)).toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
  intro v
  let Q := hf.toLp f
  have h : F v = inner ℝ Q v.val.1 := by
    rw [hEq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx,frobenius_inner_eq]
    rfl
  rw [h,Real.norm_eq_abs,← Lp.norm_toLp f hf]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (le_max_left ‖v.val.1‖ ‖v.val.2‖) (norm_nonneg _))

private theorem h10PrincipalPart_sub_pairing {U : Set Point} {u v : H10 U} {f g : Point → S0}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hu : ∀ z : H10 U, h10PrincipalPart U u z = ∫ x in U, frobeniusS0 (f x) (h10Value z x))
    (hv : ∀ z : H10 U, h10PrincipalPart U v z = ∫ x in U, frobeniusS0 (g x) (h10Value z x)) :
    ∀ z : H10 U, h10PrincipalPart U (u-v) z = ∫ x in U, frobeniusS0 ((f-g) x) (h10Value z x) := by
  intro z
  have hi : Integrable (fun x => frobeniusS0 (f x) (h10Value z x)) (volume.restrict U) :=
    integrable_frobenius_of_memLp hf (Lp.memLp z.val.1)
  have hj : Integrable (fun x => frobeniusS0 (g x) (h10Value z x)) (volume.restrict U) :=
    integrable_frobenius_of_memLp hg (Lp.memLp z.val.1)
  rw [map_sub,sub_apply,hu,hv,← integral_sub hi hj]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [Pi.sub_apply,← frobenius_inner_eq,inner_sub_left]

/-- Strong convergence of the forcing in the actual L² norm gives strong
convergence in the full H¹₀ graph of the corresponding pure weak solutions. -/
theorem tendsto_h10_of_dirichletPoisson_L2 {U : Set Point} (hU : IsBoundedDomain U)
    {u : ℕ → H10 U} {v : H10 U} {f : ℕ → Point → S0} {g : Point → S0}
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hUeq : ∀ n z, h10PrincipalPart U (u n) z = ∫ x in U, frobeniusS0 (f n x) (h10Value z x))
    (hVeq : ∀ z, h10PrincipalPart U v z = ∫ x in U, frobeniusS0 (g x) (h10Value z x))
    (hLim : Tendsto (fun n => eLpNorm (f n-g) 2 (volume.restrict U)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 v) := by
  obtain ⟨E,hE⟩ := exists_H10_dirichletPoissonEquiv hU.1.measurableSet hU.2.2
  have hNorm (n : ℕ) : ‖E (u n-v)‖ ≤ (eLpNorm (f n-g) 2 (volume.restrict U)).toReal := by
    rw [hE]
    exact norm_h10_forcingFunctional_le ((hf n).sub hg) _
      (h10PrincipalPart_sub_pairing (hf n) hg (hUeq n) hVeq)
  have hReal : Tendsto (fun n => (eLpNorm (f n-g) 2 (volume.restrict U)).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hLim
    rw [ENNReal.toReal_zero] at h
    exact h
  have hZeroNorm : Tendsto (fun n => ‖E (u n-v)‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hReal (fun _ => norm_nonneg _) hNorm
  have hZero : Tendsto (fun n => E (u n-v)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 hZeroNorm
  have hDiff : Tendsto (fun n => u n-v) atTop (𝓝 0) := by
    have h := E.symm.continuous.continuousAt.tendsto.comp hZero
    rw [map_zero] at h
    exact h.congr (fun n => E.symm_apply_apply (u n-v))
  simpa only [sub_add_cancel,zero_add] using hDiff.add_const v

end Thesis
