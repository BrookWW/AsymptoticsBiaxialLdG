module

public import Thesis.Foundation.QuaternionFrameMetric
public import HarmonicMaps.Sobolev
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Euclidean-valued absolute continuity and its weak integration identity. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace Thesis

private theorem ae_differentiableAt_ambient_of_ac {q : ℕ} {f : ℝ → Ambient q} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) : ∀ᵐ t, t ∈ uIcc a b → DifferentiableAt ℝ f t := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q => ℝ)
  let d (i : Fin q) : Ambient q →L[ℝ] ℝ := EuclideanSpace.proj i
  have hcoord (i : Fin q) : AbsolutelyContinuousOnInterval (fun t => d i (f t)) a b :=
    ac_comp_lipschitzOn hf (d i).lipschitz.lipschitzOnWith (mapsTo_univ _ _)
  filter_upwards [ae_all_iff.mpr fun i => (hcoord i).ae_differentiableAt] with t ht
  intro hmem
  have hDiff : DifferentiableAt ℝ (fun t => e (f t)) t := differentiableAt_pi.mpr fun i => ht i hmem
  have h := e.symm.toContinuousLinearMap.differentiableAt.comp t hDiff
  have hfun : (⇑e.symm ∘ fun t => e (f t)) = f := funext fun t => e.symm_apply_apply (f t)
  change DifferentiableAt ℝ (⇑e.symm ∘ fun t => e (f t)) t at h
  rwa [hfun] at h

/-- Integration by parts for an absolutely continuous Euclidean-valued map
with equal endpoint products. -/
theorem absolutelyContinuous_integral_parts {q : ℕ} {f : ℝ → Ambient q}
    {a b : ℝ} (hab : a < b) (hf : AbsolutelyContinuousOnInterval f a b)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hEndProd : ψ a • f a = ψ b • f b) :
    let B : ℝ → Ambient q := fun t => deriv ψ t • f t + ψ t • deriv f t
    Integrable B (volume.restrict (Ioo a b)) ∧ (∫ t, B t ∂(volume.restrict (Ioo a b))) = 0 := by
  intro B
  have hψAC : AbsolutelyContinuousOnInterval ψ a b :=
    hψ.contDiffOn.absolutelyContinuousOnInterval
  have hCoords (i : Fin q) : Integrable (fun t => B t i) (volume.restrict (Ioo a b)) ∧
      (∫ t, B t i ∂(volume.restrict (Ioo a b))) = 0 := by
    let d : Ambient q →L[ℝ] ℝ := EuclideanSpace.proj i
    let g (t : ℝ) := ψ t * d (f t)
    have hD : AbsolutelyContinuousOnInterval (d ∘ f) a b :=
      ac_comp_lipschitzOn hf d.lipschitz.lipschitzOnWith (mapsTo_univ _ _)
    have hAC : AbsolutelyContinuousOnInterval g a b := hψAC.mul hD
    have hDEq : (fun t => B t i) =ᵐ[(volume.restrict (Ioo a b))] deriv g := by
      filter_upwards [ae_restrict_of_ae (ae_differentiableAt_ambient_of_ac hf),
        ae_restrict_mem (μ := volume) measurableSet_Ioo] with t ht hmem
      have hmem' : t ∈ uIcc a b := by
        rw [uIcc_of_le hab.le]
        exact Ioo_subset_Icc_self hmem
      have hFd : HasDerivAt (fun s => d (f s)) (d (deriv f t)) t :=
        d.hasFDerivAt.comp_hasDerivAt t (ht hmem').hasDerivAt
      have hG := (hψ.differentiable (by simp) t).hasDerivAt.mul hFd
      change deriv ψ t * d (f t) + ψ t * d (deriv f t) = deriv g t
      exact hG.deriv.symm
    refine ⟨(hAC.intervalIntegrable_deriv.1.mono_set Ioo_subset_Ioc_self).congr hDEq.symm, ?_⟩
    have hEnd : g b = g a := by
      have h := congrArg (fun x : Ambient q => d x) hEndProd.symm
      simpa only [g, map_smul, smul_eq_mul] using h
    rw [integral_congr_ae hDEq]
    change (∫ t in Ioo a b, deriv g t) = 0
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le,
      hAC.integral_deriv_eq_sub, hEnd, sub_self]
  have hI (i : Fin q) : Integrable (fun t => B t i) (volume.restrict (Ioo a b)) := (hCoords i).1
  refine ⟨Integrable.of_eval_piLp hI, ?_⟩
  ext i
  exact (eval_integral_piLp hI i).trans (hCoords i).2

end Thesis

end
