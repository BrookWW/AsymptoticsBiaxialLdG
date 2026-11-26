module

public import Thesis.Variational.SecondDerivativeCalculus
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Continuous derivative columns determine the actual smoothness on a convex closure. -/

public section

noncomputable section

open Filter Function Set Topology
open scoped ContDiff

namespace Thesis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private def derivativeFromColumns (D : Fin 3 → F) : Point →L[ℝ] F :=
  ∑ i, (EuclideanSpace.proj i).smulRight (D i)

private theorem derivativeFromColumns_axis (D : Fin 3 → F) (j : Fin 3) :
    derivativeFromColumns D (axis j) = D j := by
  simp only [derivativeFromColumns,sum_apply,ContinuousLinearMap.smulRight_apply]
  change (∑ i : Fin 3, axis j i • D i) = D j
  simp only [axis,PiLp.single_apply,ite_smul,one_smul,zero_smul,
    Finset.sum_ite_eq',if_pos (Finset.mem_univ j)]

private theorem linearMap_ext_axis {L M : Point →L[ℝ] F} (h : ∀ j, L (axis j) = M (axis j)) :
    L = M := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : (∑ i : Fin 3, v i • axis i) = v := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,axis] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  rw [← hv,map_sum,map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul,map_smul,h]

theorem uniqueDiffOn_closure_of_open_convex {S : Set Point}
    (hS : IsOpen S) (hConv : Convex ℝ S) (hNe : S.Nonempty) :
    UniqueDiffOn ℝ (closure S) := by
  obtain ⟨x,hx⟩ := hNe
  refine uniqueDiffOn_convex hConv.closure ⟨x,mem_interior_iff_mem_nhds.mpr ?_⟩
  exact mem_of_superset (hS.mem_nhds hx) subset_closure

/-- If the actual interior derivative columns extend with order (k), their
continuous extension is the actual within derivative and the function has
order (k+1) on the closed convex patch. -/
theorem contDiffOn_succ_of_closed_convex_derivative_columns {S : Set Point}
    (hS : IsOpen S) (hConv : Convex ℝ S) (hNe : S.Nonempty)
    (k : ℕ) {f : Point → F} (hf : ContinuousOn f (closure S))
    (hfI : DifferentiableOn ℝ f S)
    (G : Fin 3 → Point → F)
    (hG : ∀ i, ContDiffOn ℝ (k : ℕ∞ω) (G i) (closure S))
    (he : ∀ i, EqOn (G i) (coordDeriv i f) S) :
    ContDiffOn ℝ (↑(k+1) : ℕ∞ω) f (closure S) ∧
      ∀ i, EqOn (fun x => fderivWithin ℝ f (closure S) x (axis i)) (G i) (closure S) := by
  let D : Point → Point →L[ℝ] F := fun x => derivativeFromColumns (fun i => G i x)
  have hD : ContDiffOn ℝ (k : ℕ∞ω) D (closure S) := by
    change ContDiffOn ℝ (k : ℕ∞ω)
      (fun x => ∑ i : Fin 3, (EuclideanSpace.proj i).smulRight (G i x)) (closure S)
    apply ContDiffOn.sum
    intro i _
    let L : F →L[ℝ] Point →L[ℝ] F :=
      ContinuousLinearMap.smulRightL ℝ Point F (EuclideanSpace.proj i)
    exact L.contDiff.comp_contDiffOn (hG i)
  have heD : EqOn D (fderiv ℝ f) S := by
    intro x hx
    apply linearMap_ext_axis
    intro i
    exact (derivativeFromColumns_axis (fun j => G j x) i).trans (he i hx)
  have hDer (x : Point) (hx : x ∈ closure S) : HasFDerivWithinAt f (D x) (closure S) x := by
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv hfI hConv hS
      (fun y hy => (hf y hy).mono subset_closure)
    have ht := ((hD.continuousOn x hx).mono subset_closure).tendsto
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact heD hy
  have hUd := uniqueDiffOn_closure_of_open_convex hS hConv hNe
  have hFinite : (k : ℕ∞ω) ≠ ω := by
    change ((↑(k : ℕ∞)) : ℕ∞ω) ≠ ⊤
    exact WithTop.coe_ne_top
  have hAll : ContDiffOn ℝ ((k : ℕ∞ω)+1) f (closure S) :=
    (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUd).2
      ⟨fun h => (hFinite h).elim,D,hD,hDer⟩
  refine ⟨by exact_mod_cast hAll,?_⟩
  intro i x hx
  change fderivWithin ℝ f (closure S) x (axis i) = G i x
  rw [(hDer x hx).fderivWithin (hUd x hx)]
  exact derivativeFromColumns_axis (fun j => G j x) i

theorem coordDeriv_mixed_commute_of_contDiffAt_two {f : Point → F} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (i j : Fin 3) :
    coordDeriv i (coordDeriv j f) x = coordDeriv j (coordDeriv i f) x := by
  change fderiv ℝ (fun y => fderiv ℝ f y (axis j)) x (axis i) =
    fderiv ℝ (fun y => fderiv ℝ f y (axis i)) x (axis j)
  rw [fderiv_fderiv_column_eq_iteratedFDeriv_two hf,
    fderiv_fderiv_column_eq_iteratedFDeriv_two hf,
    iteratedFDeriv_two_apply,iteratedFDeriv_two_apply]
  have hSym := hf.isSymmSndFDerivAt (by simp)
  exact hSym (axis i) (axis j)

end Thesis
