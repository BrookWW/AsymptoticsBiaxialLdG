module

public import Thesis.Variational.SmoothDomainClosedDerivative
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Finite jets on the closure of a smooth domain. -/

public section

noncomputable section

open Filter Function Set Topology
open scoped ContDiff

namespace Thesis

variable {U : Set Point}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem hasFDerivWithinAt_of_continuous_closed_jet
    (hU : IsSmoothDomain U) {f : Point → F} {D : Point → Point →L[ℝ] F}
    (hf : ContinuousOn f (closure U)) (hD : ContinuousOn D (closure U))
    (hDiff : ∀ x ∈ U, HasFDerivAt f (D x) x) :
    ∀ x ∈ closure U, HasFDerivWithinAt f (D x) (closure U) x := by
  have hC := hU.contDiffOn_one_of_continuous_derivative hf hD hDiff
  have hI : EqOn (fderivWithin ℝ f (closure U)) D U := by
    intro x hx
    rw [fderivWithin_of_mem_nhds (mem_of_superset (hU.1.1.mem_nhds hx) subset_closure)]
    exact (hDiff x hx).fderiv
  have hEq := hI.of_subset_closure
    (hC.continuousOn_fderivWithin hU.uniqueDiffOn_closure le_rfl) hD subset_closure Subset.rfl
  intro x hx
  rw [← hEq hx]
  exact (hC.differentiableOn one_ne_zero x hx).hasFDerivWithinAt

/-- A continuously differentiable interior field whose derivative extends
with order k has order k + 1 on the original smooth closure. -/
theorem IsSmoothDomain.contDiffOn_nat_succ_of_continuous_derivative
    (hU : IsSmoothDomain U) (k : ℕ) {f : Point → F} {D : Point → Point →L[ℝ] F}
    (hf : ContinuousOn f (closure U)) (hD : ContDiffOn ℝ (k : ℕ∞ω) D (closure U))
    (hDiff : ∀ x ∈ U, HasFDerivAt f (D x) x) : ContDiffOn ℝ (↑(k+1) : ℕ∞ω) f (closure U) := by
  have hFinite : (k : ℕ∞ω) ≠ ω := by
    change ((↑(k : ℕ∞)) : ℕ∞ω) ≠ ⊤
    exact WithTop.coe_ne_top
  have hC : ContDiffOn ℝ ((k : ℕ∞ω)+1) f (closure U) :=
    (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn_closure).2
      ⟨fun h => (hFinite h).elim,D,hD,hasFDerivWithinAt_of_continuous_closed_jet hU hf hD.continuousOn hDiff⟩
  exact_mod_cast hC

/-- Continuous extensions of a compatible finite derivative jet give the stated
regularity of its zeroth component on the smooth closed domain. -/
theorem IsSmoothDomain.contDiffOn_zero_jet_of_continuous_jets
    (hU : IsSmoothDomain U) (n : ℕ)
    (J : ∀ i : ℕ, Point → Point [×i]→L[ℝ] F)
    (hJ : ∀ i ≤ n, ContinuousOn (J i) (closure U))
    (hCompat : ∀ i < n, ∀ x ∈ U,
      HasFDerivAt (J i)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i+1) => Point) F (J (i+1) x)) x) :
    ContDiffOn ℝ (n : ℕ∞ω) (J 0) (closure U) := by
  have hRec (k : ℕ) : ∀ i, i+k ≤ n → ContDiffOn ℝ (k : ℕ∞ω) (J i) (closure U) := by
    induction k with
    | zero =>
      intro i hi
      exact contDiffOn_zero.mpr (hJ i (by omega))
    | succ k hk =>
      intro i hi
      let E : (Point [×(i+1)]→L[ℝ] F) ≃ₗᵢ[ℝ] (Point →L[ℝ] Point [×i]→L[ℝ] F) :=
        continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i+1) => Point) F
      let D : Point → Point →L[ℝ] Point [×i]→L[ℝ] F := E ∘ J (i+1)
      have hDepth : i+1+k ≤ n := by omega
      have hHigher : ContDiffOn ℝ (k : ℕ∞ω) (J (i+1)) (closure U) := hk (i+1) hDepth
      let L : (Point [×(i+1)]→L[ℝ] F) →L[ℝ] (Point →L[ℝ] Point [×i]→L[ℝ] F) := E.toContinuousLinearEquiv.toContinuousLinearMap
      have hSmooth := ContinuousLinearMap.contDiff (𝕜 := ℝ)
        (E := Point [×(i+1)]→L[ℝ] F) (F := Point →L[ℝ] Point [×i]→L[ℝ] F) (n := (k : ℕ∞ω)) L
      have hD : ContDiffOn ℝ (k : ℕ∞ω) D (closure U) :=
        hSmooth.comp_contDiffOn hHigher
      have hFirst := hasFDerivWithinAt_of_continuous_closed_jet hU
        (hJ i (by omega)) hD.continuousOn (hCompat i (by omega))
      have hFinite : (k : ℕ∞ω) ≠ ω := by
        change ((↑(k : ℕ∞)) : ℕ∞ω) ≠ ⊤
        exact WithTop.coe_ne_top
      have hAll : ContDiffOn ℝ ((k : ℕ∞ω)+1) (J i) (closure U) :=
        (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn_closure).2
          ⟨fun h => (hFinite h).elim,D,hD,hFirst⟩
      exact_mod_cast hAll
  exact hRec n 0 (by omega)

/-- A finite family of continuous extensions of the actual interior derivatives
is the actual within jet of the original function, up to and including the wall. -/
theorem IsSmoothDomain.contDiffOn_of_continuous_iteratedFDeriv_extensions
    (hU : IsSmoothDomain U) (n : ℕ) {f : Point → F}
    (hf : ContinuousOn f (closure U)) (hfI : ContDiffOn ℝ (n : ℕ∞ω) f U)
    (J : ∀ i : ℕ, Point → Point [×i]→L[ℝ] F)
    (hJ : ∀ i ≤ n, ContinuousOn (J i) (closure U))
    (hInt : ∀ i ≤ n, EqOn (J i) (iteratedFDeriv ℝ i f) U) :
    ContDiffOn ℝ (n : ℕ∞ω) f (closure U) ∧
      ∀ i ≤ n, EqOn (iteratedFDerivWithin ℝ i f (closure U)) (J i) (closure U) := by
  have hCompat (i : ℕ) (hi : i < n) (x : Point) (hx : x ∈ U) :
      HasFDerivAt (J i)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i+1) => Point) F (J (i+1) x)) x := by
    have hAt : ContDiffAt ℝ (n : ℕ∞ω) f x :=
      (hfI x hx).contDiffAt (hU.1.1.mem_nhds hx)
    have hOrder : (1 : ℕ∞ω) + (i : ℕ∞ω) ≤ (n : ℕ∞ω) := by
      exact_mod_cast (show 1+i ≤ n by omega)
    have hD := ((hAt.iteratedFDeriv_right (m := 1) hOrder).differentiableAt one_ne_zero).hasFDerivAt
    have hNear : J i =ᶠ[𝓝 x] iteratedFDeriv ℝ i f :=
      mem_of_superset (hU.1.1.mem_nhds hx) (hInt i hi.le)
    have hh := hD.congr_of_eventuallyEq hNear
    rw [fderiv_iteratedFDeriv] at hh
    simpa only [Function.comp_apply,hInt (i+1) (by omega : i+1 ≤ n) hx] using hh
  have hZero := hU.contDiffOn_zero_jet_of_continuous_jets n J hJ hCompat
  let E := continuousMultilinearCurryFin0 ℝ Point F
  have hC : ContDiffOn ℝ (n : ℕ∞ω) (E ∘ J 0) (closure U) :=
    E.toContinuousLinearEquiv.contDiff.comp_contDiffOn hZero
  have hEq : EqOn f (E ∘ J 0) U := by
    intro x hx
    rw [Function.comp_apply,hInt 0 (Nat.zero_le n) hx,iteratedFDeriv_zero_eq_comp,Function.comp_apply]
    exact (E.apply_symm_apply (f x)).symm
  have hF : ContDiffOn ℝ (n : ℕ∞ω) f (closure U) :=
    hC.congr (hEq.of_subset_closure hf hC.continuousOn subset_closure Subset.rfl)
  refine ⟨hF,?_⟩
  intro i hi
  have hE : EqOn (iteratedFDerivWithin ℝ i f (closure U)) (J i) U := by
    intro x hx
    have hn : closure U ∈ 𝓝 x := mem_of_superset (hU.1.1.mem_nhds hx) subset_closure
    have he : iteratedFDerivWithin ℝ i f (closure U) x = iteratedFDeriv ℝ i f x := by
      rw [← iteratedFDerivWithin_univ]
      exact iteratedFDerivWithin_congr_set (Filter.eventuallyEq_univ.mpr hn) i
    exact he.trans (hInt i hi hx).symm
  have hCast : (i : ℕ∞ω) ≤ (n : ℕ∞ω) := by exact_mod_cast hi
  exact hE.of_subset_closure (hF.continuousOn_iteratedFDerivWithin hCast hU.uniqueDiffOn_closure)
    (hJ i hi) subset_closure Subset.rfl

end Thesis
