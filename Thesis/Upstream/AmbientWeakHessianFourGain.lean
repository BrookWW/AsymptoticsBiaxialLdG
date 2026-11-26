module

public import Thesis.Upstream.WholeSpaceWeakHessianGain
public import Thesis.Upstream.AmbientWeakPartialAlgebra
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Fourth-integrability of the actual Euclidean weak Hessian columns. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

private theorem weakAmbientPartial_proj_pairing {q : ℕ} {u d : Point → Ambient q}
    (hu : MemLp u 2 (volume : Measure Point)) (hd : MemLp d 2 (volume : Measure Point))
    {i : Fin 3} (h : IsWeakAmbientCoordinatePartial univ i u d)
    (k : Fin q) (φ : CompactSmoothScalar) :
    (∫ x, d x k*φ.val x) = -(∫ x, u x k*(compactSmoothScalarDeriv i φ).val x) := by
  let ψ := (compactSmoothScalarDeriv i φ).val
  let L : Ambient q →L[ℝ] ℝ := EuclideanSpace.proj k
  have hp : MemLp φ.val 2 (volume : Measure Point) :=
    φ.property.1.continuous.memLp_of_hasCompactSupport φ.property.2
  have hψ : MemLp ψ 2 (volume : Measure Point) :=
    (compactSmoothScalarDeriv i φ).property.1.continuous.memLp_of_hasCompactSupport
      (compactSmoothScalarDeriv i φ).property.2
  have hI : Integrable (fun x => ψ x • u x) (volume : Measure Point) :=
    memLp_one_iff_integrable.1 (hu.smul (r := 1) hψ)
  have hJ : Integrable (fun x => φ.val x • d x) (volume : Measure Point) :=
    memLp_one_iff_integrable.1 (hd.smul (r := 1) hp)
  have hEq := h φ.val φ.property.1 φ.property.2 (subset_univ _)
  rw [Measure.restrict_univ] at hEq
  change (∫ x, ψ x • u x) = -(∫ x, φ.val x • d x) at hEq
  have hP := congrArg L hEq
  rw [map_neg,← L.integral_comp_comm hI,← L.integral_comp_comm hJ] at hP
  simp only [map_smul,smul_eq_mul] at hP
  change (∫ x, ψ x*u x k) = -(∫ x, φ.val x*d x k) at hP
  have he := congrArg Neg.neg hP
  rw [neg_neg] at he
  simpa only [ψ,mul_comm] using he.symm

/-- The original weak second Euclidean columns project to the actual
scalar distributional Hessians in each coordinate. -/
theorem isWeakScalarHessian_proj_of_memW12_univ {q : ℕ}
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    {H : Point → Fin 3 → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D)
    (hD : ∀ i, MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (fun x => D x i) (fun x => H x i))
    (k : Fin q) :
    IsWeakScalarHessian (fun x => u x k) (fun i j x => H x i j k) := by
  have huLp : MemLp u 2 (volume : Measure Point) := by simpa only [Measure.restrict_univ] using hu.2.1
  have hDLp (i : Fin 3) : MemLp (fun x => D x i) 2 (volume : Measure Point) := by
    simpa only [Measure.restrict_univ] using hu.2.2 i
  have hHLp (i j : Fin 3) : MemLp (fun x => H x i j) 2 (volume : Measure Point) := by
    simpa only [Measure.restrict_univ] using (hD i).2.2 j
  exact IsWeakScalarHessian.of_first_pairings (D := fun i x => D x i k)
    (fun i φ => weakAmbientPartial_proj_pairing huLp (hDLp i) (hu.1.2.2 i) k φ)
    (fun i j φ => weakAmbientPartial_proj_pairing (hDLp i) (hHLp i j) ((hD i).1.2.2 j) k φ)

theorem memLp_of_all_euclidean_coordinates {q : ℕ} {μ : Measure Point} {p : ℝ≥0∞}
    {u : Point → Ambient q} (h : ∀ k : Fin q, MemLp (fun x => u x k) p μ) :
    MemLp u p μ := by
  have he (x : Point) : u x = ∑ k : Fin q, u x k • EuclideanSpace.single k 1 := by
    symm
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin q) ℝ).sum_repr (u x)
  rw [show u = (fun x => ∑ k : Fin q, u x k • EuclideanSpace.single k 1) from funext he]
  apply memLp_finsetSum
  intro k _
  let L : ℝ →L[ℝ] Ambient q := (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single k 1)
  exact (h k).continuousLinearMap_comp L

/-- The same flat perturbation gain for all components of a Euclidean
field, retaining the given weak Hessian representatives. -/
theorem exists_wholeSpace_ambientWeakHessian_four_gain :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {q : ℕ} {u f : Point → Ambient q}
      {D : Point → HarmonicMaps.Gradient 3 q} {H : Point → Fin 3 → HarmonicMaps.Gradient 3 q}
      {a : Fin 3 → Fin 3 → Point → ℝ},
      MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D →
      (∀ i, MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (fun x => D x i) (fun x => H x i)) →
      HasCompactSupport f → MemLp f 2 (volume : Measure Point) → MemLp f 4 (volume : Measure Point) →
      (∀ i j, AEStronglyMeasurable (a i j) (volume : Measure Point) ∧ HasCompactSupport (a i j)) →
      (∀ i j x, |a i j x| ≤ δ) →
      ((fun x => ∑ i : Fin 3, H x i i) =ᵐ[(volume : Measure Point)]
        fun x => f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x • H x i j) →
      ∀ i j, MemLp (fun x => H x i j) 4 (volume : Measure Point) := by
  obtain ⟨δ,_,hδ,_,hEstimate⟩ := exists_wholeSpace_weakHessian_four_gain
  refine ⟨δ,hδ,?_⟩
  intro q u f D H a hu hD hfc hf₂ hf₄ ha hB hEq i j
  apply memLp_of_all_euclidean_coordinates
  intro k
  let L : Ambient q →L[ℝ] ℝ := EuclideanSpace.proj k
  have huLp : MemLp (fun x => u x k) 2 (volume : Measure Point) :=
    (show MemLp u 2 (volume : Measure Point) by simpa only [Measure.restrict_univ] using hu.2.1
      ).continuousLinearMap_comp L
  have hHLp (i j : Fin 3) : MemLp (fun x => H x i j k) 2 (volume : Measure Point) :=
    (show MemLp (fun x => H x i j) 2 (volume : Measure Point) by simpa only [Measure.restrict_univ] using (hD i).2.2 j
      ).continuousLinearMap_comp L
  have hfκ : HasCompactSupport (fun x => f x k) := by
    apply hfc.mono
    intro x hx
    by_contra hx₀
    exact hx (by change f x k = 0; rw [Function.notMem_support.mp hx₀,PiLp.zero_apply])
  have hEq' :
      scalarWeakHessianTrace (fun i j x => H x i j k) =ᵐ[(volume : Measure Point)]
        fun x => f x k+∑ i : Fin 3, ∑ j : Fin 3, a i j x * H x i j k := by
    filter_upwards [hEq] with x hx
    have h := congrArg L hx
    simp only [map_sum,map_add,map_smul,smul_eq_mul] at h
    exact h
  exact (hEstimate huLp (isWeakScalarHessian_proj_of_memW12_univ hu hD k) hHLp hfκ
    (hf₂.continuousLinearMap_comp L) (hf₄.continuousLinearMap_comp L) ha hB hEq' i j).1

end Thesis
