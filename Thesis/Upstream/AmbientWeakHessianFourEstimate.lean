module

public import Thesis.Upstream.AmbientWeakHessianFourGain
import Thesis.Upstream.WholeSpaceWeakHessianGain

/-! The quantitative whole-space perturbation estimate for Euclidean fields. -/

public section

open Filter HarmonicMaps MeasureTheory Set
open scoped ContDiff ENNReal

namespace Thesis

/-- The scalar perturbation estimate controls each actual vector Hessian
column with one dimension-dependent constant. -/
theorem exists_wholeSpace_ambientWeakHessian_four_estimate :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ {q : ℕ} {u f : Point → Ambient q}
      {D : Point → HarmonicMaps.Gradient 3 q} {H : Point → Fin 3 → HarmonicMaps.Gradient 3 q}
      {a : Fin 3 → Fin 3 → Point → ℝ},
      MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D →
      (∀ i, MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (fun x => D x i) (fun x => H x i)) →
      HasCompactSupport f → MemLp f 2 (volume : Measure Point) → MemLp f 4 (volume : Measure Point) →
      (∀ i j, AEStronglyMeasurable (a i j) (volume : Measure Point) ∧ HasCompactSupport (a i j)) →
      (∀ i j x, |a i j x| ≤ δ) →
      ((fun x => ∑ i : Fin 3, H x i i) =ᵐ[(volume : Measure Point)]
        fun x => f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x • H x i j) →
      ∀ i j, MemLp (fun x => H x i j) 4 (volume : Measure Point) ∧
        lpNorm (fun x => H x i j) 4 volume ≤ q*C*lpNorm f 4 volume := by
  obtain ⟨δ,C,hδ,hC,hEstimate⟩ := exists_wholeSpace_weakHessian_four_gain
  refine ⟨δ,C,hδ,hC,?_⟩
  intro q u f D H a hu hD hfc hf₂ hf₄ ha hB hEq i j
  have hEach (k : Fin q) : MemLp (fun x => H x i j k) 4 (volume : Measure Point) ∧
      lpNorm (fun x => H x i j k) 4 volume ≤ C*lpNorm f 4 volume := by
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
    obtain ⟨hMem,hEstimateNorm⟩ := hEstimate huLp (isWeakScalarHessian_proj_of_memW12_univ hu hD k) hHLp hfκ
      (hf₂.continuousLinearMap_comp L) (hf₄.continuousLinearMap_comp L) ha hB hEq' i j
    have hNorm : lpNorm (fun x => f x k) 4 volume ≤ lpNorm f 4 volume := by
      rw [← lpNorm_norm hf₄.1]
      exact lpNorm_mono_real hf₄.norm (fun x => PiLp.norm_apply_le (f x) k)
    exact ⟨hMem,hEstimateNorm.trans (mul_le_mul_of_nonneg_left hNorm hC.le)⟩
  refine ⟨memLp_of_all_euclidean_coordinates (fun k => (hEach k).1),?_⟩
  let G (k : Fin q) (x : Point) := H x i j k • EuclideanSpace.single k (1 : ℝ)
  have hPoint (x : Point) : H x i j = ∑ k : Fin q, G k x := by
    symm
    simpa only [G,EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin q) ℝ).sum_repr (H x i j)
  rw [show (fun x => H x i j) = ∑ k : Fin q, G k from funext fun x =>
    (hPoint x).trans (Finset.sum_apply x Finset.univ G).symm]
  have hG (k : Fin q) : MemLp (G k) 4 (volume : Measure Point) :=
    (hEach k).1.continuousLinearMap_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single k (1 : ℝ)))
  have hGN (k : Fin q) : lpNorm (G k) 4 volume ≤ C*lpNorm f 4 volume := by
    refine (lpNorm_mono_real (hEach k).1.norm (fun x => ?_)).trans ?_
    · simp [G,norm_smul,PiLp.norm_single]
    · simpa only [lpNorm_norm (hEach k).1.aestronglyMeasurable] using (hEach k).2
  exact (lpNorm_sum_le (fun k _ => hG k) (by norm_num)).trans
    ((Finset.sum_le_sum (fun k _ => hGN k)).trans_eq (by simp [mul_assoc]))

end Thesis
