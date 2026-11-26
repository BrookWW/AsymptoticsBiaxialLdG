module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.Topology.Sequences

/-! A Hilbert basis respecting the eigenspaces of a compact symmetric operator. -/

public section

noncomputable section

open Function Filter Metric Set Topology Module
open scoped RealInnerProductSpace

namespace Thesis

universe u

/-- A compact symmetric operator on a real Hilbert space has a Hilbert
basis consisting of actual eigenvectors. -/
theorem exists_hilbertBasis_of_compact_symmetric {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hCompact : IsCompactOperator T) (hSymmetric : T.IsSymmetric) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (μ : ι → ℝ), ∀ i, T (b i) = μ i • b i := by
  classical
  let V (μ : ℝ) := End.eigenspace (T : End ℝ E) μ
  have hBasis (μ : ℝ) : ∃ (S : Set (V μ)) (b : HilbertBasis S ℝ (V μ)), ⇑b = Subtype.val := by
    letI : CompleteSpace (V μ) :=
      (ContinuousLinearMap.isClosed_eigenspace (f := T) (μ := μ)).completeSpace_coe
    exact exists_hilbertBasis ℝ (V μ)
  choose S e _ using hBasis
  let I := Σ μ : ℝ, S μ
  let b₀ (i : I) : E := (e i.1 i.2 : V i.1).val
  have hEig (i : I) : T (b₀ i) = i.1 • b₀ i := End.mem_eigenspace_iff.mp (e i.1 i.2).property
  have hON : Orthonormal ℝ b₀ := by
    rw [orthonormal_iff_ite]
    rintro ⟨r,i⟩ ⟨s,j⟩
    by_cases hrs : r = s
    · subst s
      have h := (orthonormal_iff_ite.mp (e r).orthonormal) i j
      have hEq : ((⟨r,i⟩ : I) = ⟨r,j⟩) ↔ i = j := ⟨by intro he; cases he; rfl, by intro he; subst j; rfl⟩
      simp only [hEq]
      exact h
    · have hN : (⟨r,i⟩ : I) ≠ ⟨s,j⟩ := fun h => hrs (congrArg Sigma.fst h)
      rw [if_neg hN]
      have h := hSymmetric (b₀ ⟨r,i⟩) (b₀ ⟨s,j⟩)
      rw [show (T : End ℝ E) (b₀ ⟨r,i⟩) = _ from hEig ⟨r,i⟩,
        show (T : End ℝ E) (b₀ ⟨s,j⟩) = _ from hEig ⟨s,j⟩,
        real_inner_smul_left, real_inner_smul_right] at h
      by_contra hZ
      exact hrs (mul_right_cancel₀ hZ h)
  let W := Submodule.span ℝ (Set.range b₀)
  have hVle (μ : ℝ) : V μ ≤ W.topologicalClosure := by
    intro x hx
    let u : V μ := ⟨x,hx⟩
    have hβ : (Submodule.span ℝ (Set.range (e μ)) : Set (V μ)) ⊆
        ((↑) : V μ → E) ⁻¹' (W.topologicalClosure : Set E) := by
      change Submodule.span ℝ (Set.range (e μ)) ≤ W.topologicalClosure.comap (V μ).subtype
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨μ,i⟩,rfl⟩)
    have hC : IsClosed (((↑) : V μ → E) ⁻¹' (W.topologicalClosure : Set E)) :=
      (Submodule.isClosed_topologicalClosure W).preimage continuous_subtype_val
    have hAll : u ∈ (Submodule.span ℝ (Set.range (e μ))).topologicalClosure := by
      rw [(e μ).dense_span]
      exact Submodule.mem_top
    exact closure_minimal hβ hC hAll
  have hTop := T.orthogonalComplement_iSup_eigenspaces_eq_bot hCompact hSymmetric
  have hWB : Wᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    have hℓ : (⨆ μ, V μ) ≤ W.topologicalClosure := iSup_le hVle
    have h := Submodule.orthogonal_le hℓ
    rw [Submodule.orthogonal_closure] at h
    exact h.trans hTop.le
  let b : HilbertBasis I ℝ E := HilbertBasis.mkOfOrthogonalEqBot hON hWB
  have hb : ⇑b = b₀ := HilbertBasis.coe_mkOfOrthogonalEqBot hON hWB
  refine ⟨I,b,Sigma.fst,fun i => ?_⟩
  rw [hb]
  exact hEig i

/-- A compact injective map supplies the eigenspaces of its positive Gram
operator, with positive bounded masses and the exact inner product relation. -/
theorem exists_positive_hilbertBasis_of_compact_injective {E F : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (J : E →L[ℝ] F) (hJ : IsCompactOperator J) (hJI : Injective J) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (μ : ι → ℝ) (C : ℝ), 0 < C ∧
      (∀ i, 0 < μ i ∧ μ i ≤ C) ∧ ∀ i x, inner ℝ (J (b i)) (J x) = μ i * inner ℝ (b i) x := by
  let T := J.adjoint.comp J
  have hTC : IsCompactOperator T := hJ.clm_comp J.adjoint
  have hForm (x y : E) : inner ℝ (T x) y = inner ℝ (J x) (J y) :=
    J.adjoint_inner_left y (J x)
  have hForm' (x y : E) : inner ℝ x (T y) = inner ℝ (J x) (J y) :=
    J.adjoint_inner_right x (J y)
  have hSymm : T.IsSymmetric := fun x y => (hForm x y).trans (hForm' x y).symm
  obtain ⟨I,b,μ,hEig⟩ := exists_hilbertBasis_of_compact_symmetric T hTC hSymm
  let C := max 1 (‖J‖ ^ 2)
  refine ⟨I,b,μ,C,zero_lt_one.trans_le (le_max_left _ _),?_,?_⟩
  · intro i
    have hSquare : μ i = ‖J (b i)‖ ^ 2 := by
      have h := hForm (b i) (b i)
      rw [hEig i,real_inner_smul_left,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
        b.orthonormal.norm_eq_one i,one_pow,mul_one] at h
      exact h
    have hNz : J (b i) ≠ 0 := by
      intro h
      have h0 := hJI (h.trans (map_zero J).symm)
      have h1 := b.orthonormal.norm_eq_one i
      rw [h0,norm_zero] at h1
      exact zero_ne_one h1
    rw [hSquare]
    refine ⟨sq_pos_of_pos (norm_pos_iff.mpr hNz),?_⟩
    have h := J.le_opNorm (b i)
    rw [b.orthonormal.norm_eq_one i,mul_one] at h
    exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans (le_max_right _ _)
  · intro i x
    rw [← hForm,hEig,real_inner_smul_left]

/-- A bounded linear map is compact if every sequence in the unit ball
has a subsequence whose images converge. -/
theorem isCompactOperator_of_bounded_image_subsequence {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (L : E →L[ℝ] F)
    (hL : ∀ v : ℕ → E, (∀ n, ‖v n‖ ≤ 1) →
      ∃ κ : ℕ → ℕ, ∃ y : F, StrictMono κ ∧ Tendsto (fun n => L (v (κ n))) atTop (𝓝 y)) :
    IsCompactOperator L := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall L.toLinearMap
    (r := 1) zero_lt_one).2
  apply isCompact_iff_isSeqCompact.2
  intro x hx
  let K := L.toLinearMap '' closedBall (0 : E) 1
  have hA (n : ℕ) : ∃ v ∈ closedBall (0 : E) 1, dist (x n) (L v) < 1 / ((n : ℝ) + 1) := by
    have hε : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    obtain ⟨y,hy,hD⟩ := Metric.mem_closure_iff.mp (show x n ∈ closure K from hx n) _ hε
    obtain ⟨v,hv,rfl⟩ := hy
    exact ⟨v,hv,hD⟩
  choose v hv hd using hA
  obtain ⟨κ,y,hκ,hY⟩ := hL v (fun n => mem_closedBall_zero_iff.1 (hv n))
  have hN : Tendsto (x ∘ κ) atTop (𝓝 y) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨M,hM⟩ := Metric.tendsto_atTop.mp hY (ε / 2) (half_pos hε)
    have ht : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨N,hN⟩ := eventually_atTop.mp ((ht.comp hκ.tendsto_atTop).eventually_lt_const (half_pos hε))
    refine ⟨max M N, fun n hn => ?_⟩
    have hA' := (hd (κ n)).trans (hN n (hn.trans' (le_max_right _ _)))
    have hR := hM n (hn.trans' (le_max_left _ _))
    exact (dist_triangle (x (κ n)) (L (v (κ n))) y).trans_lt (by linarith only [hA',hR])
  refine ⟨y,?_ ,κ,hκ,hN⟩
  exact isClosed_closure.mem_of_tendsto hN (Eventually.of_forall fun n => hx (κ n))

/-- For a family with diagonal Gram matrix, each finite linear combination
has the corresponding weighted square norm. -/
theorem norm_sum_sq_of_diagonal_gram {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq ι]
    (F : Finset ι) (v : ι → E) (q c : ι → ℝ)
    (h : ∀ i j : ι, inner ℝ (v i) (v j) = if i = j then q i else 0) :
    ‖∑ i ∈ F, c i • v i‖ ^ 2 = ∑ i ∈ F, q i * c i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, h]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg hj,mul_zero, mul_zero])
    (fun hI => (hI hi).elim)]
  rw [if_pos rfl]
  ring

end Thesis
