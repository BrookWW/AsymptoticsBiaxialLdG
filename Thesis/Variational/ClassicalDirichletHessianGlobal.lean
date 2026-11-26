module

public import Thesis.Variational.ClassicalDirichletHessianInterior
import Thesis.Variational.GlobalDirichletGradientSup

/-! Finite physical cap localization of the classical scalar Dirichlet Hessian estimate. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology

namespace Thesis

private theorem exists_finite_classicalDirichletHessian_cap_cover
    {U : Set Point} (hU : IsSmoothDomain U) {p : ℝ}
    (hInterior : ∀ a ∈ U, HasScalarDirichletHessianCapBound U p a)
    (hWall : ∀ a ∈ frontier U, HasScalarDirichletHessianCapBound U p a) :
    ∃ (r C : closure U → ℝ) (I : Finset (closure U)),
      (∀ a, 0 < r a ∧ 0 ≤ C a) ∧ (closure U ⊆ ⋃ a ∈ I, ball a (r a)) ∧
      ∀ (a : closure U) (u : Point → ℝ) (M F G : ℝ), 0 ≤ M → 0 ≤ F → 0 ≤ G →
        ContDiffOn ℝ 2 u (closure U) → EqOn u (fun _ => 0) (frontier U) →
        (∀ x ∈ U, ‖u x‖ ≤ M) → (∀ x ∈ U, ‖laplacian u x‖ ≤ F) →
        (∀ x ∈ U, ‖fderiv ℝ u x‖ ≤ G) →
        eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 u x‖) (ENNReal.ofReal p)
          (volume.restrict (U∩ball a (r a))) ≤ ENNReal.ofReal (C a*(M+F+G)) := by
  have hCap (a : closure U) : HasScalarDirichletHessianCapBound U p a := by
    by_cases ha : ↑a ∈ U
    · exact hInterior a ha
    · apply hWall
      rw [frontier,hU.1.1.interior_eq]
      exact ⟨a.property,ha⟩
  choose r C hr hC hBound using hCap
  let W (a : closure U) := ball (a : Point) (r a)
  have hCover : closure U ⊆ ⋃ a, W a := fun x hx => mem_iUnion.2 ⟨⟨x,hx⟩,mem_ball_self (hr _)⟩
  obtain ⟨I,hI⟩ := hU.1.2.2.isCompact_closure.elim_finite_subcover W (fun _ => isOpen_ball) hCover
  exact ⟨r,C,I,fun a => ⟨hr a,hC a⟩,hI,hBound⟩

private theorem eLpNorm_le_sum_of_finite_caps {U : Set Point} (hU : MeasurableSet U)
    {ι : Type*} (I : Finset ι) {V : ι → Set Point} (hV : ∀ i ∈ I, MeasurableSet (V i))
    (hIn : ∀ i ∈ I, V i ⊆ U) (hCover : U ⊆ ⋃ i ∈ I,V i)
    {H : Point → ℝ} (hH : AEStronglyMeasurable H (volume.restrict U))
    (hH₀ : ∀ x, 0 ≤ H x) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    eLpNorm H q (volume.restrict U) ≤ ∑ i ∈ I, eLpNorm H q (volume.restrict (V i)) := by
  let μ := (volume : Measure Point).restrict U
  let F (i : ι) := (V i).indicator H
  have hSum (x : Point) (hx : x ∈ U) : H x ≤ (∑ i ∈ I,F i) x := by
    obtain ⟨i,hi⟩ := mem_iUnion.1 (hCover hx)
    obtain ⟨hiI,hxi⟩ := mem_iUnion.1 hi
    have h := Finset.single_le_sum (s := I) (f := fun j => F j x)
      (fun j _ => indicator_nonneg (fun y _ => hH₀ y) _) hiI
    rw [Finset.sum_apply]
    simpa only [F,indicator_of_mem hxi] using h
  have hM : eLpNorm H q μ ≤ eLpNorm (∑ i ∈ I,F i) q μ := by
    apply eLpNorm_mono_ae
    filter_upwards [ae_restrict_mem hU] with x hx
    have hPos : 0 ≤ (∑ i ∈ I,F i) x := (hH₀ x).trans (hSum x hx)
    rw [Real.norm_of_nonneg (hH₀ x),Real.norm_of_nonneg hPos]
    exact hSum x hx
  have hR (i : ι) (hi : i ∈ I) : μ.restrict (V i) = volume.restrict (V i) := by
    dsimp only [μ]
    rw [Measure.restrict_restrict (hV i hi),inter_eq_left.2 (hIn i hi)]
  have hA (i : ι) (hi : i ∈ I) : AEStronglyMeasurable (F i) μ := by
    dsimp only [F]
    rw [aestronglyMeasurable_indicator_iff (hV i hi),hR i hi]
    exact hH.mono_measure (Measure.restrict_mono_set volume (hIn i hi))
  refine hM.trans ((eLpNorm_sum_le hA hq).trans_eq ?_)
  refine Finset.sum_congr rfl (fun i hi => ?_)
  dsimp only [F]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (hV i hi),hR i hi]

/-- The interior and wall estimates on a finite physical cover give the
quantitative scalar estimate with the global amplitude and forcing bounds. -/
theorem scalarGlobalDirichletPoissonSecondDerivativeLp_of_caps
    (hInterior : ∀ (U : Set Point), IsSmoothDomain U → ∀ p : ℝ, 1 < p →
      ∀ a ∈ U, HasScalarDirichletHessianCapBound U p a)
    (hWall : ∀ (U : Set Point), IsSmoothDomain U → ∀ p : ℝ, 1 < p →
      ∀ a ∈ frontier U, HasScalarDirichletHessianCapBound U p a) :
    ScalarGlobalDirichletPoissonSecondDerivativeLp := by
  intro U hU p hp
  obtain ⟨r,C,I,hC,hCover,hBound⟩ := exists_finite_classicalDirichletHessian_cap_cover hU
    (hInterior U hU p hp) (hWall U hU p hp)
  obtain ⟨K,hK,hGrad⟩ := exists_global_zeroTrace_gradient_sup_bound hU
  let D := ∑ a ∈ I, C a
  let B := (1+D)*(1+K)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun a _ => (hC a).2)
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B,hB,?_⟩
  intro u hu hz M F hM hF hv hf
  let G := K*(M+F)
  have hMF : 0 ≤ M+F := add_nonneg hM hF
  have hG : 0 ≤ G := mul_nonneg hK.le hMF
  have hGradB (x : Point) (hx : x ∈ U) : ‖fderiv ℝ u x‖ ≤ G := by
    have h := hGrad hu hz hM hF hv hf x (subset_closure hx)
    have hNear : closure U ∈ 𝓝 x := mem_of_superset (hU.1.1.mem_nhds hx) subset_closure
    rwa [fderivWithin_of_mem_nhds hNear] at h
  let H (x : Point) := ‖iteratedFDeriv ℝ 2 u x‖
  let V (a : closure U) := U∩ball a (r a)
  let q := ENNReal.ofReal p
  have hq : 1 ≤ q := by
    change 1 ≤ ENNReal.ofReal p
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hV (a : closure U) : MeasurableSet (V a) := hU.1.1.measurableSet.inter measurableSet_ball
  have hVU (a : closure U) : V a ⊆ U := inter_subset_left
  have hCV : U ⊆ ⋃ a ∈ I, V a := by
    intro x hx
    obtain ⟨a,ha⟩ := mem_iUnion.1 (hCover (subset_closure hx))
    obtain ⟨haI,hxa⟩ := mem_iUnion.1 ha
    exact mem_iUnion.2 ⟨a,mem_iUnion.2 ⟨haI,hx,hxa⟩⟩
  have hH : ContinuousOn H U :=
    (((hu.mono subset_closure).continuousOn_iteratedFDerivWithin (m := 2) (by norm_num)
      hU.1.1.uniqueDiffOn).congr (fun x hx => (iteratedFDerivWithin_of_isOpen 2 hU.1.1 hx).symm)).norm
  have hHA : AEStronglyMeasurable H (volume.restrict U) := hH.aestronglyMeasurable hU.1.1.measurableSet
  have hE := eLpNorm_le_sum_of_finite_caps hU.1.1.measurableSet I (fun a _ => hV a)
    (fun a _ => hVU a) hCV hHA (fun _ => norm_nonneg _) hq
  have hLast : eLpNorm H q (volume.restrict U) ≤ ENNReal.ofReal (B*(M+F)) := by
    refine hE.trans ((Finset.sum_le_sum fun a _ => hBound a u M F G hM hF hG hu hz hv hf hGradB).trans ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (hC a).2 (add_nonneg hMF hG))]
    apply ENNReal.ofReal_le_ofReal
    rw [← Finset.sum_mul]
    change D*(M+F+G) ≤ B*(M+F)
    rw [show M+F+G = (1+K)*(M+F) by dsimp only [G]; ring, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)) hMF
  exact ⟨⟨hHA,hLast.trans_lt ENNReal.ofReal_lt_top⟩,hLast⟩

end Thesis

end
