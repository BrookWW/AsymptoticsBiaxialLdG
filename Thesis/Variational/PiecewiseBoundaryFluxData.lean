module

public import Thesis.Variational.BoundaryPohozaev
import Thesis.MeasureGeometry.SmoothGraphArea
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! The uniform classical integrability needed for the coordinate flux on a bounded domain. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal NNReal Topology

namespace Thesis

private def transverseCoordinates : Point →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ Plane ℝ).comp planeLinePlacement.symm.toContinuousLinearMap

private theorem transverseCoordinates_apply (z : Point) :
    transverseCoordinates z = WithLp.toLp 2 ![z 0,z 1] := by
  let p := planeLinePlacement.symm z
  have h := planeLinePlacement_coordinate p.1 p.2
  rw [show planeLinePlacement (p.1,p.2) = z from planeLinePlacement.apply_symm_apply z] at h
  change p.1 = _
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h.1.symm
  · exact h.2.1.symm

private theorem uniqueDiffWithinAt_of_locallyLipschitzBoundary {U : Set Point}
    (hLip : HasLocallyLipschitzBoundary U) {x : Point} (hx : x ∈ frontier U) :
    UniqueDiffWithinAt ℝ U x := by
  obtain ⟨r,A,g,L,hr,hg,hg0,hChart⟩ := hLip x hx
  let C : Set Point := {v | (L : ℝ) * ‖transverseCoordinates (A v)‖ < (A v) 2}
  have hC : IsOpen C := isOpen_lt
    (continuous_const.mul ((transverseCoordinates.continuous.comp A.continuous).norm))
    ((EuclideanSpace.proj (𝕜 := ℝ) 2).continuous.comp A.continuous)
  have hCn : C.Nonempty := by
    refine ⟨A.symm (axis 2),?_⟩
    change (L : ℝ) * ‖transverseCoordinates (A (A.symm (axis 2)))‖ < (A (A.symm (axis 2))) 2
    rw [A.apply_symm_apply]
    have h0 : transverseCoordinates (axis 2) = 0 := by
      rw [transverseCoordinates_apply]
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [axis]
    rw [h0, norm_zero, mul_zero]
    simp [axis]
  have hT : C ⊆ tangentConeAt ℝ U x := by
    intro v hv
    apply mem_tangentConeAt_of_add_smul_mem (tendsto_id'.mpr (nhdsGT_le_nhdsNE (0 : ℝ)))
    let z := A v
    let p := transverseCoordinates z
    let y (t : ℝ) := x + t • v
    have hyC : Continuous y := continuous_const.add (continuous_id.smul continuous_const)
    have hy0 : y 0 = x := by simp [y]
    have hNear : ∀ᶠ t in 𝓝[>] (0 : ℝ), y t ∈ ball x r :=
      nhdsWithin_le_nhds ((hyC.continuousAt : ContinuousAt y 0)
        (hy0.symm ▸ isOpen_ball.mem_nhds (mem_ball_self hr)))
    have hpC : Continuous (fun t : ℝ => t • p) := continuous_id.smul continuous_const
    have hpNear : ∀ᶠ t in 𝓝[>] (0 : ℝ), t • p ∈ ball (0 : Plane) r :=
      nhdsWithin_le_nhds (hpC.continuousAt
        (show ball (0 : Plane) r ∈ 𝓝 ((0 : ℝ) • p) by rw [zero_smul]; exact ball_mem_nhds _ hr))
    filter_upwards [hNear,hpNear,self_mem_nhdsWithin] with t hBall hpBall ht
    have ht0 : 0 < t := ht
    have hYEq : A (y t - x) = t • z := by
      rw [show y t - x = t • v by dsimp only [y]; abel, A.map_smul]
    have hDif := hg.dist_le_mul (t • p) hpBall 0 (mem_ball_self hr)
    rw [hg0, Real.dist_eq, sub_zero, dist_zero_right, norm_smul,
      Real.norm_of_nonneg ht0.le] at hDif
    have hLe := (le_abs_self _).trans hDif
    have hC' : (L : ℝ) * ‖p‖ < z 2 := hv
    have hGt : g (t • p) < t * z 2 := hLe.trans_lt
      (by rw [mul_left_comm (L : ℝ) t]; exact mul_lt_mul_of_pos_left hC' ht0)
    have hSet := Set.ext_iff.mp hChart (y t)
    apply (hSet.mpr ⟨?_,hBall⟩).1
    change g (WithLp.toLp 2 ![(A (y t-x)) 0,(A (y t-x)) 1]) < (A (y t-x)) 2
    rw [← transverseCoordinates_apply, hYEq, map_smul]
    exact hGt
  let W := Submodule.span ℝ (tangentConeAt ℝ U x)
  have hIn : C ⊆ interior (W : Set Point) :=
    hC.subset_interior_iff.mpr (hT.trans Submodule.subset_span)
  have hTop : W = ⊤ := W.eq_top_of_nonempty_interior' (hCn.mono hIn)
  change Submodule.span ℝ (tangentConeAt ℝ U x) = ⊤ at hTop
  simp [uniqueDiffWithinAt_iff, hTop, frontier_subset_closure hx]

/-- The actual closure of a Lipschitz domain has unique within derivatives. -/
theorem PiecewiseRegularBoundary.uniqueDiffOn_closure {U : Set Point} {ν : Point → Point}
    (hU : PiecewiseRegularBoundary U ν) : UniqueDiffOn ℝ (closure U) := by
  intro x hx
  by_cases hxU : x ∈ U
  · exact uniqueDiffWithinAt_of_mem_nhds
      (mem_of_superset (hU.isOpen.mem_nhds hxU) subset_closure)
  · have hxF : x ∈ frontier U := by
      rw [frontier, hU.isOpen.interior_eq]
      exact ⟨hx,hxU⟩
    exact (uniqueDiffWithinAt_of_locallyLipschitzBoundary hU.lipschitz hxF).mono
      subset_closure

/-- A classical scalar field and all its actual interior coordinate
derivatives are bounded on a fixed bounded Lipschitz domain. -/
theorem PiecewiseRegularBoundary.exists_uniform_value_coordDeriv_bound
    {U : Set Point} {ν : Point → Point} (hU : PiecewiseRegularBoundary U ν)
    {f : Point → ℝ} (hf : ContDiffOn ℝ 1 f (closure U)) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x ∈ closure U, ‖f x‖ ≤ M) ∧
      ∀ x ∈ U, ∀ j : Fin 3, ‖coordDeriv j f x‖ ≤ M := by
  have hK := hU.isBounded.isCompact_closure
  obtain ⟨M₁,hM₁⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨M₂,hM₂⟩ := hK.exists_bound_of_continuousOn
    (hf.continuousOn_fderivWithin hU.uniqueDiffOn_closure le_rfl)
  let M := max 0 (max M₁ M₂)
  have h₁ : M₁ ≤ M := (le_max_left M₁ M₂).trans (le_max_right _ _)
  have h₂ : M₂ ≤ M := (le_max_right M₁ M₂).trans (le_max_right _ _)
  refine ⟨M, le_max_left _ _, fun x hx => (hM₁ x hx).trans h₁, ?_⟩
  intro x hx j
  have hN : closure U ∈ 𝓝 x := mem_of_superset (hU.isOpen.mem_nhds hx) subset_closure
  have hD := ((hf _ (subset_closure hx)).contDiffAt hN).differentiableAt one_ne_zero
  have hE := fderivWithin_eq_fderiv (uniqueDiffWithinAt_of_mem_nhds hN) hD
  have hj : ‖axis j‖ = 1 := by simp [axis]
  change ‖(fderiv ℝ f x) (axis j)‖ ≤ M
  rw [← hE]
  refine ((fderivWithin ℝ f (closure U) x).le_opNorm _).trans ?_
  rw [hj, mul_one]
  exact (hM₂ x (subset_closure hx)).trans h₂

/-- The interior derivative and the original surface flux are both integrable. -/
theorem PiecewiseRegularBoundary.integrable_coordinate_flux {U : Set Point} {ν : Point → Point}
    (hU : PiecewiseRegularBoundary U ν) {f : Point → ℝ} (hf : ContDiffOn ℝ 1 f (closure U)) (j : Fin 3) :
    IntegrableOn (coordDeriv j f) U volume ∧
      IntegrableOn (fun x => f x * ν x j) (frontier U) (Measure.euclideanHausdorffMeasure 2) := by
  obtain ⟨M,hM,hF,hD⟩ := hU.exists_uniform_value_coordDeriv_bound hf
  let μ := volume.restrict U
  let σ := (Measure.euclideanHausdorffMeasure 2).restrict (frontier U)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hU.isBounded.measure_lt_top.ne
  letI : IsFiniteMeasure σ := isFiniteMeasure_restrict.2 hU.area_lt_top.ne
  have hC : ContinuousOn (coordDeriv j f) U :=
    ((hf.mono subset_closure).continuousOn_fderiv_of_isOpen hU.isOpen le_rfl).clm_apply continuousOn_const
  have hI : MemLp (coordDeriv j f) 1 μ :=
    MemLp.of_bound (hC.aestronglyMeasurable hU.isOpen.measurableSet) M
      ((ae_restrict_mem hU.isOpen.measurableSet).mono fun x hx => hD x hx j)
  have hFM : AEStronglyMeasurable f σ :=
    (hf.continuousOn.mono frontier_subset_closure).aestronglyMeasurable isClosed_frontier.measurableSet
  have hνM : AEStronglyMeasurable (fun x => ν x j) σ :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable.comp_aemeasurable hU.normal_measurable).aestronglyMeasurable
  have hJ : MemLp (fun x => f x * ν x j) 1 σ :=
    MemLp.of_bound (hFM.mul hνM) M (by
      filter_upwards [hU.normal_ae] with x hx
      have hn : ‖ν x j‖ ≤ 1 := (PiLp.norm_apply_le _ j).trans_eq hx.2.1
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans
        (by rw [mul_one]; exact hF _ (frontier_subset_closure hx.1)))
  exact ⟨memLp_one_iff_integrable.1 hI, memLp_one_iff_integrable.1 hJ⟩

end Thesis
