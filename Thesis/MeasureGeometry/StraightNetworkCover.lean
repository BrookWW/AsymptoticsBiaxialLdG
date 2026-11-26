module

public import Thesis.External.GeometricMeasureTheory
import Thesis.Foundation.QuaternionSplittingEnergy

/-! Straight weighted ray charts for the actual interior support. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace Thesis.MeasureGeometry

theorem isCompact_tensorSegment (p q : Point) : IsCompact (segment ℝ p q) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

/-- A closed interior ball with its literal radial segments and measure. -/
structure StraightRayPatch (Ω : Set Point) (μ : Measure Point) (κ : ℝ) (x : Point) where
  radius : ℝ
  radius_pos : 0 < radius
  inside : closedBall x radius ⊆ Ω
  count : ℕ
  direction : Fin count → Point
  weight : Fin count → ℝ
  direction_inj : Function.Injective direction
  direction_norm : ∀ i, ‖direction i‖ = 1
  weight_mem : ∀ i, weight i = κ ∨ weight i = 2 * κ
  carrier : μ.support ∩ closedBall x radius = ⋃ i, segment ℝ x (x + radius • direction i)
  mass : μ.restrict (closedBall x radius) =
    ∑ i, ENNReal.ofReal (weight i) • HausdorffOne.restrict (segment ℝ x (x + radius • direction i))

theorem StraightRayPatch.segment_inter_eq_singleton {Ω : Set Point} {μ : Measure Point} {κ : ℝ} {x : Point}
    (P : StraightRayPatch Ω μ κ x) {i j : Fin P.count} (hij : i ≠ j) :
    segment ℝ x (x + P.radius • P.direction i) ∩ segment ℝ x (x + P.radius • P.direction j) = {x} := by
  apply subset_antisymm
  · intro y hy
    have hI := hy.1
    have hJ := hy.2
    rw [segment_eq_image'] at hI hJ
    obtain ⟨s, hs, hsy⟩ := hI
    obtain ⟨t, ht, hty⟩ := hJ
    simp only [add_sub_cancel_left, smul_smul] at hsy hty
    have hst : (s * P.radius) • P.direction i = (t * P.radius) • P.direction j :=
      add_left_cancel (hsy.trans hty.symm)
    have hsr : 0 ≤ s * P.radius := mul_nonneg hs.1 P.radius_pos.le
    have htr : 0 ≤ t * P.radius := mul_nonneg ht.1 P.radius_pos.le
    have hEq : s * P.radius = t * P.radius := by
      have h := congrArg norm hst
      simpa only [norm_smul, Real.norm_of_nonneg hsr, Real.norm_of_nonneg htr,
        P.direction_norm, mul_one] using h
    rw [← hEq] at hst
    have hz : s * P.radius = 0 := by
      by_contra hn
      exact hij (P.direction_inj ((smul_right_injective Point hn) hst))
    rw [hz, zero_smul, add_zero] at hsy
    exact mem_singleton_iff.2 hsy.symm
  · intro y hy
    obtain rfl := mem_singleton_iff.1 hy
    exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

/-- The actual measure on one of the ray segments retains exactly its own
weight. The other rays meet it at only the common vertex. -/
theorem StraightRayPatch.restrict_segment {Ω : Set Point} {μ : Measure Point} {κ : ℝ} {x : Point}
    (P : StraightRayPatch Ω μ κ x) (i : Fin P.count) :
    μ.restrict (segment ℝ x (x + P.radius • P.direction i)) =
      ENNReal.ofReal (P.weight i) • HausdorffOne.restrict (segment ℝ x (x + P.radius • P.direction i)) := by
  classical
  let L (j : Fin P.count) := segment ℝ x (x + P.radius • P.direction j)
  have hSub : L i ⊆ closedBall x P.radius := by
    intro y hy
    exact ((congrArg (fun T : Set Point => y ∈ T) P.carrier).mpr (mem_iUnion.2 ⟨i, hy⟩)).2
  have hMass := congrArg (fun m : Measure Point => m.restrict (L i)) P.mass
  change (μ.restrict (closedBall x P.radius)).restrict (L i) =
    (∑ j, ENNReal.ofReal (P.weight j) • HausdorffOne.restrict (L j)).restrict (L i) at hMass
  rw [Measure.restrict_restrict_of_subset hSub, ← Measure.sum_fintype,
    Measure.restrict_sum_of_countable, Measure.sum_fintype] at hMass
  refine hMass.trans ?_
  rw [Finset.sum_eq_single i]
  · rw [Measure.restrict_smul, Measure.restrict_restrict_of_subset Subset.rfl]
  · intro j _ hj
    rw [Measure.restrict_smul, Measure.restrict_restrict (isCompact_tensorSegment _ _).measurableSet]
    change ENNReal.ofReal (P.weight j) • HausdorffOne.restrict (L i ∩ L j) = 0
    rw [P.segment_inter_eq_singleton hj.symm]
    letI : NullSingletonClass HausdorffOne := Measure.nullSingletonClass_hausdorff Point (by norm_num)
    rw [Measure.restrict_eq_zero.mpr (measure_singleton x), smul_zero]
  · exact fun h => False.elim (h (Finset.mem_univ i))

/-- Quantized density and the actual associated stationary varifold give a
weighted ray chart at each interior point, including the empty chart off support. -/
theorem exists_straightRayPatch (hAA : External.AllardAlmgrenLocalStructure)
    (a : BulkCoefficients) {Ω : Set Point} (hΩ : IsOpen Ω) (μ : FiniteMeasure Point)
    (V : Measure (Point × LineProjection))
    (hV : IsAssociatedVarifold Ω (Ω ∩ (μ : Measure Point).support) μ V)
    (hStationary : IsStationaryVarifold Ω V)
    (hPositive : ∃ c > (0 : ℝ), ∀ x ∈ Ω ∩ (μ : Measure Point).support,
      ∃ θ ≥ c, Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ))
    (hQuant : DensityQuantized a μ (Ω ∩ (μ : Measure Point).support))
    {x : Point} (hx : x ∈ Ω) : Nonempty (StraightRayPatch Ω μ (kappaStar a) x) := by
  classical
  by_cases hs : x ∈ (μ : Measure Point).support
  · obtain ⟨r, m, v, θ, hr, _, hIn, hInj, hW, hSupport, hMass⟩ := hAA Ω hΩ μ
      (Ω ∩ (μ : Measure Point).support) V (kappaStar a) (kappaStar_pos a) hV hStationary
        hPositive hQuant x ⟨hx, hs⟩
    exact ⟨⟨r, hr, hIn, m, v, θ, hInj, fun i => (hW i).1, fun i => (hW i).2, hSupport, hMass⟩⟩
  · let W := Ω \ (μ : Measure Point).support
    have hW : IsOpen W := hΩ.sdiff (μ : Measure Point).isClosed_support
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW x ⟨hx, hs⟩
    let R := r / 2
    have hR := half_pos hr
    have hClosed : closedBall x R ⊆ W :=
      (closedBall_subset_ball (half_lt_self hr)).trans hrW
    refine ⟨⟨R, hR, hClosed.trans sdiff_subset, 0, Fin.elim0, Fin.elim0, ?_,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_, ?_⟩⟩
    · exact fun i => Fin.elim0 i
    · simp only [iUnion_of_empty]
      exact Set.eq_empty_iff_forall_notMem.2 fun y hy => (hClosed hy.2).2 hy.1
    · simp only [Finset.univ_eq_empty, Finset.sum_empty]
      have hNull : (μ : Measure Point) (closedBall x R) = 0 := le_antisymm
        ((measure_mono fun y hy => (hClosed hy).2).trans (Measure.measure_compl_support (μ := (μ : Measure Point))).le)
        zero_le
      exact Measure.restrict_eq_zero.2 hNull

/-- A fixed finite collection of actual ray charts covers a neighborhood of
the compact set. The closure is exactly the union of their closed balls. -/
theorem exists_finite_straightRay_cover {Ω K : Set Point} {μ : Measure Point} {κ : ℝ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hPatch : ∀ x ∈ Ω, Nonempty (StraightRayPatch Ω μ κ x)) :
    ∃ (P : ∀ x : K, StraightRayPatch Ω μ κ x.val) (t : Finset K) (U : Set Point),
      IsOpen U ∧ K ⊆ U ∧ CompactlyContained U Ω ∧
      U = (⋃ i : ↥t, ball i.val.val (P i.val).radius) ∧
      closure U = (⋃ i : ↥t, closedBall i.val.val (P i.val).radius) ∧
      μ.support ∩ closure U = ⋃ i : ↥t, ⋃ j : Fin (P i.val).count,
        segment ℝ i.val.val (i.val.val + (P i.val).radius • (P i.val).direction j) := by
  classical
  let P (x : K) := Classical.choice (hPatch x.val (hKΩ x.property))
  let B (x : K) := ball x.val (P x).radius
  have hCover : K ⊆ ⋃ i, B i := fun x hx =>
    mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (P ⟨x, hx⟩).radius_pos⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover B (fun _ => isOpen_ball) hCover
  let U := ⋃ i : ↥t, B i.val
  have hU : K ⊆ U := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
    exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  have hC : closure U = (⋃ i : ↥t, closedBall i.val.val (P i.val).radius) := by
    rw [show U = ⋃ i : ↥t, B i.val from rfl, closure_iUnion_of_finite]
    exact iUnion_congr fun i => closure_ball _ (P i.val).radius_pos.ne'
  have hCΩ : CompactlyContained U Ω := by
    rw [CompactlyContained, hC]
    refine ⟨isCompact_iUnion fun _ => isCompact_closedBall _ _, iUnion_subset fun i => (P i.val).inside⟩
  refine ⟨P, t, U, isOpen_iUnion (fun _ => isOpen_ball), hU, hCΩ, rfl, hC, ?_⟩
  rw [hC, inter_iUnion]
  exact iUnion_congr fun i => (P i.val).carrier

end Thesis.MeasureGeometry
