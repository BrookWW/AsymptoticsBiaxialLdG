module

public import Thesis.MeasureGeometry.StraightNetworkCover
public import Thesis.MeasureGeometry.FiniteSegmentSubdivision

/-! Finite weighted segment representation on a compactly contained neighborhood. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set Function
open scoped ENNReal Topology

namespace Thesis.MeasureGeometry

/-- The actual support and measure have a common finite segment subdivision
on a neighborhood of the compact set, with disjoint open edges. -/
theorem exists_weightedSegmentNetwork_of_rayPatches {Ω K : Set Point} {μ : Measure Point} {κ : ℝ}
    (hK : CompactlyContained K Ω)
    (hPatch : ∀ x ∈ Ω, Nonempty (StraightRayPatch Ω μ κ x)) :
    ∃ (U : Set Point) (m : ℕ) (p q : Fin m → Point) (θ : Fin m → ℝ),
      let L := fun i : Fin m => segment ℝ (p i) (q i)
      IsOpen U ∧ closure K ⊆ U ∧ CompactlyContained U Ω ∧
      (∀ i, p i ≠ q i ∧ (θ i = κ ∨ θ i = 2 * κ)) ∧
      μ.support ∩ closure U = ⋃ i, L i ∧
      μ.support ∩ closure K = ⋃ i, L i ∩ closure K ∧
      (∀ i j, i ≠ j → ∀ x ∈ L i ∩ L j,
        (x = p i ∨ x = q i) ∧ (x = p j ∨ x = q j)) ∧
      (∀ i, μ.restrict (L i) = ENNReal.ofReal (θ i) • HausdorffOne.restrict (L i)) ∧
      μ.restrict (closure U) = ∑ i, ENNReal.ofReal (θ i) • HausdorffOne.restrict (L i) ∧
      μ.restrict (closure K) = ∑ i, ENNReal.ofReal (θ i) • HausdorffOne.restrict (L i ∩ closure K) := by
  classical
  obtain ⟨P, t, U, hU, hKU, hUΩ, _, _, hCarrier⟩ :=
    exists_finite_straightRay_cover hK.1 hK.2 hPatch
  let I := Σ i : ↥t, Fin (P i.val).count
  let x (i : I) : Point := i.1.val.val
  let y (i : I) : Point := x i + (P i.1.val).radius • (P i.1.val).direction i.2
  let w (i : I) : ℝ := (P i.1.val).weight i.2
  have hxy (i : I) : x i ≠ y i := by
    intro h
    have hv := (P i.1.val).direction_norm i.2
    have hz : (P i.1.val).direction i.2 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hv
      exact zero_ne_one hv
    have hEq : x i + (0 : Point) = x i + (P i.1.val).radius • (P i.1.val).direction i.2 :=
      (add_zero (x i)).trans h
    exact (smul_ne_zero (P i.1.val).radius_pos.ne' hz)
      (add_left_cancel hEq).symm
  have hRaw (i : I) : μ.restrict (segment ℝ (x i) (y i)) =
      ENNReal.ofReal (w i) • HausdorffOne.restrict (segment ℝ (x i) (y i)) :=
    (P i.1.val).restrict_segment i.2
  have hRawSet : μ.support ∩ closure U = ⋃ i : I, segment ℝ (x i) (y i) := by
    rw [hCarrier]
    ext z
    simp only [mem_iUnion]
    exact ⟨fun ⟨i, j, h⟩ => ⟨⟨i, j⟩, h⟩, fun ⟨i, h⟩ => ⟨i.1, i.2, h⟩⟩
  obtain ⟨m, p, q, o, hPieces, hSet, hMeet⟩ := exists_finite_segment_subdivision x y hxy
  let θ := w ∘ o
  let L (i : Fin m) := segment ℝ (p i) (q i)
  have hL (i : Fin m) : MeasurableSet (L i) := (isCompact_tensorSegment _ _).measurableSet
  have hTot : μ.support ∩ closure U = ⋃ i, L i := hRawSet.trans hSet.symm
  have hWeight (i : Fin m) : μ.restrict (L i) = ENNReal.ofReal (θ i) • HausdorffOne.restrict (L i) := by
    have h := congrArg (fun μ : Measure Point => μ.restrict (L i)) (hRaw (o i))
    rw [Measure.restrict_smul, Measure.restrict_restrict_of_subset (hPieces i).2,
      Measure.restrict_restrict_of_subset (hPieces i).2] at h
    exact h
  have hSing (i : Fin m) {z : Point} (hz : z ∈ L i) : μ {z} = 0 := by
    have h' := congrArg (fun μ : Measure Point => μ {z}) (hWeight i)
    rw [Measure.restrict_apply (measurableSet_singleton z), Measure.smul_apply,
      Measure.restrict_apply (measurableSet_singleton z),
      inter_eq_left.2 (singleton_subset_iff.2 hz)] at h'
    letI : NullSingletonClass HausdorffOne := Measure.nullSingletonClass_hausdorff Point (by norm_num)
    simpa only [measure_singleton, mul_zero, smul_eq_mul] using h'
  have hDisj : Pairwise (AEDisjoint μ on L) := by
    intro i j hij
    change μ (L i ∩ L j) = 0
    have hSub : L i ∩ L j ⊆ {p i} ∪ {q i} := by
      intro z hz
      exact (hMeet i j hij z hz).1
    have hNull : μ ({p i} ∪ {q i}) = 0 := le_antisymm
      ((measure_union_le _ _).trans_eq (by
        rw [hSing i (left_mem_segment ℝ _ _), hSing i (right_mem_segment ℝ _ _), add_zero])) zero_le
    exact le_antisymm ((measure_mono hSub).trans_eq hNull) zero_le
  have hSupport : ∀ᵐ z ∂μ, z ∈ μ.support := by
    rw [ae_iff]
    exact Measure.measure_compl_support
  have hCap : μ.restrict (closure U) = ∑ i, ENNReal.ofReal (θ i) • HausdorffOne.restrict (L i) := by
    calc
      _ = μ.restrict (μ.support ∩ closure U) := by
        apply Measure.restrict_congr_set
        filter_upwards [hSupport] with z hz
        exact propext ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
      _ = _ := by
        rw [hTot, Measure.restrict_iUnion_ae hDisj (fun i => (hL i).nullMeasurableSet), Measure.sum_fintype]
        exact Finset.sum_congr rfl fun i _ => hWeight i
  have hcl : closure K ⊆ closure U := hKU.trans subset_closure
  refine ⟨U, m, p, q, θ, hU, hKU, hUΩ, fun i => ⟨(hPieces i).1, (P (o i).1.val).weight_mem (o i).2⟩,
    hTot, ?_, hMeet, hWeight, hCap, ?_⟩
  · calc
      μ.support ∩ closure K = (μ.support ∩ closure U) ∩ closure K := by rw [inter_assoc, inter_eq_right.2 hcl]
      _ = _ := by rw [hTot, iUnion_inter]
  · have h := congrArg (fun μ : Measure Point => μ.restrict (closure K)) hCap
    rw [Measure.restrict_restrict_of_subset hcl, ← Measure.sum_fintype,
      Measure.restrict_sum_of_countable, Measure.sum_fintype] at h
    refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Measure.restrict_smul, Measure.restrict_restrict isClosed_closure.measurableSet, inter_comm]

end Thesis.MeasureGeometry
