module

public import Thesis.MeasureGeometry.WeightedSegmentNetwork
public import Thesis.MeasureGeometry.SegmentFlux
public import Thesis.MeasureGeometry.MeridianCoordinates

/-! The local support and weight at an interior point of an actual segment. -/

public section

noncomputable section

open Metric Set MeasureTheory
open scoped ENNReal

namespace Thesis.MeasureGeometry

/-- The affine line through an interior point of a nondegenerate segment
agrees with that segment on a ball about the point. -/
theorem exists_ball_segment_eq_affineAxis {p q x : Point} (hpq : p ≠ q)
    (hx : x ∈ openSegment ℝ p q) :
    ∃ R > 0, ∀ z ∈ ball x R, z ∈ segment ℝ p q ↔
      z ∈ (fun y : Point => x + y) ''
        ((Submodule.span ℝ {segmentDirection p q} : Submodule ℝ Point) : Set Point) := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  let L := ‖q-p‖
  have hL : 0 < L := norm_pos_iff.mpr (sub_ne_zero.mpr hpq.symm)
  let R := L * min u (1-u)
  have hR : 0 < R := mul_pos hL (lt_min hu.1 (sub_pos.mpr hu.2))
  let x := AffineMap.lineMap p q u
  let v := segmentDirection p q
  have hV : L • v = q-p := by
    change L • (L⁻¹ • (q-p)) = q-p
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hLine (t : ℝ) : AffineMap.lineMap p q t = p + t • (q-p) := by
    rw [AffineMap.lineMap_apply_module]
    module
  have hTranslate (t : ℝ) : x + t • v = AffineMap.lineMap p q (u + t/L) := by
    rw [hLine, show x = p + u • (q-p) from hLine u, ← hV, add_smul,
      smul_smul (t/L) L, div_mul_cancel₀ _ hL.ne']
    module
  refine ⟨R,hR,?_⟩
  intro z hz
  constructor
  · intro hzS
    rw [segment_eq_image_lineMap] at hzS
    obtain ⟨t, ht, rfl⟩ := hzS
    refine ⟨((t-u)*L) • v, Submodule.smul_mem _ _ (Submodule.subset_span (mem_singleton v)), ?_⟩
    change x + ((t-u)*L) • v = AffineMap.lineMap p q t
    rw [hTranslate, mul_div_cancel_right₀ _ hL.ne']
    congr 1
    ring
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
    change x + t • v ∈ segment ℝ p q
    change x + t • v ∈ ball x R at hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_segmentDirection hpq,
      mul_one, Real.norm_eq_abs] at hz
    have ht : -(L*u) < t ∧ t < L*(1-u) := by
      have h₁ := mul_le_mul_of_nonneg_left (min_le_left u (1-u)) hL.le
      have h₂ := mul_le_mul_of_nonneg_left (min_le_right u (1-u)) hL.le
      exact ⟨(neg_le_neg h₁).trans_lt (abs_lt.mp hz).1, (abs_lt.mp hz).2.trans_le h₂⟩
    have htu : u + t/L ∈ Icc (0 : ℝ) 1 := by
      have h0 : -u < t/L := (lt_div_iff₀ hL).mpr (by nlinarith only [ht.1])
      have h1 : t/L < 1-u := (div_lt_iff₀ hL).mpr (by nlinarith only [ht.2])
      exact ⟨by linarith only [h0], by linarith only [h1]⟩
    rw [hTranslate, segment_eq_image_lineMap]
    exact mem_image_of_mem _ htu

/-- Near an open-segment point the original measure and support come from
the same constant weight on that segment's full affine axis. -/
theorem exists_ball_localWeightedAxis_of_segmentNetwork
    {K U S : Set Point} {μ : Measure Point} (hK : IsOpen K) (hKU : K ⊆ U)
    {m : ℕ} {p q : Fin m → Point} {θ : Fin m → ℝ}
    (hS : S ∩ closure U = ⋃ j, segment ℝ (p j) (q j))
    (hn : ∀ j, p j ≠ q j)
    (hMeet : ∀ i j : Fin m, i ≠ j → ∀ z ∈ segment ℝ (p i) (q i) ∩ segment ℝ (p j) (q j),
      (z = p i ∨ z = q i) ∧ (z = p j ∨ z = q j))
    (hμ : μ.restrict (closure K) = ∑ j, ENNReal.ofReal (θ j) •
      HausdorffOne.restrict (segment ℝ (p j) (q j) ∩ closure K))
    (i : Fin m) {x : Point} (hxK : x ∈ K) (hx : x ∈ openSegment ℝ (p i) (q i)) :
    ∃ R > 0, ball x R ⊆ K ∧
      (∀ z ∈ ball x R, z ∈ S ↔ z ∈ (fun y : Point => x+y) ''
        ((Submodule.span ℝ {segmentDirection (p i) (q i)} : Submodule ℝ Point) : Set Point)) ∧
      μ.restrict (ball x R) = (ENNReal.ofReal (θ i) • HausdorffOne.restrict
        ((fun y : Point => x+y) ''
          ((Submodule.span ℝ {segmentDirection (p i) (q i)} : Submodule ℝ Point) : Set Point))).restrict
            (ball x R) := by
  classical
  let L (j : Fin m) := segment ℝ (p j) (q j)
  let A := (fun y : Point => x+y) ''
    ((Submodule.span ℝ {segmentDirection (p i) (q i)} : Submodule ℝ Point) : Set Point)
  let W := K \ ⋃ j : {j : Fin m // j ≠ i}, L j
  have hW : IsOpen W := hK.sdiff (isClosed_iUnion_of_finite fun j => (isCompact_tensorSegment _ _).isClosed)
  have hxL : x ∈ L i := openSegment_subset_segment ℝ _ _ hx
  have hxW : x ∈ W := by
    refine ⟨hxK, ?_⟩
    intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    rcases (hMeet i j.val (Ne.symm j.property) x ⟨hxL,hj⟩).1 with h | h
    · exact hn i (left_mem_openSegment_iff.mp (h ▸ hx))
    · exact hn i (right_mem_openSegment_iff.mp (h ▸ hx))
  obtain ⟨R₁,hR₁,hB₁⟩ := Metric.isOpen_iff.mp hW x hxW
  obtain ⟨R₂,hR₂,hB₂⟩ := exists_ball_segment_eq_affineAxis (hn i) hx
  let R := min R₁ R₂
  have hR : 0 < R := lt_min hR₁ hR₂
  have hBW : ball x R ⊆ W := (ball_subset_ball (min_le_left _ _)).trans hB₁
  have hBK : ball x R ⊆ K := hBW.trans sdiff_subset
  have hBA {z : Point} (hz : z ∈ ball x R) : z ∈ L i ↔ z ∈ A :=
    hB₂ z (ball_subset_ball (min_le_right _ _) hz)
  have hAvoid {j : Fin m} (hj : j ≠ i) {z : Point} (hz : z ∈ ball x R) : z ∉ L j :=
    fun h => (hBW hz).2 (mem_iUnion.mpr ⟨⟨j,hj⟩,h⟩)
  refine ⟨R,hR,hBK,?_,?_⟩
  · intro z hz
    have hzU : z ∈ closure U := subset_closure (hKU (hBK hz))
    rw [← hBA hz]
    constructor
    · intro h
      have h' : z ∈ ⋃ j, L j := hS ▸ (show z ∈ S ∩ closure U from ⟨h,hzU⟩)
      obtain ⟨j,hj⟩ := mem_iUnion.mp h'
      by_cases e : j = i
      · exact e ▸ hj
      · exact (hAvoid e hz hj).elim
    · intro h
      exact ((show z ∈ S ∩ closure U from hS.symm ▸ mem_iUnion.mpr ⟨i,h⟩)).1
  · change μ.restrict (ball x R) = (ENNReal.ofReal (θ i) • HausdorffOne.restrict A).restrict (ball x R)
    rw [← Measure.restrict_restrict_of_subset (hBK.trans subset_closure), hμ]
    ext D hD
    have hM : MeasurableSet (D ∩ ball x R) := hD.inter measurableSet_ball
    simp only [Measure.restrict_apply hD, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.restrict_apply hM]
    rw [Finset.sum_eq_single i]
    · have hSet : (D ∩ ball x R) ∩ (L i ∩ closure K) = (D ∩ ball x R) ∩ A := by
        ext z
        constructor
        · rintro ⟨⟨hzD,hzB⟩,hzL,_⟩
          exact ⟨⟨hzD,hzB⟩,(hBA hzB).mp hzL⟩
        · rintro ⟨⟨hzD,hzB⟩,hzA⟩
          exact ⟨⟨hzD,hzB⟩,(hBA hzB).mpr hzA,subset_closure (hBK hzB)⟩
      change ENNReal.ofReal (θ i) • HausdorffOne ((D ∩ ball x R) ∩ (L i ∩ closure K)) =
        ENNReal.ofReal (θ i) • HausdorffOne ((D ∩ ball x R) ∩ A)
      rw [hSet]
    · intro j _ hji
      have hEmpty : (D ∩ ball x R) ∩ (L j ∩ closure K) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        exact fun z hz => hAvoid hji hz.1.2 hz.2.1
      change ENNReal.ofReal (θ j) • HausdorffOne ((D ∩ ball x R) ∩ (L j ∩ closure K)) = 0
      rw [hEmpty, measure_empty, smul_zero]
    · simp

end Thesis.MeasureGeometry
