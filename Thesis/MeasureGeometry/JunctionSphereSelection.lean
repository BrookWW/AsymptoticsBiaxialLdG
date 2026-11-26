module

public import Thesis.MeasureGeometry.MeridianTrace
public import Thesis.MeasureGeometry.JunctionGeometry
import Mathlib.Topology.Bases
import Mathlib.Analysis.Convex.Topology

/-! Spherical radius selection away from the actual point singular set. -/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology

namespace Thesis.MeasureGeometry

/-- A set locally finite in an open region, and contained there, is
countable in the actual Euclidean ambient space. -/
theorem locallyFiniteIn_countable {W S : Set Point}
    (hW : IsOpen W) (hSW : S ⊆ W) (hLoc : LocallyFiniteIn W S) : S.Countable := by
  let B := countableBasis Point
  let A := {u : Set Point | u ∈ B ∧ IsCompact (closure u) ∧ closure u ⊆ W}
  have hA : A.Countable := (countable_countableBasis Point).mono fun _ h => h.1
  have hCount : (⋃ u ∈ A, S ∩ u).Countable :=
    hA.biUnion (fun u hu => ((hLoc (closure u) hu.2.1 hu.2.2).subset
      (inter_subset_inter_right S subset_closure)).countable)
  apply hCount.mono
  intro x hx
  obtain ⟨r, hr, hR⟩ := Metric.isOpen_iff.mp hW x (hSW hx)
  let ρ := r / 2
  have hρ : 0 < ρ := half_pos hr
  have hBopen : IsOpen (ball x ρ) := isOpen_ball
  have hxρ : x ∈ ball x ρ := mem_ball_self hρ
  obtain ⟨u, hu, hxu, hSub⟩ := (isBasis_countableBasis Point).exists_subset_of_mem_open hxρ hBopen
  have hc : closure u ⊆ closedBall x ρ := closure_minimal (hSub.trans ball_subset_closedBall) isClosed_closedBall
  have hCu : IsCompact (closure u) := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hc
  have hCW : closure u ⊆ W := hc.trans ((closedBall_subset_ball (by dsimp [ρ]; linarith only [hr])).trans hR)
  exact mem_iUnion₂.mpr ⟨u, ⟨hu, hCu, hCW⟩, ⟨hx, hxu⟩⟩

/-- Any positive interval of radii contains a sphere disjoint from the
same countable point singular set. -/
theorem exists_sphere_disjoint_countable {P : Set Point} (hP : P.Countable) (x : Point)
    {r₀ r₁ : ℝ} (hR : r₀ < r₁) :
    ∃ r ∈ Ioo r₀ r₁, Disjoint (sphere x r) P := by
  let D := (fun y : Point => dist y x) '' P
  have hD : (volume : Measure ℝ) D = 0 := (hP.image _).measure_zero _
  have hMiss : (Ioo r₀ r₁ \ D).Nonempty := by
    by_contra! h
    have hSub : Ioo r₀ r₁ ⊆ D := by
      intro r hr
      by_contra hr'
      have hc : r ∈ Ioo r₀ r₁ \ D := ⟨hr, hr'⟩
      rw [h] at hc
      exact Set.notMem_empty _ hc
    have hV : 0 < (volume : Measure ℝ) (Ioo r₀ r₁) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hR)
    exact hV.not_ge ((measure_mono (μ := volume) hSub).trans_eq hD)
  obtain ⟨r, hr, hrD⟩ := hMiss
  refine ⟨r, hr, disjoint_left.mpr ?_⟩
  intro y hy hyP
  exact hrD ⟨y, hyP, mem_sphere.mp hy⟩

/-- An incident segment cuts the small centered sphere precisely at the
point given by its literal frozen outward direction. -/
theorem incidentSegment_inter_sphere_eq_singleton {m : ℕ} {p q : Fin m → Point} {x : Point}
    (hn : ∀ i, p i ≠ q i) (i : ↥(incidentSegments p q x)) {r : ℝ} (hr : 0 < r)
    (hrL : r < ‖(if x = p i then q i else p i) - x‖) :
    segment ℝ (p i) (q i) ∩ sphere x r = {x + r • outwardDirection p q x i} := by
  let y := if x = p i then q i else p i
  have hSeg : segment ℝ (p i) (q i) = segment ℝ x y := by
    by_cases hx : x = p i
    · simp [y, hx]
    · have hq := ((Finset.mem_filter.mp i.property).2 : x = p i ∨ x = q i).resolve_left hx
      exact (segment_symm ℝ (p i) (q i)).trans (congrArg₂ (segment ℝ) hq.symm (if_neg hx).symm)
  ext z
  constructor
  · rintro ⟨hL, hz⟩
    rw [hSeg, segment_eq_image_lineMap] at hL
    obtain ⟨t, ht, rfl⟩ := hL
    have hPx : dist (AffineMap.lineMap x y t) x = t * ‖y - x‖ := by
      rw [AffineMap.lineMap_apply_module', dist_eq_norm, add_sub_cancel_right, norm_smul,
        Real.norm_of_nonneg ht.1]
    have hR : t * ‖y - x‖ = r := hPx.symm.trans (mem_sphere.mp hz)
    have hNorm : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (incident_otherEndpoint_ne hn i))
    have ht' : t = r / ‖y - x‖ := (eq_div_iff hNorm.ne').2 hR
    apply mem_singleton_iff.mpr
    rw [ht', AffineMap.lineMap_apply_module']
    change (r / ‖y - x‖) • (y - x) + x = x + r • (‖y - x‖⁻¹ • (y - x))
    rw [div_eq_mul_inv, smul_smul, add_comm]
  · intro hz
    rw [mem_singleton_iff.mp hz]
    refine ⟨openSegment_subset_segment ℝ _ _ (openSegment_of_outward_step hn i hr hrL), ?_⟩
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.le, norm_outwardDirection hn i, mul_one]

/-- Small spheres in the chosen interior region meet the finite network
only at the actual outgoing rays incident at the vertex. -/
theorem exists_small_junction_sphere_sections
    {U K S : Set Point} (hK : IsOpen K) (hKU : K ⊆ U)
    {m : ℕ} (p q : Fin m → Point) (hn : ∀ i, p i ≠ q i)
    (hRep : S ∩ closure U = ⋃ i : Fin m, segment ℝ (p i) (q i))
    (hMeet : ∀ i j : Fin m, i ≠ j → ∀ z ∈ segment ℝ (p i) (q i) ∩ segment ℝ (p j) (q j),
      (z = p i ∨ z = q i) ∧ (z = p j ∨ z = q j))
    {x : Point} (hx : x ∈ K) (hInc : (incidentSegments p q x).Nonempty) :
    ∃ R > (0 : ℝ), ∀ {r : ℝ}, r ∈ Ioo 0 R →
      sphere x r ⊆ K ∧ S ∩ sphere x r =
        range (fun i : ↥(incidentSegments p q x) => x + r • outwardDirection p q x i) ∧
        ∀ i : ↥(incidentSegments p q x), r < ‖(if x = p i then q i else p i) - x‖ := by
  classical
  let I := incidentSegments p q x
  let L (i : Fin m) := segment ℝ (p i) (q i)
  let N := ⋃ j : {i : Fin m // i ∉ I}, L j.val
  have hN : IsClosed N := by
    apply isClosed_iUnion_of_finite
    intro j
    have hc : Continuous (fun t : ℝ => AffineMap.lineMap (p j.val) (q j.val) t) := by
      simp_rw [AffineMap.lineMap_apply_module']
      fun_prop
    exact (segment_eq_image_lineMap ℝ (p j.val) (q j.val) ▸ (isCompact_Icc.image hc)).isClosed
  have hxN : x ∉ N := by
    intro h
    obtain ⟨⟨i, hi⟩, hxi⟩ := mem_iUnion.mp h
    obtain ⟨j, hj⟩ := hInc
    have hEnd : x = p j ∨ x = q j := (Finset.mem_filter.mp hj).2
    have hxj : x ∈ L j := hEnd.elim
      (fun h => h.symm ▸ left_mem_segment ℝ (p j) (q j))
      (fun h => h.symm ▸ right_mem_segment ℝ (p j) (q j))
    have hij : i ≠ j := fun he => hi (he.symm ▸ hj)
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hMeet i j hij x ⟨hxi, hxj⟩).1⟩)
  obtain ⟨rK, hrK, hBall⟩ := Metric.isOpen_iff.mp (hK.inter hN.isOpen_compl) x ⟨hx, hxN⟩
  let len (i : ↥I) := ‖(if x = p i then q i else p i) - x‖
  have hLen (i : ↥I) : 0 < len i :=
    norm_pos_iff.2 (sub_ne_zero.2 (incident_otherEndpoint_ne hn i))
  let A := Finset.univ.image len
  have hA : A.Nonempty := by
    obtain ⟨i, hi⟩ := hInc
    exact ⟨len ⟨i, hi⟩, Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩⟩
  let d := A.min' hA
  have hd : 0 < d := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem A hA)
    exact (hLen i).trans_eq hi
  have hdL (i : ↥I) : d ≤ len i := Finset.min'_le A _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  refine ⟨min rK d, lt_min hrK hd, ?_⟩
  intro r hr
  have hRK : r < rK := hr.2.trans_le (min_le_left _ _)
  have hRL (i : ↥I) : r < len i := hr.2.trans_le ((min_le_right _ _).trans (hdL i))
  have hsph : sphere x r ⊆ K ∩ Nᶜ := (sphere_subset_ball hRK).trans hBall
  refine ⟨hsph.trans inter_subset_left, ?_, hRL⟩
  ext z
  constructor
  · rintro ⟨hS, hz⟩
    have hzU : z ∈ U := hKU (hsph hz).1
    have hL : z ∈ ⋃ i, L i := hRep ▸ ⟨hS, subset_closure hzU⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hL
    have hI : i ∈ I := by
      by_contra h
      exact (hsph hz).2 (mem_iUnion.mpr ⟨⟨i,h⟩, hi⟩)
    let j : ↥I := ⟨i,hI⟩
    have hEq := incidentSegment_inter_sphere_eq_singleton hn j hr.1 (hRL j)
    exact ⟨j, (mem_singleton_iff.mp (hEq ▸ ⟨hi,hz⟩)).symm⟩
  · rintro ⟨i, rfl⟩
    have hi := incidentSegment_inter_sphere_eq_singleton hn i hr.1 (hRL i)
    have h : x + r • outwardDirection p q x i ∈ L i ∩ sphere x r :=
      hi.symm ▸ mem_singleton _
    have hU : x + r • outwardDirection p q x i ∈ U := hKU (hsph h.2).1
    have hS : x + r • outwardDirection p q x i ∈ S ∩ closure U :=
       hRep.symm ▸ mem_iUnion.mpr ⟨i.val, h.1⟩
    exact ⟨hS.1, h.2⟩

end Thesis.MeasureGeometry
