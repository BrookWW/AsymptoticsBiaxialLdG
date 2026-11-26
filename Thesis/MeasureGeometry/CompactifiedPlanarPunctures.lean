module

public import Thesis.MeasureGeometry.PlanarStripPartition

/-! The vanishing sum of peripheral light characters on the punctured
compactified plane. -/

public section

noncomputable section

open Metric OnePoint Set
open scoped BigOperators Topology

namespace Thesis.MeasureGeometry

/-- The one-point compactification of the plane with the indicated finite
points removed. -/
@[expose] def compactifiedPlanarPunctures {n : ℕ} (p : Fin n → ℝ × ℝ) :
    Set (OnePoint (ℝ × ℝ)) :=
  (range fun i => (p i : OnePoint (ℝ × ℝ)))ᶜ

private theorem exists_strip_circle_radius
    {l r b t : ℝ} (z : ℝ × ℝ) (hx : z.1 ∈ Ioo l r) (hy : z.2 ∈ Ioo b t) :
    ∃ δ > (0 : ℝ), l ≤ z.1-δ ∧ z.1+δ ≤ r ∧ b ≤ z.2-δ ∧ z.2+δ ≤ t := by
  let c := min (min (z.1-l) (r-z.1)) (min (z.2-b) (t-z.2))
  have hc : 0 < c := lt_min (lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2))
    (lt_min (sub_pos.mpr hy.1) (sub_pos.mpr hy.2))
  have hc₀ : c ≤ z.1-l := (min_le_left _ _).trans (min_le_left _ _)
  have hc₁ : c ≤ r-z.1 := (min_le_left _ _).trans (min_le_right _ _)
  have hc₂ : c ≤ z.2-b := (min_le_right _ _).trans (min_le_left _ _)
  have hc₃ : c ≤ t-z.2 := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨c/2,half_pos hc,by linarith only [hc,hc₀],by linarith only [hc,hc₁],
    by linarith only [hc,hc₂],by linarith only [hc,hc₃]⟩

/-- Around each ordered puncture there is an actual circular trace, with
the surrounding disk meeting the punctures only at its center. The sum of
the light indicators of these traces is zero modulo two. -/
theorem exists_compactifiedPlanarPeripheralCircles {a : BulkCoefficients} (v : Sphere3)
    {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ × ℝ)
    (hp : StrictMono (fun i => (p i).1))
    (Q : C(compactifiedPlanarPunctures p,vacuum a)) :
    ∃ (δ : Fin n → ℝ) (b : Fin n → C(NativeCircle,vacuum a)),
      (∀ i, 0 < δ i) ∧
      (∀ (i j : Fin n) (z : Plane), z ∈ Disk →
        p i + δ i • planePairCoordinates z = p j → j = i ∧ z = 0) ∧
      (∀ (i : Fin n) (θ : NativeCircle),
        ∃ h : (planarPairCirclePoint (p i) (δ i) θ : OnePoint (ℝ × ℝ)) ∈ compactifiedPlanarPunctures p,
          b i θ = Q ⟨_,h⟩) ∧
      (∑ i, if nativeVacuumCircleCost a (b i) = kappaStar a then (1 : ZMod 2) else 0) = 0 := by
  classical
  obtain ⟨A,x,hA,hx₀,hxN,hx,hA_bound,hSep⟩ := exists_ordered_planar_strips hn p hp
  obtain ⟨hNoSide,hOnly⟩ := ordered_planar_strips_separate p x hx hSep
  let W := compactifiedPlanarPunctures p
  let U := {z : ℝ × ℝ | (z : OnePoint (ℝ × ℝ)) ∈ W}
  let Q₀ : C(U,vacuum a) := compactifiedPlaneRestriction Q
  have hA_y (i : Fin n) : (p i).2 ∈ Ioo (-A) A := by
    apply abs_lt.mp
    change ‖(p i).2‖ < A
    exact (norm_snd_le (p i)).trans_lt (hA_bound i)
  have hNoInf : (∞ : OnePoint (ℝ × ℝ)) ∈ W := by
    rintro ⟨i,h⟩
    exact OnePoint.coe_ne_infty (p i) h
  have hOutside (z : ℝ × ℝ) (h : A ≤ ‖z‖) : z ∈ U := by
    rintro ⟨j,he⟩
    have he' : p j = z := OnePoint.coe_injective he
    exact (not_lt_of_ge h) (he' ▸ hA_bound j)
  have hTop (y : ℝ) : (y,A) ∈ U := hOutside _ (by
    change A ≤ max |y| |A|
    rw [abs_of_pos hA]
    exact le_max_right _ _)
  have hBottom (y : ℝ) : (y,-A) ∈ U := hOutside _ (by
    change A ≤ max |y| |-A|
    rw [abs_neg,abs_of_pos hA]
    exact le_max_right _ _)
  have hSides (i : ℕ) (y : ℝ) (_ : y ∈ Icc (-A) A) : (x i,y) ∈ U := by
    rintro ⟨j,he⟩
    exact hNoSide i j (congrArg Prod.fst (OnePoint.coe_injective he)).symm
  have hBox (i : Fin n) : (Icc (x i.val) (x (i.val+1)) ×ˢ Icc (-A) A) \ {p i} ⊆ U := by
    rintro y ⟨hy,hy'⟩ ⟨j,hj⟩
    have hE : p j = y := OnePoint.coe_injective hj
    have hIndex : i = j := hOnly i j (hE.symm ▸ hy.1)
    exact hy' (mem_singleton_iff.mpr (hE.symm.trans (congrArg p hIndex).symm))
  choose δ hδ hL hR hB hT using fun i : Fin n =>
    exists_strip_circle_radius (p i) (hSep i) (hA_y i)
  have hDisk (i j : Fin n) (z : Plane) (hz : z ∈ Disk)
      (h : p i + δ i • planePairCoordinates z = p j) : j = i ∧ z = 0 := by
    have hMem := planarPairDiskPoint_mem_box (p i) (hδ i).le (hL i) (hR i) (hB i) (hT i)
      z (mem_closedBall_zero_iff.mp hz)
    rw [h] at hMem
    have hi : j = i := (hOnly i j hMem.1).symm
    refine ⟨hi,?_⟩
    have hEq : δ i • planePairCoordinates z = 0 := by
      have hEq : p i + δ i • planePairCoordinates z = p i + 0 := by rw [h,hi,add_zero]
      exact add_left_cancel hEq
    apply planePairCoordinates.injective
    rw [map_zero]
    exact (smul_eq_zero.mp hEq).resolve_left (hδ i).ne'
  have hCirc (i : Fin n) (θ : NativeCircle) : (planarPairCirclePoint (p i) (δ i) θ : OnePoint (ℝ × ℝ)) ∈ W :=
    hBox i ⟨planarPairCirclePoint_mem_box (p i) (hδ i).le (hL i) (hR i) (hB i) (hT i) θ,
      fun h => planarPairCirclePoint_ne_center _ (hδ i).ne' θ (mem_singleton_iff.mp h)⟩
  let b (i : Fin n) : C(NativeCircle,vacuum a) :=
    ⟨fun θ => Q ⟨_,hCirc i θ⟩,Q.continuous.comp
      ((OnePoint.continuous_coe.comp (continuous_planarPairCirclePoint (p i) (δ i))).subtype_mk _)⟩
  refine ⟨δ,b,hδ,hDisk,fun i θ => ⟨hCirc i θ,rfl⟩,?_⟩
  have hBA : -A ≤ A := by linarith only [hA]
  let P (i : ℕ) := rectangularPerimeter (x i) (x (i+1)) (-A) A
  have hP (i : ℕ) : ∀ s, P i s ∈ U :=
    rectangularPerimeter_mem_from_sides hBA hTop hBottom (hSides i) (hSides (i+1))
  let w (i : ℕ) := vacuumPathLightParity a v (mappedPathOn Q₀ (P i) (hP i))
  have hCircleEq (i : Fin n) : w i.val =
      if nativeVacuumCircleCost a (b i) = kappaStar a then 1 else 0 := by
    rw [← vacuumPathLightParity_nativeCircleLoop]
    exact rectangularLightParity_eq_circle v Q₀ (p i) (hSep i) (hA_y i) (hBox i)
      (hδ i) (hL i) (hR i) (hB i) (hT i) (hP i.val)
  have hOut {l r : ℝ} (hl : l = -A) (hr : r = A)
      (h : ∀ s, rectangularPerimeter l r (-A) A s ∈ U) :
      vacuumPathLightParity a v (mappedPathOn Q₀ (rectangularPerimeter l r (-A) A) h) = 0 := by
    subst l r
    exact rectangularLightParity_zero_of_compactified v Q hA hNoInf hOutside h
  have hw := rectangularLightParity_sum_strips v Q₀ x hx hBA hTop hBottom hSides n
  have hSumRange : (∑ i ∈ Finset.range n, w i) = 0 := hw.trans
    (hOut hx₀ hxN (rectangularPerimeter_mem_from_sides hBA hTop hBottom (hSides 0) (hSides n)))
  calc
    _ = ∑ i : Fin n, w i.val := Finset.sum_congr rfl (fun i _ => (hCircleEq i).symm)
    _ = ∑ i ∈ Finset.range n, w i := Fin.sum_univ_eq_sum_range w n
    _ = 0 := hSumRange

end Thesis.MeasureGeometry
