module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! Absolute continuity under interval reparametrization and pasting. -/

public section

noncomputable section

open Metric Set
open scoped NNReal Topology

namespace Thesis

private theorem maps_disjoint_uIoc_of_monotoneOn
    {g : ℝ → ℝ} {S : Set ℝ} {x y z w : ℝ}
    (hg : MonotoneOn g S ∨ AntitoneOn g S) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hw : w ∈ S)
    (h : Disjoint (uIoc x y) (uIoc z w)) :
    Disjoint (uIoc (g x) (g y)) (uIoc (g z) (g w)) := by
  have hMin {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) : min a b ∈ S := by
    rcases le_total a b with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h]
  have hMax {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) : max a b ∈ S := by
    rcases le_total a b with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  have hLe : min (max x y) (max z w) ≤ max (min x y) (min z w) :=
    Ioc_disjoint_Ioc.mp h
  apply Ioc_disjoint_Ioc.mpr
  rcases hg with hm | hm
  · have hh := hm (hMin (hMax hx hy) (hMax hz hw)) (hMax (hMin hx hy) (hMin hz hw)) hLe
    rw [hm.map_min (hMax hx hy) (hMax hz hw), hm.map_max (hMin hx hy) (hMin hz hw),
      hm.map_max hx hy, hm.map_max hz hw, hm.map_min hx hy, hm.map_min hz hw] at hh
    exact hh
  · have hh := hm (hMin (hMax hx hy) (hMax hz hw)) (hMax (hMin hx hy) (hMin hz hw)) hLe
    rw [hm.map_min (hMax hx hy) (hMax hz hw), hm.map_max (hMin hx hy) (hMin hz hw),
      hm.map_max hx hy, hm.map_max hz hw, hm.map_min hx hy, hm.map_min hz hw] at hh
    exact hh

/-- An absolutely continuous map has the same property after a
Lipschitz monotone or antitone reparametrization of its closed interval. -/
theorem absolutelyContinuousOnInterval_comp_monotoneOn
    {E : Type*} [PseudoMetricSpace E] {f : ℝ → E} {g : ℝ → ℝ} {a b c d : ℝ} {L : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f c d) (hg : MapsTo g (uIcc a b) (uIcc c d))
    (hLip : LipschitzOnWith L g (uIcc a b))
    (hMono : MonotoneOn g (uIcc a b) ∨ AntitoneOn g (uIcc a b)) :
    AbsolutelyContinuousOnInterval (f ∘ g) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ,hδ,hControl⟩ := hf ε hε
  have hL : 0 < (L : ℝ)+1 := by positivity
  refine ⟨δ/((L : ℝ)+1),div_pos hδ hL,?_⟩
  intro J hJ hSmall
  let K : ℕ × (ℕ → ℝ × ℝ) := (J.1,fun i => (g (J.2 i).1,g (J.2 i).2))
  have hK : K ∈ AbsolutelyContinuousOnInterval.disjWithin c d := by
    refine ⟨fun i hi => ⟨hg (hJ.1 i hi).1,hg (hJ.1 i hi).2⟩,?_⟩
    intro i hi j hj hij
    exact maps_disjoint_uIoc_of_monotoneOn hMono (hJ.1 i hi).1 (hJ.1 i hi).2
      (hJ.1 j hj).1 (hJ.1 j hj).2 (hJ.2 hi hj hij)
  have hKSmall : (∑ i ∈ Finset.range K.1, dist (K.2 i).1 (K.2 i).2) < δ := by
    apply lt_of_le_of_lt ?_ ((lt_div_iff₀' hL).mp hSmall)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := hLip.dist_le_mul _ (hJ.1 i hi).1 _ (hJ.1 i hi).2
    exact h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg)
  exact hControl K hK hKSmall

theorem absolutelyContinuousOnInterval_congr {E : Type*} [PseudoMetricSpace E]
    {f g : ℝ → E} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (he : EqOn f g (uIcc a b)) : AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ,hδ,hE⟩ := hf ε hε
  refine ⟨δ,hδ, fun J hJ hSmall => ?_⟩
  have hEq : (∑ i ∈ Finset.range J.1, dist (g (J.2 i).1) (g (J.2 i).2)) =
      ∑ i ∈ Finset.range J.1, dist (f (J.2 i).1) (f (J.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← he (hJ.1 i hi).1, ← he (hJ.1 i hi).2]
  rw [hEq]
  exact hE J hJ hSmall

/-- Absolute continuity on two adjacent closed intervals gives the same
regularity on their concatenation. -/
theorem absolutelyContinuousOnInterval_of_adjacent
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hLeft : AbsolutelyContinuousOnInterval f a b)
    (hRight : AbsolutelyContinuousOnInterval f b c) : AbsolutelyContinuousOnInterval f a c := by
  let l (x : ℝ) := min x b
  let r (x : ℝ) := max x b
  have hLmap : MapsTo l (uIcc a c) (uIcc a b) := by
    rw [uIcc_of_le (hab.trans hbc),uIcc_of_le hab]
    exact fun x hx => ⟨le_min hx.1 hab,min_le_right x b⟩
  have hRmap : MapsTo r (uIcc a c) (uIcc b c) := by
    rw [uIcc_of_le (hab.trans hbc),uIcc_of_le hbc]
    exact fun x hx => ⟨le_max_right x b,max_le hx.2 hbc⟩
  have hLl : LipschitzWith 1 l := LipschitzWith.id.min_const b
  have hRl : LipschitzWith 1 r := LipschitzWith.id.max_const b
  have hl : Monotone l := fun _ _ h => min_le_min h le_rfl
  have hr : Monotone r := fun _ _ h => max_le_max h le_rfl
  have hL := absolutelyContinuousOnInterval_comp_monotoneOn hLeft hLmap hLl.lipschitzOnWith
    (Or.inl (hl.monotoneOn _))
  have hR := absolutelyContinuousOnInterval_comp_monotoneOn hRight hRmap hRl.lipschitzOnWith
    (Or.inl (hr.monotoneOn _))
  have hCl : LipschitzOnWith 0 (fun _ : ℝ => f b) (uIcc a c) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp
  have hC := hCl.absolutelyContinuousOnInterval
  apply absolutelyContinuousOnInterval_congr ((hL.add hR).sub hC)
  intro x _
  change f (min x b) + f (max x b) - f b = f x
  rcases le_total x b with h | h
  · rw [min_eq_left h, max_eq_right h, add_sub_cancel_right]
  · rw [min_eq_right h, max_eq_left h, add_sub_cancel_left]

theorem absolutelyContinuousOnInterval_comp_add_right
    {E : Type*} [PseudoMetricSpace E] {f : ℝ → E} {a b s : ℝ} (h : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f (a+s) (b+s)) :
    AbsolutelyContinuousOnInterval (fun x => f (x+s)) a b := by
  let g (x : ℝ) := x+s
  have hMap : MapsTo g (uIcc a b) (uIcc (a+s) (b+s)) := by
    rw [uIcc_of_le h,uIcc_of_le (add_le_add_left h s)]
    exact fun x hx => ⟨add_le_add_left hx.1 s,add_le_add_left hx.2 s⟩
  have hLip : LipschitzOnWith 1 g (uIcc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x _ y _
    rw [NNReal.coe_one,one_mul,Real.dist_eq,Real.dist_eq]
    dsimp only [g]
    rw [add_sub_add_right_eq_sub]
  have hMono : Monotone g := fun _ _ hxy => add_le_add_left hxy s
  exact absolutelyContinuousOnInterval_comp_monotoneOn hf hMap hLip (Or.inl (hMono.monotoneOn _))

end Thesis
