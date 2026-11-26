module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Disjoint fivefold selection and its measure packing bound. -/

public section

open Set Metric MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace SupportingAnalysis

section Selection

variable {X ι : Type*} [PseudoMetricSpace X] [SeparableSpace X]

/-- A bounded-radius family admits a countable disjoint subfamily whose fivefold open balls
cover the original union. Balls of nonpositive radius can be discarded. -/
theorem exists_fivefold_disjoint_subfamily (I : Set ι) (x : ι → X) (r : ι → ℝ)
    {R : ℝ} (hr : ∀ i ∈ I, r i ≤ R) :
    ∃ J ⊆ I, J.Countable ∧ (∀ j ∈ J, 0 < r j) ∧
      J.PairwiseDisjoint (fun j => ball (x j) (r j)) ∧
      (⋃ i ∈ I, ball (x i) (r i)) ⊆ ⋃ j ∈ J, ball (x j) (5 * r j) := by
  let Ipos : Set ι := {i ∈ I | 0 < r i}
  obtain ⟨J, hJI, hd, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball Ipos x r R
      (fun i hi => hr i hi.1) 5 (by norm_num)
  have hjpos (j : ι) (hj : j ∈ J) : 0 < r j := (hJI hj).2
  have hJcount := hd.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun j hj => ⟨x j, mem_ball_self (hjpos j hj)⟩)
  refine ⟨J, fun j hj => (hJI hj).1, hJcount, hjpos, hd, ?_⟩
  intro y hy
  obtain ⟨i, hi, hiy⟩ := mem_iUnion₂.1 hy
  have hir : 0 < r i := (dist_nonneg (x := y) (y := x i)).trans_lt (mem_ball.1 hiy)
  obtain ⟨j, hj, hij⟩ := hcover i ⟨hi, hir⟩
  exact mem_iUnion₂.2 ⟨j, hj, hij hiy⟩

end Selection

section Packing

variable {X ι : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Disjoint balls with lower density `c (s / κ)^d` inside a finite-mass set spend
at most `κ^d / c` times the ambient mass, over the entire selected family. -/
theorem summable_radius_pow_of_disjoint_ball_lower_bound
    (μ : Measure X) (U : Set X) {J : Set ι} (x : ι → X) (s : ι → ℝ) (d : ℕ)
    {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hU : μ U ≠ ⊤)
    (hs : ∀ i ∈ J, 0 ≤ s i)
    (hdisj : J.PairwiseDisjoint (fun i => ball (x i) (s i / κ)))
    (hsub : ∀ i ∈ J, ball (x i) (s i / κ) ⊆ U)
    (hlow : ∀ i ∈ J, ENNReal.ofReal (c * (s i / κ) ^ d) ≤ μ (ball (x i) (s i / κ))) :
    Summable (fun i : J => s i ^ d) ∧
      (∑' i : J, s i ^ d) ≤ κ ^ d / c * (μ U).toReal := by
  classical
  let B : J → Set X := fun i => ball (x i) (s i / κ)
  have hdisjB : PairwiseDisjoint (univ : Set J) B :=
    fun i _ j _ hij => hdisj i.2 j.2 (fun h => hij (Subtype.ext h))
  have hfin (i : J) : μ (B i) ≠ ⊤ :=
    ne_top_of_le_ne_top hU (measure_mono (hsub i i.2))
  have hterm (i : J) : c * (s i / κ) ^ d ≤ (μ (B i)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (hfin i)).1 (hlow i i.2)
  have hbudget (t : Finset J) : (∑ i ∈ t, s i ^ d) ≤ κ ^ d / c * (μ U).toReal := by
    have hμsum : ∑ i ∈ t, μ (B i) ≤ μ U := by
      rw [← measure_biUnion_finset (μ := μ) (s := t) (f := B) (fun i _ j _ hij => hdisjB (mem_univ i) (mem_univ j) hij)
        (fun _ _ => measurableSet_ball)]
      exact measure_mono (iUnion₂_subset (fun i _ => hsub i i.2))
    have hreal : (∑ i ∈ t, (μ (B i)).toReal) ≤ (μ U).toReal := by
      rw [← ENNReal.toReal_sum (fun i _ => hfin i)]
      exact ENNReal.toReal_mono hU hμsum
    have hpartial : (∑ i ∈ t, (s i / κ) ^ d) ≤ (μ U).toReal / c := by
      apply (le_div_iff₀ hc).2
      rw [mul_comm, Finset.mul_sum]
      exact (Finset.sum_le_sum fun i _ => hterm i).trans hreal
    calc
      _ = κ ^ d * ∑ i ∈ t, (s i / κ) ^ d := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_pow, mul_div_cancel₀ _ hκ.ne']
      _ ≤ κ ^ d * ((μ U).toReal / c) :=
        mul_le_mul_of_nonneg_left hpartial (pow_nonneg hκ.le _)
      _ = _ := by ring
  exact ⟨summable_of_sum_le (fun i => pow_nonneg (hs i i.2) _) hbudget,
    Real.tsum_le_of_sum_le (fun i => pow_nonneg (hs i i.2) _) hbudget⟩

end Packing

section Window

variable {X : Type*} [PseudoMetricSpace X] [SeparableSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Fivefold selection for admissible symmetric windows, with the radius sum needed for
the good-ball family. Each retained center comes with its original admissible window. -/
theorem exists_symmetric_window_cover_with_radius_budget
    (μ : Measure X) (U G : Set X) (d : ℕ) (adm : X → ℝ → Prop)
    {ρ c : ℝ} (hc : 0 < c) (hU : μ U ≠ ⊤)
    (hgood : ∀ x ∈ G, ∃ s : ℝ, 0 < s ∧ s < ρ ∧ adm x s ∧ ball x (s / 10) ⊆ U ∧
      ENNReal.ofReal (c * (s / 10) ^ d) ≤ μ (ball x (s / 10))) :
    ∃ (s : G → ℝ) (J : Set G), J.Countable ∧
      (∀ j ∈ J, 0 < s j ∧ s j < ρ ∧ adm j (s j)) ∧
      J.PairwiseDisjoint (fun j => ball (j : X) (s j / 10)) ∧
      G ⊆ (⋃ j ∈ J, ball (j : X) (s j / 2)) ∧
      Summable (fun j : J => s j ^ d) ∧
      (∑' j : J, s j ^ d) ≤ (10 : ℝ) ^ d / c * (μ U).toReal := by
  have hwitness (x : G) := hgood x x.2
  choose s hs hr hadm hsub hmass using hwitness
  obtain ⟨J, _, hJ, _, hd, hcover⟩ :=
    exists_fivefold_disjoint_subfamily (univ : Set G) Subtype.val (fun j => s j / 10)
      (R := ρ / 10) (fun j _ => div_le_div_of_nonneg_right (hr j).le (by norm_num))
  obtain ⟨hSummable, hbudget⟩ :=
    summable_radius_pow_of_disjoint_ball_lower_bound μ U Subtype.val s d
      (by norm_num : (0 : ℝ) < 10) hc hU (fun i _ => (hs i).le) hd
      (fun i _ => hsub i) (fun i _ => hmass i)
  refine ⟨s, J, hJ, fun j _ => ⟨hs j, hr j, hadm j⟩, hd, ?_, hSummable, hbudget⟩
  intro y hy
  let i : G := ⟨y, hy⟩
  have hyball : y ∈ ball (i : X) (s i / 10) :=
    mem_ball_self (div_pos (hs i) (by norm_num))
  have hycover := hcover (mem_iUnion₂.2 ⟨i, mem_univ _, hyball⟩)
  obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.1 hycover
  refine mem_iUnion₂.2 ⟨j, hj, ?_⟩
  rwa [show s j / 2 = 5 * (s j / 10) by ring]

end Window

end SupportingAnalysis
