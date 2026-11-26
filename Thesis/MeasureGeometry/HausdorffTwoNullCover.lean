module

public import Thesis.Definitions
public import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Finite small-radius covers of compact surface-null sets. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace Thesis

private theorem hausdorffTwo_eq_zero_of_euclidean_eq_zero {K : Set Point}
    (hK : Measure.euclideanHausdorffMeasure 2 K = 0) : Measure.hausdorffMeasure 2 K = 0 := by
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.nnreal_smul_coe_apply,
    mul_eq_zero] at hK
  apply hK.resolve_left
  have h := Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero 2
  with_unfolding_all exact ENNReal.coe_ne_zero.mpr h

private theorem exists_countable_cover_ediam_sq {K : Set Point}
    (hK : Measure.hausdorffMeasure 2 K = 0) {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∃ T : ℕ → Set Point, K ⊆ ⋃ n, T n ∧
      (∀ n, ediam (T n) ≤ ENNReal.ofReal R) ∧ ∑' n, ediam (T n) ^ (2 : ℕ) < ENNReal.ofReal η := by
  let u := ENNReal.ofReal R
  have hu : 0 < u := ENNReal.ofReal_pos.mpr hR
  have hSmall :
      (⨅ (T : ℕ → Set Point) (_ : K ⊆ ⋃ n, T n) (_ : ∀ n, ediam (T n) ≤ u),
          ∑' n, ⨆ _ : (T n).Nonempty, ediam (T n) ^ (2 : ℝ)) < ENNReal.ofReal η := by
    have hLe :
        (⨅ (T : ℕ → Set Point) (_ : K ⊆ ⋃ n, T n) (_ : ∀ n, ediam (T n) ≤ u),
          ∑' n, ⨆ _ : (T n).Nonempty, ediam (T n) ^ (2 : ℝ)) ≤
          Measure.hausdorffMeasure 2 K := by
      rw [Measure.hausdorffMeasure_apply]
      exact le_iSup_of_le u (le_iSup_of_le hu le_rfl)
    exact hLe.trans_lt (hK ▸ ENNReal.ofReal_pos.mpr hη)
  obtain ⟨T,hT,hTu,hTs⟩ := by
    simpa only [iInf_lt_iff, exists_prop] using hSmall
  refine ⟨T,hT,hTu,?_⟩
  have hEq (n : ℕ) : (⨆ _ : (T n).Nonempty, ediam (T n) ^ (2 : ℝ)) = ediam (T n) ^ (2 : ℕ) := by
    by_cases hn : (T n).Nonempty
    · simp only [iSup_pos hn, ENNReal.rpow_two]
    · rw [Set.not_nonempty_iff_eq_empty.mp hn]
      simp
  simpa only [hEq] using hTs

/-- A compact set of zero Euclidean Hausdorff area has finite ball covers
with centers in the set and arbitrarily small sum of squared radii. -/
theorem IsCompact.exists_finite_ball_cover_sq_of_hausdorffTwo_zero
    {K : Set Point} (hK : IsCompact K) (hK₀ : Measure.euclideanHausdorffMeasure 2 K = 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ (ι : Type) (I : Finset ι) (c : ι → Point) (r : ι → ℝ),
      (∀ i ∈ I, c i ∈ K ∧ 0 < r i ∧ r i < δ) ∧
      K ⊆ ⋃ i ∈ I, ball (c i) (r i) ∧ ∑ i ∈ I, (r i) ^ 2 < η := by
  classical
  obtain ⟨T,hT,hD,hSum⟩ := exists_countable_cover_ediam_sq
    (hausdorffTwo_eq_zero_of_euclidean_eq_zero hK₀) (show 0 < δ / 4 by positivity)
    (show 0 < η / 8 by positivity)
  let J := {n : ℕ // (T n ∩ K).Nonempty}
  obtain ⟨c,hc⟩ := Classical.axiomOfChoice (fun n : J => n.property)
  have hNotTop (n : ℕ) : ediam (T n) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hD n)
  let d (n : ℕ) := (ediam (T n)).toReal
  have hd (n : ℕ) : 0 ≤ d n := ENNReal.toReal_nonneg
  have hdδ (n : ℕ) : d n ≤ δ / 4 := ENNReal.toReal_ofReal (by positivity : 0 ≤ δ / 4) ▸
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (hD n)
  let s := min (δ / 4) (min (η / 16) 1)
  have hs : 0 < s := lt_min (by positivity) (lt_min (by positivity) zero_lt_one)
  have hsδ : s ≤ δ / 4 := min_le_left _ _
  have hsη : s ≤ η / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hs₁ : s ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  let r (n : J) := d n.val + s * (1 / 2 : ℝ) ^ n.val
  have hr (n : J) : 0 < r n := add_pos_of_nonneg_of_pos (hd n) (mul_pos hs (by positivity))
  have hrδ (n : J) : r n < δ := by
    have hg : (1 / 2 : ℝ) ^ n.val ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hG := mul_le_of_le_one_right hs.le hg
    dsimp only [r]
    linarith only [hdδ n, hsδ, hG, hδ]
  have hCover : K ⊆ ⋃ n : J, ball (c n) (r n) := by
    intro x hx
    obtain ⟨m,hm⟩ := mem_iUnion.mp (hT hx)
    let n : J := ⟨m,⟨x,hm,hx⟩⟩
    have hdc : dist x (c n) ≤ d m := by
      rw [dist_edist]
      exact ENNReal.toReal_mono (hNotTop m) (edist_le_ediam_of_mem hm (hc n).1)
    exact mem_iUnion.2 ⟨n,mem_ball.2 (hdc.trans_lt (lt_add_of_pos_right _ (mul_pos hs (by positivity))))⟩
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover (fun i : J => ball (c i) (r i)) (fun _ => isOpen_ball) hCover
  let F := I.map (⟨Subtype.val, Subtype.val_injective⟩ : J ↪ ℕ)
  have hDsum : ∑ i ∈ I, d i.val ^ 2 < η / 8 := by
    have hCmp : (∑ i ∈ I, ENNReal.ofReal (d i.val ^ 2)) ≤ ∑' n, ediam (T n) ^ (2 : ℕ) := by
      have hEq (n : ℕ) : ENNReal.ofReal (d n ^ 2) = ediam (T n) ^ (2 : ℕ) := by
        rw [ENNReal.ofReal_pow (hd n), ENNReal.ofReal_toReal (hNotTop n)]
      simp only [hEq]
      have hSubset := ENNReal.sum_le_tsum (s := F) (f := fun n => ediam (T n) ^ (2 : ℕ))
      simpa only [F, Finset.sum_map, Function.Embedding.coeFn_mk] using hSubset
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)] at hCmp
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < η / 8)).1 (hCmp.trans_lt hSum)
  have hGeom : ∑ i ∈ I, (1 / 4 : ℝ) ^ i.val ≤ 4 / 3 := by
    have hS : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hL := hS.sum_le_tsum F (fun n _ => by positivity)
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hL
    norm_num only [one_div, inv_sub_inv] at hL
    calc
      _ = ∑ n ∈ F, (1 / 4 : ℝ) ^ n := by simp [F]
      _ ≤ _ := hL.trans_eq (by norm_num)
  refine ⟨J,I,c,r,fun n _ => ⟨(hc n).2,hr n,hrδ n⟩,hI,?_⟩
  have hSq (n : J) : r n ^ 2 ≤ 2 * d n.val ^ 2 + 2 * s ^ 2 * (1 / 4 : ℝ) ^ n.val := by
    dsimp only [r]
    have e : ((1 / 2 : ℝ) ^ n.val) ^ 2 = (1 / 4 : ℝ) ^ n.val := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h := sq_nonneg (d n.val - s * (1 / 2 : ℝ) ^ n.val)
    have hP : (s * (1 / 2 : ℝ) ^ n.val) ^ 2 =
        s ^ 2 * (1 / 4 : ℝ) ^ n.val := by rw [mul_pow,e]
    nlinarith only [h,hP]
  have hSs : s ^ 2 ≤ η / 16 :=
    (by simpa only [pow_two, mul_one] using mul_le_of_le_one_right hs.le hs₁ : s ^ 2 ≤ s).trans hsη
  calc
    _ ≤ ∑ i ∈ I, (2 * d i.val ^ 2 + 2 * s ^ 2 * (1 / 4 : ℝ) ^ i.val) :=
      Finset.sum_le_sum fun n _ => hSq n
    _ = 2 * (∑ i ∈ I, d i.val ^ 2) + 2 * s ^ 2 * (∑ i ∈ I, (1 / 4 : ℝ) ^ i.val) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ < η := by
      have hA := mul_le_mul_of_nonneg_left hGeom (show 0 ≤ 2 * s ^ 2 by positivity)
      nlinarith only [hDsum,hA,hSs,hη]

end Thesis
