module

public import Thesis.Definitions
public import Thesis.MeasureGeometry.WeakConvergence
import StratificationTheory.MeasureTheory.HausdorffLowerGrowth

/-! One-dimensional densities and the Hausdorff length estimate. -/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Thesis.MeasureGeometry

theorem eventually_mem_positive_interval {R : ℝ} (hR : 0 < R) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ Ioo 0 R := by
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0),
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hR)] with r hr hrR
  exact ⟨hr, hrR⟩

/-- Normalized open-ball monotonicity passes to closed balls of the weak limit.
The intermediate radius keeps the Portmanteau lower bound on an open ball. -/
theorem monotoneOn_oneDensity_of_weakConvergence
    {μ : ℕ → FiniteMeasure Point} {ν : FiniteMeasure Point}
    (hν : Tendsto μ atTop (𝓝 ν)) (x : Point) {R : ℝ}
    (hmono : ∀ n, MonotoneOn
      (fun r => ((μ n : Measure Point) (ball x r)).toReal / (2 * r)) (Ioo 0 R)) :
    MonotoneOn (oneDensity ν x) (Ioo 0 R) := by
  intro r hr t ht hrt
  rcases hrt.eq_or_lt with rfl | hrt
  · exact le_rfl
  have hpos (a : ℝ) (ha : 0 < a) : 0 < 2 * a := mul_pos (by norm_num) ha
  let A := (ν : Measure Point) (closedBall x r)
  let B := (ν : Measure Point) (closedBall x t)
  have hB : B ≠ ⊤ := measure_ne_top (ν : Measure Point) _
  have hstep (s : ℝ) (hrs : r < s) (hst : s < t) :
      A ≤ ENNReal.ofReal (s / t) * B := by
    have hs0 : 0 < s := hr.1.trans hrs
    let c := ENNReal.ofReal (s / t)
    have hc : c ≠ ⊤ := ENNReal.ofReal_ne_top
    have hbound (n : ℕ) : (μ n : Measure Point) (ball x s) ≤
        c * (μ n : Measure Point) (closedBall x t) := by
      let m := μ n
      have h := hmono n ⟨hs0, hst.trans ht.2⟩ ht hst.le
      have hcross := (div_le_div_iff₀ (hpos s hs0) (hpos t ht.1)).mp h
      have hreal : ((m : Measure Point) (ball x s)).toReal ≤
          s / t * ((m : Measure Point) (closedBall x t)).toReal := by
        calc
          _ ≤ ((m : Measure Point) (ball x t)).toReal * s / t := by
            apply (le_div_iff₀ ht.1).2
            dsimp only [m]
            nlinarith only [hcross]
          _ = s / t * ((m : Measure Point) (ball x t)).toReal := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (ENNReal.toReal_mono (measure_ne_top (m : Measure Point) _)
              (measure_mono ball_subset_closedBall))
            (div_nonneg hs0.le ht.1.le)
      have h := ENNReal.ofReal_mono hreal
      rwa [ENNReal.ofReal_toReal (measure_ne_top (m : Measure Point) _),
        ENNReal.ofReal_mul (div_nonneg hs0.le ht.1.le),
        ENNReal.ofReal_toReal (measure_ne_top (m : Measure Point) _)] at h
    have hmul : Monotone (fun y : ℝ≥0∞ => c * y) := fun _ _ hy => mul_le_mul_right hy c
    have hsup := hmul.map_limsup_of_continuousAt (F := atTop)
      (fun n => (μ n : Measure Point) (closedBall x t))
      (ENNReal.continuous_const_mul hc).continuousAt
    calc
      A ≤ (ν : Measure Point) (ball x s) := measure_mono (closedBall_subset_ball hrs)
      _ ≤ atTop.liminf (fun n => (μ n : Measure Point) (ball x s)) :=
        measure_open_le_liminf hν isOpen_ball
      _ ≤ atTop.limsup (fun n => (μ n : Measure Point) (ball x s)) := liminf_le_limsup
      _ ≤ atTop.limsup (fun n => c * (μ n : Measure Point) (closedBall x t)) :=
        limsup_le_limsup (Eventually.of_forall hbound)
      _ = c * atTop.limsup (fun n => (μ n : Measure Point) (closedBall x t)) := hsup.symm
      _ ≤ c * B := hmul (FiniteMeasure.limsup_measure_closed_le_of_tendsto hν isClosed_closedBall)
  have hcont : Continuous (fun s : ℝ => ENNReal.ofReal (s / t) * B) :=
    (ENNReal.continuous_mul_const hB).comp (ENNReal.continuous_ofReal.comp (continuous_id.div_const t))
  have htend : Tendsto (fun s : ℝ => ENNReal.ofReal (s / t) * B) (𝓝[>] r)
      (𝓝 (ENNReal.ofReal (r / t) * B)) :=
    (hcont.tendsto r).mono_left nhdsWithin_le_nhds
  have hexact : A ≤ ENNReal.ofReal (r / t) * B := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds htend
    filter_upwards [self_mem_nhdsWithin (a := r) (s := Ioi r),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hrt)] with s hs hs'
    exact hstep s hs hs'
  have hbprod : ENNReal.ofReal (r / t) * B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB
  have hreal := ENNReal.toReal_mono hbprod hexact
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg hr.1.le ht.1.le)] at hreal
  have hprod : A.toReal * t ≤ B.toReal * r := by
    apply (le_div_iff₀ ht.1).mp
    calc
      A.toReal ≤ r / t * B.toReal := hreal
      _ = B.toReal * r / t := by ring
  change A.toReal / (2 * r) ≤ B.toReal / (2 * t)
  exact (div_le_div_iff₀ (hpos r hr.1) (hpos t ht.1)).2 (by nlinarith only [hprod])

/-- A nondecreasing normalized mass has a uniquely determined finite endpoint density. -/
theorem existsUnique_oneDensity_limit (μ : Measure Point) (x : Point) {R : ℝ}
    (hR : 0 < R) (hmono : MonotoneOn (oneDensity μ x) (Ioo 0 R)) :
    ∃! θ : ℝ, Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ) := by
  let S := oneDensity μ x '' Ioo 0 R
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact div_nonneg ENNReal.toReal_nonneg (mul_nonneg (by norm_num) hr.1.le)
  have hS : S.Nonempty := (nonempty_Ioo.mpr hR).image _
  have hθ : Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 (sInf S)) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [eventually_mem_positive_interval hR] with r hr
      exact ha.trans_le (csInf_le hbdd (mem_image_of_mem _ hr))
    · intro a ha
      obtain ⟨y, ⟨r, hr, rfl⟩, hra⟩ := (csInf_lt_iff hbdd hS).1 ha
      filter_upwards [eventually_mem_positive_interval hr.1] with s hs
      exact (hmono ⟨hs.1, hs.2.trans hr.2⟩ hr hs.2.le).trans_lt hra
  exact ⟨sInf S, hθ, fun _ ht => tendsto_nhds_unique ht hθ⟩

theorem mem_support_iff_ball_pos {μ : Measure Point} {x : Point} :
    x ∈ μ.support ↔ ∀ r > (0 : ℝ), 0 < μ (ball x r) :=
  nhds_basis_ball.mem_measureSupport

/-- A clearing-out bound for closed balls characterizes the support via the
actual density of the same measure. -/
theorem density_support_of_clearing_out (μ : Measure Point) [IsFiniteMeasure μ] (x : Point)
    {R η θ : ℝ} (hR : 0 < R) (hη : 0 < η)
    (hθ : Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ))
    (hclear : ∀ r ∈ Ioo 0 R, μ (closedBall x r) < ENNReal.ofReal (η * r) →
      μ (ball x (r / 2)) = 0) :
    (x ∈ μ.support ↔ 0 < θ) ∧ (x ∈ μ.support ↔ η / 2 ≤ θ) := by
  by_cases hx : x ∈ μ.support
  · have hlower : η / 2 ≤ θ := by
      apply le_of_tendsto_of_tendsto tendsto_const_nhds hθ
      filter_upwards [eventually_mem_positive_interval hR] with r hr
      have hm : ENNReal.ofReal (η * r) ≤ μ (closedBall x r) := by
        apply le_of_not_gt
        intro hlt
        have hm' := (mem_support_iff_ball_pos.mp hx) (r / 2) (half_pos hr.1)
        rw [hclear r hr hlt] at hm'
        exact (lt_irrefl 0 hm')
      have hreal := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).mp hm
      change η / 2 ≤ (μ (closedBall x r)).toReal / (2 * r)
      apply (le_div_iff₀ (mul_pos (by norm_num : 0 < (2 : ℝ)) hr.1)).2
      calc
        η / 2 * (2 * r) = η * r := by ring
        _ ≤ _ := hreal
    exact ⟨⟨fun _ => (half_pos hη).trans_le hlower, fun _ => hx⟩, ⟨fun _ => hlower, fun _ => hx⟩⟩
  · obtain ⟨b, hb, hb0⟩ := nhds_basis_ball.notMem_measureSupport.mp hx
    have hz : Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_mem_positive_interval hb] with r hr
      have hle := measure_mono (μ := μ) (closedBall_subset_ball (x := x) hr.2)
      rw [hb0] at hle
      simp [oneDensity, nonpos_iff_eq_zero.mp hle]
    have hzero := tendsto_nhds_unique hθ hz
    rw [hzero]
    exact ⟨⟨False.elim ∘ hx, fun h => (lt_irrefl 0 h).elim⟩,
      ⟨False.elim ∘ hx, fun h => ((half_pos hη).not_ge h).elim⟩⟩

/-- The positive-density support estimate on each subset, in the same
Hausdorff normalization as the frozen statement. -/
theorem hausdorffOne_le_of_positive_oneDensity (μ : Measure Point) [IsFiniteMeasure μ]
    [μ.OuterRegular] {E S : Set Point} (hES : E ⊆ S) {η : ℝ} (hη : 0 < η)
    (hD : ∀ x ∈ S, ∃ θ ≥ η / 2, Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ)) :
    HausdorffOne E ≤ ENNReal.ofReal (40 / η) * μ E := by
  have hη4 : 0 < η / 4 := by positivity
  have hfine : ∀ x ∈ E, ∀ δ > (0 : ℝ), ∃ r ∈ Ioo 0 δ,
      ENNReal.ofReal ((η / 4) * r ^ (1 : ℕ)) ≤ μ (ball x r) := by
    intro x hx δ hδ
    obtain ⟨θ, hθ, hlim⟩ := hD x (hES hx)
    have hηθ : η / 4 < θ := by linarith only [hη, hθ]
    have he : ∀ᶠ s in 𝓝[>] 0, s ∈ Ioo 0 (δ / 2) ∧ η / 4 < oneDensity μ x s :=
      (eventually_mem_positive_interval (half_pos hδ)).and
        (hlim.eventually (eventually_gt_nhds hηθ))
    obtain ⟨s, hs, hsD⟩ := he.exists
    have h2s : s < 2 * s := by linarith only [hs.1]
    refine ⟨2 * s, ⟨mul_pos (by norm_num) hs.1, by linarith only [hs.2]⟩, ?_⟩
    apply le_trans _ (measure_mono (closedBall_subset_ball h2s))
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).mpr
    rw [pow_one]
    exact ((lt_div_iff₀ (mul_pos (by norm_num : 0 < (2 : ℝ)) hs.1)).mp hsD).le
  let c : ℝ≥0 := ⟨η / 4, hη4.le⟩
  have hc : 0 < c := hη4
  have hc_eq : (c : ℝ≥0∞) = ENNReal.ofReal (η / 4) := by
    change (c : ℝ≥0∞) = ENNReal.ofReal (c : ℝ)
    rw [ENNReal.ofReal_coe_nnreal]
  have hgrowth : ∀ x ∈ E, ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ r < δ ∧
        (c : ℝ≥0∞) * (ENNReal.ofReal r) ^ (1 : ℝ) ≤ μ (ball x r) := by
    intro x hx δ hδ
    obtain ⟨r, hr, hmass⟩ := hfine x hx δ hδ
    refine ⟨r, hr.1, hr.2, ?_⟩
    rw [ENNReal.rpow_one, hc_eq, ← ENNReal.ofReal_mul hη4.le]
    simpa only [pow_one] using hmass
  have h := StratificationTheory.hausdorffMeasure_le_measure_of_lower_growth
    μ E c hc 1 (by norm_num) hgrowth
  have hcoef : (10 : ℝ) / (η / 4) = 40 / η := by
    field_simp [hη.ne']
    ring
  rw [ENNReal.rpow_one, ← ENNReal.ofReal_ofNat 10, hc_eq, ← ENNReal.ofReal_div_of_pos hη4] at h
  simpa only [HausdorffOne, hcoef] using h

end Thesis.MeasureGeometry

end
