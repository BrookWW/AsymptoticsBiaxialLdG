module

public import Thesis.MeasureGeometry.EnergyMeasure
public import Thesis.MeasureGeometry.LineDensity

/-! Uniform local energy bounds from an eventual clearing-out estimate. -/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal BigOperators Topology

namespace Thesis.MeasureGeometry

/-- Choosing the constant from a finite equal-radius cover uses only the compact
region and radius, before choosing the measure sequence or its tail. -/
theorem exists_eventual_cover_bound (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : Set Point → ℝ → ℝ, (∀ U r, 0 < C U r) ∧
      ∀ U : Set Point, IsCompact (closure U) → ∀ r : ℝ, 0 < r →
        ∀ μ : ℕ → Measure Point,
          (∀ x ∈ closure U, ∀ᶠ n in atTop, μ n (ball x (r / 2)) ≤ ENNReal.ofReal (C₀ * r)) →
          ∀ᶠ n in atTop, μ n U ≤ ENNReal.ofReal (C U r) := by
  classical
  have mkbound (U : Set Point) (r : ℝ) :
      ∃ B : ℝ, 0 < B ∧
        (IsCompact (closure U) → 0 < r → ∀ μ : ℕ → Measure Point,
          (∀ x ∈ closure U, ∀ᶠ n in atTop, μ n (ball x (r / 2)) ≤ ENNReal.ofReal (C₀ * r)) →
          ∀ᶠ n in atTop, μ n U ≤ ENNReal.ofReal B) := by
    by_cases hr : 0 < r
    · by_cases hK : IsCompact (closure U)
      · let V : closure U → Set Point := fun x => ball x (r / 2)
        have hcov : closure U ⊆ ⋃ x, V x := by
          intro x hx
          exact mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (half_pos hr)⟩
        obtain ⟨I, hI⟩ := hK.elim_finite_subcover V (fun _ => isOpen_ball) hcov
        let B := (I.card : ℝ) * (C₀ * r) + 1
        refine ⟨B, by dsimp [B]; positivity, ?_⟩
        intro _ _ μ hm
        have hAll : ∀ᶠ n in atTop, ∀ i ∈ I, μ n (V i) ≤ ENNReal.ofReal (C₀ * r) :=
          (eventually_all_finset I).2 fun i _ => hm i i.property
        filter_upwards [hAll] with n hn
        calc
          μ n U ≤ μ n (⋃ i ∈ I, V i) := measure_mono (subset_closure.trans hI)
          _ ≤ ∑ i ∈ I, μ n (V i) := measure_biUnion_finset_le _ _
          _ ≤ ∑ _ ∈ I, ENNReal.ofReal (C₀ * r) := Finset.sum_le_sum hn
          _ = ENNReal.ofReal ((I.card : ℝ) * (C₀ * r)) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg I.card)]
          _ ≤ ENNReal.ofReal B := ENNReal.ofReal_mono (by simp [B])
      · exact ⟨1, zero_lt_one, fun h => (hK h).elim⟩
    · exact ⟨1, zero_lt_one, fun _ h => (hr h).elim⟩
  choose C hC hb using mkbound
  exact ⟨C, hC, fun U hU r hr => hb U r hU hr⟩

/-- A finite initial prefix can be absorbed into a bound on the same sequence. -/
theorem exists_all_index_measure_bound (μ : ℕ → Measure Point) (U : Set Point)
    (hfin : ∀ n, μ n U ≠ ∞) {B : ℝ}
    (hB : ∀ᶠ n in atTop, μ n U ≤ ENNReal.ofReal B) :
    ∃ C > 0, ∀ n, μ n U ≤ ENNReal.ofReal C := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hB
  let C₁ : ℝ := ∑ n ∈ Finset.range N, (μ n U).toReal
  have hC₁ : 0 ≤ C₁ := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  refine ⟨max B C₁ + 1, by linarith only [hC₁, le_max_right B C₁], ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (ENNReal.ofReal_mono (by linarith only [le_max_left B C₁]))
  · have hi : n ∈ Finset.range N := Finset.mem_range.2 (lt_of_not_ge hn)
    have hle : (μ n U).toReal ≤ C₁ :=
      Finset.single_le_sum (f := fun i => (μ i U).toReal) (fun _ _ => ENNReal.toReal_nonneg) hi
    rw [← ENNReal.ofReal_toReal (hfin n)]
    exact ENNReal.ofReal_mono (by linarith only [hle, le_max_right B C₁])

/-- Compact containment supplies an admissible positive radius uniformly over
all centers in the closure. -/
theorem exists_closedBall_subset_of_compactlyContained {U W : Set Point}
    (hU : CompactlyContained U W) (hW : IsOpen W) :
    ∃ r > 0, ∀ x ∈ closure U, closedBall x r ⊆ W := by
  obtain ⟨r, hr, hsub⟩ := hU.1.exists_cthickening_subset_open hW hU.2
  exact ⟨r, hr, fun x hx => (closedBall_subset_cthickening hx r).trans hsub⟩

private theorem tendsto_log_inv_scale_atTop (ε : ℕ → ElasticScale)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => Real.log (1 / (ε n : ℝ))) atTop atTop := by
  have hpos : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall (fun n => (ε n).property.1)⟩
  simpa only [one_div, Function.comp_def] using
    Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hpos)

private theorem energy_of_subset_eq_log_mul_normalizedMeasure (a : BulkCoefficients)
    (ε : ElasticScale) {Ω S : Set Point} (hS : MeasurableSet S) (hsub : S ⊆ Ω)
    (u : Point → S0) (D : Point → Gradient) :
    energy a ε S u D = ENNReal.ofReal (Real.log (1 / (ε : ℝ))) *
      normalizedEnergyMeasure a ε Ω u D S := by
  have hlog := log_inv_scale_pos ε
  rw [normalizedEnergyMeasure_apply a ε Ω u D hS, inter_eq_left.mpr hsub,
    ← mul_assoc, ← ENNReal.ofReal_mul hlog.le, mul_inv_cancel₀ hlog.ne', ENNReal.ofReal_one, one_mul]

/-- The limit mass on a closed ball supplies the eventual rescaled energy and
radius hypotheses for clearing out on that ball. -/
theorem eventually_clearingOut_ball_hypotheses (a : BulkCoefficients)
    {Ω : Set Point} {x : Point} {r η ε₀ : ℝ} (hr : 0 < r) (hη : 0 < η) (hε₀ : 0 < ε₀)
    (hball : closedBall x r ⊆ Ω) (ε : ℕ → ElasticScale)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (Q : ℕ → Point → S0) (D : ℕ → Point → Gradient)
    {μ : ℕ → FiniteMeasure Point} {ν : FiniteMeasure Point}
    (hμ : ∀ n, (μ n : Measure Point) = normalizedEnergyMeasure a (ε n) Ω (Q n) (D n))
    (hw : Tendsto μ atTop (𝓝 ν))
    (hν : (ν : Measure Point) (closedBall x r) < ENNReal.ofReal (η * r)) :
    ∀ᶠ n in atTop, (ε n : ℝ) ≤ ε₀ * r ∧ energy a (ε n) (ball x r) (Q n) (D n) ≤
      ENNReal.ofReal (η * r * Real.log (r / (ε n : ℝ))) := by
  have hmass := (ENNReal.toReal_lt_toReal (measure_ne_top (ν : Measure Point) _)
    ENNReal.ofReal_ne_top).2 hν
  rw [ENNReal.toReal_ofReal (mul_nonneg hη.le hr.le)] at hmass
  obtain ⟨q, hq₁, hq₂⟩ := exists_between hmass
  have hq : 0 < q := ENNReal.toReal_nonneg.trans_lt hq₁
  have hqmass : (ν : Measure Point) (closedBall x r) < ENNReal.ofReal q := by
    have h := ENNReal.ofReal_lt_ofReal_iff hq |>.mpr hq₁
    rwa [ENNReal.ofReal_toReal (measure_ne_top (ν : Measure Point) _)] at h
  have hqev : ∀ᶠ n in atTop, (μ n : Measure Point) (closedBall x r) < ENNReal.ofReal q :=
    eventually_lt_of_limsup_lt
      ((FiniteMeasure.limsup_measure_closed_le_of_tendsto hw isClosed_closedBall).trans_lt hqmass)
  have hLe : ∀ᶠ n in atTop, -(η * r * Real.log r) / (η * r - q) ≤ Real.log (1 / (ε n : ℝ)) :=
    (tendsto_atTop.mp (tendsto_log_inv_scale_atTop ε hε)) _
  have hscale : ∀ᶠ n in atTop, (ε n : ℝ) < ε₀ * r :=
    hε.eventually (eventually_lt_nhds (mul_pos hε₀ hr))
  filter_upwards [hqev, hLe, hscale] with n hn hnl hns
  refine ⟨hns.le, ?_⟩
  let L := Real.log (1 / (ε n : ℝ))
  have hL : 0 < L := log_inv_scale_pos (ε n)
  have hlog : Real.log (r / (ε n : ℝ)) = L + Real.log r := by
    dsimp only [L]
    rw [Real.log_div hr.ne' (ε n).property.1.ne',
      Real.log_div one_ne_zero (ε n).property.1.ne', Real.log_one]
    ring
  have hquad : L * q ≤ η * r * (L + Real.log r) := by
    have hh := (div_le_iff₀ (sub_pos.mpr hq₂)).mp hnl
    change -(η * r * Real.log r) ≤ L * (η * r - q) at hh
    nlinarith only [hh]
  calc
    energy a (ε n) (ball x r) (Q n) (D n) ≤ energy a (ε n) (closedBall x r) (Q n) (D n) :=
      lintegral_mono_set ball_subset_closedBall
    _ = ENNReal.ofReal L * (μ n : Measure Point) (closedBall x r) := by
      rw [hμ n]
      exact energy_of_subset_eq_log_mul_normalizedMeasure a (ε n) isClosed_closedBall.measurableSet
        hball (Q n) (D n)
    _ ≤ ENNReal.ofReal L * ENNReal.ofReal q := mul_le_mul_right hn.le _
    _ = ENNReal.ofReal (L * q) := (ENNReal.ofReal_mul hL.le).symm
    _ ≤ _ := by rw [hlog]; exact ENNReal.ofReal_mono hquad

/-- An eventual uniform unnormalized energy bound on an open set makes the
limit normalized measure vanish there. -/
theorem measure_open_eq_zero_of_eventual_bound (a : BulkCoefficients)
    {Ω U : Set Point} (hU : IsOpen U) (hsub : U ⊆ Ω) (ε : ℕ → ElasticScale)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (Q : ℕ → Point → S0) (D : ℕ → Point → Gradient)
    {μ : ℕ → FiniteMeasure Point} {ν : FiniteMeasure Point}
    (hμ : ∀ n, (μ n : Measure Point) = normalizedEnergyMeasure a (ε n) Ω (Q n) (D n))
    (hw : Tendsto μ atTop (𝓝 ν)) {C : ℝ}
    (hC : ∀ᶠ n in atTop, energy a (ε n) U (Q n) (D n) ≤ ENNReal.ofReal C) :
    (ν : Measure Point) U = 0 := by
  have ht0 : Tendsto (fun n => (Real.log (1 / (ε n : ℝ)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_log_inv_scale_atTop ε hε)
  have hcoef : Tendsto (fun n => ENNReal.ofReal ((Real.log (1 / (ε n : ℝ)))⁻¹))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp ht0
  have hlim : Tendsto (fun n => ENNReal.ofReal ((Real.log (1 / (ε n : ℝ)))⁻¹) * ENNReal.ofReal C)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      ((ENNReal.continuous_mul_const ENNReal.ofReal_ne_top).tendsto 0).comp hcoef
  have he : ∀ᶠ n in atTop, (μ n : Measure Point) U ≤
      ENNReal.ofReal ((Real.log (1 / (ε n : ℝ)))⁻¹) * ENNReal.ofReal C := by
    filter_upwards [hC] with n hn
    rw [hμ n, normalizedEnergyMeasure_apply a (ε n) Ω (Q n) (D n) hU.measurableSet,
      inter_eq_left.mpr hsub]
    exact mul_le_mul_right hn _
  exact nonpos_iff_eq_zero.mp <| (measure_open_le_liminf hw hU).trans <|
    (Filter.liminf_le_liminf he).trans (hlim.liminf_eq).le

/-- Apply the model's clearing estimate with the hypotheses supplied by the
closed-ball weak limit. The same event forces the limiting half-ball mass to zero. -/
theorem small_limitMass_eventually_bound_and_zero (a : BulkCoefficients)
    {Ω : Set Point} {x : Point} {r η ε₀ C : ℝ} (hr : 0 < r) (hη : 0 < η) (hε₀ : 0 < ε₀)
    (hball : closedBall x r ⊆ Ω) (ε : ℕ → ElasticScale)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (Q : ℕ → Point → S0) (D : ℕ → Point → Gradient)
    {μ : ℕ → FiniteMeasure Point} {ν : FiniteMeasure Point}
    (hμ : ∀ n, (μ n : Measure Point) = normalizedEnergyMeasure a (ε n) Ω (Q n) (D n))
    (hw : Tendsto μ atTop (𝓝 ν))
    (hν : (ν : Measure Point) (closedBall x r) < ENNReal.ofReal (η * r))
    (hclear : ∀ n, (ε n : ℝ) ≤ ε₀ * r → energy a (ε n) (ball x r) (Q n) (D n) ≤
      ENNReal.ofReal (η * r * Real.log (r / (ε n : ℝ))) →
      energy a (ε n) (ball x (r / 2)) (Q n) (D n) ≤ ENNReal.ofReal (C * r)) :
    (∀ᶠ n in atTop, energy a (ε n) (ball x (r / 2)) (Q n) (D n) ≤ ENNReal.ofReal (C * r)) ∧
      (ν : Measure Point) (ball x (r / 2)) = 0 := by
  have hbound := (eventually_clearingOut_ball_hypotheses a hr hη hε₀
    hball ε hε Q D hμ hw hν).mono fun n hn => hclear n hn.1 hn.2
  have hsub : ball x (r / 2) ⊆ Ω :=
    (ball_subset_ball (by linarith : r / 2 ≤ r)).trans (ball_subset_closedBall.trans hball)
  exact ⟨hbound, measure_open_eq_zero_of_eventual_bound a isOpen_ball hsub ε hε Q D hμ hw hbound⟩

/-- The two off-support energy bounds on the same normalized-measure sequence,
using the model clearing estimate on compactly contained balls. -/
theorem exists_offSupport_energy_bounds (a : BulkCoefficients)
    {η ε₀ C₀ : ℝ} (hη : 0 < η) (hε₀ : 0 < ε₀) (hC₀ : 0 ≤ C₀) :
    ∃ C : Set Point → ℝ → ℝ, (∀ U r, 0 < C U r) ∧
      ∀ (Ω : Set Point), IsOpen Ω → ∀ (ε : ℕ → ElasticScale),
        Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        ∀ (Q : ℕ → Point → S0) (D : ℕ → Point → Gradient)
          (μ : ℕ → FiniteMeasure Point) (ν : FiniteMeasure Point),
        (∀ n, (μ n : Measure Point) = normalizedEnergyMeasure a (ε n) Ω (Q n) (D n)) →
        Tendsto μ atTop (𝓝 ν) →
        (∀ n, energy a (ε n) Ω (Q n) (D n) < ∞) →
        (∀ (x : Point) (r : ℝ), 0 < r → closedBall x r ⊆ Ω →
          ∀ n, (ε n : ℝ) ≤ ε₀ * r → energy a (ε n) (ball x r) (Q n) (D n) ≤
            ENNReal.ofReal (η * r * Real.log (r / (ε n : ℝ))) →
            energy a (ε n) (ball x (r / 2)) (Q n) (D n) ≤ ENNReal.ofReal (C₀ * r)) →
        ∀ U : Set Point, IsOpen U → CompactlyContained U (Ω \ (ν : Measure Point).support) →
          (∃ B > (0 : ℝ), ∀ n, energy a (ε n) U (Q n) (D n) ≤ ENNReal.ofReal B) ∧
          ∀ r : ℝ, 0 < r → (∀ x ∈ closure U, closedBall x r ⊆ Ω \ (ν : Measure Point).support) →
            ∀ᶠ n in atTop, energy a (ε n) U (Q n) (D n) ≤ ENNReal.ofReal (C U r) := by
  obtain ⟨C, hC, hcover⟩ := exists_eventual_cover_bound C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ ε hε Q D μ ν hμ hw hfin hclear U hUo hU
  let W := Ω \ (ν : Measure Point).support
  have hW : IsOpen W := hΩ.sdiff (ν : Measure Point).isClosed_support
  have hUsub : U ⊆ Ω := (subset_closure.trans hU.2).trans sdiff_subset
  let m (n : ℕ) := energyMeasure a (ε n) Ω (Q n) (D n)
  have hme (n : ℕ) : m n U = energy a (ε n) U (Q n) (D n) := by
    change energyMeasure a (ε n) Ω (Q n) (D n) U = _
    rw [energyMeasure_apply a (ε n) Ω (Q n) (D n) hUo.measurableSet, inter_eq_left.mpr hUsub]
  have hquant (r : ℝ) (hr : 0 < r) (hB : ∀ x ∈ closure U, closedBall x r ⊆ W) :
      ∀ᶠ n in atTop, m n U ≤ ENNReal.ofReal (C U r) := by
    apply hcover U hU.1 r hr m
    intro x hx
    have hball : closedBall x r ⊆ Ω := (hB x hx).trans sdiff_subset
    have hz : (ν : Measure Point) (closedBall x r) = 0 := by
      apply nonpos_iff_eq_zero.mp
      exact (measure_mono ((hB x hx).trans (sdiff_subset_compl Ω ((ν : Measure Point).support)))).trans
        (Measure.measure_compl_support (μ := (ν : Measure Point))).le
    have hνsmall : (ν : Measure Point) (closedBall x r) < ENNReal.ofReal (η * r) := by
      rw [hz]
      exact ENNReal.ofReal_pos.mpr (mul_pos hη hr)
    have hball' : ball x (r / 2) ⊆ Ω :=
      (ball_subset_ball (by linarith : r / 2 ≤ r)).trans (ball_subset_closedBall.trans hball)
    exact (small_limitMass_eventually_bound_and_zero a hr hη hε₀ hball ε hε Q D hμ hw hνsmall
      (hclear x r hr hball)).1.mono fun n hn => by
        simpa only [m, energyMeasure_apply a (ε n) Ω (Q n) (D n) isOpen_ball.measurableSet,
          inter_eq_left.mpr hball'] using hn
  refine ⟨?_, fun r hr hB => (hquant r hr hB).mono fun n hn => by rwa [hme n] at hn⟩
  obtain ⟨r, hr, hB⟩ := exists_closedBall_subset_of_compactlyContained hU hW
  have hfin' (n : ℕ) : m n U ≠ ∞ := by
    rw [hme n]
    exact ne_top_of_le_ne_top (hfin n).ne (lintegral_mono_set hUsub)
  obtain ⟨B, hBpos, hBbound⟩ := exists_all_index_measure_bound m U hfin' (hquant r hr hB)
  exact ⟨B, hBpos, fun n => by simpa only [hme n] using hBbound n⟩

end Thesis.MeasureGeometry

end
