module

public import Thesis.MeasureGeometry.WeakConvergence
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Regular

/-! Compactness of a finite collection of signed densities relative to a
single convergent sequence of compactly supported finite measures. -/

public section

open Set Filter MeasureTheory
open scoped BigOperators BoundedContinuousFunction ENNReal NNReal Topology

namespace Thesis.MeasureGeometry

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

private noncomputable def shiftedMeasure (μ : FiniteMeasure X) (C : ℝ≥0) (g : X → ℝ) : Measure X :=
  (μ : Measure X).withDensity fun x => ENNReal.ofReal ((C : ℝ) + g x)

omit [MetricSpace X] [BorelSpace X] in
private theorem shiftedMeasure_le (μ : FiniteMeasure X) (C : ℝ≥0) {g : X → ℝ}
    (hcap : ∀ x, |g x| ≤ C) : shiftedMeasure μ C g ≤ (2 * C : ℝ≥0) • (μ : Measure X) := by
  change shiftedMeasure μ C g ≤ ((2 * C : ℝ≥0) : ℝ≥0∞) • (μ : Measure X)
  rw [shiftedMeasure, ← withDensity_const]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro x
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_mono
  have hx := (abs_le.mp (hcap x)).2
  push_cast
  linarith only [hx]

private theorem integral_mul_eq_shiftedMeasure_sub (μ : FiniteMeasure X) (C : ℝ≥0)
    {g : X → ℝ} (hg : Measurable g) (hcap : ∀ x, |g x| ≤ C) (φ : X →ᵇ ℝ) :
    (∫ x, g x * φ x ∂(μ : Measure X)) =
      (∫ x, φ x ∂shiftedMeasure μ C g) -
        C * (∫ x, φ x ∂(μ : Measure X)) := by
  let w (x : X) := ENNReal.ofReal ((C : ℝ) + g x)
  have hw : Measurable w := (measurable_const.add hg).ennreal_ofReal
  have htop : ∀ᵐ x ∂(μ : Measure X), w x < ⊤ := Filter.Eventually.of_forall
    fun _ => ENNReal.ofReal_lt_top
  have hwReal (x : X) : (w x).toReal = C + g x := by
    apply ENNReal.toReal_ofReal
    linarith only [(abs_le.mp (hcap x)).1]
  letI : IsFiniteMeasure ((μ : Measure X).withDensity w) :=
    isFiniteMeasure_of_le _ (shiftedMeasure_le μ C hcap)
  have hφ := φ.integrable (μ := (μ : Measure X))
  have hwφ : Integrable (fun x => (C + g x) * φ x) (μ : Measure X) := by
    have h₁ := (integrable_withDensity_iff_integrable_smul' (E := ℝ) hw htop).1
      (φ.integrable (μ := (μ : Measure X).withDensity w))
    simpa only [smul_eq_mul, hwReal] using h₁
  have hchange := integral_withDensity_eq_integral_toReal_smul hw htop φ
  simp only [smul_eq_mul, hwReal] at hchange
  calc
    _ = ∫ x, (C + g x) * φ x - C * φ x ∂(μ : Measure X) :=
      integral_congr_ae (Filter.Eventually.of_forall fun _ => by ring)
    _ = _ := by
      change _ = (∫ x, φ x ∂(μ : Measure X).withDensity w) - _
      rw [integral_sub hwφ (hφ.const_mul C), integral_const_mul, ← hchange]

/-- Uniformly bounded densities of finitely many entries admit one common
subsequence and a Radon–Nikodym limit relative to the given scalar limit. -/
theorem exists_weaklyConvergent_boundedDensities {I : Type*} [Fintype I]
    {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    {μ : ℕ → FiniteMeasure X} {ν : FiniteMeasure X} (hμ : Tendsto μ atTop (𝓝 ν))
    (B : ℝ≥0) (hB : ∀ n, (μ n).mass ≤ B) (hμK : ∀ n, (μ n : Measure X) Kᶜ = 0)
    (C : ℝ≥0) (g : I → ℕ → X → ℝ) (hg : ∀ i n, Measurable (g i n))
    (hcap : ∀ i n x, |g i n x| ≤ C) :
    ∃ (s : ℕ → ℕ) (F : I → X → ℝ), StrictMono s ∧
      ∀ i, Measurable (F i) ∧ Integrable (F i) (ν : Measure X) ∧
        ∀ φ : X →ᵇ ℝ, Tendsto
          (fun n => ∫ x, g i (s n) x * φ x ∂(μ (s n) : Measure X)) atTop
          (𝓝 (∫ x, F i x * φ x ∂(ν : Measure X))) := by
  let c : ℝ≥0 := 2 * C
  let h (j : Bool × I) (n : ℕ) (x : X) := if j.1 then g j.2 n x else -g j.2 n x
  have hh (j : Bool × I) (n : ℕ) (x : X) : |h j n x| ≤ C := by
    by_cases hj : j.1 = true <;> simp [h, hj, hcap]
  let shifted (j : Bool × I) (n : ℕ) : FiniteMeasure X :=
    ⟨shiftedMeasure (μ n) C (h j n), isFiniteMeasure_of_le _ (shiftedMeasure_le (μ n) C (hh j n))⟩
  have hshift (j : Bool × I) (n : ℕ) : (shifted j n : Measure X) ≤ c • (μ n : Measure X) :=
    shiftedMeasure_le (μ n) C (hh j n)
  have hshiftMass (j : Bool × I) (n : ℕ) : (shifted j n).mass ≤ c * B := by
    apply ENNReal.coe_le_coe.mp
    rw [FiniteMeasure.ennreal_mass, ENNReal.coe_mul]
    refine (hshift j n univ).trans ?_
    rw [Measure.coe_nnreal_smul_apply, ← FiniteMeasure.ennreal_mass]
    exact mul_le_mul_right (ENNReal.coe_le_coe.mpr (hB n)) (c : ℝ≥0∞)
  have hshiftSupp (j : Bool × I) (n : ℕ) : (shifted j n : Measure X) Kᶜ = 0 := by
    refine le_antisymm ((hshift j n Kᶜ).trans ?_) zero_le
    rw [Measure.coe_nnreal_smul_apply, hμK n, mul_zero]
  obtain ⟨η, s, hs, hη⟩ := exists_supportedFiniteMeasure_family_subsequence hK hne shifted
    (c * B) hshiftMass hshiftSupp
  have hsum (i : I) (n : ℕ) : shifted (true, i) n + shifted (false, i) n = c • μ n := by
    apply FiniteMeasure.toMeasure_injective
    change shiftedMeasure (μ n) C (g i n) + shiftedMeasure (μ n) C (fun x => -g i n x) =
      (c : ℝ≥0∞) • (μ n : Measure X)
    let w₁ (x : X) := ENNReal.ofReal ((C : ℝ) + g i n x)
    let w₂ (x : X) := ENNReal.ofReal ((C : ℝ) - g i n x)
    have hw₁ : Measurable w₁ := (measurable_const.add (hg i n)).ennreal_ofReal
    change (μ n : Measure X).withDensity w₁ + (μ n : Measure X).withDensity w₂ = _
    rw [← withDensity_add_left hw₁, ← withDensity_const]
    apply congrArg ((μ n : Measure X).withDensity)
    funext x
    change ENNReal.ofReal ((C : ℝ) + g i n x) + ENNReal.ofReal ((C : ℝ) - g i n x) = (c : ℝ≥0∞)
    have hx := abs_le.mp (hcap i n x)
    rw [← ENNReal.ofReal_add (by linarith only [hx.1]) (by linarith only [hx.2]),
      ← ENNReal.ofReal_coe_nnreal]
    congr 1
    push_cast [c]
    ring
  have hsumlim (i : I) : η (true, i) + η (false, i) = c • ν := by
    apply tendsto_nhds_unique_of_eventuallyEq
      ((hη (true, i)).2.add (hη (false, i)).2)
      (tendsto_const_nhds.smul (hμ.comp hs.tendsto_atTop))
    exact Filter.Eventually.of_forall fun n => hsum i (s n)
  have hdom (i : I) : (η (true, i) : Measure X) ≤ c • (ν : Measure X) := by
    rw [← FiniteMeasure.toMeasure_smul, ← hsumlim, FiniteMeasure.toMeasure_add]
    intro W
    rw [Measure.add_apply]
    exact le_self_add
  have habs (i : I) : (η (true, i) : Measure X) ≪ (ν : Measure X) := by
    refine (Measure.absolutelyContinuous_of_le (hdom i)).trans ?_
    intro W hW
    rw [Measure.coe_nnreal_smul_apply, hW, mul_zero]
  let ρ (i : I) (x : X) := ((η (true, i) : Measure X).rnDeriv (ν : Measure X) x).toReal
  let F (i : I) (x : X) := ρ i x - C
  refine ⟨s, F, hs, ?_⟩
  intro i
  have hρ : Measurable (ρ i) := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hρint : Integrable (ρ i) (ν : Measure X) := by
    have hi := (integrable_toReal_rnDeriv_mul_iff (f := fun _ : X => (1 : ℝ))
      (habs i)).2 (integrable_const 1)
    simpa only [ρ, mul_one] using hi
  refine ⟨hρ.sub_const C, hρint.sub (integrable_const _), ?_⟩
  intro φ
  have hcont := FiniteMeasure.continuous_integral_boundedContinuousFunction φ
  have hweak := ((hcont.tendsto (η (true, i))).comp (hη (true, i)).2).sub
    (((hcont.tendsto ν).comp (hμ.comp hs.tendsto_atTop)).const_mul (C : ℝ))
  have htest (n : ℕ) : (∫ x, g i (s n) x * φ x ∂(μ (s n) : Measure X)) =
      (∫ x, φ x ∂(shifted (true, i) (s n) : Measure X)) - C * (∫ x, φ x ∂(μ (s n) : Measure X)) :=
    integral_mul_eq_shiftedMeasure_sub (μ (s n)) C (hg i (s n)) (hcap i (s n)) φ
  have hρφ : Integrable (fun x => ρ i x * φ x) (ν : Measure X) :=
    (integrable_toReal_rnDeriv_mul_iff (habs i)).2 (φ.integrable (μ := (η (true, i) : Measure X)))
  have htestLim : (∫ x, F i x * φ x ∂(ν : Measure X)) =
      (∫ x, φ x ∂(η (true, i) : Measure X)) - C * (∫ x, φ x ∂(ν : Measure X)) := by
    change (∫ x, (ρ i x - C) * φ x ∂(ν : Measure X)) = _
    simp_rw [sub_mul]
    rw [integral_sub hρφ ((φ.integrable (μ := (ν : Measure X))).const_mul _), integral_const_mul]
    exact congrArg (fun z : ℝ => z - C * ∫ x, φ x ∂(ν : Measure X))
      (integral_toReal_rnDeriv_mul (habs i))
  rw [htestLim]
  exact hweak.congr (fun n => (htest n).symm)

omit [MeasurableSpace X] [BorelSpace X] in
private theorem exists_boundedContinuous_approx_indicator {K : Set X} (hK : IsClosed K)
    (hne : K.Nonempty) :
    ∃ φ : ℕ → X →ᵇ ℝ, (∀ n x, φ n x ∈ Icc (0 : ℝ) 1) ∧
      ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (K.indicator 1 x)) := by
  let b (n : ℕ) (x : X) := max 0 (1 - (n : ℝ) * Metric.infDist x K)
  have hb (n : ℕ) (x : X) : b n x ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le zero_le_one
      (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) Metric.infDist_nonneg))⟩
  have hcont (n : ℕ) : Continuous (b n) := continuous_const.max
    (continuous_const.sub (continuous_const.mul (Metric.continuous_infDist_pt K)))
  let φ (n : ℕ) : X →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨b n, hcont n⟩ 1 (by
    intro x y
    rw [Real.dist_eq]
    change |b n x - b n y| ≤ 1
    exact abs_le.mpr ⟨by linarith only [(hb n x).1, (hb n y).2],
      by linarith only [(hb n x).2, (hb n y).1]⟩)
  refine ⟨φ, hb, ?_⟩
  intro x
  change Tendsto (fun n => b n x) atTop (𝓝 (K.indicator 1 x))
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx]
    simp [b, Metric.infDist_zero_of_mem hx]
  · rw [indicator_of_notMem hx]
    have hp : 0 < Metric.infDist x K := (Metric.infDist_pos_iff_notMem_closure hne).1
      (hK.closure_eq.symm ▸ hx)
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / Metric.infDist x K)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hmul : 1 ≤ (n : ℝ) * Metric.infDist x K := (div_le_iff₀ hp).1
      (hN.trans (Nat.cast_le.mpr hn))
    exact (max_eq_left (sub_nonpos.mpr hmul)).symm

/-- Nonnegative compact tests detect positivity of an integrable density. -/
theorem ae_nonneg_of_boundedContinuous_tests {μ : Measure X} [μ.InnerRegular]
    {f : X → ℝ} (hm : Measurable f) (hf : Integrable f μ)
    (h : ∀ φ : X →ᵇ ℝ, (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x, f x * φ x ∂μ) : 0 ≤ᵐ[μ] f := by
  by_contra hn
  let S : Set X := {x | f x < 0}
  have hS : MeasurableSet S := measurableSet_lt hm measurable_const
  have hμS : 0 < μ S := by
    apply pos_iff_ne_zero.2
    intro hz
    apply hn
    rw [Filter.EventuallyLE, ae_iff]
    simpa only [Pi.zero_apply, not_le] using hz
  obtain ⟨K, hKS, hK, hμK⟩ := hS.exists_lt_isCompact hμS
  have hne : K.Nonempty := by
    by_contra hn'
    have he := Set.not_nonempty_iff_eq_empty.mp hn'
    rw [he, measure_empty] at hμK
    exact lt_irrefl _ hμK
  obtain ⟨φ, hφ, hlim⟩ := exists_boundedContinuous_approx_indicator hK.isClosed hne
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun x => f x * φ n x) μ :=
    fun n => hf.aestronglyMeasurable.mul (φ n).continuous.aestronglyMeasurable
  have hbound (n : ℕ) (x : X) : ‖f x * φ n x‖ ≤ ‖f x‖ := by
    rw [norm_mul, Real.norm_of_nonneg (hφ n x).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hφ n x).2
  have hlimInt := tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall (hbound n)) hf.norm
    (Filter.Eventually.of_forall fun x => (hlim x).const_mul (f x))
  have hcut : (fun x => f x * K.indicator 1 x) = K.indicator f := by
    funext x
    by_cases hx : x ∈ K <;> simp [hx]
  rw [hcut, integral_indicator hK.measurableSet] at hlimInt
  have hpos : 0 ≤ ∫ x in K, f x ∂μ :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlimInt
      (Filter.Eventually.of_forall fun n => h (φ n) fun x => (hφ n x).1)
  have hneg : 0 ≤ᵐ[μ.restrict K] (fun x => -f x) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact (neg_nonneg.mpr (hKS hx).le : 0 ≤ -f x)
  have hsp : K ⊆ Function.support (fun x => -f x) := by
    intro x hx
    exact neg_ne_zero.2 (hKS hx).ne
  have hspMass : 0 < μ.restrict K (Function.support (fun x => -f x)) := by
    have hmsp : MeasurableSet (Function.support (fun x => -f x)) := by
      change MeasurableSet ((fun x => -f x) ⁻¹' {(0 : ℝ)})ᶜ
      exact (hm.neg (measurableSet_singleton 0)).compl
    rw [Measure.restrict_apply hmsp, inter_eq_right.mpr hsp]
    exact hμK
  have hstrict := (integral_pos_iff_support_of_nonneg_ae hneg hf.neg.integrableOn).2 hspMass
  rw [integral_neg] at hstrict
  linarith only [hpos, hstrict]

/-- Affine inequalities pass to the actual limit of a finite collection of
densities under bounded continuous testing. -/
theorem ae_affine_nonneg_of_weakDensities {I : Type*} [Fintype I]
    {μ : ℕ → FiniteMeasure X} {ν : FiniteMeasure X} [(ν : Measure X).InnerRegular]
    (hμ : Tendsto μ atTop (𝓝 ν)) {g : I → ℕ → X → ℝ} {F : I → X → ℝ}
    (hg : ∀ i n, Integrable (g i n) (μ n : Measure X)) (hm : ∀ i, Measurable (F i))
    (hF : ∀ i, Integrable (F i) (ν : Measure X))
    (hweak : ∀ (i : I) (φ : X →ᵇ ℝ), Tendsto
      (fun n => ∫ x, g i n x * φ x ∂(μ n : Measure X)) atTop
      (𝓝 (∫ x, F i x * φ x ∂(ν : Measure X))))
    (b : I → ℝ) (c : ℝ) (hpos : ∀ n, ∀ᵐ x ∂(μ n : Measure X), 0 ≤ c + ∑ i, b i * (g i n x)) :
    ∀ᵐ x ∂(ν : Measure X), 0 ≤ c + ∑ i, b i * F i x := by
  let f (x : X) := c + ∑ i, b i * F i x
  have hf₁ : Measurable f := measurable_const.add (Finset.measurable_sum _ fun i _ =>
    (hm i).const_mul (b i))
  have hf₂ : Integrable f (ν : Measure X) :=
    (integrable_const c).add (integrable_finsetSum _ fun i _ => (hF i).const_mul (b i))
  apply ae_nonneg_of_boundedContinuous_tests hf₁ hf₂
  intro φ hφ
  have hSplit (σ : FiniteMeasure X) (w : I → X → ℝ) (hw : ∀ i, Integrable (w i) (σ : Measure X)) :
      (∫ x, (c + ∑ i, b i * w i x) * φ x ∂(σ : Measure X)) =
      c * (∫ x, φ x ∂(σ : Measure X)) +
        ∑ i, b i * (∫ x, w i x * φ x ∂(σ : Measure X)) := by
    have hmul (i : I) : Integrable (fun x => w i x * φ x) (σ : Measure X) :=
      (hw i).mul_bdd φ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => φ.norm_coe_le_norm x)
    simp_rw [add_mul, Finset.sum_mul, mul_assoc]
    rw [integral_add ((φ.integrable (μ := (σ : Measure X))).const_mul c)
      (integrable_finsetSum _ fun i _ => (hmul i).const_mul (b i)), integral_const_mul,
        integral_finsetSum _ (fun i _ => (hmul i).const_mul (b i))]
    simp only [integral_const_mul]
  have hμtest := ((FiniteMeasure.continuous_integral_boundedContinuousFunction φ).tendsto ν).comp hμ
  have hlim := (hμtest.const_mul c).add
    (tendsto_finsetSum Finset.univ fun i _ => (hweak i φ).const_mul (b i))
  change 0 ≤ ∫ x, (c + ∑ i, b i * F i x) * φ x ∂(ν : Measure X)
  rw [hSplit ν F hF]
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  apply Filter.Eventually.of_forall
  intro n
  change 0 ≤ c * (∫ x, φ x ∂(μ n : Measure X)) +
    ∑ i, b i * (∫ x, g i n x * φ x ∂(μ n : Measure X))
  rw [← hSplit (μ n) (fun i => g i n) (fun i => hg i n)]
  apply integral_nonneg_of_ae
  filter_upwards [hpos n] with x hx
  exact mul_nonneg hx (hφ x)

end Thesis.MeasureGeometry

end
