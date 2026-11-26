module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! Weak convergence on a common compact support. The compact-support reduction
uses the same subtype restriction as the finite-measure compactness on a compact carrier. -/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace Thesis.MeasureGeometry

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem compact_subsequence [CompactSpace X] [Nonempty X]
    (μ : ℕ → FiniteMeasure X) (C : ℝ≥0) (hC : ∀ j, (μ j).mass ≤ C) :
    ∃ (ν : FiniteMeasure X) (s : ℕ → ℕ), StrictMono s ∧ Tendsto (μ ∘ s) atTop (𝓝 ν) := by
  let f : ℕ → ℝ≥0 × ProbabilityMeasure X := fun j => ((μ j).mass, (μ j).normalize)
  have hf : ∀ j, f j ∈ Icc 0 C ×ˢ univ := fun j => ⟨⟨zero_le, hC j⟩, mem_univ _⟩
  obtain ⟨p, -, s, hs, h⟩ :=
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) C)).prod
      (isCompact_univ : IsCompact (univ : Set (ProbabilityMeasure X)))).tendsto_subseq hf
  refine ⟨p.1 • p.2.toFiniteMeasure, s, hs, ?_⟩
  have hc : Continuous (fun z : ℝ≥0 × ProbabilityMeasure X => z.1 • z.2.toFiniteMeasure) :=
    continuous_fst.smul (ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_snd)
  have hh := (hc.tendsto p).comp h
  convert hh using 1
  funext j
  exact (μ (s j)).self_eq_mass_smul_normalize

/-- Extract one subsequence with weak limits on both the compact subtype and the
ambient space, and retain the same support for the limit. -/
theorem exists_supportedFiniteMeasure_subsequence
    {K : Set X} (hK : IsCompact K) (hne : K.Nonempty) (μ : ℕ → FiniteMeasure X) (C : ℝ≥0)
    (hC : ∀ j, (μ j).mass ≤ C) (hs : ∀ j, (μ j : Measure X) Kᶜ = 0) :
    ∃ (ν : FiniteMeasure X) (s : ℕ → ℕ), StrictMono s ∧
      (ν : Measure X) Kᶜ = 0 ∧ Tendsto (μ ∘ s) atTop (𝓝 ν) ∧
      Tendsto (fun j => (μ (s j)).comap ((↑) : K → X)) atTop
        (𝓝 (ν.comap ((↑) : K → X))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : Nonempty K := hne.to_subtype
  let f : K → X := Subtype.val
  have hf : IsClosedEmbedding f := IsClosedEmbedding.subtypeVal hK.isClosed
  let κ : ℕ → FiniteMeasure K := fun j => (μ j).comap f
  have hκ : ∀ j, (κ j).mass ≤ C := fun j =>
    (FiniteMeasure.mass_comap_le _ _).trans (hC j)
  obtain ⟨η, s, hsMono, hκlim⟩ := compact_subsequence κ C hκ
  have hmap (j : ℕ) : (κ j).map f = μ j := by
    apply FiniteMeasure.toMeasure_injective
    change Measure.map f (Measure.comap f (μ j : Measure X)) = μ j
    rw [map_comap_subtype_coe hK.isClosed.measurableSet]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    exact hs j
  have hcomap : (η.map f).comap f = η := by
    apply FiniteMeasure.toMeasure_injective
    exact hf.measurableEmbedding.comap_map (η : Measure K)
  have hsupp : (η.map f : Measure X) Kᶜ = 0 := by
    change Measure.map f (η : Measure K) Kᶜ = 0
    rw [Measure.map_apply hf.measurableEmbedding.measurable hK.isClosed.measurableSet.compl]
    have : f ⁻¹' Kᶜ = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      exact fun y h => h y.property
    rw [this, measure_empty]
  refine ⟨η.map f, s, hsMono, hsupp, ?_, ?_⟩
  · have h := (FiniteMeasure.continuous_map hf.continuous).tendsto η |>.comp hκlim
    simpa only [Function.comp_def, hmap] using h
  · change Tendsto (κ ∘ s) atTop (𝓝 ((η.map f).comap f))
    rwa [hcomap]

/-- A finite family of bounded measures has a single weakly convergent
subsequence, with every limit carried by the common compact set. -/
theorem exists_supportedFiniteMeasure_family_subsequence
    {I : Type*} [Fintype I] {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    (μ : I → ℕ → FiniteMeasure X) (C : ℝ≥0) (hm : ∀ i n, (μ i n).mass ≤ C)
    (hs : ∀ i n, (μ i n : Measure X) Kᶜ = 0) :
    ∃ (ν : I → FiniteMeasure X) (s : ℕ → ℕ), StrictMono s ∧
      ∀ i, (ν i : Measure X) Kᶜ = 0 ∧ Tendsto (μ i ∘ s) atTop (𝓝 (ν i)) := by
  classical
  have hfinite (J : Finset I) : ∃ (ν : I → FiniteMeasure X) (s : ℕ → ℕ), StrictMono s ∧
      ∀ i ∈ J, (ν i : Measure X) Kᶜ = 0 ∧ Tendsto (μ i ∘ s) atTop (𝓝 (ν i)) := by
    induction J using Finset.induction_on with
    | empty =>
        exact ⟨fun _ => 0, id, strictMono_id, fun _ hi => (Finset.notMem_empty _ hi).elim⟩
    | insert i J hi ih =>
        obtain ⟨ν, s, hmono, hν⟩ := ih
        obtain ⟨v, t, ht, hv₁, hv₂, _⟩ := exists_supportedFiniteMeasure_subsequence hK hne
          (μ i ∘ s) C (fun k => hm i (s k)) (fun k => hs i (s k))
        refine ⟨fun j => if j = i then v else ν j, s ∘ t, hmono.comp ht, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa [Function.comp_assoc] using And.intro hv₁ hv₂
        · have hne' : j ≠ i := fun h => hi (h ▸ hj)
          simpa only [if_neg hne', Function.comp_assoc] using
            And.intro (hν j hj).1 ((hν j hj).2.comp ht.tendsto_atTop)
  obtain ⟨ν, s, hmono, hν⟩ := hfinite Finset.univ
  exact ⟨ν, s, hmono, fun i => hν i (Finset.mem_univ _)⟩

/-- On the compact subtype, weak convergence gives convergence of all continuous
real-valued test integrals. -/
theorem tendsto_continuous_integral_of_finiteMeasure_tendsto
    {ι : Type*} [CompactSpace X] {L : Filter ι} {μ : ι → FiniteMeasure X}
    {ν : FiniteMeasure X} (h : Tendsto μ L (𝓝 ν)) (φ : C(X, ℝ)) :
    Tendsto (fun j => ∫ x, φ x ∂(μ j : Measure X)) L
      (𝓝 (∫ x, φ x ∂(ν : Measure X))) := by
  exact ((FiniteMeasure.continuous_integral_continuousMap φ).tendsto ν).comp h

/-- The limit measure of a convergent sequence evaluates any continuity set at
the limit of the sequence's evaluations. -/
theorem tendsto_measure_of_null_frontier {ι : Type*} [Nonempty X]
    {μ : ι → FiniteMeasure X} {ν : FiniteMeasure X} {L : Filter ι} {S : Set X}
    (h : Tendsto μ L (𝓝 ν)) (hS : (ν : Measure X) (frontier S) = 0) :
    Tendsto (fun j => (μ j : Measure X) S) L (𝓝 ((ν : Measure X) S)) := by
  simp_rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  apply (ENNReal.continuous_coe.tendsto _).comp
  by_cases hν : ν = 0
  · subst ν
    have hmass : Tendsto (fun j => (μ j).mass) L (𝓝 0) := by simpa using h.mass
    simpa using (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmass
      (fun j => (zero_le : 0 ≤ μ j S)) (fun j => (μ j).apply_le_mass S))
  · have hnul : ν.normalize (frontier S) = 0 := by
      apply ENNReal.coe_eq_zero.mp
      rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        ν.toMeasure_normalize_eq_of_nonzero hν, Measure.coe_nnreal_smul_apply, hS, mul_zero]
    have hprob : Tendsto (fun j => (μ j).normalize S) L (𝓝 (ν.normalize S)) :=
      ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
        (FiniteMeasure.tendsto_normalize_of_tendsto h hν) hnul
    convert h.mass.mul hprob using 1
    · funext j
      exact (μ j).self_eq_mass_mul_normalize S
    · exact congrArg nhds (ν.self_eq_mass_mul_normalize S)

/-- Select a ball radius at which the limit measure does not charge the frontier. -/
theorem exists_null_frontier_ball (μ : FiniteMeasure X) (x : X) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, (μ : Measure X) (frontier (Metric.ball x r)) = 0 := by
  simpa only [Metric.thickening_singleton] using
    exists_null_frontier_thickening (μ : Measure X) ({x} : Set X) hab

/-- The Portmanteau lower bound for open sets with arbitrary finite masses.
Convergence of total mass permits taking complements in the closed-set bound. -/
theorem measure_open_le_liminf {ι : Type*} {μ : ι → FiniteMeasure X} {ν : FiniteMeasure X}
    {L : Filter ι} (h : Tendsto μ L (𝓝 ν)) {G : Set X} (hG : IsOpen G) :
    (ν : Measure X) G ≤ L.liminf (fun n => (μ n : Measure X) G) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  let η : ℝ≥0∞ := (δ : ℝ≥0∞) / 2
  have hη : η ≠ 0 := (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr hδ.ne')).ne'
  have hηadd : η + η = (δ : ℝ≥0∞) := ENNReal.add_halves _
  have hcomp := FiniteMeasure.limsup_measure_closed_le_of_tendsto h hG.isClosed_compl
  have hcompEv : ∀ᶠ n in L, (μ n : Measure X) Gᶜ < (ν : Measure X) Gᶜ + η :=
    eventually_lt_of_limsup_lt (hcomp.trans_lt (ENNReal.lt_add_right (measure_ne_top _ _) hη))
  have hmass : Tendsto (fun n => (μ n : Measure X) univ) L (𝓝 ((ν : Measure X) univ)) := by
    have hcoe : Tendsto (fun n => ((μ n).mass : ℝ≥0∞)) L (𝓝 (ν.mass : ℝ≥0∞)) :=
      (ENNReal.continuous_coe.tendsto ν.mass).comp h.mass
    simpa only [FiniteMeasure.ennreal_mass] using hcoe
  have hmassEv : ∀ᶠ n in L, (ν : Measure X) univ < (μ n : Measure X) univ + η :=
    (hmass.add_const η).eventually
      (eventually_gt_nhds (ENNReal.lt_add_right (measure_ne_top _ _) hη))
  apply tsub_le_iff_right.mp
  refine le_liminf_of_le (h := ?_)
  filter_upwards [hcompEv, hmassEv] with n hn hnm
  apply tsub_le_iff_right.mpr
  apply (ENNReal.add_le_add_iff_right (measure_ne_top (ν : Measure X) Gᶜ)).mp
  calc
    (ν : Measure X) G + (ν : Measure X) Gᶜ = (ν : Measure X) univ :=
      measure_add_measure_compl hG.measurableSet
    _ ≤ (μ n : Measure X) univ + η := hnm.le
    _ = (μ n : Measure X) G + (μ n : Measure X) Gᶜ + η := by
      rw [measure_add_measure_compl hG.measurableSet]
    _ ≤ (μ n : Measure X) G + ((ν : Measure X) Gᶜ + η) + η := by gcongr
    _ = (μ n : Measure X) G + (η + η) + (ν : Measure X) Gᶜ := by ac_rfl
    _ = _ := by rw [hηadd]

end Thesis.MeasureGeometry

end
