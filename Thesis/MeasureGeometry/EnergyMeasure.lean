module

public import Thesis.Definitions
public import Thesis.MeasureGeometry.WeakConvergence

/-! The normalized energy measure and its limit on the closure of a bounded domain. -/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace Thesis

/-- The unnormalized energy as a measure on the ambient space. -/
noncomputable def energyMeasure (a : BulkCoefficients) (ε : ElasticScale)
    (Ω : Set Point) (u : Point → S0) (D : Point → Gradient) : Measure Point :=
  (volume.restrict Ω).withDensity (fun x => ENNReal.ofReal (energyDensity a ε (u x) (D x)))

theorem energyMeasure_apply (a : BulkCoefficients) (ε : ElasticScale)
    (Ω : Set Point) (u : Point → S0) (D : Point → Gradient) {S : Set Point}
    (hS : MeasurableSet S) : energyMeasure a ε Ω u D S = energy a ε (S ∩ Ω) u D := by
  rw [energyMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS]
  rfl

theorem log_inv_scale_pos (ε : ElasticScale) : 0 < Real.log (1 / (ε : ℝ)) := by
  apply Real.log_pos
  exact (lt_div_iff₀ ε.property.1).2 (by simpa only [one_mul] using ε.property.2)

/-- Evaluation of the normalized energy measure on a Borel subset of the ambient space. -/
theorem normalizedEnergyMeasure_apply (a : BulkCoefficients) (ε : ElasticScale)
    (Ω : Set Point) (u : Point → S0) (D : Point → Gradient) {S : Set Point}
    (hS : MeasurableSet S) :
    normalizedEnergyMeasure a ε Ω u D S =
      ENNReal.ofReal (Real.log (1 / (ε : ℝ)))⁻¹ * energy a ε (S ∩ Ω) u D := by
  rw [normalizedEnergyMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS]
  have hlog := log_inv_scale_pos ε
  have hpoint (x : Point) :
      ENNReal.ofReal (energyDensity a ε (u x) (D x) / Real.log (1 / (ε : ℝ))) =
        ENNReal.ofReal (Real.log (1 / (ε : ℝ)))⁻¹ *
          ENNReal.ofReal (energyDensity a ε (u x) (D x)) := by
    rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (inv_nonneg.mpr hlog.le)]
  simp_rw [hpoint]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem normalizedEnergyMeasure_compl_closure (a : BulkCoefficients) (ε : ElasticScale)
    (Ω : Set Point) (u : Point → S0) (D : Point → Gradient) :
    normalizedEnergyMeasure a ε Ω u D (closure Ω)ᶜ = 0 := by
  have he : (closure Ω)ᶜ ∩ Ω = ∅ :=
    disjoint_iff_inter_eq_empty.mp (disjoint_compl_left_iff_subset.mpr subset_closure)
  rw [normalizedEnergyMeasure_apply a ε Ω u D isClosed_closure.measurableSet.compl, he]
  simp [energy]

/-- The logarithmic energy cap bounds the mass uniformly for scales at most one half. -/
theorem normalizedEnergyMeasure_mass_le (a : BulkCoefficients) (ε : ElasticScale)
    (hε : (ε : ℝ) ≤ 1 / 2) (Ω : Set Point) (u : Point → S0) (D : Point → Gradient)
    (M : ℝ) (hM : 0 ≤ M)
    (hE : energy a ε Ω u D ≤ ENNReal.ofReal (M * (Real.log (1 / (ε : ℝ)) + 1))) :
    normalizedEnergyMeasure a ε Ω u D univ ≤ ENNReal.ofReal (M * (1 + (Real.log 2)⁻¹)) := by
  let L := Real.log (1 / (ε : ℝ))
  have hL : 0 < L := log_inv_scale_pos ε
  have htwo : (2 : ℝ) ≤ 1 / (ε : ℝ) := (le_div_iff₀ ε.property.1).2 (by linarith)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLlower : Real.log 2 ≤ L := Real.log_le_log (by norm_num) htwo
  have hinv : L⁻¹ ≤ (Real.log 2)⁻¹ := (inv_le_inv₀ hL hlogTwo).2 hLlower
  rw [normalizedEnergyMeasure_apply a ε Ω u D MeasurableSet.univ, univ_inter]
  calc
    _ ≤ ENNReal.ofReal L⁻¹ * ENNReal.ofReal (M * (L + 1)) :=
      by gcongr
    _ = ENNReal.ofReal (M * (1 + L⁻¹)) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hL.le)]
      congr 1
      field_simp
    _ ≤ _ := by gcongr

/-- One subsequence gives both the weak-* statement on the compact closure and
ambient weak convergence, so later open and closed ball tests use the same limit. -/
theorem normalizedEnergyMeasure_subsequence (a : BulkCoefficients)
    {Ω : Set Point} (hΩ : IsBoundedDomain Ω)
    (ε : ℕ → ElasticScale) (hε : ∀ n, (ε n : ℝ) ≤ 1 / 2)
    (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient)
    (M : ℝ) (hM : 0 ≤ M)
    (hE : ∀ n, energy a (ε n) Ω (Q (ε n)) (D (ε n)) ≤
      ENNReal.ofReal (M * (Real.log (1 / (ε n : ℝ)) + 1))) :
    ∃ (ν : FiniteMeasure Point) (s : ℕ → ℕ), StrictMono s ∧
      (ν : Measure Point) (closure Ω)ᶜ = 0 ∧
      WeakStarOnClosure Ω
        (fun n => normalizedEnergyMeasure a (ε (s n)) Ω (Q (ε (s n))) (D (ε (s n)))) ν ∧
      ∃ (μ : ℕ → FiniteMeasure Point),
        (∀ n, (μ n : Measure Point) =
          normalizedEnergyMeasure a (ε n) Ω (Q (ε n)) (D (ε n))) ∧
        Tendsto (μ ∘ s) atTop (𝓝 ν) := by
  let K := closure Ω
  have hK : IsCompact K := hΩ.2.2.isCompact_closure
  let B := ENNReal.ofReal (M * (1 + (Real.log 2)⁻¹))
  let m : ℕ → Measure Point := fun n => normalizedEnergyMeasure a (ε n) Ω (Q (ε n)) (D (ε n))
  have hmass (n : ℕ) : m n univ ≤ B :=
    normalizedEnergyMeasure_mass_le a (ε n) (hε n) Ω (Q (ε n)) (D (ε n)) M hM (hE n)
  let μ : ℕ → FiniteMeasure Point := fun n =>
    ⟨m n, ⟨(hmass n).trans_lt ENNReal.ofReal_lt_top⟩⟩
  have hμ (n : ℕ) : (μ n).mass ≤ B.toNNReal :=
    ENNReal.toNNReal_mono ENNReal.ofReal_ne_top (hmass n)
  have hs (n : ℕ) : (μ n : Measure Point) Kᶜ = 0 :=
    normalizedEnergyMeasure_compl_closure a (ε n) Ω (Q (ε n)) (D (ε n))
  obtain ⟨ν, s, hmono, hsupp, hamb, htest⟩ :=
    MeasureGeometry.exists_supportedFiniteMeasure_subsequence
      hK hΩ.2.1.nonempty.closure μ B.toNNReal hμ hs
  refine ⟨ν, s, hmono, hsupp, ?_, μ, fun n => rfl, hamb⟩
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  intro φ
  exact MeasureGeometry.tendsto_continuous_integral_of_finiteMeasure_tendsto htest φ

theorem support_subset_closure_of_compl_null {Ω : Set Point} {ν : Measure Point}
    (hν : ν (closure Ω)ᶜ = 0) :
    IsClosed ν.support ∧ ν.support ⊆ closure Ω := by
  refine ⟨ν.isClosed_support, Measure.support_subset_of_isClosed isClosed_closure ?_⟩
  change ∀ᵐ x ∂ν, x ∈ closure Ω
  rw [ae_iff]
  exact hν

/-- For finite measures carried by the closure, weak-* tests on the closure
also give weak convergence in the ambient finite-measure topology. -/
theorem finiteMeasure_tendsto_of_weakStarOnClosure {Ω : Set Point}
    {μ : ℕ → FiniteMeasure Point} {ν : FiniteMeasure Point}
    (hμ : ∀ n, (μ n : Measure Point) (closure Ω)ᶜ = 0)
    (hν : (ν : Measure Point) (closure Ω)ᶜ = 0)
    (h : WeakStarOnClosure Ω (fun n => (μ n : Measure Point)) ν) :
    Tendsto μ atTop (𝓝 ν) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro φ
  let φ' : C(closure Ω, ℝ) := ⟨fun x => φ x, φ.continuous.comp continuous_subtype_val⟩
  have compare (m : Measure Point) (hm : m (closure Ω)ᶜ = 0) :
      (∫ x, φ x ∂m) = ∫ y, φ' y ∂m.comap ((↑) : closure Ω → Point) := by
    let f : closure Ω → Point := Subtype.val
    have hf : MeasurableEmbedding f := MeasurableEmbedding.subtype_coe isClosed_closure.measurableSet
    have hmap : Measure.map f (Measure.comap f m) = m := by
      rw [map_comap_subtype_coe isClosed_closure.measurableSet]
      apply Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff]
      exact hm
    change (∫ x, φ x ∂m) = ∫ y, φ (f y) ∂m.comap f
    rw [← hf.integral_map, hmap]
  simp_rw [compare _ (hμ _), compare _ hν]
  exact h φ'

/-- Weak-* normalized energy compactness for an entire family with the source
logarithmic energy bound. -/
theorem exists_normalizedEnergyMeasure_limit (a : BulkCoefficients)
    {Ω : Set Point} (hΩ : IsBoundedDomain Ω)
    (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient)
    (M : ℝ) (hM : 0 ≤ M)
    (hE : ∀ ε, energy a ε Ω (Q ε) (D ε) ≤
      ENNReal.ofReal (M * (Real.log (1 / (ε : ℝ)) + 1))) :
    ∃ (ε : ℕ → ElasticScale) (ν : FiniteMeasure Point),
      Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧
      (ν : Measure Point) (closure Ω)ᶜ = 0 ∧
      WeakStarOnClosure Ω (fun n => normalizedEnergyMeasure a (ε n) Ω (Q (ε n)) (D (ε n))) ν ∧
      IsClosed (ν : Measure Point).support ∧ (ν : Measure Point).support ⊆ closure Ω := by
  let initial (n : ℕ) : ElasticScale := ⟨1 / ((n : ℝ) + 2), by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    refine ⟨by positivity, (div_lt_iff₀ (by positivity)).2 ?_⟩
    linarith only [hn]⟩
  have hsmall (n : ℕ) : (initial n : ℝ) ≤ 1 / 2 := by
    change 1 / ((n : ℝ) + 2) ≤ 1 / 2
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact (div_le_iff₀ (by positivity)).2 (by linarith only [hn])
  have ht : Tendsto (fun n => (initial n : ℝ)) atTop (𝓝 0) := by
    have H := (tendsto_add_atTop_iff_nat 1).2
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [initial, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using H
  obtain ⟨ν, s, hmono, hsupp, hweak, _, _, _⟩ :=
    normalizedEnergyMeasure_subsequence a hΩ initial hsmall Q D M hM fun n => hE (initial n)
  exact ⟨initial ∘ s, ν, ht.comp hmono.tendsto_atTop, hsupp, hweak,
    support_subset_closure_of_compl_null hsupp⟩

end Thesis

end
