module

public import Thesis.MeasureGeometry.LogarithmicSupport
public import Thesis.Variational.LocalEnergyRegularLimit
public import Thesis.Variational.EulerLagrange
import Thesis.MeasureGeometry.EnergyMeasure

/-! The common measure and strong Sobolev subsequence in the logarithmic regime. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius NNReal Topology

namespace Thesis.MeasureGeometry

/-- Normalized measures, off-support comparison, the vacuum map and the
stationary interior varifold are carried by one sequence and one limit. -/
theorem exists_logarithmic_limit_core (a : BulkCoefficients)
    (hProj : HasPenalizedProjectionLayer a) (hDense : External.SmoothVacuumSphereDensity a)
    (hP : External.QuaternionSpherePoincare 3 (by decide : 2 ≤ 3)) (hA19 : External.A19Prop31)
    (hReg : InteriorPoissonRegularity) (M : ℝ) (hM : 0 < M) :
    ∃ C : Set Point → ℝ → ℝ,
      (∀ U r, 0 < C U r) ∧
      ∀ (Ω : Set Point), IsBoundedDomain Ω →
      ∀ (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient),
        (∀ ε, IsLocalEnergyMinimizer a ε Ω (Q ε) (D ε)) →
        (∀ ε, energy a ε Ω (Q ε) (D ε) ≤ ENNReal.ofReal (M * (Real.log (1 / (ε : ℝ)) + 1)) ∧
          eLpNorm (Q ε) ⊤ (volume.restrict Ω) ≤ ENNReal.ofReal M) →
        ∃ (ε : ℕ → ElasticScale) (ν : FiniteMeasure Point)
          (Q₀ : Point → S0) (D₀ : Point → Gradient) (Qreg : ℕ → Point → S0),
          let S := (ν : Measure Point).support
          let W := Ω \ S
          let Spts := singularSet W Q₀
          Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧
          (ν : Measure Point) (closure Ω)ᶜ = 0 ∧ IsClosed S ∧ S ⊆ closure Ω ∧
          WeakStarOnClosure Ω (fun n => normalizedEnergyMeasure a (ε n) Ω (Q (ε n)) (D (ε n))) ν ∧
          CountablyRectifiableOne (Ω ∩ S) ∧ HausdorffOne (Ω ∩ S) < ⊤ ∧
          (∀ U : Set Point, IsOpen U → CompactlyContained U W →
            ∃ B > (0 : ℝ), ∀ n, energy a (ε n) U (Q (ε n)) (D (ε n)) ≤ ENNReal.ofReal B) ∧
          (∀ (U : Set Point) (r : ℝ), IsOpen U → CompactlyContained U W → 0 < r →
            (∀ x ∈ closure U, closedBall x r ⊆ W) →
            ∀ᶠ n in atTop, energy a (ε n) U (Q (ε n)) (D (ε n)) ≤ ENNReal.ofReal (C U r)) ∧
          IsLocalDirichletMinimizer a W Q₀ D₀ ∧ WeakLaplacianEq W D₀ (harmonicRhs a Q₀ D₀) ∧
          StrongH1Loc W (Q ∘ ε) (D ∘ ε) Q₀ D₀ ∧ ConvergesScaledPotentialLoc a W ε (Q ∘ ε) ∧
          LocallyFiniteIn W Spts ∧ ContDiffOn ℝ ∞ Q₀ (W \ Spts) ∧
          D₀ =ᵐ[volume.restrict (W \ Spts)] ClassicalGradient Q₀ ∧
          (∀ n, Qreg n =ᵐ[volume.restrict Ω] Q (ε n)) ∧ (∀ n, ContDiffOn ℝ ∞ (Qreg n) Ω) ∧
          (∀ n, ∀ x ∈ Ω, (ε n : ℝ) ^ 2 • (laplacian (Qreg n) x : S0).val = bulkGradient a (Qreg n x)) ∧
          (∃ c > (0 : ℝ), ∀ x ∈ Ω ∩ S, ∃ θ ≥ c, Tendsto (oneDensity ν x) (𝓝[>] 0) (𝓝 θ)) ∧
          ∃ V : Measure (Point × LineProjection), IsAssociatedVarifold Ω (Ω ∩ S) ν V ∧ IsStationaryVarifold Ω V := by
  obtain ⟨C, hC, hOff⟩ := exists_offSupport_energy_bounds_of_projectionLayer a hProj hDense hP M hM
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ Q D hMin hBounds
  let initial (n : ℕ) : ElasticScale := ⟨1 / ((n : ℝ) + 2), by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    refine ⟨by positivity, (div_lt_iff₀ (by positivity)).2 ?_⟩
    linarith only [hn]⟩
  have hsmall (n : ℕ) : (initial n : ℝ) ≤ 1 / 2 := by
    change 1 / ((n : ℝ) + 2) ≤ 1 / 2
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact (div_le_iff₀ (by positivity)).2 (by linarith only [hn])
  have ht : Tendsto (fun n => (initial n : ℝ)) atTop (𝓝 0) := by
    have H := (tendsto_add_atTop_iff_nat 1).2 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [initial, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using H
  obtain ⟨ν, s, hs, hν, hStar, μ, hμ, hμLim⟩ := normalizedEnergyMeasure_subsequence a hΩ
    initial hsmall Q D M hM.le (fun n => (hBounds (initial n)).1)
  let ε := initial ∘ s
  let u := Q ∘ ε
  let J := D ∘ ε
  let m := μ ∘ s
  have hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) := ht.comp hs.tendsto_atTop
  have hm (n : ℕ) : (m n : Measure Point) = normalizedEnergyMeasure a (ε n) Ω (u n) (J n) := hμ (s n)
  have hFin (n : ℕ) : energy a (ε n) Ω (u n) (J n) < ⊤ := (hBounds (ε n)).1.trans_lt ENNReal.ofReal_lt_top
  have hRange (n : ℕ) : ∀ᵐ x ∂volume.restrict Ω, ‖u n x‖ ≤ M := by
    filter_upwards [enorm_ae_le_eLpNormEssSup (u n) (volume.restrict Ω)] with x hx
    apply (ENNReal.ofReal_le_ofReal_iff hM.le).1
    rw [ofReal_norm]
    have hb := (hBounds (ε n)).2
    rw [eLpNorm_exponent_top] at hb
    exact hx.trans hb
  have hV (n : ℕ) := exists_smoothRepresentative_of_localEnergyMinimizer_of_eLpNorm_top_le
    a (ε n) hΩ.1 (hMin (ε n)) hReg (hBounds (ε n)).2
  choose v hv hvs hvD hvEq using hV
  let B : ℝ≥0 := (ENNReal.ofReal (M * (1 + (Real.log 2)⁻¹))).toNNReal
  have hMass (n : ℕ) : (m n).mass ≤ B := by
    apply ENNReal.toNNReal_mono ENNReal.ofReal_ne_top
    rw [hm n]
    exact normalizedEnergyMeasure_mass_le a (ε n) (hsmall (s n)) Ω (u n) (J n) M hM.le (hBounds (ε n)).1
  let S := (ν : Measure Point).support
  let W := Ω \ S
  have hSupport := support_subset_closure_of_compl_null hν
  have hW : IsOpen W := hΩ.1.sdiff hSupport.1
  have hBoundsW := hOff Ω hΩ.1 ε hε u J m ν (fun n => hMin (ε n)) hRange hm hμLim hFin
  obtain ⟨c, hc, hSupportData⟩ := logarithmic_limit_rectifiable_support_of_projectionLayer a hProj hDense hP hA19 M hM
  obtain ⟨hDensity, hRect, hLength, V, hAssoc, hStat⟩ :=
    hSupportData hΩ hε (fun n => hMin (ε n)) hRange hv hvD hvs hvEq hm hμLim B hMass
  have hWΩ : W ⊆ Ω := sdiff_subset
  have hMinW (n : ℕ) : IsLocalEnergyMinimizer a (ε n) W (u n) (J n) := by
    refine ⟨fun U hU hUW => (hMin (ε n)).1 U hU ⟨hUW.1, hUW.2.trans hWΩ⟩, ?_⟩
    exact fun c r hr hrW => (hMin (ε n)).2 c r hr (hrW.trans hWΩ)
  have hNormW (n : ℕ) : ∀ᵐ x ∂volume.restrict W, ‖u n x‖ ≤ M :=
    ae_restrict_of_ae_restrict_of_subset hWΩ (hRange n)
  have hFinW (n : ℕ) : energy a (ε n) W (u n) (J n) ≠ ⊤ :=
    ((lintegral_mono_set hWΩ).trans_lt (hFin n)).ne
  obtain ⟨κ, Q₀, D₀, hκ, hQMin, hQHarm, hStrong, hPot, hSfinite, hQSmooth, hQGrad⟩ :=
    exists_local_vacuum_regular_limit_of_projectionLayer a hProj hW ε hε u J hMinW M hM hNormW hFinW
      (fun U hU hUW => (hBoundsW U hU hUW).1)
  let δ := ε ∘ κ
  refine ⟨δ, ν, Q₀, D₀, v ∘ κ, hε.comp hκ.tendsto_atTop, hν, hSupport.1, hSupport.2,
    fun φ => (hStar φ).comp hκ.tendsto_atTop, hRect, hLength, ?_, ?_, hQMin, hQHarm,
    hStrong, hPot, hSfinite, hQSmooth, hQGrad, fun n => (hv (κ n)).symm, fun n => hvs (κ n),
    fun n => hvEq (κ n), ?_, V, hAssoc, hStat⟩
  · intro U hU hUW
    obtain ⟨B, hB, h⟩ := (hBoundsW U hU hUW).1
    exact ⟨B, hB, fun n => h (κ n)⟩
  · intro U r hU hUW hr hClosed
    exact hκ.tendsto_atTop.eventually ((hBoundsW U hU hUW).2 r hr hClosed)
  · refine ⟨c / 2, half_pos hc, fun x hx => ?_⟩
    obtain ⟨θ, hθ, _, hPoint⟩ := hDensity x hx.1
    exact ⟨θ, hPoint.1 hx.2, hθ⟩

end Thesis.MeasureGeometry
