module

public import Thesis.MeasureGeometry.CylinderLateralClass
public import Thesis.Variational.InteriorBulkSmall
public import Thesis.MeasureGeometry.MeridianTrace
import Thesis.Variational.EulerLagrange

/-! Regular lateral estimates for the same representatives and weak-* sequence. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

/-- The original normalized measure is invariant under the verified
almost-everywhere change to a classical representative. -/
theorem normalizedEnergyMeasure_congr_ae
    (a : BulkCoefficients) (ε : ElasticScale) {Ω : Set Point}
    {Q P : Point → S0} {D G : Point → Gradient}
    (hQ : Q =ᵐ[volume.restrict Ω] P) (hD : D =ᵐ[volume.restrict Ω] G) :
    normalizedEnergyMeasure a ε Ω Q D = normalizedEnergyMeasure a ε Ω P G := by
  unfold normalizedEnergyMeasure
  apply withDensity_congr_ae
  filter_upwards [hQ, hD] with x hx hJ
  rw [hx, hJ]

/-- On an open domain, the bound of the actual bounded Sobolev
representative carries over pointwise to its continuous representative. -/
theorem pointwise_norm_bound_of_eqOn_ae {Ω : Set Point} (hΩ : IsOpen Ω)
    {u Q : Point → S0} {M : ℝ} (hM : 0 ≤ M)
    (hU : eLpNorm u ⊤ (volume.restrict Ω) ≤ ENNReal.ofReal M)
    (hQ : ContinuousOn Q Ω) (hEq : Q =ᵐ[volume.restrict Ω] u) :
    ∀ x ∈ Ω, ‖Q x‖ ≤ M := by
  have hBound : ∀ᵐ x ∂volume.restrict Ω, ‖Q x‖ ≤ M := by
    filter_upwards [enorm_ae_le_eLpNormEssSup u (volume.restrict Ω), hEq] with x hx he
    rw [he]
    apply (ENNReal.ofReal_le_ofReal_iff hM).mp
    rw [ofReal_norm]
    rw [eLpNorm_exponent_top] at hU
    exact hx.trans hU
  have h : (fun x => ‖Q x‖) =ᵐ[volume.restrict Ω] fun x => min ‖Q x‖ M :=
    hBound.mono fun _ hx => (min_eq_left hx).symm
  intro x hx
  exact (Measure.eqOn_open_of_ae_eq h hΩ hQ.norm (hQ.norm.inf continuousOn_const) hx).trans_le (min_le_right _ _)

private theorem strongH1_change_classicalData {U : Set Point}
    {u Q : ℕ → Point → S0} {D : ℕ → Point → Gradient} {q : Point → S0} {G : Point → Gradient}
    (hStrong : StrongH1 U u D q G)
    (hQ : ∀ n, u n =ᵐ[volume.restrict U] Q n)
    (hD : ∀ n, D n =ᵐ[volume.restrict U] ClassicalGradient (Q n))
    (hG : G =ᵐ[volume.restrict U] ClassicalGradient q) :
    StrongH1 U Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q) := by
  refine ⟨fun n => (hStrong.1 n).congr_ae (hQ n) (hD n),
    hStrong.2.1.congr_ae EventuallyEq.rfl hG, ?_⟩
  refine hStrong.2.2.congr' (Eventually.of_forall (fun n => ?_))
  unfold h1Deviation
  apply lintegral_congr_ae
  filter_upwards [hQ n, hD n, hG] with x hx hDx hGx
  rw [hx, hDx, hGx]

private theorem scaledPotential_change_classicalData (a : BulkCoefficients)
    {Ω R : Set Point} (hRΩ : R ⊆ Ω) {ε : ℕ → ElasticScale} {u Q : ℕ → Point → S0}
    (hQ : ∀ n, u n =ᵐ[volume.restrict Ω] Q n)
    (hPot : ConvergesScaledPotentialLoc a Ω ε u) : ConvergesScaledPotentialLoc a R ε Q := by
  intro U hU hUR
  have hUΩ : CompactlyContained U Ω := ⟨hUR.1, hUR.2.trans hRΩ⟩
  have hE (n : ℕ) : (fun x => ((ε n : ℝ)⁻¹ ^ 2) * bulkPotential a (u n x))
      =ᵐ[volume.restrict U] (fun x => ((ε n : ℝ)⁻¹ ^ 2) * bulkPotential a (Q n x)) :=
    (ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hUΩ.2) (hQ n)).mono
      (fun x hx => by
        change ((ε n : ℝ)⁻¹ ^ 2) * bulkPotential a (u n x) =
          ((ε n : ℝ)⁻¹ ^ 2) * bulkPotential a (Q n x)
        rw [hx])
  have hMem (n : ℕ) : MemLp (fun x => ((ε n : ℝ)⁻¹ ^ 2) * bulkPotential a (u n x))
      1 (volume.restrict U) := (hPot U hU hUΩ).1 n
  refine ⟨fun n => (memLp_congr_ae (hE n)).mp (hMem n), ?_⟩
  exact ((hPot U hU hUΩ).2).congr' (Eventually.of_forall fun n => eLpNorm_congr_ae (hE n))

/-- The original normalized measures, smooth representatives, and regular
interior convergence all retain the same sequence of elastic scales. -/
theorem regularCylinderData_of_sameSequence
    (a : BulkCoefficients) {Ω W R : Set Point} (hΩ : IsOpen Ω) (hR : IsOpen R)
    (hRW : R ⊆ W) (hWΩ : W ⊆ Ω)
    (hEstimate : InteriorPoissonGradientEstimate) (hMean : External.ClassicalScalarSubsolutionMeanValue)
    {M : ℝ} (hM : 0 ≤ M) (ε : ℕ → ElasticScale)
    (u Q : ℕ → Point → S0) (D : ℕ → Point → Gradient) (q : Point → S0) (G : Point → Gradient)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hu : ∀ n, MemH1Loc Ω (u n) (D n))
    (huB : ∀ n, eLpNorm (u n) ⊤ (volume.restrict Ω) ≤ ENNReal.ofReal M)
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω)
    (hEq : ∀ n, u n =ᵐ[volume.restrict Ω] Q n)
    (hEuler : ∀ n x, x ∈ Ω → (ε n : ℝ) ^ 2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x))
    (hStrong : StrongH1Loc W u D q G) (hBulk : ConvergesScaledPotentialLoc a W ε u)
    (hq : ContDiffOn ℝ ∞ q R) (hqVac : TakesVacuumValues a W q)
    (hG : G =ᵐ[volume.restrict R] ClassicalGradient q) :
    (∀ n, normalizedEnergyMeasure a (ε n) Ω (u n) (D n) =
      normalizedEnergyMeasure a (ε n) Ω (Q n) (ClassicalGradient (Q n))) ∧
    (∀ n x, x ∈ Ω → ‖Q n x‖ ≤ M) ∧ MapsTo q R (vacuum a) ∧
    (∀ K : Set Point, IsCompact K → K ⊆ R → ∃ C > (0 : ℝ),
      ∀ n x, x ∈ K → energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ C) ∧
    ∀ K : Set Point, IsCompact K → K ⊆ R → TendstoUniformlyOn Q q atTop K := by
  have hRΩ := hRW.trans hWΩ
  have hD (n : ℕ) : D n =ᵐ[volume.restrict Ω] ClassicalGradient (Q n) :=
    (hu n).ae_eq_classicalGradient hΩ ((hQ n).of_le (by decide)) (hEq n)
  have hMeasure (n : ℕ) := normalizedEnergyMeasure_congr_ae a (ε n) (hEq n) (hD n)
  have hBound (n : ℕ) := pointwise_norm_bound_of_eqOn_ae hΩ hM (huB n) (hQ n).continuousOn (hEq n).symm
  have hStrongR : StrongH1Loc R Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q) := by
    intro U hU hUR
    have hUΩ := subset_closure.trans (hUR.2.trans hRΩ)
    exact strongH1_change_classicalData (hStrong U hU ⟨hUR.1, hUR.2.trans hRW⟩)
      (fun n => ae_restrict_of_ae_restrict_of_subset hUΩ (hEq n))
      (fun n => ae_restrict_of_ae_restrict_of_subset hUΩ (hD n))
      (ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hUR.2) hG)
  have hEqW (n : ℕ) : u n =ᵐ[volume.restrict W] Q n :=
    ae_restrict_of_ae_restrict_of_subset hWΩ (hEq n)
  have hBulkR : ConvergesScaledPotentialLoc a R ε Q :=
    scaledPotential_change_classicalData a hRW hEqW hBulk
  have hVac : MapsTo q R (vacuum a) :=
    mapsTo_vacuum_of_continuousOn_of_takesVacuumValues a hR hq.continuousOn
      (ae_restrict_of_ae_restrict_of_subset hRW hqVac)
  have hq₂ : ContDiffOn ℝ 2 q R := hq.of_le (by decide)
  have hQ_R (n : ℕ) : ContDiffOn ℝ ∞ (Q n) R := (hQ n).mono hRΩ
  have hEulerR (n : ℕ) (x : Point) (hx : x ∈ R) := hEuler n x (hRΩ hx)
  have hBoundR (n : ℕ) (x : Point) (hx : x ∈ R) : ‖Q n x‖ ≤ max 0 M :=
    (hBound n x (hRΩ hx)).trans (le_max_right _ _)
  have hUniform := convergesC0Loc_of_strongH1Loc_of_regular_penalized_solutions a hR hEstimate hMean
    hq₂ ε Q hε hQ_R hEulerR hBoundR hStrongR hBulkR
  refine ⟨hMeasure, hBound, hVac, ?_, ?_⟩
  · intro K hK hKR
    exact exists_uniform_interior_energyDensity_bound a hR hK hKR hEstimate hMean
      hq₂ ε Q hε hQ_R hEulerR hBoundR hStrongR hBulkR
  · intro K hK hKR
    have h := hUniform.2.2 0 le_rfl K hK hKR
    apply tendstoUniformlyOn_iff.mpr
    intro d hd
    filter_upwards [(tendstoUniformlyOn_iff.mp h) d hd] with n hn x hx
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, LinearIsometryEquiv.dist_map] using hn x hx

end Thesis.MeasureGeometry
