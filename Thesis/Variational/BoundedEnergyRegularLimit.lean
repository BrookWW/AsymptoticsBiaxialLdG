module

public import Thesis.Variational.BoundedEnergyStrongLimit
public import Thesis.Upstream.Rellich
public import Thesis.Upstream.VacuumRegularity
import Thesis.Variational.BoundaryLimit

/-! The bounded-energy vacuum limit and its locally finite point singular set. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

/-- The actual bounded-energy family has one vacuum Dirichlet-minimizing
limit with strong local convergence and the actual regular representative. -/
theorem exists_boundedEnergy_regular_limit_of_projectionLayer (a : BulkCoefficients)
    (hProj : HasPenalizedProjectionLayer a) (M : ℝ) (hM : 0 < M)
    {Ω : Set Point} (hΩ : IsBoundedDomain Ω)
    (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient)
    (hMin : ∀ ε, IsLocalEnergyMinimizer a ε Ω (Q ε) (D ε))
    (hBounds : ∀ ε, energy a ε Ω (Q ε) (D ε) ≤ ENNReal.ofReal M ∧
      eLpNorm (Q ε) ⊤ (volume.restrict Ω) ≤ ENNReal.ofReal M) :
    ∃ (ε : ℕ → ElasticScale) (Q₀ : Point → S0) (D₀ : Point → Gradient) (S : Set Point),
      Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧ MemH1 Ω Q₀ D₀ ∧ TakesVacuumValues a Ω Q₀ ∧
      StrongH1Loc Ω (Q ∘ ε) (D ∘ ε) Q₀ D₀ ∧ ConvergesScaledPotentialLoc a Ω ε (Q ∘ ε) ∧
      IsLocalDirichletMinimizer a Ω Q₀ D₀ ∧ S ⊆ Ω ∧ LocallyFiniteIn Ω S ∧
      ContDiffOn ℝ ∞ Q₀ (Ω \ S) ∧ D₀ =ᵐ[volume.restrict (Ω \ S)] ClassicalGradient Q₀ := by
  obtain ⟨ε, v, G, hε, _, hv, hvVac, _, hStrong, _, _, hWeak⟩ :=
    exists_vacuum_weak_limit_of_bounded_energy_family a hΩ Q D hMin M hM hBounds
  let u := Q ∘ ε
  let d := D ∘ ε
  have hvLoc : MemH1Loc Ω v G := fun _ _ hW => hv.mono (subset_closure.trans hW.2)
  have hNorm (k : ℕ) : ∀ᵐ x ∂volume.restrict Ω, ‖u k x‖ ≤ M := by
    filter_upwards [enorm_ae_le_eLpNormEssSup (u k) (volume.restrict Ω)] with x hx
    apply (ENNReal.ofReal_le_ofReal_iff hM.le).1
    rw [ofReal_norm]
    have hb := (hBounds (ε k)).2
    rw [eLpNorm_exponent_top] at hb
    exact hx.trans hb
  have hFin (k : ℕ) : energy a (ε k) Ω (u k) (d k) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hBounds (ε k)).1
  have hB (c : Point) (R : ℝ) (_ : 0 < R) (hRΩ : closedBall c R ⊆ Ω) :
      ∃ B > 0, ∀ k, energy a (ε k) (ball c R) (u k) (d k) ≤ ENNReal.ofReal B :=
    ⟨M, hM, fun k => (lintegral_mono_set (ball_subset_closedBall.trans hRΩ)).trans (hBounds (ε k)).1⟩
  have hS (c : Point) (R : ℝ) (_ : 0 < R) (hRΩ : closedBall c R ⊆ Ω) :
      Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict (ball c R))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hStrong (fun _ => zero_le)
      (fun k => eLpNorm_mono_measure _ (Measure.restrict_mono_set _ (ball_subset_closedBall.trans hRΩ)))
  have hW (c : Point) (R : ℝ) (_ : 0 < R) (hRΩ : closedBall c R ⊆ Ω) (i : Fin 3) :
      WeakL2FrobeniusConvergence (ball c R) (fun k x => d k x i) (fun x => G x i) :=
    WeakL2FrobeniusConvergence.mono (hWeak i) measurableSet_ball (ball_subset_closedBall.trans hRΩ)
  obtain ⟨hConv, hPot, hMinV⟩ := strongH1Loc_and_minimizing_of_penalizedProjectionLayer a hProj hΩ.1
    ε hε u d v G (fun k => hMin (ε k)) hvLoc hvVac M hM hNorm hFin hB hS hW
  obtain ⟨hSfinite, w, hwEq, hwLoc, hwSmooth, hwGrad⟩ := vacuum_minimizer_exists_regularRepresentative a hΩ.1 hMinV
  have hw := hv.congr_ae hwEq.symm EventuallyEq.rfl
  have hwVac := hvVac.congr_ae hwEq.symm
  have hwMin : IsLocalDirichletMinimizer a Ω w G := by
    refine ⟨hwLoc, hwVac, ?_⟩
    intro c r hr hrΩ z J hz hzN hzT
    have hEq := ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hrΩ) hwEq
    exact hMinV.2.2 c r hr hrΩ z J hz hzN (hzT.congr_ae EventuallyEq.rfl hEq EventuallyEq.rfl EventuallyEq.rfl)
  have hConvW : StrongH1Loc Ω u d w G := by
    intro W hW hWΩ
    exact (hConv W hW hWΩ).congr_ae_limit
      (ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hWΩ.2) hwEq.symm) EventuallyEq.rfl
  refine ⟨ε, w, G, singularSet Ω v, hε, hw, hwVac, hConvW, hPot, hwMin, ?_, hSfinite, hwSmooth, hwGrad⟩
  exact fun _ hx => hx.1

end Thesis
