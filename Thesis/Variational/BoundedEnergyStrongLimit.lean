module

public import Thesis.Variational.GoodRadiusAnnularComparison
import StratificationTheory.Compactness.InteriorBallEnlargement

/-! Strong local convergence and vacuum Dirichlet minimality from the projection layer. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

/-- An actual vacuum weak limit gains strong local Sobolev convergence,
vanishing scaled potential and local Dirichlet minimality. The energy cap
is local on each compactly contained ball. -/
theorem strongH1Loc_and_minimizing_of_penalizedProjectionLayer (a : BulkCoefficients)
    (hProj : HasPenalizedProjectionLayer a) {Ω : Set Point} (hΩ : IsOpen Ω)
    (ε : ℕ → ElasticScale) (hε : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0))
    (u : ℕ → Point → S0) (D : ℕ → Point → Gradient) (v : Point → S0) (G : Point → Gradient)
    (hMin : ∀ k, IsLocalEnergyMinimizer a (ε k) Ω (u k) (D k))
    (hv : MemH1Loc Ω v G) (hVac : TakesVacuumValues a Ω v)
    (M : ℝ) (hM : 0 < M) (hNorm : ∀ k, ∀ᵐ x ∂volume.restrict Ω, ‖u k x‖ ≤ M)
    (hFinite : ∀ k, energy a (ε k) Ω (u k) (D k) ≠ ⊤)
    (hBound : ∀ c R, 0 < R → closedBall c R ⊆ Ω →
      ∃ B : ℝ, 0 < B ∧ ∀ k, energy a (ε k) (ball c R) (u k) (D k) ≤ ENNReal.ofReal B)
    (hStrong : ∀ c R, 0 < R → closedBall c R ⊆ Ω →
      Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict (ball c R))) atTop (𝓝 0))
    (hWeak : ∀ c R, 0 < R → closedBall c R ⊆ Ω → ∀ j : Fin 3,
      WeakL2FrobeniusConvergence (ball c R) (fun k x => D k x j) (fun x => G x j)) :
    StrongH1Loc Ω u D v G ∧ ConvergesScaledPotentialLoc a Ω ε u ∧ IsLocalDirichletMinimizer a Ω v G := by
  have hLocal (c : Point) (r : ℝ) (hr : 0 < r) (hrΩ : closedBall c r ⊆ Ω) :
      CompactlyContained (ball c r) Ω := by
    unfold CompactlyContained
    rw [closure_ball c hr.ne']
    exact ⟨isCompact_closedBall _ _, hrΩ⟩
  have hUB (k : ℕ) (c : Point) (r : ℝ) (hr : 0 < r) (hrΩ : closedBall c r ⊆ Ω) :
      MemH1 (ball c r) (u k) (D k) := (hMin k).1 _ isOpen_ball (hLocal c r hr hrΩ)
  have hVB (c : Point) (r : ℝ) (hr : 0 < r) (hrΩ : closedBall c r ⊆ Ω) :
      MemH1 (ball c r) v G := hv _ isOpen_ball (hLocal c r hr hrΩ)
  have hVN (c : Point) (r : ℝ) (hrΩ : closedBall c r ⊆ Ω) : TakesVacuumValues a (ball c r) v :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hrΩ) hVac
  have hBall (c : Point) (r : ℝ) (hr : 0 < r) (hrΩ : closedBall c r ⊆ Ω) :
      (StrongH1 (ball c r) u D v G ∧
        Tendsto (fun k => eLpNorm (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (u k x))
          1 (volume.restrict (ball c r))) atTop (𝓝 0)) ∧
      (∀ z J, MemH1 (ball c r) z J → TakesVacuumValues a (ball c r) z →
        SameTrace (ball c r) z v J G → dirichletEnergy (ball c r) G ≤ dirichletEnergy (ball c r) J) := by
    obtain ⟨R, hrR, hRΩ⟩ := StratificationTheory.Compactness.exists_larger_closedBall_in_openDomain
      ⟨Ω, hΩ⟩ c hr.le hrΩ
    have hR : 0 < R := hr.trans hrR
    obtain ⟨B, hB, hEB⟩ := hBound c R hR hRΩ
    have hRB : ball c R ⊆ Ω := ball_subset_closedBall.trans hRΩ
    have hFinBall (k : ℕ) : energy a (ε k) (ball c R) (u k) (D k) ≠ ⊤ :=
      ne_top_of_le_ne_top (hFinite k) (lintegral_mono_set hRB)
    have hTail : ∀ᶠ k in atTop, (ε k : ℝ) < r := hε.eventually_lt_const hr
    have hConn (ι : ℕ → ℕ) (hι : StrictMono ι) :
        ∃ (s : ℝ) (hs : s ∈ Ioo r R) (κ : ℕ → ℕ) (cost : ℕ → ℝ≥0∞),
          StrictMono κ ∧ Tendsto cost atTop (𝓝 0) ∧
          ∀ᶠ k in atTop, ∃ W : RadialAnnularConnector c s R hs.2 (u (ι (κ k))) v,
            energy a (ε (ι (κ k))) (radialAnnulus c W.radius s) W.toFun W.gradient ≤ cost k := by
      obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hι.tendsto_atTop.eventually hTail)
      let τ (k : ℕ) := n₀ + k
      have hτ : StrictMono τ := fun _ _ h => Nat.add_lt_add_left h _
      let σ := ι ∘ τ
      have hσ : StrictMono σ := hι.comp hτ
      obtain ⟨s, hs, κ, cost, hκ, hCost, hShells⟩ := exists_goodRadius_annular_connectors a hProj hΩ c hr hrR hRΩ
        (ε ∘ σ) (hε.comp hσ.tendsto_atTop) (fun k => hn₀ (τ k) (Nat.le_add_right n₀ k))
        (u ∘ σ) (D ∘ σ) v G (fun k => (hMin (σ k)).1) hv hVac M B hM hB
        (fun k => ae_restrict_of_ae_restrict_of_subset hRB (hNorm (σ k)))
        (fun k => hEB (σ k)) ((hStrong c R hR hRΩ).comp hσ.tendsto_atTop)
      exact ⟨s, hs, τ ∘ κ, cost, hτ.comp hκ, hCost, hShells⟩
    constructor
    · apply strongH1_and_scaledPotential_of_ball_subsubsequences a ε c r u D v G
        (fun k => hUB k c r hr hrΩ) (hVB c r hr hrΩ)
      intro ι hι
      obtain ⟨s, hs, κ, cost, hκ, hCost, hShells⟩ := hConn ι hι
      let σ := ι ∘ κ
      have hσ : StrictMono σ := hι.comp hκ
      have hs₀ : 0 < s := hr.trans hs.1
      have hsΩ : closedBall c s ⊆ Ω := (closedBall_subset_closedBall hs.2.le).trans hRΩ
      have hW : ∀ i : Fin 3, WeakL2FrobeniusConvergence (ball c s) (fun k x => D (σ k) x i) (fun x => G x i) := by
        intro i ψ
        exact (hWeak c s hs₀ hsΩ i ψ).comp hσ.tendsto_atTop
      obtain ⟨hsH, _, hsP, _⟩ := strongH1_and_scaledPotential_of_annular_connectors a (ε ∘ σ) c hs.2 hRΩ
        (u ∘ σ) (D ∘ σ) v G (fun k => hMin (σ k)) (fun k => hFinBall (σ k))
        (fun k => hUB (σ k) c s hs₀ hsΩ) (hVB c s hs₀ hsΩ) (hVN c s hsΩ)
        ((hStrong c s hs₀ hsΩ).comp hσ.tendsto_atTop) hW cost hCost hShells
      have hSub : ball c r ⊆ ball c s := ball_subset_ball hs.1.le
      refine ⟨κ, hκ, hsH.mono hSub, ?_⟩
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsP (fun _ => zero_le) ?_
      intro k
      exact eLpNorm_mono_measure _ (Measure.restrict_mono_set _ hSub)
    · intro z J _ hzN hzTrace
      obtain ⟨s, hs, κ, cost, hκ, hCost, hShells⟩ := hConn id strictMono_id
      have hs₀ : 0 < s := hr.trans hs.1
      have hsΩ : closedBall c s ⊆ Ω := (closedBall_subset_closedBall hs.2.le).trans hRΩ
      have hW : ∀ i : Fin 3, WeakL2FrobeniusConvergence (ball c s) (fun k x => D (κ k) x i) (fun x => G x i) := by
        intro i ψ
        exact (hWeak c s hs₀ hsΩ i ψ).comp hκ.tendsto_atTop
      have hMinS := dirichletComparison_of_annular_connectors a (ε ∘ κ) c hs₀ hs.2 hRΩ (u ∘ κ) (D ∘ κ)
        v G (fun k => hMin (κ k)) (fun k => hFinBall (κ k)) (fun k => hUB (κ k) c s hs₀ hsΩ)
        (hVB c R hR hRΩ) (hVN c R hRΩ) hW cost hCost hShells
      exact dirichletComparison_on_smaller_concentric_ball a c hs.1.le v G (hVB c s hs₀ hsΩ)
        (hVN c s hsΩ) hMinS z J hzN hzTrace
  obtain ⟨hH, hPot⟩ := strongH1Loc_and_scaledPotentialLoc_of_ball_convergence a ε hΩ u D v G
    (fun k => (hMin k).1) hv hFinite (fun c r hr hrΩ => (hBall c r hr hrΩ).1)
  exact ⟨hH, hPot, hv, hVac, fun c r hr hrΩ => (hBall c r hr hrΩ).2⟩

end Thesis
