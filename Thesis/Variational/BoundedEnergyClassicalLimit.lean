module

public import Thesis.Variational.BoundedEnergyRegularLimit
public import Thesis.Variational.ClassicalLimitTransfer
public import Thesis.Variational.VacuumHarmonicVariation
public import Thesis.Variational.EulerLagrange

/-! The original bounded family and its regular classical graph on one subsequence. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

/-- The same bounded-energy limit has the whole-domain weak harmonic
equation, original smooth approximants, and the classical Sobolev graph
on the actual complement of its point singular set. -/
theorem exists_boundedEnergy_classical_limit_of_projectionLayer (a : BulkCoefficients)
    (hProj : HasPenalizedProjectionLayer a) (hReg : InteriorPoissonRegularity) (M : ℝ) (hM : 0 < M)
    {Ω : Set Point} (hΩ : IsBoundedDomain Ω)
    (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient)
    (hMin : ∀ ε, IsLocalEnergyMinimizer a ε Ω (Q ε) (D ε))
    (hBounds : ∀ ε, energy a ε Ω (Q ε) (D ε) ≤ ENNReal.ofReal M ∧
      eLpNorm (Q ε) ⊤ (volume.restrict Ω) ≤ ENNReal.ofReal M) :
    ∃ (ε : ℕ → ElasticScale) (q : Point → S0) (G : Point → Gradient) (S : Set Point)
      (v : ℕ → Point → S0),
      let U := Ω \ S
      Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧ MemH1 Ω q G ∧ TakesVacuumValues a Ω q ∧
      StrongH1Loc Ω (Q ∘ ε) (D ∘ ε) q G ∧ ConvergesScaledPotentialLoc a Ω ε (Q ∘ ε) ∧
      IsLocalDirichletMinimizer a Ω q G ∧ WeakLaplacianEq Ω G (harmonicRhs a q G) ∧
      S ⊆ Ω ∧ LocallyFiniteIn Ω S ∧ IsOpen U ∧ ContDiffOn ℝ ∞ q U ∧
      (∀ n, v n =ᵐ[volume.restrict Ω] Q (ε n)) ∧
      (∀ n, D (ε n) =ᵐ[volume.restrict Ω] ClassicalGradient (v n)) ∧
      (∀ n, ContDiffOn ℝ ∞ (v n) Ω) ∧
      (∀ n x, x ∈ Ω → (ε n : ℝ) ^ 2 • (laplacian (v n) x : S0).val = bulkGradient a (v n x)) ∧
      (∀ n x, x ∈ Ω → ‖v n x‖ ≤ M) ∧
      StrongH1Loc U v (fun n => ClassicalGradient (v n)) q (ClassicalGradient q) ∧
      ConvergesScaledPotentialLoc a U ε v := by
  obtain ⟨ε, q, G, S, hε, hq, hVac, hStrong, hPot, hMinq, hS, hF, hSmooth, hGrad⟩ :=
    exists_boundedEnergy_regular_limit_of_projectionLayer a hProj M hM hΩ Q D hMin hBounds
  have hV (n : ℕ) := exists_smoothRepresentative_of_localEnergyMinimizer_of_eLpNorm_top_le
    a (ε n) hΩ.1 (hMin (ε n)) hReg (hBounds (ε n)).2
  choose v hv hvSmooth hvG hvEuler using hV
  have hvBounds (n : ℕ) : ∀ x ∈ Ω, ‖v n x‖ ≤ M := by
    have hN := ae_norm_le_of_eLpNorm_top_le (hBounds (ε n)).2
    rw [max_eq_right hM.le] at hN
    apply pointwise_norm_le_of_ae_bound hΩ.1 (hvSmooth n).continuousOn
    filter_upwards [hN, hv n] with x hx he
    rw [← he]
    exact hx
  let U := Ω \ S
  have hU : IsOpen U := hF.isOpen_sdiff hΩ.1
  have hSub : U ⊆ Ω := sdiff_subset
  have hUQ (n : ℕ) : Q (ε n) =ᵐ[volume.restrict U] v n :=
    ae_restrict_of_ae_restrict_of_subset hSub (hv n)
  have hUD (n : ℕ) : D (ε n) =ᵐ[volume.restrict U] ClassicalGradient (v n) :=
    ae_restrict_of_ae_restrict_of_subset hSub (hvG n)
  have hS' := hStrong.congr_ae_on_subset hSub hUQ hUD
    (Filter.EventuallyEq.refl _ _) hGrad
  have hP' := hPot.congr_ae_on_subset hSub hUQ
  exact ⟨ε, q, G, S, v, hε, hq, hVac, hStrong, hPot, hMinq,
    (hMinq.weakLaplacianEq_harmonicRhs hΩ.1).2, hS, hF, hU, hSmooth,
    fun n => (hv n).symm, hvG, hvSmooth, hvEuler, hvBounds, hS', hP'⟩

end Thesis
