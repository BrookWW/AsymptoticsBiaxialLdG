module

public import Thesis.Variational.GlobalClassical
public import Thesis.Variational.InteriorClassicalConvergence
public import Thesis.Variational.RegularClosureConvergence
public import Thesis.Variational.SmoothLimitFirstCorrection
import Thesis.Variational.ClassicalLimitTransfer
import Thesis.Variational.GlobalComparison
import Thesis.Variational.InteriorHarmonicRemainder
import Thesis.Variational.SmoothLocalJetCompactness
import Thesis.Variational.H10FractionalEmbedding
import Thesis.Variational.FractionalL2Duality
import Thesis.Variational.FractionalRellich
import Thesis.Variational.DirichletFractionalHardy
import Thesis.Variational.DirichletPoissonMorrey
import Thesis.Variational.ClassicalDirichletHessianBoundary
import Thesis.Variational.DirichletWallRegularity
import Thesis.Variational.DirichletAdjointRegularity
import Thesis.Variational.NonexpansiveTraceComposition
import Thesis.Variational.SmoothDomainTraceOperator
import Thesis.Variational.LipschitzGaussGreen
import Thesis.Variational.BoundaryPoissonL4Gradient
import Thesis.Variational.SubsolutionMeanValue
import Thesis.Variational.InteriorLinearPoissonDerivatives
import Thesis.Upstream.PoissonGradientBound
import Thesis.Upstream.PlanarMorseSard
import Thesis.Variational.VacuumHarmonicVariation
import Thesis.MeasureGeometry.MeridianTrace

/-! The global limit and correction with the original fixed boundary lift. -/

public section

open Set Filter MeasureTheory Metric
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

/-- The same global subsequence has its finite point singular set, fixed
wall values, all interior classical convergence and regular closure
Hölder convergence from the independent linear estimates. -/
theorem exists_globalEnergy_classical_limit
    (hReg : External.GlobalDirichletPoissonClosureC2)
    (hGG : External.LipschitzGaussGreen) (hSard : External.MorseSardPlaneToReal)
    (hPoisson : External.ZeroTraceBoundaryPoissonL4GradientEstimate)
    (hMean : External.ClassicalScalarSubsolutionMeanValue) (hInterior : InteriorPoissonGradientEstimate)
    (hHolder : External.GlobalDirichletPoissonGradientHolder)
    (a : BulkCoefficients) {Ω : Set Point} (hΩ : IsSmoothDomain Ω)
    (T : SobolevTraceOperator Ω) (hComp : NonexpansiveSobolevTraceComposition Ω)
    (hSU : External.SU83BoundaryRegularity)
    (b : frontier Ω → Sphere3) (hLift : IsSmoothBoundaryLift Ω b)
    (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient)
    (hMin : ∀ ε, IsGlobalEnergyMinimizer a ε Ω (fun x => cover a (b x)) (Q ε) (D ε)) :
    ∃ (ε : ℕ → ElasticScale) (q : Point → S0) (G : Point → Gradient) (v : ℕ → Point → S0) (B : Point → S0),
      let S := singularSet Ω q
      let U := Ω \ S
      Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧
      StrongH1 Ω (fun n => Q (ε n)) (fun n => D (ε n)) q G ∧
      IsGlobalDirichletMinimizer a Ω (fun x => cover a (b x)) q G ∧ S.Finite ∧
      (∀ n, v n =ᵐ[volume.restrict Ω] Q (ε n)) ∧
      (∀ n, D (ε n) =ᵐ[volume.restrict Ω] ClassicalGradient (v n)) ∧
      (∀ α : ℝ, 0 < α → α < 1 → ConvergesC1HolderLoc α Ω S v q) ∧
      (∀ j : ℕ, ConvergesCjLoc j U v q) ∧
      ContDiff ℝ ∞ B ∧ (∀ x : frontier Ω, B x = cover a (b x)) ∧
      (∀ n, (ContDiffOn ℝ 2 (v n) (closure Ω) ∧ ContDiffOn ℝ ∞ (v n) Ω) ∧ EqOn (v n) B (frontier Ω) ∧
        ∀ x ∈ Ω, (ε n : ℝ) ^ 2 • (laplacian (v n) x : S0).val = bulkGradient a (v n x)) ∧
      ContDiffOn ℝ 2 q (closure Ω \ S) ∧ (∀ x : frontier Ω, q x = cover a (b x)) ∧
      G =ᵐ[volume.restrict Ω] ClassicalGradient q ∧
      StrongH1 Ω v (fun n => ClassicalGradient (v n)) q G ∧
      BddAbove ((fun p : ℕ × Point => ‖v p.1 p.2‖) '' (univ ×ˢ Ω)) ∧
      ConvergesScaledPotentialLoc a Ω ε v ∧
      ∀ c ∈ frontier Ω, ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
        ∀ᶠ n in atTop, ∀ x ∈ Ω ∩ ball c r,
          energyDensity a (ε n) (v n x) (ClassicalGradient (v n) x) ≤ L := by
  obtain ⟨B, Qc, ε, q, G, V, hB, hBVal, hQc, hε, hStrong, hMinq, hFin, hV, hWallV, _,
    hqSmooth, hqCollar, hqWall, hGrad, hBulkLp, hBulk, _, hWall⟩ :=
    exists_classical_global_limit_with_regular_wall_collar hReg hGG hSard hPoisson hMean hInterior
      a hΩ T hComp hSU b hLift Q D hMin
  let v := Qc ∘ ε
  let S := singularSet Ω q
  let U := Ω \ S
  let Bdy := fun x : frontier Ω => cover a (b x)
  let M := max (Real.sqrt 2 * vacuumRadius a) (eLpNorm Bdy ⊤ (frontierSurfaceMeasure Ω)).toReal
  have hM : 0 ≤ M := (mul_nonneg (Real.sqrt_nonneg _) (vacuumRadius_pos a).le).trans (le_max_left _ _)
  have hOpen := isOpen_diff_singularSet (Ω := Ω) q
  have hvSmooth (n : ℕ) :
      ContDiffOn ℝ 2 (v n) (closure Ω) ∧ ContDiffOn ℝ ∞ (v n) Ω := (hQc (ε n)).2.2.1
  have hvWall (n : ℕ) : EqOn (v n) B (frontier Ω) := (hQc (ε n)).2.2.2.1
  have hvEuler (n : ℕ) (x : Point) (hx : x ∈ Ω) :
      (ε n : ℝ) ^ 2 • (laplacian (v n) x : S0).val = bulkGradient a (v n x) :=
    (hQc (ε n)).2.2.2.2 x hx
  have hvRange (n : ℕ) : ∀ x ∈ Ω, ‖v n x‖ ≤ M := by
    have hN := ae_norm_le_of_eLpNorm_top_le
      ((hMin (ε n)).eLpNorm_top_le_vacuumOrTrace hΩ.1.1 hΩ.1.2.2 hComp)
    change ∀ᵐ x ∂volume.restrict Ω, ‖Q (ε n) x‖ ≤ max 0 M at hN
    rw [max_eq_right hM] at hN
    apply pointwise_norm_le_of_ae_bound hΩ.1.1 ((hvSmooth n).2.continuousOn)
    filter_upwards [hN, (hQc (ε n)).1] with x hx he
    change ‖Qc (ε n) x‖ ≤ M
    rw [← he]
    exact hx
  have hStrongOriginal :
      StrongH1 Ω (fun n => Q (ε n)) (fun n => D (ε n)) q G :=
    hStrong.congr_ae_graphs (fun n => (hQc (ε n)).1.symm) (fun n => (hQc (ε n)).2.1.symm)
      EventuallyEq.rfl EventuallyEq.rfl
  have hStrongReg : StrongH1Loc U v (fun n => ClassicalGradient (v n)) q (ClassicalGradient q) := by
    intro W _ hWU
    exact (hStrong.congr_ae_graphs (fun _ => EventuallyEq.rfl) (fun _ => EventuallyEq.rfl)
      EventuallyEq.rfl hGrad).mono (subset_closure.trans (hWU.2.trans sdiff_subset))
  have hPot : ConvergesScaledPotentialLoc a Ω ε v := by
    intro W _ hW
    have hSub : W ⊆ Ω := subset_closure.trans hW.2
    have hμ := Measure.restrict_mono_set volume hSub
    exact ⟨fun n => (hBulkLp n).mono_measure hμ,
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hBulk
        (fun _ => zero_le) (fun n => eLpNorm_mono_measure _ hμ)⟩
  have hPotReg : ConvergesScaledPotentialLoc a U ε v :=
    fun W hW hWU => hPot W hW ⟨hWU.1, hWU.2.trans sdiff_subset⟩
  have hBound : BddAbove ((fun p : ℕ × Point => ‖v p.1 p.2‖) '' (univ ×ˢ U)) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨⟨n, x⟩, hx, rfl⟩
    exact hvRange n x hx.2.1
  have hCj := convergesCjLoc_of_regular_penalized_solutions a hInterior hMean hOpen ε v q hε
    (fun n => (hvSmooth n).2.mono sdiff_subset) hqSmooth
    (fun n x hx => hvEuler n x hx.1) hBound hStrongReg hPotReg
  have hQC : ContDiffOn ℝ 2 q (closure Ω \ S) :=
    contDiffOn_regular_closure_of_interior_and_wall hΩ.1.1 hFin.isClosed hV hWallV
      (hqSmooth.of_le (WithTop.coe_le_coe.mpr le_top)) hqCollar
  have hBvac : MapsTo B (frontier Ω) (vacuum a) := by
    intro x hx
    rw [hBVal ⟨x, hx⟩]
    exact cover_mem_vacuum a (b ⟨x, hx⟩)
  have hWall' (c : Point) (hc : c ∈ frontier Ω) : ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
        ∀ᶠ n in atTop, ∀ x ∈ Ω ∩ ball c r,
          energyDensity a (ε n) (v n x) (ClassicalGradient (v n) x) ≤ L := by
    obtain ⟨r, L, hr, hL, _, h⟩ := hWall c hc
    exact ⟨r / 2, L, half_pos hr, hL, h⟩
  have hC1 (α : ℝ) (hα : 0 < α) (hα₁ : α < 1) :
      ConvergesC1HolderLoc α Ω S v q :=
    convergesC1HolderLoc_of_regular_wall_energy_cap hHolder a hΩ hFin.isClosed hB hBvac ε v q hε
      (fun n => (hvSmooth n).1) hQC hvWall hvEuler hM hvRange (hCj 2) hWall' hα hα₁
  exact ⟨ε, q, G, v, B, hε, hStrongOriginal, hMinq, hFin, fun n => (hQc (ε n)).1.symm,
    fun n => (hQc (ε n)).2.1, hC1, hCj, hB, hBVal, fun n => ⟨hvSmooth n, hvWall n, hvEuler n⟩,
    hQC, hqWall, hGrad, hStrong,
    ⟨M, by rintro _ ⟨⟨n, x⟩, hx, rfl⟩; exact hvRange n x hx.2⟩, hPot, hWall'⟩

private theorem singularSet_eq_empty_of_contDiffOn {Ω : Set Point} (hΩ : IsOpen Ω)
    {q : Point → S0} (hq : ContDiffOn ℝ ∞ q Ω) : singularSet Ω q = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  exact hx.2 ⟨Ω, q, hΩ, hx.1, subset_rfl, hq, EventuallyEq.rfl⟩

/-- The literal Theorem 1.5 proposition, used by the explicit-input provider. -/
@[expose] def GlobalEnergyLimitAndCorrectionConclusion : Prop :=
  ∀ (a : BulkCoefficients) (Ω : Set Point), IsSmoothDomain Ω →
    ∀ (u_b : frontier Ω → Sphere3), IsSmoothBoundaryLift Ω u_b →
      ∀ (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient),
        let Q_b := fun x : frontier Ω => cover a (u_b x)
        (∀ ε, IsGlobalEnergyMinimizer a ε Ω Q_b (Q ε) (D ε)) →
        ∃ (ε : ℕ → ElasticScale) (Q₀ : Point → S0) (D₀ : Point → Gradient)
          (Qreg : ℕ → Point → S0),
          let S := singularSet Ω Q₀
          Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧
          StrongH1 Ω (fun n => Q (ε n)) (fun n => D (ε n)) Q₀ D₀ ∧
          IsGlobalDirichletMinimizer a Ω Q_b Q₀ D₀ ∧ S.Finite ∧
          (∀ n, Qreg n =ᵐ[volume.restrict Ω] Q (ε n)) ∧
          (∀ α : ℝ, 0 < α → α < 1 → ConvergesC1HolderLoc α Ω S Qreg Q₀) ∧
          (∀ j : ℕ, 2 ≤ j → ConvergesCjLoc j (Ω \ S) Qreg Q₀) ∧
          (ContDiffOn ℝ ∞ Q₀ Ω →
            (∃ L : H10 Ω →ₗ[ℝ] HMinusOne Ω,
              Function.Bijective L ∧
              ∀ v w : H10 Ω, L v w = linearizedPairing a Ω Q₀ D₀ v w) →
            ∃ Q₁ : Point → S0,
              let W := fun n x => (ε n : ℝ)⁻¹ ^ 2 • (Qreg n x - Q₀ x)
              let r := vacuumRadius a
              let Qperp := fun x => normalPart a (Q₀ x) (Q₁ x)
              let Qparallel := fun x => tangentPart a (Q₀ x) (Q₁ x)
              ContDiffOn ℝ ∞ Q₁ Ω ∧
              (∀ s : ℝ, 0 < s → s < 1/2 → ConvergesHs s Ω W Q₁) ∧
              (∀ j : ℕ, 2 ≤ j → ConvergesCjLoc j Ω W Q₁) ∧
              ∀ x ∈ Ω,
                let A : Tensor := Q₀ x
                let B : Tensor := Q₁ x
                (A * B).trace =
                  -(gradientNormSq (ClassicalGradient Q₀ x) /
                    (4*r^2*(a.a4 + 4*a.a6*r^2))) ∧
                (A^2 * B).trace =
                  -(gradientTraceMul (ClassicalGradient Q₀) (ClassicalGradient Q₀) A x /
                    (a.a6'*r^4)) ∧
                Qperp x = ((A*B).trace / (2*r^2)) • A +
                  ((A^2*B).trace / (2*r^4)) • (3 : ℝ) • biaxialQuadratic a A ∧
                laplacian Qparallel x = tangentCorrectionRhs a Q₀ Q₁ x)


/-- The complete global theorem relative to boundary regularity of the
limiting minimizing harmonic map. -/
theorem globalEnergyLimitAndCorrection_relative
    (hSU : External.SU83BoundaryRegularity) :
    GlobalEnergyLimitAndCorrectionConclusion := by
  unfold GlobalEnergyLimitAndCorrectionConclusion
  intro a Ω hΩ b hLift Q D Q_b hMin
  let hMean := classicalScalarSubsolutionMeanValue
  let hInterior := interiorPoissonGradientEstimate
  let hW2p := globalDirichletPoissonSecondDerivativeLp
  have hHolder := globalDirichletPoissonGradientHolder_of_secondDerivativeLp hW2p
  have hReg := globalDirichletPoissonClosureC2_of_zeroTrace weakZeroTracePoissonClosureTwo
  have hAdj := dirichletAdjointFractionalEstimate
  obtain ⟨T⟩ := hΩ.exists_sobolevTraceOperator
  have hComp := T.nonexpansiveSobolevTraceComposition hΩ
  obtain ⟨ε, q, G, v, B, hε, hStrong, hMinq, hS, hvQ, hDG, hC1, hCj, hB, hBval,
    hv, hqC, hqWall, hGrad, hStrongv, hBound, hBulk, _⟩ :=
    exists_globalEnergy_classical_limit hReg lipschitzGaussGreen morseSardPlaneToReal
      zeroTraceBoundaryPoissonL4GradientEstimate hMean hInterior hHolder a hΩ T hComp hSU
      b hLift Q D hMin
  by_cases hNondeg : ContDiffOn ℝ ∞ q Ω ∧
      ∃ L : H10 Ω →ₗ[ℝ] HMinusOne Ω, Function.Bijective L ∧
        ∀ z w : H10 Ω, L z w = linearizedPairing a Ω q G z w
  · obtain ⟨hq, hInv⟩ := hNondeg
    have hEmpty := singularSet_eq_empty_of_contDiffOn hΩ.1.1 hq
    have hSame (n : ℕ) : SameTrace Ω (v n) B (ClassicalGradient (v n)) (ClassicalGradient B) :=
      T.sameTrace_every_smoothLift hΩ.1.1 hΩ.1.2.2 (hStrongv.1 n)
        ((hMin (ε n)).2.1.congr_ae (hvQ n).symm (hDG n)) hB hBval
    have hqSame : SameTrace Ω q B (ClassicalGradient q) (ClassicalGradient B) :=
      T.sameTrace_every_smoothLift hΩ.1.1 hΩ.1.2.2 (hMinq.1.congr_ae EventuallyEq.rfl hGrad)
        (hMinq.2.1.congr_ae EventuallyEq.rfl hGrad) hB hBval
    have hBvac : MapsTo B (frontier Ω) (vacuum a) := by
      intro x hx
      rw [hBval ⟨x, hx⟩]
      exact cover_mem_vacuum a (b ⟨x, hx⟩)
    have hqVac := MeasureGeometry.mapsTo_vacuum_of_continuousOn_of_takesVacuumValues a hΩ.1.1
      hq.continuousOn hMinq.2.2.1
    have hHarm := (IsLocalDirichletMinimizer.harmonicRhs_of_regularRepresentative hΩ.1.1 hΩ.1.1 subset_rfl
      (hMinq.isLocalDirichletMinimizer hΩ.1.1) (hq.of_le (WithTop.coe_le_coe.mpr le_top)) EventuallyEq.rfl).2
    have hStrongLoc : StrongH1Loc Ω v (fun n => ClassicalGradient (v n)) q (ClassicalGradient q) := by
      intro W _ hW
      exact (hStrongv.congr_ae_graphs (fun _ => EventuallyEq.rfl) (fun _ => EventuallyEq.rfl)
        EventuallyEq.rfl hGrad).mono (subset_closure.trans hW.2)
    have hEuler (n : ℕ) := (hv n).2.2
    have hPack : SmoothLimitCorrectionData a Ω B ε v q G :=
      { domain := hΩ
        liftSmooth := hB
        liftVacuum := hBvac
        elasticLimit := hε
        approximantsClosed := fun n => (hv n).1.1
        approximantsSmooth := fun n => (hv n).1.2
        limitSmooth := hq
        limitSmoothClosure := by simpa only [hEmpty, sdiff_empty] using hqC
        approximantsTrace := fun n => (hv n).2.1
        limitTrace := fun x hx => (hqWall ⟨x, hx⟩).trans (hBval ⟨x, hx⟩).symm
        approximantsSameTrace := hSame
        limitSameTrace := hqSame
        limitVacuum := hqVac
        limitColumns := hGrad
        eulerEquation := hEuler
        harmonicEquation := hHarm
        closedHolder := by simpa only [hEmpty] using hC1 (1 / 2) (by norm_num) (by norm_num)
        interiorSmooth := fun j _ => by simpa only [hEmpty, sdiff_empty] using hCj j
        jacobiBijective := hInv
        interiorRemainderRate := exists_compact_projectedHarmonicRemainder_bound a hInterior hMean
          hΩ.1.1 ε v q hε (fun n => (hv n).1.2) hq hEuler hBound hStrongLoc hBulk }
    obtain ⟨κ, P, hκ, hP⟩ := exists_smooth_limit_firstCorrection_subsequence
      hW2p hInterior hAdj fractionalL2NormDuality dirichletFractionalHardyAndCollar
      fractionalSobolevCompactEmbedding h10FractionalEmbedding
      interiorLinearPoissonSystemDerivativeEstimate smoothLocalJetCompactness hPack
    exact ⟨ε ∘ κ, q, G, v ∘ κ, hε.comp hκ.tendsto_atTop, hStrong.subsequence hκ.tendsto_atTop, hMinq,
      hS, fun n => hvQ (κ n), fun α hα hα₁ => (hC1 α hα hα₁).subsequence hκ.tendsto_atTop,
      fun j _ => (hCj j).subsequence hκ.tendsto_atTop, fun _ _ => ⟨P, hP⟩⟩
  · exact ⟨ε, q, G, v, hε, hStrong, hMinq, hS, hvQ, hC1, fun j _ => hCj j,
      fun hq hInv => (hNondeg ⟨hq, hInv⟩).elim⟩

end Thesis
