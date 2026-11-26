module

public import Thesis.Variational.CorrectionWeakOperatorData
public import Thesis.Variational.InteriorCorrectionCoefficients
public import Thesis.Variational.InteriorCorrectionConvergence
public import Thesis.Variational.ScaledFirstCorrectionEstimate
public import Thesis.Variational.FractionalCorrectionCompactness
public import Thesis.Variational.FirstCorrectionEquations

/-! The strong first correction for a smooth global limit. -/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance smoothLimitCorrectionFunctionalENorm : ContinuousENorm S0 :=
  SeminormedAddGroup.toContinuousENorm

local instance smoothLimitCorrectionCoefficientNormed : NormedAddCommGroup ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance smoothLimitCorrectionCoefficientSpace : NormedSpace ℝ ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance smoothLimitCorrectionDualNormed (U : Set Point) : NormedAddCommGroup (HMinusOne U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance smoothLimitCorrectionDualSpace (U : Set Point) : NormedSpace ℝ (HMinusOne U) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance smoothLimitCorrectionInverseNormed (U : Set Point) :
    NormedAddCommGroup (HMinusOne U →L[ℝ] H10 U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

/-- The original smooth-limit fields and their fixed trace in the
nondegenerate branch of the global theorem. -/
structure SmoothLimitCorrectionData
    (a : BulkCoefficients) (U : Set Point) (b : Point → S0)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (q : Point → S0) (D : Point → Gradient) : Prop where
  domain : IsSmoothDomain U
  liftSmooth : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) b
  liftVacuum : MapsTo b (frontier U) (vacuum a)
  elasticLimit : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)
  approximantsClosed : ∀ n, ContDiffOn ℝ 2 (Q n) (closure U)
  approximantsSmooth : ∀ n, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (Q n) U
  limitSmooth : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) q U
  limitSmoothClosure : ContDiffOn ℝ 2 q (closure U)
  approximantsTrace : ∀ n, EqOn (Q n) b (frontier U)
  limitTrace : EqOn q b (frontier U)
  approximantsSameTrace : ∀ n, SameTrace U (Q n) b (ClassicalGradient (Q n)) (ClassicalGradient b)
  limitSameTrace : SameTrace U q b (ClassicalGradient q) (ClassicalGradient b)
  limitVacuum : MapsTo q U (vacuum a)
  limitColumns : D =ᵐ[volume.restrict U] ClassicalGradient q
  eulerEquation : ∀ n, ∀ x ∈ U,
    (ε n : ℝ)^2 • (↑(laplacian (Q n) x) : Tensor) = bulkGradient a (Q n x)
  harmonicEquation : ∀ x ∈ U, (↑(laplacian q x) : Tensor) = harmonicRhs a q (ClassicalGradient q) x
  closedHolder : ConvergesC1HolderLoc (1/2) U ∅ Q q
  interiorSmooth : ∀ j : ℕ, 2 ≤ j → ConvergesCjLoc j U Q q
  jacobiBijective : ∃ L : H10 U →ₗ[ℝ] HMinusOne U, Function.Bijective L ∧
    ∀ v w : H10 U, L v w = linearizedPairing a U q D v w
  interiorRemainderRate : ∀ K : Set Point, IsCompact K → K ⊆ U → ∀ j : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (projectedHarmonicRemainder a (ε n) (Q n)) x‖ ≤ C * (ε n : ℝ)^2

def scaledFirstCorrectionDifference
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (q : Point → S0) (n : ℕ) (x : Point) : S0 :=
  (ε n : ℝ)⁻¹^2 • (Q n x - q x)

def scaledFirstCorrectionSource
    (a : BulkCoefficients) (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (n : ℕ) (x : Point) : S0 :=
  (ε n : ℝ)⁻¹^2 • projectedHarmonicRemainder a (ε n) (Q n) x

private theorem contDiffOn_laplacian_of_smooth
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0}
    (hQ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (laplacian Q) U := by
  have hD {f : Point → S0} (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) f U) (j : Fin 3) :
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (coordDeriv j f) U := by
    have hd : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (ClassicalGradient f) U :=
      (contDiffOn_correctionStateField hU hf).snd
    exact (contDiffOn_pi.mp hd) j
  unfold laplacian
  exact ContDiffOn.sum fun j _ => hD (hD hQ j) j

private theorem contDiffOn_projected_remainder_of_classical_equation
    (a : BulkCoefficients) (ε : ElasticScale) {U : Set Point} (hU : IsOpen U) {Q : Point → S0}
    (hQ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U)
    (hEq : ∀ x ∈ U, (ε : ℝ)^2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (projectedHarmonicRemainder a ε Q) U := by
  have h := (contDiffOn_laplacian_of_smooth hU hQ).add
    ((contDiff_projectedHarmonicNonlinearity a).comp_contDiffOn (contDiffOn_correctionStateField hU hQ))
  have h' : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (projectedHarmonicExpression a Q) U := h
  exact h'.congr fun x hx => (projectedHarmonicExpression_eq_remainder a ε Q x (hEq x hx)).symm

private theorem memLp_scaled_remainder_of_classical_closure
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    (ε : ElasticScale) {Q : Point → S0} (hQ₂ : ContDiffOn ℝ 2 Q (closure U))
    (hQ : ContDiffOn ℝ ∞ Q U)
    (hEq : ∀ x ∈ U, (ε : ℝ)^2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) :
    MemLp (fun x => (ε : ℝ)⁻¹^2 • projectedHarmonicRemainder a ε Q x) 2 (volume.restrict U) := by
  have hQ₁ : ContDiffOn ℝ 1 Q (closure U) := hQ₂.of_le (by norm_num)
  obtain ⟨M, F, hM, hF, hQv, hQl⟩ := exists_value_laplacian_bound_of_contDiffOn_closure hU hQ₂
  let D (x : Point) (j : Fin 3) := fderivWithin ℝ Q (closure U) x (axis j)
  have hD : ContinuousOn D (closure U) := by
    apply continuousOn_pi.mpr
    intro j
    exact (ContinuousLinearMap.apply ℝ S0 (axis j)).continuous.comp_continuousOn
      (hQ₁.continuousOn_fderivWithin hU.uniqueDiffOn_closure le_rfl)
  obtain ⟨D₀, hD₀⟩ := hU.1.2.2.isCompact_closure.exists_bound_of_continuousOn hD
  let N (p : S0 × Gradient) := projectedHarmonicNonlinearity a p.1 p.2
  let R := max M (max D₀ 0)
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : S0 × Gradient) R).exists_bound_of_continuousOn
    (contDiff_projectedHarmonicNonlinearity a).continuous.continuousOn
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  apply MemLp.of_bound (((contDiffOn_projected_remainder_of_classical_equation a ε hU.1.1
    hQ hEq).const_smul ((ε : ℝ)⁻¹^2)).continuousOn.aestronglyMeasurable
      hU.1.1.measurableSet) ((ε : ℝ)⁻¹^2*(F+max B 0))
  filter_upwards [ae_restrict_mem (μ := volume) hU.1.1.measurableSet] with x hx
  have hCol : D x = ClassicalGradient Q x := closureGradient_eq_classical_on_interior hU.1.1 hQ₁ hx
  have hDG := hD₀ x (subset_closure hx)
  rw [hCol] at hDG
  have hX : correctionStateField Q x ∈ Metric.closedBall (0 : S0 × Gradient) R := by
    apply mem_closedBall_zero_iff.mpr
    rw [Prod.norm_def]
    exact max_le ((hQv x hx).trans (le_max_left _ _))
      (hDG.trans ((le_max_left _ _).trans (le_max_right _ _)))
  have hN : ‖N (correctionStateField Q x)‖ ≤ max B 0 := (hB _ hX).trans (le_max_left _ _)
  rw [← projectedHarmonicExpression_eq_remainder a ε Q x (hEq x hx), norm_smul,
    Real.norm_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact (norm_add_le _ _).trans (add_le_add (hQl x hx) hN)

private theorem scaled_smooth_limit_H10_representatives
    {a : BulkCoefficients} {U : Set Point} {b : Point → S0}
    {ε : ℕ → ElasticScale} {Q : ℕ → Point → S0} {q : Point → S0} {D : Point → Gradient}
    (h : SmoothLimitCorrectionData a U b ε Q q D) :
    ∀ n, ∃ v : H10 U, h10Value v =ᵐ[volume.restrict U] scaledFirstCorrectionDifference ε Q q n ∧
      h10Gradient v =ᵐ[volume.restrict U] ClassicalGradient (scaledFirstCorrectionDifference ε Q q n) := by
  intro n
  let c := (ε n : ℝ)⁻¹^2
  obtain ⟨v,hVal,hGrad⟩ := exists_scaled_H10_difference_of_sameTrace h.domain.1.1
    (h.approximantsSameTrace n) h.limitSameTrace c
  refine ⟨v,hVal,?_⟩
  have hDiff (x : Point) (hx : x ∈ U) :
      ClassicalGradient (scaledFirstCorrectionDifference ε Q q n) x =
        c • (ClassicalGradient (Q n) x - ClassicalGradient q x) := by
    have h₁ := (((h.approximantsSmooth n) x hx).contDiffAt (h.domain.1.1.mem_nhds hx)).differentiableAt (by simp)
    have h₂ := ((h.limitSmooth x hx).contDiffAt (h.domain.1.1.mem_nhds hx)).differentiableAt (by simp)
    have hD := ((h₁.hasFDerivAt.sub h₂.hasFDerivAt).const_smul c).fderiv
    funext j
    exact DFunLike.congr_fun hD (axis j)
  filter_upwards [hGrad, ae_restrict_mem (μ := volume) h.domain.1.1.measurableSet] with x hx hxU
  exact hx.trans (hDiff x hxU).symm

private theorem scaled_smooth_limit_weak_equation
    {a : BulkCoefficients} {U : Set Point} {b : Point → S0}
    {ε : ℕ → ElasticScale} {Q : ℕ → Point → S0} {q : Point → S0} {D : Point → Gradient}
    (h : SmoothLimitCorrectionData a U b ε Q q D) (n : ℕ)
    (L : H10 U ≃L[ℝ] HMinusOne U)
    (hPair : ∀ z w : H10 U, L z w = weakCorrectionPairing U (averagedCorrectionCoefficient a q (Q n)) z w) :
    ∃ v : H10 U, h10Value v =ᵐ[volume.restrict U] scaledFirstCorrectionDifference ε Q q n ∧
      ∀ w : H10 U, L v w = ∫ x in U, frobeniusS0 (scaledFirstCorrectionSource a ε Q n x) (h10Value w x) := by
  obtain ⟨v,hVal,hGrad⟩ := scaled_smooth_limit_H10_representatives h n
  have hF₂ := memLp_scaled_remainder_of_classical_closure a h.domain (ε n)
    (h.approximantsClosed n) (h.approximantsSmooth n) (h.eulerEquation n)
  have hQ₂ : ContDiffOn ℝ 2 (Q n) U :=
    (h.approximantsClosed n).mono subset_closure
  have hq₂ : ContDiffOn ℝ 2 q U := h.limitSmooth.of_le (WithTop.coe_le_coe.mpr le_top)
  have hW : ContDiffOn ℝ 2 (scaledFirstCorrectionDifference ε Q q n) U :=
    (hQ₂.sub hq₂).const_smul ((ε n : ℝ)⁻¹^2)
  have hPde (x : Point) (hx : x ∈ U) :
      laplacian (scaledFirstCorrectionDifference ε Q q n) x +
        averagedCorrectionCoefficient a q (Q n) x (scaledFirstCorrectionDifference ε Q q n x,
          ClassicalGradient (scaledFirstCorrectionDifference ε Q q n) x) = scaledFirstCorrectionSource a ε Q n x :=
    scaled_firstCorrection_equation a (ε n) h.domain.1.1 hQ₂ hq₂ hx
      (h.limitVacuum hx) (h.harmonicEquation x hx) (h.eulerEquation n x hx)
  refine ⟨v,hVal,?_⟩
  exact h10_weakEquation_of_classical_weakCorrectionPairing h.domain.1.1
    (averagedCorrectionCoefficient a q (Q n)) L.toContinuousLinearMap hPair hW hF₂ v hVal hGrad hPde


private theorem exists_eventual_scaled_smooth_limit_forcing_bound
    (hPoisson : InteriorPoissonGradientEstimate)
    (hHardy : External.DirichletFractionalHardyAndCollar)
    {a : BulkCoefficients} {U : Set Point} {b : Point → S0}
    {ε : ℕ → ElasticScale} {Q : ℕ → Point → S0} {q : Point → S0} {D : Point → Gradient}
    (h : SmoothLimitCorrectionData a U b ε Q q D) (s : ℝ) (hs : 0 < s) (hs₁ : s < 1/2) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ᶠ n in atTop, HasFractionalDirichletForcingBound s U
      (scaledFirstCorrectionSource a ε Q n) N := by
  obtain ⟨c,C,hc,hC,hR⟩ := exists_eventual_projectedHarmonicRemainder_wall_profile_of_global_C1Holder
    a hPoisson h.domain h.approximantsClosed h.approximantsSmooth
    (fun n x hx => (h.approximantsTrace n hx).symm ▸ h.liftVacuum hx)
    h.limitVacuum h.eulerEquation h.closedHolder
  obtain ⟨K,hK,hForce⟩ := exists_scaled_dirichlet_forcing_bound_of_wall_profile hHardy h.domain s c hs hs₁ hc
  refine ⟨K*C,mul_nonneg hK hC.le,?_⟩
  filter_upwards [hR] with n hRn
  have hRmeas : AEStronglyMeasurable (projectedHarmonicRemainder a (ε n) (Q n))
      (volume.restrict U) :=
    (contDiffOn_projected_remainder_of_classical_equation a (ε n) h.domain.1.1
      (h.approximantsSmooth n) (h.eulerEquation n)).continuousOn.aestronglyMeasurable
        h.domain.1.1.measurableSet
  have hF := hForce (projectedHarmonicRemainder a (ε n) (Q n)) C (ε n) hC.le
    (ε n).2.1 hRmeas hRn
  change HasFractionalDirichletForcingBound s U
    (fun x => (↑(ε n) : ℝ)⁻¹^2 • projectedHarmonicRemainder a (ε n) (Q n) x) (K*C)
  rw [inv_pow]
  exact hF

private theorem eventual_scaled_correction_weak_data
    (hW2p : External.GlobalDirichletPoissonSecondDerivativeLp)
    (hPoisson : InteriorPoissonGradientEstimate)
    (hHardy : External.DirichletFractionalHardyAndCollar)
    {a : BulkCoefficients} {U : Set Point} {b : Point → S0}
    {ε : ℕ → ElasticScale} {Q : ℕ → Point → S0} {q : Point → S0} {D : Point → Gradient}
    (h : SmoothLimitCorrectionData a U b ε Q q D) (s : ℝ) (hs : 0 < s) (hs₁ : s < 1/2) :
    ∃ M N : ℝ, 0 ≤ M ∧ 0 ≤ N ∧ ∀ᶠ n in atTop, ∃ (L : H10 U ≃L[ℝ] HMinusOne U) (v : H10 U),
      HasBoundedDirichletCorrectionCoefficients U 4 M (averagedCorrectionCoefficient a q (Q n)) ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ M ∧
      (∀ z w : H10 U, L z w = weakCorrectionPairing U (averagedCorrectionCoefficient a q (Q n)) z w) ∧
      HasFractionalDirichletForcingBound s U (scaledFirstCorrectionSource a ε Q n) N ∧
      h10Value v =ᵐ[volume.restrict U] scaledFirstCorrectionDifference ε Q q n ∧
      (∀ w : H10 U, L v w = ∫ x in U, frobeniusS0 (scaledFirstCorrectionSource a ε Q n x) (h10Value w x)) := by
  have hOperators := @exists_eventual_weakCorrectionOperator_data hW2p a U h.domain b h.liftSmooth 4
    (by norm_num) ε Q q D h.approximantsClosed h.approximantsSmooth h.limitSmooth h.limitSmoothClosure
    (fun n x hx => (h.approximantsTrace n hx).symm ▸ h.liftVacuum hx) h.approximantsTrace h.limitTrace
    h.limitVacuum h.limitColumns h.eulerEquation h.closedHolder h.jacobiBijective
  obtain ⟨M,hM,hOp⟩ := hOperators
  have hForcing := exists_eventual_scaled_smooth_limit_forcing_bound hPoisson hHardy h s hs hs₁
  obtain ⟨N,hN,hForce⟩ := hForcing
  refine ⟨M,N,hM,hN,?_⟩
  filter_upwards [hOp,hForce] with n hn hFn
  obtain ⟨L,hL,hCoeff,hPair⟩ := hn
  have hScaled := @scaled_smooth_limit_weak_equation a U b ε Q q D h n L hPair
  obtain ⟨v,hVal,hWeak⟩ := hScaled
  exact ⟨L,v,hCoeff,hL,hPair,hFn,hVal,hWeak⟩

theorem exists_eventual_Hs_bound_smooth_limit_correction
    (hW2p : External.GlobalDirichletPoissonSecondDerivativeLp)
    (hPoisson : InteriorPoissonGradientEstimate)
    (hAdj : External.DirichletAdjointFractionalEstimate) (hDual : External.FractionalL2NormDuality)
    (hHardy : External.DirichletFractionalHardyAndCollar)
    {a : BulkCoefficients} {U : Set Point} {b : Point → S0}
    {ε : ℕ → ElasticScale} {Q : ℕ → Point → S0} {q : Point → S0} {D : Point → Gradient}
    (h : SmoothLimitCorrectionData a U b ε Q q D) (s : ℝ) (hs : 0 < s) (hs₁ : s < 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      MemHs s U (scaledFirstCorrectionDifference ε Q q n) ∧
      Real.sqrt ((fractionalEnergy s U (scaledFirstCorrectionDifference ε Q q n)).toReal) ≤ C := by
  obtain ⟨M,N,hM,hN,hEq⟩ := eventual_scaled_correction_weak_data hW2p hPoisson hHardy h s hs hs₁
  exact exists_eventual_Hs_bound_of_weakCorrection_data hAdj hDual h.domain s 4 M N hs hs₁
    (by norm_num) hM hN (scaledFirstCorrectionDifference ε Q q) (scaledFirstCorrectionSource a ε Q)
    (fun n => averagedCorrectionCoefficient a q (Q n)) hEq

private theorem exists_smooth_limit_correction_subsequence_from_L2
    (hInterior : External.InteriorLinearPoissonSystemDerivativeEstimate)
    (hJet : External.SmoothLocalJetCompactness)
    {a : BulkCoefficients} {U : Set Point} {b : Point → S0}
    {ε : ℕ → ElasticScale} {Q : ℕ → Point → S0} {q : Point → S0} {D : Point → Gradient}
    (h : SmoothLimitCorrectionData a U b ε Q q D) {C : ℝ} (hC : 0 ≤ C)
    (hL2 : ∀ᶠ n in atTop, MemLp (scaledFirstCorrectionDifference ε Q q n) 2 (volume.restrict U) ∧
      eLpNorm (scaledFirstCorrectionDifference ε Q q n) 2 (volume.restrict U) ≤ ENNReal.ofReal C) :
    ∃ (κ : ℕ → ℕ) (P : Point → S0), StrictMono κ ∧ ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) P U ∧
      ∀ j : ℕ, 2 ≤ j → ConvergesCjLoc j U (scaledFirstCorrectionDifference ε Q q ∘ κ) P := by
  let W := scaledFirstCorrectionDifference ε Q q
  let F := scaledFirstCorrectionSource a ε Q
  let A (n : ℕ) := averagedCorrectionCoefficient a q (Q n)
  have hOpen := h.domain.1.1
  have hQOpen (n : ℕ) : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (Q n) U :=
    h.approximantsSmooth n
  have hW (n : ℕ) : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (W n) U :=
    ((hQOpen n).sub h.limitSmooth).const_smul ((ε n : ℝ)⁻¹^2)
  have hR (n : ℕ) : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (projectedHarmonicRemainder a (ε n) (Q n)) U :=
    contDiffOn_projected_remainder_of_classical_equation a (ε n) hOpen (hQOpen n) (h.eulerEquation n)
  have hF (n : ℕ) : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (F n) U := (hR n).const_smul ((ε n : ℝ)⁻¹^2)
  have hA (n : ℕ) : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (A n) U :=
    (contDiff_averagedHarmonicLinearization a).comp_contDiffOn
      ((contDiffOn_correctionStateField hOpen h.limitSmooth).prodMk (contDiffOn_correctionStateField hOpen (hQOpen n)))
  have hPde (n : ℕ) (x : Point) (hx : x ∈ U) :
      laplacian (W n) x + A n x (W n x, ClassicalGradient (W n) x) = F n x :=
    scaled_firstCorrection_equation a (ε n) hOpen
      ((hQOpen n).of_le (WithTop.coe_le_coe.mpr le_top)) (h.limitSmooth.of_le (WithTop.coe_le_coe.mpr le_top)) hx
      (h.limitVacuum hx) (h.harmonicEquation x hx) (h.eulerEquation n x hx)
  have hFC (K : Set Point) (hK : IsCompact K) (hKU : K ⊆ U) (j : ℕ) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ j (F n) x‖ ≤ B := by
    obtain ⟨B,hB,hRate⟩ := h.interiorRemainderRate K hK hKU j
    refine ⟨B,hB,?_⟩
    filter_upwards [hRate] with n hn x hx
    have hAt : ContDiffAt ℝ j (projectedHarmonicRemainder a (ε n) (Q n)) x :=
      (((hR n) x (hKU hx)).contDiffAt (hOpen.mem_nhds (hKU hx))).of_le (WithTop.coe_le_coe.mpr le_top)
    have hScale : iteratedFDeriv ℝ j (F n) x =
        (ε n : ℝ)⁻¹^2 • iteratedFDeriv ℝ j (projectedHarmonicRemainder a (ε n) (Q n)) x := by
      change iteratedFDeriv ℝ j
        (((ε n : ℝ)⁻¹^2 : ℝ) • projectedHarmonicRemainder a (ε n) (Q n)) x = _
      exact iteratedFDeriv_const_smul_apply (a := (ε n : ℝ)⁻¹^2) hAt
    rw [hScale,norm_smul,Real.norm_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hn x hx) (sq_nonneg _)).trans_eq (by
      rw [inv_pow]
      field_simp [(ε n).2.1.ne'])
  exact exists_smooth_correction_subsequence_of_linear_system hInterior hJet hOpen A W F hA hW hF hPde hC hL2
    (fun K hK hKU j => exists_eventual_compact_derivative_bound_averagedCorrectionCoefficient
      a hOpen hK hKU hQOpen h.limitSmooth h.interiorSmooth j) hFC

/-- The actual smooth-limit correction converges after a single
subsequence in every stated fractional and local smooth topology, and
satisfies the exact first-correction identities. -/
theorem exists_smooth_limit_firstCorrection_subsequence
    (hW2p : External.GlobalDirichletPoissonSecondDerivativeLp)
    (hPoisson : InteriorPoissonGradientEstimate)
    (hAdj : External.DirichletAdjointFractionalEstimate) (hDual : External.FractionalL2NormDuality)
    (hHardy : External.DirichletFractionalHardyAndCollar)
    (hFractional : External.FractionalSobolevCompactEmbedding) (hEmbed : External.H10FractionalEmbedding)
    (hInterior : External.InteriorLinearPoissonSystemDerivativeEstimate)
    (hJet : External.SmoothLocalJetCompactness)
    {a : BulkCoefficients} {U : Set Point} {b : Point → S0}
    {ε : ℕ → ElasticScale} {Q : ℕ → Point → S0} {q : Point → S0} {D : Point → Gradient}
    (h : SmoothLimitCorrectionData a U b ε Q q D) :
    ∃ (κ : ℕ → ℕ) (P : Point → S0), StrictMono κ ∧
      let W := scaledFirstCorrectionDifference (ε ∘ κ) (Q ∘ κ) q
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) P U ∧
      (∀ s : ℝ, 0 < s → s < 1/2 → ConvergesHs s U W P) ∧
      (∀ j : ℕ, 2 ≤ j → ConvergesCjLoc j U W P) ∧
      ∀ x ∈ U,
        let r := vacuumRadius a
        let A : Tensor := q x
        let B : Tensor := P x
        (A*B).trace = -(gradientNormSq (ClassicalGradient q x) / (4*r^2*(a.a4+4*a.a6*r^2))) ∧
        (A^2*B).trace = -(gradientTraceMul (ClassicalGradient q) (ClassicalGradient q) A x / (a.a6'*r^4)) ∧
        normalPart a A B = ((A*B).trace/(2*r^2)) • A +
          ((A^2*B).trace/(2*r^4)) • (3 : ℝ) • biaxialQuadratic a A ∧
        laplacian (fun y => tangentPart a (q y) (P y)) x = tangentCorrectionRhs a q P x := by
  let W := scaledFirstCorrectionDifference ε Q q
  have hHs (s : ℝ) (hs : 0 < s) (hs₁ : s < 1/2) :=
    exists_eventual_Hs_bound_smooth_limit_correction hW2p hPoisson hAdj hDual hHardy h s hs hs₁
  obtain ⟨C,hC,hHsTop⟩ := hHs (1/4) (by norm_num) (by norm_num)
  have hL2 : ∀ᶠ n in atTop, MemLp (W n) 2 (volume.restrict U) ∧
      eLpNorm (W n) 2 (volume.restrict U) ≤ ENNReal.ofReal C :=
    hHsTop.mono fun n hn => hn.1.memLp_two_and_eLpNorm_le_of_sqrt_bound hC hn.2
  obtain ⟨κ,P,hκ,hP,hInt⟩ := exists_smooth_limit_correction_subsequence_from_L2 hInterior hJet h hC hL2
  have hOne (x : Point) (hx : x ∈ U) : Tendsto (fun n => W (κ n) x) atTop (𝓝 (P x)) :=
    (hInt 2 le_rfl).tendsto_at_of_two hx
  have hMem (s : ℝ) (hs : 0 < s) (hs₁ : s < 1) (n : ℕ) : MemHs s U (W (κ n)) := by
    obtain ⟨v,hv,_⟩ := scaled_smooth_limit_H10_representatives h (κ n)
    exact (hEmbed U h.domain s hs hs₁ v).congr_ae hv
  have hFrac (s : ℝ) (hs : 0 < s) (hs₁ : s < 1/2) : ConvergesHs s U (W ∘ κ) P := by
    let t := (s+1/2)/2
    have hst : s < t := by dsimp only [t]; linarith only [hs₁]
    have ht : t < 1/2 := by dsimp only [t]; linarith only [hs₁]
    obtain ⟨B,_,hBt⟩ := hHs t (hs.trans hst) ht
    have hBound : ∀ᶠ n in atTop, fractionalEnergy t U ((W ∘ κ) n) ≤ ENNReal.ofReal (B^2) :=
      (hκ.tendsto_atTop.eventually hBt).mono fun n hn => hn.1.energy_le_of_sqrt_bound hn.2
    exact convergesHs_of_pointwise_and_bounded_higher_energy hFractional h.domain hs hst ht
      (fun n => hMem s hs (hs₁.trans (by norm_num)) n)
      (fun n => hMem t (hs.trans hst) (ht.trans (by norm_num)) n)
      ⟨ENNReal.ofReal (B^2), ENNReal.ofReal_lt_top, hBound⟩ hOne
  refine ⟨κ,P,hκ,hP,hFrac,hInt,?_⟩
  exact firstCorrection_equations_of_convergesC2Loc a h.domain.1.1 (ε ∘ κ) (Q ∘ κ) q P
    (h.elasticLimit.comp hκ.tendsto_atTop)
    (fun n => (h.approximantsClosed (κ n)).mono subset_closure)
    (h.limitSmooth.of_le (WithTop.coe_le_coe.mpr le_top)) h.limitVacuum h.harmonicEquation
    (fun n => h.eulerEquation (κ n)) (hInt 2 le_rfl)

end Thesis

end
