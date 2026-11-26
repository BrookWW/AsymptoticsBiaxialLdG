module

public import Thesis.Variational.CorrectionCoefficientBounds
public import Thesis.Variational.WeakCorrectionInverse

/-! Uniform weak inverse and Sobolev coefficient data for the smooth limit. -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped BigOperators ContDiff ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance correctionWeakOperatorsStateNormed : NormedAddCommGroup ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance correctionWeakOperatorsStateSpace : NormedSpace ℝ ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance correctionWeakOperatorsStateMetric : MetricSpace ((S0 × Gradient) →L[ℝ] S0) :=
  correctionWeakOperatorsStateNormed.toMetricSpace

local instance correctionWeakOperatorsStatePseudoMetrizable :
    TopologicalSpace.PseudoMetrizableSpace ((S0 × Gradient) →L[ℝ] S0) :=
  @UniformSpace.pseudoMetrizableSpace ((S0 × Gradient) →L[ℝ] S0)
    correctionWeakOperatorsStateMetric.toPseudoMetricSpace.toUniformSpace inferInstance

local instance correctionWeakOperatorsDualNormed (U : Set Point) : NormedAddCommGroup (HMinusOne U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance correctionWeakOperatorsDualSpace (U : Set Point) : NormedSpace ℝ (HMinusOne U) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance correctionWeakOperatorsInverseNormed (U : Set Point) :
    NormedAddCommGroup (HMinusOne U →L[ℝ] H10 U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

theorem norm_correctionStateField_le {M : ℝ} (hM : 0 ≤ M)
    {q : Point → S0} {x : Point} (hq : ‖q x‖ ≤ M)
    (hG : Real.sqrt (gradientNormSq (ClassicalGradient q x)) ≤ M) :
    ‖correctionStateField q x‖ ≤ M := by
  rw [Prod.norm_def]
  apply max_le hq
  apply (pi_norm_le_iff_of_nonneg hM).2
  intro j
  refine (Real.le_sqrt_of_sq_le ?_).trans hG
  rw [gradientNormSq_eq_sum_norm_sq]
  exact Finset.single_le_sum (f := fun i : Fin 3 => ‖ClassicalGradient q x i‖^2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ j)

private theorem eventually_correction_state_distance_lt
    {U : Set Point} (hU : IsSmoothDomain U) {Q : ℕ → Point → S0} {q : Point → S0}
    (hConv : ConvergesC1HolderLoc (1/2) U ∅ Q q) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n in atTop, ∀ x ∈ U, ‖correctionStateField (Q n) x - correctionStateField q x‖ < r := by
  simp only [ConvergesC1HolderLoc, Set.sdiff_empty] at hConv
  obtain ⟨_, _, hVal, hGrad, _⟩ := hConv.2.2 (closure U) hU.1.2.2.isCompact_closure subset_rfl
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hVal r hr, Metric.tendstoUniformlyOn_iff.mp hGrad r hr]
    with n hn hnGrad x hx
  have hxCl := subset_closure hx
  have h₁ : ‖Q n x - q x‖ < r := by
    rw [← dist_eq_norm, dist_comm]
    exact hn x hxCl
  have h₂ : ‖ClassicalGradient (Q n) x - ClassicalGradient q x‖ < r := by
    rw [← dist_eq_norm, dist_comm]
    have hd := hnGrad x hxCl
    rw [closureGradient_eq_classical_on_interior hU.1.1 hConv.2.1 hx,
      closureGradient_eq_classical_on_interior hU.1.1 (hConv.1 n) hx] at hd
    exact hd
  change ‖(Q n x - q x, ClassicalGradient (Q n) x - ClassicalGradient q x)‖ < r
  rw [Prod.norm_def, max_lt_iff]
  exact ⟨h₁,h₂⟩

private theorem exists_tendsto_zero_coefficient_error
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    {Q : ℕ → Point → S0} {q : Point → S0} (hConv : ConvergesC1HolderLoc (1/2) U ∅ Q q)
    {M : ℝ} (hq : ∀ x ∈ U, ‖correctionStateField q x‖ ≤ M)
    (hQ : ∀ᶠ n in atTop, ∀ x ∈ U, ‖correctionStateField (Q n) x‖ ≤ M) :
    let A (x : Point) := fderiv ℝ (fun y : S0 × Gradient => projectedHarmonicNonlinearity a y.1 y.2)
      (correctionStateField q x)
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᶠ n in atTop, 0 ≤ δ n ∧
      ∀ x ∈ U, ‖averagedCorrectionCoefficient a q (Q n) x - A x‖ ≤ δ n := by
  intro A
  obtain ⟨C, hC, hReg⟩ := exists_norm_averagedHarmonicLinearization_sub_le a M
  let B (n : ℕ) (x : Point) := ‖averagedCorrectionCoefficient a q (Q n) x - A x‖
  let δ (n : ℕ) := sSup (B n '' U)
  have hNonempty (n : ℕ) : (B n '' U).Nonempty := hU.1.2.1.1.image _
  have hDom : ∀ᶠ n in atTop, ∀ x ∈ U, B n x ≤ C * ‖correctionStateField (Q n) x - correctionStateField q x‖ :=
    hQ.mono fun n hn x hx => hReg (correctionStateField q x) (correctionStateField (Q n) x) (hq x hx) (hn x hx)
  have hBdd : ∀ᶠ n in atTop, BddAbove (B n '' U) := by
    filter_upwards [hDom, hQ] with n hn hnQ
    refine ⟨C*(M+M), ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact (hn x hx).trans (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hnQ x hx) (hq x hx))) hC)
  have hLe : ∀ᶠ n in atTop, 0 ≤ δ n ∧ ∀ x ∈ U, B n x ≤ δ n := by
    filter_upwards [hBdd] with n hn
    have hUpper (x : Point) (hx : x ∈ U) : B n x ≤ δ n := le_csSup hn (mem_image_of_mem _ hx)
    obtain ⟨x, hx⟩ := hU.1.2.1.1
    exact ⟨(norm_nonneg _).trans (hUpper x hx), hUpper⟩
  refine ⟨δ, ?_, hLe⟩
  apply Metric.tendsto_nhds.mpr
  intro r hr
  let d := r/(2*(C+1))
  have hd : 0 < d := div_pos hr (by positivity)
  have hScale : C*d ≤ r/2 := by
    dsimp only [d]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 2*(C+1))]
    nlinarith only [hr]
  filter_upwards [hLe,hDom,eventually_correction_state_distance_lt hU hConv hd] with n hn hnD hnC
  rw [dist_zero_right, Real.norm_of_nonneg hn.1]
  refine (csSup_le (hNonempty n) ?_).trans_lt (half_lt_self hr)
  rintro z ⟨x, hx, rfl⟩
  exact (hnD x hx).trans ((mul_le_mul_of_nonneg_left (hnC x hx).le hC).trans hScale)

private theorem linearizedPairing_congr_ae_columns
    (a : BulkCoefficients) {U : Set Point} (q : Point → S0)
    {D E : Point → Gradient} (hDE : D =ᵐ[volume.restrict U] E) (v w : H10 U) :
    linearizedPairing a U q D v w = linearizedPairing a U q E v w := by
  unfold linearizedPairing
  apply integral_congr_ae
  filter_upwards [hDE] with x hx
  simp only [gradientTraceMul, hx]

private theorem aestronglyMeasurable_averagedCorrectionCoefficient
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U) {q Q : Point → S0}
    (hq : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) q U)
    (hQ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U) :
    AEStronglyMeasurable (averagedCorrectionCoefficient a q Q) (volume.restrict U) := by
  have hC : ContinuousOn (averagedCorrectionCoefficient a q Q) U :=
    (contDiffOn_averagedCorrectionCoefficient a hU hq hQ).continuousOn
  exact hC.aestronglyMeasurable hU.measurableSet

theorem exists_eventual_coefficientLp_data_of_uniform_fields
    (hPoisson : External.GlobalDirichletPoissonSecondDerivativeLp)
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    {b : Point → S0} (hb : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) b) (p : ℝ) (hp : 1 < p)
    {Q : ℕ → Point → S0} {q : Point → S0}
    (hQ : ∀ n, ContDiffOn ℝ 2 (Q n) (closure U))
    (hQOpen : ∀ n, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (Q n) U)
    (hq : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) q U) (hqCl : ContDiffOn ℝ 2 q (closure U))
    (hTrace : ∀ n, EqOn (Q n) b (frontier U)) (hqTrace : EqOn q b (frontier U))
    (M : ℝ) (hM : 0 ≤ M)
    (hqData : ∀ x ∈ U, ‖q x‖ ≤ M ∧ ‖laplacian q x‖ ≤ M ∧
      Real.sqrt (gradientNormSq (ClassicalGradient q x)) ≤ M)
    (hQData : ∀ᶠ n in atTop, ∀ x ∈ U, ‖Q n x‖ ≤ M ∧ ‖laplacian (Q n) x‖ ≤ M ∧
      Real.sqrt (gradientNormSq (ClassicalGradient (Q n) x)) ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      HasBoundedDirichletCorrectionCoefficients U p C (averagedCorrectionCoefficient a q (Q n)) := by
  obtain ⟨N,hN,hW2p⟩ := exists_uniform_secondDerivativeLp_bound_of_fixedTrace hPoisson hU hb p M hp hM
  obtain ⟨C,hC,hCoeff⟩ := exists_boundedDirichletCorrectionCoefficients_of_secondDerivativeLp a hU.1 p M N hp hM hN
  have hqW2p := hW2p q hqCl hqTrace (fun x hx => ⟨(hqData x hx).1, (hqData x hx).2.1⟩)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hQData] with n hn
  have hQW2p := hW2p (Q n) (hQ n) (hTrace n) (fun x hx => ⟨(hn x hx).1, (hn x hx).2.1⟩)
  exact hCoeff q (Q n) hq (hQOpen n) (fun x hx => ⟨(hqData x hx).1,(hqData x hx).2.2,
    (hn x hx).1,(hn x hx).2.2⟩) hqW2p.1 hQW2p.1 hqW2p.2 hQW2p.2

private theorem exists_eventual_weak_inverse_for_uniform_states_aux
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    {Q : ℕ → Point → S0} {q : Point → S0} {D : Point → Gradient}
    (hQ : ∀ n, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (Q n) U)
    (hq : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) q U)
    (hVac : MapsTo q U (vacuum a)) (hD : D =ᵐ[volume.restrict U] ClassicalGradient q)
    (hConv : ConvergesC1HolderLoc (1/2) U ∅ Q q)
    (hBij : ∃ L : H10 U →ₗ[ℝ] HMinusOne U, Function.Bijective L ∧
      ∀ v w : H10 U, L v w = linearizedPairing a U q D v w)
    {M : ℝ} (hqState : ∀ x ∈ U, ‖correctionStateField q x‖ ≤ M)
    (hQState : ∀ᶠ n in atTop, ∀ x ∈ U, ‖correctionStateField (Q n) x‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∃ L : H10 U ≃L[ℝ] HMinusOne U,
      ‖L.symm.toContinuousLinearMap‖ ≤ C ∧
      ∀ v w : H10 U, L v w = weakCorrectionPairing U (averagedCorrectionCoefficient a q (Q n)) v w := by
  let A₀ (x : Point) := fderiv ℝ (fun y : S0 × Gradient => projectedHarmonicNonlinearity a y.1 y.2)
    (correctionStateField q x)
  let A (n : ℕ) := averagedCorrectionCoefficient a q (Q n)
  obtain ⟨δ,hδ,hSmall⟩ := exists_tendsto_zero_coefficient_error a hU hConv hqState hQState
  have hF := (contDiff_projectedHarmonicNonlinearity a).continuous_fderiv (by simp)
  have hA₀ : ContinuousOn A₀ U := hF.comp_continuousOn (contDiffOn_correctionStateField hU.1.1 hq).continuousOn
  obtain ⟨M₀,hM₀⟩ := (isCompact_closedBall (0 : S0 × Gradient) M).exists_bound_of_continuousOn hF.continuousOn
  have hA₀Bound : ∀ᵐ x ∂volume.restrict U, ‖A₀ x‖ ≤ max M₀ 0 := by
    filter_upwards [ae_restrict_mem (μ := volume) hU.1.1.measurableSet] with x hx
    exact (hM₀ _ (mem_closedBall_zero_iff.mpr (hqState x hx))).trans (le_max_left _ _)
  have hA₀Meas : AEStronglyMeasurable A₀ (volume.restrict U) := hA₀.aestronglyMeasurable hU.1.1.measurableSet
  have hVacAe : TakesVacuumValues a U q :=
    (ae_restrict_mem (μ := volume) hU.1.1.measurableSet).mono hVac
  have hBase : ∃ L : H10 U →ₗ[ℝ] HMinusOne U, Function.Bijective L ∧
      ∀ v w : H10 U, L v w = weakCorrectionPairing U A₀ v w := by
    obtain ⟨L,hL,hPair⟩ := hBij
    refine ⟨L,hL,?_⟩
    intro v w
    exact (hPair v w).trans ((linearizedPairing_congr_ae_columns a q hD v w).trans
      (weakCorrectionPairing_fderiv_eq_linearizedPairing a U q (ClassicalGradient q) hVacAe v w).symm)
  have hMeas (n : ℕ) : AEStronglyMeasurable (A n) (volume.restrict U) :=
    aestronglyMeasurable_averagedCorrectionCoefficient a hU.1.1 hq (hQ n)
  have hPerturb : ∀ᶠ n in atTop, AEStronglyMeasurable (A n) (volume.restrict U) ∧
      0 ≤ δ n ∧ ∀ᵐ x ∂volume.restrict U, ‖A n x - A₀ x‖ ≤ δ n := by
    apply hSmall.mono
    intro n hs
    have hδn : 0 ≤ δ n := hs.1
    have hν : ∀ᵐ x ∂volume.restrict U, ‖A n x - A₀ x‖ ≤ δ n :=
      (ae_restrict_mem (μ := volume) hU.1.1.measurableSet).mono fun x hx => hs.2 x hx
    exact ⟨hMeas n,hδn,hν⟩
  exact eventually_uniform_inverse_of_weakCorrectionPairing_coefficients A₀ hA₀Meas
    (max M₀ 0) (le_max_right _ _) hA₀Bound hBase A δ hδ hPerturb

theorem exists_eventual_weak_inverse_for_uniform_states
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    {Q : ℕ → Point → S0} {q : Point → S0} {D : Point → Gradient}
    (hQ : ∀ n, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (Q n) U)
    (hq : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) q U)
    (hVac : MapsTo q U (vacuum a)) (hD : D =ᵐ[volume.restrict U] ClassicalGradient q)
    (hConv : ConvergesC1HolderLoc (1/2) U ∅ Q q)
    (hBij : ∃ L : H10 U →ₗ[ℝ] HMinusOne U, Function.Bijective L ∧
      ∀ v w : H10 U, L v w = linearizedPairing a U q D v w)
    {M : ℝ} (hqState : ∀ x ∈ U, ‖correctionStateField q x‖ ≤ M)
    (hQState : ∀ᶠ n in atTop, ∀ x ∈ U, ‖correctionStateField (Q n) x‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∃ L : H10 U ≃L[ℝ] HMinusOne U,
      ‖L.symm.toContinuousLinearMap‖ ≤ C ∧
      ∀ v w : H10 U, L v w = weakCorrectionPairing U (averagedCorrectionCoefficient a q (Q n)) v w := by
  exact @exists_eventual_weak_inverse_for_uniform_states_aux a U hU Q q D
    hQ hq hVac hD hConv hBij M hqState hQState

theorem combine_eventual_correction_operator_bounds
    {U : Set Point} (p : ℝ) (A : ℕ → Point → (S0 × Gradient) →L[ℝ] S0)
    (C T : ℝ) (hC : 0 ≤ C)
    (hData : ∀ᶠ n in atTop, HasBoundedDirichletCorrectionCoefficients U p C (A n))
    (hInverse : ∀ᶠ n in atTop, ∃ L : H10 U ≃L[ℝ] HMinusOne U, ‖L.symm.toContinuousLinearMap‖ ≤ T ∧
      ∀ v w : H10 U, L v w = weakCorrectionPairing U (A n) v w) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ∃ L : H10 U ≃L[ℝ] HMinusOne U,
      ‖L.symm.toContinuousLinearMap‖ ≤ M ∧ HasBoundedDirichletCorrectionCoefficients U p M (A n) ∧
      ∀ v w : H10 U, L v w = weakCorrectionPairing U (A n) v w := by
  let B := max C T
  have hB : 0 ≤ B := hC.trans (le_max_left _ _)
  refine ⟨B,hB,?_⟩
  filter_upwards [hData,hInverse] with n hn hI
  obtain ⟨L,hL,hPair⟩ := hI
  refine ⟨L,hL.trans (le_max_right _ _),?_ ,hPair⟩
  refine ⟨hn.1,hn.2.1.mono (fun x hx => hx.trans (le_max_left _ _)),?_⟩
  intro j
  exact ⟨(hn.2.2 j).1,(hn.2.2 j).2.1,(hn.2.2 j).2.2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩

end Thesis

end
