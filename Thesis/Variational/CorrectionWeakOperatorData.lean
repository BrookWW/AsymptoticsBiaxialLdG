module

public import Thesis.Variational.CorrectionWeakOperators

/-! Uniform coefficient and inverse data for the smooth-limit correction. -/

public section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance correctionWeakOperatorDataDualNormed (U : Set Point) : NormedAddCommGroup (HMinusOne U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance correctionWeakOperatorDataDualSpace (U : Set Point) : NormedSpace ℝ (HMinusOne U) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance correctionWeakOperatorDataInverseNormed (U : Set Point) :
    NormedAddCommGroup (HMinusOne U →L[ℝ] H10 U) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

/-- The frozen bijective weak linearization gives an eventual uniform
inverse for the literal averaged coefficients. The same constants bound
their column derivatives in \(L^p\). -/
theorem exists_eventual_weakCorrectionOperator_data
    (hPoisson : External.GlobalDirichletPoissonSecondDerivativeLp)
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    {b : Point → S0} (hb : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) b) (p : ℝ) (hp : 1 < p)
    {ε : ℕ → ElasticScale} {Q : ℕ → Point → S0} {q : Point → S0} {D : Point → Gradient}
    (hQ : ∀ n, ContDiffOn ℝ 2 (Q n) (closure U))
    (hQOpen : ∀ n, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (Q n) U)
    (hq : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) q U) (hqCl : ContDiffOn ℝ 2 q (closure U))
    (hWall : ∀ n, MapsTo (Q n) (frontier U) (vacuum a))
    (hTrace : ∀ n, EqOn (Q n) b (frontier U)) (hqTrace : EqOn q b (frontier U))
    (hVac : MapsTo q U (vacuum a)) (hD : D =ᵐ[volume.restrict U] ClassicalGradient q)
    (hEq : ∀ n, ∀ x ∈ U, (ε n : ℝ)^2 • (↑(laplacian (Q n) x) : Tensor) = bulkGradient a (Q n x))
    (hConv : ConvergesC1HolderLoc (1/2) U ∅ Q q)
    (hBij : ∃ L : H10 U →ₗ[ℝ] HMinusOne U, Function.Bijective L ∧
      ∀ v w : H10 U, L v w = linearizedPairing a U q D v w) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ∃ L : H10 U ≃L[ℝ] HMinusOne U,
      ‖L.symm.toContinuousLinearMap‖ ≤ M ∧
      HasBoundedDirichletCorrectionCoefficients U p M (averagedCorrectionCoefficient a q (Q n)) ∧
      ∀ v w : H10 U, L v w = weakCorrectionPairing U (averagedCorrectionCoefficient a q (Q n)) v w := by
  obtain ⟨M,hM,hqData,hQData⟩ := exists_eventual_smoothLimit_state_laplacian_bounds a hU hQ hqCl hWall hVac hEq hConv
  obtain ⟨C,hC,hData⟩ := exists_eventual_coefficientLp_data_of_uniform_fields
    hPoisson a hU hb p hp hQ hQOpen hq hqCl hTrace hqTrace M hM hqData hQData
  have hqState (x : Point) (hx : x ∈ U) : ‖correctionStateField q x‖ ≤ M :=
    norm_correctionStateField_le hM (hqData x hx).1 (hqData x hx).2.2
  have hQState : ∀ᶠ n in atTop, ∀ x ∈ U, ‖correctionStateField (Q n) x‖ ≤ M :=
    hQData.mono fun n hn x hx => norm_correctionStateField_le hM (hn x hx).1 (hn x hx).2.2
  have hI := @exists_eventual_weak_inverse_for_uniform_states
    a U hU Q q D hQOpen hq hVac hD hConv hBij M hqState hQState
  obtain ⟨T,_,hInverse⟩ := hI
  exact combine_eventual_correction_operator_bounds p (fun n => averagedCorrectionCoefficient a q (Q n))
    C T hC hData hInverse

end Thesis

end
