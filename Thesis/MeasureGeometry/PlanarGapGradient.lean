module

public import Thesis.Foundation.SpectralGapGradient
public import Thesis.MeasureGeometry.PlanarVacuumAnnulus

/-! The gap and projection contributions to the planar Dirichlet density. -/

@[expose] public section

noncomputable section

open Filter Set Topology
open scoped ContDiff Matrix.Norms.Frobenius

namespace Thesis

/-- Squared Euclidean gradient norm of a scalar planar map. -/
def planarScalarGradientSq (f : Plane → ℝ) (x : Plane) : ℝ :=
  ∑ j : Fin 2, (fderiv ℝ f x (EuclideanSpace.single j 1)) ^ 2

/-- Squared Frobenius gradient of the chosen spectral projection. Its value
is used with gap-squared weight, or on strictly positive superlevels. -/
def planarSpectralProjectionGradientSq (a : BulkCoefficients) (Q : Plane → S0) (x : Plane) : ℝ :=
  ∑ j : Fin 2,
    ‖fderiv ℝ (fun y => ((spectralVacuumPoint a (Q y)).val : Tensor)) x (EuclideanSpace.single j 1)‖ ^ 2

/-- The manuscript's derivative split in the planar Dirichlet density,
including its exact r_*²/36 coefficient. -/
theorem planarModifiedGap_dirichlet_split (a : BulkCoefficients) (τ : GapSmoothingParameter)
    (Q : Plane → S0) (x : Plane) (hQ : DifferentiableAt ℝ Q x) :
    vacuumRadius a ^ 2 / 36 * planarScalarGradientSq (fun y => modifiedSpectralGap a τ (Q y)) x +
      (1 / 2 : ℝ) * (modifiedSpectralGap a τ (Q x)) ^ 2 * planarSpectralProjectionGradientSq a Q x ≤
        planarSmoothDirichletDensity Q x := by
  by_cases hsimple : Q x ∈ simpleSpectrumLocus
  · let A := Q x
    let Φ := modifiedSpectralGap a τ
    let P (A : S0) := ((spectralVacuumPoint a A).val : Tensor)
    have hOpen : simpleSpectrumLocus ∈ 𝓝 A := isOpen_simpleSpectrumLocus.mem_nhds hsimple
    have hF : DifferentiableAt ℝ Φ A :=
      (((contDiffOn_modifiedSpectralGap a τ A hsimple).contDiffAt hOpen).differentiableAt (by decide))
    have hPS₀ : DifferentiableAt ℝ (fun A => (spectralVacuumPoint a A).val) A :=
      (((contDiffOn_spectralVacuumPoint a A hsimple).contDiffAt hOpen).differentiableAt (by decide))
    have hP : DifferentiableAt ℝ P A := symmetricTraceless.subtypeL.differentiableAt.comp A hPS₀
    have hΦ : fderiv ℝ (fun y => modifiedSpectralGap a τ (Q y)) x =
        (fderiv ℝ Φ A).comp (fderiv ℝ Q x) := fderiv_comp x hF hQ
    have hρ : fderiv ℝ (fun y => ((spectralVacuumPoint a (Q y)).val : Tensor)) x =
        (fderiv ℝ P A).comp (fderiv ℝ Q x) := fderiv_comp x hP hQ
    have hT : fderiv ℝ (fun y => (Q y : Tensor)) x =
        symmetricTraceless.subtypeL.comp (fderiv ℝ Q x) := by
      have hf : HasFDerivAt (⇑symmetricTraceless.subtypeL) symmetricTraceless.subtypeL A :=
        symmetricTraceless.subtypeL.hasFDerivAt
      exact (hf.comp x hQ.hasFDerivAt).fderiv
    have hi (i : Fin 2) :=
      modifiedGap_spectralProjection_derivative_split a τ A hsimple
        (fderiv ℝ Q x (EuclideanSpace.single i 1))
    unfold planarScalarGradientSq planarSpectralProjectionGradientSq planarSmoothDirichletDensity
    rw [hΦ, hρ, hT]
    simp only [ContinuousLinearMap.comp_apply]
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    have h := add_le_add (hi 0) (hi 1)
    change (vacuumRadius a ^ 2 / 18 * (fderiv ℝ Φ A (fderiv ℝ Q x (EuclideanSpace.single 0 1))) ^ 2 +
        (Φ A) ^ 2 * ‖fderiv ℝ P A (fderiv ℝ Q x (EuclideanSpace.single 0 1))‖ ^ 2) +
      (vacuumRadius a ^ 2 / 18 * (fderiv ℝ Φ A (fderiv ℝ Q x (EuclideanSpace.single 1 1))) ^ 2 +
        (Φ A) ^ 2 * ‖fderiv ℝ P A (fderiv ℝ Q x (EuclideanSpace.single 1 1))‖ ^ 2) ≤
      ‖symmetricTraceless.subtypeL (fderiv ℝ Q x (EuclideanSpace.single 0 1))‖ ^ 2 +
        ‖symmetricTraceless.subtypeL (fderiv ℝ Q x (EuclideanSpace.single 1 1))‖ ^ 2 at h
    change vacuumRadius a ^ 2 / 36 *
        ((fderiv ℝ Φ A (fderiv ℝ Q x (EuclideanSpace.single 0 1))) ^ 2 +
          (fderiv ℝ Φ A (fderiv ℝ Q x (EuclideanSpace.single 1 1))) ^ 2) +
      (1 / 2 : ℝ) * (Φ A) ^ 2 *
        (‖fderiv ℝ P A (fderiv ℝ Q x (EuclideanSpace.single 0 1))‖ ^ 2 +
          ‖fderiv ℝ P A (fderiv ℝ Q x (EuclideanSpace.single 1 1))‖ ^ 2) ≤ _
    linarith only [h]
  · have hz : modifiedSpectralGap a τ (Q x) = 0 :=
      le_antisymm (le_of_not_gt (mt (modifiedSpectralGap_pos_iff a τ (Q x)).1 hsimple))
        (modifiedSpectralGap_nonneg a τ (Q x))
    have hmin : IsLocalMin (fun y => modifiedSpectralGap a τ (Q y)) x :=
      Eventually.of_forall fun y => by
        change modifiedSpectralGap a τ (Q x) ≤ modifiedSpectralGap a τ (Q y)
        rw [hz]
        exact modifiedSpectralGap_nonneg a τ (Q y)
    have hdz := hmin.fderiv_eq_zero
    simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_mul,
      planarScalarGradientSq, hdz, zero_apply, Finset.sum_const_zero, add_zero]
    exact planarSmoothDirichletDensity_nonneg Q x

/-- The operator norm of the scalar derivative is bounded by the Euclidean
norm of its two coordinate derivatives. -/
theorem norm_fderiv_le_sqrt_planarScalarGradientSq (f : Plane → ℝ) (x : Plane) :
    ‖fderiv ℝ f x‖ ≤ Real.sqrt (planarScalarGradientSq f x) := by
  let D := fderiv ℝ f x
  let a := D (EuclideanSpace.single 0 1)
  let b := D (EuclideanSpace.single 1 1)
  have hsum : planarScalarGradientSq f x = a ^ 2 + b ^ 2 := by
    rw [planarScalarGradientSq, Fin.sum_univ_two]
  have hs : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  rw [hsum]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro z
  have hz : z = z 0 • EuclideanSpace.single 0 1 + z 1 • EuclideanSpace.single 1 1 := by
    ext j
    fin_cases j <;> simp
  have hDz : D z = z 0 * a + z 1 * b := by
    conv_lhs => rw [hz]
    simp only [map_add, map_smul, smul_eq_mul, a, b]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  change ‖D z‖ ^ 2 ≤ _
  rw [mul_pow, Real.sq_sqrt hs, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
    hDz, Real.norm_eq_abs, sq_abs]
  nlinarith only [sq_nonneg (a * z 1 - b * z 0)]

end Thesis
