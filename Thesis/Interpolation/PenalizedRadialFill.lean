module

public import Thesis.Interpolation.PenalizedShell
import HarmonicMaps.Analysis.BallPolarIntegral
import StratificationTheory.Foundation.AngularL2Membership
import StratificationTheory.Frozen.SphereRadialBallExtension
import Thesis.Foundation.BulkGeometry
import Thesis.StressEnergy

/-! Degree-zero radial filling with the actual bulk and Dirichlet energies. -/

public section

open Filter MeasureTheory Metric Set
open scoped Matrix.Norms.Frobenius Topology

namespace Thesis

theorem integrable_bulkPotential_of_ae_norm_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (a : BulkCoefficients) (B : ℝ) {u : X → S0}
    (hu : AEStronglyMeasurable u μ) (hB : ∀ᵐ x ∂μ, ‖u x‖ ≤ B) :
    Integrable (fun x => bulkPotential a (u x)) μ := by
  have hb := (contDiff_bulkPotential a).continuous
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : S0) B).exists_bound_of_continuousOn hb.continuousOn
  have hLp : MemLp (fun x => bulkPotential a (u x)) 1 μ := MemLp.of_bound
    (hb.comp_aestronglyMeasurable hu) C (hB.mono fun x hx => hC _ (by simpa only [mem_closedBall,
      dist_zero_right] using hx))
  exact hLp.integrable (by norm_num)

private theorem integral_radial_bulkPotential_eq (a : BulkCoefficients) {R : ℝ} (hR : 0 < R)
    {u : UnitTensorSphere → S0} {w : Point → S0}
    (hRad : ∀ (ρ : HarmonicMaps.PositiveRadius) (θ : UnitTensorSphere), w (ρ.val • θ.val) = u θ)
    (hW : IntegrableOn (fun x => bulkPotential a (w x)) (ball 0 R)) :
    (∫ x in ball (0 : Point) R, bulkPotential a (w x)) =
      (R ^ 3 / 3) * ∫ θ : UnitTensorSphere, bulkPotential a (u θ) ∂tensorSphereMeasure := by
  have hσ : tensorSphereMeasure = (volume : Measure Point).toSphere :=
    StratificationTheory.euclideanHausdorffMeasure_unitSphere_eq_toSphere (n := 3) (by decide)
  rw [HarmonicMaps.integral_ball_eq_polar (n := 3) (by decide) hW, ← hσ]
  let B := ∫ θ : UnitTensorSphere, bulkPotential a (u θ) ∂tensorSphereMeasure
  have hEq : (∫ r in Ioo (0 : ℝ) R, r ^ (3 - 1 : ℕ) *
      ∫ θ : UnitTensorSphere, bulkPotential a (w (0 + r • θ.val)) ∂tensorSphereMeasure) =
        ∫ r in Ioo (0 : ℝ) R, r ^ 2 * B := by
    refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
    simp only [Nat.reduceSub]
    have hFun : (fun θ : UnitTensorSphere => bulkPotential a (w (0 + r • θ.val))) =
        fun θ => bulkPotential a (u θ) := by
      funext θ
      rw [zero_add, hRad ⟨r, hr.1⟩ θ]
    rw [hFun]
  have hMoment : (∫ r in Ioo (0 : ℝ) R, r ^ (2 : ℕ)) = R ^ 3 / 3 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le, integral_pow]
    norm_num
  rw [hEq, integral_mul_const, hMoment]

/-- A bounded native sphere trace has the degree-zero ball filling with the
same weak gradient and exact one- and three-dimensional energy factors. -/
theorem exists_penalized_radial_ball_extension (a : BulkCoefficients) (ε : ElasticScale)
    (u : UnitTensorSphere → S0) (hu : MemSphereH1 u) (B : ℝ)
    (hB : ∀ᵐ θ ∂tensorSphereMeasure, ‖u θ‖ ≤ B) {R : ℝ} (hR : 0 < R) :
    ∃ (w : Point → S0) (D : Point → Gradient) (J : RadialL2Trace (R / 2) R),
      MemH1 (ball 0 R) w D ∧
      (∀ (ρ : HarmonicMaps.PositiveRadius) (θ : UnitTensorSphere), w (ρ.val • θ.val) = u θ) ∧
      RepresentsRadialL2Trace 0 w J ∧
      (∀ t, J t = hu.1.toLp (fun θ => frobeniusCoordinateEquiv (u θ))) ∧
      (∀ᵐ x ∂volume.restrict (ball 0 R), ‖w x‖ ≤ B) ∧
      energy a ε (ball 0 R) w D = ENNReal.ofReal
        (((1 / 2 : ℝ) * R) * sphereGradientEnergy u hu + (R ^ 3 / 3) * sphereScaledBulkEnergy a ε u) := by
  let F (θ : UnitTensorSphere) := frobeniusCoordinateEquiv (u θ)
  obtain ⟨f, Df, hf, hRay, _, hDI, hDE, hInheritance⟩ :=
    StratificationTheory.exists_radial_ball_sobolev_extension (n := 3) (by decide) F hu hR
  let w (x : Point) := frobeniusCoordinateEquiv.symm (f x)
  let D (x : Point) (j : Fin 3) := frobeniusCoordinateEquiv.symm (Df x j)
  have hf₂ : frobeniusField w = f := funext fun x => frobeniusCoordinateEquiv.apply_symm_apply _
  have hD₂ : frobeniusGradient D = Df := funext fun x => funext fun j =>
    frobeniusCoordinateEquiv.apply_symm_apply _
  have hw : MemH1 (ball 0 R) w D :=
    (memH1_iff_memW12 (HarmonicMaps.ballDomain 0 R) _ _).2 (by simpa only [hf₂, hD₂] using hf)
  have hRad : ∀ (ρ : HarmonicMaps.PositiveRadius) (θ : UnitTensorSphere), w (ρ.val • θ.val) = u θ := by
    intro ρ θ
    rw [show w (ρ.val • θ.val) = frobeniusCoordinateEquiv.symm (f (ρ.val • θ.val)) from rfl,
      hRay ρ θ, show F θ = frobeniusCoordinateEquiv (u θ) from rfl, LinearIsometryEquiv.symm_apply_apply]
  have hBF : ∀ᵐ θ ∂tensorSphereMeasure, ‖F θ‖ ≤ B := by
    simpa only [F, LinearIsometryEquiv.norm_map] using hB
  have hwB : ∀ᵐ x ∂volume.restrict (ball 0 R), ‖w x‖ ≤ B := by
    simpa only [w, LinearIsometryEquiv.norm_map] using hInheritance (fun z => ‖z‖ ≤ B) hBF
  let J : RadialL2Trace (R / 2) R := ContinuousMap.const _ (hu.1.toLp F)
  have hJ : RepresentsRadialL2Trace 0 w J := by
    unfold RepresentsRadialL2Trace
    refine Eventually.of_forall fun t ht => ?_
    have ht₀ : 0 < t := (half_pos hR).trans ht.1
    have hEq : (fun θ : UnitTensorSphere => frobeniusField w (0 + t • θ.val)) = F := by
      funext θ
      rw [hf₂, zero_add]
      exact hRay ⟨t, ht₀⟩ θ
    exact ⟨hEq ▸ hu.1, by simp only [J, ContinuousMap.const_apply, hEq]⟩
  refine ⟨w, D, J, hw, hRad, hJ, fun _ => rfl, hwB, ?_⟩
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Point) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hBInt : IntegrableOn (fun x => bulkPotential a (w x)) (ball 0 R) :=
    integrable_bulkPotential_of_ae_norm_bound a B hw.1.1 hwB
  have hBVal := integral_radial_bulkPotential_eq a hR hRad hBInt
  have hGrad (x : Point) : gradientNormSq (D x) = HarmonicMaps.hsNormSq (Df x) := by
    simp only [gradientNormSq_eq_sum_norm_sq, D, HarmonicMaps.hsNormSq, LinearIsometryEquiv.norm_map]
  have hInt : IntegrableOn (fun x => energyDensity a ε (w x) (D x)) (ball 0 R) := by
    simp only [energyDensity, hGrad]
    exact (hDI.const_mul _).add (hBInt.const_mul _)
  have hNonneg (x : Point) : 0 ≤ energyDensity a ε (w x) (D x) := by
    rw [energyDensity, gradientNormSq_eq_sum_norm_sq]
    exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _))
  rw [energy, ← ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall hNonneg)]
  have hDval : (∫ x in ball (0 : Point) R, HarmonicMaps.hsNormSq (Df x)) = R * sphereGradientEnergy u hu := by
    rw [show (↑(3 : ℕ) : ℝ) - 2 = 1 from by norm_num, div_one] at hDE
    simpa only [Nat.reduceSub, pow_one, sphereGradientEnergy,
      HarmonicMaps.hsNormSq, F] using hDE
  simp only [energyDensity, hGrad]
  rw [integral_add (hDI.const_mul _) (hBInt.const_mul _), integral_const_mul, integral_const_mul, hDval, hBVal,
    sphereScaledBulkEnergy, integral_const_mul]
  congr 1
  ring

end Thesis
