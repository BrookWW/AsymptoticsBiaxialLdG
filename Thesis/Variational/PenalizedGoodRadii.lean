module

public import Thesis.Interpolation.PenalizedRadialFill
import HarmonicMaps.Analysis.BallEnergyAbsoluteContinuity
import StratificationTheory.Frozen.SphereSliceEnergy
import StratificationTheory.Frozen.SphereGradientCharacterization
import StratificationTheory.Foundation.AngularGradientEnergy
import StratificationTheory.Foundation.PolarAETransport
import StratificationTheory.Foundation.SphereSliceGradientData

/-! The actual coarea density and the compatible Sobolev sphere traces. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ENNReal Matrix.Norms.Frobenius

namespace Thesis

@[expose] def penalizedBallIntegral (a : BulkCoefficients) (ε : ElasticScale) (c : Point)
    (u : Point → S0) (D : Point → Gradient) (r : ℝ) : ℝ :=
  ∫ x in ball c r, energyDensity a ε (u x) (D x)

/-- The measurable polar density differentiates the actual penalized volume
energy. Its integral on the outer half-radius interval is controlled by that
same whole-ball energy. -/
theorem exists_penalizedBall_coarea_density (a : BulkCoefficients) (ε : ElasticScale) (c : Point)
    {R : ℝ} (hR : 0 < R) {u : Point → S0} {D : Point → Gradient}
    (hu : MemH1 (ball c R) u D) (hE : energy a ε (ball c R) u D ≠ ⊤) :
    ∃ g : ℝ → ℝ, Measurable g ∧ IntegrableOn g (Ioo (R / 2) R) ∧
      AbsolutelyContinuousOnInterval (penalizedBallIntegral a ε c u D) (R / 2) R ∧
      MonotoneOn (penalizedBallIntegral a ε c u D) (Icc (R / 2) R) ∧
      (∫ t in Ioo (R / 2) R, g t) ≤ penalizedBallIntegral a ε c u D R ∧
      (∀ s ∈ Icc 0 R, energy a ε (ball c s) u D = ENNReal.ofReal (penalizedBallIntegral a ε c u D s)) ∧
      ∀ᵐ r ∂volume.restrict (Ioo (R / 2) R),
        g r = polarIntegralDensity c (fun x => energyDensity a ε (u x) (D x)) r ∧
        HasDerivAt (penalizedBallIntegral a ε c u D) (g r) r ∧ 0 ≤ g r := by
  let f (x : Point) := energyDensity a ε (u x) (D x)
  let g₀ := polarIntegralDensity c f
  have hf : IntegrableOn f (ball c R) := integrable_energyDensity_of_energy_ne_top a ε hu hE
  have hf₀ (x : Point) : 0 ≤ f x := energyDensity_nonneg a ε _ _
  have hI : IntegrableOn g₀ (Ioo 0 R) := integrableOn_polar_boundary_density (by decide : 0 < 3) hf
  let g := hI.1.aemeasurable.mk g₀
  have hg : Measurable g := hI.1.aemeasurable.measurable_mk
  have hgg : g₀ =ᵐ[volume.restrict (Ioo 0 R)] g := hI.1.aemeasurable.ae_eq_mk
  have hSub : Ioo (R / 2) R ⊆ Ioo 0 R := fun _ hx => ⟨(by linarith : 0 < R / 2).trans hx.1, hx.2⟩
  have hIg : IntegrableOn g (Ioo 0 R) := hI.congr hgg
  have hgin : IntegrableOn g (Ioo (R / 2) R) := hIg.mono_set hSub
  have hAC := absolutelyContinuousOnInterval_integral_ball (by decide : 0 < 3) hR.le hf
  have hA : AbsolutelyContinuousOnInterval (penalizedBallIntegral a ε c u D) (R / 2) R := by
    apply hAC.mono
    rw [uIcc_of_le (by linarith : R / 2 ≤ R), uIcc_of_le hR.le]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hMon : MonotoneOn (penalizedBallIntegral a ε c u D) (Icc (R / 2) R) := by
    intro s hs t ht hst
    exact setIntegral_mono_set (hf.mono_set (ball_subset_ball ht.2)) (ae_of_all _ hf₀)
      (Eventually.of_forall (ball_subset_ball hst))
  have h₀ (r : ℝ) : 0 ≤ g₀ r := mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => hf₀ _)
  have hHalfEq : g₀ =ᵐ[volume.restrict (Ioo (R / 2) R)] g :=
    ae_restrict_of_ae_restrict_of_subset hSub hgg
  have hMass : (∫ t in Ioo (R / 2) R, g t) ≤ penalizedBallIntegral a ε c u D R := by
    calc
      _ = ∫ t in Ioo (R / 2) R, g₀ t := integral_congr_ae hHalfEq.symm
      _ ≤ ∫ t in Ioo 0 R, g₀ t := setIntegral_mono_set hI (ae_of_all _ h₀) (Eventually.of_forall hSub)
      _ = _ := (integral_ball_eq_polar (by decide : 0 < 3) hf).symm
  have hEq (s : ℝ) (hs : s ∈ Icc 0 R) : energy a ε (ball c s) u D =
      ENNReal.ofReal (penalizedBallIntegral a ε c u D s) := by
    exact (ofReal_integral_eq_lintegral_ofReal (hf.mono_set (ball_subset_ball hs.2))
      (Eventually.of_forall hf₀)).symm
  refine ⟨g, hg, hgin, hA, hMon, hMass, hEq, ?_⟩
  have hDer := ae_hasDerivAt_integral_ball (by decide : 0 < 3) hR.le hf
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hSub hgg, ae_restrict_mem measurableSet_Ioo,
    hDer.filter_mono (ae_mono Measure.restrict_le_self)] with r hr hrMem hDer'
  rw [← hr]
  exact ⟨rfl, hDer' (hSub hrMem), h₀ r⟩

private theorem sphereGradientEnergy_eq_sum_LpNormSq (u : UnitTensorSphere → S0) (h : MemSphereH1 u) :
    sphereGradientEnergy u h = ∑ i : Fin 3, ‖sphereGradient (by decide : 2 ≤ 3)
      (fun θ => frobeniusCoordinateEquiv (u θ)) h i‖ ^ 2 := by
  let G := sphereGradient (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (u θ)) h
  have hI := sum_column_Lp_norm_sq_eq_integral_angular_hsNormSq (fun i => Lp.memLp (G i))
  have hEq (i : Fin 3) : (Lp.memLp (G i)).toLp (G i) = G i := Lp.toLp_coeFn _ _
  simpa only [hEq, hsNormSq, sphereGradientEnergy, G, Nat.reduceSub] using hI.symm

/-- The unit-sphere restriction at a genuine radius has the rescaled
tangential penalized energy bounded by the original full-gradient coarea
density at that radius. -/
theorem ae_scaled_spherePenalizedEnergy_le_coarea (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) (c : Point) {R : ℝ} (hR : 0 < R)
    (hClosed : closedBall c R ⊆ Ω) {u : Point → S0} {D : Point → Gradient}
    (hu : MemH1Loc Ω u D) (M : ℝ) (hM : ∀ᵐ x ∂volume.restrict (ball c R), ‖u x‖ ≤ M) :
    ∀ᵐ r ∂volume.restrict (Ioo 0 R),
      let b : UnitTensorSphere → S0 := fun θ => u (c + r • θ.val)
      ∃ hb : MemSphereH1 b,
        (∀ᵐ θ ∂tensorSphereMeasure, ‖b θ‖ ≤ M) ∧
        ∀ ε' : ElasticScale, (ε' : ℝ) = (ε : ℝ) / r →
          spherePenalizedEnergy a ε' b hb ≤ polarIntegralDensity c (fun x => energyDensity a ε (u x) (D x)) r := by
  let U : OpenDomain 3 := ⟨Ω, hΩ⟩
  have hu' := (memH1Loc_iff_memW12Loc U u D).1 hu
  have hM' := ae_polar_slice_of_ae_ball hM
  have hσ : tensorSphereMeasure = (volume : Measure Point).toSphere :=
    euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3)
  letI : IsFiniteMeasure tensorSphereMeasure := by rw [hσ]; infer_instance
  filter_upwards [ae_sphereSobolev_and_gradientEnergy (by decide : 2 ≤ 3) hu' hR hClosed,
    ae_sphere_slice_gradient_class_energy_le (by decide : 0 < 3) hu' hR hClosed,
    ae_exists_sphere_slice_radial_gradient_data (by decide : 0 < 3) hu' hR hClosed,
    hM', ae_restrict_mem measurableSet_Ioo] with r hs hsG hsD hB hr
  obtain ⟨hb, _⟩ := hs
  let b : UnitTensorSphere → S0 := fun θ => u (c + r • θ.val)
  let G := sphereGradient (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (b θ)) hb
  have hBG : ∀ᵐ θ ∂tensorSphereMeasure, ‖b θ‖ ≤ M := hσ ▸ hB
  refine ⟨hb, hBG, ?_⟩
  intro ε' hε'
  have hData := (sphereGradient_characterization (by decide : 2 ≤ 3)
    (fun θ => frobeniusCoordinateEquiv (b θ)) hb).1.1
  obtain ⟨w, Dw, hW, hRay, hDRay⟩ := hData
  have hGrad := hsG w Dw G hW hRay hDRay
  have hEqG (θ : UnitTensorSphere) : hsNormSq (frobeniusGradient D (c + r • θ.val)) =
      gradientNormSq (D (c + r • θ.val)) := by
    simp only [hsNormSq, frobeniusGradient, frobeniusCoordinateEquiv.norm_map, gradientNormSq_eq_sum_norm_sq]
  have hGactual : sphereGradientEnergy b hb ≤ r ^ 2 *
      ∫ θ : UnitTensorSphere, gradientNormSq (D (c + r • θ.val)) ∂tensorSphereMeasure := by
    rw [sphereGradientEnergy_eq_sum_LpNormSq b hb]
    simpa only [hEqG, Nat.reduceSub] using hGrad
  have hGint : Integrable (fun θ : UnitTensorSphere => gradientNormSq (D (c + r • θ.val)))
      tensorSphereMeasure := by
    simp_rw [← hEqG, hsNormSq]
    exact integrable_finsetSum Finset.univ fun i _ => (hsD.1 i).integrable_norm_pow (by norm_num)
  have hpMeas := ((frobeniusCoordinateEquiv_memLp_iff _ _ _).1 hb.1).aestronglyMeasurable
  have hPot : Integrable (fun θ : UnitTensorSphere => bulkPotential a (b θ)) tensorSphereMeasure :=
    integrable_bulkPotential_of_ae_norm_bound a M hpMeas hBG
  have hDen : ((ε' : ℝ)⁻¹) ^ 2 = r ^ 2 * ((ε : ℝ)⁻¹) ^ 2 := by
    rw [hε', inv_div, div_eq_mul_inv, mul_pow]
  unfold spherePenalizedEnergy sphereScaledBulkEnergy polarIntegralDensity
  rw [← hσ]
  simp_rw [energyDensity, hDen]
  rw [integral_add (hGint.const_mul _) (hPot.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul]
  linarith only [mul_le_mul_of_nonneg_left hGactual (by norm_num : 0 ≤ (1 / 2 : ℝ))]

end Thesis
