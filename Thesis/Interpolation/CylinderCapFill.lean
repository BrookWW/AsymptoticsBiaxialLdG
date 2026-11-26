module

public import Thesis.Interpolation.CylinderCapGeometry
public import Thesis.Interpolation.PenalizedRadialFill
import HarmonicMaps.Analysis.EuclideanHausdorffLipschitz
import Thesis.Upstream.MinimizingSobolev
import Thesis.StressEnergy
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-! A homogeneous penalized filling of the actual short cylindrical end cap. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal NNReal Matrix.Norms.Frobenius

namespace Thesis

/-- Standard bi-Lipschitz Sobolev transport on three-dimensional open
Euclidean sets, with both Lipschitz constants bounded by twenty. -/
@[expose] def External.AmbientBiLipschitzSobolevPullback3 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (F : Point ≃ₜ Point),
    LipschitzWith 20 (F : Point → Point) → LipschitzWith 20 (F.symm : Point → Point) →
    ∀ (U : OpenDomain 3) (u : Point → Ambient 5) (D : Point → HarmonicMaps.Gradient 3 5),
      MemW12 U u D →
      ∃ E : Point → HarmonicMaps.Gradient 3 5,
        MemW12 ⟨F ⁻¹' U.val, U.property.preimage F.continuous⟩ (u ∘ F) E ∧
        HarmonicMaps.dirichletEnergy E (F ⁻¹' U.val) ≤ ENNReal.ofReal C * HarmonicMaps.dirichletEnergy D U.val

namespace MeasureGeometry

private theorem homeomorph_map_volume_le_cube (F : Point ≃ₜ Point) {L : ℝ≥0}
    (hF : LipschitzWith L (F.symm : Point → Point)) (U : Set Point) :
    Measure.map F (volume.restrict (F ⁻¹' U)) ≤ (L : ℝ≥0∞) ^ 3 • volume.restrict U := by
  have hEmb : MeasurableEmbedding F := F.isClosedEmbedding.measurableEmbedding
  have hFull : Measure.map F (volume : Measure Point) ≤ (L : ℝ≥0∞) ^ 3 • volume := by
    apply Measure.le_iff.2
    intro V hV
    rw [Measure.map_apply F.continuous.measurable hV, ← F.image_symm, Measure.smul_apply, smul_eq_mul]
    have h := HarmonicMaps.euclideanHausdorff_lipschitzOn_image_le_volume
      (hF.lipschitzOnWith (s := Set.univ)) (subset_univ V)
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
    have hDim : Module.finrank ℝ Point = 3 := by simp [Point]
    rwa [hDim] at h
  rw [← hEmb.restrict_map, ← Measure.restrict_smul]
  exact Measure.restrict_mono_measure hFull _

private theorem energy_eq_dirichlet_add_lintegral_of_memH1 (a : BulkCoefficients) (ε : ElasticScale)
    {U : Set Point} {u : Point → S0} {D : Point → Gradient} (hu : MemH1 U u D) :
    energy a ε U u D = dirichletEnergy U D +
      ∫⁻ x in U, ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a (u x)) := by
  rw [energy_eq_dirichlet_add_scaledPotential a ε _ hu.2.1, eLpNorm_one_eq_lintegral_enorm]
  congr 1
  exact lintegral_congr fun x => by
    rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _))]

private theorem pullback_energy_le {a : BulkCoefficients} (ε : ElasticScale)
    (F : Point ≃ₜ Point) {U : Set Point} {u : Point → S0} {D E : Point → Gradient}
    (hu : MemH1 U u D) (hw : MemH1 (F ⁻¹' U) (u ∘ F) E)
    {C : ℝ}
    (hGrad : dirichletEnergy (F ⁻¹' U) E ≤ ENNReal.ofReal C * dirichletEnergy U D)
    (hLip : LipschitzWith 20 (F.symm : Point → Point)) :
    energy a ε (F ⁻¹' U) (u ∘ F) E ≤ ENNReal.ofReal (max C (20 ^ 3)) * energy a ε U u D := by
  let μ := volume.restrict (F ⁻¹' U)
  let ν := volume.restrict U
  let H (x : Point) := ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a (u x))
  let k := ENNReal.ofReal ((20 : ℝ) ^ 3)
  have hk : (20 : ℝ≥0∞) ^ 3 = k := by dsimp only [k]; norm_num
  have hDom : Measure.map F μ ≤ k • ν := hk ▸ homeomorph_map_volume_le_cube F hLip U
  have hAS : AEMeasurable H ν :=
    (ENNReal.continuous_ofReal.comp ((contDiff_bulkPotential a).continuous.const_mul _)
      |>.comp_aestronglyMeasurable hu.1.aestronglyMeasurable).aemeasurable
  have hAS' : AEMeasurable H (Measure.map F μ) := (hAS.smul_measure k).mono_measure hDom
  have hP : (∫⁻ x, H (F x) ∂μ) ≤ k * ∫⁻ x, H x ∂ν := by
    rw [← lintegral_map' hAS' F.continuous.measurable.aemeasurable]
    exact (lintegral_mono' hDom le_rfl).trans_eq (lintegral_smul_measure _ _)
  let K := ENNReal.ofReal (max C ((20 : ℝ) ^ 3))
  have hG : ENNReal.ofReal C ≤ K := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hB : k ≤ K := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  rw [energy_eq_dirichlet_add_lintegral_of_memH1 a ε hw, energy_eq_dirichlet_add_lintegral_of_memH1 a ε hu,
    mul_add]
  exact add_le_add (hGrad.trans (by gcongr)) (hP.trans (by gcongr))

/-- Short cylindrical terminal regions have a filling with the actual
transported trace and one factor of their physical radius in the cost. -/
theorem exists_penalized_terminalCylinder_fill (a : BulkCoefficients)
    (hTransport : External.AmbientBiLipschitzSobolevPullback3) :
    ∃ K : ℝ, 0 < K ∧ ∀ {e : Point} (he : ‖e‖ = 1) (c : Point)
      {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R)
      (ε : ElasticScale) (b : UnitTensorSphere → S0) (hb : MemSphereH1 b) (B : ℝ),
      (∀ᵐ θ ∂tensorSphereMeasure, ‖b θ‖ ≤ B) →
      let U := terminalCylinderCap e c R H
      let F := terminalCylinderBallChart he c hR hLow hHigh
      ∃ (w : Point → S0) (D : Point → Gradient) (T : RadialL2Trace (R / 2) R),
        MemH1 U w D ∧
        (∀ θ : UnitTensorSphere, w (F.symm (R • θ.val)) = b θ) ∧
        RepresentsRadialL2Trace 0 (w ∘ F.symm) T ∧
        (∀ t, T t = hb.1.toLp (fun θ => frobeniusCoordinateEquiv (b θ))) ∧
        (∀ᵐ x ∂volume.restrict U, ‖w x‖ ≤ B) ∧
        energy a ε U w D ≤ ENNReal.ofReal (K * R *
          ((1 / 2 : ℝ) * sphereGradientEnergy b hb + R ^ 2 * sphereScaledBulkEnergy a ε b)) := by
  obtain ⟨C, hC, hTransport⟩ := hTransport
  let K := max C ((20 : ℝ) ^ 3)
  have hK : 0 < K := hC.trans_le (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro e he c R H hR hLow hHigh ε b hb B hBound U F
  let V := ballDomain (0 : Point) R
  have hU : U = F ⁻¹' V.val := terminalCylinderCap_eq_preimage_ball he c hR hLow hHigh
  have hfLip : LipschitzWith 20 (F : Point → Point) := by
    intro x y
    refine (lipschitz_terminalCylinderBallChart he c hR hLow hHigh x y).trans ?_
    gcongr
    norm_num
  have hfiLip : LipschitzWith 20 (F.symm : Point → Point) :=
    lipschitz_terminalCylinderBallChart_symm he c hR hLow hHigh
  obtain ⟨u, J, T, hu, hRad, hRep, hT, hUB, hEnergy⟩ :=
    exists_penalized_radial_ball_extension a ε b hb B hBound hR
  have hNative : MemW12 V (frobeniusField u) (frobeniusGradient J) :=
    (memH1_iff_memW12 V _ _).1 hu
  obtain ⟨E, hE, hDir⟩ := hTransport F hfLip hfiLip V _ _ hNative
  let w := u ∘ F
  let D (x : Point) (i : Fin 3) := frobeniusCoordinateEquiv.symm (E x i)
  let U' : OpenDomain 3 := ⟨F ⁻¹' V.val, V.property.preimage F.continuous⟩
  have hFrob : frobeniusField w = (frobeniusField u) ∘ F := rfl
  have hCol : frobeniusGradient D = E := funext fun x => funext fun i =>
    frobeniusCoordinateEquiv.apply_symm_apply (E x i)
  have hw : MemH1 (F ⁻¹' V.val) w D := (memH1_iff_memW12 U' w D).2 (hFrob.symm ▸ hCol.symm ▸ hE)
  have hRange : ∀ᵐ x ∂volume.restrict U, ‖w x‖ ≤ B := by
    rw [hU]
    have hDom := homeomorph_map_volume_le_cube F hfiLip V.val
    have hQM : Measure.QuasiMeasurePreserving F (volume.restrict (F ⁻¹' V.val)) (volume.restrict V.val) :=
      ⟨F.continuous.measurable, Measure.absolutelyContinuous_of_le_smul hDom⟩
    exact hQM.ae hUB
  have hDF : dirichletEnergy (F ⁻¹' V.val) D ≤ ENNReal.ofReal C * dirichletEnergy V.val J := by
    rw [dirichletEnergy_eq_half_upstream, hCol, dirichletEnergy_eq_half_upstream,
      mul_left_comm (ENNReal.ofReal C)]
    exact mul_le_mul_right hDir _
  have hBack : w ∘ F.symm = u := by
    funext x
    change u (F (F.symm x)) = u x
    rw [Homeomorph.apply_symm_apply]
  refine ⟨w, D, T, hU.symm ▸ hw, ?_, hBack.symm ▸ hRep, hT, hRange, ?_⟩
  · intro θ
    change u (F (F.symm (R • θ.val))) = b θ
    rw [Homeomorph.apply_symm_apply]
    exact hRad ⟨R, hR⟩ θ
  · rw [hU]
    refine (pullback_energy_le ε F hu hw hDF hfiLip).trans ?_
    refine (mul_le_mul_right hEnergy.le _).trans ?_
    rw [← ENNReal.ofReal_mul hK.le]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_assoc K R]
    apply mul_le_mul_of_nonneg_left ?_ hK.le
    have hB₀ := nonneg_sphereScaledBulkEnergy a ε b
    have hCube : R ^ 3 / 3 ≤ R ^ 3 := by linarith only [pow_nonneg hR.le 3]
    calc
      _ ≤ (1 / 2 : ℝ) * R * sphereGradientEnergy b hb + R ^ 3 * sphereScaledBulkEnergy a ε b :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hCube hB₀)
      _ = _ := by ring

end MeasureGeometry
end Thesis
