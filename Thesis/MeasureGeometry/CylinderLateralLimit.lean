module

public import Thesis.MeasureGeometry.CylinderSliceEnergy
public import Thesis.Variational.InteriorBulkSmall
import Thesis.Variational.BoundaryPoissonEstimate
import Thesis.Variational.BoundaryPohozaev

/-! The actual angular and bulk energies of a regular lateral surface. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius RealInnerProductSpace Topology

namespace Thesis.MeasureGeometry

private def lateralAngle (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (Q : Point → S0) (r z t : ℝ) : S0 :=
  cylinderSliceMap B c Q z (r • (circleNativeParam (t - Real.pi)).val)

private def lateralPoint (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (r z t : ℝ) : Point :=
  c + axisChart B (r • (circleNativeParam (t - Real.pi)).val, z)

private def lateralVelocity (B : OrthonormalBasis (Fin 3) ℝ Point) (r t : ℝ) : Point :=
  axisChartPlane B (r • deriv (fun u => (circleNativeParam u).val) (t - Real.pi))

private theorem continuous_lateralPoint (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (r : ℝ) :
    Continuous (fun p : ℝ × ℝ => lateralPoint B c r p.2 p.1) := by
  change Continuous (fun p : ℝ × ℝ => c + axisChart B
    (r • (circleNativeParam (p.1 - Real.pi)).val, p.2))
  have hA : Continuous (fun p : ℝ × ℝ => (circleNativeParam (p.1 - Real.pi)).val) :=
    continuous_subtype_val.comp (continuous_circleNativeParam.comp (continuous_fst.sub continuous_const))
  have hR : Continuous (fun p : ℝ × ℝ => r • (circleNativeParam (p.1 - Real.pi)).val) := hA.const_smul r
  exact continuous_const.add ((continuous_axisChart B).comp (hR.prodMk continuous_snd))

private theorem continuous_lateralVelocity (B : OrthonormalBasis (Fin 3) ℝ Point) (r : ℝ) :
    Continuous (lateralVelocity B r) := by
  have hArg : Continuous (fun t : ℝ => t - Real.pi) := continuous_id.sub continuous_const
  exact (axisChartPlane B).continuous.comp
    ((contDiff_circleNativeParam_val.continuous_deriv_one.comp hArg).const_smul r)

private theorem lateralAngle_deriv_eq {B : OrthonormalBasis (Fin 3) ℝ Point} {c : Point}
    {Q : Point → S0} {r z t : ℝ}
    (hQ : DifferentiableAt ℝ Q (lateralPoint B c r z t)) :
    deriv (lateralAngle B c Q r z) t = fderiv ℝ Q (lateralPoint B c r z t) (lateralVelocity B r t) := by
  have hParam : HasDerivAt (fun u => (circleNativeParam u).val)
      (deriv (fun u => (circleNativeParam u).val) (t - Real.pi)) (t - Real.pi) :=
    (contDiff_circleNativeParam_val.differentiable one_ne_zero _).hasDerivAt
  have hR : HasDerivAt (fun u => r • (circleNativeParam (u - Real.pi)).val)
      (r • deriv (fun u => (circleNativeParam u).val) (t - Real.pi)) t := by
    have hArg : HasDerivAt (fun u : ℝ => u - Real.pi) 1 t := (hasDerivAt_id t).sub_const Real.pi
    simpa only [Function.comp_def, one_smul, Pi.smul_def] using! (hParam.scomp t hArg).const_smul r
  have hΦ : HasFDerivAt (fun y => c + axisChart B (y, z)) (axisChartPlane B)
      (r • (circleNativeParam (t - Real.pi)).val) := by
    simp_rw [axisChart_eq_plane_add_axis]
    exact ((axisChartPlane B).hasFDerivAt.add_const _).const_add _
  have hΓ := hΦ.comp_hasDerivAt t hR
  exact (hQ.hasFDerivAt.comp_hasDerivAt t hΓ).deriv

private theorem lateralAngle_deriv_sq_le {B : OrthonormalBasis (Fin 3) ℝ Point} {c : Point}
    {Q : Point → S0} {r z t : ℝ} (hr : 0 ≤ r)
    (hQ : DifferentiableAt ℝ Q (lateralPoint B c r z t)) :
    ‖deriv (lateralAngle B c Q r z) t‖ ^ 2 ≤
      r ^ 2 * gradientNormSq (ClassicalGradient Q (lateralPoint B c r z t)) := by
  let x := lateralPoint B c r z t
  let v := lateralVelocity B r t
  have hv : ‖v‖ = r := by
    dsimp only [v]
    rw [lateralVelocity, norm_axisChartPlane, norm_smul, Real.norm_of_nonneg hr,
      norm_deriv_circleNativeParam_val, mul_one]
  have h := norm_gradientFromColumns_le (ClassicalGradient Q x) v
  rw [gradientFromColumns_classicalGradient, hv] at h
  have h₀ : 0 ≤ gradientNormSq (ClassicalGradient Q x) := by
    rw [gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [lateralAngle_deriv_eq hQ]
  change ‖fderiv ℝ Q x v‖ ^ 2 ≤ _
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [mul_pow, Real.sq_sqrt h₀] at hh

/-- The angular cost in the cylinder comparison is integrable in height,
and is bounded by the actual three-dimensional energy density on each
regular lateral circle. -/
theorem integrable_cylinderLateralSliceCost_and_bound
    (a : BulkCoefficients) (ε : ElasticScale) (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) {Q : Point → S0} {Ω : Set Point} (hΩ : IsOpen Ω) (hQ : ContDiffOn ℝ ∞ Q Ω)
    {r lo hi C : ℝ} (hr : 0 ≤ r)
    (hSide : ∀ z ∈ Icc lo hi, ∀ w : NativeCircle, c + axisChart B (r • w.val, z) ∈ Ω)
    (hBound : ∀ z ∈ Icc lo hi, ∀ w : NativeCircle,
      energyDensity a ε (Q (c + axisChart B (r • w.val, z)))
        (ClassicalGradient Q (c + axisChart B (r • w.val, z))) ≤ C) :
    IntegrableOn (cylinderLateralSliceCost a ε r B c Q) (Ioo lo hi) ∧
    ∀ z ∈ Icc lo hi, cylinderLateralSliceCost a ε r B c Q z ≤ r ^ 2 * C * (2 * Real.pi) := by
  let I := Icc (0 : ℝ) (2 * Real.pi)
  let J := Icc lo hi
  let F (p : ℝ × ℝ) := lateralPoint B c r p.2 p.1
  let D (p : ℝ × ℝ) := ‖deriv (lateralAngle B c Q r p.2) p.1‖ ^ 2
  let V (p : ℝ × ℝ) := bulkPotential a (Q (F p))
  have hF : Continuous F := continuous_lateralPoint B c r
  have hFU (p : ℝ × ℝ) (hp : p ∈ I ×ˢ J) : F p ∈ Ω :=
    hSide p.2 hp.2 (circleNativeParam (p.1 - Real.pi))
  have hFDeriv : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ Q (F p)) (I ×ˢ J) :=
    (hQ.continuousOn_fderiv_of_isOpen hΩ (by simp)).comp hF.continuousOn hFU
  have hD : ContinuousOn D (I ×ˢ J) := by
    have hD' := ((hFDeriv.clm_apply ((continuous_lateralVelocity B r).comp continuous_fst).continuousOn).norm).pow 2
    apply hD'.congr
    intro p hp
    dsimp only [D]
    rw [lateralAngle_deriv_eq
      (((hQ _ (hFU p hp)).contDiffAt (hΩ.mem_nhds (hFU p hp))).differentiableAt (by simp))]
    rfl
  have hV : ContinuousOn V (I ×ˢ J) :=
    (contDiff_bulkPotential a).continuous.comp_continuousOn (hQ.continuousOn.comp hF.continuousOn hFU)
  have hIJ : IsCompact (I ×ˢ J) := isCompact_Icc.prod isCompact_Icc
  let μ : Measure ℝ := volume.restrict (Ioo 0 (2 * Real.pi))
  let ν : Measure ℝ := volume.restrict (Ioo lo hi)
  have hProd (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (I ×ˢ J)) : Integrable g (μ.prod ν) := by
    change Integrable g (((volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi))).prod
      (volume.restrict (Ioo lo hi)))
    rw [Measure.prod_restrict]
    exact (hg.integrableOn_compact hIJ).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hDProd := (hProd D hD).integral_prod_right
  have hVProd := (hProd V hV).integral_prod_right
  refine ⟨(hDProd.const_mul (1 / 2 : ℝ)).add (hVProd.const_mul ((r / (ε : ℝ)) ^ 2)), ?_⟩
  intro z hz
  have hComp : Continuous (fun t : ℝ => (t, z)) := continuous_id.prodMk continuous_const
  have hM : MapsTo (fun t : ℝ => (t, z)) I (I ×ˢ J) := fun _ ht => ⟨ht, hz⟩
  have hDc : ContinuousOn (fun t => D (t,z)) I := hD.comp hComp.continuousOn hM
  have hVc : ContinuousOn (fun t => V (t,z)) I := hV.comp hComp.continuousOn hM
  have hDz : IntegrableOn (fun t => D (t,z)) (Ioo 0 (2 * Real.pi)) :=
    (hDc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hVz : IntegrableOn (fun t => V (t,z)) (Ioo 0 (2 * Real.pi)) :=
    (hVc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  change (1 / 2 : ℝ) * (∫ t in Ioo 0 (2 * Real.pi), D (t,z)) +
      (r / (ε : ℝ)) ^ 2 * (∫ t in Ioo 0 (2 * Real.pi), V (t,z)) ≤ _
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hDz.const_mul _) (hVz.const_mul _)]
  have hInt : IntegrableOn (fun _ : ℝ => r ^ 2 * C) (Ioo 0 (2 * Real.pi)) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  refine (setIntegral_mono_on ((hDz.const_mul _).add (hVz.const_mul _)) hInt
    measurableSet_Ioo (fun t _ => ?_)).trans_eq ?_
  · let x := F (t,z)
    have hx := hSide z hz (circleNativeParam (t - Real.pi))
    have hG := lateralAngle_deriv_sq_le hr
      (((hQ _ hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
    have hE := mul_le_mul_of_nonneg_left (hBound z hz (circleNativeParam (t - Real.pi))) (sq_nonneg r)
    change (1 / 2 : ℝ) * D (t,z) + (r / (ε : ℝ)) ^ 2 * V (t,z) ≤ _
    change D (t,z) ≤ r ^ 2 * gradientNormSq (ClassicalGradient Q x) at hG
    change r ^ 2 * energyDensity a ε (Q x) (ClassicalGradient Q x) ≤ _ at hE
    unfold energyDensity at hE
    have hCoeff : (r / (ε : ℝ)) ^ 2 = r ^ 2 * (ε : ℝ)⁻¹ ^ 2 := by
      rw [div_eq_mul_inv, mul_pow]
    rw [hCoeff]
    change (1 / 2 : ℝ) * D (t,z) + (r ^ 2 * (ε : ℝ)⁻¹ ^ 2) * bulkPotential a (Q x) ≤ _
    linarith only [hG, hE]
  · rw [setIntegral_const, Measure.real_def, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    ring

end Thesis.MeasureGeometry
