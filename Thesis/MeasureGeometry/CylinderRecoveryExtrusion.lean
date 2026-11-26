module

public import Thesis.MeasureGeometry.CylinderSliceEnergy
public import Thesis.Upstream.MinimizingSobolev
import StratificationTheory.Interpolation.CylinderLinearInterpolation
import StratificationTheory.Foundation.SmoothOpenDomainSobolevPullback
import StratificationTheory.Foundation.IsometricSobolevPullback

/-! The planar recovery core extended at constant height in the actual
translated orthonormal cylinder. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis.MeasureGeometry

/-- The canonical split of planar coordinates and the height coordinate. -/
def recoveryReferenceSplit (x : Point) : Plane × ℝ :=
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  ((e x).1, (e x).2 0)

private theorem continuous_recoveryReferenceSplit : Continuous recoveryReferenceSplit :=
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  (continuous_fst.comp e.continuous).prodMk
    ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp (continuous_snd.comp e.continuous))

theorem recoveryReferenceSplit_injective : Function.Injective recoveryReferenceSplit := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  intro x y h
  apply e.injective
  apply Prod.ext
  · exact congrArg (fun p : Plane × ℝ => p.1) h
  · ext i
    fin_cases i
    exact congrArg (fun p : Plane × ℝ => p.2) h

private theorem recoveryReferenceSplit_pack (p : Plane × ℝ) :
    recoveryReferenceSplit (planeLinePack (WithLp.toLp 2 p)) = p := by
  rcases p with ⟨y, z⟩
  apply Prod.ext
  · ext i
    fin_cases i <;>
      simp [recoveryReferenceSplit, planeLinePack, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
        PiLp.sumPiLpEquivProdLpPiLp, finSumFinEquiv]
  · simp [recoveryReferenceSplit, planeLinePack, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      PiLp.sumPiLpEquivProdLpPiLp, finSumFinEquiv]

private def recoveryReferenceCylinder (r lo hi : ℝ) : OpenDomain 3 :=
  ⟨recoveryReferenceSplit ⁻¹' (ball (0 : Plane) r ×ˢ Ioo lo hi),
    (isOpen_ball.prod isOpen_Ioo).preimage continuous_recoveryReferenceSplit⟩

/-- The native open domain of the physical cylinder. -/
def translatedAxisCylinderDomain (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (r lo hi : ℝ) : OpenDomain 3 :=
  ⟨translatedAxisCylinder c (B 2) r lo hi, isOpen_translatedAxisCylinder c (B 2) r lo hi⟩

/-- Coordinates relative to the actual axis and translation of the
cylinder. The first component lies in the physical transverse plane. -/
def cylinderRecoveryCoordinates (B : OrthonormalBasis (Fin 3) ℝ Point) (c x : Point) : Plane × ℝ :=
  recoveryReferenceSplit (B.repr (x - c))

theorem cylinderRecoveryCoordinates_axisChart (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (p : Plane × ℝ) :
    cylinderRecoveryCoordinates B c (c + axisChart B p) = p := by
  rw [cylinderRecoveryCoordinates, add_sub_cancel_left, axisChart, LinearIsometryEquiv.apply_symm_apply]
  exact recoveryReferenceSplit_pack p

theorem axisChart_cylinderRecoveryCoordinates (B : OrthonormalBasis (Fin 3) ℝ Point) (c x : Point) :
    c + axisChart B (cylinderRecoveryCoordinates B c x) = x := by
  have h := cylinderRecoveryCoordinates_axisChart B c (cylinderRecoveryCoordinates B c x)
  exact sub_left_injective (B.repr.injective (recoveryReferenceSplit_injective h))

private theorem preimage_recoveryReferenceCylinder (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (r lo hi : ℝ) :
    (fun x : Point => B.repr (x - c)) ⁻¹' (recoveryReferenceCylinder r lo hi).val =
      translatedAxisCylinder c (B 2) r lo hi := by
  ext x
  change cylinderRecoveryCoordinates B c x ∈ ball (0 : Plane) r ×ˢ Ioo lo hi ↔
    x - c ∈ openAxisCylinder (B 2) r lo hi
  have hAx : axisChart B (cylinderRecoveryCoordinates B c x) = x - c := by
    simpa only [add_sub_cancel_left] using
      congrArg (fun y : Point => y - c) (axisChart_cylinderRecoveryCoordinates B c x)
  rw [← preimage_openAxisCylinder_axisChart B, mem_preimage, hAx]

private theorem measurePreserving_recoveryReferenceRotation (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (r lo hi : ℝ) :
    MeasurePreserving (fun x : Point => B.repr (x - c))
      (volume.restrict (translatedAxisCylinder c (B 2) r lo hi))
      (volume.restrict (recoveryReferenceCylinder r lo hi).val) := by
  have hF : MeasurePreserving (fun x : Point => B.repr (x - c)) volume volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      B.repr.measurePreserving.comp (measurePreserving_add_right (volume : Measure Point) (-c))
  have h := hF.restrict_preimage (recoveryReferenceCylinder r lo hi).property.measurableSet
  rwa [preimage_recoveryReferenceCylinder] at h

private theorem measurePreserving_recoveryReferenceSplit (r lo hi : ℝ) :
    MeasurePreserving recoveryReferenceSplit (volume.restrict (recoveryReferenceCylinder r lo hi).val)
      (((volume : Measure Plane).restrict (ball 0 r)).prod ((volume : Measure ℝ).restrict (Ioo lo hi))) := by
  have h := (StratificationTheory.measurePreserving_cylinder_coordinates 2).restrict_preimage
    (measurableSet_ball.prod measurableSet_Ioo : MeasurableSet (ball (0 : Plane) r ×ˢ Ioo lo hi))
  change MeasurePreserving recoveryReferenceSplit _ _ at h
  rwa [← Measure.prod_restrict] at h

theorem measurePreserving_cylinderRecoveryCoordinates (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (r lo hi : ℝ) :
    MeasurePreserving (cylinderRecoveryCoordinates B c)
      (volume.restrict (translatedAxisCylinder c (B 2) r lo hi))
      (((volume : Measure Plane).restrict (ball 0 r)).prod ((volume : Measure ℝ).restrict (Ioo lo hi))) :=
  (measurePreserving_recoveryReferenceSplit r lo hi).comp (measurePreserving_recoveryReferenceRotation B c r lo hi)

/-- Projecting the cylinder volume to its transverse disk multiplies the
disk measure by the exact cylinder height. -/
theorem measure_map_cylinderRecoveryBase (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (r lo hi : ℝ) :
    Measure.map (fun x => (cylinderRecoveryCoordinates B c x).1)
      (volume.restrict (translatedAxisCylinder c (B 2) r lo hi)) =
        ENNReal.ofReal (hi - lo) • (volume.restrict (ball (0 : Plane) r)) := by
  have hMP := measurePreserving_cylinderRecoveryCoordinates B c r lo hi
  change Measure.map (Prod.fst ∘ cylinderRecoveryCoordinates B c) _ = _
  rw [← Measure.map_map measurable_fst hMP.measurable, hMP.map_eq, Measure.map_fst_prod,
    Measure.restrict_apply_univ, Real.volume_Ioo]

/-- The actual constant-height field, evaluated at the transverse
coordinate of the physical point. -/
def cylinderRecoveryField (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (w : Plane → Ambient 5) (x : Point) : Ambient 5 :=
  w (cylinderRecoveryCoordinates B c x).1

/-- The planar weak columns, padded by a zero axial column and expressed
in the fixed ambient coordinates. -/
def cylinderRecoveryDerivative (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (Dw : Plane → HarmonicMaps.Gradient 2 5) (x : Point) (i : Fin 3) : Ambient 5 :=
  ∑ j : Fin 3, (B.repr (EuclideanSpace.single i 1)) j •
    Fin.addCases (Dw (cylinderRecoveryCoordinates B c x).1) (fun _ : Fin 1 => 0) j

theorem cylinderRecoveryField_axisChart (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (w : Plane → Ambient 5) (y : Plane) (z : ℝ) :
    cylinderRecoveryField B c w (c + axisChart B (y, z)) = w y := by
  rw [cylinderRecoveryField, cylinderRecoveryCoordinates_axisChart]

theorem cylinderRecoveryDerivative_hsNormSq (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (Dw : Plane → HarmonicMaps.Gradient 2 5) (x : Point) :
    hsNormSq (cylinderRecoveryDerivative B c Dw x) =
      hsNormSq (Dw (cylinderRecoveryCoordinates B c x).1) := by
  unfold cylinderRecoveryDerivative
  rw [StratificationTheory.hsNormSq_source_isometry]
  let D : Fin (2 + 1) → Ambient 5 := fun j => Fin.addCases
    (fun k : Fin 2 => Dw (cylinderRecoveryCoordinates B c x).1 k) (fun _ : Fin 1 => 0) j
  change (∑ j : Fin (2 + 1), ‖D j‖ ^ 2) = _
  rw [Fin.sum_univ_add (a := 2) (b := 1)]
  simp only [D, Fin.addCases_left, Fin.addCases_right, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, add_zero, hsNormSq]

/-- The exact extrusion weak graph on the translated physical cylinder. -/
theorem cylinderRecovery_memW12 (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (r lo hi : ℝ)
    {w : Plane → Ambient 5} {Dw : Plane → HarmonicMaps.Gradient 2 5}
    (hw : MemW12 (ballDomain (0 : Plane) r) w Dw) :
    MemW12 (translatedAxisCylinderDomain B c r lo hi) (cylinderRecoveryField B c w)
      (cylinderRecoveryDerivative B c Dw) := by
  let Ω := translatedAxisCylinderDomain B c r lo hi
  let V := recoveryReferenceCylinder r lo hi
  let F : Point → Point := B.repr.toContinuousLinearEquiv ∘ (fun x : Point => x - c)
  let W (x : Point) := w (recoveryReferenceSplit x).1
  let D (x : Point) : HarmonicMaps.Gradient 3 5 :=
    fun i => Fin.addCases (fun j : Fin 2 => Dw (recoveryReferenceSplit x).1 j)
      (fun _ : Fin 1 => (0 : Ambient 5)) (show Fin (2 + 1) from i)
  have hVol : (volume : Measure Plane) (ball 0 r) ≠ ⊤ :=
    ((measure_mono ball_subset_closedBall).trans_lt ((isCompact_closedBall (0 : Plane) r).measure_lt_top)).ne
  have hW : MemW12 V W D :=
    StratificationTheory.MemW12.cylinder_lift (ballDomain (0 : Plane) r) hVol lo hi hw
  have hF : ContDiff ℝ ∞ F :=
    B.repr.toContinuousLinearEquiv.contDiff.comp (contDiff_id.sub contDiff_const)
  let L := B.repr.toContinuousLinearEquiv.toContinuousLinearMap
  have hDF (x : Point) : fderiv ℝ F x = L := by
    exact ((B.repr.toContinuousLinearEquiv.hasFDerivAt.comp x
      ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c)).fderiv).trans (ContinuousLinearMap.comp_id L)
  have hDL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖B.repr x‖ ≤ 1 * ‖x‖
    rw [B.repr.norm_map, one_mul]
  have hMap : MapsTo F Ω.val V.val := by
    intro x hx
    have h := preimage_recoveryReferenceCylinder B c r lo hi
    exact show x ∈ F ⁻¹' V.val from h.symm ▸ hx
  have hMP := measurePreserving_recoveryReferenceRotation B c r lo hi
  have hμ : Measure.map F (volume.restrict Ω.val) ≤ (1 : ℝ≥0∞) • volume.restrict V.val := by
    rw [one_smul]
    exact hMP.map_eq.le
  have hWeak := StratificationTheory.memW12_smooth_open_domain_pullback hW Ω F hF.contDiffOn hMap 1
    (fun x _ => by rw [hDF x]; exact hDL) 1 ENNReal.one_ne_top hμ
  simp_rw [hDF] at hWeak
  exact hWeak

/-- A transverse integrand is multiplied by the exact height, with the
same original disk measure. -/
theorem lintegral_cylinderRecoveryBase_eq_height_mul
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (r lo hi : ℝ)
    (f : Plane → ℝ≥0∞) (hf : AEMeasurable f (volume.restrict (ball (0 : Plane) r))) :
    (∫⁻ x in translatedAxisCylinder c (B 2) r lo hi, f (cylinderRecoveryCoordinates B c x).1) =
      ENNReal.ofReal (hi - lo) * ∫⁻ y in ball (0 : Plane) r, f y := by
  let μ := (volume : Measure Point).restrict (translatedAxisCylinder c (B 2) r lo hi)
  let P (x : Point) := (cylinderRecoveryCoordinates B c x).1
  have hP : Measurable P := measurable_fst.comp (measurePreserving_cylinderRecoveryCoordinates B c r lo hi).measurable
  have hMap := measure_map_cylinderRecoveryBase B c r lo hi
  have hF : AEMeasurable f (Measure.map P μ) := by
    rw [hMap]
    exact hf.smul_measure _
  calc
    _ = ∫⁻ y, f y ∂Measure.map P μ := (lintegral_map' hF hP.aemeasurable).symm
    _ = _ := by rw [hMap, lintegral_smul_measure, smul_eq_mul]

theorem cylinderRecovery_dirichletEnergy (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (r lo hi : ℝ) {w : Plane → Ambient 5} {Dw : Plane → HarmonicMaps.Gradient 2 5}
    (hw : MemW12 (ballDomain (0 : Plane) r) w Dw) :
    HarmonicMaps.dirichletEnergy (cylinderRecoveryDerivative B c Dw) (translatedAxisCylinder c (B 2) r lo hi) =
      ENNReal.ofReal (hi - lo) * HarmonicMaps.dirichletEnergy Dw (ball (0 : Plane) r) := by
  unfold HarmonicMaps.dirichletEnergy
  simp_rw [cylinderRecoveryDerivative_hsNormSq]
  exact lintegral_cylinderRecoveryBase_eq_height_mul B c r lo hi _
    hw.integrable_hsNormSq.aestronglyMeasurable.aemeasurable.ennreal_ofReal

def cylinderRecoveryTensorField (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (w : Plane → Ambient 5) (x : Point) : S0 :=
  frobeniusCoordinateEquiv.symm (cylinderRecoveryField B c w x)

def cylinderRecoveryTensorDerivative (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (Dw : Plane → HarmonicMaps.Gradient 2 5) (x : Point) (i : Fin 3) : S0 :=
  frobeniusCoordinateEquiv.symm (cylinderRecoveryDerivative B c Dw x i)

theorem cylinderRecovery_tensorMemH1 (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (r lo hi : ℝ) {w : Plane → Ambient 5} {Dw : Plane → HarmonicMaps.Gradient 2 5}
    (hw : MemW12 (ballDomain (0 : Plane) r) w Dw) :
    MemH1 (translatedAxisCylinder c (B 2) r lo hi) (cylinderRecoveryTensorField B c w)
      (cylinderRecoveryTensorDerivative B c Dw) := by
  apply (memH1_iff_memW12 (translatedAxisCylinderDomain B c r lo hi) _ _).2
  have hF : frobeniusField (cylinderRecoveryTensorField B c w) = cylinderRecoveryField B c w :=
    funext fun _ => frobeniusCoordinateEquiv.apply_symm_apply _
  have hD : frobeniusGradient (cylinderRecoveryTensorDerivative B c Dw) = cylinderRecoveryDerivative B c Dw :=
    funext fun _ => funext fun _ => frobeniusCoordinateEquiv.apply_symm_apply _
  rw [hF, hD]
  exact cylinderRecovery_memW12 B c r lo hi hw

/-- The exact energy of the constant-height recovery core, retaining the
displayed planar weak columns and the actual sextic bulk potential. -/
theorem cylinderRecovery_tensorEnergy_eq_height_mul_planarWeakEnergy
    (a : BulkCoefficients) (ε : ElasticScale) (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (r lo hi : ℝ) (hHeight : lo ≤ hi) {w : Plane → Ambient 5} {Dw : Plane → HarmonicMaps.Gradient 2 5}
    (hw : MemW12 (ballDomain (0 : Plane) r) w Dw)
    (hBulk : IntegrableOn (fun y => planarCoordinateBulkPotential a (w y)) (ball (0 : Plane) r)) :
    energy a ε (translatedAxisCylinder c (B 2) r lo hi) (cylinderRecoveryTensorField B c w)
      (cylinderRecoveryTensorDerivative B c Dw) =
        ENNReal.ofReal ((hi - lo) * planarWeakEnergy a (ε : ℝ) w Dw r) := by
  let f (y : Plane) := (1 / 2 : ℝ) * hsNormSq (Dw y) +
    (ε : ℝ)⁻¹ ^ 2 * planarCoordinateBulkPotential a (w y)
  have hFP (y : Plane) : 0 ≤ f y :=
    add_nonneg (mul_nonneg (by norm_num) (hsNormSq_nonneg _))
      (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _))
  have hI₁ : IntegrableOn (fun y => (1 / 2 : ℝ) * hsNormSq (Dw y)) (ball (0 : Plane) r) :=
    hw.integrable_hsNormSq.const_mul _
  have hI₂ : IntegrableOn (fun y => (ε : ℝ)⁻¹ ^ 2 * planarCoordinateBulkPotential a (w y))
      (ball (0 : Plane) r) := hBulk.const_mul _
  have hI : IntegrableOn f (ball (0 : Plane) r) := hI₁.add hI₂
  have hReal : (∫ y in ball (0 : Plane) r, f y) = planarWeakEnergy a (ε : ℝ) w Dw r := by
    change (∫ y in ball (0 : Plane) r, (1 / 2 : ℝ) * hsNormSq (Dw y) +
      (ε : ℝ)⁻¹ ^ 2 * planarCoordinateBulkPotential a (w y)) = _
    rw [integral_add hI₁ hI₂, integral_const_mul, integral_const_mul]
    rfl
  have hEq (x : Point) :
      energyDensity a ε (cylinderRecoveryTensorField B c w x) (cylinderRecoveryTensorDerivative B c Dw x) =
        f (cylinderRecoveryCoordinates B c x).1 := by
    have hG : gradientNormSq (cylinderRecoveryTensorDerivative B c Dw x) =
        hsNormSq (cylinderRecoveryDerivative B c Dw x) := by
      rw [gradientNormSq_eq_sum_norm_sq]
      simp only [cylinderRecoveryTensorDerivative, LinearIsometryEquiv.norm_map, hsNormSq]
    unfold energyDensity f
    rw [hG, cylinderRecoveryDerivative_hsNormSq]
    rfl
  unfold energy
  simp_rw [hEq]
  rw [lintegral_cylinderRecoveryBase_eq_height_mul B c r lo hi _
    hI.aestronglyMeasurable.aemeasurable.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hFP), hReal,
    ENNReal.ofReal_mul (sub_nonneg.mpr hHeight)]

end Thesis.MeasureGeometry

end
