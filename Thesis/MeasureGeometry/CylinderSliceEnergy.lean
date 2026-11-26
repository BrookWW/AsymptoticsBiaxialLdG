module

public import Thesis.MeasureGeometry.CylinderCoordinates
public import Thesis.MeasureGeometry.PlanarBoundaryScaling
import Mathlib.MeasureTheory.Integral.Prod
import Thesis.StressEnergy

/-! The exact planar lower bound integrated on an oriented cylinder. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius RealInnerProductSpace Topology

namespace Thesis.MeasureGeometry

def translatedAxisCylinder (c e : Point) (r lo hi : ℝ) : Set Point :=
  (fun x : Point => x - c) ⁻¹' openAxisCylinder e r lo hi

def translatedClosedAxisCylinder (c e : Point) (r lo hi : ℝ) : Set Point :=
  (fun x : Point => x - c) ⁻¹' closedAxisCylinder e r lo hi

theorem isOpen_translatedAxisCylinder (c e : Point) (r lo hi : ℝ) :
    IsOpen (translatedAxisCylinder c e r lo hi) :=
  (isOpen_openAxisCylinder e r lo hi).preimage (continuous_id.sub continuous_const)

theorem isCompact_translatedClosedAxisCylinder {c e : Point} (he : ‖e‖ = 1) (r lo hi : ℝ) :
    IsCompact (translatedClosedAxisCylinder c e r lo hi) := by
  have hEq : translatedClosedAxisCylinder c e r lo hi = (fun x : Point => c + x) '' closedAxisCylinder e r lo hi := by
    ext x
    constructor
    · intro hx
      exact ⟨x - c, hx, by abel⟩
    · rintro ⟨y, hy, rfl⟩
      change c + y - c ∈ closedAxisCylinder e r lo hi
      rwa [add_sub_cancel_left]
  rw [hEq]
  exact (isCompact_closedAxisCylinder he r lo hi).image (continuous_const.add continuous_id)

theorem translatedAxisCylinder_subset_closed (c e : Point) (r lo hi : ℝ) :
    translatedAxisCylinder c e r lo hi ⊆ translatedClosedAxisCylinder c e r lo hi := by
  intro x hx
  change x - c ∈ openAxisCylinder e r lo hi at hx
  change x - c ∈ closedAxisCylinder e r lo hi
  exact openAxisCylinder_subset_closedAxisCylinder e r lo hi hx

/-- Fubini in the genuine translated oriented cylinder. -/
theorem integral_translatedAxisCylinder_eq_iterated
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (r lo hi : ℝ)
    (f : Point → ℝ) (hf : IntegrableOn f (translatedAxisCylinder c (B 2) r lo hi)) :
    Integrable (fun p : Plane × ℝ => f (c + axisChart B p))
      (((volume : Measure Plane).restrict (ball 0 r)).prod ((volume : Measure ℝ).restrict (Ioo lo hi))) ∧
    (∫ x in translatedAxisCylinder c (B 2) r lo hi, f x) =
      ∫ z in Ioo lo hi, ∫ y in ball (0 : Plane) r, f (c + axisChart B (y, z)) := by
  classical
  let S := translatedAxisCylinder c (B 2) r lo hi
  let T (p : Plane × ℝ) := c + axisChart B p
  let P := (ball (0 : Plane) r) ×ˢ Ioo lo hi
  let ν := ((volume : Measure Plane).prod (volume : Measure ℝ))
  have hS : MeasurableSet S := (isOpen_translatedAxisCylinder _ _ _ _ _).measurableSet
  have hP : MeasurableSet P := measurableSet_ball.prod measurableSet_Ioo
  have hT : MeasurePreserving T ν (volume : Measure Point) := by
    simpa only [T, Function.comp_def, add_comm c] using
      (measurePreserving_add_left (volume : Measure Point) c).comp (measurePreserving_axisChart B)
  have hPre : T ⁻¹' S = P := by
    have hC := preimage_openAxisCylinder_axisChart B r lo hi
    convert hC using 1
    ext p
    change c + axisChart B p - c ∈ openAxisCylinder (B 2) r lo hi ↔ _
    rw [add_sub_cancel_left]
    rfl
  have hInd : (fun p => S.indicator f (T p)) = P.indicator (fun p => f (T p)) := by
    funext p
    rw [← hPre]
    by_cases hp : T p ∈ S
    · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ T ⁻¹' S from hp)]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ T ⁻¹' S from hp)]
  have hfI : Integrable (S.indicator f) volume := (integrable_indicator_iff hS).2 hf
  have hIT : Integrable (fun p => S.indicator f (T p)) ν := hT.integrable_comp_of_integrable hfI
  rw [hInd] at hIT
  have hIP : Integrable (fun p => f (T p)) (ν.restrict P) := (integrable_indicator_iff hP).mp hIT
  have hν : ν.restrict P =
      ((volume : Measure Plane).restrict (ball (0 : Plane) r)).prod ((volume : Measure ℝ).restrict (Ioo lo hi)) := by
    exact (Measure.prod_restrict _ _).symm
  constructor
  · rwa [← hν]
  · have hMap : (∫ p, S.indicator f (T p) ∂ν) = ∫ x, S.indicator f x := by
      rw [← integral_map hT.measurable.aemeasurable (hT.map_eq.symm ▸ hfI.aestronglyMeasurable), hT.map_eq]
    rw [hInd, integral_indicator hP, integral_indicator hS] at hMap
    rw [hν] at hIP hMap
    rw [← hMap, integral_prod_symm _ hIP]

private theorem sum_norm_sq_linear_basis_eq {L : Point →ₗ[ℝ] Ambient 5}
    (A B : OrthonormalBasis (Fin 3) ℝ Point) :
    (∑ i, ‖L (A i)‖ ^ 2) = ∑ i, ‖L (B i)‖ ^ 2 := by
  let C := EuclideanSpace.basisFun (Fin 5) ℝ
  have hAux (D : OrthonormalBasis (Fin 3) ℝ Point) :
      (∑ i, ‖L (D i)‖ ^ 2) = ∑ k, ‖L.adjoint (C k)‖ ^ 2 := by
    calc
      _ = ∑ i, ∑ k, ‖inner ℝ (L (D i)) (C k)‖ ^ 2 :=
        Finset.sum_congr rfl (fun _ _ => (C.sum_sq_norm_inner_left _).symm)
      _ = ∑ k, ∑ i, ‖inner ℝ (D i) (L.adjoint (C k))‖ ^ 2 := by
        simp_rw [LinearMap.adjoint_inner_right]
        exact Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun _ _ => D.sum_sq_norm_inner_right _)
  exact (hAux A).trans (hAux B).symm

/-- The transverse slice in the exact same orthonormal coordinates. -/
def cylinderSliceMap (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (Q : Point → S0) (z : ℝ) (y : Plane) : S0 := Q (c + axisChart B (y, z))

private theorem cylinderSlice_pointDeriv {B : OrthonormalBasis (Fin 3) ℝ Point} {c : Point}
    {Q : Point → S0} {y : Plane} {z : ℝ}
    (hQ : DifferentiableAt ℝ Q (c + axisChart B (y, z))) :
    fderiv ℝ (cylinderSliceMap B c Q z) y =
      (fderiv ℝ Q (c + axisChart B (y, z))).comp (axisChartPlane B) := by
  have hAff : HasFDerivAt (fun p => c + axisChart B (p, z)) (axisChartPlane B) y := by
    simp_rw [axisChart_eq_plane_add_axis]
    exact ((((axisChartPlane B).hasFDerivAt (x := y)).add_const (z • B 2)).const_add c)
  exact (hQ.hasFDerivAt.comp y hAff).fderiv

theorem planarSmoothEnergyDensity_slice_le {B : OrthonormalBasis (Fin 3) ℝ Point} {c : Point}
    (a : BulkCoefficients) (ε : ElasticScale) {Q : Point → S0} {y : Plane} {z : ℝ}
    (hQ : DifferentiableAt ℝ Q (c + axisChart B (y, z))) :
    planarSmoothEnergyDensity a ε (cylinderSliceMap B c Q z) y ≤
      energyDensity a ε (Q (c + axisChart B (y, z))) (ClassicalGradient Q (c + axisChart B (y, z))) := by
  let x := c + axisChart B (y, z)
  let L : Point →L[ℝ] S0 := fderiv ℝ Q x
  let v := cylinderSliceMap B c Q z
  have hV := cylinderSlice_pointDeriv (B := B) (c := c) (y := y) (z := z) hQ
  have hv : DifferentiableAt ℝ v y := by
    have hAff : DifferentiableAt ℝ (fun p => c + axisChart B (p, z)) y := by
      simp_rw [axisChart_eq_plane_add_axis]
      exact ((axisChartPlane B).differentiableAt.add_const _).const_add _
    exact hQ.comp y hAff
  have hFT : fderiv ℝ (fun p => (v p : Tensor)) y =
      symmetricTraceless.subtypeL.comp (L.comp (axisChartPlane B)) := by
    have hSub : HasFDerivAt (⇑symmetricTraceless.subtypeL) symmetricTraceless.subtypeL (v y) :=
      symmetricTraceless.subtypeL.hasFDerivAt
    exact (hSub.comp y (hV ▸ hv.hasFDerivAt)).fderiv
  let F := frobeniusCoordinateEquiv.toContinuousLinearMap.comp L
  have hBasis := sum_norm_sq_linear_basis_eq (L := F.toLinearMap)
    (EuclideanSpace.basisFun (Fin 3) ℝ) B
  have hFNorm (v : Point) : ‖F v‖ = ‖L v‖ := frobeniusCoordinateEquiv.norm_map (L v)
  have hNormEq : (∑ i : Fin 3, ‖L (axis i)‖ ^ 2) = ∑ i : Fin 3, ‖L (B i)‖ ^ 2 := by
    simpa only [ContinuousLinearMap.coe_coe, EuclideanSpace.basisFun_apply, axis, hFNorm] using hBasis
  have hDir : planarSmoothDirichletDensity v y ≤ (1 / 2 : ℝ) * gradientNormSq (ClassicalGradient Q x) := by
    unfold planarSmoothDirichletDensity
    rw [hFT, gradientNormSq_eq_sum_norm_sq]
    simp only [ContinuousLinearMap.comp_apply, axisChartPlane_single]
    change (1 / 2 : ℝ) * (∑ i : Fin 2, ‖L (B i.castSucc)‖ ^ 2) ≤
      (1 / 2 : ℝ) * (∑ i : Fin 3, ‖L (axis i)‖ ^ 2)
    rw [hNormEq, Fin.sum_univ_two, Fin.sum_univ_three]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have h0 : Fin.castSucc (0 : Fin 2) = (0 : Fin 3) := by decide
    have h1 : Fin.castSucc (1 : Fin 2) = (1 : Fin 3) := by decide
    rw [h0, h1]
    linarith only [sq_nonneg ‖L (B 2)‖]
  unfold planarSmoothEnergyDensity energyDensity
  change planarSmoothDirichletDensity v y + bulkPotential a (Q x) / (ε : ℝ) ^ 2 ≤
    (1 / 2 : ℝ) * gradientNormSq (ClassicalGradient Q x) + (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x)
  rw [inv_pow, div_eq_mul_inv, mul_comm (bulkPotential a (Q x))]
  exact add_le_add_left hDir _

/-- Angular and bulk energy on one actual lateral circle, multiplied by
its physical radius. -/
def cylinderLateralSliceCost (a : BulkCoefficients) (ε r : ℝ)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (Q : Point → S0) (z : ℝ) : ℝ :=
  let β (t : ℝ) := cylinderSliceMap B c Q z (r • (circleNativeParam (t - Real.pi)).val)
  (1 / 2 : ℝ) * (∫ t in Ioo 0 (2 * Real.pi), ‖deriv β t‖ ^ 2) +
    (r / ε) ^ 2 * ∫ t in Ioo 0 (2 * Real.pi), bulkPotential a (β t)

theorem continuousOn_classicalEnergyDensity {Ω : Set Point} (hΩ : IsOpen Ω)
    (a : BulkCoefficients) (ε : ElasticScale) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω) :
    ContinuousOn (fun x => energyDensity a ε (Q x) (ClassicalGradient Q x)) Ω := by
  have hD : ContinuousOn (fderiv ℝ Q) Ω := hQ.continuousOn_fderiv_of_isOpen hΩ (by simp)
  have hDir : ContinuousOn (fun x => gradientNormSq (ClassicalGradient Q x)) Ω := by
    simp_rw [gradientNormSq_eq_sum_norm_sq, ClassicalGradient, coordDeriv]
    exact continuousOn_finsetSum _ fun i _ => ((hD.clm_apply continuousOn_const).norm).pow 2
  unfold energyDensity
  exact (continuousOn_const.mul hDir).add (continuousOn_const.mul
    ((contDiff_bulkPotential a).continuous.comp_continuousOn hQ.continuousOn))

private theorem continuousOn_planarSmoothEnergyDensity
    (a : BulkCoefficients) (ε : ℝ) {U : Set Plane} (hU : IsOpen U)
    {v : Plane → S0} (hV : ContDiffOn ℝ ∞ v U) :
    ContinuousOn (planarSmoothEnergyDensity a ε v) U := by
  have hQT : ContDiffOn ℝ ∞ (fun y => (v y : Tensor)) U :=
    symmetricTraceless.subtypeL.contDiff.comp_contDiffOn hV
  have hDT : ContinuousOn (fun y => fderiv ℝ (fun y => (v y : Tensor)) y) U :=
    hQT.continuousOn_fderiv_of_isOpen hU (by simp)
  have hDir : ContinuousOn (planarSmoothDirichletDensity v) U := by
    unfold planarSmoothDirichletDensity
    exact continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
      ((hDT.clm_apply continuousOn_const).norm).pow 2)
  exact hDir.add (((contDiff_bulkPotential a).continuous.comp_continuousOn hV.continuousOn).div_const _)

theorem contDiff_axisChart_horizontal_affine (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (z : ℝ) : ContDiff ℝ ∞ (fun y => c + axisChart B (y, z)) := by
  simp_rw [axisChart_eq_plane_add_axis]
  exact contDiff_const.add ((axisChartPlane B).contDiff.add contDiff_const)

theorem planarSmoothEnergy_slice_le_volume_integral
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    {r z : ℝ} (hSub : ∀ y ∈ closedBall (0 : Plane) r, c + axisChart B (y, z) ∈ Ω) :
    planarSmoothEnergy a ε (cylinderSliceMap B c Q z) r ≤
      ∫ y in ball (0 : Plane) r, energyDensity a ε (Q (c + axisChart B (y, z)))
        (ClassicalGradient Q (c + axisChart B (y, z))) := by
  let T (y : Plane) := c + axisChart B (y, z)
  let U := T ⁻¹' Ω
  have hT : ContDiff ℝ ∞ T := contDiff_axisChart_horizontal_affine B c z
  have hU : IsOpen U := hΩ.preimage hT.continuous
  have hV : ContDiffOn ℝ ∞ (cylinderSliceMap B c Q z) U :=
    hQ.comp hT.contDiffOn (fun _ hy => hy)
  have hF : ContinuousOn (fun y => energyDensity a ε (Q (T y)) (ClassicalGradient Q (T y)))
      (closedBall (0 : Plane) r) :=
    (continuousOn_classicalEnergyDensity hΩ a ε hQ).comp hT.continuous.continuousOn hSub
  have hI : IntegrableOn (fun y => energyDensity a ε (Q (T y)) (ClassicalGradient Q (T y)))
      (ball (0 : Plane) r) :=
    (hF.integrableOn_compact (isCompact_closedBall (0 : Plane) r)).mono_set ball_subset_closedBall
  have hCts := (continuousOn_planarSmoothEnergyDensity a ε hU hV).mono hSub
  have hEclosed : IntegrableOn (planarSmoothEnergyDensity a ε (cylinderSliceMap B c Q z))
      (closedBall (0 : Plane) r) := hCts.integrableOn_compact (isCompact_closedBall (0 : Plane) r)
  have hE := hEclosed.mono_set (ball_subset_closedBall : ball (0 : Plane) r ⊆ closedBall 0 r)
  unfold planarSmoothEnergy
  apply setIntegral_mono_on hE hI measurableSet_ball
  intro y hy
  have hyΩ : T y ∈ Ω := hSub y (ball_subset_closedBall hy)
  have hQ₁ : ContDiffOn ℝ 1 Q Ω := hQ.of_le (by decide)
  have hD : ContDiffAt ℝ 1 Q (T y) := (hQ₁ _ hyΩ).contDiffAt (hΩ.mem_nhds hyΩ)
  exact planarSmoothEnergyDensity_slice_le a ε (hD.differentiableAt one_ne_zero)

/-- Integrating the physical planar lower bound gives the cylinder lower
energy. The same projected class and gap are used on its actual circles. -/
theorem exists_classical_cylinder_lower
    (hcoarea : External.PlanarScalarCoarea) (hAngular : External.PeriodicAngularSobolev)
    (a : BulkCoefficients) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
      {Ω : Set Point} (hΩ : IsOpen Ω) (Q : Point → S0) (hQ : ContDiffOn ℝ ∞ Q Ω)
      {r lo hi g : ℝ} (hr : 0 < r) (hHeight : lo < hi) (hg : 0 < g) (ε : ElasticScale)
      (hε : (ε : ℝ) < r / 80)
      (hCyl : translatedClosedAxisCylinder c (B 2) r lo hi ⊆ Ω)
      (hBound : ∀ x ∈ translatedClosedAxisCylinder c (B 2) r lo hi, ‖Q x‖ ≤ M)
      (hGap : ∀ z ∈ Ioo lo hi, ∀ w : NativeCircle,
        g ≤ normalizedSpectralGap a (cylinderSliceMap B c Q z (r • w.val)))
      (e : ℝ)
      (hClass : ∀ z ∈ Ioo lo hi, ∃ q : C(NativeCircle, vacuum a),
        nativeVacuumCircleCost a q = e ∧
          ∀ w, q w = spectralVacuumPoint a (cylinderSliceMap B c Q z (r • w.val)))
      (hLat : IntegrableOn (cylinderLateralSliceCost a ε r B c Q) (Ioo lo hi)),
      (hi - lo) * (e * g ^ 2 * Real.log (r / (ε : ℝ)) - C) ≤
        (∫ x in translatedAxisCylinder c (B 2) r lo hi, energyDensity a ε (Q x) (ClassicalGradient Q x)) +
          Real.log 80 * ∫ z in Ioo lo hi, cylinderLateralSliceCost a ε r B c Q z := by
  obtain ⟨C, hC, hDisk⟩ := exists_planarSmooth_boundary_gap_lower_radius hcoarea hAngular a M hM
  refine ⟨C, hC, ?_⟩
  intro B c Ω hΩ Q hQ r lo hi g hr hHeight hg ε hε hCyl hBound hGap e hClass hLat
  let K := translatedClosedAxisCylinder c (B 2) r lo hi
  let S := translatedAxisCylinder c (B 2) r lo hi
  let F (x : Point) := energyDensity a ε (Q x) (ClassicalGradient Q x)
  have hK : IsCompact K := isCompact_translatedClosedAxisCylinder (B.orthonormal.norm_eq_one 2) _ _ _
  have hF : ContinuousOn F Ω := continuousOn_classicalEnergyDensity hΩ a ε hQ
  have hKInt : IntegrableOn F K := (hF.mono hCyl).integrableOn_compact hK
  have hSInt : IntegrableOn F S := hKInt.mono_set (translatedAxisCylinder_subset_closed _ _ _ _ _)
  obtain ⟨hProd, hFub⟩ := integral_translatedAxisCylinder_eq_iterated B c r lo hi F hSInt
  let H (z : ℝ) := ∫ y in ball (0 : Plane) r, F (c + axisChart B (y, z))
  have hHInt : IntegrableOn H (Ioo lo hi) := hProd.integral_prod_right
  have hIn (z : ℝ) (hz : z ∈ Icc lo hi) (y : Plane) (hy : y ∈ closedBall 0 r) :
      c + axisChart B (y, z) ∈ K := by
    change c + axisChart B (y, z) - c ∈ closedAxisCylinder (B 2) r lo hi
    rw [add_sub_cancel_left]
    change cylinderTransverseRadius (B 2) (axisChart B (y, z)) ≤ r ∧
      lo ≤ cylinderHeight (B 2) (axisChart B (y, z)) ∧ cylinderHeight (B 2) (axisChart B (y, z)) ≤ hi
    rw [cylinderTransverseRadius_axisChart, cylinderHeight_axisChart]
    exact ⟨mem_closedBall_zero_iff.mp hy, hz.1, hz.2⟩
  have hPt (z : ℝ) (hz : z ∈ Ioo lo hi) :
      e * g ^ 2 * Real.log (r / (ε : ℝ)) - C ≤
        H z + Real.log 80 * cylinderLateralSliceCost a ε r B c Q z := by
    let T (y : Plane) := c + axisChart B (y, z)
    let U := T ⁻¹' Ω
    have hT : ContDiff ℝ ∞ T := contDiff_axisChart_horizontal_affine B c z
    have hU : IsOpen U := hΩ.preimage hT.continuous
    have hBU : closedBall (0 : Plane) r ⊆ U := fun y hy =>
      hCyl (hIn z (Ioo_subset_Icc_self hz) y hy)
    have hV : ContDiffOn ℝ ∞ (cylinderSliceMap B c Q z) U :=
      hQ.comp hT.contDiffOn (fun y hy => hy)
    obtain ⟨q, he, hq⟩ := hClass z hz
    have h := hDisk hr ε.property.1 hε hg _ U hU hBU hV
      (fun y hy => hBound _ (hIn z (Ioo_subset_Icc_self hz) y (ball_subset_closedBall hy)))
      (hGap z hz) q hq
    change nativeVacuumCircleCost a q * g ^ 2 * Real.log (r / (ε : ℝ)) - C ≤
      planarSmoothEnergy a ε (cylinderSliceMap B c Q z) r +
        Real.log 80 * cylinderLateralSliceCost a ε r B c Q z at h
    rw [he] at h
    apply h.trans
    apply add_le_add_left
    exact planarSmoothEnergy_slice_le_volume_integral B c a ε hΩ hQ hBU
  have hFinit : (volume : Measure ℝ) (Ioo lo hi) ≠ ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hIntConst : IntegrableOn (fun _ : ℝ => e * g ^ 2 * Real.log (r / (ε : ℝ)) - C) (Ioo lo hi) :=
    integrableOn_const hFinit
  have hI := setIntegral_mono_on hIntConst (hHInt.add (hLat.const_mul (Real.log 80))) measurableSet_Ioo
    (fun z hz => hPt z hz)
  rw [setIntegral_const, Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hHeight.le),
    smul_eq_mul] at hI
  change _ ≤ ∫ z in Ioo lo hi, H z + Real.log 80 * cylinderLateralSliceCost a ε r B c Q z at hI
  rw [integral_add hHInt (hLat.const_mul (Real.log 80)), integral_const_mul] at hI
  rw [hFub]
  exact hI

end Thesis.MeasureGeometry
