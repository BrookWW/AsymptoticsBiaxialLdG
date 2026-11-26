module

public import Thesis.Interpolation.VacuumDiskFill
import Thesis.Interpolation.AbsolutelyContinuousTest
import Thesis.Interpolation.QuaternionSphereSobolevLift
import StratificationTheory.Foundation.RadialL2Transfer
import StratificationTheory.Foundation.AngularL2Membership
import StratificationTheory.Foundation.PolarAETransport
import StratificationTheory.Foundation.SphereCircleWeakData
import StratificationTheory.Frozen.SphereGradientCharacterization
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.Prod

/-! Transfer of one periodic absolutely continuous angular graph to the native circle. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Topology

namespace Thesis

private abbrev angularPeriod : ℝ := 2 * Real.pi
private abbrev angularIntervalMeasure : Measure ℝ := volume.restrict (Ioo 0 angularPeriod)

private def periodicAngularParam (t : ℝ) : UnitBoundarySphere 2 := circleNativeParam (t - Real.pi)

private def periodicAngularRay (t : ℝ) : Domain 2 := (periodicAngularParam t).val

private def periodicAngularTangent (t : ℝ) : Domain 2 :=
  WithLp.toLp 2 ![-Real.sin (t - Real.pi), Real.cos (t - Real.pi)]

private theorem periodicAngularParam_zero_eq_period : periodicAngularParam 0 = periodicAngularParam angularPeriod := by
  unfold periodicAngularParam angularPeriod
  rw [zero_sub, show 2 * Real.pi - Real.pi = Real.pi by ring, circleNativeParam_neg_pi]

private theorem periodicAngularParam_measurePreserving :
    MeasurePreserving periodicAngularParam angularIntervalMeasure (unitBoundarySurface 2) := by
  have hShift := (measurePreserving_add_right (volume : Measure ℝ) (-Real.pi)).restrict_preimage
    (measurableSet_Ioo (a := -Real.pi) (b := Real.pi))
  have hPre : (fun t : ℝ => t + -Real.pi) ⁻¹' Ioo (-Real.pi) Real.pi = Ioo 0 angularPeriod := by
    ext t
    change -Real.pi < t + -Real.pi ∧ t + -Real.pi < Real.pi ↔ 0 < t ∧ t < 2 * Real.pi
    constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
  rw [hPre] at hShift
  have hParam : MeasurePreserving circleNativeParam (volume.restrict (Ioo (-Real.pi) Real.pi))
      (unitBoundarySurface 2) := ⟨continuous_circleNativeParam.measurable, map_circleNativeParam_Ioo_eq_native⟩
  rw [show periodicAngularParam = circleNativeParam ∘ (fun t : ℝ => t + -Real.pi) by
    funext t; exact congrArg circleNativeParam (sub_eq_add_neg t Real.pi)]
  exact hParam.comp hShift

private def periodicAngularArg (θ : UnitBoundarySphere 2) : ℝ :=
  (Complex.orthonormalBasisOneI.repr.symm θ.val).arg + Real.pi

private theorem measurable_periodicAngularArg : Measurable periodicAngularArg :=
  (Complex.measurable_arg.comp (Complex.orthonormalBasisOneI.repr.symm.continuous.measurable.comp
    measurable_subtype_coe)).add_const _

private theorem circleNativeParam_eq_complex (t : ℝ) : (circleNativeParam t).val =
    Complex.orthonormalBasisOneI.repr ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) := by
  ext i
  fin_cases i <;> simp [circleNativeParam_coe, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

private theorem periodicAngularArg_param {t : ℝ} (ht : t ∈ Ioo 0 angularPeriod) :
    periodicAngularArg (periodicAngularParam t) = t := by
  have ht' : t - Real.pi ∈ Ioc (-Real.pi) Real.pi := by
    have ht₂ := ht.2
    change t < 2 * Real.pi at ht₂
    exact ⟨by linarith only [ht.1], by linarith only [ht₂]⟩
  unfold periodicAngularArg periodicAngularParam
  rw [circleNativeParam_eq_complex, LinearIsometryEquiv.symm_apply_apply, Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.arg_cos_add_sin_mul_I ht', sub_add_cancel]

private theorem periodicAngularArg_measurePreserving :
    MeasurePreserving periodicAngularArg (unitBoundarySurface 2) angularIntervalMeasure := by
  refine ⟨measurable_periodicAngularArg, ?_⟩
  rw [← periodicAngularParam_measurePreserving.map_eq, Measure.map_map measurable_periodicAngularArg
    periodicAngularParam_measurePreserving.measurable]
  have h : periodicAngularArg ∘ periodicAngularParam =ᵐ[angularIntervalMeasure] id := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with t ht
    exact periodicAngularArg_param ht
  rw [Measure.map_congr h, Measure.map_id]

private theorem hasDerivAt_periodicAngularRay (t : ℝ) :
    HasDerivAt periodicAngularRay (periodicAngularTangent t) t := by
  have h := (hasDerivAt_circleNativeParam_val (t - Real.pi)).scomp t
    ((hasDerivAt_id t).sub_const Real.pi)
  change HasDerivAt (fun s : ℝ => (circleNativeParam (s - Real.pi)).val)
    (WithLp.toLp 2 ![-Real.sin (t - Real.pi), Real.cos (t - Real.pi)] : Domain 2) t
  simpa only [Function.comp_def, id_eq, one_smul] using h

private theorem periodicAngular_integral_parts {q : ℕ} {f : ℝ → Ambient q}
    (hf : AbsolutelyContinuousOnInterval f 0 angularPeriod) (hfEnd : f 0 = f angularPeriod)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψEnd : ψ 0 = ψ angularPeriod) :
    let B : ℝ → Ambient q := fun t => deriv ψ t • f t + ψ t • deriv f t
    Integrable B angularIntervalMeasure ∧ (∫ t, B t ∂angularIntervalMeasure) = 0 :=
  absolutelyContinuous_integral_parts Real.two_pi_pos hf hψ (by rw [hfEnd, hψEnd])

private abbrev angularCollarRadii := Ioo (1 / 2 : ℝ) (3 / 2)

private def angularCollar : OpenDomain 2 :=
  ⟨(fun x : Domain 2 => ‖x‖) ⁻¹' angularCollarRadii, isOpen_Ioo.preimage continuous_norm⟩

private theorem periodicAngular_polar_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {F : Domain 2 → E}
    (hF : IntegrableOn F angularCollar.val) :
    (∫ x in angularCollar.val, F x) =
      ∫ r in angularCollarRadii, r • ∫ t in Ioo (0 : ℝ) angularPeriod, F (r • periodicAngularRay t) := by
  let X := ({(0 : Domain 2)}ᶜ : Set (Domain 2))
  let P := Ioi (0 : ℝ)
  let J := (Subtype.val : P → ℝ) ⁻¹' angularCollarRadii
  let η := (Measure.volumeIoiPow 1).restrict J
  let σ := unitBoundarySurface 2
  let H := homeomorphUnitSphereProd (Domain 2)
  letI : IsFiniteMeasure angularIntervalMeasure := isFiniteMeasure_restrict.mpr
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  letI : IsFiniteMeasure η := by
    constructor
    rw [Measure.restrict_apply_univ]
    have hJ : J ⊆ Iio (⟨2, (show (0 : ℝ) < 2 by norm_num)⟩ : P) := by
      intro r hr
      change (r : ℝ) < 2
      exact hr.2.trans (by norm_num)
    refine (measure_mono hJ).trans_lt ?_
    rw [Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_lt_top
  have hσ : σ = (volume : Measure (Domain 2)).toSphere :=
    euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)
  letI : IsFiniteMeasure σ := by rw [hσ]; infer_instance
  have hJ : MeasurableSet J := measurableSet_Ioo.preimage measurable_subtype_coe
  have hpre : H ⁻¹' (univ ×ˢ J) = (Subtype.val : X → Domain 2) ⁻¹' angularCollar.val := by
    ext x
    simp only [mem_preimage, mem_prod, mem_univ, true_and, J, angularCollar]
    change (H x).2.val ∈ angularCollarRadii ↔ ‖x.val‖ ∈ angularCollarRadii
    rw [homeomorphUnitSphereProd_apply_snd_coe]
  have hm := (volume : Measure (Domain 2)).measurePreserving_homeomorphUnitSphereProd
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] at hm
  have hM := hm.restrict_preimage (MeasurableSet.univ.prod hJ)
  rw [show (homeomorphUnitSphereProd (Domain 2)) ⁻¹' (univ ×ˢ J) =
    (Subtype.val : X → Domain 2) ⁻¹' angularCollar.val from hpre, ← Measure.prod_restrict,
    Measure.restrict_univ, ← hσ] at hM
  have hc := (measurePreserving_subtype_coe
    ((measurableSet_singleton (0 : Domain 2)).compl) (μa := volume)).restrict_preimage
      angularCollar.property.measurableSet
  rw [restrict_compl_singleton] at hc
  let H₀ (p : UnitBoundarySphere 2 × P) := F (p.2.val • p.1.val)
  have hEq : F ∘ (Subtype.val : X → Domain 2) = H₀ ∘ H := by
    funext x
    have h := congrArg (fun y : X => y.val) (H.symm_apply_apply x)
    have hRay : (H x).2.val • (H x).1.val = x.val := by
      simpa only [H, homeomorphUnitSphereProd_symm_apply_coe] using h
    exact congrArg F hRay.symm
  have hH₀ : Integrable H₀ (σ.prod η) := by
    have hFX := hc.integrable_comp_of_integrable hF
    rw [hEq] at hFX
    exact (hM.integrable_comp_emb (Homeomorph.measurableEmbedding _) (g := H₀)).mp hFX
  let Φ : ℝ × P → UnitBoundarySphere 2 × P := Prod.map periodicAngularParam id
  have hPhi : MeasurePreserving Φ (angularIntervalMeasure.prod η) (σ.prod η) := by
    refine ⟨periodicAngularParam_measurePreserving.measurable.prodMap measurable_id, ?_⟩
    change Measure.map (Prod.map periodicAngularParam id) (angularIntervalMeasure.prod η) = σ.prod η
    rw [← Measure.map_prod_map _ _ periodicAngularParam_measurePreserving.measurable measurable_id,
      periodicAngularParam_measurePreserving.map_eq, Measure.map_id]
  let A (r : ℝ) := ∫ t, F (r • periodicAngularRay t) ∂angularIntervalMeasure
  calc
    _ = ∫ x : X, F x.val ∂((volume : Measure (Domain 2)).comap (Subtype.val : X → Domain 2) |>.restrict
          ((Subtype.val : X → Domain 2) ⁻¹' angularCollar.val)) :=
      (hc.integral_comp (MeasurableEmbedding.subtype_coe
        ((measurableSet_singleton (0 : Domain 2)).compl)) F).symm
    _ = ∫ p, H₀ p ∂σ.prod η := by
      change (∫ x, (F ∘ (Subtype.val : X → Domain 2)) x ∂_) = _
      rw [hEq]
      exact hM.integral_comp (Homeomorph.measurableEmbedding _) H₀
    _ = ∫ p, (H₀ ∘ Φ) p ∂angularIntervalMeasure.prod η := by
      rw [← hPhi.map_eq]
      exact integral_map hPhi.aemeasurable (hPhi.map_eq.symm ▸ hH₀.aestronglyMeasurable)
    _ = ∫ r : P, A r.val ∂η := integral_prod_symm _ (hPhi.integrable_comp_of_integrable hH₀)
    _ = _ := by
      change (∫ r : P in J, A r.val ∂Measure.volumeIoiPow 1) = ∫ r in angularCollarRadii, r • A r
      rw [Measure.volumeIoiPow,
        setIntegral_withDensity_eq_setIntegral_toReal_smul (by fun_prop)
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ hJ]
      have hJac (r : P) : (ENNReal.ofReal (r.val ^ (1 : ℕ))).toReal = r.val := by
        rw [pow_one, ENNReal.toReal_ofReal r.property.le]
      simp_rw [hJac]
      rw [← (MeasurableEmbedding.subtype_coe measurableSet_Ioi).setIntegral_map
        (fun r : ℝ => r • A r) angularCollarRadii,
        (MeasurableEmbedding.subtype_coe measurableSet_Ioi).map_comap, Subtype.range_val,
        Measure.restrict_restrict_of_subset (show angularCollarRadii ⊆ Ioi 0 from
          fun r hr => (by norm_num : (0 : ℝ) < 1 / 2).trans hr.1)]

private theorem norm_periodicAngularRay (t : ℝ) : ‖periodicAngularRay t‖ = 1 :=
  mem_sphere_zero_iff_norm.mp (periodicAngularParam t).property

private theorem periodicAngularRay_contDiff : ContDiff ℝ ∞ periodicAngularRay := by
  change ContDiff ℝ ∞ (fun t => (circleNativeParam (t - Real.pi)).val)
  exact contDiff_circleNativeParam_val.comp (contDiff_id.sub contDiff_const)

private theorem periodicAngularTangent_eq_quarter_turn (t : ℝ) :
    periodicAngularTangent t = WithLp.toLp 2 ![-(periodicAngularRay t) 1, (periodicAngularRay t) 0] := by
  ext i
  fin_cases i <;> simp [periodicAngularTangent, periodicAngularRay, periodicAngularParam, circleNativeParam_coe]

private theorem periodicAngularTangent_zero_eq_period : periodicAngularTangent 0 =
    periodicAngularTangent angularPeriod := by
  rw [periodicAngularTangent_eq_quarter_turn, periodicAngularTangent_eq_quarter_turn]
  unfold periodicAngularRay
  rw [periodicAngularParam_zero_eq_period]

private theorem periodicAngularTangent_coord_contDiff (i : Fin 2) :
    ContDiff ℝ ∞ (fun t => periodicAngularTangent t i) := by
  fin_cases i
  · change ContDiff ℝ ∞ (fun t => -Real.sin (t - Real.pi))
    exact (Real.contDiff_sin.comp (contDiff_id.sub contDiff_const)).neg
  · change ContDiff ℝ ∞ (fun t => Real.cos (t - Real.pi))
    exact Real.contDiff_cos.comp (contDiff_id.sub contDiff_const)

private theorem hasDerivAt_periodicAngularTangent_coord (i : Fin 2) (t : ℝ) :
    HasDerivAt (fun s => periodicAngularTangent s i) (-(periodicAngularRay t) i) t := by
  have hArg := (hasDerivAt_id t).sub_const Real.pi
  fin_cases i
  · change HasDerivAt (fun s => -Real.sin (s - Real.pi)) (-(periodicAngularRay t) 0) t
    have h : HasDerivAt (fun s => Real.sin (s - Real.pi)) (Real.cos (t - Real.pi)) t := by
      have h' := (Real.hasDerivAt_sin (t - Real.pi)).scomp t hArg
      simpa only [Function.comp_def, id_eq, one_smul] using h'
    rw [show (periodicAngularRay t) 0 = Real.cos (t - Real.pi) by
      simp only [periodicAngularRay, periodicAngularParam, circleNativeParam_coe, PiLp.toLp_apply,
        Matrix.cons_val_zero]]
    exact h.neg
  · change HasDerivAt (fun s => Real.cos (s - Real.pi)) (-(periodicAngularRay t) 1) t
    have h := (Real.hasDerivAt_cos (t - Real.pi)).scomp t hArg
    have hCoord : (periodicAngularRay t) 1 = Real.sin (t - Real.pi) := by
      simp only [periodicAngularRay, periodicAngularParam, circleNativeParam_coe, PiLp.toLp_apply,
        Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hCoord]
    simpa only [Function.comp_def, id_eq, one_smul] using h

private theorem coord_single_eq_periodic_frame (i : Fin 2) (t : ℝ) :
    EuclideanSpace.single i (1 : ℝ) =
      (periodicAngularRay t i) • periodicAngularRay t +
        (periodicAngularTangent t i) • periodicAngularTangent t := by
  have h := Real.sin_sq_add_cos_sq t
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [periodicAngularRay, periodicAngularParam, periodicAngularTangent, circleNativeParam_coe,
      EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    nlinarith only [h]

private theorem hasDerivAt_radial_test {φ : Domain 2 → ℝ} (hφ : ContDiff ℝ ∞ φ) (r t : ℝ) :
    HasDerivAt (fun s : ℝ => s * φ (s • periodicAngularRay t))
      (φ (r • periodicAngularRay t) +
        r * fderiv ℝ φ (r • periodicAngularRay t) (periodicAngularRay t)) r := by
  have hRay : HasDerivAt (fun s : ℝ => s • periodicAngularRay t) (periodicAngularRay t) r := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id r).smul_const (periodicAngularRay t)
  have h : HasDerivAt (fun s => φ (s • periodicAngularRay t))
      (fderiv ℝ φ (r • periodicAngularRay t) (periodicAngularRay t)) r :=
    (hφ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r hRay
  have hProd := (hasDerivAt_id r).mul h
  rw [show φ (r • periodicAngularRay t) + r * fderiv ℝ φ (r • periodicAngularRay t) (periodicAngularRay t) =
    1 * φ (r • periodicAngularRay t) + r * fderiv ℝ φ (r • periodicAngularRay t) (periodicAngularRay t) by simp]
  exact hProd

private theorem hasDerivAt_angular_test {φ : Domain 2 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (i : Fin 2) (r t : ℝ) :
    HasDerivAt (fun s => periodicAngularTangent s i * φ (r • periodicAngularRay s))
      (-(periodicAngularRay t i) * φ (r • periodicAngularRay t) +
        periodicAngularTangent t i * (r * fderiv ℝ φ (r • periodicAngularRay t) (periodicAngularTangent t))) t := by
  have hRay := (hasDerivAt_periodicAngularRay t).const_smul r
  have h0 : HasDerivAt (fun s => φ (r • periodicAngularRay s))
      (fderiv ℝ φ (r • periodicAngularRay t) (r • periodicAngularTangent t)) t :=
    (hφ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hRay
  rw [map_smul, smul_eq_mul] at h0
  exact (hasDerivAt_periodicAngularTangent_coord i t).mul h0

private theorem angular_polar_test_derivative {φ : Domain 2 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (i : Fin 2) (r t : ℝ) :
    r * coordinateDerivative φ hφ i (r • periodicAngularRay t) =
      periodicAngularRay t i * deriv (fun s : ℝ => s * φ (s • periodicAngularRay t)) r +
        deriv (fun s => periodicAngularTangent s i * φ (r • periodicAngularRay s)) t := by
  rw [(hasDerivAt_radial_test hφ r t).deriv, (hasDerivAt_angular_test hφ i r t).deriv]
  unfold coordinateDerivative
  rw [coord_single_eq_periodic_frame i t, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

private theorem angularCollar_subset_ball : angularCollar.val ⊆ ball (0 : Domain 2) 2 := by
  intro x hx
  exact mem_ball_zero_iff.2 (hx.2.trans (by norm_num))

private def periodicAngularRadialTerm {q : ℕ} (v : C(UnitBoundarySphere 2, Ambient q))
    (φ : Domain 2 → ℝ) (i : Fin 2) (r t : ℝ) : Ambient q :=
  (periodicAngularRay t i * (φ (r • periodicAngularRay t) +
    r * fderiv ℝ φ (r • periodicAngularRay t) (periodicAngularRay t))) • v (periodicAngularParam t)

private theorem continuous_periodicAngularRadialTerm {q : ℕ} (v : C(UnitBoundarySphere 2, Ambient q))
    {φ : Domain 2 → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : Fin 2) :
    Continuous (Function.uncurry (periodicAngularRadialTerm v φ i)) := by
  let V (t : ℝ) := v (periodicAngularParam t)
  have hV : Continuous V := v.continuous.comp
    (continuous_circleNativeParam.comp (continuous_id.sub continuous_const))
  have hRay := periodicAngularRay_contDiff.continuous
  have hRayCoord : Continuous (fun t => periodicAngularRay t i) :=
    (PiLp.continuous_apply 2 _ i).comp hRay
  have hφDeriv := hφ.continuous_fderiv (by simp)
  change Continuous (fun p : ℝ × ℝ =>
    (periodicAngularRay p.2 i * (φ (p.1 • periodicAngularRay p.2) +
      p.1 * fderiv ℝ φ (p.1 • periodicAngularRay p.2) (periodicAngularRay p.2))) • V p.2)
  fun_prop

private theorem integral_periodicAngular_weak_test {q : ℕ}
    (v : C(UnitBoundarySphere 2, Ambient q)) (f : ℝ → Ambient q)
    (hf : AbsolutelyContinuousOnInterval f 0 angularPeriod)
    (hParam : EqOn f (fun t => v (periodicAngularParam t)) (Icc 0 angularPeriod))
    {φ : Domain 2 → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : Fin 2) {r : ℝ} (hr : 0 < r) :
    (∫ t, r • (coordinateDerivative φ hφ i (r • periodicAngularRay t) • f t +
      φ (r • periodicAngularRay t) • ((r⁻¹ * periodicAngularTangent t i) • deriv f t))
        ∂angularIntervalMeasure) = ∫ t, periodicAngularRadialTerm v φ i r t ∂angularIntervalMeasure := by
  let A := periodicAngularRadialTerm v φ i
  let ψ (t : ℝ) : ℝ := periodicAngularTangent t i * φ (r • periodicAngularRay t)
  have hψSmooth : ContDiff ℝ ∞ ψ := (periodicAngularTangent_coord_contDiff i).mul
    (hφ.comp (periodicAngularRay_contDiff.const_smul r))
  have hFEnd : f 0 = f angularPeriod := by
    rw [hParam (left_mem_Icc.mpr Real.two_pi_pos.le), hParam (right_mem_Icc.mpr Real.two_pi_pos.le)]
    exact congrArg v periodicAngularParam_zero_eq_period
  have hψEnd : ψ 0 = ψ angularPeriod := by
    dsimp only [ψ]
    rw [periodicAngularTangent_zero_eq_period]
    unfold periodicAngularRay
    rw [periodicAngularParam_zero_eq_period]
  obtain ⟨hI, hZero⟩ := periodicAngular_integral_parts hf hFEnd (hψSmooth.of_le (by simp)) hψEnd
  have hTerm (t : ℝ) (ht : t ∈ Ioo 0 angularPeriod) :
      r • (coordinateDerivative φ hφ i (r • periodicAngularRay t) • f t +
        φ (r • periodicAngularRay t) • ((r⁻¹ * periodicAngularTangent t i) • deriv f t)) =
        A r t + (deriv ψ t • f t + ψ t • deriv f t) := by
    rw [smul_add, smul_smul, smul_smul, smul_smul]
    have hScale : (r * φ (r • periodicAngularRay t)) * (r⁻¹ * periodicAngularTangent t i) = ψ t := by
      dsimp only [ψ]
      field_simp [hr.ne']
    rw [hScale, angular_polar_test_derivative hφ i r t, add_smul]
    change (_ • f t + deriv ψ t • f t) + ψ t • deriv f t = _
    have hA : A r t = (periodicAngularRay t i *
        deriv (fun s : ℝ => s * φ (s • periodicAngularRay t)) r) • f t := by
      rw [(hasDerivAt_radial_test hφ r t).deriv]
      exact congrArg (fun z : Ambient q => _ • z) (hParam (Ioo_subset_Icc_self ht)).symm
    rw [hA, add_assoc]
  have hAInt : Integrable (A r) angularIntervalMeasure := by
    have hEmb : Continuous (fun t : ℝ => (r, t)) := continuous_const.prodMk continuous_id
    have hC : Continuous (A r) := by
      change Continuous (Function.uncurry (periodicAngularRadialTerm v φ i) ∘ fun t : ℝ => (r, t))
      exact (continuous_periodicAngularRadialTerm v hφ i).comp hEmb
    exact (hC.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  change (∫ t in Ioo 0 angularPeriod, _) = _
  calc
    _ = ∫ t in Ioo (0 : ℝ) angularPeriod, A r t + (deriv ψ t • f t + ψ t • deriv f t) :=
      setIntegral_congr_fun measurableSet_Ioo hTerm
    _ = (∫ t, A r t ∂angularIntervalMeasure) +
        ∫ t, deriv ψ t • f t + ψ t • deriv f t ∂angularIntervalMeasure := integral_add hAInt hI
    _ = _ := by rw [hZero, add_zero]

private theorem integral_periodicAngular_radial_test {q : ℕ}
    (v : C(UnitBoundarySphere 2, Ambient q)) {φ : Domain 2 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφSupport : tsupport φ ⊆ angularCollar.val) (i : Fin 2) :
    (∫ r in angularCollarRadii, ∫ t in Ioo (0 : ℝ) angularPeriod, periodicAngularRadialTerm v φ i r t) = 0 := by
  let A := periodicAngularRadialTerm v φ i
  let ν := (volume : Measure ℝ).restrict angularCollarRadii
  have hAInt : Integrable (Function.uncurry A) (ν.prod angularIntervalMeasure) := by
    change Integrable (Function.uncurry A)
      ((volume.restrict angularCollarRadii).prod (volume.restrict (Ioo 0 angularPeriod)))
    rw [Measure.prod_restrict]
    exact ((continuous_periodicAngularRadialTerm v hφ i).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  change (∫ r, ∫ t, A r t ∂angularIntervalMeasure ∂ν) = 0
  rw [integral_integral_swap hAInt]
  have hRadial (t : ℝ) : (∫ r in angularCollarRadii, A r t) = 0 := by
    let b (s : ℝ) := s * φ (s • periodicAngularRay t)
    have hb : ContDiff ℝ ∞ b := by dsimp only [b]; fun_prop
    have hCoeff : (fun r => A r t) = fun r =>
        deriv b r • (periodicAngularRay t i • v (periodicAngularParam t)) := by
      funext r
      have hbDeriv : deriv b r = φ (r • periodicAngularRay t) +
          r * fderiv ℝ φ (r • periodicAngularRay t) (periodicAngularRay t) :=
        (hasDerivAt_radial_test hφ r t).deriv
      rw [smul_smul, hbDeriv, mul_comm]
      rfl
    have hEndpoints : b (1 / 2) = 0 ∧ b (3 / 2) = 0 := by
      have hZero (s : ℝ) (hs : 0 ≤ s) (hn : s ∉ angularCollarRadii) : b s = 0 := by
        have hOut : s • periodicAngularRay t ∉ angularCollar.val := by
          change ‖s • periodicAngularRay t‖ ∉ angularCollarRadii
          simpa only [norm_smul, Real.norm_of_nonneg hs, norm_periodicAngularRay, mul_one] using hn
        exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport fun h => hOut (hφSupport h))
      exact ⟨hZero _ (by norm_num) (fun h => lt_irrefl _ h.1),
        hZero _ (by norm_num) (fun h => lt_irrefl _ h.2)⟩
    rw [hCoeff, integral_smul_const, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2),
      intervalIntegral.integral_deriv_eq_sub (fun r _ => hb.differentiable (by simp) r)
        ((hb.continuous_deriv (by simp)).intervalIntegrable _ _),
      hEndpoints.1, hEndpoints.2, sub_self, zero_smul]
  have hZero : (fun t => ∫ r, A r t ∂ν) = fun _ => (0 : Ambient q) := funext hRadial
  rw [hZero, integral_zero]

private theorem hasWeakGradient_periodicAngularExtension {q : ℕ}
    (v : C(UnitBoundarySphere 2, Ambient q)) (f : ℝ → Ambient q)
    (hf : AbsolutelyContinuousOnInterval f 0 angularPeriod)
    (hParam : EqOn f (fun t => v (periodicAngularParam t)) (Icc 0 angularPeriod))
    {w : Domain 2 → Ambient q} {D : Domain 2 → HarmonicMaps.Gradient 2 q}
    (hw : MemLp w 2 (volume.restrict angularCollar.val))
    (hD : ∀ i, MemLp (fun x => D x i) 2 (volume.restrict angularCollar.val))
    (hWray : ∀ r ∈ angularCollarRadii, ∀ t ∈ Ioo 0 angularPeriod, w (r • periodicAngularRay t) = f t)
    (hDray : ∀ r ∈ angularCollarRadii, ∀ t ∈ Ioo 0 angularPeriod, ∀ i,
      D (r • periodicAngularRay t) i = (r⁻¹ * periodicAngularTangent t i) • deriv f t) :
    HasWeakGradient angularCollar w D := by
  letI : IsFiniteMeasure (volume.restrict angularCollar.val) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono angularCollar_subset_ball))
  have hWI : IntegrableOn w angularCollar.val := hw.integrable (by norm_num)
  have hDI (i : Fin 2) : IntegrableOn (fun x => D x i) angularCollar.val := (hD i).integrable (by norm_num)
  refine ⟨hWI.locallyIntegrableOn, fun i => (hDI i).locallyIntegrableOn, ?_⟩
  intro i φ hφ hφCompact hφSupport
  let F (x : Domain 2) := coordinateDerivative φ hφ i x • w x + φ x • D x i
  have hφ₀ := hφ.continuous.memLp_top_of_hasCompactSupport hφCompact (volume.restrict angularCollar.val)
  have hφ₁Cont : Continuous (coordinateDerivative φ hφ i) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ₁ := hφ₁Cont.memLp_top_of_hasCompactSupport
    (hφCompact.fderiv_apply ℝ (EuclideanSpace.single i 1)) (volume.restrict angularCollar.val)
  have hF₀ : IntegrableOn (fun x => coordinateDerivative φ hφ i x • w x) angularCollar.val :=
    hWI.smul_of_top_right hφ₁
  have hF₁ : IntegrableOn (fun x => φ x • D x i) angularCollar.val := (hDI i).smul_of_top_right hφ₀
  have hF : IntegrableOn F angularCollar.val := hF₀.add hF₁
  apply eq_neg_of_add_eq_zero_left
  rw [← integral_add hF₀ hF₁]
  change (∫ x in angularCollar.val, F x) = 0
  rw [periodicAngular_polar_integral hF]
  have hAngular (r : ℝ) (hr : r ∈ angularCollarRadii) :
      r • (∫ t in Ioo (0 : ℝ) angularPeriod, F (r • periodicAngularRay t)) =
        ∫ t in Ioo (0 : ℝ) angularPeriod, periodicAngularRadialTerm v φ i r t := by
    have hr₀ : 0 < r := (by norm_num : (0 : ℝ) < 1 / 2).trans hr.1
    rw [← integral_smul]
    refine (setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)).trans
      (integral_periodicAngular_weak_test v f hf hParam hφ i hr₀)
    simp only [F, hWray r hr t ht, hDray r hr t ht i]
  rw [setIntegral_congr_fun measurableSet_Ioo hAngular]
  exact integral_periodicAngular_radial_test v hφ hφSupport i

private theorem angularCollar_contains_unitSphere : sphere (0 : Domain 2) 1 ⊆ angularCollar.val := by
  intro x hx
  change ‖x‖ ∈ angularCollarRadii
  rw [mem_sphere_zero_iff_norm.mp hx]
  norm_num

private theorem zero_notMem_angularCollar : (0 : Domain 2) ∉ angularCollar.val := by
  change ‖(0 : Domain 2)‖ ∉ angularCollarRadii
  norm_num

private theorem sphereGradient_of_angularCollar {q : ℕ}
    {v : UnitBoundarySphere 2 → Ambient q} (hv : MemSphereW12 (le_refl 2) v)
    {w : Domain 2 → Ambient q} {D : Domain 2 → HarmonicMaps.Gradient 2 q}
    {G : UnitBoundarySphere 2 → HarmonicMaps.Gradient 2 q} (hw : MemW12 angularCollar w D)
    (hWray : ∀ (ρ : PositiveRadius) (θ : UnitBoundarySphere 2), w (ρ.val • θ.val) = v θ)
    (hDray : ∀ (ρ : PositiveRadius) (θ : UnitBoundarySphere 2) (i : Fin 2),
      D (ρ.val • θ.val) i = ρ.val⁻¹ • G θ i) :
    (fun θ => fun i => (sphereGradient (le_refl 2) v hv i) θ) =ᵐ[unitBoundarySurface 2] G := by
  let P (x : Domain 2) : Prop := ∀ hx : x ≠ 0, ∀ i : Fin 2,
    D x i = ‖x‖⁻¹ • (sphereGradient (le_refl 2) v hv i) ((homeomorphUnitSphereProd (Domain 2) ⟨x, hx⟩).1)
  have hP : ∀ᵐ x ∂volume.restrict angularCollar.val, P x :=
    (sphereGradient_characterization (le_refl 2) v hv).1.2.2 angularCollar angularCollar_contains_unitSphere
      zero_notMem_angularCollar w D hw (fun ρ θ _ => hWray ρ θ)
  have hRays := ae_polar_slice_of_ae_volume ((ae_restrict_iff' angularCollar.property.measurableSet).mp hP)
    (0 : Domain 2)
  have hσ : unitBoundarySurface 2 = (volume : Measure (Domain 2)).toSphere :=
    euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)
  rw [← hσ] at hRays
  have hRays' : ∀ᵐ r ∂volume.restrict angularCollarRadii, ∀ᵐ θ ∂unitBoundarySurface 2,
      r • θ.val ∈ angularCollar.val → P (r • θ.val) := by
    have hSub : angularCollarRadii ⊆ Ioi (0 : ℝ) := fun _ h => (by norm_num : (0 : ℝ) < 1 / 2).trans h.1
    simpa only [zero_add] using hRays.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))
  have hMass : (volume : Measure ℝ) angularCollarRadii ≠ 0 := by rw [Real.volume_Ioo]; norm_num
  obtain ⟨r, hr, hAt⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hMass hRays'
  have hr₀ := (by norm_num : (0 : ℝ) < 1 / 2).trans hr.1
  filter_upwards [hAt] with θ hθ
  have hNorm : ‖r • θ.val‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr₀.le, mem_sphere_zero_iff_norm.mp θ.property, mul_one]
  have hNZ : r • θ.val ≠ 0 := norm_pos_iff.mp (hNorm.symm ▸ hr₀)
  have hMem : r • θ.val ∈ angularCollar.val := by
    change ‖r • θ.val‖ ∈ angularCollarRadii
    rwa [hNorm]
  let H := homeomorphUnitSphereProd (Domain 2)
  have hDirection : (H ⟨r • θ.val, hNZ⟩).1 = θ := by
    have hX : H.symm (θ, ⟨r, hr₀⟩) = ⟨r • θ.val, hNZ⟩ := by
      apply Subtype.ext
      change ((homeomorphUnitSphereProd (Domain 2)).symm
        (θ, (⟨r, hr₀⟩ : Ioi (0 : ℝ)))).val = r • θ.val
      rw [homeomorphUnitSphereProd_symm_apply_coe]
    rw [← hX, H.apply_symm_apply]
  funext i
  have h := hθ hMem hNZ i
  change D (r • θ.val) i = ‖r • θ.val‖⁻¹ • (sphereGradient (le_refl 2) v hv i) (H ⟨r • θ.val, hNZ⟩).1 at h
  have hL : D (r • θ.val) i = r⁻¹ • G θ i := hDray ⟨r, hr₀⟩ θ i
  rw [hL, hNorm, hDirection] at h
  have hScaled := congrArg (fun z : Ambient q => r • z) h.symm
  simpa only [smul_smul, mul_inv_cancel₀ hr₀.ne', one_smul] using hScaled

private theorem hsNormSq_periodicAngularTangent_smul {q : ℕ} (t : ℝ) (z : Ambient q) :
    hsNormSq (fun i => periodicAngularTangent t i • z) = ‖z‖ ^ 2 := by
  have h := Real.sin_sq_add_cos_sq t
  simp [hsNormSq, Fin.sum_univ_two, periodicAngularTangent, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    ← add_mul, h]

/-- A periodic absolutely continuous angular graph defines the actual native
Sobolev circle, with its original unhalved angular derivative energy. -/
theorem periodicAngularSobolev : External.PeriodicAngularSobolev := by
  intro q v f hParam hAC hf
  let σ := unitBoundarySurface 2
  have hσ : σ = (volume : Measure (Domain 2)).toSphere :=
    euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)
  letI : IsFiniteMeasure σ := by rw [hσ]; infer_instance
  letI : CompactSpace (UnitBoundarySphere 2) := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hv : MemLp (⇑v) 2 σ := v.continuous.memLp_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  let G (θ : UnitBoundarySphere 2) (i : Fin 2) : Ambient q :=
    periodicAngularTangent (periodicAngularArg θ) i • deriv f (periodicAngularArg θ)
  have hd : MemLp (deriv f ∘ periodicAngularArg) 2 σ :=
    hf.comp_measurePreserving periodicAngularArg_measurePreserving
  have hG (i : Fin 2) : MemLp (fun θ => G θ i) 2 σ := by
    have hT : MemLp (fun θ : UnitBoundarySphere 2 => periodicAngularTangent (periodicAngularArg θ) i) ∞ σ := by
      apply memLp_top_of_bound
        (((periodicAngularTangent_coord_contDiff i).continuous.measurable.comp
          measurable_periodicAngularArg).aestronglyMeasurable) 1
      exact ae_of_all _ fun θ => by
        fin_cases i <;> simp [periodicAngularTangent, Real.abs_sin_le_one, Real.abs_cos_le_one]
    exact hd.smul (r := 2) hT
  let dir := sphereRadialDirection (periodicAngularParam 0)
  let w : Domain 2 → Ambient q := v ∘ dir
  let D (x : Domain 2) (i : Fin 2) := ‖x‖⁻¹ • G (dir x) i
  have hDir (ρ : PositiveRadius) (θ : UnitBoundarySphere 2) : dir (ρ.val • θ.val) = θ := by
    simp only [dir, sphereRadialDirection_smul _ ρ.property, sphereRadialDirection_unit]
  have hWray (ρ : PositiveRadius) (θ : UnitBoundarySphere 2) : w (ρ.val • θ.val) = v θ := by
    simp only [w, Function.comp_apply, hDir]
  have hDray (ρ : PositiveRadius) (θ : UnitBoundarySphere 2) (i : Fin 2) :
      D (ρ.val • θ.val) i = ρ.val⁻¹ • G θ i := by
    simp only [D, norm_smul, Real.norm_of_nonneg ρ.property.le, mem_sphere_zero_iff_norm.mp θ.property,
      mul_one, hDir]
  have hW : MemLp w 2 (volume.restrict angularCollar.val) :=
    (memLp_two_radial_collar_and_norm (by decide : 0 < 2) (hσ ▸ hv) hWray (1 / 2)
      (by norm_num : (0 : ℝ) < 3 / 2)).1
  have hDL (i : Fin 2) : MemLp (fun x => D x i) 2 (volume.restrict angularCollar.val) :=
    (memLp_two_weighted_radial_collar_and_norm (by decide : 0 < 2) (hσ ▸ hG i) (W := fun x => D x i) 1
      (fun ρ θ => (hDray ρ θ i).trans (by rw [one_div])) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 3 / 2)).1
  have hWeak : HasWeakGradient angularCollar w D := by
    apply hasWeakGradient_periodicAngularExtension v f hAC hParam hW hDL
    · intro r hr t ht
      exact (hWray ⟨r, (by norm_num : (0 : ℝ) < 1 / 2).trans hr.1⟩ (periodicAngularParam t)).trans
        (hParam (Ioo_subset_Icc_self ht)).symm
    · intro r hr t ht i
      calc
        D (r • periodicAngularRay t) i = r⁻¹ • G (periodicAngularParam t) i :=
          hDray ⟨r, (by norm_num : (0 : ℝ) < 1 / 2).trans hr.1⟩ (periodicAngularParam t) i
        _ = _ := by simp only [G, periodicAngularArg_param ht, smul_smul]
  have hw : MemW12 angularCollar w D := ⟨hWeak, hW, hDL⟩
  have hvW : MemSphereW12 (le_refl 2) v := ⟨hv, angularCollar, angularCollar_contains_unitSphere,
    zero_notMem_angularCollar, w, D, hw, fun ρ θ _ => hWray ρ θ⟩
  refine ⟨hvW, le_of_eq ?_⟩
  rw [integral_congr_ae ((sphereGradient_of_angularCollar hvW hw hWray hDray).mono fun _ h => congrArg hsNormSq h)]
  simp_rw [G, hsNormSq_periodicAngularTangent_smul]
  have hMeas : AEStronglyMeasurable (fun t => ‖deriv f t‖ ^ 2)
      (Measure.map periodicAngularArg (unitBoundarySurface 2)) := by
    rw [periodicAngularArg_measurePreserving.map_eq]
    exact (hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).aestronglyMeasurable
  have hF := integral_map periodicAngularArg_measurePreserving.aemeasurable hMeas
  rw [periodicAngularArg_measurePreserving.map_eq] at hF
  exact hF.symm

end Thesis

end
