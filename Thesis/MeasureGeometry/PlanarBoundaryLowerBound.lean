module

public import Thesis.MeasureGeometry.PlanarSobolevLowerBound
public import Thesis.MeasureGeometry.PlanarTraceBound
public import Thesis.Interpolation.MeshFaceNullHomotopy
import HarmonicMaps.Analysis.AffineBallMeasure
import Thesis.StressEnergy
import StratificationTheory.Foundation.RadialPiecewiseProperties
import StratificationTheory.Foundation.AngularL2Membership

/-! The planar logarithmic lower bound from the original Sobolev boundary trace. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

private theorem nativeVacuumCircleCost_le_two_kappa (a : BulkCoefficients)
    (q : C(NativeCircle, vacuum a)) : nativeVacuumCircleCost a q ≤ 2 * kappaStar a := by
  by_cases hq : 0 < nativeVacuumCircleCost a q
  · exact (nativeVacuumCircleCost_bounds_of_pos a q hq).2
  · exact (le_of_not_gt hq).trans (mul_nonneg (by norm_num) (kappaStar_pos a).le)

/-- The boundary trace version of the planar logarithmic lower bound on
the unit disk, with the exact boundary cost multiplier log 80. -/
theorem exists_planarWeakEnergy_boundary_gap_lower_unit (hcoarea : External.PlanarScalarCoarea)
    (hAngular : External.PeriodicAngularSobolev) (a : BulkCoefficients) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε g : ℝ}, 0 < ε → ε < 1 / 80 → 0 < g →
      ∀ (u : Plane → Ambient 5) (Du : Plane → HarmonicMaps.Gradient 2 5),
        MemW12 (ballDomain (0 : Plane) 1) u Du →
        (∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖u x‖ ≤ C₀) →
        ∀ (b : C(NativeCircle, S0)) {s : ℝ} (hs : s < 1) (H : VacuumBallTrace 2 s),
          RepresentsVacuumBallTrace u H →
          (∃ hb : MemLp (fun θ => frobeniusCoordinateEquiv (b θ)) 2 (unitBoundarySurface 2),
            H ⟨1, hs.le, le_rfl⟩ = hb.toLp _) →
          let β (t : ℝ) := b (circleNativeParam (t - Real.pi))
          AbsolutelyContinuousOnInterval β 0 (2 * Real.pi) →
          MemLp (deriv β) 2 (volume.restrict (Ioo 0 (2 * Real.pi))) →
          (∀ θ, g ≤ normalizedSpectralGap a (b θ)) →
          ∀ q : C(NativeCircle, vacuum a), (∀ θ, q θ = spectralVacuumPoint a (b θ)) →
            nativeVacuumCircleCost a q * g ^ 2 * Real.log (1 / ε) - C ≤
              planarWeakEnergy a ε u Du 1 +
                Real.log 80 * ((1 / 2 : ℝ) * (∫ t in Ioo 0 (2 * Real.pi), ‖deriv β t‖ ^ 2) +
                  ε⁻¹ ^ 2 * ∫ t in Ioo 0 (2 * Real.pi), bulkPotential a (β t)) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : S0) C₀).exists_bound_of_continuousOn
    (continuous_normalizedSpectralGap a).continuousOn
  obtain ⟨C, hC, hLower⟩ := exists_planarWeakEnergy_continuous_collar_lower hcoarea a C₀ hC₀
  have hLog : (1 / 2 : ℝ) ≤ Real.log 80 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 80)
    norm_num at h
    linarith only [h]
  let K := 2 * kappaStar a * M ^ 2 * Real.log 80
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (kappaStar_pos a).le)
    (sq_nonneg _)) ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans hLog)
  refine ⟨C + K, add_pos_of_pos_of_nonneg hC hK, ?_⟩
  intro ε g hε _hεupper hg u Du hu huB b s hs H hH hEnd β hBAC hBD hGap q hq
  let b₀ : C(NativeCircle, Ambient 5) := ⟨fun z => frobeniusCoordinateEquiv (b z),
    frobeniusCoordinateEquiv.continuous.comp b.continuous⟩
  obtain ⟨hb₀, hbEnd⟩ := hEnd
  have hbB : ∀ z : NativeCircle, ‖b₀ z‖ ≤ C₀ := norm_le_of_nativeBallTrace hs H hH b₀ hb₀ hbEnd huB
  have hgM : g ≤ M := by
    have hBall : b nativeCircleLoopBase ∈ closedBall (0 : S0) C₀ := by
      apply mem_closedBall_zero_iff.mpr
      simpa only [b₀, ContinuousMap.coe_mk, frobeniusCoordinateEquiv.norm_map] using hbB nativeCircleLoopBase
    exact (hGap nativeCircleLoopBase).trans ((le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using hM (b nativeCircleLoopBase) hBall))
  let β₀ : ℝ → Ambient 5 := frobeniusCoordinateEquiv ∘ β
  have hβAC : AbsolutelyContinuousOnInterval β₀ 0 (2 * Real.pi) := by
    rw [absolutelyContinuousOnInterval_iff] at hBAC ⊢
    simpa only [β₀, Function.comp_apply, frobeniusCoordinateEquiv.isometry.dist_eq] using hBAC
  have hβDer : deriv β₀ = frobeniusCoordinateEquiv ∘ deriv β := by
    funext t
    rw [← fderiv_apply_one_eq_deriv, show β₀ = frobeniusCoordinateEquiv ∘ β from rfl,
      LinearIsometryEquiv.comp_fderiv, ContinuousLinearMap.comp_apply, Function.comp_apply,
      fderiv_apply_one_eq_deriv]
    rfl
  have hβMem : MemLp (deriv β₀) 2 (volume.restrict (Ioo 0 (2 * Real.pi))) :=
    hβDer.symm ▸ frobeniusCoordinateEquiv.toContinuousLinearMap.comp_memLp' hBD
  obtain ⟨hb, hBE⟩ := hAngular b₀ β₀ (by intro t ht; rfl) hβAC hβMem
  have hGradB : (∫ θ : NativeCircle, hsNormSq (fun i => sphereGradient (le_refl 2) b₀ hb i θ) ∂unitBoundarySurface 2) ≤
      ∫ t in Ioo 0 (2 * Real.pi), ‖deriv β t‖ ^ 2 := by
    simpa only [hβDer, Function.comp_apply, frobeniusCoordinateEquiv.norm_map] using hBE
  have hbTrace : H ⟨1, hs.le, le_rfl⟩ = hb.1.toLp b₀ := hbEnd
  let r : ℝ := 1 / 80
  have hr : 0 < r := by norm_num [r]
  have hr₁ : r < 1 := by norm_num [r]
  let η : ℝ := 80 * ε
  have hη : 0 < η := mul_pos (by norm_num) hε
  obtain ⟨w, Dw, hw, hW, hWGrad⟩ := exists_planarSobolev_radialCollar hr hr₁ b₀ hb hu hs H hH hbTrace
  have hInB : ∀ᵐ x ∂volume.restrict (ball (0 : Plane) r), ‖u (r⁻¹ • x)‖ ≤ C₀ := by
    simpa only [zero_add, sub_zero, one_div, inv_inv] using
      ae_affineBall (0 : Plane) 0 (t := r⁻¹) (inv_pos.mpr hr) 1 huB
  have hwB : ∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖w x‖ ≤ C₀ := by
    have h := ae_radial_piecewise_property (0 : Plane) hr hr₁ (fun x => u (r⁻¹ • x))
      (fun x => b₀ (sphereRadialDirection nativeCircleLoopBase x)) (fun A => ‖A‖ ≤ C₀)
      hInB (ae_of_all _ fun x => hbB (sphereRadialDirection nativeCircleLoopBase x))
    filter_upwards [h] with x hx
    simpa only [hW x, sub_zero] using hx
  let V : OpenDomain 2 := ⟨{x | r < ‖x‖ ∧ ‖x‖ < 1}, isOpen_Ioo.preimage continuous_norm⟩
  have hV : V.val ⊆ ball (0 : Plane) 1 := fun x hx => mem_ball_zero_iff.mpr hx.2
  have hVC : ContinuousOn w V.val := by
    have hvNonzero : V.val ⊆ ({0}ᶜ : Set Plane) := by
      intro x hx hz
      have hz' : x = 0 := hz
      exact (hr.trans hx.1).ne' (by rw [hz', norm_zero])
    apply ((b₀.continuous.comp_continuousOn (continuousOn_sphereRadialDirection nativeCircleLoopBase)).mono hvNonzero).congr
    intro x hx
    exact (hW x).trans (if_neg (not_lt_of_gt hx.1))
  have hRad (x : Plane) (hx : r ≤ ‖x‖) :
      frobeniusCoordinateEquiv.symm (w x) = b (sphereRadialDirection nativeCircleLoopBase x) := by
    rw [hW x, if_neg hx.not_gt]
    exact frobeniusCoordinateEquiv.symm_apply_apply _
  have hAnn (x : Plane) (hx : (1 / 40 : ℝ) ≤ ‖x‖) (_hxR : ‖x‖ ≤ 39 / 40) :
      g ≤ normalizedSpectralGap a (frobeniusCoordinateEquiv.symm (w x)) := by
    rw [hRad x ((by norm_num [r] : r ≤ 1 / 40).trans hx)]
    exact hGap _
  have hKV (x : Plane) (hx : (1 / 40 : ℝ) ≤ ‖x‖) (hxR : ‖x‖ ≤ 39 / 40) : x ∈ V.val :=
    ⟨(by norm_num [r] : r < 1 / 40).trans_le hx, hxR.trans_lt (by norm_num)⟩
  have hqW (z : NativeCircle) : q z =
      spectralVacuumPoint a (frobeniusCoordinateEquiv.symm (w ((39 / 40 : ℝ) • z.val))) := by
    rw [hRad _ (by rw [planar_norm_on_circle (by norm_num)]; norm_num [r]),
      sphereRadialDirection_smul nativeCircleLoopBase (by norm_num), sphereRadialDirection_unit]
    exact hq z
  have hELower := hLower hη hg w Dw hw hwB hAnn V hV hVC hKV q hqW
  have hFin : IsFiniteMeasure ((volume : Measure Plane).restrict (ball (0 : Plane) 1)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
        exact (measure_mono ball_subset_closedBall).trans_lt
          ((isCompact_closedBall (0 : Plane) 1).measure_lt_top)⟩
  letI := hFin
  let p := planarCoordinateBulkPotential a
  have hPotW : IntegrableOn (fun x => p (w x)) (ball (0 : Plane) 1) :=
    integrable_planarCoordinateBulkPotential_of_bound a hw.2.1.aestronglyMeasurable hwB
  have hWP := planarRadialCollar_integral hr hr₁ u w b₀ hW p hPotW
  have hPBcont : Continuous (fun z : NativeCircle => bulkPotential a (b z)) :=
    (contDiff_bulkPotential a).continuous.comp b.continuous
  letI : IsFiniteMeasure (unitBoundarySurface 2) := by
    change IsFiniteMeasure (Measure.euclideanHausdorffMeasure (2 - 1) : Measure NativeCircle)
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)]
    infer_instance
  have hPBint : Integrable (fun z : NativeCircle => bulkPotential a (b z)) (unitBoundarySurface 2) :=
    integrableOn_univ.mp (hPBcont.continuousOn.integrableOn_compact isCompact_univ)
  have hPotAngle := nativeCircle_integral_angular (fun z => bulkPotential a (b z)) hPBint
  have hPotB : (∫ θ : NativeCircle, p (b₀ θ) ∂unitBoundarySurface 2) =
      ∫ t in Ioo 0 (2 * Real.pi), bulkPotential a (β t) := by
    rw [hPotAngle]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    change bulkPotential a (frobeniusCoordinateEquiv.symm (frobeniusCoordinateEquiv (b z))) = _
    rw [frobeniusCoordinateEquiv.symm_apply_apply]
  have hεη : ε ≤ η := by dsimp only [η]; linarith only [hε]
  have hCoeff : η⁻¹ ^ 2 ≤ ε⁻¹ ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hη.le)
    (inv_le_inv₀ hη hε |>.mpr hεη) _
  have hPotU : 0 ≤ (∫ x in ball (0 : Plane) 1, p (u x)) := integral_nonneg fun _ => bulkPotential_nonneg a _
  have hPotA : 0 ≤ (∫ t in Ioo 0 (2 * Real.pi), bulkPotential a (β t)) :=
    integral_nonneg fun _ => bulkPotential_nonneg a _
  have hCoreCoeff : η⁻¹ ^ 2 * r ^ 2 ≤ ε⁻¹ ^ 2 := by
    simpa only [mul_one] using mul_le_mul hCoeff (show r ^ 2 ≤ 1 by norm_num [r]) (sq_nonneg _) (sq_nonneg _)
  have hCollarCoeff : η⁻¹ ^ 2 * ((1 - r ^ 2) / 2) ≤ Real.log 80 * ε⁻¹ ^ 2 := by
    have h := mul_le_mul hCoeff (show (1 - r ^ 2) / 2 ≤ Real.log 80 from
      (show (1 - r ^ 2) / 2 ≤ 1 / 2 by norm_num [r]).trans hLog)
      (show 0 ≤ (1 - r ^ 2) / 2 by norm_num [r]) (sq_nonneg _)
    simpa only [mul_comm] using h
  have hLogEq : Real.log (1 / r) = Real.log 80 := by norm_num [r]
  have hLogPos : 0 ≤ Real.log 80 := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hLog
  have hEUpper : planarWeakEnergy a η w Dw 1 ≤
      planarWeakEnergy a ε u Du 1 +
        Real.log 80 * ((1 / 2 : ℝ) * (∫ t in Ioo 0 (2 * Real.pi), ‖deriv β t‖ ^ 2) +
          ε⁻¹ ^ 2 * ∫ t in Ioo 0 (2 * Real.pi), bulkPotential a (β t)) := by
    unfold planarWeakEnergy
    change (1 / 2 : ℝ) * (∫ x in ball (0 : Plane) 1, hsNormSq (Dw x)) +
      η⁻¹ ^ 2 * (∫ x in ball (0 : Plane) 1, p (w x)) ≤ _
    rw [hWGrad, hWP, hPotB, hLogEq]
    have hG := mul_le_mul_of_nonneg_left hGradB (show 0 ≤ (1 / 2 : ℝ) * Real.log 80 by positivity)
    have hP := mul_le_mul_of_nonneg_right hCoreCoeff hPotU
    have hA := mul_le_mul_of_nonneg_right hCollarCoeff hPotA
    linarith only [hG, hP, hA]
  have hLogScale : Real.log (1 / η) = Real.log (1 / ε) - Real.log 80 := by
    rw [one_div, Real.log_inv, show η = 80 * ε from rfl, Real.log_mul (by norm_num) hε.ne',
      one_div, Real.log_inv]
    ring
  let e := nativeVacuumCircleCost a q
  have he := nativeVacuumCircleCost_le_two_kappa a q
  have hEGap : e * g ^ 2 * Real.log 80 ≤ K := by
    have h := mul_le_mul he (pow_le_pow_left₀ hg.le hgM 2) (sq_nonneg _) (mul_nonneg (by norm_num) (kappaStar_pos a).le)
    exact mul_le_mul_of_nonneg_right h hLogPos
  rw [hLogScale] at hELower
  have hCompare : e * g ^ 2 * Real.log (1 / ε) - (C + K) ≤
      e * g ^ 2 * (Real.log (1 / ε) - Real.log 80) - C := by
    linarith only [hEGap]
  exact (hCompare.trans hELower).trans hEUpper

/-- The lower bound required for the original nontrivial mesh face. -/
theorem hasUnitDiskNontrivialLogLowerBound (hcoarea : External.PlanarScalarCoarea)
    (hAngular : External.PeriodicAngularSobolev) (a : BulkCoefficients) :
    HasUnitDiskNontrivialLogLowerBound a := by
  intro B hB
  obtain ⟨C, hC, h⟩ := exists_planarWeakEnergy_boundary_gap_lower_unit hcoarea hAngular a B hB
  refine ⟨C, hC.le, ?_⟩
  intro ξ hξ hξupper w Dw hw hW b s hs H hH hEnd β hBAC hBD hGap q hq hNontriv
  have hNorm : ∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖w x‖ ≤ B := by
    simpa only [frobeniusCoordinateEquiv.symm.norm_map] using hW
  have hLower := h hξ hξupper (show (0 : ℝ) < 1 / 2 by norm_num)
    w Dw hw hNorm b hs H hH hEnd hBAC hBD hGap q hq
  have he : 0 < nativeVacuumCircleCost a q := by
    obtain ⟨v, hv⟩ := vacuumQuaternionProjection_surjective a (q nativeCircleLoopBase)
    have hWord := mt (nativeVacuum_homotopic_const_iff a q v hv).2 hNontriv
    rw [nativeVacuumCircleCost_eq a q v hv, vacuumSplittingCost_eq]
    unfold quaternionSplittingWeight
    simp only [hWord, if_false]
    have hκ := kappaStar_pos a
    split_ifs <;> push_cast <;> positivity
  have hκ := (nativeVacuumCircleCost_bounds_of_pos a q he).1
  have hl : 0 ≤ Real.log ξ⁻¹ := Real.log_nonneg ((one_le_inv₀ hξ).2 (hξupper.le.trans (by norm_num)))
  have hComp : (kappaStar a / 4) * Real.log ξ⁻¹ - C ≤
      nativeVacuumCircleCost a q * (1 / 2 : ℝ) ^ 2 * Real.log (1 / ξ) - C := by
    rw [one_div ξ]
    apply sub_le_sub_right
    have hCoef : kappaStar a / 4 ≤ nativeVacuumCircleCost a q * (1 / 2 : ℝ) ^ 2 := by
      nlinarith only [hκ]
    exact mul_le_mul_of_nonneg_right hCoef hl
  exact hComp.trans hLower

end Thesis
