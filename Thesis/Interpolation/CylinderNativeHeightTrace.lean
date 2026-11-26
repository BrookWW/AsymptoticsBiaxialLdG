module

public import Thesis.Interpolation.CylinderVolumeGluing
import Thesis.Interpolation.FiniteL2TraceEstimate
import Thesis.Interpolation.LipschitzSobolevPullback
import HarmonicMaps.Analysis.RadialIntegrability
import StratificationTheory.Foundation.CylinderRawTime

/-! The original horizontal Sobolev trace and its endpoint estimate. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace Thesis.MeasureGeometry

private def cylinderHeightTraceFrame (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) : Point ≃ₜ Point where
  toFun y := c + B.repr.symm y
  invFun x := B.repr (x - c)
  left_inv y := by
    change B.repr (c + B.repr.symm y - c) = y
    rw [add_sub_cancel_left, B.repr.apply_symm_apply]
  right_inv x := by
    change c + B.repr.symm (B.repr (x - c)) = x
    rw [B.repr.symm_apply_apply, add_comm c, sub_add_cancel]
  continuous_toFun := continuous_const.add B.repr.symm.continuous
  continuous_invFun := B.repr.continuous.comp (continuous_id.sub continuous_const)

private theorem cylinderHeightTraceFrame_isometry (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) :
    Isometry (cylinderHeightTraceFrame B c) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (c + B.repr.symm x) (c + B.repr.symm y) = dist x y
  rw [dist_add_left, B.repr.symm.isometry.dist_eq]

private theorem cylinderHeightTraceFrame_symm_isometry (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) :
    Isometry (cylinderHeightTraceFrame B c).symm := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (B.repr (x - c)) (B.repr (y - c)) = dist x y
  rw [B.repr.isometry.dist_eq, dist_sub_right]

private theorem cylinderHeightTraceFrame_coordinates
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c y : Point) :
    cylinderRecoveryCoordinates B c (cylinderHeightTraceFrame B c y) = recoveryReferenceSplit y := by
  change recoveryReferenceSplit (B.repr (c + B.repr.symm y - c)) = recoveryReferenceSplit y
  rw [add_sub_cancel_left, B.repr.apply_symm_apply]

private theorem measurePreserving_cylinder_height_parameter
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R lo hi : ℝ) :
    MeasurePreserving (fun p : Plane × ℝ => c + axisChart B p)
      (((volume : Measure Plane).restrict (ball (0 : Plane) R)).prod (volume.restrict (Ioo lo hi)))
      (volume.restrict (translatedAxisCylinder c (B 2) R lo hi)) := by
  let T (p : Plane × ℝ) := c + axisChart B p
  have hVol : MeasurePreserving T ((volume : Measure Plane).prod (volume : Measure ℝ)) volume := by
    simpa only [T, Function.comp_def, add_comm c] using
      (measurePreserving_add_left (volume : Measure Point) c).comp (measurePreserving_axisChart B)
  have hPre : T ⁻¹' translatedAxisCylinder c (B 2) R lo hi = ball (0 : Plane) R ×ˢ Ioo lo hi := by
    ext p
    change T p ∈ translatedAxisCylinder c (B 2) R lo hi ↔ _
    rw [mem_translatedAxisCylinder_iff_recoveryCoordinates, cylinderRecoveryCoordinates_axisChart]
    rfl
  have hM := hVol.restrict_preimage (isOpen_translatedAxisCylinder c (B 2) R lo hi).measurableSet
  rw [hPre, ← Measure.prod_restrict] at hM
  exact hM

/-- Every actual cylinder graph has a continuous horizontal trace; its
squared norm is bounded at every height, including both end disks. -/
theorem exists_cylinderHeight_trace_with_estimate {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hI : lo < hi)
    (u : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q)
    (hu : MemW12 (translatedAxisCylinderDomain B c R lo hi) u D) :
    ∃ H : CylinderHeightL2Trace q R lo hi, RepresentsCylinderHeightL2Trace B c u H ∧
      ∀ t : Icc lo hi, ‖H t‖ ^ 2 ≤
        (2 / (hi - lo)) * (∫ x in translatedAxisCylinder c (B 2) R lo hi, ‖u x‖ ^ 2) +
          2 * (hi - lo) * (∫ x in translatedAxisCylinder c (B 2) R lo hi, hsNormSq (D x)) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let E := cylinderHeightTraceFrame B c
  let U := translatedAxisCylinderDomain B c R lo hi
  let V : OpenDomain 3 := ⟨E ⁻¹' U.val, U.property.preimage E.continuous⟩
  let S := ballDomain (0 : Plane) R
  let A : OpenDomain 3 :=
    ⟨{y | (e y).1 ∈ S.val ∧ (e y).2 0 ∈ Ioo lo hi},
      (S.property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
  have hV : V = A := by
    apply Subtype.ext
    ext y
    change E y ∈ translatedAxisCylinder c (B 2) R lo hi ↔ _
    rw [mem_translatedAxisCylinder_iff_recoveryCoordinates, cylinderHeightTraceFrame_coordinates]
    rfl
  let G (x : Point) (i : Fin 3) := ∑ j : Fin 3, (fderiv ℝ E x (EuclideanSpace.single i 1)) j • D (E x) j
  have hLip : LipschitzWith 1 (E : Point → Point) := (cylinderHeightTraceFrame_isometry B c).lipschitz
  have hInv : LipschitzWith 1 (E.symm : Point → Point) := (cylinderHeightTraceFrame_symm_isometry B c).lipschitz
  have hWA : MemW12 A (u ∘ E) G := hV ▸ memW12_lipschitz_homeomorph_preimage E hLip hInv U u D hu
  let σ := (volume : Measure Plane).restrict (ball (0 : Plane) R)
  let ν := (volume : Measure ℝ).restrict (Ioo lo hi)
  let νC := (volume : Measure ℝ).restrict (Icc lo hi)
  letI : IsFiniteMeasure σ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hν : νC = ν := Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  let T (p : Plane × ℝ) := c + axisChart B p
  let Y (p : Plane × ℝ) := e.symm (p.1, EuclideanSpace.single 0 p.2)
  let F (p : Plane × ℝ) := u (T p)
  let J (p : Plane × ℝ) := G (Y p) (Fin.natAdd 2 (0 : Fin 1))
  have hEY (p : Plane × ℝ) : E (Y p) = T p := by
    change c + B.repr.symm (e.symm (p.1, EuclideanSpace.single 0 p.2)) = c + axisChart B p
    rw [axisChart_eq_finAddEquivProd_symm]
  have hM : MeasurePreserving T (σ.prod ν) (volume.restrict U.val) :=
    measurePreserving_cylinder_height_parameter B c R lo hi
  have hY : MeasurePreserving Y (σ.prod ν) (volume.restrict A.val) := by
    have hY := (measurePreserving_cylinder_coordinates_inverse 2).restrict_preimage A.property.measurableSet
    have hPre : Y ⁻¹' A.val = (ball (0 : Plane) R) ×ˢ Ioo lo hi := by
      ext p
      simp only [Y, A, S, mem_preimage, mem_setOf_eq, ContinuousLinearEquiv.apply_symm_apply,
        PiLp.single_apply, ite_true, mem_prod, ballDomain]
    rw [hPre, ← Measure.prod_restrict] at hY
    exact hY
  have hF : MemLp F 2 (σ.prod νC) := by
    rw [hν]
    exact hu.2.1.comp_measurePreserving hM
  have hJ : MemLp J 2 (σ.prod νC) := by
    rw [hν]
    exact (hWA.2.2 _).comp_measurePreserving hY
  have hWeak (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioo lo hi) :
      ∀ᵐ p ∂σ, (∫ t in Icc lo hi, deriv φ t • F (p, t)) = -(∫ t in Icc lo hi, φ t • J (p, t)) := by
    have h := StratificationTheory.MemW12.cylinder_time_test_ae S measure_ball_ne_top hWA hφ hc hs
    filter_upwards [h] with y hy
    have hφL : MemLp φ ⊤ ν := hφ.continuous.memLp_top_of_hasCompactSupport hc _
    have hDφL : MemLp (deriv φ) ⊤ ν := (hφ.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport hc.deriv _
    have hFI : Integrable (fun t => deriv φ t • F (y, t)) ν := by
      have h := hy.1.smul_of_top_right hDφL
      change Integrable (fun t => deriv φ t • u (E (Y (y, t)))) ν at h
      simp_rw [hEY] at h
      exact h
    have hJI : Integrable (fun t => φ t • J (y, t)) ν := hy.2.1.smul_of_top_right hφL
    have hEq := hy.2.2.2
    change (∫ t, deriv φ t • (u ∘ E) (Y (y, t)) + φ t • J (y, t) ∂ν) = 0 at hEq
    simp_rw [Function.comp_apply, hEY] at hEq
    change (∫ t, deriv φ t • F (y, t) + φ t • J (y, t) ∂ν) = 0 at hEq
    rw [integral_add hFI hJI] at hEq
    change (∫ t, deriv φ t • F (y, t) ∂νC) = -(∫ t, φ t • J (y, t) ∂νC)
    rw [hν]
    exact eq_neg_of_add_eq_zero_left hEq
  obtain ⟨H, hH, hBound⟩ := exists_finite_L2_trace_with_endpoint_estimate σ hI hF hJ hWeak
  refine ⟨H, hH, ?_⟩
  intro t
  have hMapE : (∫ p, ‖F p‖ ^ 2 ∂σ.prod νC) = ∫ x in U.val, ‖u x‖ ^ 2 := by
    rw [hν, ← hM.map_eq]
    exact (integral_map hM.aemeasurable (hM.map_eq.symm ▸
      (hu.2.1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).aestronglyMeasurable)).symm
  have hGradE : (∫ p, ‖J p‖ ^ 2 ∂σ.prod νC) ≤ ∫ x in U.val, hsNormSq (D x) := by
    have hMeas := (integrable_hsNormSq_of_memLp_columns hu.2.2).aestronglyMeasurable
    have hExt : Integrable (fun p => hsNormSq (D (T p))) (σ.prod νC) := by
      rw [hν]
      exact hM.integrable_comp_of_integrable (integrable_hsNormSq_of_memLp_columns hu.2.2)
    have hPoint (p : Plane × ℝ) : ‖J p‖ ^ 2 ≤ hsNormSq (D (T p)) := by
      let i := Fin.natAdd 2 (0 : Fin 1)
      let v := fderiv ℝ E (Y p) (EuclideanSpace.single i 1)
      have hNorm : ‖v‖ ≤ 1 := by
        apply ((fderiv ℝ E (Y p)).le_opNorm _).trans
        rw [show ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 by simp, mul_one]
        exact norm_fderiv_le_of_lipschitz ℝ hLip
      have h := norm_sq_sum_gradient_le (D (T p)) v
      have hTerm : ‖J p‖ ^ 2 = ‖∑ j : Fin 3, v j • D (T p) j‖ ^ 2 := by
        dsimp only [J, G, v, i]
        rw [hEY]
      rw [hTerm]
      apply h.trans
      simpa only [one_pow, one_mul] using mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hNorm 2) (hsNormSq_nonneg (D (T p)))
    refine (integral_mono (hJ.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)) hExt hPoint).trans_eq ?_
    rw [hν, ← hM.map_eq]
    exact (integral_map hM.aemeasurable (hM.map_eq.symm ▸ hMeas)).symm
  change ‖H t‖ ^ 2 ≤ (2 / (hi - lo)) * (∫ x in U.val, ‖u x‖ ^ 2) +
    2 * (hi - lo) * (∫ x in U.val, hsNormSq (D x))
  rw [← hMapE]
  exact (hBound t).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hGradE (by linarith only [hI])))

end Thesis.MeasureGeometry

end
