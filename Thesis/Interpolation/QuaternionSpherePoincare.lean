module

public import Thesis.Interpolation.QuaternionSphereFill
import StratificationTheory.Frozen.SphereRadialBallExtension
import StratificationTheory.Foundation.AngularL2Membership
import StratificationTheory.Foundation.SphereCircleWeakData
import StratificationTheory.Foundation.BanachIntervalWeakRepresentative
import HarmonicMaps.Analysis.SobolevPoincare
import Mathlib.MeasureTheory.Integral.Prod

/-! Poincaré inequalities for the native quaternion sphere Sobolev data. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ENNReal Topology

namespace Thesis

private theorem integral_radial_unitBall_three {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {v : UnitBoundarySphere 3 → E} {w : Domain 3 → E}
    (hRay : ∀ (ρ : PositiveRadius) (θ : UnitBoundarySphere 3), w (ρ.val • θ.val) = v θ) :
    (∫ x in ball (0 : Domain 3) 1, w x) = (1 / 3 : ℝ) • ∫ θ, v θ ∂unitBoundarySurface 3 := by
  let X := ({(0 : Domain 3)}ᶜ : Set (Domain 3))
  let σ := (volume : Measure (Domain 3)).toSphere
  let r₁ : Ioi (0 : ℝ) := ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩
  let J := Iio r₁
  let η := (Measure.volumeIoiPow 2).restrict J
  let H := homeomorphUnitSphereProd (Domain 3)
  have hη : η univ = ENNReal.ofReal (1 / 3 : ℝ) := by
    norm_num [η, J, r₁, Measure.restrict_apply_univ, Measure.volumeIoiPow_apply_Iio]
  letI : IsFiniteMeasure η := ⟨hη.trans_lt ENNReal.ofReal_lt_top⟩
  have hm := (volume : Measure (Domain 3)).measurePreserving_homeomorphUnitSphereProd
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] at hm
  have hM := hm.restrict_preimage (MeasurableSet.univ.prod (measurableSet_Iio (a := r₁)))
  have hpre : H ⁻¹' (univ ×ˢ J) = (Subtype.val : X → Domain 3) ⁻¹' ball 0 1 := by
    ext x
    simp only [mem_preimage, mem_prod, mem_univ, true_and, J, mem_Iio, mem_ball, dist_zero_right]
    change ((H x).2.val < 1) ↔ ‖x.val‖ < 1
    rw [homeomorphUnitSphereProd_apply_snd_coe]
  rw [show (homeomorphUnitSphereProd (Domain 3)) ⁻¹' (univ ×ˢ Iio r₁) =
    (Subtype.val : X → Domain 3) ⁻¹' ball 0 1 from hpre, ← Measure.prod_restrict] at hM
  simp only [Measure.restrict_univ] at hM
  have hc := (measurePreserving_subtype_coe
    ((measurableSet_singleton (0 : Domain 3)).compl) (μa := volume)).restrict_preimage
      (measurableSet_ball (x := (0 : Domain 3)) (ε := 1))
  rw [restrict_compl_singleton] at hc
  have heq : (fun x : X => w x.val) = (fun p : UnitBoundarySphere 3 × Ioi (0 : ℝ) => v p.1) ∘ H := by
    funext x
    let p := H x
    have hp : p.2.val • p.1.val = x.val := by
      have h := congrArg (fun y : X => y.val) (H.symm_apply_apply x)
      simpa only [H, homeomorphUnitSphereProd_symm_apply_coe] using h
    change w x.val = v p.1
    rw [← hp]
    exact hRay ⟨p.2.val, p.2.property⟩ p.1
  have hσ : unitBoundarySurface 3 = σ := euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide)
  have hηReal : η.real univ = (1 / 3 : ℝ) := by
    rw [measureReal_def, hη, ENNReal.toReal_ofReal (by norm_num)]
  calc
    _ = ∫ x : X, w x.val ∂((volume : Measure (Domain 3)).comap (Subtype.val : X → Domain 3) |>.restrict
          ((Subtype.val : X → Domain 3) ⁻¹' ball 0 1)) :=
      (hc.integral_comp (MeasurableEmbedding.subtype_coe
        ((measurableSet_singleton (0 : Domain 3)).compl)) w).symm
    _ = ∫ p, v p.1 ∂σ.prod η := by
      rw [heq]
      exact hM.integral_comp (Homeomorph.measurableEmbedding _)
        (fun p : UnitBoundarySphere 3 × Ioi (0 : ℝ) => v p.1)
    _ = _ := by rw [integral_fun_fst, hηReal, hσ]

/-- The native two-sphere Poincaré inequality follows from the exact radial
extension into the unit ball and the Sobolev Poincaré inequality there. -/
theorem quaternionSpherePoincare_three : External.QuaternionSpherePoincare 3 (by decide : 2 ≤ 3) := by
  refine ⟨48, by norm_num, ?_⟩
  intro v hv
  obtain ⟨w, D, hw, hRay, _, _, hE, _⟩ :=
    exists_radial_ball_sobolev_extension (by decide : 3 ≤ 3) v hv zero_lt_one
  let μ := (volume : Measure (Domain 3)).restrict (ball 0 1)
  let σ := unitBoundarySurface 3
  have hMass : μ.real univ = (1 / 3 : ℝ) * σ.real univ := by
    have h := integral_radial_unitBall_three (E := ℝ) (v := fun _ => 1) (w := fun _ => 1) fun _ _ => rfl
    simpa only [μ, σ, integral_const, smul_eq_mul, mul_one] using h
  have hAvg : average μ w = average σ v := by
    rw [average_eq, average_eq, hMass, integral_radial_unitBall_three hRay, mul_inv_rev, smul_smul]
    congr 1
    ring_nf
  have hDev : (∫ x, ‖w x - average μ w‖ ^ 2 ∂μ) =
      (1 / 3 : ℝ) * ∫ θ, ‖v θ - average σ v‖ ^ 2 ∂σ := by
    rw [hAvg]
    exact integral_radial_unitBall_three (fun ρ θ => by rw [hRay ρ θ])
  have hEnergy : (∫ x in ball (0 : Domain 3) 1, hsNormSq (D x)) =
      quaternionBoundaryEnergy (by decide : 2 ≤ 3) v hv := by
    simpa [quaternionBoundaryEnergy, hsNormSq, unitBoundarySurface,
      show (3 : ℝ) - 2 = 1 by norm_num] using hE
  have hBall := hw.poincare_ball zero_lt_one
  change (∫ x, ‖w x - average μ w‖ ^ 2 ∂μ) ≤
    (2 : ℝ) ^ (3 + 1 : ℕ) * (1 : ℝ) ^ 2 * ∫ x in ball (0 : Domain 3) 1, hsNormSq (D x) at hBall
  rw [hDev, hEnergy] at hBall
  linarith only [hBall]

/-- The circle estimate uses the original sphere-gradient columns through the
native angular weak derivative and the exact arclength measure. -/
theorem quaternionSpherePoincare_two : External.QuaternionSpherePoincare 2 (by decide : 2 ≤ 2) := by
  let L := Real.pi - (-Real.pi)
  have hL : 0 < L := by dsimp only [L]; linarith only [Real.pi_pos]
  refine ⟨L ^ 2, sq_pos_of_pos hL, ?_⟩
  intro v hv
  let σ := unitBoundarySurface 2
  let ν := (volume : Measure ℝ).restrict (Ioo (-Real.pi) Real.pi)
  let f (t : ℝ) := v (circleNativeParam t)
  let τ (t : ℝ) : Domain 2 := WithLp.toLp 2 ![-Real.sin t, Real.cos t]
  let g (t : ℝ) := ∑ i : Fin 2, τ t i • (sphereGradient (by decide : 2 ≤ 2) v hv i) (circleNativeParam t)
  obtain ⟨hf, hg, hWeak, hEnergy⟩ := sphere_circle_weak_data v hv
  have hf' : MemLp f 2 ν := hf
  have hg' : MemLp g 2 ν := hg
  let E := ∫ t, ‖g t‖ ^ 2 ∂ν
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  have hEnergy' : E ≤ quaternionBoundaryEnergy (by decide : 2 ≤ 2) v hv := hEnergy
  have hν : ν.real univ = L := by
    change ((volume : Measure ℝ).restrict (Ioo (-Real.pi) Real.pi)).real univ = L
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioo]
    exact ENNReal.toReal_ofReal hL.le
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  letI : IsFiniteMeasure σ := by
    dsimp only [σ, unitBoundarySurface]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)]
    infer_instance
  have hMP : MeasurePreserving circleNativeParam ν σ :=
    ⟨continuous_circleNativeParam.measurable, map_circleNativeParam_Ioo_eq_native⟩
  have hVolumes : ν.real univ = σ.real univ := by
    rw [← hMP.map_eq, measureReal_def, measureReal_def,
      Measure.map_apply hMP.measurable MeasurableSet.univ, preimage_univ]
  have hIntegrals {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {w : UnitBoundarySphere 2 → E} (hw : AEStronglyMeasurable w σ) :
      (∫ t, w (circleNativeParam t) ∂ν) = ∫ θ, w θ ∂σ := by
    simpa only [hMP.map_eq, Function.comp_apply] using
      (integral_map hMP.aemeasurable (hMP.map_eq.symm ▸ hw)).symm
  have hAvg : average ν f = average σ v := by
    rw [average_eq, average_eq, hVolumes, hIntegrals (w := v) hv.1.aestronglyMeasurable]
  obtain ⟨F, hF, _⟩ := banach_interval_weakDerivative_exists_unique_continuous_representative
    (sub_pos.mp hL) hf' hg' hWeak
  have hFae : ∀ᵐ x ∂ν, ∀ hx : x ∈ Ioo (-Real.pi) Real.pi, F ⟨x, hx.1.le, hx.2.le⟩ = f x :=
    ae_restrict_of_ae hF.1
  have hDist (x y : ℝ) (hx : x ∈ Ioo (-Real.pi) Real.pi) (hy : y ∈ Ioo (-Real.pi) Real.pi)
      (hxF : F ⟨x, hx.1.le, hx.2.le⟩ = f x) (hyF : F ⟨y, hy.1.le, hy.2.le⟩ = f y) :
      ‖f x - f y‖ ≤ Real.sqrt (L * E) := by
    apply Real.le_sqrt_of_sq_le
    have hxy : |x - y| ≤ L := by
      apply abs_le.mpr
      dsimp only [L]
      exact ⟨by linarith only [hx.1, hy.2], by linarith only [hx.2, hy.1]⟩
    have h := hF.2.2.2.1 ⟨y, hy.1.le, hy.2.le⟩ ⟨x, hx.1.le, hx.2.le⟩
    change ‖F ⟨x, hx.1.le, hx.2.le⟩ - F ⟨y, hy.1.le, hy.2.le⟩‖ ^ 2 ≤ |x - y| * E at h
    rw [hxF, hyF] at h
    exact h.trans (mul_le_mul_of_nonneg_right hxy hE)
  have hPoint : ∀ᵐ x ∂ν, ‖f x - average ν f‖ ^ 2 ≤ L * E := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo, hFae] with x hx hxF
    have hAe : ∀ᵐ y ∂ν, ‖f x - f y‖ ≤ Real.sqrt (L * E) := by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo, hFae] with y hy hyF
      exact hDist x y hx hy (hxF hx) (hyF hy)
    have h := norm_integral_le_of_norm_le_const hAe
    rw [integral_sub (integrable_const (f x)) (hf'.integrable (by norm_num)), integral_const,
      ← measure_smul_average ν f, ← smul_sub, norm_smul,
      Real.norm_of_nonneg measureReal_nonneg, hν] at h
    have hNorm : ‖f x - average ν f‖ ≤ Real.sqrt (L * E) :=
      (mul_le_mul_iff_right₀ hL).mp (h.trans_eq (mul_comm _ _))
    exact (pow_le_pow_left₀ (norm_nonneg _) hNorm 2).trans_eq (Real.sq_sqrt (mul_nonneg hL.le hE))
  have hDev : (∫ t, ‖f t - average ν f‖ ^ 2 ∂ν) ≤ L ^ 2 * E := by
    have h := integral_mono_ae ((hf'.sub (memLp_const _)).integrable_norm_pow (by decide))
      (integrable_const (L * E)) hPoint
    rw [integral_const, smul_eq_mul, hν] at h
    calc
      _ ≤ L * (L * E) := h
      _ = _ := by ring
  have hDevMeas : AEStronglyMeasurable (fun θ => ‖v θ - average σ v‖ ^ 2) σ :=
    ((hv.1.sub (memLp_const _)).integrable_norm_pow (by decide)).aestronglyMeasurable
  rw [hAvg, hIntegrals hDevMeas] at hDev
  exact hDev.trans (mul_le_mul_of_nonneg_left hEnergy' (sq_nonneg L))

end Thesis

end
