module

public import Thesis.Interpolation.VacuumDiskCollar
public import Thesis.Foundation.VacuumFreeHomotopy
import HarmonicMaps.Analysis.AffineEnergyScaling
import HarmonicMaps.Analysis.AnnularPolarIntegral
import HarmonicMaps.Analysis.SobolevAECongruence
import HarmonicMaps.SobolevRestriction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import StratificationTheory.Compactness.RadialTraceDilation
import StratificationTheory.Foundation.RadialPiecewiseProperties
import StratificationTheory.Frozen.RadialTraceGluing

/-! Compressing a planar Sobolev disk and attaching its own radial trace. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ENNReal Matrix.Norms.Frobenius

namespace Thesis

theorem radialCollar_hs_integral
    {D : Plane → HarmonicMaps.Gradient 2 5} {r : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    {g : Fin 2 → Lp (Ambient 5) 2 (unitBoundarySurface 2)}
    (hRay : ∀ (ρ : PositiveRadius) (i : Fin 2),
      (fun θ : NativeCircle => ρ.val • D (ρ.val • θ.val) i) =ᵐ[unitBoundarySurface 2] g i)
    (hInt : IntegrableOn (fun x => hsNormSq (D x)) (ball (0 : Plane) 1 \ ball 0 r)) :
    (∫ x in ball (0 : Plane) 1 \ ball 0 r, hsNormSq (D x)) =
      Real.log (1 / r) * ∫ θ : NativeCircle, hsNormSq (fun i => g i θ) ∂unitBoundarySurface 2 := by
  let E := ∫ θ : NativeCircle, hsNormSq (fun i => g i θ) ∂unitBoundarySurface 2
  rw [HarmonicMaps.integral_annulus_eq_polar (by decide : 0 < 2) hr hr₁.le hInt]
  rw [← euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)]
  have hEq : EqOn (fun t : ℝ => t ^ (2 - 1 : ℕ) *
        ∫ θ : NativeCircle, hsNormSq (D (0 + t • θ.val)) ∂unitBoundarySurface 2)
      (fun t => t⁻¹ * E) (uIcc r 1) := by
    intro t ht
    rw [uIcc_of_le hr₁.le] at ht
    have ht₀ := hr.trans_le ht.1
    have hAll := ae_all_iff.2 (hRay ⟨t, ht₀⟩)
    have hDensity : (fun θ : NativeCircle => hsNormSq (D (t • θ.val))) =ᵐ[unitBoundarySurface 2]
        fun θ => t⁻¹ ^ 2 * hsNormSq (fun i => g i θ) := by
      filter_upwards [hAll] with θ hθ
      have hCol : D (t • θ.val) = fun i => t⁻¹ • g i θ := by
        funext i
        rw [← hθ i, smul_smul, inv_mul_cancel₀ ht₀.ne', one_smul]
      rw [hCol, hsNormSq_const_smul]
    simp only [Nat.reduceSub, pow_one, zero_add]
    rw [integral_congr_ae hDensity, integral_const_mul]
    dsimp only [E]
    field_simp
  rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_mul_const,
    integral_inv_of_pos hr zero_lt_one]

/-- The literal compressed disk with its continuous radial collar has its
original weak trace and an exact angular Dirichlet cost. -/
theorem exists_planarSobolev_radialCollar {r : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (b : C(NativeCircle, Ambient 5)) (hb : MemSphereW12 (le_refl 2) b)
    {u : Plane → Ambient 5} {Du : Plane → HarmonicMaps.Gradient 2 5}
    (hu : MemW12 (ballDomain (0 : Plane) 1) u Du)
    {s : ℝ} (hs : s < 1) (H : VacuumBallTrace 2 s) (hH : RepresentsVacuumBallTrace u H)
    (hEnd : H ⟨1, hs.le, le_rfl⟩ = hb.1.toLp _) :
    ∃ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5),
      MemW12 (ballDomain (0 : Plane) 1) w Dw ∧
      (∀ x, w x = if ‖x‖ < r then u (r⁻¹ • x) else b (sphereRadialDirection nativeCircleLoopBase x)) ∧
      (∫ x in ball (0 : Plane) 1, hsNormSq (Dw x)) =
        (∫ x in ball (0 : Plane) 1, hsNormSq (Du x)) + Real.log (1 / r) *
          ∫ θ : NativeCircle, hsNormSq (fun i => sphereGradient (le_refl 2) b hb i θ) ∂unitBoundarySurface 2 := by
  let U (x : Plane) := u (r⁻¹ • x)
  let DU (x : Plane) (i : Fin 2) := r⁻¹ • Du (r⁻¹ • x) i
  have ht : 0 < r⁻¹ := inv_pos.mpr hr
  have hU : MemW12 (ballDomain 0 r) U DU := by
    simpa only [HarmonicMaps.ballAffine, zero_add, sub_zero, one_div, inv_inv, U, DU] using
      hu.affinePullback_ball (t := r⁻¹) ht
  have hUE : (∫ x in ball (0 : Plane) r, hsNormSq (DU x)) =
      ∫ x in ball (0 : Plane) 1, hsNormSq (Du x) := by
    have hpow : (2 : ℤ) - ((2 : ℕ) : ℤ) = 0 := by norm_num
    have he : HarmonicMaps.dirichletEnergy DU ((ballDomain 0 r).val) =
        HarmonicMaps.dirichletEnergy Du ((ballDomain 0 1).val) := by
      simpa only [zero_add, sub_zero, one_div, inv_inv, DU, ballDomain, hpow, zpow_zero,
        ENNReal.ofReal_one, one_mul] using
        (dirichletEnergy_affineBall (0 : Plane) 0 (t := r⁻¹) ht 1 Du)
    rw [HarmonicMaps.dirichletEnergy_eq_ofReal_integral hU.integrable_hsNormSq,
      HarmonicMaps.dirichletEnergy_eq_ofReal_integral hu.integrable_hsNormSq] at he
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => hsNormSq_nonneg _)
      (integral_nonneg fun _ => hsNormSq_nonneg _)).1 he
  obtain ⟨J, hJ, hJEnd⟩ := extend_vacuumBallTrace (le_refl 2) hu hs H hH
  have hJ₀ : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (1 / 2) 1,
      ∃ hLp : MemLp (fun θ : NativeCircle => u (0 + t • θ.val)) 2 (unitBoundarySurface 2),
        J ⟨t, ht.1.le, ht.2.le⟩ = hLp.toLp _ := by
    simpa only [zero_add, RepresentsVacuumBallTrace] using hJ
  obtain ⟨JU, hJU, hJUend⟩ := Compactness.exists_dilated_inner_radial_trace
    (unitBoundarySurface 2) u (0 : Plane) (s := 1) (t := r⁻¹) (lo := r)
    zero_lt_one ht hr (inv_mul_cancel₀ hr.ne') le_rfl le_rfl J hJ₀
  let A : OpenDomain 2 := ⟨{x | ‖x‖ ∈ Ioo r 1}, isOpen_Ioo.preimage continuous_norm⟩
  let K : Set Plane := closedBall 0 1 \ ball 0 r
  have hK : IsCompact K := (isCompact_closedBall _ _).diff isOpen_ball
  have hKS : K ⊆ ({0}ᶜ : Set Plane) := by
    intro x hx he
    have hx₀ : x = 0 := he
    exact hx.2 (by rw [hx₀]; exact mem_ball_self hr)
  have hAK : A.val ⊆ K := by
    intro x hx
    exact ⟨(mem_closedBall_zero_iff.2 hx.2.le), fun hball => hx.1.not_ge (le_of_lt (mem_ball_zero_iff.1 hball))⟩
  obtain ⟨z, Dz, hzLoc, hzRay, hzGrad⟩ := (sphereGradient_characterization (le_refl 2) b hb).1.1
  let Z (x : Plane) := b (sphereRadialDirection nativeCircleLoopBase x)
  have hzEq {x : Plane} (hx : x ≠ 0) : z x = Z x := by
    have hxN : 0 < ‖x‖ := norm_pos_iff.2 hx
    let θ := sphereRadialDirection nativeCircleLoopBase x
    have hR : ‖x‖ • θ.val = x := by
      change ‖x‖ • (sphereRadialDirection nativeCircleLoopBase x).val = x
      rw [sphereRadialDirection, dif_pos hx, NormedSpace.norm_smul_normalize]
    have he := hzRay ⟨‖x‖, hxN⟩ θ
    change z (‖x‖ • θ.val) = b θ at he
    rw [hR] at he
    exact he
  have hZ : MemW12 A Z Dz := by
    have hZloc := hzLoc.mono (hAK.trans hKS)
    have hM : MemW12 A z Dz := ⟨hZloc.1,
      (hzLoc.2.1 K hK hKS).mono_measure (Measure.restrict_mono_set _ hAK),
      fun i => (hzLoc.2.2 i K hK hKS).mono_measure (Measure.restrict_mono_set _ hAK)⟩
    exact hM.congr_ae ((ae_restrict_mem A.property.measurableSet).mono fun _ hx => hzEq (hKS (hAK hx)))
      (Filter.EventuallyEq.refl _ _)
  have hZE : (∫ x in A.val, hsNormSq (Dz x)) = Real.log (1 / r) *
      ∫ θ : NativeCircle, hsNormSq (fun i => sphereGradient (le_refl 2) b hb i θ) ∂unitBoundarySurface 2 := by
    have hDiff : ball (0 : Plane) 1 \ ball 0 r =ᵐ[volume] A.val := by
      filter_upwards [ae_norm_sub_ne_radius (0 : Plane) hr] with x hx
      have hne : ‖x‖ ≠ r := by simpa only [sub_zero] using hx
      change (x ∈ ball (0 : Plane) 1 \ ball 0 r) = (‖x‖ ∈ Ioo r 1)
      simp only [Set.mem_sdiff, mem_ball_zero_iff, mem_Ioo, not_lt, eq_iff_iff]
      exact ⟨fun hx' => ⟨lt_of_le_of_ne hx'.2 hne.symm, hx'.1⟩, fun hx' => ⟨hx'.2, hx'.1.le⟩⟩
    have hzInt := hZ.integrable_hsNormSq
    change IntegrableOn (fun x => hsNormSq (Dz x)) A.val at hzInt
    have hMeasure : (volume : Measure Plane).restrict (ball 0 1 \ ball 0 r) = volume.restrict A.val :=
      Measure.restrict_congr_set hDiff
    have hzInt' : IntegrableOn (fun x => hsNormSq (Dz x)) (ball (0 : Plane) 1 \ ball 0 r) := by
      change Integrable (fun x => hsNormSq (Dz x)) ((volume : Measure Plane).restrict (ball 0 1 \ ball 0 r))
      rwa [hMeasure]
    calc
      _ = ∫ x in ball (0 : Plane) 1 \ ball 0 r, hsNormSq (Dz x) :=
        congrArg (fun μ : Measure Plane => ∫ x, hsNormSq (Dz x) ∂μ) hMeasure.symm
      _ = _ := radialCollar_hs_integral hr hr₁ hzGrad hzInt'
  have hZRay (t : ℝ) (ht : 0 < t) (θ : NativeCircle) : Z (0 + t • θ.val) = b θ := by
    simp only [zero_add, Z, sphereRadialDirection_smul nativeCircleLoopBase ht, sphereRadialDirection_unit]
  let JZ : C(Icc r ((r + 1) / 2), Lp (Ambient 5) 2 (unitBoundarySurface 2)) :=
    ContinuousMap.const _ (hb.1.toLp b)
  have hJZ : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo r ((r + 1) / 2),
      ∃ hLp : MemLp (fun θ : NativeCircle => Z (0 + t • θ.val)) 2 (unitBoundarySurface 2),
        JZ ⟨t, ht.1.le, ht.2.le⟩ = hLp.toLp _ := by
    refine ae_of_all _ fun t ht => ?_
    have he : (fun θ : NativeCircle => Z (0 + t • θ.val)) = b :=
      funext (hZRay t (hr.trans ht.1))
    exact ⟨he.symm ▸ hb.1, MemLp.toLp_congr hb.1 _ (Eventually.of_forall fun θ => (congrFun he θ).symm)⟩
  have hMatch : JU ⟨r, by linarith, le_rfl⟩ = JZ ⟨r, le_rfl, by linarith⟩ :=
    hJUend.trans (hJEnd.trans hEnd)
  have hJU' : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (r / 2) r,
      ∃ hLp : MemLp (fun θ : NativeCircle => U (0 + t • θ.val)) 2 (unitBoundarySurface 2),
        JU ⟨t, ht.1.le, ht.2.le⟩ = hLp.toLp _ := by simpa only [U, zero_add, sub_zero] using hJU
  have hZ' : MemW12 ⟨{x : Plane | r < ‖x - 0‖ ∧ ‖x - 0‖ < 1},
      isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩ Z Dz := by
    simpa only [sub_zero, A, mem_Ioo] using hZ
  obtain ⟨hw, hwE⟩ := memW12_radial_trace_gluing (le_refl 2) 0 hr hr₁ U Z DU Dz hU hZ' JU JZ hJU' hJZ hMatch
  let w (x : Plane) := if ‖x - 0‖ < r then U x else Z x
  let Dw (x : Plane) (i : Fin 2) := if ‖x - 0‖ < r then DU x i else Dz x i
  refine ⟨w, Dw, hw, fun x => by simp only [w, sub_zero, U, Z], ?_⟩
  have hsum : (∫ x in ball (0 : Plane) 1, hsNormSq (Dw x)) =
      (∫ x in ball (0 : Plane) r, hsNormSq (DU x)) + ∫ x in A.val, hsNormSq (Dz x) := by
    simpa only [sub_zero, A, mem_Ioo, Dw] using hwE
  rw [hsum, hUE, hZE]

/-- Polar and affine changes of variables give the exact integral of any
integrable density of the compressed Sobolev disk and its radial collar. -/
theorem planarRadialCollar_integral {r : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (u w : Plane → Ambient 5) (b : C(NativeCircle, Ambient 5))
    (hW : ∀ x, w x = if ‖x‖ < r then u (r⁻¹ • x) else b (sphereRadialDirection nativeCircleLoopBase x))
    (F : Ambient 5 → ℝ)
    (hInt : IntegrableOn (fun x => F (w x)) (ball (0 : Plane) 1)) :
    (∫ x in ball (0 : Plane) 1, F (w x)) =
      r ^ 2 * (∫ x in ball (0 : Plane) 1, F (u x)) +
        (1 - r ^ 2) / 2 * ∫ θ : NativeCircle, F (b θ) ∂unitBoundarySurface 2 := by
  classical
  let B := ball (0 : Plane) r
  let U := ball (0 : Plane) 1
  have hBU : B ⊆ U := ball_subset_ball hr₁.le
  have hScale : (∫ x in B, F (w x)) = r ^ 2 * ∫ x in U, F (u x) := by
    have hCore : EqOn (fun x => F (w x)) (fun x => F (u (r⁻¹ • x))) B := by
      intro x hx
      change F (w x) = F (u (r⁻¹ • x))
      rw [hW x, if_pos (mem_ball_zero_iff.mp hx)]
    rw [setIntegral_congr_fun measurableSet_ball hCore]
    have hBmeas : MeasurableSet B := measurableSet_ball
    rw [← integral_indicator hBmeas]
    have hPre (x : Plane) : x ∈ B ↔ r⁻¹ • x ∈ U := by
      simp only [B, U, mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      rw [← div_eq_inv_mul, div_lt_iff₀ hr, one_mul]
    have hInd (x : Plane) : B.indicator (fun y => F (u (r⁻¹ • y))) x =
        U.indicator (fun y => F (u y)) (r⁻¹ • x) := by
      by_cases hx : x ∈ B
      · rw [indicator_of_mem hx, indicator_of_mem ((hPre x).mp hx)]
      · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hPre x).mpr h))]
    rw [show B.indicator (fun y => F (u (r⁻¹ • y))) =
        (fun x => U.indicator (fun y => F (u y)) (r⁻¹ • x)) from funext hInd]
    have hDim : Module.finrank ℝ Plane = 2 := by simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
    rw [Measure.integral_comp_smul_of_nonneg volume _ r⁻¹ (hR := inv_nonneg.mpr hr.le), hDim,
      inv_pow, inv_inv, smul_eq_mul, integral_indicator measurableSet_ball]
  let E := ∫ θ : NativeCircle, F (b θ) ∂unitBoundarySurface 2
  have hAnn : (∫ x in U \ B, F (w x)) = (1 - r ^ 2) / 2 * E := by
    have hIK : IntegrableOn (fun x => F (w x)) (U \ B) := hInt.mono_set sdiff_subset
    rw [HarmonicMaps.integral_annulus_eq_polar (by decide : 0 < 2) hr hr₁.le hIK]
    rw [← euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)]
    have hEq : EqOn (fun t : ℝ => t ^ (2 - 1 : ℕ) *
        ∫ θ : NativeCircle, F (w (0 + t • θ.val)) ∂unitBoundarySurface 2)
        (fun t => t * E) (uIcc r 1) := by
      intro t ht
      rw [uIcc_of_le hr₁.le] at ht
      have ht₀ := hr.trans_le ht.1
      simp only [Nat.reduceSub, pow_one, zero_add]
      congr 1
      apply integral_congr_ae
      apply ae_of_all
      intro θ
      have hn : ‖t • θ.val‖ = t := by
        rw [norm_smul, Real.norm_of_nonneg ht₀.le, mem_sphere_zero_iff_norm.mp θ.property, mul_one]
      change F (w (t • θ.val)) = F (b θ)
      rw [hW, hn, if_neg ht.1.not_gt, sphereRadialDirection_smul nativeCircleLoopBase ht₀,
        sphereRadialDirection_unit]
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_mul_const, integral_id]
    ring
  have hSplit := setIntegral_sdiff (t := B) measurableSet_ball hInt hBU
  linarith only [hSplit, hScale, hAnn]

end Thesis
