module

public import Thesis.Interpolation.VacuumDiskFill
public import Thesis.Interpolation.QuaternionSphereSobolevLift
import HarmonicMaps.Analysis.AffineEnergyScaling
import HarmonicMaps.Analysis.AnnularPolarIntegral
import HarmonicMaps.Analysis.SobolevAECongruence
import HarmonicMaps.SobolevRestriction
import StratificationTheory.Compactness.RadialTraceDilation
import StratificationTheory.Foundation.RadialPiecewiseTrace
import StratificationTheory.Foundation.RadialPiecewiseProperties
import StratificationTheory.Foundation.RadialTraceCompatibility
import StratificationTheory.Frozen.RadialTraceGluing

/-! A disk filling with the original boundary map on a full radial collar. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped Matrix.Norms.Frobenius

namespace Thesis

/-- The native circle energy of a continuous vacuum loop is bounded by
the angular energy of its original Frobenius tensor representative. -/
theorem exists_memSphereW12_of_vacuumAngular (a : BulkCoefficients)
    (hAngular : External.PeriodicAngularSobolev) (b : C(UnitBoundarySphere 2, vacuum a))
    (γ : ℝ → vacuum a)
    (hParam : EqOn γ (fun t => b (circleNativeParam (t - Real.pi))) (Icc 0 (2 * Real.pi)))
    (hAC : AbsolutelyContinuousOnInterval (fun t => ((γ t).val : Tensor)) 0 (2 * Real.pi))
    (hD : MemLp (deriv (fun t => ((γ t).val : Tensor))) 2 (volume.restrict (Ioo 0 (2 * Real.pi)))) :
    ∃ hb : MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (b θ).val),
      vacuumSphereGradientEnergy (le_refl 2) b hb ≤
        ∫ t in Ioo 0 (2 * Real.pi), ‖deriv (fun t => ((γ t).val : Tensor)) t‖ ^ 2 := by
  let T := 2 * Real.pi
  let f (t : ℝ) := ((γ t).val : Tensor)
  let L := frobeniusCoordinateEquiv.toContinuousLinearMap.comp traceFreeSymmetricPartCLM
  let R := symmetricTraceless.subtypeL.comp frobeniusCoordinateEquiv.symm.toContinuousLinearMap
  let z (t : ℝ) := L (f t)
  let B : C(UnitBoundarySphere 2, Ambient 5) := ⟨fun θ => frobeniusCoordinateEquiv (b θ).val,
    frobeniusCoordinateEquiv.continuous.comp (continuous_subtype_val.comp b.continuous)⟩
  have hL (s : S0) : L (s : Tensor) = frobeniusCoordinateEquiv s := by
    change frobeniusCoordinateEquiv (traceFreeSymmetricPart (s : Tensor)) = _
    rw [traceFreeSymmetricPart_of_S0]
  have hf : R ∘ z = f := by
    funext t
    change R (L ((γ t).val : Tensor)) = _
    rw [hL]
    change ((frobeniusCoordinateEquiv.symm (frobeniusCoordinateEquiv (γ t).val) : S0) : Tensor) = _
    rw [frobeniusCoordinateEquiv.symm_apply_apply]
  have hLNorm (x : Tensor) : ‖L x‖ ≤ ‖x‖ := by
    change ‖frobeniusCoordinateEquiv (traceFreeSymmetricPart x)‖ ≤ ‖x‖
    rw [frobeniusCoordinateEquiv.norm_map]
    exact norm_traceFreeSymmetricPart_le x
  have hACz : AbsolutelyContinuousOnInterval z 0 T := by
    rw [absolutelyContinuousOnInterval_iff] at hAC ⊢
    intro ε hε
    obtain ⟨δ, hδ, hCrit⟩ := hAC ε hε
    refine ⟨δ, hδ, fun I hI hSmall => lt_of_le_of_lt ?_ (hCrit I hI hSmall)⟩
    apply Finset.sum_le_sum
    intro j _
    simp only [z, dist_eq_norm, ← map_sub]
    exact hLNorm _
  have hDer : deriv z = L ∘ deriv f := by
    funext t
    by_cases ht : DifferentiableAt ℝ f t
    · exact (L.hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt).deriv
    · have hzt : ¬ DifferentiableAt ℝ z t := fun hz => ht <| hf ▸ R.differentiableAt.comp t hz
      calc
        deriv z t = 0 := deriv_zero_of_not_differentiableAt hzt
        _ = L 0 := (L.map_zero).symm
        _ = (L ∘ deriv f) t := congrArg L (deriv_zero_of_not_differentiableAt ht).symm
  have hDz : MemLp (deriv z) 2 (volume.restrict (Ioo 0 T)) := hDer.symm ▸ L.comp_memLp' hD
  have hEq : EqOn z (fun t => B (circleNativeParam (t - Real.pi))) (Icc 0 T) := by
    intro t ht
    change L (((γ t).val : Tensor)) = frobeniusCoordinateEquiv (b _).val
    rw [hL, hParam ht]
  obtain ⟨hb, hE⟩ := hAngular B z hEq hACz hDz
  refine ⟨hb, hE.trans ?_⟩
  apply integral_mono_ae (hDz.integrable_norm_pow (by norm_num)) (hD.integrable_norm_pow (by norm_num))
  exact ae_of_all _ fun t => by
    change ‖deriv z t‖ ^ 2 ≤ ‖deriv f t‖ ^ 2
    rw [show deriv z t = L (deriv f t) from congrFun hDer t]
    exact pow_le_pow_left₀ (norm_nonneg _) (hLNorm _) 2

theorem extend_vacuumBallTrace {n : ℕ} (hn : 2 ≤ n)
    {u : Domain n → Ambient 5} {D : Domain n → HarmonicMaps.Gradient n 5}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u D)
    {b : ℝ} (hb : b < 1) (K : VacuumBallTrace n b) (hK : RepresentsVacuumBallTrace u K) :
    ∃ J : VacuumBallTrace n (1 / 2), RepresentsVacuumBallTrace u J ∧
      J ⟨1, by norm_num, le_rfl⟩ = K ⟨1, hb.le, le_rfl⟩ := by
  let a : ℝ := 1 / 2
  let m := max a b
  have hm : m < 1 := max_lt (by norm_num) hb
  let r := (m + 1) / 2
  have hm_r : m < r := by dsimp only [r]; linarith
  have ha_r : a < r := (le_max_left _ _).trans_lt hm_r
  have hb_r : b < r := (le_max_right _ _).trans_lt hm_r
  have hr : r < 1 := by dsimp only [r]; linarith
  obtain ⟨H, hH, _⟩ := ambient_radial_trace_existsUnique hn hu.to_memW12Loc
    (c := (0 : Domain n)) (show 0 < a by norm_num) ha_r (closedBall_subset_ball hr)
  have hK₀ : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo b 1,
      ∃ htLp : MemLp (fun θ : UnitBoundarySphere n => u (0 + t • θ.val)) 2 (unitBoundarySurface n),
        K ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp _ := by
    simpa only [zero_add, RepresentsVacuumBallTrace] using hK
  let K' := K.comp ⟨fun t : Icc r 1 => (⟨t.val, hb_r.le.trans t.property.1, t.property.2⟩ : Icc b 1),
    continuous_subtype_val.subtype_mk _⟩
  have hK' : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo r 1,
      ∃ htLp : MemLp (fun θ : UnitBoundarySphere n => u (0 + t • θ.val)) 2 (unitBoundarySurface n),
        K' ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp _ := by
    filter_upwards [hK₀] with t ht htr
    exact ht ⟨hb_r.trans htr.1, htr.2⟩
  have hAgree := radial_representatives_eq_on_closed_overlap (u := u) (0 : Domain n)
    hm_r (le_max_left a b) (le_refl r) (le_max_right a b) hr.le H K hH hK₀ ⟨r, hm_r.le, le_rfl⟩
  have hMatch : H ⟨r, ha_r.le, le_rfl⟩ = K' ⟨r, le_rfl, hr.le⟩ := hAgree
  obtain ⟨J, _, hRight, hRaw⟩ := exists_radial_trace_piecewise (0 : Domain n) (unitBoundarySurface n)
    (show 0 < a by norm_num) ha_r hr u u H K' hH hK' hMatch
  refine ⟨J, ?_, hRight ⟨1, hr.le, le_rfl⟩⟩
  simpa only [ite_self, zero_add, RepresentsVacuumBallTrace] using hRaw

private theorem collar_hs_integral
    {D : Domain 2 → HarmonicMaps.Gradient 2 5}
    {g : Fin 2 → Lp (Ambient 5) 2 (unitBoundarySurface 2)}
    (hRay : ∀ (ρ : PositiveRadius) (i : Fin 2),
      (fun θ : UnitBoundarySphere 2 => ρ.val • D (ρ.val • θ.val) i) =ᵐ[unitBoundarySurface 2] g i)
    (hInt : IntegrableOn (fun x => hsNormSq (D x))
      (ball (0 : Domain 2) 1 \ ball 0 (1 / 2))) :
    (∫ x in ball (0 : Domain 2) 1 \ ball 0 (1 / 2), hsNormSq (D x)) ≤
      ∫ θ : UnitBoundarySphere 2, hsNormSq (fun i => g i θ) ∂unitBoundarySurface 2 := by
  let E := ∫ θ : UnitBoundarySphere 2, hsNormSq (fun i => g i θ) ∂unitBoundarySurface 2
  have hE : 0 ≤ E := integral_nonneg fun _ => hsNormSq_nonneg _
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hInterval : (1 / 2 : ℝ) ≤ 1 := by norm_num
  rw [HarmonicMaps.integral_annulus_eq_polar (by decide : 0 < 2) hhalf hInterval hInt]
  rw [← euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)]
  have hEq : EqOn (fun t : ℝ => t ^ (2 - 1 : ℕ) *
        ∫ θ : UnitBoundarySphere 2, hsNormSq (D (0 + t • θ.val)) ∂unitBoundarySurface 2)
      (fun t => t⁻¹ * E) (uIcc (1 / 2) 1) := by
    intro t ht
    rw [uIcc_of_le hInterval] at ht
    have ht₀ := hhalf.trans_le ht.1
    have hAll := ae_all_iff.2 (hRay ⟨t, ht₀⟩)
    have hDensity : (fun θ : UnitBoundarySphere 2 => hsNormSq (D (t • θ.val))) =ᵐ[unitBoundarySurface 2]
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
  rw [intervalIntegral.integral_congr hEq]
  have hInv : ContinuousOn (fun t : ℝ => t⁻¹ * E) (uIcc (1 / 2) 1) := by
    apply (continuousOn_id.inv₀ _).mul continuousOn_const
    intro t ht
    rw [uIcc_of_le hInterval] at ht
    exact (hhalf.trans_le ht.1).ne'
  refine (intervalIntegral.integral_mono_on hInterval hInv.intervalIntegrable
    (intervalIntegrable_const (c := 2 * E)) ?_).trans_eq ?_
  · intro t ht
    exact mul_le_mul_of_nonneg_right ((inv_le_iff_one_le_mul₀ (hhalf.trans_le ht.1)).2
      (by linarith [ht.1])) hE
  · rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring

/-- Compress an existing disk filling and append the degree-zero extension
of its continuous Sobolev circle trace. The collar has the exact pointwise
boundary values and adds at most the circle Dirichlet energy. -/
theorem exists_vacuumDisk_with_radial_collar (a : BulkCoefficients)
    (base : UnitBoundarySphere 2) (b : C(UnitBoundarySphere 2, vacuum a))
    (hb : MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (b θ).val))
    {u : Domain 2 → Ambient 5} {Du : Domain 2 → HarmonicMaps.Gradient 2 5}
    (hu : MemW12 (ballDomain (0 : Domain 2) 1) u Du)
    (hVac : ∀ᵐ x ∂volume.restrict (ball (0 : Domain 2) 1),
      frobeniusCoordinateEquiv.symm (u x) ∈ vacuum a)
    {s : ℝ} (hs : s < 1) (H : VacuumBallTrace 2 s) (hH : RepresentsVacuumBallTrace u H)
    (hEnd : H ⟨1, hs.le, le_rfl⟩ = hb.1.toLp _) :
    ∃ (w : Domain 2 → Ambient 5) (Dw : Domain 2 → HarmonicMaps.Gradient 2 5),
      MemW12 (ballDomain (0 : Domain 2) 1) w Dw ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain 2) 1), frobeniusCoordinateEquiv.symm (w x) ∈ vacuum a) ∧
      (∀ x, 1 / 2 ≤ ‖x‖ → w x = frobeniusCoordinateEquiv (b (sphereRadialDirection base x)).val) ∧
      RepresentsVacuumBallTrace w (ContinuousMap.const (Icc (1 / 2 : ℝ) 1) (hb.1.toLp _)) ∧
      (∫ x in ball (0 : Domain 2) 1, hsNormSq (Dw x)) ≤
        (∫ x in ball (0 : Domain 2) 1, hsNormSq (Du x)) + vacuumSphereGradientEnergy (le_refl 2) b hb := by
  let B (θ : UnitBoundarySphere 2) := frobeniusCoordinateEquiv (b θ).val
  let r : ℝ := 1 / 2
  have hr : 0 < r := by norm_num [r]
  have hr₁ : r < 1 := by norm_num [r]
  let U (x : Domain 2) := u ((2 : ℝ) • x)
  let DU (x : Domain 2) (i : Fin 2) := (2 : ℝ) • Du ((2 : ℝ) • x) i
  have hU : MemW12 (ballDomain 0 r) U DU := by
    simpa only [HarmonicMaps.ballAffine, zero_add, sub_zero, r, U, DU] using
      hu.affinePullback_ball (t := 2) (by norm_num)
  have hUVac : ∀ᵐ x ∂volume.restrict (ball (0 : Domain 2) r),
      frobeniusCoordinateEquiv.symm (U x) ∈ vacuum a := by
    simpa only [zero_add, sub_zero, U, r] using
      ae_affineBall (0 : Domain 2) 0 (t := 2) (by norm_num) 1 hVac
  have hUE : (∫ x in ball (0 : Domain 2) r, hsNormSq (DU x)) =
      ∫ x in ball (0 : Domain 2) 1, hsNormSq (Du x) := by
    have hpow : (2 : ℤ) - ((2 : ℕ) : ℤ) = 0 := by norm_num
    have he : HarmonicMaps.dirichletEnergy DU ((ballDomain 0 r).val) =
        HarmonicMaps.dirichletEnergy Du ((ballDomain 0 1).val) := by
      simpa only [zero_add, sub_zero, r, DU, ballDomain, hpow, zpow_zero,
        ENNReal.ofReal_one, one_mul] using
        (dirichletEnergy_affineBall (0 : Domain 2) 0 (t := 2) (by norm_num) 1 Du)
    rw [HarmonicMaps.dirichletEnergy_eq_ofReal_integral hU.integrable_hsNormSq,
      HarmonicMaps.dirichletEnergy_eq_ofReal_integral hu.integrable_hsNormSq] at he
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => hsNormSq_nonneg _)
      (integral_nonneg fun _ => hsNormSq_nonneg _)).1 he
  obtain ⟨J, hJ, hJEnd⟩ := extend_vacuumBallTrace (le_refl 2) hu hs H hH
  have hJ₀ : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (1 / 2) 1,
      ∃ hLp : MemLp (fun θ : UnitBoundarySphere 2 => u (0 + t • θ.val)) 2 (unitBoundarySurface 2),
        J ⟨t, ht.1.le, ht.2.le⟩ = hLp.toLp _ := by
    simpa only [zero_add, RepresentsVacuumBallTrace] using hJ
  obtain ⟨JU, hJU, hJUend⟩ := Compactness.exists_dilated_inner_radial_trace
    (unitBoundarySurface 2) u (0 : Domain 2) (s := 1) (t := 2) (lo := r)
    (by norm_num) (by norm_num) hr (by norm_num [r]) le_rfl le_rfl J hJ₀
  let A : OpenDomain 2 := ⟨{x | ‖x‖ ∈ Ioo r 1}, isOpen_Ioo.preimage continuous_norm⟩
  let K : Set (Domain 2) := closedBall 0 1 \ ball 0 r
  have hK : IsCompact K := (isCompact_closedBall _ _).diff isOpen_ball
  have hKS : K ⊆ ({0}ᶜ : Set (Domain 2)) := by
    intro x hx he
    have hx₀ : x = 0 := he
    exact hx.2 (by rw [hx₀]; exact mem_ball_self hr)
  have hAK : A.val ⊆ K := by
    intro x hx
    exact ⟨(mem_closedBall_zero_iff.2 hx.2.le), fun hball => hx.1.not_ge (le_of_lt (mem_ball_zero_iff.1 hball))⟩
  obtain ⟨z, Dz, hzLoc, hzRay, hzGrad⟩ := (sphereGradient_characterization (le_refl 2) B hb).1.1
  let Z (x : Domain 2) := B (sphereRadialDirection base x)
  have hzEq {x : Domain 2} (hx : x ≠ 0) : z x = Z x := by
    have hxN : 0 < ‖x‖ := norm_pos_iff.2 hx
    let θ := sphereRadialDirection base x
    have hR : ‖x‖ • θ.val = x := by
      change ‖x‖ • (sphereRadialDirection base x).val = x
      rw [sphereRadialDirection, dif_pos hx, NormedSpace.norm_smul_normalize]
    have he := hzRay ⟨‖x‖, hxN⟩ θ
    change z (‖x‖ • θ.val) = B θ at he
    rw [hR] at he
    exact he
  have hZ : MemW12 A Z Dz := by
    have hZloc := hzLoc.mono (hAK.trans hKS)
    have hM : MemW12 A z Dz := ⟨hZloc.1,
      (hzLoc.2.1 K hK hKS).mono_measure (Measure.restrict_mono_set _ hAK),
      fun i => (hzLoc.2.2 i K hK hKS).mono_measure (Measure.restrict_mono_set _ hAK)⟩
    exact hM.congr_ae ((ae_restrict_mem A.property.measurableSet).mono fun _ hx => hzEq (hKS (hAK hx)))
      (Filter.EventuallyEq.refl _ _)
  have hZE : (∫ x in A.val, hsNormSq (Dz x)) ≤ vacuumSphereGradientEnergy (le_refl 2) b hb := by
    have hDiff : ball (0 : Domain 2) 1 \ ball 0 r =ᵐ[volume] A.val := by
      filter_upwards [ae_norm_sub_ne_radius (0 : Domain 2) hr] with x hx
      have hne : ‖x‖ ≠ r := by simpa only [sub_zero] using hx
      change (x ∈ ball (0 : Domain 2) 1 \ ball 0 r) = (‖x‖ ∈ Ioo r 1)
      simp only [Set.mem_sdiff, mem_ball_zero_iff, mem_Ioo, not_lt, eq_iff_iff]
      exact ⟨fun hx' => ⟨lt_of_le_of_ne hx'.2 hne.symm, hx'.1⟩, fun hx' => ⟨hx'.2, hx'.1.le⟩⟩
    have hzInt := hZ.integrable_hsNormSq
    change IntegrableOn (fun x => hsNormSq (Dz x)) A.val at hzInt
    have hMeasure : (volume : Measure (Domain 2)).restrict (ball 0 1 \ ball 0 r) = volume.restrict A.val :=
      Measure.restrict_congr_set hDiff
    have hzInt' : IntegrableOn (fun x => hsNormSq (Dz x)) (ball (0 : Domain 2) 1 \ ball 0 r) := by
      change Integrable (fun x => hsNormSq (Dz x)) ((volume : Measure (Domain 2)).restrict (ball 0 1 \ ball 0 r))
      exact Eq.mpr (congrArg (fun μ : Measure (Domain 2) => Integrable (fun x => hsNormSq (Dz x)) μ)
        hMeasure) (show Integrable (fun x => hsNormSq (Dz x)) (volume.restrict A.val) from hzInt)
    have he := collar_hs_integral hzGrad hzInt'
    calc
      _ = ∫ x in ball (0 : Domain 2) 1 \ ball 0 r, hsNormSq (Dz x) :=
        congrArg (fun μ : Measure (Domain 2) => ∫ x, hsNormSq (Dz x) ∂μ) hMeasure.symm
      _ ≤ _ := he
  have hZRay (t : ℝ) (ht : 0 < t) (θ : UnitBoundarySphere 2) : Z (0 + t • θ.val) = B θ := by
    simp only [zero_add, Z, sphereRadialDirection_smul base ht, sphereRadialDirection_unit]
  let JZ : C(Icc r ((r + 1) / 2), Lp (Ambient 5) 2 (unitBoundarySurface 2)) :=
    ContinuousMap.const _ (hb.1.toLp B)
  have hJZ : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo r ((r + 1) / 2),
      ∃ hLp : MemLp (fun θ : UnitBoundarySphere 2 => Z (0 + t • θ.val)) 2 (unitBoundarySurface 2),
        JZ ⟨t, ht.1.le, ht.2.le⟩ = hLp.toLp _ := by
    refine ae_of_all _ fun t ht => ?_
    have he : (fun θ : UnitBoundarySphere 2 => Z (0 + t • θ.val)) = B :=
      funext (hZRay t (hr.trans ht.1))
    have hB : MemLp B 2 (unitBoundarySurface 2) := hb.1
    exact ⟨he.symm ▸ hB, MemLp.toLp_congr hB _ (Eventually.of_forall fun θ => (congrFun he θ).symm)⟩
  have hMatch : JU ⟨r, by linarith, le_rfl⟩ = JZ ⟨r, le_rfl, by linarith⟩ :=
    hJUend.trans (hJEnd.trans hEnd)
  have hJU' : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (r / 2) r,
      ∃ hLp : MemLp (fun θ : UnitBoundarySphere 2 => U (0 + t • θ.val)) 2 (unitBoundarySurface 2),
        JU ⟨t, ht.1.le, ht.2.le⟩ = hLp.toLp _ := by simpa only [U, zero_add, sub_zero] using hJU
  have hZ' : MemW12 ⟨{x : Domain 2 | r < ‖x - 0‖ ∧ ‖x - 0‖ < 1},
      isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm⟩ Z Dz := by
    simpa only [sub_zero, A, mem_Ioo] using hZ
  obtain ⟨hw, hwE⟩ := memW12_radial_trace_gluing (le_refl 2) 0 hr hr₁ U Z DU Dz hU hZ' JU JZ hJU' hJZ hMatch
  let w (x : Domain 2) := if ‖x - 0‖ < r then U x else Z x
  let Dw (x : Domain 2) (i : Fin 2) := if ‖x - 0‖ < r then DU x i else Dz x i
  have hWZ (x : Domain 2) (hx : r ≤ ‖x‖) : w x = Z x := by simp only [w, sub_zero, if_neg hx.not_gt]
  have hWV := ae_radial_piecewise_property 0 hr hr₁ U Z (fun x => frobeniusCoordinateEquiv.symm x ∈ vacuum a)
    hUVac (ae_of_all _ fun x => by
      change frobeniusCoordinateEquiv.symm (frobeniusCoordinateEquiv (b (sphereRadialDirection base x)).val) ∈ vacuum a
      rw [frobeniusCoordinateEquiv.symm_apply_apply]
      exact (b (sphereRadialDirection base x)).property)
  refine ⟨w, Dw, hw, hWV, hWZ, ?_, ?_⟩
  · change RepresentsVacuumBallTrace w (ContinuousMap.const (Icc r 1) (hb.1.toLp B))
    unfold RepresentsVacuumBallTrace
    refine ae_of_all _ fun t ht => ?_
    have he : (fun θ : UnitBoundarySphere 2 => w (t • θ.val)) = B := by
      funext θ
      have ht₀ := hr.trans ht.1
      have hn : ‖t • θ.val‖ = t := by
        rw [norm_smul, Real.norm_of_nonneg ht₀.le, mem_sphere_zero_iff_norm.1 θ.property, mul_one]
      have hNr : r ≤ ‖t • θ.val‖ := by rw [hn]; exact ht.1.le
      rw [hWZ _ hNr]
      simpa only [zero_add] using hZRay t ht₀ θ
    have hB : MemLp B 2 (unitBoundarySurface 2) := hb.1
    exact ⟨he.symm ▸ hB, MemLp.toLp_congr hB _ (Eventually.of_forall fun θ => (congrFun he θ).symm)⟩
  · have hsum : (∫ x in ball (0 : Domain 2) 1, hsNormSq (Dw x)) =
        (∫ x in ball (0 : Domain 2) r, hsNormSq (DU x)) + ∫ x in A.val, hsNormSq (Dz x) := by
      simpa only [sub_zero, A, mem_Ioo, Dw] using hwE
    exact hsum.le.trans (add_le_add hUE.le hZE)

end Thesis
