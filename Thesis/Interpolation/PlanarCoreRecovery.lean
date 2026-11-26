module

public import Thesis.Interpolation.VacuumDiskCollar
public import Thesis.MeasureGeometry.PlanarSobolevLowerBound
public import Thesis.Foundation.QuaternionLoopCompetitors
public import Thesis.Foundation.QuaternionSplittingEnergy
import Thesis.MeasureGeometry.PlanarRadialCollar
import HarmonicMaps.Analysis.AffineBallMeasure
import StratificationTheory.Foundation.AffineDomainSobolevPullback
import StratificationTheory.Foundation.RadialPiecewiseProperties
import StratificationTheory.Foundation.RadialSobolevPullback

/-! A penalized planar core with its literal Sobolev vacuum boundary. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ENNReal Matrix.Norms.Frobenius

namespace Thesis

private theorem exists_ambient_unitCore (b : C(NativeCircle, Ambient 5))
    (hb : MemSphereW12 (le_refl 2) b) {B : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ θ, ‖b θ‖ ≤ B) :
    ∃ (u : Plane → Ambient 5) (Du : Plane → HarmonicMaps.Gradient 2 5) (H : VacuumBallTrace 2 (1 / 2)),
      MemW12 (ballDomain (0 : Plane) 1) u Du ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖u x‖ ≤ B) ∧
      RepresentsVacuumBallTrace u H ∧ H ⟨1, by norm_num, le_rfl⟩ = hb.1.toLp _ := by
  obtain ⟨u, Du, hu, huB, hRay, _⟩ := exists_ambient_affine_collar_of_sphere (le_refl 2)
    b hb (ae_of_all _ hBound) (0 : Ambient 5) (by simpa only [norm_zero] using hB)
    (h := 1 / 2) (by norm_num) le_rfl
  let H : VacuumBallTrace 2 (1 / 2) := ⟨fun t => ((t.val - 1 / 2) / (1 / 2)) • hb.1.toLp _,
    ((continuous_subtype_val.sub continuous_const).div_const _).smul continuous_const⟩
  refine ⟨u, Du, H, hu, huB, ?_, ?_⟩
  · unfold RepresentsVacuumBallTrace
    refine ae_of_all _ fun t ht => ?_
    have ht' : t ∈ Ioo (1 - (1 / 2 : ℝ)) 1 := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
      exact ht
    have hEq : (fun θ : NativeCircle => u (t • θ.val)) =
        ((t - 1 / 2) / (1 / 2)) • (b : NativeCircle → Ambient 5) := by
      funext θ
      rw [hRay t ht' θ, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, sub_zero, zero_add]
      rfl
    let A : MemLp (((t - 1 / 2) / (1 / 2)) • (b : NativeCircle → Ambient 5)) 2 (unitBoundarySurface 2) :=
      hb.1.const_smul _
    let B' : MemLp (fun θ : NativeCircle => u (t • θ.val)) 2 (unitBoundarySurface 2) :=
      A.ae_eq (Eventually.of_forall (congrFun hEq.symm))
    refine ⟨B', ?_⟩
    exact (MemLp.toLp_const_smul _ hb.1).symm.trans (MemLp.toLp_congr A B'
      (Eventually.of_forall (congrFun hEq.symm)))
  · change (((1 : ℝ) - 1 / 2) / (1 / 2)) • hb.1.toLp _ = _
    norm_num

/-- Any continuous Sobolev vacuum loop has a one-core penalized recovery,
with the exact angular logarithmic coefficient. The core cost depends
only on the fixed angular datum and the material. -/
theorem exists_planarSobolev_core_recovery (a : BulkCoefficients)
    (b : C(NativeCircle, vacuum a))
    (hb : MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (b θ).val)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε < 1 →
      ∃ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5),
        MemW12 (ballDomain (0 : Plane) 1) w Dw ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖w x‖ ≤ Real.sqrt 2 * vacuumRadius a) ∧
        (∀ r ≥ ε, ∀ θ : NativeCircle, w (r • θ.val) = frobeniusCoordinateEquiv (b θ).val) ∧
        RepresentsVacuumBallTrace w (ContinuousMap.const (Icc ε 1) (hb.1.toLp _)) ∧
        planarWeakEnergy a ε w Dw 1 =
          (1 / 2 : ℝ) * ambientBoundaryEnergy (le_refl 2)
            (fun θ => frobeniusCoordinateEquiv (b θ).val) hb * Real.log (1 / ε) + C := by
  let B := Real.sqrt 2 * vacuumRadius a
  let β : C(NativeCircle, Ambient 5) :=
    ⟨fun θ => frobeniusCoordinateEquiv (b θ).val,
      frobeniusCoordinateEquiv.continuous.comp (continuous_subtype_val.comp b.continuous)⟩
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (vacuumRadius_pos a).le
  have hβ (θ : NativeCircle) : ‖β θ‖ ≤ B := by
    change ‖frobeniusCoordinateEquiv (b θ).val‖ ≤ B
    rw [frobeniusCoordinateEquiv.norm_map]
    exact (vacuum_norm (b θ).property).le
  obtain ⟨u, Du, H, hu, huB, hH, Hend⟩ := exists_ambient_unitCore β hb hB hβ
  let C := planarWeakEnergy a 1 u Du 1
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (by norm_num) (integral_nonneg fun _ => hsNormSq_nonneg _))
    (mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => bulkPotential_nonneg a _))
  refine ⟨C, hC, ?_⟩
  intro ε hε hε₁
  obtain ⟨w, Dw, hw, hValue, hDir⟩ :=
    exists_planarSobolev_radialCollar hε hε₁ β hb hu (by norm_num) H hH Hend
  have hInner : ∀ᵐ x ∂volume.restrict (ball (0 : Plane) ε), ‖u (ε⁻¹ • x)‖ ≤ B := by
    simpa only [zero_add, sub_zero, one_div, inv_inv] using
      ae_affineBall (0 : Plane) 0 (t := ε⁻¹) (inv_pos.2 hε) 1 huB
  have hwB : ∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖w x‖ ≤ B := by
    have h := ae_radial_piecewise_property 0 hε hε₁ (fun x : Plane => u (ε⁻¹ • x))
      (fun x : Plane => β (sphereRadialDirection nativeCircleLoopBase x)) (fun x => ‖x‖ ≤ B)
      hInner (ae_of_all _ fun x => hβ (sphereRadialDirection nativeCircleLoopBase x))
    simpa only [sub_zero, ← hValue] using h
  have hRay (r : ℝ) (hr : r ≥ ε) (θ : NativeCircle) : w (r • θ.val) = β θ := by
    have hPos := hε.trans_le hr
    have hN : ‖r • θ.val‖ = r := by
      rw [norm_smul, Real.norm_of_nonneg hPos.le, mem_sphere_zero_iff_norm.1 θ.property, mul_one]
    rw [hValue, hN, if_neg hr.not_gt, sphereRadialDirection_smul nativeCircleLoopBase hPos, sphereRadialDirection_unit]
  refine ⟨w, Dw, hw, hwB, hRay, ?_, ?_⟩
  · unfold RepresentsVacuumBallTrace
    refine ae_of_all _ fun r hr => ?_
    have he : (fun θ : NativeCircle => w (r • θ.val)) = β := funext (hRay r hr.1.le)
    have hLp : MemLp (fun θ : NativeCircle => w (r • θ.val)) 2 (unitBoundarySurface 2) := he.symm ▸ hb.1
    exact ⟨hLp, MemLp.toLp_congr hb.1 hLp (Eventually.of_forall fun θ => (congrFun he θ).symm)⟩
  · letI : IsFiniteMeasure (volume.restrict (ball (0 : Plane) 1)) :=
      isFiniteMeasure_restrict.2 measure_ball_ne_top
    have hMeas : AEStronglyMeasurable w (volume.restrict (ball (0 : Plane) 1)) := hw.2.1.aestronglyMeasurable
    have hPot := integrable_planarCoordinateBulkPotential_of_bound a hMeas hwB
    have hChange := planarRadialCollar_integral hε hε₁ u w β hValue (planarCoordinateBulkPotential a) hPot
    have hZero : (∫ θ : NativeCircle, planarCoordinateBulkPotential a (β θ) ∂unitBoundarySurface 2) = 0 := by
      have hZ (θ : NativeCircle) : planarCoordinateBulkPotential a (β θ) = 0 := by
        change bulkPotential a (frobeniusCoordinateEquiv.symm (frobeniusCoordinateEquiv (b θ).val)) = 0
        rw [frobeniusCoordinateEquiv.symm_apply_apply]
        exact (bulkPotential_eq_zero_iff a _).2 (b θ).property
      simp only [hZ, integral_zero]
    rw [hZero, mul_zero, add_zero] at hChange
    unfold planarWeakEnergy
    rw [hDir, hChange]
    have hCancel : ε⁻¹ ^ 2 * ε ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow]
    rw [← mul_assoc, hCancel, one_mul]
    dsimp only [ambientBoundaryEnergy, C, planarWeakEnergy, hsNormSq, β, ContinuousMap.coe_mk]
    simp only [inv_one, one_pow, one_mul]
    ring

/-- A based Sobolev vacuum loop gives the same native round-circle datum,
retaining its class and no more than its original angular energy. -/
theorem exists_nativeVacuumCircle_of_H1_path (a : BulkCoefficients) (hPolar : External.PeriodicAngularSobolev)
    {A : vacuum a} (p : Path A A) (hp : VacuumLoopH1 p) :
    ∃ (b : C(NativeCircle, vacuum a)) (hBase : A = b nativeCircleLoopBase)
      (hb : MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (b θ).val)),
      (nativeCircleLoop b).cast hBase hBase = p ∧
      (1 / 2 : ℝ) * ambientBoundaryEnergy (le_refl 2) (fun θ => frobeniusCoordinateEquiv (b θ).val) hb ≤
        vacuumLoopEnergy p := by
  obtain ⟨b, hBase, hMatch⟩ := exists_nativeCircleLoop_descent p
  let T := 2 * Real.pi
  have hT : 0 < T := Real.two_pi_pos
  let γ (t : ℝ) := p (vacuumLoopParameter T t)
  have hParam : EqOn γ (fun t => b (circleNativeParam (t - Real.pi))) (Icc 0 T) := by
    intro t ht
    have hEq := congrArg (fun l : Path A A => l (vacuumLoopParameter T t)) hMatch
    have hDiv : t / T ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hT.le, (div_le_one hT).2 ht.2⟩
    have hRaw : (vacuumLoopParameter T t).val = t / T :=
      congrArg Subtype.val (projIcc_of_mem zero_le_one hDiv)
    change nativeCircleLoop b (vacuumLoopParameter T t) = γ t at hEq
    rw [nativeCircleLoop_apply, hRaw] at hEq
    change b (circleNativeParam (T * (t / T) - Real.pi)) = γ t at hEq
    rw [mul_comm T, div_mul_cancel₀ _ hT.ne'] at hEq
    exact hEq.symm
  obtain ⟨hb, hE⟩ := exists_memSphereW12_of_vacuumAngular a hPolar b γ hParam hp.1 hp.2
  refine ⟨b, hBase, hb, hMatch, ?_⟩
  have hEnergy : vacuumLoopEnergy p =
      (1 / 2 : ℝ) * ∫ t in Ioo 0 T, ‖deriv (vacuumLoopTensor p T) t‖ ^ 2 := by
    unfold vacuumLoopEnergy
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_Ioc_eq_integral_Ioo, integral_const_mul]
  rw [hEnergy]
  exact mul_le_mul_of_nonneg_left hE (by norm_num)

/-- The optimal light representative admits a recovery with the
coefficient from the actual covering class. -/
theorem exists_lightVacuumCircle_recovery (a : BulkCoefficients)
    (hPolar : External.PeriodicAngularSobolev) (v : Sphere3)
    {g : QuaternionGroup 2} (hg : IsLightQuaternion g) :
    ∃ (b : C(NativeCircle, vacuum a)) (hBase : vacuumQuaternionProjection a v = b nativeCircleLoopBase),
      nativeVacuumLoopWord a b v hBase = g ∧
      MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (b θ).val) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε < 1 →
        ∃ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5),
          MemW12 (ballDomain (0 : Plane) 1) w Dw ∧
          (∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖w x‖ ≤ Real.sqrt 2 * vacuumRadius a) ∧
          (∀ r ≥ ε, ∀ θ : NativeCircle, w (r • θ.val) = frobeniusCoordinateEquiv (b θ).val) ∧
          planarWeakEnergy a ε w Dw 1 ≤ kappaStar a * Real.log (1 / ε) + C := by
  obtain ⟨p, hWord, hp, hEnergy⟩ := exists_vacuumLoop_light_competitor a v hg
  obtain ⟨b, hBase, hb, hMatch, hE⟩ := exists_nativeVacuumCircle_of_H1_path a hPolar p hp
  obtain ⟨C, hC, hRec⟩ := exists_planarSobolev_core_recovery a b hb
  have hWord' : nativeVacuumLoopWord a b v hBase = g := by
    change vacuumFundamentalGroupEquiv a v
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop b).cast hBase hBase))) = g
    rw [hMatch]
    exact hWord
  refine ⟨b, hBase, hWord', hb, C, hC, ?_⟩
  intro ε hε hε₁
  obtain ⟨w, Dw, hw, hwB, hRay, _, hRec⟩ := hRec hε hε₁
  refine ⟨w, Dw, hw, hwB, hRay, hRec.le.trans ?_⟩
  have hLog : 0 ≤ Real.log (1 / ε) := Real.log_nonneg ((one_le_div₀ hε).2 hε₁.le)
  exact add_le_add (mul_le_mul_of_nonneg_right (hE.trans_eq hEnergy) hLog) le_rfl

/-- The native planar graph keeps its actual values under a positive
similarity, with exact two-dimensional penalized energy. -/
theorem planarRecovery_affine (a : BulkCoefficients) (c : Plane) {R ε : ℝ} (hR : 0 < R)
    {u : Plane → Ambient 5} {Du : Plane → HarmonicMaps.Gradient 2 5}
    (hu : MemW12 (ballDomain (0 : Plane) 1) u Du) :
    let w : Plane → Ambient 5 := fun x => u (R⁻¹ • (x - c))
    ∃ D : Plane → HarmonicMaps.Gradient 2 5, MemW12 (ballDomain c R) w D ∧
      (∀ P : Ambient 5 → Prop, (∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), P (u x)) →
        ∀ᵐ x ∂volume.restrict (ball c R), P (w x)) ∧
      ((1 / 2 : ℝ) * (∫ x in ball c R, hsNormSq (D x)) +
        ε⁻¹ ^ 2 * ∫ x in ball c R, planarCoordinateBulkPotential a (w x)) =
          planarWeakEnergy a (ε / R) u Du 1 := by
  intro w
  let ζ := ε / R
  let F (x : Plane) := (0 : Plane) + (R⁻¹ : ℝ) • (x - c)
  let D (x : Plane) (i : Fin 2) := R⁻¹ • Du (F x) i
  let U := ballDomain (0 : Plane) 1
  have hPre : F ⁻¹' U.val = ball c R := by
    ext x
    change (0 : Plane) + R⁻¹ • (x - c) ∈ ball (0 : Plane) 1 ↔ x ∈ ball c R
    rw [zero_add, mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le), mem_ball, dist_eq_norm,
      mul_comm, ← div_eq_mul_inv, div_lt_one hR]
  have hU : (volume : Measure Plane) U.val ≠ ⊤ := measure_ball_ne_top
  obtain ⟨hw, _, hDir, _, hVal⟩ := memW12_affine_preimage_energy (Ω := U) hU hu 0 c
    (r := R⁻¹) (inv_pos.2 hR)
  let V : OpenDomain 2 := ⟨F ⁻¹' U.val, U.property.preimage (affineBall_contDiff (0 : Plane) c R⁻¹).continuous⟩
  have hDom : V = ballDomain c R := Subtype.ext hPre
  have hF : u ∘ F = w := funext fun x => by
    change u ((0 : Plane) + R⁻¹ • (x - c)) = u (R⁻¹ • (x - c))
    rw [zero_add]
  have huD : MemW12 (ballDomain c R) w D := hDom ▸ (hF ▸ (show MemW12 V (u ∘ F) D from hw))
  have hwP (P : Ambient 5 → Prop) (hP : ∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), P (u x)) :
      ∀ᵐ x ∂volume.restrict (ball c R), P (w x) := by
    have h := hVal P hP
    change ∀ᵐ x ∂volume.restrict (F ⁻¹' U.val), P ((u ∘ F) x) at h
    exact hPre ▸ (hF ▸ h)
  have hwE : (∫ x in ball c R, hsNormSq (D x)) =
      ∫ x in ball (0 : Plane) 1, hsNormSq (Du x) := by
    change (∫ x in F ⁻¹' U.val, hsNormSq (D x)) =
      (R⁻¹) ^ (2 - ((2 : ℕ) : ℤ)) * (∫ x in U.val, hsNormSq (Du x)) at hDir
    rw [hPre, show (2 : ℤ) - ((2 : ℕ) : ℤ) = 0 by norm_num, zpow_zero, one_mul] at hDir
    exact hDir
  have hBulk : (∫ x in ball c R, planarCoordinateBulkPotential a (w x)) =
      R ^ 2 * ∫ x in ball (0 : Plane) 1, planarCoordinateBulkPotential a (u x) := by
    simpa only [one_div, inv_inv, zero_add, smul_eq_mul, inv_pow, F, w, Function.comp_apply] using
      integral_affineBall (0 : Plane) c (t := R⁻¹) (inv_pos.2 hR) 1 (planarCoordinateBulkPotential a ∘ u)
  refine ⟨D, huD, hwP, ?_⟩
  rw [hwE, hBulk]
  have hPower : ε⁻¹ ^ 2 * R ^ 2 = ζ⁻¹ ^ 2 := by
    unfold ζ
    rw [inv_div, div_eq_mul_inv, mul_pow, mul_comm]
  rw [← mul_assoc, hPower]
  rfl

/-- The actual light recovery at any center and radius with the native
two-dimensional scaling and the same angular data on all outer slices. -/
theorem exists_lightVacuumCircle_recovery_on_ball (a : BulkCoefficients)
    (hPolar : External.PeriodicAngularSobolev) (v : Sphere3)
    {g : QuaternionGroup 2} (hg : IsLightQuaternion g) :
    ∃ (b : C(NativeCircle, vacuum a)) (hBase : vacuumQuaternionProjection a v = b nativeCircleLoopBase),
      nativeVacuumLoopWord a b v hBase = g ∧
      MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (b θ).val) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Plane) {R ε : ℝ}, 0 < ε → ε < R →
        ∃ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5),
          MemW12 (ballDomain c R) w Dw ∧
          (∀ᵐ x ∂volume.restrict (ball c R), ‖w x‖ ≤ Real.sqrt 2 * vacuumRadius a) ∧
          (∀ r ≥ ε, ∀ θ : NativeCircle, w (c + r • θ.val) = frobeniusCoordinateEquiv (b θ).val) ∧
          ((1 / 2 : ℝ) * (∫ x in ball c R, hsNormSq (Dw x)) +
            ε⁻¹ ^ 2 * ∫ x in ball c R, planarCoordinateBulkPotential a (w x)) ≤
              kappaStar a * Real.log (R / ε) + C := by
  obtain ⟨b, hBase, hWord, hb, C, hC, hRec⟩ := exists_lightVacuumCircle_recovery a hPolar v hg
  refine ⟨b, hBase, hWord, hb, C, hC, ?_⟩
  intro c R ε hε hεR
  have hR := hε.trans hεR
  let ζ := ε / R
  have hζ : 0 < ζ := div_pos hε hR
  have hζ₁ : ζ < 1 := (div_lt_one hR).2 hεR
  obtain ⟨u, Du, hu, huB, hRay, hEnergy⟩ := hRec hζ hζ₁
  obtain ⟨D, hw, hVal, hE⟩ := planarRecovery_affine a c (ε := ε) hR hu
  let w (x : Plane) := u (R⁻¹ • (x - c))
  have hwRay (r : ℝ) (hr : r ≥ ε) (θ : NativeCircle) :
      w (c + r • θ.val) = frobeniusCoordinateEquiv (b θ).val := by
    change u (R⁻¹ • (c + r • θ.val - c)) = _
    rw [add_sub_cancel_left, smul_smul, mul_comm R⁻¹, ← div_eq_mul_inv]
    exact hRay (r / R) ((div_le_div_iff_of_pos_right hR).2 hr) θ
  have hLog : Real.log (1 / ζ) = Real.log (R / ε) := by rw [one_div, show ζ⁻¹ = R / ε from inv_div _ _]
  refine ⟨w, D, hw, hVal (fun z => ‖z‖ ≤ Real.sqrt 2 * vacuumRadius a) huB, hwRay,
    hE.le.trans (hEnergy.trans_eq ?_)⟩
  rw [hLog]

/-- Trivial and light words have literal disk recoveries with their own
splitting coefficient and fixed angular boundary data. -/
theorem exists_lightOrTrivialVacuumCore_on_ball (a : BulkCoefficients)
    (hPolar : External.PeriodicAngularSobolev) (v : Sphere3)
    {g : QuaternionGroup 2} (hg : g = 1 ∨ IsLightQuaternion g) :
    ∃ (b : C(NativeCircle, vacuum a)) (hBase : vacuumQuaternionProjection a v = b nativeCircleLoopBase),
      nativeVacuumLoopWord a b v hBase = g ∧
      MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (b θ).val) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Plane) {R ε : ℝ}, 0 < ε → ε < R →
        ∃ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5),
          MemW12 (ballDomain c R) w Dw ∧
          (∀ᵐ x ∂volume.restrict (ball c R), ‖w x‖ ≤ Real.sqrt 2 * vacuumRadius a) ∧
          (∀ r ≥ ε, ∀ θ : NativeCircle, w (c + r • θ.val) = frobeniusCoordinateEquiv (b θ).val) ∧
          ((1 / 2 : ℝ) * (∫ x in ball c R, hsNormSq (Dw x)) +
            ε⁻¹ ^ 2 * ∫ x in ball c R, planarCoordinateBulkPotential a (w x)) ≤
              vacuumSplittingCost a v g * Real.log (R / ε) + C := by
  rcases hg with rfl | hLight
  · let A := vacuumQuaternionProjection a v
    let b := ContinuousMap.const NativeCircle A
    let V := frobeniusCoordinateEquiv A.val
    have hB : MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (b θ).val) :=
      memSphereW12_smooth_slice (le_refl 2) (f := fun _ => V) contDiff_const 0 1
    refine ⟨b, rfl, nativeVacuumLoopWord_const a v A rfl, hB, 0, le_rfl, ?_⟩
    intro c R ε _ _
    letI : IsFiniteMeasure (volume.restrict (ballDomain c R).val) :=
      isFiniteMeasure_restrict.2 (show (volume : Measure Plane) (ball c R) ≠ ⊤ from measure_ball_ne_top)
    let w : Plane → Ambient 5 := fun _ => V
    let Dw : Plane → HarmonicMaps.Gradient 2 5 := fun _ _ => 0
    have hWeak : HasWeakGradient (ballDomain c R) w Dw := by
      simpa only [coordinateDerivative, w, fderiv_fun_const, Pi.zero_apply, zero_apply, Dw] using
        hasWeakGradient_of_contDiff (ballDomain c R) (f := w) contDiff_const
    have hw : MemW12 (ballDomain c R) w Dw := ⟨hWeak, memLp_const V, fun _ => MemLp.zero⟩
    have hv : ‖V‖ ≤ Real.sqrt 2 * vacuumRadius a := by
      rw [show ‖V‖ = ‖A.val‖ from frobeniusCoordinateEquiv.norm_map _]
      exact (vacuum_norm A.property).le
    have hP : planarCoordinateBulkPotential a V = 0 := by
      change bulkPotential a (frobeniusCoordinateEquiv.symm (frobeniusCoordinateEquiv A.val)) = 0
      rw [frobeniusCoordinateEquiv.symm_apply_apply]
      exact (bulkPotential_eq_zero_iff a _).2 A.property
    refine ⟨w, Dw, hw, ae_of_all _ fun _ => hv, fun _ _ _ => rfl, ?_⟩
    simp [vacuumSplittingCost_one, w, Dw, hsNormSq, hP]
  · rw [vacuumSplittingCost_light a v hLight]
    exact exists_lightVacuumCircle_recovery_on_ball a hPolar v hLight

end Thesis
