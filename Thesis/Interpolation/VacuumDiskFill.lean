module

public import Thesis.Foundation.QuaternionLoopSobolev
public import Thesis.Interpolation.CircleTraceDescent
public import Thesis.Interpolation.VacuumSphereFill
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! The disk filling of a trivial vacuum loop through its closed Sobolev lift. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped Matrix.Norms.Frobenius Quaternion

namespace Thesis

/-- The interval-to-circle Sobolev change of variables on one full period. -/
@[expose] def External.PeriodicAngularSobolev : Prop :=
  ∀ {q : ℕ} (v : C(UnitBoundarySphere 2, Ambient q)) (f : ℝ → Ambient q),
    EqOn f (fun t => v (circleNativeParam (t - Real.pi))) (Icc 0 (2 * Real.pi)) →
    AbsolutelyContinuousOnInterval f 0 (2 * Real.pi) →
    MemLp (deriv f) 2 (volume.restrict (Ioo 0 (2 * Real.pi))) →
    ∃ hv : MemSphereW12 (le_refl 2) v,
      (∫ θ : UnitBoundarySphere 2, hsNormSq
        (fun i => (sphereGradient (le_refl 2) v hv i) θ) ∂unitBoundarySurface 2) ≤
        ∫ t in Ioo 0 (2 * Real.pi), ‖deriv f t‖ ^ 2

private theorem absolutelyContinuousOnInterval_quaternionTuple {q : ℝ → ℍ} {a b : ℝ}
    (hq : AbsolutelyContinuousOnInterval q a b) :
    AbsolutelyContinuousOnInterval (Quaternion.linearIsometryEquivTuple ∘ q) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hq ⊢
  simpa only [Function.comp_apply, Quaternion.linearIsometryEquivTuple.isometry.dist_eq] using hq

private theorem deriv_quaternionTuple (q : ℝ → ℍ) :
    deriv (Quaternion.linearIsometryEquivTuple ∘ q) = Quaternion.linearIsometryEquivTuple ∘ deriv q := by
  funext t
  rw [← fderiv_apply_one_eq_deriv, LinearIsometryEquiv.comp_fderiv]
  rw [Function.comp_apply, ← fderiv_apply_one_eq_deriv]
  rfl

/-- A null-class Sobolev vacuum loop has a vacuum-valued disk filling with
the original circle trace and a Dirichlet bound by the angular derivative. -/
theorem exists_vacuum_disk_fill_of_null_loop (a : BulkCoefficients)
    (hAngular : External.PeriodicAngularSobolev) (hP : External.QuaternionSpherePoincare 2 (le_refl 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v₀ : Sphere3)
      (γ : Path (vacuumQuaternionProjection a v₀) (vacuumQuaternionProjection a v₀))
      (b : UnitBoundarySphere 2 → vacuum a),
      (∀ t ∈ Icc 0 (2 * Real.pi), γ (vacuumLoopParameter (2 * Real.pi) t) =
        b (circleNativeParam (t - Real.pi))) →
      AbsolutelyContinuousOnInterval (vacuumLoopTensor γ (2 * Real.pi)) 0 (2 * Real.pi) →
      MemLp (deriv (vacuumLoopTensor γ (2 * Real.pi))) 2 (volume.restrict (Ioo 0 (2 * Real.pi))) →
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) = 1 →
      ∃ (s : ℝ) (hs : s < 1) (w : Domain 2 → Ambient 5)
        (Dw : Domain 2 → HarmonicMaps.Gradient 2 5) (H : VacuumBallTrace 2 s),
        0 < s ∧ MemW12 (ballDomain (0 : Domain 2) 1) w Dw ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Domain 2) 1), frobeniusCoordinateEquiv.symm (w x) ∈ vacuum a) ∧
        RepresentsVacuumBallTrace w H ∧
        (∃ hbLp : MemLp (fun θ => frobeniusCoordinateEquiv (b θ).val) 2 (unitBoundarySurface 2),
          H ⟨1, hs.le, le_rfl⟩ = hbLp.toLp _) ∧
        (∫ x in ball (0 : Domain 2) 1, hsNormSq (Dw x)) ≤
          C * (∫ t in Ioo 0 (2 * Real.pi), ‖deriv (vacuumLoopTensor γ (2 * Real.pi)) t‖ ^ 2) := by
  obtain ⟨K, hK, hSphereFill⟩ := exists_quaternion_sphere_fill_unit (le_refl 2) hP
  obtain ⟨L, hL, hVacuumFill⟩ := exists_vacuum_ball_fill_of_quaternion_fill a
  let A := 8 * vacuumRadius a ^ 2
  have hA : 0 < A := by dsimp only [A]; positivity [vacuumRadius_pos a]
  refine ⟨L * K / A, div_pos (mul_pos hL hK) hA, ?_⟩
  intro v₀ γ b hParam hAC hD hNull
  let T := 2 * Real.pi
  have hT : 0 < T := Real.two_pi_pos
  obtain ⟨v, hv, hv₀, hv₁, hCov, hqAC, hqD, hEnergy⟩ :=
    vacuumLoop_exists_closed_sobolev_lift a v₀ γ hT hAC hD hNull
  let q (t : ℝ) := Quaternion.linearIsometryEquivTuple.symm (v t).val
  let f : ℝ → Ambient 4 := Quaternion.linearIsometryEquivTuple ∘ q
  have hfEval (t : ℝ) : f t = (v t).val := Quaternion.linearIsometryEquivTuple.apply_symm_apply _
  have hfAC : AbsolutelyContinuousOnInterval f 0 T := absolutelyContinuousOnInterval_quaternionTuple hqAC
  have hfD : MemLp (deriv f) 2 (volume.restrict (Ioo 0 T)) := by
    rw [show deriv f = Quaternion.linearIsometryEquivTuple ∘ deriv q from deriv_quaternionTuple q]
    exact Quaternion.linearIsometryEquivTuple.toContinuousLinearMap.comp_memLp' hqD
  have hfDerNorm (t : ℝ) : ‖deriv f t‖ = ‖deriv q t‖ := by
    rw [show deriv f = Quaternion.linearIsometryEquivTuple ∘ deriv q from deriv_quaternionTuple q]
    exact Quaternion.linearIsometryEquivTuple.norm_map _
  let V : C(AngularInterval, Sphere3) := ⟨fun t => v (t.val + Real.pi), hv.comp (by fun_prop)⟩
  have hEnd : V ⟨-Real.pi, le_rfl, by linarith [Real.pi_pos]⟩ =
      V ⟨Real.pi, by linarith [Real.pi_pos], le_rfl⟩ := by
    change v (-Real.pi + Real.pi) = v (Real.pi + Real.pi)
    rw [neg_add_cancel, show Real.pi + Real.pi = T by dsimp only [T]; ring, hv₀, hv₁]
  obtain ⟨l, hl⟩ := exists_circleTrace_descent V hEnd
  let l₄ : C(UnitBoundarySphere 2, Ambient 4) := ⟨fun θ => (l θ).val,
    continuous_subtype_val.comp l.continuous⟩
  have hfC : EqOn f (fun t => l₄ (circleNativeParam (t - Real.pi))) (Icc 0 T) := by
    intro t ht
    have hAngle : t - Real.pi ∈ AngularInterval := by
      have h := ht.2
      change t ≤ 2 * Real.pi at h
      exact ⟨by linarith [ht.1], by linarith⟩
    rw [hfEval]
    change (v t).val = (l (circleNativeParam (t - Real.pi))).val
    rw [hl ⟨t - Real.pi, hAngle⟩]
    change (v t).val = (v (t - Real.pi + Real.pi)).val
    rw [sub_add_cancel]
  obtain ⟨hL4, hL4E⟩ := hAngular l₄ f hfC hfAC hfD
  have hSphere : ∀ᵐ θ ∂unitBoundarySurface 2, ‖l₄ θ‖ = 1 := ae_of_all _ fun θ => by
    change ‖(l θ).val‖ = 1
    simpa only [mem_sphere, dist_zero_right] using (l θ).property
  obtain ⟨s, hs, u, Du, J, hs₀, hu, huSphere, huTrace, huEnd, huEnergy⟩ :=
    hSphereFill l₄ hL4 hSphere
  obtain ⟨w, Dw, H, hw, hwVac, hwTrace, hwEnd, hwEnergy⟩ :=
    hVacuumFill (le_refl 2) l hL4.1 hs J hu huSphere huTrace huEnd
  have hMatch (θ : UnitBoundarySphere 2) : cover a (l θ) = (b θ).val := by
    obtain ⟨s, rfl⟩ := circleNativeParam_closed_surjective θ
    rw [hl s]
    apply Subtype.ext
    have hs₀ : s.val + Real.pi ∈ Icc 0 T :=
      ⟨by linarith [s.property.1], by dsimp only [T]; linarith [s.property.2]⟩
    have hEq := congrFun hCov (s.val + Real.pi)
    change (cover a (v (s.val + Real.pi)) : Tensor) =
      ((γ (vacuumLoopParameter T (s.val + Real.pi))).val : Tensor) at hEq
    rw [hParam _ hs₀, add_sub_cancel_right] at hEq
    exact hEq
  have hh : (fun θ => frobeniusCoordinateEquiv (cover a (l θ))) =
      fun θ : UnitBoundarySphere 2 => frobeniusCoordinateEquiv (b θ).val :=
    funext fun θ => congrArg frobeniusCoordinateEquiv (hMatch θ)
  rw [hh] at hwEnd
  refine ⟨s, hs, w, Dw, H, hs₀, hw, hwVac, hwTrace, hwEnd, ?_⟩
  have hQL := (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).1
    (intervalIntegrable_sq_norm_of_memLp_two hT.le hD)
  have hqL := (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).1
    (intervalIntegrable_sq_norm_of_memLp_two hT.le hqD)
  have hEL : A * (∫ t in Ioo 0 T, ‖deriv q t‖ ^ 2) ≤
      ∫ t in Ioo 0 T, ‖deriv (vacuumLoopTensor γ T) t‖ ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hqL.const_mul A) hQL hEnergy
  have hMin := huEnergy.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hK.le)
  have hqBound : (∫ t in Ioo 0 T, ‖deriv q t‖ ^ 2) ≤
      (∫ t in Ioo 0 T, ‖deriv (vacuumLoopTensor γ T) t‖ ^ 2) / A :=
    (le_div_iff₀ hA).2 (by rw [mul_comm]; exact hEL)
  have hFBound : quaternionBoundaryEnergy (le_refl 2) l₄ hL4 ≤ ∫ t in Ioo 0 T, ‖deriv q t‖ ^ 2 := by
    simpa only [quaternionBoundaryEnergy, hsNormSq, hfDerNorm] using hL4E
  calc
    _ ≤ L * (∫ x in ball (0 : Domain 2) 1, hsNormSq (Du x)) := hwEnergy
    _ ≤ L * (K * quaternionBoundaryEnergy (le_refl 2) l₄ hL4) := mul_le_mul_of_nonneg_left hMin hL.le
    _ ≤ L * (K * (∫ t in Ioo 0 T, ‖deriv q t‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFBound hK.le) hL.le
    _ ≤ L * (K * ((∫ t in Ioo 0 T, ‖deriv (vacuumLoopTensor γ T) t‖ ^ 2) / A)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqBound hK.le) hL.le
    _ = _ := by ring

end Thesis
