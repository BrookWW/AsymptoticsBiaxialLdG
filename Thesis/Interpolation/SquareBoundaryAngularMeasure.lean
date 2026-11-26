module

public import Thesis.Interpolation.SquareCircleTrace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The change of variables from the four physical sides to the angular period. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped Matrix.Norms.Frobenius

namespace Thesis

def unitSquareSideAngleCenter (i : Fin 2) (upper : Bool) : ℝ :=
  if i = 0 then (if upper then 0 else Real.pi) else (if upper then Real.pi/2 else -(Real.pi/2))

def unitSquareSideAngleSign (i : Fin 2) (upper : Bool) : ℝ :=
  if i = 0 then (if upper then 1 else -1) else (if upper then -1 else 1)

/-- The standard coordinate on a given square side expressed as a polar angle. -/
def unitSquareSideAngle (i : Fin 2) (upper : Bool) (s : ℝ) : ℝ :=
  unitSquareSideAngleCenter i upper + unitSquareSideAngleSign i upper * Real.arctan s

theorem unitSquareSideAngleSign_eq (i : Fin 2) (upper : Bool) :
    unitSquareSideAngleSign i upper = 1 ∨ unitSquareSideAngleSign i upper = -1 := by
  cases upper <;> fin_cases i <;> simp [unitSquareSideAngleSign]

private theorem continuous_unitSquareSideParameter (i : Fin 2) (upper : Bool) :
    Continuous (unitSquareSideParameter i upper) := by
  let s (t : ℝ) := (projIcc (-1 : ℝ) 1 (by norm_num) t).val
  have hs : Continuous s := continuous_subtype_val.comp continuous_projIcc
  let f (t : ℝ) := EuclideanSpace.single (0 : Fin 1) (s t)
  have he (t : ℝ) : f t = s t • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
    ext j
    fin_cases j
    simp [f]
  have hf : Continuous f := (hs.smul continuous_const).congr (fun t => (he t).symm)
  have hF : Continuous (fun t => unitCellFaceSlice i (f t) (if upper then 1 else -1)) := by
    simp only [unitCellFaceSlice_coordinates]
    split_ifs <;> fun_prop
  exact hF.subtype_mk _

private theorem sidePoint_coordinates (i : Fin 2) (upper : Bool) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    (unitSquareSideParameter i upper s).val =
      if i = 0 then WithLp.toLp 2 ![if upper then (1 : ℝ) else -1, s]
      else WithLp.toLp 2 ![s, if upper then (1 : ℝ) else -1] := by
  let v : Domain 1 := EuclideanSpace.single 0 s
  have hv : v 0 = s := by simp [v]
  rw [← hv, unitSquareSideParameter_eq i upper v (hv.symm ▸ hs), unitCellFaceSlice_coordinates]

private theorem norm_sidePoint (i : Fin 2) (upper : Bool) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    ‖(unitSquareSideParameter i upper s).val‖ = Real.sqrt (1+s^2) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity), EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
    sidePoint_coordinates i upper hs]
  cases upper <;> fin_cases i <;> simp <;> ring

/-- Each arctangent chart reaches the exact original radial square
boundary point, retaining the original coordinate normalization. -/
theorem unitSquareCircle_symm_sideAngle (i : Fin 2) (upper : Bool) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    unitSquareCircleHomeomorph.symm (circleNativeParam (unitSquareSideAngle i upper s)) =
      unitSquareSideParameter i upper s := by
  let x := unitSquareSideParameter i upper s
  have hX := (mem_unitSquareBoundary_iff _).mp x.property
  have hN : ‖x.val‖ = Real.sqrt (1+s^2) := norm_sidePoint i upper hs
  apply unitSquareCircleHomeomorph.injective
  rw [unitSquareCircleHomeomorph.apply_symm_apply]
  apply Subtype.ext
  change (circleNativeParam (unitSquareSideAngle i upper s)).val = coordinateCubeToBall x.val
  rw [coordinateCubeToBall, hX, hN, circleNativeParam_coe]
  change WithLp.toLp 2 ![Real.cos (unitSquareSideAngle i upper s), Real.sin (unitSquareSideAngle i upper s)] =
    (1 / Real.sqrt (1+s^2)) • (unitSquareSideParameter i upper s).val
  rw [sidePoint_coordinates i upper hs]
  ext j
  cases upper <;> fin_cases i <;> fin_cases j <;>
    simp [unitSquareSideAngle,unitSquareSideAngleCenter,unitSquareSideAngleSign,Real.cos_add,Real.sin_add,
      Real.cos_neg,Real.sin_neg,Real.cos_arctan,Real.sin_arctan] <;>
    simp [div_eq_mul_inv,mul_comm]

theorem unitSquareSideAngle_hasDerivAt (i : Fin 2) (upper : Bool) (s : ℝ) :
    HasDerivAt (unitSquareSideAngle i upper)
      (unitSquareSideAngleSign i upper * (1+s^2)⁻¹) s :=
  ((Real.hasDerivAt_arctan' s).const_mul (unitSquareSideAngleSign i upper)).const_add
    (unitSquareSideAngleCenter i upper)

theorem image_unitSquareSideAngle (i : Fin 2) (upper : Bool) :
    unitSquareSideAngle i upper '' Ioo (-1 : ℝ) 1 =
      Ioo (unitSquareSideAngleCenter i upper - Real.pi/4) (unitSquareSideAngleCenter i upper + Real.pi/4) := by
  rcases unitSquareSideAngleSign_eq i upper with h | h
  · have hF : unitSquareSideAngle i upper = fun s => unitSquareSideAngleCenter i upper + Real.arctan s := by
      funext s
      rw [unitSquareSideAngle,h,one_mul]
    have hC : Continuous (fun s => unitSquareSideAngleCenter i upper + Real.arctan s) :=
      continuous_const.add Real.continuous_arctan
    have hM : StrictMono (fun s => unitSquareSideAngleCenter i upper + Real.arctan s) :=
      fun a b hab => by dsimp only; linarith only [Real.arctan_strictMono hab]
    rw [hF,hC.image_Ioo_of_strictMono hM]
    simp [Real.arctan_neg,Real.arctan_one,sub_eq_add_neg]
  · have hF : unitSquareSideAngle i upper = fun s => unitSquareSideAngleCenter i upper - Real.arctan s := by
      funext s
      rw [unitSquareSideAngle,h,neg_one_mul,sub_eq_add_neg]
    have hc : Continuous (fun s => unitSquareSideAngleCenter i upper - Real.arctan s) :=
      continuous_const.sub Real.continuous_arctan
    have ha : StrictAnti (fun s => unitSquareSideAngleCenter i upper - Real.arctan s) :=
      fun a b hab => sub_lt_sub_left (Real.arctan_strictMono hab) _
    rw [hF, hc.continuousOn.image_Ioo_of_strictAntiOn (by norm_num) (ha.strictAntiOn _)]
    simp [Real.arctan_neg,Real.arctan_one,sub_eq_add_neg]

def squareBoundaryUnclamped {E : Type*} [TopologicalSpace E]
    (p : C(UnitSquareBoundary,E)) (t : ℝ) : E :=
  p (unitSquareCircleHomeomorph.symm (circleNativeParam t))

theorem continuous_squareBoundaryUnclamped {E : Type*} [TopologicalSpace E]
    (p : C(UnitSquareBoundary,E)) : Continuous (squareBoundaryUnclamped p) :=
  p.continuous.comp (unitSquareCircleHomeomorph.symm.continuous.comp continuous_circleNativeParam)

theorem squareBoundaryUnclamped_periodic {E : Type*} [TopologicalSpace E]
    (p : C(UnitSquareBoundary,E)) : Function.Periodic (squareBoundaryUnclamped p) (2*Real.pi) := by
  intro t
  have hC : circleNativeParam (t+2*Real.pi) = circleNativeParam t := by
    apply Subtype.ext
    rw [circleNativeParam_coe,circleNativeParam_coe,Real.cos_add_two_pi,Real.sin_add_two_pi]
  exact congrArg (fun z => p (unitSquareCircleHomeomorph.symm z)) hC

theorem squareBoundaryAngular_eq_unclamped {E : Type*} [TopologicalSpace E]
    (p : C(UnitSquareBoundary,E)) {t : ℝ} (ht : t ∈ Icc 0 (2*Real.pi)) :
    squareBoundaryAngular p t = squareBoundaryUnclamped p (t-Real.pi) := by
  have hπ : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have ht' : t/(2*Real.pi) ∈ Icc 0 1 := ⟨div_nonneg ht.1 hπ.le,(div_le_one hπ).mpr ht.2⟩
  have hParam : (vacuumLoopParameter (2*Real.pi) t).val = t/(2*Real.pi) :=
    congrArg Subtype.val (projIcc_of_mem zero_le_one ht')
  rw [squareBoundaryAngular,squareBoundaryUnclamped,nativeCircleLoopParam_apply,hParam]
  have hCancel : 2*Real.pi * (t/(2*Real.pi)) = t := by field_simp
  rw [hCancel]

theorem intervalIntegral_eq_setIntegral_Ioo {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, f t) = ∫ t in Ioo a b, f t := by
  rw [intervalIntegral.integral_of_le hab, Measure.restrict_congr_set Ioo_ae_eq_Ioc]

private theorem squareBoundary_unclamped_integral_sector (p : C(UnitSquareBoundary,ℝ)) (hp : ∀ x, 0 ≤ p x)
    (i : Fin 2) (upper : Bool) :
    (∫ t in (unitSquareSideAngleCenter i upper - Real.pi/4)..(unitSquareSideAngleCenter i upper + Real.pi/4),
      squareBoundaryUnclamped p t) ≤ ∫ s in Ioo (-1 : ℝ) 1, p (unitSquareSideParameter i upper s) := by
  have hc := continuous_squareBoundaryUnclamped p
  let k := unitSquareSideAngleCenter i upper
  let f := unitSquareSideAngle i upper
  let f' (s : ℝ) := unitSquareSideAngleSign i upper * (1+s^2)⁻¹
  have hdf (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1) : HasDerivWithinAt f (f' s) (Ioo (-1 : ℝ) 1) s :=
    (unitSquareSideAngle_hasDerivAt i upper s).hasDerivWithinAt
  have hfi : Function.Injective f := by
    intro x y hxy
    apply Real.arctan_injective
    change unitSquareSideAngleCenter i upper + unitSquareSideAngleSign i upper * Real.arctan x =
      unitSquareSideAngleCenter i upper + unitSquareSideAngleSign i upper * Real.arctan y at hxy
    have hne : unitSquareSideAngleSign i upper ≠ 0 := by
      rcases unitSquareSideAngleSign_eq i upper with h | h <;> simp [h]
    exact mul_left_cancel₀ hne (add_left_cancel hxy)
  have hdom : k-Real.pi/4 ≤ k+Real.pi/4 := by linarith only [Real.pi_pos]
  rw [intervalIntegral_eq_setIntegral_Ioo hdom, ← image_unitSquareSideAngle,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hdf hfi.injOn]
  have hDen : Continuous (fun s : ℝ => 1+s^2) := continuous_const.add (continuous_id.pow 2)
  have hF' : Continuous f' := continuous_const.mul
    (hDen.inv₀ fun s => ne_of_gt (by positivity : 0 < (1 : ℝ)+s^2))
  have hSide : Continuous (fun s => p (unitSquareSideParameter i upper s)) :=
    p.continuous.comp (continuous_unitSquareSideParameter i upper)
  apply setIntegral_mono_on ((hF'.abs.smul (hc.comp
    (continuous_const.add (continuous_const.mul Real.continuous_arctan)))).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (hSide.integrableOn_Icc.mono_set Ioo_subset_Icc_self) measurableSet_Ioo
  intro s hs
  have hCoeff : |f' s| ≤ 1 := by
    have hA : |unitSquareSideAngleSign i upper| = 1 := by
      rcases unitSquareSideAngleSign_eq i upper with h | h <;> simp [h]
    have hD : 0 < 1+s^2 := by positivity
    dsimp only [f']
    rw [abs_mul,hA,one_mul,abs_of_nonneg (inv_nonneg.mpr hD.le)]
    exact inv_le_one_of_one_le₀ (by linarith only [sq_nonneg s])
  change |f' s| * p (unitSquareCircleHomeomorph.symm (circleNativeParam (unitSquareSideAngle i upper s))) ≤ _
  rw [unitSquareCircle_symm_sideAngle i upper (Ioo_subset_Icc_self hs)]
  exact (mul_le_mul_of_nonneg_right hCoeff (hp _)).trans_eq (one_mul _)

/-- The four sides cover one full angular integral of a periodic function. -/
theorem integral_twoPi_eq_squareSideAngle_sectors {f : ℝ → ℝ}
    (hPeriodic : Function.Periodic f (2*Real.pi))
    (hf : ∀ a b, IntervalIntegrable f volume a b) :
    (∫ t in (-Real.pi)..Real.pi, f t) =
      ∑ i : Fin 2, ∑ upper : Bool,
        ∫ t in (unitSquareSideAngleCenter i upper - Real.pi/4)..(unitSquareSideAngleCenter i upper + Real.pi/4),
          f t := by
  have hPeriod := hPeriodic.intervalIntegral_add_eq (-Real.pi) (-(3*Real.pi/4))
  rw [show -Real.pi + 2*Real.pi = Real.pi by ring,
    show -(3*Real.pi/4)+2*Real.pi = 5*Real.pi/4 by ring] at hPeriod
  rw [hPeriod]
  let a := -(3*Real.pi/4)
  let b := -(Real.pi/4)
  let c := Real.pi/4
  let d := 3*Real.pi/4
  let e := 5*Real.pi/4
  have hAB := intervalIntegral.integral_add_adjacent_intervals (hf a b) (hf b c)
  have hAC := intervalIntegral.integral_add_adjacent_intervals (hf a c) (hf c d)
  have hAD := intervalIntegral.integral_add_adjacent_intervals (hf a d) (hf d e)
  change (∫ t in a..e, f t) = _
  rw [← hAD, ← hAC, ← hAB,Fin.sum_univ_two]
  simp only [Fintype.sum_bool,unitSquareSideAngleCenter,Fin.isValue,ite_true,ite_false,
    one_ne_zero,Bool.false_eq_true]
  have h₁ : -(Real.pi/2)-Real.pi/4 = a := by dsimp only [a]; ring
  have h₂ : -(Real.pi/2)+Real.pi/4 = b := by dsimp only [b]; ring
  have h₃ : Real.pi - Real.pi/4 = d := by dsimp only [d]; ring
  have h₄ : Real.pi + Real.pi/4 = e := by dsimp only [e]; ring
  have h₅ : Real.pi/2 - Real.pi/4 = c := by dsimp only [c]; ring
  have h₆ : Real.pi/2 + Real.pi/4 = d := by dsimp only [d]; ring
  rw [h₁,h₂,h₃,h₄,h₅,h₆,zero_sub,zero_add]
  change _ = ((∫ t in b..c, f t) + (∫ t in d..e, f t)) +
    ((∫ t in c..d, f t) + (∫ t in a..b, f t))
  abel

/-- Angular integration of a nonnegative square boundary density is at
most the sum of the original four coordinate integrals. -/
theorem squareBoundaryAngularMeasure : External.SquareBoundaryAngularMeasure := by
  refine ⟨1,one_pos,?_⟩
  intro p hp
  have hπ : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hAng :
      (∫ t in Ioo 0 (2*Real.pi), squareBoundaryAngular p t) =
        ∫ t in (-Real.pi)..Real.pi, squareBoundaryUnclamped p t := by
    rw [← intervalIntegral_eq_setIntegral_Ioo hπ.le]
    calc
      _ = ∫ t in (0 : ℝ)..(2*Real.pi), squareBoundaryUnclamped p (t-Real.pi) :=
        intervalIntegral.integral_congr (fun t ht =>
          squareBoundaryAngular_eq_unclamped p (uIcc_of_le hπ.le ▸ ht))
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_right,zero_sub,show 2*Real.pi-Real.pi = Real.pi by ring]
  rw [hAng,integral_twoPi_eq_squareSideAngle_sectors (squareBoundaryUnclamped_periodic p)
    (fun a b => (continuous_squareBoundaryUnclamped p).intervalIntegrable a b),one_mul]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun upper _ =>
    squareBoundary_unclamped_integral_sector p hp i upper

end Thesis
