module

public import Thesis.Interpolation.PlanarPairCircleCompression

/-! The actual outer peripheral word of the two-half-plane reference map. -/

public section

noncomputable section

open Metric Set StratificationTheory
open scoped Topology

namespace Thesis

theorem planarPairCircleComplex_re (z : NativeCircle) : (planarPairCircleComplex z).re = z.val 0 := by
  change (Complex.orthonormalBasisOneI.repr.symm z.val).re = _
  rw [Complex.orthonormalBasisOneI_repr_symm_apply]
  simp

private theorem planarPairCircleComplex_param (t : ℝ) :
    planarPairCircleComplex (circleNativeParam t) = Complex.exp ((t : ℂ)*Complex.I) := by
  change MeasureGeometry.complexPlaneCoordinates.symm (circleNativeParam t).val = _
  rw [MeasureGeometry.circleNativeParam_val_eq_complexExp,LinearIsometryEquiv.symm_apply_apply]

private theorem circleNativeParam_add_two_pi_pair (t : ℝ) :
    circleNativeParam (t+2*Real.pi) = circleNativeParam t := by
  apply Subtype.ext
  rw [circleNativeParam_coe,circleNativeParam_coe,Real.cos_add_two_pi,Real.sin_add_two_pi]

private theorem planarPairHalfCircle_angle (left : Bool) (t : ℝ)
    (h : if left then Real.cos t ≤ 0 else 0 ≤ Real.cos t) :
    planarPairHalfCircle left (circleNativeParam t) = circleNativeParam (2*t) := by
  have h' : if left then (planarPairCircleComplex (circleNativeParam t)).re ≤ 0
      else 0 ≤ (planarPairCircleComplex (circleNativeParam t)).re := by
    rw [planarPairCircleComplex_re]
    have he : (circleNativeParam t).val 0 = Real.cos t := by rw [circleNativeParam_coe]; rfl
    rw [he]
    exact h
  apply Subtype.ext
  apply MeasureGeometry.complexPlaneCoordinates.symm.injective
  change planarPairCircleComplex (planarPairHalfCircle left (circleNativeParam t)) =
    planarPairCircleComplex (circleNativeParam (2*t))
  rw [planarPairHalfCircle_eq_square left _ h',planarPairCircleComplex_param,planarPairCircleComplex_param,
    pow_two,← Complex.exp_add]
  push_cast
  congr 1
  ring

private def planarPairQuarterTurnCircle : C(NativeCircle,NativeCircle) :=
  MeasureGeometry.nativeCircle_unitComplex
    (Complex.exp (((Real.pi/2 : ℝ) : ℂ)*Complex.I))
    (MeasureGeometry.norm_complex_circle_exp _) false

private theorem planarPairQuarterTurnCircle_param (t : ℝ) :
    planarPairQuarterTurnCircle (circleNativeParam t) = circleNativeParam (Real.pi/2+t) := by
  apply Subtype.ext
  apply MeasureGeometry.complexPlaneCoordinates.symm.injective
  change MeasureGeometry.complexPlaneCoordinates.symm
    (planarPairQuarterTurnCircle (circleNativeParam t)).val =
    planarPairCircleComplex (circleNativeParam (Real.pi/2+t))
  rw [planarPairQuarterTurnCircle,MeasureGeometry.nativeCircle_unitComplex_val,
    LinearIsometryEquiv.symm_apply_apply]
  simp only [Bool.false_eq_true,ite_false]
  change Complex.exp (((Real.pi/2 : ℝ) : ℂ)*Complex.I) *
    planarPairCircleComplex (circleNativeParam t) = _
  rw [planarPairCircleComplex_param,planarPairCircleComplex_param,← Complex.exp_add]
  push_cast
  congr 1
  ring

theorem planarPairCoreCenter_first (i : Fin 2) :
    planarPairCoreCenter i 0 = if i = 0 then -1/2 else 1/2 := by
  rw [planarPairCoreCenter,PiLp.single_apply,if_pos rfl]

theorem planarPairCoreCenter_norm (i : Fin 2) : ‖planarPairCoreCenter i‖ = 1/2 := by
  rw [planarPairCoreCenter,PiLp.norm_single]
  split <;> norm_num

private theorem sphereRadialDirection_complex_re (x : Plane) (hx : x ≠ 0) :
    (planarPairCircleComplex (sphereRadialDirection nativeCircleLoopBase x)).re =
      ‖x‖⁻¹ * x 0 := by
  rw [planarPairCircleComplex_re,sphereRadialDirection,dif_pos hx]
  rfl

/-- The two genuine peripheral loops on a round outer circle, with the
centers moved toward zero by the given parameter. -/
@[expose] def planarPairOuterFamily {a : BulkCoefficients}
    (R : ℝ) (inner : Fin 2 → C(NativeCircle,vacuum a)) (t : unitInterval) (z : NativeCircle) :
    vacuum a :=
  if z.val 0 ≤ 0 then
    inner 0 (planarPairHalfCircle true
      (sphereRadialDirection nativeCircleLoopBase (R • z.val-(1-t.val) • planarPairCoreCenter 0)))
  else
    inner 1 (planarPairHalfCircle false
      (sphereRadialDirection nativeCircleLoopBase (R • z.val-(1-t.val) • planarPairCoreCenter 1)))

private theorem planarPairOuterFamily_arg_ne {R : ℝ} (hR : 1/2 < R)
    (i : Fin 2) (t : unitInterval) (z : NativeCircle) :
    R • z.val-(1-t.val) • planarPairCoreCenter i ≠ 0 := by
  intro h
  have hN := congrArg (fun x : Plane => ‖x‖) (sub_eq_zero.mp h)
  have hR' : 0 < R := (by norm_num : 0 < (1/2 : ℝ)).trans hR
  rw [norm_smul,norm_smul,Real.norm_of_nonneg hR'.le,
    Real.norm_of_nonneg (sub_nonneg.mpr t.property.2),mem_sphere_zero_iff_norm.mp z.property,
    planarPairCoreCenter_norm,mul_one] at hN
  nlinarith only [hR,hN,t.property.1]

private theorem continuous_planarPairOuterFamily {a : BulkCoefficients}
    {R : ℝ} (hR : 1/2 < R) (inner : Fin 2 → C(NativeCircle,vacuum a))
    (A : vacuum a) (hA : ∀ i, A = inner i nativeCircleLoopBase) :
    Continuous (fun p : unitInterval × NativeCircle => planarPairOuterFamily R inner p.1 p.2) := by
  let U (i : Fin 2) (p : unitInterval × NativeCircle) : Plane :=
    R • p.2.val-(1-p.1.val) • planarPairCoreCenter i
  let D (p : unitInterval × NativeCircle) := p.2.val 0
  have hD : Continuous D := (EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd)
  have hU (i : Fin 2) : Continuous (U i) :=
    ((continuous_subtype_val.comp continuous_snd).const_smul R).sub
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul continuous_const)
  let J (i : Fin 2) (p : unitInterval × NativeCircle) :=
    inner i (planarPairHalfCircle (decide (i=0)) (sphereRadialDirection nativeCircleLoopBase (U i p)))
  have hJ (i : Fin 2) : Continuous (J i) :=
    (inner i).continuous.comp ((planarPairHalfCircle (decide (i=0))).continuous.comp
      ((continuousOn_sphereRadialDirection nativeCircleLoopBase).comp_continuous (hU i)
        (fun p => planarPairOuterFamily_arg_ne hR i p.1 p.2)))
  have hSeam (p : unitInterval × NativeCircle) (hp : D p = 0) : J 0 p = J 1 p := by
    have h(x : Fin 2) : (U x p) 0 = -(1-p.1.val)*(if x=0 then -1/2 else 1/2) := by
      dsimp only [U]
      rw [PiLp.sub_apply,PiLp.smul_apply,PiLp.smul_apply,planarPairCoreCenter_first]
      change R*D p-(1-p.1.val)*(if x=0 then -1/2 else 1/2) = _
      rw [hp,mul_zero]
      ring
    have hR₀ : 0 ≤ (planarPairCircleComplex (sphereRadialDirection nativeCircleLoopBase (U 0 p))).re := by
      rw [sphereRadialDirection_complex_re _ (planarPairOuterFamily_arg_ne hR 0 p.1 p.2),h 0]
      apply mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
      norm_num only [ite_true]
      nlinarith only [p.1.property.2]
    have hR₁ : (planarPairCircleComplex (sphereRadialDirection nativeCircleLoopBase (U 1 p))).re ≤ 0 := by
      rw [sphereRadialDirection_complex_re _ (planarPairOuterFamily_arg_ne hR 1 p.1 p.2),h 1]
      apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _))
      norm_num only [one_ne_zero,ite_false]
      nlinarith only [p.1.property.2]
    have hSide0 := planarPairHalfCircle_eq_base true (sphereRadialDirection nativeCircleLoopBase (U 0 p)) hR₀
    have hSide1 := planarPairHalfCircle_eq_base false (sphereRadialDirection nativeCircleLoopBase (U 1 p)) hR₁
    change inner 0 (planarPairHalfCircle true _) = inner 1 (planarPairHalfCircle false _)
    rw [hSide0,hSide1,← hA 0,← hA 1]
  exact (hJ 0).if_le (hJ 1) hD continuous_const hSeam

private theorem planarPairOuterFamily_one_west {a : BulkCoefficients} {R : ℝ} (hR : 0 < R)
    (inner : Fin 2 → C(NativeCircle,vacuum a)) (z : NativeCircle) (hz : z.val 0 ≤ 0) :
    planarPairOuterFamily R inner 1 z = inner 0 (planarPairHalfCircle true z) := by
  rw [planarPairOuterFamily, if_pos hz]
  simp only [show (1 : unitInterval).val = 1 from rfl,sub_self,zero_smul,sub_zero,
    sphereRadialDirection_smul nativeCircleLoopBase hR,sphereRadialDirection_unit]

private theorem planarPairOuterFamily_one_east {a : BulkCoefficients} {R : ℝ} (hR : 0 < R)
    (inner : Fin 2 → C(NativeCircle,vacuum a)) (A : vacuum a)
    (hA : ∀ i, A = inner i nativeCircleLoopBase) (z : NativeCircle) (hz : 0 ≤ z.val 0) :
    planarPairOuterFamily R inner 1 z = inner 1 (planarPairHalfCircle false z) := by
  by_cases hW : z.val 0 ≤ 0
  · have h0 : z.val 0 = 0 := le_antisymm hW hz
    rw [planarPairOuterFamily_one_west hR inner z hW]
    have hC : (planarPairCircleComplex z).re = 0 := (planarPairCircleComplex_re z).trans h0
    rw [planarPairHalfCircle_eq_base true z hC.ge,planarPairHalfCircle_eq_base false z hC.le,
      ← hA 0,← hA 1]
  · rw [planarPairOuterFamily,if_neg hW]
    simp only [show (1 : unitInterval).val = 1 from rfl,sub_self,zero_smul,sub_zero,
      sphereRadialDirection_smul nativeCircleLoopBase hR,sphereRadialDirection_unit]

private theorem planarPairOuterFamily_one_path {a : BulkCoefficients} {R : ℝ} (hR : 0 < R)
    (inner : Fin 2 → C(NativeCircle,vacuum a)) (A : vacuum a)
    (hA : ∀ i, A = inner i nativeCircleLoopBase) (t : unitInterval) :
    planarPairOuterFamily R inner 1 (planarPairQuarterTurnCircle (nativeCircleLoopParam t)) =
      (((nativeCircleLoop (inner 1)).cast (hA 1) (hA 1)).trans
        ((nativeCircleLoop (inner 0)).cast (hA 0) (hA 0))) t := by
  let θ := 2*Real.pi*t.val-Real.pi/2
  have hAngular : planarPairQuarterTurnCircle (nativeCircleLoopParam t) = circleNativeParam θ := by
    rw [nativeCircleLoopParam_apply,planarPairQuarterTurnCircle_param]
    congr 1
    dsimp only [θ]
    ring
  have hCoord : (circleNativeParam θ).val 0 = Real.cos θ := by rw [circleNativeParam_coe]; rfl
  have hπ := Real.pi_pos
  have hπ₂ : 0 ≤ 2*Real.pi := mul_nonneg (by norm_num) hπ.le
  rw [Path.trans_apply,hAngular]
  split_ifs with ht
  · have hCos : 0 ≤ Real.cos θ := by
      apply Real.cos_nonneg_of_mem_Icc
      exact ⟨by dsimp only [θ]; linarith only [mul_nonneg hπ₂ t.property.1],
        by dsimp only [θ]; linarith only [mul_le_mul_of_nonneg_left ht hπ₂]⟩
    have hEast : 0 ≤ (circleNativeParam θ).val 0 := by rwa [hCoord]
    rw [planarPairOuterFamily_one_east hR inner A hA _ hEast,
      planarPairHalfCircle_angle false θ hCos]
    change inner 1 (circleNativeParam (2*θ)) = inner 1 (nativeCircleLoopParam _)
    rw [nativeCircleLoopParam_apply]
    apply congrArg (inner 1)
    apply congrArg circleNativeParam
    dsimp only [θ]
    ring
  · have hCos : Real.cos θ ≤ 0 := by
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      · dsimp only [θ]
        linarith only [mul_le_mul_of_nonneg_left (le_of_not_ge ht) hπ₂]
      · dsimp only [θ]
        linarith only [mul_le_mul_of_nonneg_left t.property.2 hπ₂]
    have hWest : (circleNativeParam θ).val 0 ≤ 0 := by rwa [hCoord]
    rw [planarPairOuterFamily_one_west hR inner _ hWest,
      planarPairHalfCircle_angle true θ hCos]
    change inner 0 (circleNativeParam (2*θ)) = inner 0 (nativeCircleLoopParam _)
    rw [nativeCircleLoopParam_apply]
    apply congrArg (inner 0)
    rw [show 2*θ = (2*Real.pi*(2*t.val-1)-Real.pi)+2*Real.pi by dsimp only [θ]; ring,
      circleNativeParam_add_two_pi_pair]

/-- The actual outer curve of the compressed interior has the ordered
product class of the prescribed two peripheral loops. -/
theorem exists_planarPairOuterCurve_homotopic
    (a : BulkCoefficients) {R : ℝ} (hR : 1/2 < R) (A : vacuum a)
    (outer : C(NativeCircle,vacuum a)) (inner : Fin 2 → C(NativeCircle,vacuum a))
    (h₀ : A = outer nativeCircleLoopBase) (hᵢ : ∀ i, A = inner i nativeCircleLoopBase)
    (hWord : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop outer).cast h₀ h₀)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop (inner 0)).cast (hᵢ 0) (hᵢ 0))) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop (inner 1)).cast (hᵢ 1) (hᵢ 1)))) :
    ∃ b : C(NativeCircle,vacuum a), (∀ z, b z = planarPairOuterFamily R inner 0 z) ∧ b.Homotopic outer := by
  let G : C(unitInterval × NativeCircle,vacuum a) :=
    ⟨fun p => planarPairOuterFamily R inner p.1 p.2,continuous_planarPairOuterFamily hR inner A hᵢ⟩
  let b : C(NativeCircle,vacuum a) := ⟨fun z => G (0,z),G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let d : C(NativeCircle,vacuum a) := ⟨fun z => G (1,z),G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let rot := planarPairQuarterTurnCircle
  let e := d.comp rot
  have hR' : 0 < R := (by norm_num : (0 : ℝ) < 1/2).trans hR
  have he : A = e nativeCircleLoopBase := by
    have h := planarPairOuterFamily_one_path hR' inner A hᵢ 0
    rw [nativeCircleLoopParam_zero,Path.source] at h
    exact h.symm
  have hPath : ((nativeCircleLoop e).cast he he) =
      (((nativeCircleLoop (inner 1)).cast (hᵢ 1) (hᵢ 1)).trans
        ((nativeCircleLoop (inner 0)).cast (hᵢ 0) (hᵢ 0))) := by
    apply Path.ext
    funext t
    exact planarPairOuterFamily_one_path hR' inner A hᵢ t
  have hPathClass :
      Path.Homotopic.Quotient.mk ((nativeCircleLoop e).cast he he) =
        Path.Homotopic.Quotient.mk ((nativeCircleLoop outer).cast h₀ h₀) := by
    rw [hPath]
    change _ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop outer).cast h₀ h₀))
    rw [hWord,FundamentalGroup.mul_def]
    rfl
  have hE : e.Homotopic outer := nativeCircle_homotopic_of_based_path_homotopy he h₀
    (Quotient.exact hPathClass)
  have hBD : b.Homotopic d := ⟨⟨G,fun _ => rfl,fun _ => rfl⟩⟩
  have hED : e.Homotopic d := by
    have hRot := MeasureGeometry.nativeCircle_unitComplex_rotation_homotopic_id
      (Complex.exp (((Real.pi/2 : ℝ) : ℂ)*Complex.I)) (MeasureGeometry.norm_complex_circle_exp _)
    exact (ContinuousMap.Homotopic.refl d).comp hRot
  exact ⟨b,fun _ => rfl,hBD.trans (hED.symm.trans hE)⟩

end Thesis
