module

public import Thesis.MeasureGeometry.PlanarPerimeterParity
import Thesis.MeasureGeometry.MeridianCircleOrientation
import Mathlib.Analysis.Normed.Lp.PiLp

/-! Circle and perimeter comparisons in a rectangle containing one puncture. -/

public section

noncomputable section

open Metric Set StratificationTheory
open scoped BigOperators Topology unitInterval

namespace Thesis.MeasureGeometry

/-- The ordinary Cartesian pair coordinates of the Euclidean plane. -/
@[expose] def planePairCoordinates : Plane ≃L[ℝ] ℝ × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

theorem planePairCoordinates_apply (z : Plane) : planePairCoordinates z = (z 0,z 1) := rfl

/-- The actual circular trace of radius `r` about `z` in the plane. -/
@[expose] def planarPairCirclePoint (z : ℝ × ℝ) (r : ℝ) (θ : NativeCircle) : ℝ × ℝ :=
  z + r • planePairCoordinates θ.val

theorem continuous_planarPairCirclePoint (z : ℝ × ℝ) (r : ℝ) :
    Continuous (planarPairCirclePoint z r) :=
  continuous_const.add ((planePairCoordinates.continuous.comp continuous_subtype_val).const_smul r)

theorem planarPairCirclePoint_ne_center (z : ℝ × ℝ) {r : ℝ} (hr : r ≠ 0) (θ : NativeCircle) :
    planarPairCirclePoint z r θ ≠ z := by
  intro h
  have h0 : r • planePairCoordinates θ.val = 0 := by
    have hh : z + r • planePairCoordinates θ.val = z + 0 := h.trans (add_zero _).symm
    exact add_left_cancel hh
  have hθ : θ.val = 0 := by
    apply planePairCoordinates.injective
    rw [map_zero]
    exact (smul_eq_zero.mp h0).resolve_left hr
  have hθn := mem_sphere_zero_iff_norm.mp θ.property
  rw [hθ,norm_zero] at hθn
  exact zero_ne_one hθn

theorem planarPairDiskPoint_mem_box {l r b t : ℝ} (z : ℝ × ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hx₀ : l ≤ z.1-δ) (hx₁ : z.1+δ ≤ r) (hy₀ : b ≤ z.2-δ) (hy₁ : z.2+δ ≤ t)
    (y : Plane) (hy : ‖y‖ ≤ 1) : z + δ • planePairCoordinates y ∈ Icc l r ×ˢ Icc b t := by
  have hcoord (i : Fin 2) : |y i| ≤ 1 := by
    have h := PiLp.norm_apply_le (p := (2 : ENNReal)) y i
    rw [Real.norm_eq_abs] at h
    exact h.trans hy
  obtain ⟨hxL,hxR⟩ := abs_le.mp (hcoord 0)
  obtain ⟨hyL,hyR⟩ := abs_le.mp (hcoord 1)
  rw [planePairCoordinates_apply]
  change (l ≤ z.1 + δ * y 0 ∧ z.1 + δ * y 0 ≤ r) ∧
    (b ≤ z.2 + δ * y 1 ∧ z.2 + δ * y 1 ≤ t)
  constructor <;> constructor
  · nlinarith only [hx₀,mul_le_mul_of_nonneg_left hxL hδ]
  · nlinarith only [hx₁,mul_le_mul_of_nonneg_left hxR hδ]
  · nlinarith only [hy₀,mul_le_mul_of_nonneg_left hyL hδ]
  · nlinarith only [hy₁,mul_le_mul_of_nonneg_left hyR hδ]

theorem planarPairCirclePoint_mem_box {l r b t : ℝ} (z : ℝ × ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hx₀ : l ≤ z.1-δ) (hx₁ : z.1+δ ≤ r) (hy₀ : b ≤ z.2-δ) (hy₁ : z.2+δ ≤ t)
    (θ : NativeCircle) : planarPairCirclePoint z δ θ ∈ Icc l r ×ˢ Icc b t :=
  planarPairDiskPoint_mem_box z hδ hx₀ hx₁ hy₀ hy₁ θ.val (mem_sphere_zero_iff_norm.mp θ.property).le

/-- The active side at each time of the perimeter path. -/
theorem rectangularPerimeter_side (l r b t : ℝ) (s : unitInterval) :
    let p := rectangularPerimeter l r b t s
    if (s : ℝ) ≤ 1/2 then
      if (s : ℝ) ≤ 1/4 then p.2 = t else p.1 = l
    else
      if (s : ℝ) ≤ 3/4 then p.2 = b else p.1 = r := by
  dsimp only
  unfold rectangularPerimeter
  rw [Path.trans_apply]
  split_ifs with h₁ h₂ h₃
  · rw [Path.trans_apply, dif_pos (show (2 : ℝ) * s.val ≤ 1/2 by linarith only [h₂])]
    rw [Path.segment_apply, AffineMap.lineMap_apply_module]
    change (1 - 2*(2*s.val)) * t + (2*(2*s.val)) * t = t
    ring
  · rw [Path.trans_apply, dif_neg (show ¬ (2 : ℝ) * s.val ≤ 1/2 by linarith only [lt_of_not_ge h₂])]
    rw [Path.segment_apply, AffineMap.lineMap_apply_module]
    change (1 - (2*(2*s.val)-1)) * l + (2*(2*s.val)-1) * l = l
    ring
  · rw [Path.trans_apply, dif_pos (show (2 : ℝ) * s.val-1 ≤ 1/2 by linarith only [h₃])]
    rw [Path.segment_apply, AffineMap.lineMap_apply_module]
    change (1 - 2*(2*s.val-1)) * b + (2*(2*s.val-1)) * b = b
    ring
  · rw [Path.trans_apply, dif_neg (show ¬ (2 : ℝ) * s.val-1 ≤ 1/2 by linarith only [lt_of_not_ge h₃])]
    rw [Path.segment_apply, AffineMap.lineMap_apply_module]
    change (1 - (2*(2*s.val-1)-1)) * r + (2*(2*s.val-1)-1) * r = r
    ring

private def quarterCornerRotation : C(NativeCircle,NativeCircle) :=
  nativeCircle_unitComplex (Complex.exp ((((5 * Real.pi / 4 : ℝ) : ℂ) * Complex.I)))
    (norm_complex_circle_exp _) false

private theorem quarterCornerRotation_param (s : unitInterval) :
    quarterCornerRotation (nativeCircleLoopParam s) = circleNativeParam (Real.pi/4 + 2*Real.pi*s.val) := by
  apply Subtype.ext
  rw [quarterCornerRotation,nativeCircle_unitComplex_val,if_neg Bool.false_ne_true,nativeCircleLoopParam_apply,
    circleNativeParam_val_eq_complexExp,circleNativeParam_val_eq_complexExp,
    LinearIsometryEquiv.symm_apply_apply,← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem circle_comp_quarterCornerRotation_homotopic {X : Type*} [TopologicalSpace X]
    (b : C(NativeCircle,X)) : (b.comp quarterCornerRotation).Homotopic b := by
  obtain ⟨H⟩ := nativeCircle_unitComplex_rotation_homotopic_id
    (Complex.exp ((((5 * Real.pi / 4 : ℝ) : ℂ) * Complex.I))) (norm_complex_circle_exp _)
  refine ⟨⟨b.comp H.toContinuousMap,fun z => ?_,fun z => ?_⟩⟩
  · exact congrArg b (H.apply_zero z)
  · exact congrArg b (H.apply_one z)

private theorem strict_linear_interpolation_lt (s : unitInterval) {x y z : ℝ}
    (hx : x < z) (hy : y < z) : (1-s.val)*x + s.val*y < z :=
  (convex_Iio z) hx hy (sub_nonneg.mpr s.property.2) s.property.1 (sub_add_cancel _ _)

private theorem strict_linear_interpolation_gt (s : unitInterval) {x y z : ℝ}
    (hx : z < x) (hy : z < y) : z < (1-s.val)*x + s.val*y :=
  (convex_Ioi z) hx hy (sub_nonneg.mpr s.property.2) s.property.1 (sub_add_cancel _ _)

/-- If the closed rectangle contains only the indicated possible puncture,
its light character equals that of a circle around that puncture. -/
theorem rectangularLightParity_eq_circle {a : BulkCoefficients} (v : Sphere3)
    {U : Set (ℝ × ℝ)} (Q : C(U,vacuum a)) {l r b t : ℝ} (z : ℝ × ℝ)
    (hx : z.1 ∈ Ioo l r) (hy : z.2 ∈ Ioo b t)
    (hBox : (Icc l r ×ˢ Icc b t) \ {z} ⊆ U) {δ : ℝ} (hδ : 0 < δ)
    (hx₀ : l ≤ z.1-δ) (hx₁ : z.1+δ ≤ r) (hy₀ : b ≤ z.2-δ) (hy₁ : z.2+δ ≤ t)
    (hP : ∀ s, rectangularPerimeter l r b t s ∈ U) :
    let f : C(NativeCircle,vacuum a) :=
      ⟨fun θ => Q ⟨planarPairCirclePoint z δ θ,
        hBox ⟨planarPairCirclePoint_mem_box z hδ.le hx₀ hx₁ hy₀ hy₁ θ,
          fun h => planarPairCirclePoint_ne_center z hδ.ne' θ (mem_singleton_iff.mp h)⟩⟩,
        Q.continuous.comp ((continuous_planarPairCirclePoint z δ).subtype_mk _)⟩
    vacuumPathLightParity a v (mappedPathOn Q (rectangularPerimeter l r b t) hP) =
      vacuumPathLightParity a v (nativeCircleLoop f) := by
  intro f
  let P := rectangularPerimeter l r b t
  let C₀ (s : unitInterval) := planarPairCirclePoint z δ (quarterCornerRotation (nativeCircleLoopParam s))
  let F (s : unitInterval × unitInterval) := (1 - s.1.val) • P s.2 + s.1.val • C₀ s.2
  have hF_cts : Continuous F := by
    have hC : Continuous C₀ := (continuous_planarPairCirclePoint z δ).comp
      (quarterCornerRotation.continuous.comp nativeCircleLoopParam.continuous)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (P.continuous.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul (hC.comp continuous_snd))
  have hC_first (s : unitInterval) :
      (C₀ s).1 = z.1 + δ * Real.cos (Real.pi/4 + 2*Real.pi*s.val) := by
    dsimp only [C₀]
    rw [quarterCornerRotation_param]
    rfl
  have hC_second (s : unitInterval) :
      (C₀ s).2 = z.2 + δ * Real.sin (Real.pi/4 + 2*Real.pi*s.val) := by
    dsimp only [C₀]
    rw [quarterCornerRotation_param]
    rfl
  have hF_ne (s u : unitInterval) : F (s,u) ≠ z := by
    let α := Real.pi/4 + 2*Real.pi*u.val
    have hπ : 0 < Real.pi := Real.pi_pos
    have hp₀ := (show 0 ≤ u.val from u.property.1)
    have hp₁ := (show u.val ≤ 1 from u.property.2)
    have hEdge := rectangularPerimeter_side l r b t u
    by_cases hhalf : u.val ≤ 1/2
    · by_cases hquarter : u.val ≤ 1/4
      · have hP' : (P u).2 = t := by simpa only [if_pos hhalf,if_pos hquarter] using hEdge
        have hSin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi
          (by dsimp only [α]; nlinarith only [hπ,mul_nonneg hπ.le hp₀])
          (by dsimp only [α]; nlinarith only [hπ,mul_le_mul_of_nonneg_left hquarter hπ.le])
        have hC : z.2 < (C₀ u).2 := by rw [hC_second]; exact lt_add_of_pos_right _ (mul_pos hδ hSin)
        have hPos : z.2 < (F (s,u)).2 := by
          change z.2 < (1-s.val)*(P u).2 + s.val*(C₀ u).2
          rw [hP']
          exact strict_linear_interpolation_gt s hy.2 hC
        exact fun he => hPos.ne (congrArg Prod.snd he).symm
      · have hP' : (P u).1 = l := by simpa only [if_pos hhalf,if_neg hquarter] using hEdge
        have hCos : Real.cos α < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt
          (by dsimp only [α]; nlinarith only [hπ,mul_lt_mul_of_pos_left (lt_of_not_ge hquarter) hπ])
          (by dsimp only [α]; nlinarith only [hπ,mul_le_mul_of_nonneg_left hhalf hπ.le])
        have hC : (C₀ u).1 < z.1 := by rw [hC_first]; exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg hδ hCos)
        have hNeg : (F (s,u)).1 < z.1 := by
          change (1-s.val)*(P u).1 + s.val*(C₀ u).1 < z.1
          rw [hP']
          exact strict_linear_interpolation_lt s hx.1 hC
        exact fun he => hNeg.ne (congrArg Prod.fst he)
    · by_cases hthree : u.val ≤ 3/4
      · have hP' : (P u).2 = b := by simpa only [if_neg hhalf,if_pos hthree] using hEdge
        have hSin₁ : 0 < Real.sin (α-Real.pi) := Real.sin_pos_of_pos_of_lt_pi
          (by dsimp only [α]; nlinarith only [hπ,mul_lt_mul_of_pos_left (lt_of_not_ge hhalf) hπ])
          (by dsimp only [α]; nlinarith only [hπ,mul_le_mul_of_nonneg_left hthree hπ.le])
        have hSin : Real.sin α < 0 := by rw [Real.sin_sub_pi] at hSin₁; linarith only [hSin₁]
        have hC : (C₀ u).2 < z.2 := by rw [hC_second]; exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg hδ hSin)
        have hNeg : (F (s,u)).2 < z.2 := by
          change (1-s.val)*(P u).2 + s.val*(C₀ u).2 < z.2
          rw [hP']
          exact strict_linear_interpolation_lt s hy.1 hC
        exact fun he => hNeg.ne (congrArg Prod.snd he)
      · have hP' : (P u).1 = r := by simpa only [if_neg hhalf,if_neg hthree] using hEdge
        have hCos : 0 < Real.cos α := by
          rw [← Real.cos_sub_two_pi]
          apply Real.cos_pos_of_mem_Ioo
          constructor <;> dsimp only [α]
          · nlinarith only [hπ,mul_lt_mul_of_pos_left (lt_of_not_ge hthree) hπ]
          · nlinarith only [hπ,mul_le_mul_of_nonneg_left hp₁ hπ.le]
        have hC : z.1 < (C₀ u).1 := by rw [hC_first]; exact lt_add_of_pos_right _ (mul_pos hδ hCos)
        have hPos : z.1 < (F (s,u)).1 := by
          change z.1 < (1-s.val)*(P u).1 + s.val*(C₀ u).1
          rw [hP']
          exact strict_linear_interpolation_gt s hx.2 hC
        exact fun he => hPos.ne (congrArg Prod.fst he).symm
  have hF_mem (s : unitInterval × unitInterval) : F s ∈ U := by
    apply hBox
    refine ⟨?_,fun he => hF_ne s.1 s.2 (mem_singleton_iff.mp he)⟩
    exact ((convex_Icc l r).prod (convex_Icc b t))
      (rectangularPerimeter_mem_closed (hx.1.trans hx.2).le (hy.1.trans hy.2).le s.2)
      (planarPairCirclePoint_mem_box z hδ.le hx₀ hx₁ hy₀ hy₁ _) (sub_nonneg.mpr s.1.property.2)
      s.1.property.1 (sub_add_cancel _ _)
  let H : C(unitInterval × unitInterval,vacuum a) :=
    ⟨fun s => Q ⟨F s,hF_mem s⟩,Q.continuous.comp (hF_cts.subtype_mk _)⟩
  apply Eq.trans _ (vacuumPathLightParity_nativeCircleLoop_homotopic a v
    (circle_comp_quarterCornerRotation_homotopic f))
  apply vacuumPathLightParity_of_periodic_square _ _ _ _ H
  · intro s
    apply congrArg Q
    apply Subtype.ext
    change F (0,s) = P s
    simp [F]
  · intro s
    apply congrArg Q
    apply Subtype.ext
    change F (1,s) = C₀ s
    simp [F]
  · intro s
    apply congrArg Q
    apply Subtype.ext
    have hC : C₀ 0 = C₀ 1 := by dsimp only [C₀]; rw [nativeCircleLoopParam_zero,nativeCircleLoopParam_one]
    change (1-s.val) • P 0 + s.val • C₀ 0 = (1-s.val) • P 1 + s.val • C₀ 1
    rw [P.source,P.target,hC]

end Thesis.MeasureGeometry
