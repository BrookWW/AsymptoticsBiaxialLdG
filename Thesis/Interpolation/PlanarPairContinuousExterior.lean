module

public import Thesis.Interpolation.PlanarPairOuterProduct

/-! A continuous extension on the actual two-hole exterior with all three collars. -/

public section

noncomputable section

open Metric Set StratificationTheory
open scoped Topology

namespace Thesis

/-- The original plane with the two actual reference centers removed. -/
@[expose] def planarPairCentersCompl : Set Plane := {x | ∀ i : Fin 2, x ≠ planarPairCoreCenter i}

private def innerCompressionParameter (r : ℝ) : unitInterval :=
  projIcc 0 1 zero_le_one (32*(r-9/32))

private theorem innerCompressionParameter_zero {r : ℝ} (hr : r ≤ 9/32) :
    innerCompressionParameter r = 0 :=
  projIcc_of_le_left zero_le_one (by linarith only [hr])

private theorem innerCompressionParameter_one {r : ℝ} (hr : 5/16 ≤ r) :
    innerCompressionParameter r = 1 :=
  projIcc_of_right_le zero_le_one (by linarith only [hr])

private def outerExtensionParameter (r : ℝ) : unitInterval :=
  projIcc 0 1 zero_le_one (32*(r-13/16))

private theorem outerExtensionParameter_zero {r : ℝ} (hr : r ≤ 13/16) :
    outerExtensionParameter r = 0 :=
  projIcc_of_le_left zero_le_one (by linarith only [hr])

private theorem outerExtensionParameter_one {r : ℝ} (hr : 27/32 ≤ r) :
    outerExtensionParameter r = 1 :=
  projIcc_of_right_le zero_le_one (by linarith only [hr])

private theorem planarPairCentersCompl_of_norm {z : Plane}
    (hz : 1/2 < ‖z‖) : z ∈ planarPairCentersCompl := by
  intro i h
  rw [h,planarPairCoreCenter_norm] at hz
  exact lt_irrefl _ hz

private theorem planarPairDir_re (x : Plane) (hx : x ≠ 0) :
    (planarPairCircleComplex (sphereRadialDirection nativeCircleLoopBase x)).re = ‖x‖⁻¹*x 0 := by
  rw [planarPairCircleComplex_re,sphereRadialDirection,dif_pos hx]
  rfl

private theorem radius_minus_center_ge {R : ℝ} (hR : 0 ≤ R) (z : NativeCircle) (i : Fin 2) :
    R-1/2 ≤ ‖R • z.val-planarPairCoreCenter i‖ := by
  have h := norm_le_norm_sub_add (R • z.val) (planarPairCoreCenter i)
  rw [norm_smul,Real.norm_of_nonneg hR,mem_sphere_zero_iff_norm.mp z.property,mul_one,
    planarPairCoreCenter_norm] at h
  linarith only [h]

private theorem exists_planarPairCompressedInterior (a : BulkCoefficients)
    (A : vacuum a) (inner : Fin 2 → C(NativeCircle,vacuum a))
    (hᵢ : ∀ i, A = inner i nativeCircleLoopBase) :
    ∃ p : Plane → vacuum a, ContinuousOn p planarPairCentersCompl ∧
      (∀ i : Fin 2, ∀ x ∈ planarPairCentersCompl, x ∈ closedBall (planarPairCoreCenter i) (9/32) →
        p x = inner i (sphereRadialDirection nativeCircleLoopBase (x-planarPairCoreCenter i))) ∧
      (∀ z : NativeCircle, p ((13/16 : ℝ) • z.val) = planarPairOuterFamily (13/16) inner 0 z) := by
  classical
  let H (i : Fin 2) : (ContinuousMap.id NativeCircle).Homotopy (planarPairHalfCircle (decide (i=0))) :=
    Classical.choice (exists_planarPairHalfCircle_homotopy (decide (i=0)))
  let W (i : Fin 2) (x : Plane) := x-planarPairCoreCenter i
  let u (i : Fin 2) (x : Plane) :=
    inner i (H i (innerCompressionParameter ‖W i x‖,sphereRadialDirection nativeCircleLoopBase (W i x)))
  let p (x : Plane) := if x 0 ≤ 0 then u 0 x else u 1 x
  have hW (i : Fin 2) : Continuous (W i) := continuous_id.sub continuous_const
  have hR : Continuous innerCompressionParameter := by
    exact continuous_projIcc.comp (continuous_const.mul (continuous_id.sub continuous_const))
  have hU (i : Fin 2) : ContinuousOn (u i) planarPairCentersCompl := by
    have hDir : ContinuousOn (fun x => sphereRadialDirection nativeCircleLoopBase (W i x))
        planarPairCentersCompl :=
      (continuousOn_sphereRadialDirection nativeCircleLoopBase).comp (hW i).continuousOn
        (fun x hx => sub_ne_zero.mpr (hx i))
    exact ((inner i).continuous.comp (H i).continuous).comp_continuousOn
      ((hR.comp (hW i).norm).continuousOn.prodMk hDir)
  have hInner (i : Fin 2) (x : Plane) (hx : ‖W i x‖ ≤ 9/32) :
      u i x = inner i (sphereRadialDirection nativeCircleLoopBase (W i x)) := by
    change inner i (H i (innerCompressionParameter ‖W i x‖,_)) = _
    rw [innerCompressionParameter_zero hx]
    exact congrArg (inner i) ((H i).map_zero_left _)
  have hOuter (i : Fin 2) (x : Plane) (hx : 5/16 ≤ ‖W i x‖) :
      u i x = inner i (planarPairHalfCircle (decide (i=0))
        (sphereRadialDirection nativeCircleLoopBase (W i x))) := by
    change inner i (H i (innerCompressionParameter ‖W i x‖,_)) = _
    rw [innerCompressionParameter_one hx]
    exact congrArg (inner i) ((H i).map_one_left _)
  have hFront (x : Plane) (hx : x ∈ planarPairCentersCompl) (h0 : x 0 = 0) : u 0 x = u 1 x := by
    have hCoord (i : Fin 2) : W i x 0 = if i=0 then 1/2 else -1/2 := by
      dsimp only [W]
      rw [PiLp.sub_apply,h0,planarPairCoreCenter_first]
      split <;> norm_num
    have hWbig (i : Fin 2) : 5/16 ≤ ‖W i x‖ := by
      have h := PiLp.norm_apply_le (W i x) (0 : Fin 2)
      rw [hCoord i] at h
      split at h <;> norm_num at h <;> linarith only [h]
    have hBase₀ : planarPairHalfCircle true (sphereRadialDirection nativeCircleLoopBase (W 0 x)) =
        nativeCircleLoopBase := by
      apply planarPairHalfCircle_eq_base true
      change 0 ≤ (planarPairCircleComplex (sphereRadialDirection nativeCircleLoopBase (W 0 x))).re
      rw [planarPairDir_re _ (sub_ne_zero.mpr (hx 0)),hCoord 0,if_pos rfl]
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (by norm_num)
    have hBase₁ : planarPairHalfCircle false (sphereRadialDirection nativeCircleLoopBase (W 1 x)) =
        nativeCircleLoopBase := by
      apply planarPairHalfCircle_eq_base false
      change (planarPairCircleComplex (sphereRadialDirection nativeCircleLoopBase (W 1 x))).re ≤ 0
      rw [planarPairDir_re _ (sub_ne_zero.mpr (hx 1)),hCoord 1,if_neg (by decide : (1 : Fin 2) ≠ 0)]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) (by norm_num)
    rw [hOuter 0 x (hWbig 0),hOuter 1 x (hWbig 1)]
    change inner 0 (planarPairHalfCircle true _) = inner 1 (planarPairHalfCircle false _)
    rw [hBase₀,hBase₁,← hᵢ 0,← hᵢ 1]
  have hp : ContinuousOn p planarPairCentersCompl := by
    let S := {x : Plane | x 0 ≤ 0}
    have hEdge : ∀ x ∈ planarPairCentersCompl ∩ frontier S, u 0 x = u 1 x := by
      intro x hx
      have h := frontier_le_subset_eq (EuclideanSpace.proj (0 : Fin 2)).continuous continuous_const hx.2
      exact hFront x hx.1 h
    change ContinuousOn (S.piecewise (u 0) (u 1)) planarPairCentersCompl
    exact ContinuousOn.piecewise hEdge ((hU 0).mono inter_subset_left) ((hU 1).mono inter_subset_left)
  refine ⟨p,hp,?_,?_⟩
  · intro i x hx hB
    have hRad : ‖W i x‖ ≤ 9/32 := by simpa only [W,mem_closedBall,dist_eq_norm] using hB
    have hCoord := PiLp.norm_apply_le (W i x) (0 : Fin 2)
    dsimp only [W] at hCoord
    rw [PiLp.sub_apply,planarPairCoreCenter_first] at hCoord
    have hAbs : |x 0-(if i=0 then -1/2 else 1/2)| ≤ 9/32 := hCoord.trans hRad
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> decide
    rcases hi with rfl | rfl
    · have hWest : x 0 ≤ 0 := by
        rw [if_pos rfl] at hAbs
        have h := (abs_le.mp hAbs).2
        linarith only [h]
      dsimp only [p]
      rw [if_pos hWest,hInner 0 x hRad]
    · have hEast : ¬ x 0 ≤ 0 := by
        have hn : (1 : Fin 2) ≠ 0 := by decide
        rw [if_neg hn] at hAbs
        have h := (abs_le.mp hAbs).1
        exact not_le.mpr (by linarith only [h])
      dsimp only [p]
      rw [if_neg hEast,hInner 1 x hRad]
  · intro z
    let R : ℝ := 13/16
    have hR₀ : 0 ≤ R := by dsimp only [R]; norm_num
    have hBig (i : Fin 2) : 5/16 ≤ ‖W i (R • z.val)‖ := by
      have h := radius_minus_center_ge hR₀ z i
      dsimp only [R] at h
      norm_num at h
      exact h
    have hFirst : (R • z.val) 0 ≤ 0 ↔ z.val 0 ≤ 0 := by
      rw [PiLp.smul_apply]
      change R*z.val 0 ≤ 0 ↔ _
      have hR' : 0 < R := by dsimp only [R]; norm_num
      constructor
      · intro h
        exact le_of_not_gt (fun hn => (mul_pos hR' hn).not_ge h)
      · exact mul_nonpos_of_nonneg_of_nonpos hR'.le
    have hZero : (1-(0 : unitInterval).val : ℝ) = 1 := sub_zero _
    change (if (R • z.val) 0 ≤ 0 then u 0 (R • z.val) else u 1 (R • z.val)) =
      planarPairOuterFamily R inner 0 z
    by_cases hz : z.val 0 ≤ 0
    · rw [if_pos (hFirst.mpr hz),hOuter 0 (R • z.val) (hBig 0),planarPairOuterFamily,if_pos hz,hZero,one_smul]
      rfl
    · rw [if_neg (fun h => hz (hFirst.mp h)),hOuter 1 (R • z.val) (hBig 1),
        planarPairOuterFamily,if_neg hz,hZero,one_smul]
      rfl

/-- The native continuous filling for the actual reference pair, equal
to each prescribed loop on the corresponding radial collar. -/
theorem exists_planarPairContinuousExterior
    (a : BulkCoefficients) (A : vacuum a)
    (outer : C(NativeCircle,vacuum a)) (inner : Fin 2 → C(NativeCircle,vacuum a))
    (h₀ : A = outer nativeCircleLoopBase) (hᵢ : ∀ i, A = inner i nativeCircleLoopBase)
    (hWord : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop outer).cast h₀ h₀)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop (inner 0)).cast (hᵢ 0) (hᵢ 0))) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop (inner 1)).cast (hᵢ 1) (hᵢ 1)))) :
    ∃ p : Plane → vacuum a, ContinuousOn p planarPairCentersCompl ∧
      (∀ i : Fin 2, ∀ x ∈ planarPairCentersCompl, x ∈ closedBall (planarPairCoreCenter i) (9/32) →
        p x = inner i (sphereRadialDirection nativeCircleLoopBase (x-planarPairCoreCenter i))) ∧
      ∀ r ≥ (27/32 : ℝ), ∀ θ : NativeCircle, p (r • θ.val) = outer θ := by
  obtain ⟨w,hw,hInner,hEval⟩ := exists_planarPairCompressedInterior a A inner hᵢ
  obtain ⟨b,hb,⟨H⟩⟩ := exists_planarPairOuterCurve_homotopic a (by norm_num : (1/2 : ℝ) < 13/16)
    A outer inner h₀ hᵢ hWord
  let g (x : Plane) := H (outerExtensionParameter ‖x‖,sphereRadialDirection nativeCircleLoopBase x)
  let p (x : Plane) := if ‖x‖ ≤ 13/16 then w x else g x
  let B := {x : Plane | ‖x‖ ≤ (13/16 : ℝ)}
  have hR : Continuous outerExtensionParameter := by
    exact continuous_projIcc.comp (continuous_const.mul (continuous_id.sub continuous_const))
  have hg : ContinuousOn g ({0}ᶜ : Set Plane) :=
    H.continuous.comp_continuousOn ((hR.comp continuous_norm).continuousOn.prodMk
      (continuousOn_sphereRadialDirection nativeCircleLoopBase))
  have hFront : ∀ x ∈ planarPairCentersCompl ∩ frontier B, w x = g x := by
    intro x hx
    have hNorm : ‖x‖ = 13/16 := frontier_le_subset_eq continuous_norm continuous_const hx.2
    have hN : x ≠ 0 := by
      intro h
      rw [h,norm_zero] at hNorm
      norm_num at hNorm
    let θ := sphereRadialDirection nativeCircleLoopBase x
    have hxθ : (13/16 : ℝ) • θ.val = x := by
      change (13/16 : ℝ) • (sphereRadialDirection nativeCircleLoopBase x).val = x
      rw [← hNorm,sphereRadialDirection,dif_pos hN]
      exact NormedSpace.norm_smul_normalize x
    have hwθ : w x = b θ := (congrArg w hxθ).symm.trans ((hEval θ).trans (hb θ).symm)
    change w x = H (outerExtensionParameter ‖x‖,θ)
    rw [outerExtensionParameter_zero hNorm.le]
    exact hwθ.trans (H.map_zero_left θ).symm
  have hp : ContinuousOn p planarPairCentersCompl := by
    change ContinuousOn (B.piecewise w g) planarPairCentersCompl
    refine ContinuousOn.piecewise hFront (hw.mono inter_subset_left) (hg.mono ?_)
    intro x hx
    have h : x ∈ closure {y : Plane | (13/16 : ℝ) < ‖y‖} := by
      simpa only [B,Set.compl_setOf,not_le] using hx.2
    have hf : (13/16 : ℝ) ≤ ‖x‖ := closure_lt_subset_le continuous_const continuous_norm h
    exact fun h => by
      have he : x = 0 := mem_singleton_iff.mp h
      rw [he,norm_zero] at hf
      norm_num at hf
  refine ⟨p,hp,?_,?_⟩
  · intro i x hx hB
    have h : ‖x‖ ≤ 13/16 := by
      have hT := dist_triangle x (planarPairCoreCenter i) 0
      rw [dist_zero_right,dist_zero_right,planarPairCoreCenter_norm] at hT
      have hd := mem_closedBall.mp hB
      linarith only [hT,hd]
    dsimp only [p]
    rw [if_pos h]
    exact hInner i x hx hB
  · intro r hr θ
    have hr₀ : 0 < r := (by norm_num : 0 < (27/32 : ℝ)).trans_le hr
    have hN : ‖r • θ.val‖ = r := by
      rw [norm_smul,Real.norm_of_nonneg hr₀.le,mem_sphere_zero_iff_norm.mp θ.property,mul_one]
    have hOut : ¬ ‖r • θ.val‖ ≤ 13/16 := by rw [hN]; linarith only [hr]
    dsimp only [p]
    rw [if_neg hOut]
    change H (outerExtensionParameter ‖r • θ.val‖,sphereRadialDirection nativeCircleLoopBase (r • θ.val)) = _
    rw [hN,outerExtensionParameter_one hr,sphereRadialDirection_smul nativeCircleLoopBase hr₀,
      sphereRadialDirection_unit]
    exact H.map_one_left θ

end Thesis
