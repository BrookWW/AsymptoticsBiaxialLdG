module

public import Thesis.MeasureGeometry.MeridianCircleOrientation
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! An injective real linear map of the normal plane deforms to a unit
complex rotation or reversal without passing through the origin. -/

@[expose] public section

noncomputable section

open Metric Set
open scoped ContDiff RealInnerProductSpace

namespace Thesis.MeasureGeometry

private theorem complex_re_im_smul (z : ℂ) :
    z.re • (1 : ℂ) + z.im • Complex.I = z := by
  apply Complex.ext <;> simp

private theorem positive_convex_mix {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < (1 - t) * a + t := by
  by_cases h : t = 1
  · simp [h]
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht.2 h)) ha) ht.1

/-- The ellipse of an injective real plane map deforms through nonzero
curves to the actual round meridian with its orientation recorded. -/
theorem exists_nondegenerate_normalPlane_deformation (A : Plane →L[ℝ] Plane)
    (hAi : Function.Injective A) :
    ∃ (w : ℂ) (hw : ‖w‖ = 1) (rev : Bool) (F : ℝ × Plane → Plane), ContDiff ℝ ∞ F ∧
      (∀ z, F (0,z) = A z) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z : Plane, z ≠ 0 → F (t,z) ≠ 0) ∧
      ∀ z : NativeCircle, F (1,z.val) = (nativeCircle_unitComplex w hw rev z).val := by
  let E := complexPlaneCoordinates
  let L : ℂ →L[ℝ] ℂ := E.symm.toContinuousLinearMap.comp (A.comp E.toContinuousLinearMap)
  have hLi : Function.Injective L := (E.symm.injective.comp hAi).comp E.injective
  let u := L 1
  let v := L Complex.I
  have hu : u ≠ 0 := fun h => one_ne_zero (hLi (h.trans L.map_zero.symm))
  let a := ‖u‖
  have ha : 0 < a := norm_pos_iff.mpr hu
  let w := a⁻¹ • u
  have hw : ‖w‖ = 1 := by
    change ‖a⁻¹ • u‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
    change a⁻¹ * a = 1
    exact inv_mul_cancel₀ ha.ne'
  have hw₀ : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    norm_num at hw
  have hwua : a • w = u := by
    dsimp only [w]
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  let z₁ := w⁻¹ * v
  have hz₁ : w * z₁ = v := by
    dsimp only [z₁]
    rw [← mul_assoc, mul_inv_cancel₀ hw₀, one_mul]
  have him : z₁.im ≠ 0 := by
    intro h
    have hreal : z₁ = (z₁.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using h
    have hLinear : v = (z₁.re / a) • u := by
      calc
        v = w * z₁ := hz₁.symm
        _ = z₁.re • w := by
          rw [hreal, Algebra.smul_def]
          exact mul_comm _ _
        _ = (z₁.re / a) • u := by dsimp only [w]; rw [smul_smul, div_eq_mul_inv]
    have hBasis : Complex.I = (z₁.re / a) • (1 : ℂ) := hLi
      (hLinear.trans (L.map_smul _ _).symm)
    have hi := congrArg Complex.im hBasis
    simp only [Complex.I_im, Complex.smul_im, Complex.one_im, smul_zero, one_ne_zero] at hi
  let rev := if z₁.im < 0 then true else false
  let J : ℂ := if rev then -Complex.I else Complex.I
  let W (t : ℝ) := (1 - t) • z₁ + t • J
  have hWim (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (W t).im ≠ 0 := by
    have ht₀ : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    by_cases hi : z₁.im < 0
    · have hJ : J.im = -1 := by simp [J, rev, hi]
      have hI := positive_convex_mix (a := -z₁.im) (neg_pos.mpr hi) ht
      dsimp only [W]
      rw [Complex.add_im, Complex.smul_im, Complex.smul_im, hJ, smul_eq_mul, smul_eq_mul]
      linarith only [hI]
    · have hJ : J.im = 1 := by simp [J, rev, hi]
      have hi' : 0 < z₁.im := lt_of_le_of_ne (le_of_not_gt hi) him.symm
      dsimp only [W]
      rw [Complex.add_im, Complex.smul_im, Complex.smul_im, hJ, smul_eq_mul, smul_eq_mul, mul_one]
      exact (positive_convex_mix hi' ht).ne'
  let a' (t : ℝ) := (1 - t) * a + t
  let G (p : ℝ × ℂ) := w * ((a' p.1 * p.2.re) • (1 : ℂ) + p.2.im • W p.1)
  let F (p : ℝ × Plane) := E (G (p.1, E.symm p.2))
  have hG : ContDiff ℝ ∞ G := by
    have hRe : ContDiff ℝ ∞ (fun p : ℝ × ℂ => p.2.re) := Complex.reCLM.contDiff.comp contDiff_snd
    have hIm : ContDiff ℝ ∞ (fun p : ℝ × ℂ => p.2.im) := Complex.imCLM.contDiff.comp contDiff_snd
    have hA' : ContDiff ℝ ∞ (fun p : ℝ × ℂ => a' p.1) := by dsimp only [a']; fun_prop
    have hW' : ContDiff ℝ ∞ (fun p : ℝ × ℂ => W p.1) := by dsimp only [W]; fun_prop
    exact contDiff_const.mul (((hA'.mul hRe).smul contDiff_const).add (hIm.smul hW'))
  have hF : ContDiff ℝ ∞ F := E.toContinuousLinearMap.contDiff.comp
    (hG.comp (contDiff_fst.prodMk (E.symm.toContinuousLinearMap.contDiff.comp contDiff_snd)))
  refine ⟨w, hw, rev, F, hF, ?_, ?_, ?_⟩
  · intro y
    let z := E.symm y
    have hz : E z = y := E.apply_symm_apply _
    have hF0 : G (0,z) = w * ((a * z.re) • (1 : ℂ) + z.im • z₁) := by
      simp only [G, a', W, sub_zero, one_mul, add_zero, one_smul, zero_smul]
    have hF1 : G (0,z) = z.re • u + z.im • v := by
      rw [hF0, mul_add]
      have hB : w * (z.im • z₁) = z.im • v := by
        rw [mul_smul_comm, hz₁]
      have hA : w * ((a * z.re) • (1 : ℂ)) = z.re • u := by
        calc
          _ = (a * z.re) • w := by rw [mul_smul_comm, mul_one]
          _ = (z.re * a) • w := congrArg (fun t : ℝ => t • w) (mul_comm a z.re)
          _ = z.re • (a • w) := (smul_smul _ _ _).symm
          _ = _ := by rw [hwua]
      rw [hA, hB]
    have hL : L z = z.re • u + z.im • v := by
      calc
        L z = L (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg L (complex_re_im_smul z).symm
        _ = _ := by rw [map_add, map_smul, map_smul]
    change E (G (0,z)) = A y
    rw [hF1, ← hL]
    change E (E.symm (A (E z))) = _
    rw [E.apply_symm_apply, hz]
  · intro t ht y hy h
    let z := E.symm y
    have hZ : z ≠ 0 := fun h0 => hy (E.symm.injective (h0.trans E.symm.map_zero.symm))
    have hG₀ : G (t,z) = 0 := E.injective (h.trans E.map_zero.symm)
    have hSum : (a' t * z.re) • (1 : ℂ) + z.im • W t = 0 :=
      (mul_eq_zero.mp hG₀).resolve_left hw₀
    have hi := congrArg Complex.im hSum
    rw [Complex.add_im, Complex.smul_im, Complex.one_im, smul_zero, Complex.smul_im, smul_eq_mul,
      zero_add, Complex.zero_im] at hi
    have hiz : z.im = 0 := (mul_eq_zero.mp hi).resolve_right (hWim t ht)
    have hr := congrArg Complex.re hSum
    rw [Complex.add_re, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one,
      hiz, zero_smul, Complex.zero_re, add_zero] at hr
    have hrz : z.re = 0 := (mul_eq_zero.mp hr).resolve_left (positive_convex_mix ha ht).ne'
    exact hZ (Complex.ext hrz hiz)
  · intro y
    let z := E.symm y.val
    have h₁ : G (1,z) = w * (z.re • (1 : ℂ) + z.im • J) := by
      simp only [G, a', W, sub_self, zero_mul, zero_add, one_mul, zero_smul, one_smul]
    have hZ : z.re • (1 : ℂ) + z.im • J = if rev then star z else z := by
      by_cases hr : rev = true
      · apply Complex.ext <;> simp [J, hr]
      · simpa only [J, if_neg hr] using complex_re_im_smul z
    change E (G (1,z)) = _
    rw [h₁, hZ, nativeCircle_unitComplex_val]

end Thesis.MeasureGeometry
