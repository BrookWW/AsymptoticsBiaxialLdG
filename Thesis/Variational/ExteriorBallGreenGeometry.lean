module

public import Thesis.Upstream.PoissonL4Potential

/-! The Kelvin inversion and the positive Newton kernel of an exterior ball. -/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped RealInnerProductSpace

namespace Thesis

/-- The spherical inversion of the source in the physical exterior ball. -/
@[expose] def kelvinBallImage (a : Point) (ρ : ℝ) (y : Point) : Point :=
  a + (ρ ^ 2 / ‖y-a‖ ^ 2) • (y-a)

/-- The exterior Green kernel, with the overall sphere-area factor suppressed. -/
@[expose] def exteriorBallNewtonKernel (a : Point) (ρ : ℝ) (x y : Point) : ℝ :=
  poissonInversePower 1 (x-y) - (ρ / ‖y-a‖) * poissonInversePower 1 (x - kelvinBallImage a ρ y)

theorem measurable_kelvinBallImage (a : Point) (ρ : ℝ) : Measurable (kelvinBallImage a ρ) := by
  have hN : Measurable (fun y : Point => ‖y-a‖ ^ (2 : ℕ)) :=
    (continuous_id.sub continuous_const).measurable.norm.pow_const _
  have hZ : Measurable (fun y : Point => y-a) := (continuous_id.sub continuous_const).measurable
  have hc : Measurable (fun y : Point => ρ^2 / ‖y-a‖^2) :=
    measurable_const.div hN
  exact measurable_const.add (hc.smul hZ)

theorem measurable_exteriorBallNewtonKernel_source (a : Point) (ρ : ℝ) (x : Point) :
    Measurable (exteriorBallNewtonKernel a ρ x) := by
  have hK := measurable_poissonInversePower 1
  have h : Measurable (fun y : Point => x-y) := (continuous_const.sub continuous_id).measurable
  have hNorm : Measurable (fun y : Point => ρ / ‖y-a‖) :=
    measurable_const.div ((continuous_id.sub continuous_const).measurable.norm)
  exact (hK.comp h).sub (hNorm.mul (hK.comp (measurable_const.sub (measurable_kelvinBallImage a ρ))))

theorem kelvinBallImage_norm_from_center (a : Point) {ρ : ℝ} (hρ : 0 < ρ)
    {y : Point} (hy : ρ < ‖y-a‖) :
    ‖kelvinBallImage a ρ y - a‖ = ρ ^ 2 / ‖y-a‖ := by
  have hy₀ := hρ.trans hy
  rw [kelvinBallImage, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  field_simp

theorem kelvinBallImage_mem_ball (a : Point) {ρ : ℝ} (hρ : 0 < ρ)
    {y : Point} (hy : ρ < ‖y-a‖) :
    kelvinBallImage a ρ y ∈ ball a ρ := by
  rw [mem_ball, dist_eq_norm, kelvinBallImage_norm_from_center a hρ hy]
  apply (div_lt_iff₀ (hρ.trans hy)).2
  simpa only [pow_two] using mul_lt_mul_of_pos_left hy hρ

theorem kelvinBallImage_dist_sq (a x : Point) {ρ : ℝ} (hρ : 0 < ρ)
    {y : Point} (hy : ρ < ‖y-a‖) :
    ‖x - kelvinBallImage a ρ y‖ ^ 2 =
      (ρ^2 / ‖y-a‖^2) * ‖x-y‖ ^ 2 +
        (1 - ρ^2 / ‖y-a‖^2) * (‖x-a‖ ^ 2 - ρ^2) := by
  let u := x-a
  let v := y-a
  let s := ρ^2 / ‖v‖^2
  have hv := hρ.trans hy
  have hX : x - kelvinBallImage a ρ y = u - s • v := by unfold kelvinBallImage; dsimp only [u,v,s]; abel
  have hY : x-y = u-v := by dsimp only [u,v]; abel
  rw [hX, hY, norm_sub_sq_real u (s • v), norm_sub_sq_real u v, real_inner_smul_right, norm_smul,
    Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  change _ = s * (‖u‖^2 - 2 * inner ℝ u v + ‖v‖^2) + (1-s)*(‖u‖^2-ρ^2)
  have hs : s * ‖v‖ ^ 2 = ρ^2 := div_mul_cancel₀ _ (pow_ne_zero 2 hv.ne')
  have hs₂ : (s * ‖v‖)^2 = s * ρ^2 := by
    calc
      _ = s * (s * ‖v‖^2) := by ring
      _ = _ := by rw [hs]
  rw [hs₂]
  linear_combination -hs

theorem kelvinBallImage_dist_lower (a x : Point) {ρ : ℝ} (hρ : 0 < ρ)
    {y : Point} (hy : ρ < ‖y-a‖) (hx : ρ ≤ ‖x-a‖) :
    (ρ / ‖y-a‖) * ‖x-y‖ ≤ ‖x - kelvinBallImage a ρ y‖ := by
  have hy₀ := hρ.trans hy
  have hs : ρ^2 / ‖y-a‖^2 ≤ 1 := (div_le_one (pow_pos hy₀ 2)).2
    (pow_le_pow_left₀ hρ.le hy.le 2)
  have hX : 0 ≤ ‖x-a‖ ^ 2 - ρ^2 := sub_nonneg.mpr (pow_le_pow_left₀ hρ.le hx 2)
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [kelvinBallImage_dist_sq a x hρ hy, mul_pow, div_pow]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hs) hX)

theorem kelvinBallImage_dist_surface (a x : Point) {ρ : ℝ} (hρ : 0 < ρ)
    {y : Point} (hy : ρ < ‖y-a‖) (hx : ‖x-a‖ = ρ) :
    ‖x - kelvinBallImage a ρ y‖ = (ρ / ‖y-a‖) * ‖x-y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (div_nonneg hρ.le (norm_nonneg _)) (norm_nonneg _))).mp
  rw [kelvinBallImage_dist_sq a x hρ hy, hx, sub_self, mul_zero, add_zero, mul_pow, div_pow]

private theorem x_ne_kelvinBallImage (a x : Point) {ρ : ℝ} (hρ : 0 < ρ)
    {y : Point} (hy : ρ < ‖y-a‖) (hx : ρ ≤ ‖x-a‖) : x ≠ kelvinBallImage a ρ y := by
  intro heq
  have h := kelvinBallImage_mem_ball a hρ hy
  rw [← heq, mem_ball, dist_eq_norm] at h
  exact h.not_ge hx

theorem exteriorBallNewtonKernel_nonneg (a x : Point) {ρ : ℝ} (hρ : 0 < ρ)
    {y : Point} (hy : ρ < ‖y-a‖) (hx : ρ ≤ ‖x-a‖) (hxy : x ≠ y) :
    0 ≤ exteriorBallNewtonKernel a ρ x y := by
  have hq : 0 < ρ / ‖y-a‖ := div_pos hρ (hρ.trans hy)
  have hxyN : 0 < ‖x-y‖ := norm_pos_iff.2 (sub_ne_zero.mpr hxy)
  have hxI : 0 < ‖x - kelvinBallImage a ρ y‖ :=
    norm_pos_iff.2 (sub_ne_zero.mpr (x_ne_kelvinBallImage a x hρ hy hx))
  have h := (inv_le_inv₀ hxI (mul_pos hq hxyN)).2 (kelvinBallImage_dist_lower a x hρ hy hx)
  unfold exteriorBallNewtonKernel
  rw [poissonInversePower_one, poissonInversePower_one]
  apply sub_nonneg.mpr
  refine (mul_le_mul_of_nonneg_left h hq.le).trans_eq ?_
  field_simp [(hρ.trans hy).ne', hρ.ne', hxyN.ne']

theorem exteriorBallNewtonKernel_eq_zero_on_sphere (a x : Point) {ρ : ℝ} (hρ : 0 < ρ)
    {y : Point} (hy : ρ < ‖y-a‖) (hx : ‖x-a‖ = ρ) :
    exteriorBallNewtonKernel a ρ x y = 0 := by
  have hq : 0 < ρ / ‖y-a‖ := div_pos hρ (hρ.trans hy)
  have hxy : x ≠ y := fun heq => (hy.ne') (heq ▸ hx)
  unfold exteriorBallNewtonKernel
  rw [poissonInversePower_one, poissonInversePower_one, kelvinBallImage_dist_surface a x hρ hy hx]
  have hq' := hq.ne'
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hq', one_mul, sub_self]

theorem exteriorBallNewtonKernel_le (a x : Point) (ρ : ℝ) (y : Point) (hρ : 0 ≤ ρ) :
    exteriorBallNewtonKernel a ρ x y ≤ poissonInversePower 1 (x-y) :=
  sub_le_self _ (mul_nonneg (div_nonneg hρ (norm_nonneg _)) (poissonInversePower_nonneg _ _))

private theorem kelvinBallImage_inverse_square_le (a x : Point) {ρ : ℝ} (hρ : 0 < ρ)
    {y : Point} (hy : ρ < ‖y-a‖) (hx : ρ ≤ ‖x-a‖) (hxy : x ≠ y) :
    (ρ / ‖y-a‖) * poissonInversePower 2 (x-kelvinBallImage a ρ y) ≤
      (‖y-a‖ / ρ) * poissonInversePower 2 (x-y) := by
  have hq : 0 < ρ / ‖y-a‖ := div_pos hρ (hρ.trans hy)
  have hxyN : 0 < ‖x-y‖ := norm_pos_iff.2 (sub_ne_zero.mpr hxy)
  have hxI : 0 < ‖x - kelvinBallImage a ρ y‖ :=
    norm_pos_iff.2 (sub_ne_zero.mpr (x_ne_kelvinBallImage a x hρ hy hx))
  have h := (inv_le_inv₀ hxI (mul_pos hq hxyN)).2 (kelvinBallImage_dist_lower a x hρ hy hx)
  rw [poissonInversePower_two, poissonInversePower_two]
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h 2) hq.le).trans_eq ?_
  field_simp

/-- Uniform difference bound for the Green kernel at two exterior points.
The estimate uses the original source distances. -/
theorem exteriorBallNewtonKernel_abs_sub_le (a x z : Point) {ρ : ℝ} (hρ : 0 < ρ)
    {y : Point} (hy : ρ < ‖y-a‖) (hx : ρ ≤ ‖x-a‖) (hz : ρ ≤ ‖z-a‖)
    (hxy : x ≠ y) (hzy : z ≠ y) :
    |exteriorBallNewtonKernel a ρ x y - exteriorBallNewtonKernel a ρ z y| ≤
      (1 + ‖y-a‖ / ρ) * dist x z *
        (poissonInversePower 2 (x-y) + poissonInversePower 2 (z-y)) / 2 := by
  let q := ρ / ‖y-a‖
  let w := kelvinBallImage a ρ y
  let K (x y : Point) := poissonInversePower 1 (x-y)
  let h (x y : Point) := poissonInversePower 2 (x-y)
  have hq : 0 ≤ q := div_nonneg hρ.le (norm_nonneg _)
  have heq : exteriorBallNewtonKernel a ρ x y - exteriorBallNewtonKernel a ρ z y =
      (K x y - K z y) - q * (K x w - K z w) := by unfold exteriorBallNewtonKernel; dsimp only [q,w,K]; ring
  have hI := abs_poissonInversePower_one_sub_le x z w
    (x_ne_kelvinBallImage a x hρ hy hx) (x_ne_kelvinBallImage a z hρ hy hz)
  have h₂ : q * |K x w - K z w| ≤
      (‖y-a‖ / ρ) * dist x z * (h x y + h z y) / 2 := by
    apply (mul_le_mul_of_nonneg_left hI hq).trans
    have hc := add_le_add (kelvinBallImage_inverse_square_le a x hρ hy hx hxy)
      (kelvinBallImage_inverse_square_le a z hρ hy hz hzy)
    have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ dist x z from dist_nonneg)
    have hF := div_le_div_of_nonneg_right hc' (by norm_num : (0 : ℝ) ≤ 2)
    convert hF using 1 <;> dsimp only [q,w,h] <;> ring
  rw [heq]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg hq]
  refine (add_le_add (abs_poissonInversePower_one_sub_le x z y hxy hzy) h₂).trans_eq ?_
  dsimp only [h]
  ring

end Thesis

end
