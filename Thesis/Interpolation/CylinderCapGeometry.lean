module

public import Thesis.MeasureGeometry.CylinderMass
public import Thesis.Interpolation.PlanarBallSquare

/-! Uniform physical coordinates for the short terminal cylinder. -/

public section

noncomputable section

open Metric Set
open scoped NNReal RealInnerProductSpace

namespace Thesis.MeasureGeometry

/-- The homogeneous radial size with transverse radius one and axial
half-height (1/k). -/
@[expose] def cylinderCapGauge (e : Point) (k : ℝ) (x : Point) : ℝ :=
  max (cylinderTransverseRadius e x) (k * |cylinderHeight e x|)

private theorem abs_cylinderHeight_le_norm {e : Point} (he : ‖e‖ = 1) (x : Point) :
    |cylinderHeight e x| ≤ ‖x‖ := by
  simpa only [cylinderHeight, he, one_mul] using abs_real_inner_le_norm e x

private theorem cylinderTransverseRadius_le_two_norm {e : Point} (he : ‖e‖ = 1) (x : Point) :
    cylinderTransverseRadius e x ≤ 2 * ‖x‖ := by
  calc
    _ ≤ ‖x‖ + ‖cylinderHeight e x • e‖ := norm_sub_le _ _
    _ = ‖x‖ + |cylinderHeight e x| := by rw [norm_smul, Real.norm_eq_abs, he, mul_one]
    _ ≤ _ := by linarith only [abs_cylinderHeight_le_norm he x]

private theorem cylinderCapGauge_nonneg (e : Point) (k : ℝ) (x : Point) :
    0 ≤ cylinderCapGauge e k x := (norm_nonneg _).trans (le_max_left _ _)

private theorem cylinderCapGauge_le_four_norm {e : Point} (he : ‖e‖ = 1)
    {k : ℝ} (hk₄ : k ≤ 4) (x : Point) :
    cylinderCapGauge e k x ≤ 4 * ‖x‖ := by
  refine max_le ((cylinderTransverseRadius_le_two_norm he x).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))) ?_
  exact mul_le_mul (by exact hk₄) (abs_cylinderHeight_le_norm he x) (abs_nonneg _) (by norm_num)

private theorem norm_le_two_cylinderCapGauge {e : Point} (he : ‖e‖ = 1)
    {k : ℝ} (hk : 1 ≤ k) (x : Point) :
    ‖x‖ ≤ 2 * cylinderCapGauge e k x := by
  have h₁ : cylinderTransverseRadius e x ≤ cylinderCapGauge e k x := le_max_left _ _
  have h₂ : |cylinderHeight e x| ≤ cylinderCapGauge e k x :=
    ((one_mul _).symm.le.trans (mul_le_mul_of_nonneg_right hk (abs_nonneg _))).trans (le_max_right _ _)
  have h := norm_add_le (x - cylinderHeight e x • e) (cylinderHeight e x • e)
  rw [sub_add_cancel, norm_smul, Real.norm_eq_abs, he, mul_one] at h
  exact h.trans (by change ‖x - cylinderHeight e x • e‖ ≤ _ at h₁; linarith only [h₁, h₂])

/-- The physical cylinder gauge is positively homogeneous. -/
theorem cylinderCapGauge_smul (e : Point) (k : ℝ) {s : ℝ} (hs : 0 ≤ s) (x : Point) :
    cylinderCapGauge e k (s • x) = s * cylinderCapGauge e k x := by
  have hh : cylinderHeight e (s • x) = s * cylinderHeight e x := real_inner_smul_right e x s
  have ht : cylinderTransverseRadius e (s • x) = s * cylinderTransverseRadius e x := by
    unfold cylinderTransverseRadius
    rw [hh, ← smul_smul, ← smul_sub, norm_smul, Real.norm_of_nonneg hs]
  unfold cylinderCapGauge
  rw [hh, ht, abs_mul, abs_of_nonneg hs,
    show k * (s * |cylinderHeight e x|) = s * (k * |cylinderHeight e x|) by ring,
    mul_max_of_nonneg _ _ hs]

private theorem cylinderCapGauge_abs_sub_le {e : Point} (he : ‖e‖ = 1)
    {k : ℝ} (hk : 1 ≤ k) (hk₄ : k ≤ 4) (x y : Point) :
    |cylinderCapGauge e k x - cylinderCapGauge e k y| ≤ 4 * ‖x - y‖ := by
  have hh : cylinderHeight e (x - y) = cylinderHeight e x - cylinderHeight e y :=
    inner_sub_right _ _ _
  have ht : (x - cylinderHeight e x • e) - (y - cylinderHeight e y • e) =
      (x - y) - cylinderHeight e (x - y) • e := by
    rw [hh, sub_smul]
    abel
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · calc
      _ ≤ ‖(x - cylinderHeight e x • e) - (y - cylinderHeight e y • e)‖ := abs_norm_sub_norm_le _ _
      _ ≤ 2 * ‖x - y‖ := by rw [ht]; exact cylinderTransverseRadius_le_two_norm he _
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)
  · have hk₀ : 0 ≤ k := zero_le_one.trans hk
    rw [← mul_sub, abs_mul, abs_of_nonneg hk₀]
    exact mul_le_mul hk₄ (((abs_abs_sub_abs_le_abs_sub _ _).trans_eq (congrArg abs hh.symm)).trans
      (abs_cylinderHeight_le_norm he _)) (abs_nonneg _) (by norm_num)

private theorem cylinderCapGauge_pos {e : Point} (he : ‖e‖ = 1) {k : ℝ} (hk : 1 ≤ k)
    {x : Point} (hx : x ≠ 0) : 0 < cylinderCapGauge e k x := by
  have h := norm_le_two_cylinderCapGauge he hk x
  have hx' := norm_pos_iff.2 hx
  linarith only [h, hx']

@[expose] def cylinderCapToBall (e : Point) (k : ℝ) (x : Point) : Point :=
  (cylinderCapGauge e k x / ‖x‖) • x

@[expose] def ballToCylinderCap (e : Point) (k : ℝ) (x : Point) : Point :=
  (‖x‖ / cylinderCapGauge e k x) • x

theorem cylinderCapToBall_norm (e : Point) (k : ℝ) (x : Point) :
    ‖cylinderCapToBall e k x‖ = cylinderCapGauge e k x := by
  by_cases hx : x = 0
  · subst x
    simp [cylinderCapToBall, cylinderCapGauge, cylinderTransverseRadius, cylinderHeight]
  · have h := norm_pos_iff.2 hx
    rw [cylinderCapToBall, norm_smul,
      Real.norm_of_nonneg (div_nonneg (cylinderCapGauge_nonneg e k x) h.le), div_mul_cancel₀ _ h.ne']

theorem cylinderCapGauge_ballToCylinderCap {e : Point} (he : ‖e‖ = 1) {k : ℝ} (hk : 1 ≤ k) (x : Point) :
    cylinderCapGauge e k (ballToCylinderCap e k x) = ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp [ballToCylinderCap, cylinderCapGauge, cylinderTransverseRadius, cylinderHeight]
  · have hg := cylinderCapGauge_pos he hk hx
    rw [ballToCylinderCap, cylinderCapGauge_smul e k (div_nonneg (norm_nonneg _) hg.le),
      div_mul_cancel₀ _ hg.ne']

theorem lipschitz_cylinderCapToBall {e : Point} (he : ‖e‖ = 1) {k : ℝ} (hk : 1 ≤ k) (hk₄ : k ≤ 4) :
    LipschitzWith 12 (cylinderCapToBall e k) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_ofNat, cylinderCapToBall]
  have h := radialRatio_norm_sub_le (cylinderCapGauge e k) norm (cylinderCapGauge_nonneg e k) norm_nonneg
    (fun _ => norm_pos_iff.2) (C := 4) (K := 1) (by norm_num) zero_le_one
    (cylinderCapGauge_le_four_norm he hk₄)
    (fun _ => by rw [one_mul]) (Lf := 4) (Lg := 1) (by norm_num) zero_le_one
    (cylinderCapGauge_abs_sub_le he hk hk₄)
    (fun x y => by simpa only [one_mul] using abs_norm_sub_norm_le x y) x y
  norm_num at h
  exact h

theorem lipschitz_ballToCylinderCap {e : Point} (he : ‖e‖ = 1) {k : ℝ} (hk : 1 ≤ k) (hk₄ : k ≤ 4) :
    LipschitzWith 20 (ballToCylinderCap e k) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_ofNat, ballToCylinderCap]
  have hc := norm_le_two_cylinderCapGauge he hk
  have h := radialRatio_norm_sub_le norm (cylinderCapGauge e k) norm_nonneg (cylinderCapGauge_nonneg e k)
    (fun _ => cylinderCapGauge_pos he hk) (C := 2) (K := 2) (by norm_num) (by norm_num)
    hc hc (Lf := 1) (Lg := 4) zero_le_one (by norm_num)
    (fun x y => by simpa only [one_mul] using abs_norm_sub_norm_le x y)
    (cylinderCapGauge_abs_sub_le he hk hk₄) x y
  norm_num at h
  exact h

/-- A terminal cylinder of bounded aspect ratio is carried to the same
radius ball by its exact radial coordinates. -/
def cylinderCapBallHomeomorph {e : Point} (he : ‖e‖ = 1) {k : ℝ} (hk : 1 ≤ k) (hk₄ : k ≤ 4) : Point ≃ₜ Point where
  toFun := cylinderCapToBall e k
  invFun := ballToCylinderCap e k
  left_inv x := by
    by_cases hx : x = 0
    · simp [hx, ballToCylinderCap, cylinderCapToBall]
    · have hn := norm_pos_iff.2 hx
      have hg := cylinderCapGauge_pos he hk hx
      unfold ballToCylinderCap
      rw [cylinderCapToBall_norm, cylinderCapToBall,
        cylinderCapGauge_smul e k (div_nonneg hg.le hn.le), smul_smul]
      have h : (cylinderCapGauge e k x / (cylinderCapGauge e k x / ‖x‖ * cylinderCapGauge e k x)) *
          (cylinderCapGauge e k x / ‖x‖) = 1 := by field_simp
      rw [h, one_smul]
  right_inv x := by
    by_cases hx : x = 0
    · simp [hx, ballToCylinderCap, cylinderCapToBall]
    · have hn := norm_pos_iff.2 hx
      have hg := cylinderCapGauge_pos he hk hx
      unfold cylinderCapToBall
      rw [cylinderCapGauge_ballToCylinderCap he hk, ballToCylinderCap, norm_smul,
        Real.norm_of_nonneg (div_nonneg hn.le hg.le), smul_smul]
      have h : (‖x‖ / (‖x‖ / cylinderCapGauge e k x * ‖x‖)) * (‖x‖ / cylinderCapGauge e k x) = 1 := by
        field_simp
      rw [h, one_smul]
  continuous_toFun := (lipschitz_cylinderCapToBall he hk hk₄).continuous
  continuous_invFun := (lipschitz_ballToCylinderCap he hk hk₄).continuous

/-- The physical terminal cap, with its chosen center, radius and half-height. -/
@[expose] def terminalCylinderCap (e c : Point) (R H : ℝ) : Set Point :=
  (fun x => x - c) ⁻¹' openAxisCylinder e R (-H) H

private theorem capRatio_bounds {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R) :
    0 < H ∧ 1 ≤ R / H ∧ R / H ≤ 4 := by
  have hH : 0 < H := (div_pos hR (by norm_num)).trans_le hLow
  exact ⟨hH, (one_le_div₀ hH).2 hHigh, (div_le_iff₀ hH).2 (by linarith only [hLow])⟩

/-- The ambient coordinates of the physical cap retain the common center,
the transverse scale and the prescribed half-height. -/
def terminalCylinderBallChart {e : Point} (he : ‖e‖ = 1) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R) : Point ≃ₜ Point :=
  (Homeomorph.addRight (-c)).trans
    (cylinderCapBallHomeomorph he (capRatio_bounds hR hLow hHigh).2.1 (capRatio_bounds hR hLow hHigh).2.2)

/-- The inverse cylinder chart adds the physical center to the inverse radial map. -/
theorem terminalCylinderBallChart_symm_apply {e : Point} (he : ‖e‖ = 1) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R) (x : Point) :
    (terminalCylinderBallChart he c hR hLow hHigh).symm x =
      c + ballToCylinderCap e (R / H) x := by
  change ballToCylinderCap e (R / H) x - (-c) = _
  rw [sub_neg_eq_add, add_comm]

theorem lipschitz_terminalCylinderBallChart {e : Point} (he : ‖e‖ = 1) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R) :
    LipschitzWith 12 (terminalCylinderBallChart he c hR hLow hHigh) := by
  have h := capRatio_bounds hR hLow hHigh
  change LipschitzWith 12 (cylinderCapToBall e (R / H) ∘ fun z : Point => z + (-c))
  simpa only [mul_one] using
    (lipschitz_cylinderCapToBall he h.2.1 h.2.2).comp (isometry_add_right (-c)).lipschitz

theorem lipschitz_terminalCylinderBallChart_symm {e : Point} (he : ‖e‖ = 1) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R) :
    LipschitzWith 20 ((terminalCylinderBallChart he c hR hLow hHigh).symm : Point → Point) := by
  have h := capRatio_bounds hR hLow hHigh
  change LipschitzWith 20 ((fun z : Point => z - (-c)) ∘ ballToCylinderCap e (R / H))
  simp only [sub_neg_eq_add]
  simpa only [one_mul] using (isometry_add_right c).lipschitz.comp
    (lipschitz_ballToCylinderCap he h.2.1 h.2.2)

/-- The chart norm is the original transverse-axial gauge. -/
theorem terminalCylinderBallChart_norm {e : Point} (he : ‖e‖ = 1) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R) (x : Point) :
    ‖terminalCylinderBallChart he c hR hLow hHigh x‖ = cylinderCapGauge e (R / H) (x - c) := by
  change ‖cylinderCapToBall e (R / H) (x + -c)‖ = cylinderCapGauge e (R / H) (x - c)
  rw [cylinderCapToBall_norm, sub_eq_add_neg]

theorem terminalCylinderCap_eq_preimage_ball {e : Point} (he : ‖e‖ = 1) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R) :
    terminalCylinderCap e c R H = terminalCylinderBallChart he c hR hLow hHigh ⁻¹' ball (0 : Point) R := by
  have hH := (capRatio_bounds hR hLow hHigh).1
  apply Set.ext
  intro x
  simp only [terminalCylinderCap, openAxisCylinder, mem_preimage, mem_setOf_eq, mem_ball_zero_iff,
    terminalCylinderBallChart_norm, cylinderCapGauge, max_lt_iff, ← abs_lt]
  have hScale : (R / H) * H = R := div_mul_cancel₀ _ hH.ne'
  have hk := div_pos hR hH
  constructor
  · rintro ⟨ht, hz⟩
    exact ⟨ht, (mul_lt_mul_of_pos_left hz hk).trans_eq hScale⟩
  · rintro ⟨ht, hz⟩
    exact ⟨ht, lt_of_not_ge fun h => (not_lt_of_ge (mul_le_mul_of_nonneg_left h hk.le))
      (hz.trans_eq hScale.symm)⟩

theorem terminalCylinderCap_frontier_eq_preimage_sphere {e : Point} (he : ‖e‖ = 1) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R) :
    frontier (terminalCylinderCap e c R H) =
      terminalCylinderBallChart he c hR hLow hHigh ⁻¹' sphere (0 : Point) R := by
  rw [terminalCylinderCap_eq_preimage_ball he c hR hLow hHigh, ← Homeomorph.preimage_frontier, frontier_ball _ hR.ne']

end Thesis.MeasureGeometry
