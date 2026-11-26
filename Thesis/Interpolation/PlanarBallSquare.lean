module

public import Thesis.Interpolation.SphericalCellGeometry
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import HarmonicMaps.Analysis.EuclideanHausdorffLipschitz

/-! Uniform radial bi-Lipschitz coordinates for the planar square and disk. -/

public section

noncomputable section

open Metric Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace Thesis

theorem radialRatio_norm_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hgZ : ∀ x, x ≠ 0 → 0 < g x) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hCnorm : ∀ x, f x ≤ C * g x) (hKnorm : ∀ x, ‖x‖ ≤ K * g x)
    {Lf Lg : ℝ} (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hfLip : ∀ x y, |f x - f y| ≤ Lf * ‖x - y‖)
    (hgLip : ∀ x y, |g x - g y| ≤ Lg * ‖x - y‖)
    (x y : E) : ‖(f x / g x) • x - (f y / g y) • y‖ ≤ (C + K * (Lf + C * Lg)) * ‖x - y‖ := by
  let a (x : E) := f x / g x
  have hA₀ (x : E) : 0 ≤ a x := div_nonneg (hf x) (hg x)
  have hA (x : E) : |a x| ≤ C := by
    rw [abs_of_nonneg (hA₀ x)]
    by_cases h : g x = 0
    · simpa only [a, h, div_zero] using hC
    · exact (div_le_iff₀ (lt_of_le_of_ne (hg x) (fun he => h he.symm))).2 (hCnorm x)
  have hLip : 0 ≤ Lf + C * Lg := add_nonneg hLf (mul_nonneg hC hLg)
  have hNC : C ≤ C + K * (Lf + C * Lg) := le_add_of_nonneg_right (mul_nonneg hK hLip)
  by_cases hy : y = 0
  · subst y
    change ‖a x • x - a 0 • 0‖ ≤ _
    rw [smul_zero, sub_zero, sub_zero, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((hA x).trans hNC) (norm_nonneg _)
  by_cases hx : x = 0
  · subst x
    change ‖a 0 • 0 - a y • y‖ ≤ _
    rw [smul_zero, zero_sub, zero_sub, norm_neg, norm_neg, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((hA y).trans hNC) (norm_nonneg _)
  have hX := hgZ x hx
  have hY := hgZ y hy
  have hEq : a x - a y = (f x - f y + a x * (g y - g x)) / g y := by
    dsimp only [a]
    field_simp
    ring
  have hNumer : |f x - f y + a x * (g y - g x)| ≤ (Lf + C * Lg) * ‖x - y‖ := by
    calc
      _ ≤ |f x - f y| + |a x * (g y - g x)| := abs_add_le _ _
      _ = |f x - f y| + |a x| * |g x - g y| := by rw [abs_mul, abs_sub_comm (g y) (g x)]
      _ ≤ Lf * ‖x - y‖ + C * (Lg * ‖x - y‖) := add_le_add (hfLip x y)
        (mul_le_mul (hA x) (hgLip x y) (abs_nonneg _) hC)
      _ = _ := by ring
  have hQuot : |a x - a y| * ‖y‖ ≤ K * (Lf + C * Lg) * ‖x - y‖ := by
    rw [hEq, abs_div, abs_of_pos hY]
    calc
      _ = |f x - f y + a x * (g y - g x)| * (‖y‖ / g y) := by ring
      _ ≤ ((Lf + C * Lg) * ‖x - y‖) * K := mul_le_mul hNumer
        ((div_le_iff₀ hY).2 (hKnorm y)) (by positivity) (by positivity)
      _ = _ := by ring
  change ‖a x • x - a y • y‖ ≤ _
  rw [show a x • x - a y • y = a x • (x - y) + (a x - a y) • y by
    rw [smul_sub, sub_smul]
    abel]
  calc
    _ ≤ ‖a x • (x - y)‖ + ‖(a x - a y) • y‖ := norm_add_le _ _
    _ ≤ C * ‖x - y‖ + K * (Lf + C * Lg) * ‖x - y‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)) hQuot
    _ = _ := by ring

private theorem abs_coordinateNorm_sub_le {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    |‖WithLp.ofLp x‖ - ‖WithLp.ofLp y‖| ≤ ‖x - y‖ := by
  refine (abs_norm_sub_norm_le (WithLp.ofLp x) (WithLp.ofLp y)).trans ?_
  rw [← WithLp.ofLp_sub]
  exact (StratificationTheory.cube_coordinate_norm_comparison (x - y)).1

theorem lipschitz_coordinateCubeToBall_plane : LipschitzWith 3 (coordinateCubeToBall (n := 2)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_ofNat, coordinateCubeToBall]
  have h := radialRatio_norm_sub_le (fun z : Plane => ‖WithLp.ofLp z‖) norm
    (fun _ => norm_nonneg _) norm_nonneg (fun _ => norm_pos_iff.2)
    (C := 1) (K := 1) zero_le_one zero_le_one
    (fun z => by simpa only [one_mul] using (StratificationTheory.cube_coordinate_norm_comparison z).1)
    (fun _ => by rw [one_mul]) (Lf := 1) (Lg := 1) zero_le_one zero_le_one
    (fun x y => by simpa only [one_mul] using abs_coordinateNorm_sub_le x y)
    (fun x y => by simpa only [one_mul] using abs_norm_sub_norm_le x y) x y
  norm_num at h
  exact h

theorem lipschitz_ballToCoordinateCube_plane : LipschitzWith 8 (ballToCoordinateCube (n := 2)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_ofNat, ballToCoordinateCube]
  have hcmp (z : Plane) : ‖z‖ ≤ 2 * ‖WithLp.ofLp z‖ :=
    (StratificationTheory.cube_coordinate_norm_comparison z).2
  have h := radialRatio_norm_sub_le (norm : Plane → ℝ) (fun z : Plane => ‖WithLp.ofLp z‖)
    norm_nonneg (fun _ => norm_nonneg _) (fun _ => coordinateNorm_pos)
    (C := 2) (K := 2) (by norm_num) (by norm_num) hcmp hcmp (Lf := 1) (Lg := 1) zero_le_one zero_le_one
    (fun x y => by simpa only [one_mul] using abs_norm_sub_norm_le x y)
    (fun x y => by simpa only [one_mul] using abs_coordinateNorm_sub_le x y) x y
  norm_num at h
  exact h

/-- The actual planar square and disk are related by this ambient radial homeomorphism. -/
@[expose] def planarSquareBallHomeomorph : Plane ≃ₜ Plane where
  toFun := coordinateCubeToBall
  invFun := ballToCoordinateCube
  left_inv := ballToCoordinateCube_coordinateCubeToBall
  right_inv := coordinateCubeToBall_ballToCoordinateCube
  continuous_toFun := continuous_coordinateCubeToBall
  continuous_invFun := continuous_ballToCoordinateCube

private theorem quasiMeasurePreserving_of_lipschitz_inverse (e : Plane ≃ₜ Plane) {C : ℝ≥0}
    (hLip : LipschitzWith C (e.symm : Plane → Plane)) :
    QuasiMeasurePreserving (e : Plane → Plane) volume volume := by
  refine ⟨e.continuous.measurable, Measure.AbsolutelyContinuous.mk ?_⟩
  intro U hU hZero
  rw [Measure.map_apply e.continuous.measurable hU, ← e.image_symm]
  have h := HarmonicMaps.euclideanHausdorff_lipschitzOn_image_le_volume
    (hLip.lipschitzOnWith (s := Set.univ)) (subset_univ U)
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume, hZero, mul_zero] at h
  exact nonpos_iff_eq_zero.1 h

theorem planarSquareBallHomeomorph_quasiMeasurePreserving :
    QuasiMeasurePreserving (planarSquareBallHomeomorph : Plane → Plane) volume volume :=
  quasiMeasurePreserving_of_lipschitz_inverse _ lipschitz_ballToCoordinateCube_plane

theorem planarSquareBallHomeomorph_symm_quasiMeasurePreserving :
    QuasiMeasurePreserving (planarSquareBallHomeomorph.symm : Plane → Plane) volume volume :=
  quasiMeasurePreserving_of_lipschitz_inverse _ lipschitz_coordinateCubeToBall_plane

@[expose] def planarSquare (R : ℝ) : Set Plane := {x | ‖WithLp.ofLp x‖ < R}

theorem planarSquare_eq_preimage_ball (R : ℝ) :
    planarSquare R = planarSquareBallHomeomorph ⁻¹' ball (0 : Plane) R := by
  ext x
  change ‖WithLp.ofLp x‖ < R ↔ coordinateCubeToBall x ∈ ball (0 : Plane) R
  rw [mem_ball, dist_zero_right, norm_coordinateCubeToBall]

theorem frontier_planarSquare {R : ℝ} (hR : 0 < R) :
    frontier (planarSquare R) = {x : Plane | ‖WithLp.ofLp x‖ = R} := by
  rw [planarSquare_eq_preimage_ball, ← planarSquareBallHomeomorph.preimage_frontier,
    frontier_ball (0 : Plane) hR.ne']
  ext x
  change (coordinateCubeToBall x ∈ sphere (0 : Plane) R) ↔ _
  rw [mem_sphere_zero_iff_norm, norm_coordinateCubeToBall]
  rfl

end Thesis
