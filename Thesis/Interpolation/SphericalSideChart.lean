module

public import Thesis.Interpolation.SphericalGrid

/-! Uniform coordinates for the lateral faces of the spherical lattice layer. -/

@[expose] public section

open Metric Set

namespace Thesis

theorem radial_dist_bounds {x y : Point} {r s : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hr : r ∈ Icc (1 / 2 : ℝ) 1)
    (hs : s ∈ Icc (1 / 2 : ℝ) 1) :
    dist (r • x) (s • y) ≤ dist x y + dist r s ∧
      dist r s ≤ dist (r • x) (s • y) ∧ dist x y ≤ 4 * dist (r • x) (s • y) := by
  have hr₀ : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hr.1
  have hs₀ : 0 ≤ s := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hs.1
  have hUpper : ‖r • x - s • y‖ ≤ ‖x - y‖ + |r - s| := by
    have hSplit : r • x - s • y = r • (x - y) + (r - s) • y := by
      simp only [smul_sub, sub_smul]
      abel
    rw [hSplit]
    calc
      _ ≤ ‖r • (x - y)‖ + ‖(r - s) • y‖ := norm_add_le _ _
      _ = r * ‖x - y‖ + |r - s| := by
        simp only [norm_smul, Real.norm_of_nonneg hr₀, Real.norm_eq_abs, hy, mul_one]
      _ ≤ _ := add_le_add (mul_le_of_le_one_left (norm_nonneg _) hr.2) le_rfl
  have hRadial : |r - s| ≤ ‖r • x - s • y‖ := by
    have h := abs_norm_sub_norm_le (r • x) (s • y)
    simpa only [norm_smul, Real.norm_of_nonneg hr₀, Real.norm_of_nonneg hs₀, hx, hy, mul_one] using h
  have hAng : ‖x - y‖ ≤ 4 * ‖r • x - s • y‖ := by
    have hSplit : r • (x - y) = (r • x - s • y) + (s - r) • y := by
      simp only [smul_sub, sub_smul]
      abel
    have hn : r * ‖x - y‖ ≤ ‖r • x - s • y‖ + |r - s| := calc
      _ = ‖r • (x - y)‖ := by rw [norm_smul, Real.norm_of_nonneg hr₀]
      _ = _ := congrArg norm hSplit
      _ ≤ ‖r • x - s • y‖ + ‖(s - r) • y‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, hy, mul_one, Real.norm_eq_abs, abs_sub_comm]
    have hlo := mul_le_mul_of_nonneg_right hr.1 (norm_nonneg (x - y))
    linarith only [hlo, hn, hRadial]
  simpa only [dist_eq_norm, Real.norm_eq_abs] using And.intro hUpper ⟨hRadial, hAng⟩

/-- The radial chart of one selected side uses independent edge and radius
parameters. Its edge points are radially normalized from the same cube. -/
noncomputable def sphericalLateralEdge (c : Point) (h : ℝ) (e : TensorGridEdge)
    (z : ℝ × ℝ) : Point :=
  z.2 • NormedSpace.normalize (tensorGridEdgePoint c h e z.1)

/-- All lateral faces of the selected cube have the same bi-Lipschitz bounds,
including the edge endpoints at both spherical radii. -/
theorem sphericalLateralEdge_bilipschitz {c : Point} {h a : ℝ} (hh : 0 < h) {m : ℕ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    (ha : 1 / 2 ≤ a) {e : TensorGridEdge} (he : e ∈ cubeBoundaryEdges m)
    {z w : ℝ × ℝ} (hz : z ∈ Icc (0 : ℝ) h ×ˢ Icc a 1) (hw : w ∈ Icc (0 : ℝ) h ×ˢ Icc a 1) :
    dist (sphericalLateralEdge c h e z) (sphericalLateralEdge c h e w) ≤ 33 * dist z w ∧
      dist z w ≤ 68 * dist (sphericalLateralEdge c h e z) (sphericalLateralEdge c h e w) := by
  let x := NormedSpace.normalize (tensorGridEdgePoint c h e z.1)
  let y := NormedSpace.normalize (tensorGridEdgePoint c h e w.1)
  obtain ⟨hx, hy, hu, hl⟩ := normalized_grid_edge_dist hh hc hm he hz.1 hw.1
  have hx₁ : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
  have hy₁ : ‖y‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hy
  obtain ⟨hR, hRad, hAng⟩ := radial_dist_bounds (r := z.2) (s := w.2) hx₁ hy₁
    ⟨ha.trans hz.2.1, hz.2.2⟩ ⟨ha.trans hw.2.1, hw.2.2⟩
  change dist (z.2 • x) (w.2 • y) ≤ 33 * dist z w ∧ dist z w ≤ 68 * dist (z.2 • x) (w.2 • y)
  rw [Prod.dist_eq]
  constructor
  · have h₁ := mul_le_mul_of_nonneg_left (le_max_left (dist z.1 w.1) (dist z.2 w.2))
      (by norm_num : (0 : ℝ) ≤ 32)
    linarith only [hR, hu, h₁, le_max_right (dist z.1 w.1) (dist z.2 w.2)]
  · apply max_le
    · linarith only [hl, hAng]
    · linarith only [hRad, dist_nonneg (x := z.2 • x) (y := w.2 • y)]

end Thesis
