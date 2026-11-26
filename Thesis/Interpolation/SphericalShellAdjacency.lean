module

public import Thesis.Interpolation.SphericalShellPiecewise

/-! Exact adjacent shell cells at the relative interiors of their radial sides. -/

public section

open Filter MeasureTheory Metric Set

namespace Thesis

abbrev ShellSideIndex (m : ℕ) := ShellCellIndex m × (Fin 2 × Bool)

/-- The edge common to all charts representing this physical side. -/
@[expose] def ShellSideIndex.edge {m : ℕ} (s : ShellSideIndex m) : ↥(cubeBoundaryEdges m) :=
  tensorSquareCoordinateEdge s.1 s.2.1 s.2.2

/-- An actual pair of incident cells and their common physical side, with
the normal oriented towards the positive half-space cell. -/
structure ShellLocalInterface (c : Point) (h : ℝ) (m : ℕ) (y : Point) where
  lower : ShellSideIndex m
  upper : ShellSideIndex m
  distinct_cells : lower.1 ≠ upper.1
  common_edge : lower.edge = upper.edge
  normal : Point →L[ℝ] ℝ
  normal_ne : normal ≠ 0
  normal_zero : normal y = 0
  region : Set Point
  region_open : IsOpen region
  point_mem : y ∈ region
  lower_closed : ∀ z ∈ region, z ∈ sphericalClosedCell c h lower.1.val ↔ normal z ≤ 0
  upper_closed : ∀ z ∈ region, z ∈ sphericalClosedCell c h upper.1.val ↔ 0 ≤ normal z
  lower_interior : ∀ z ∈ region, z ∈ interior (sphericalClosedCell c h lower.1.val) ↔ normal z < 0
  upper_interior : ∀ z ∈ region, z ∈ interior (sphericalClosedCell c h upper.1.val) ↔ 0 < normal z
  common_side : ∀ z ∈ region, normal z = 0 → ∃ t r : ℝ,
    t ∈ Ioo 0 h ∧ r ∈ Ioo (1 - h) 1 ∧ z = sphericalLateralEdge c h upper.edge.val (t, r)

/-- Outside the finite radial corner lines, every point of the open shell
which is not in a cell interior has two neighboring half-space cells. -/
theorem exists_shellLocalInterface {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32)) (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {y : Point} (hy : y ∈ (sphericalShellDomain h).val) (hReg : y ∉ sphericalShellCornerLines c h m)
    (hNoInt : ∀ f : ShellCellIndex m, y ∉ interior (sphericalClosedCell c h f.val)) :
    Nonempty (ShellLocalInterface c h m y) := by
  classical
  let V (f : ShellCellIndex m) := sphericalClosedCell c h f.val
  have hClosed (f : ShellCellIndex m) : IsClosed (V f) :=
    (sphericalClosedCell_geometry hh hh' hc hm f.property).1.isClosed
  have cover (z : Point) (hz : z ∈ (sphericalShellDomain h).val) : ∃ f : ShellCellIndex m, z ∈ V f := by
    have hZ : z ∈ ⋃ f ∈ cubeBoundarySquares m, sphericalClosedCell c h f := by
      rw [iUnion_sphericalClosedCell_eq_closedShell hh hh' hc hm]
      change ‖z - 0‖ ∈ Ioo (1 - h) 1 at hz
      change ‖z‖ ∈ Icc (1 - h) 1
      simpa only [sub_zero] using Ioo_subset_Icc_self hz
    obtain ⟨f, hf, hz'⟩ := mem_iUnion₂.mp hZ
    exact ⟨⟨f, hf⟩, hz'⟩
  have regularSide (f : ShellCellIndex m) (hyf : y ∈ V f) :
      ∃ (i : Fin 2) (b : Bool) (t r : ℝ), t ∈ Ioo (0 : ℝ) h ∧ r ∈ Ioo (1 - h) 1 ∧
        y = sphericalCellPoint c h f.val (shellSquareSideParameters i (if b then h else 0) t, r) := by
    have hb : y ∈ frontier (V f) := by
      rw [frontier, (hClosed f).closure_eq]
      exact ⟨hyf, hNoInt f⟩
    exact exists_shellCell_lateral_side_of_regular_boundary hh hh' hc hm f hb hy hReg
  obtain ⟨f, hyf⟩ := cover y hy
  obtain ⟨i, b, s, r, hs, hr, hPoint⟩ := regularSide f hyf
  obtain ⟨L, N, hL, hN, hNy, hLy, hC₁, hI₁, hSide₁⟩ :=
    sphericalClosedCell_halfspace_near_side hh hh' hc hm f.property i b hs hr
  rw [← hPoint] at hNy hLy
  let R : Set Point := ⋂ g : ShellCellIndex m, if y ∈ V g then univ else (V g)ᶜ
  have hR : IsOpen R := isOpen_iInter_of_finite fun g => by
    by_cases hy' : y ∈ V g
    · simp [hy']
    · simp [hy', (hClosed g).isOpen_compl]
  have hyR : y ∈ R := mem_iInter.mpr fun g => by
    by_cases hy' : y ∈ V g <;> simp [hy']
  let N₀ := N ∩ R ∩ (sphericalShellDomain h).val
  have hN₀ : IsOpen N₀ := (hN.inter hR).inter (sphericalShellDomain h).property
  have hy₀ : y ∈ N₀ := ⟨⟨hNy, hyR⟩, hy⟩
  obtain ⟨d, hd⟩ := exists_pos_of_ne_zero_planeForm L hL
  obtain ⟨ε, hε, hZ⟩ := exists_positive_step_mem_open hN₀ hy₀ (-d)
  let z := y + ε • (-d)
  have hz : z ∈ N₀ := hZ
  have hLz : L z < 0 := by
    simp only [z, map_add, map_smul, map_neg, hLy, zero_add, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hε (neg_neg_of_pos hd)
  obtain ⟨g, hzg⟩ := cover z hz.2
  have hgf : g ≠ f := by
    intro h
    exact (not_le_of_gt hLz) ((hC₁ z hz.1.1).mp (h ▸ hzg))
  have hyg : y ∈ V g := by
    by_contra h
    have hn := mem_iInter.mp hz.1.2 g
    simp only [h, if_false] at hn
    exact hn hzg
  obtain ⟨k, p, t, R₀, ht, hR₀, hPoint₂⟩ := regularSide g hyg
  obtain ⟨M, S, hM, hS, hSy, hMy, hC₂, hI₂, hSide₂⟩ :=
    sphericalClosedCell_halfspace_near_side hh hh' hc hm g.property k p ht hR₀
  rw [← hPoint₂] at hSy hMy
  let A := N₀ ∩ S
  have hA : IsOpen A := hN₀.inter hS
  have hyA : y ∈ A := ⟨hy₀, hSy⟩
  have hDis (w : Point) (hw : w ∈ A) : ¬(0 < L w ∧ 0 < M w) := by
    rintro ⟨hLw, hMw⟩
    exact Set.disjoint_left.mp (sphericalClosedCell_disjoint_interiors hh hh' hc hm f.property g.property
      (fun e => hgf (Subtype.ext e.symm))) ((hI₁ w hw.1.1.1).mpr hLw) ((hI₂ w hw.2).mpr hMw)
  obtain ⟨C, hC, hOpp⟩ := opposite_planeForms_of_disjoint_near hL hM hA hyA hLy hMy hDis
  have hEq : (tensorSquareCoordinateEdge g k p).val = (tensorSquareCoordinateEdge f i b).val := by
    have hP₁ := hPoint.trans (shellSquareSide_point_on_edge c h f i b s r)
    have hP₂ := hPoint₂.trans (shellSquareSide_point_on_edge c h g k p t R₀)
    exact (sphericalLateralEdge_eq_of_open_point hh hc hm (tensorSquareCoordinateEdge g k p).property
      (tensorSquareCoordinateEdge f i b).property ht hs (by linarith only [hR₀.1, hh'])
      (by linarith only [hr.1, hh']) (hP₂.symm.trans hP₁)).1
  refine ⟨{ lower := (g, k, p)
            upper := (f, i, b)
            distinct_cells := hgf
            common_edge := Subtype.ext hEq
            normal := L
            normal_ne := hL
            normal_zero := hLy
            region := A
            region_open := hA
            point_mem := hyA
            lower_closed := ?_
            upper_closed := fun z hz => hC₁ z hz.1.1.1
            lower_interior := ?_
            upper_interior := fun z hz => hI₁ z hz.1.1.1
            common_side := ?_ }⟩
  · intro z hz
    rw [hC₂ z hz.2, hOpp z, neg_mul, neg_nonneg]
    exact ⟨fun h => le_of_not_gt (fun h' => (not_lt_of_ge h) (mul_pos hC h')),
      fun h => mul_nonpos_of_nonneg_of_nonpos hC.le h⟩
  · intro z hz
    rw [hI₂ z hz.2, hOpp z, neg_mul, neg_pos]
    exact ⟨fun h => lt_of_not_ge (fun h' => (not_lt_of_ge (mul_nonneg hC.le h')) h),
      fun h => mul_neg_of_pos_of_neg hC h⟩
  · intro z hz hzL
    obtain ⟨t, r, ht, hr, hz'⟩ := hSide₁ z hz.1.1.1 hzL
    exact ⟨t, r, ht, hr, hz'.trans (shellSquareSide_point_on_edge c h f i b t r)⟩

end Thesis
