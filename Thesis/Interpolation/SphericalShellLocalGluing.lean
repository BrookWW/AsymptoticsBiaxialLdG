module

public import Thesis.Interpolation.SphericalShellAdjacency

/-! The actual adjacent ambient cell graphs glue near their common side. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped Topology

namespace Thesis

private theorem memW12_restrict_open {n q : ℕ} {U V : OpenDomain n} {u : Domain n → Ambient q}
    {D : Domain n → HarmonicMaps.Gradient n q} (hu : MemW12 U u D) (hV : V.val ⊆ U.val) : MemW12 V u D :=
  ⟨hu.1.mono hV, hu.2.1.mono_measure (Measure.restrict_mono_set volume hV),
    fun i => (hu.2.2 i).mono_measure (Measure.restrict_mono_set volume hV)⟩

/-- The two actual cell fields glue on a ball about the common face point.
Only their continuous face values are used to recover the native L² traces. -/
theorem memW12_near_shellLocalInterface {q m : ℕ} {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32)) (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {y : Point} (J : ShellLocalInterface c h m y)
    (u : ShellCellIndex m → Point → Ambient q) (D : ShellCellIndex m → Point → HarmonicMaps.Gradient 3 q)
    (hW : ∀ f, MemW12 (sphericalCellOpenDomain c h f.val) (u f) (D f))
    {NL NR : Set Point} (hNL : IsOpen NL) (hNR : IsOpen NR) (hyL : y ∈ NL) (hyR : y ∈ NR)
    (hCL : ContinuousOn (u J.lower.1) (NL ∩ sphericalClosedCell c h J.lower.1.val))
    (hCR : ContinuousOn (u J.upper.1) (NR ∩ sphericalClosedCell c h J.upper.1.val))
    (hSame : ∀ z ∈ J.region, J.normal z = 0 → u J.lower.1 z = u J.upper.1 z) :
    ∃ r : ℝ, 0 < r ∧ MemW12 (ballDomain y r) (sphericalShellPiecewiseField c h u)
      (sphericalShellPiecewiseDerivative c h D) := by
  classical
  let L := J.normal
  let S := J.region ∩ NL ∩ NR
  have hS : IsOpen S := (J.region_open.inter hNL).inter hNR
  obtain ⟨ρ, hρ, hBall⟩ := Metric.isOpen_iff.mp hS y ⟨⟨J.point_mem, hyL⟩, hyR⟩
  let ρ₀ := ρ / 2
  have hρ₀ : 0 < ρ₀ := half_pos hρ
  have hClosed : closedBall y ρ₀ ⊆ S := (closedBall_subset_ball (half_lt_self hρ)).trans hBall
  obtain ⟨Q, a, ha, hQ⟩ := exists_cellInterface_normalFrame L J.normal_ne
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  have hQy : (e (Q.symm y)).2 0 = 0 :=
    (mul_eq_zero.mp ((hQ y).symm.trans J.normal_zero)).resolve_left ha.ne'
  obtain ⟨δ, hδ, hySlab, hSlab⟩ := exists_rotatedSlab_in_closedBall Q y hρ₀ hQy
  let U := ballDomain (e (Q.symm y)).1 δ
  let V := rotatedCellInterfaceSlab U Q (-δ) δ
  letI : IsFiniteMeasure (volume.restrict U.val) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hQz (z : Point) : L (Q z) = a * (e z).2 0 := by rw [hQ, Q.symm_apply_apply]
  have hSmallSide (z : Point) (hz : z ∈ cellInterfaceClosedSlab U (-δ) δ) : Q z ∈ S := hClosed (hSlab z hz)
  let K₁ := closedBall y ρ₀ ∩ sphericalClosedCell c h J.lower.1.val
  let K₂ := closedBall y ρ₀ ∩ sphericalClosedCell c h J.upper.1.val
  have hLeftClosed (z : Point) (hz : z ∈ cellInterfaceClosedSlab U (-δ) 0) : Q z ∈ K₁ := by
    have hz' : z ∈ cellInterfaceClosedSlab U (-δ) δ := ⟨hz.1, Icc_subset_Icc_right hδ.le hz.2⟩
    have hS' := hSmallSide z hz'
    refine ⟨hSlab z hz', (J.lower_closed _ hS'.1.1).mpr ?_⟩
    change L (Q z) ≤ 0
    rw [hQz]
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hz.2.2
  have hRightClosed (z : Point) (hz : z ∈ cellInterfaceClosedSlab U 0 δ) : Q z ∈ K₂ := by
    have hz' : z ∈ cellInterfaceClosedSlab U (-δ) δ := ⟨hz.1, Icc_subset_Icc_left (neg_nonpos.mpr hδ.le) hz.2⟩
    have hS' := hSmallSide z hz'
    refine ⟨hSlab z hz', (J.upper_closed _ hS'.1.1).mpr ?_⟩
    change 0 ≤ L (Q z)
    rw [hQz]
    exact mul_nonneg ha.le hz.2.1
  have hK₁Cont : ContinuousOn (u J.lower.1) K₁ := hCL.mono (fun _ hz => ⟨(hClosed hz.1).1.2, hz.2⟩)
  have hK₂Cont : ContinuousOn (u J.upper.1) K₂ := hCR.mono (fun _ hz => ⟨(hClosed hz.1).2, hz.2⟩)
  have hClosedCell (f : ShellCellIndex m) : IsClosed (sphericalClosedCell c h f.val) :=
    (sphericalClosedCell_geometry hh hh' hc hm f.property).1.isClosed
  obtain ⟨B₁, hB₁⟩ := ((isCompact_closedBall y ρ₀).inter_right (hClosedCell J.lower.1)).exists_bound_of_continuousOn hK₁Cont
  obtain ⟨B₂, hB₂⟩ := ((isCompact_closedBall y ρ₀).inter_right (hClosedCell J.upper.1)).exists_bound_of_continuousOn hK₂Cont
  have hU₁ : (rotatedCellInterfaceSlab U Q (-δ) 0).val ⊆ (sphericalCellOpenDomain c h J.lower.1.val).val := by
    intro z hz
    have hz' : Q.symm z ∈ cellInterfaceClosedSlab U (-δ) 0 := ⟨hz.1, Ioo_subset_Icc_self hz.2⟩
    have hK := hLeftClosed (Q.symm z) hz'
    rw [Q.apply_symm_apply] at hK
    apply (J.lower_interior _ (hClosed hK.1).1.1).mpr
    change L z < 0
    rw [hQ]
    exact mul_neg_of_pos_of_neg ha hz.2.2
  have hU₂ : (rotatedCellInterfaceSlab U Q 0 δ).val ⊆ (sphericalCellOpenDomain c h J.upper.1.val).val := by
    intro z hz
    have hz' : Q.symm z ∈ cellInterfaceClosedSlab U 0 δ := ⟨hz.1, Ioo_subset_Icc_self hz.2⟩
    have hK := hRightClosed (Q.symm z) hz'
    rw [Q.apply_symm_apply] at hK
    apply (J.upper_interior _ (hClosed hK.1).1.1).mpr
    change 0 < L z
    rw [hQ]
    exact mul_pos ha hz.2.1
  have hMatch (x : Domain 2) (hx : x ∈ U.val) :
      u J.lower.1 (Q (cellInterfacePoint x 0)) = u J.upper.1 (Q (cellInterfacePoint x 0)) := by
    have hPoint : cellInterfacePoint x 0 ∈ cellInterfaceClosedSlab U (-δ) δ := by
      simpa only [cellInterfaceClosedSlab, cellInterfacePoint, ContinuousLinearEquiv.apply_symm_apply,
        mem_setOf_eq, PiLp.single_apply, ite_true] using And.intro hx (show (0 : ℝ) ∈ Icc (-δ) δ from
          ⟨neg_nonpos.mpr hδ.le, hδ.le⟩)
    apply hSame _ (hSmallSide _ hPoint).1.1
    change L (Q (cellInterfacePoint x 0)) = 0
    rw [hQz]
    simp [cellInterfacePoint, e]
  have hGlue := memW12_rotatedCellInterface_glue U Q (neg_lt_zero.mpr hδ) hδ
    (memW12_restrict_open (hW J.lower.1) hU₁) (memW12_restrict_open (hW J.upper.1) hU₂)
    (hK₁Cont.comp Q.continuous.continuousOn hLeftClosed) (hK₂Cont.comp Q.continuous.continuousOn hRightClosed)
    (B := max B₁ B₂)
    (fun z hz => (hB₁ _ (hLeftClosed z hz)).trans (le_max_left _ _))
    (fun z hz => (hB₂ _ (hRightClosed z hz)).trans (le_max_right _ _)) hMatch
  let s : Point → ℝ := fun z => (e (Q.symm z)).2 0
  let w := sphericalShellPiecewiseField c h u
  let E := sphericalShellPiecewiseDerivative c h D
  have hNoPlane : ∀ᵐ z : Point ∂volume, L z ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using volume_cellInterface_plane L J.normal_ne
  have hEq : ∀ᵐ z ∂volume.restrict V.val,
      (if s z < 0 then u J.lower.1 z else u J.upper.1 z) = w z ∧
        (fun i => if s z < 0 then D J.lower.1 z i else D J.upper.1 z i) = E z := by
    filter_upwards [ae_restrict_of_ae hNoPlane, ae_restrict_mem V.property.measurableSet] with z hLz hz
    have hs : s z ∈ Ioo (-δ) δ := hz.2
    have hsz : s z ≠ 0 := fun e' => hLz (by rw [hQ]; change a * s z = 0; rw [e', mul_zero])
    rcases lt_or_gt_of_ne hsz with hl | hr
    · have hslab : z ∈ (rotatedCellInterfaceSlab U Q (-δ) 0).val := ⟨hz.1, hs.1, hl⟩
      obtain ⟨h₁, h₂⟩ := sphericalShellPiecewise_eq_on_cell hh hh' hc hm u D J.lower.1 (hU₁ hslab)
      exact ⟨by simpa only [if_pos hl] using h₁.symm, by simpa only [if_pos hl] using h₂.symm⟩
    · have hslab : z ∈ (rotatedCellInterfaceSlab U Q 0 δ).val := ⟨hz.1, hr, hs.2⟩
      obtain ⟨h₁, h₂⟩ := sphericalShellPiecewise_eq_on_cell hh hh' hc hm u D J.upper.1 (hU₂ hslab)
      exact ⟨by simpa only [if_neg (not_lt_of_ge hr.le)] using h₁.symm,
        by simpa only [if_neg (not_lt_of_ge hr.le)] using h₂.symm⟩
  have hV : MemW12 V w E := hGlue.congr_ae (hEq.mono fun _ h => h.1) (hEq.mono fun _ h => h.2)
  obtain ⟨r, hr, hR⟩ := Metric.isOpen_iff.mp V.property y hySlab
  exact ⟨r, hr, memW12_restrict_open hV hR⟩

/-- Actual continuous common side values glue the original finite shell
graphs, including the removable radial corner lines. -/
theorem sphericalShellPiecewise_memW12_of_common_sides {q m : ℕ} {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32)) (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    (u : ShellCellIndex m → Point → Ambient q) (D : ShellCellIndex m → Point → HarmonicMaps.Gradient 3 q)
    (hGraph : ∀ f, MemW12 (sphericalCellOpenDomain c h f.val) (u f) (D f))
    {B : ℝ} (hB : ∀ f, ∀ᵐ x ∂volume.restrict (sphericalCellOpenDomain c h f.val).val, ‖u f x‖ ≤ B)
    (edge : ↥(cubeBoundaryEdges m) → ℝ × ℝ → Ambient q)
    (hSide : ∀ (s : ShellSideIndex m) {t r : ℝ}, t ∈ Ioo (0 : ℝ) h → r ∈ Ioo (1 - h) 1 →
      let z := sphericalLateralEdge c h s.edge.val (t, r)
      u s.1 z = edge s.edge (t, r) ∧ ∃ N : Set Point, IsOpen N ∧ z ∈ N ∧
        ContinuousOn (u s.1) (N ∩ sphericalClosedCell c h s.1.val)) :
    let w := sphericalShellPiecewiseField c h u
    let E := sphericalShellPiecewiseDerivative c h D
    MemW12 (sphericalShellDomain h) w E ∧ ∀ᵐ x ∂volume.restrict (sphericalShellDomain h).val, ‖w x‖ ≤ B := by
  classical
  intro w E
  obtain ⟨hWLp, hDLp, hWeak, _, _, hInherit⟩ := sphericalShellPiecewise_data hh hh' hc hm u D hGraph
  have hBound := hInherit (fun y => ‖y‖ ≤ B) hB
  refine ⟨sphericalShell_memW12_of_off_cornerLines (m := m) c h hWLp
    (fun i => (hDLp i).mono_measure Measure.restrict_le_self) hBound ?_, hBound⟩
  intro y hy hyReg
  by_cases hInt : ∃ f : ShellCellIndex m, y ∈ (sphericalCellOpenDomain c h f.val).val
  · obtain ⟨f, hf⟩ := hInt
    obtain ⟨r, hr, hSub⟩ := Metric.isOpen_iff.mp (sphericalCellOpenDomain c h f.val).property y hf
    exact ⟨r, hr, memW12_restrict_open (hWeak f) hSub⟩
  · obtain ⟨J⟩ := exists_shellLocalInterface hh hh' hc hm hy hyReg (not_exists.mp hInt)
    obtain ⟨t, r, ht, hr, hY⟩ := J.common_side y J.point_mem J.normal_zero
    have hY' : y = sphericalLateralEdge c h J.lower.edge.val (t, r) := by rwa [J.common_edge]
    obtain ⟨_, NL, hNL, hyL, hCL⟩ := hSide J.lower ht hr
    obtain ⟨_, NR, hNR, hyR, hCR⟩ := hSide J.upper ht hr
    apply memW12_near_shellLocalInterface hh hh' hc hm J u D hGraph hNL hNR
      (hY'.symm ▸ hyL) (hY.symm ▸ hyR) hCL hCR
    intro z hz hz₀
    obtain ⟨t, r, ht, hr, hzU⟩ := J.common_side z hz hz₀
    have hzL : z = sphericalLateralEdge c h J.lower.edge.val (t, r) := by rwa [J.common_edge]
    have hL := (hSide J.lower ht hr).1
    have hR := (hSide J.upper ht hr).1
    rw [← hzL] at hL
    rw [← hzU] at hR
    exact hL.trans (by rw [J.common_edge]; exact hR.symm)

end Thesis
