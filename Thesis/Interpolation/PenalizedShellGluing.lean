module

public import Thesis.Interpolation.SphericalShellLocalGluing

/-! Global weak gluing of the actual finite penalized spherical shell. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal Topology Matrix.Norms.Frobenius

namespace Thesis

variable {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}

/-- The original cell graphs and their common global weak shell graph. -/
structure PenalizedFilledShell (G : PenalizedSphereFaces a B h v hv)
    (I : ∀ f : ShellCellIndex G.grid.level, ProjectedCellInnerFace G f) where
  faceFamily : ShellCellIndex G.grid.level → CompatiblePhysicalCellFaces 5 (max B (Real.sqrt 2 * vacuumRadius a)) h
  face_eq : ∀ f, (faceFamily f).face = penalizedShellCellFace (I f)
  derivative_eq : ∀ f, (faceFamily f).derivative = penalizedShellCellFaceDerivative (I f)
  cell : ∀ f, SphericalCellFilling ((faceFamily f).toUnit G.ht_pos) G.grid.center h f.val
  memW12 : MemW12 (sphericalShellDomain h)
    (sphericalShellPiecewiseField G.grid.center h (fun f => (cell f).field))
    (sphericalShellPiecewiseDerivative G.grid.center h (fun f => (cell f).derivative))
  bound : ∀ᵐ x ∂volume.restrict (sphericalShellDomain h).val,
    ‖sphericalShellPiecewiseField G.grid.center h (fun f => (cell f).field) x‖ ≤ max B (Real.sqrt 2 * vacuumRadius a)

/-- The actual finite cells glue across the common radial faces, leaving
only the finite removable corner lines in the open shell. -/
theorem exists_penalizedFilledShell (G : PenalizedSphereFaces a B h v hv)
    (hB : ∀ θ, ‖v θ‖ ≤ B) (hSmall : h ≤ 1 / 32) {C : ℝ} (S : PenalizedCellSides G.grid C)
    (I : ∀ f : ShellCellIndex G.grid.level, ProjectedCellInnerFace G f) : Nonempty (PenalizedFilledShell G I) := by
  classical
  let c := G.grid.center
  let m := G.grid.level
  have hh := G.ht_pos
  have hh' : h ≤ 1 / 2 := hSmall.trans (by norm_num)
  have hc (i : Fin 3) : c i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(G.grid.offset_mem i).1, (G.grid.offset_mem i).2.le.trans hSmall⟩
  have hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4) := G.grid.radius_mem
  have hCell (f : ShellCellIndex m) := exists_penalizedShellCell hB hSmall S (I f)
  choose A hA hAD hW using hCell
  let W (f : ShellCellIndex m) := Classical.choice (hW f)
  let u (f : ShellCellIndex m) := (W f).field
  let D (f : ShellCellIndex m) := (W f).derivative
  let w := sphericalShellPiecewiseField c h u
  let E := sphericalShellPiecewiseDerivative c h D
  let M := max B (Real.sqrt 2 * vacuumRadius a)
  have hGraph (f : ShellCellIndex m) : MemW12 (sphericalCellOpenDomain c h f.val) (u f) (D f) := (W f).memW12
  obtain ⟨hWLp, hDLp, hWeak, _, _, hInherit⟩ := sphericalShellPiecewise_data hh hh' hc hm u D hGraph
  have hfBound (f : ShellCellIndex m) :
      ∀ᵐ x ∂volume.restrict (sphericalCellOpenDomain c h f.val).val, ‖u f x‖ ≤ M :=
    (W f).values (fun x => ‖x‖ ≤ M) ((A f).toUnit hh).face_bound
  have hBound : ∀ᵐ x ∂volume.restrict (sphericalShellDomain h).val, ‖w x‖ ≤ M :=
    hInherit (fun x => ‖x‖ ≤ M) hfBound
  have hSide (s : ShellSideIndex m) {z : Point} {t r : ℝ} (ht : t ∈ Ioo (0 : ℝ) h) (hr : r ∈ Ioo (1 - h) 1)
      (hz : z = sphericalLateralEdge c h s.edge.val (t, r)) :
      u s.1 z = G.grid.cellSide s.edge (WithLp.toLp 2 ![t, r - (1 - h)]) ∧
        ∃ N : Set Point, IsOpen N ∧ z ∈ N ∧ ContinuousOn (u s.1) (N ∩ sphericalClosedCell c h s.1.val) := by
    rw [hz]
    exact (penalizedShellCell_open_side hSmall (I s.1) (hA s.1) (W s.1) s.2.1 s.2.2 ht hr).2
  have hLocal (y : Point) (hy : y ∈ (sphericalShellDomain h).val) (hyReg : y ∉ sphericalShellCornerLines c h m) :
      ∃ r : ℝ, 0 < r ∧ MemW12 (ballDomain y r) w E := by
    by_cases hInt : ∃ f : ShellCellIndex m, y ∈ (sphericalCellOpenDomain c h f.val).val
    · obtain ⟨f, hf⟩ := hInt
      obtain ⟨r, hr, hSub⟩ := Metric.isOpen_iff.mp (sphericalCellOpenDomain c h f.val).property y hf
      have hw := hWeak f
      exact ⟨r, hr, hw.1.mono hSub, hw.2.1.mono_measure (Measure.restrict_mono_set volume hSub),
        fun i => (hw.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)⟩
    · obtain ⟨J⟩ := exists_shellLocalInterface hh hh' hc hm hy hyReg (not_exists.mp hInt)
      obtain ⟨t, r, ht, hr, hY⟩ := J.common_side y J.point_mem J.normal_zero
      have hY' : y = sphericalLateralEdge c h J.lower.edge.val (t, r) := by rwa [J.common_edge]
      obtain ⟨_, NL, hNL, hyL, hCL⟩ := hSide J.lower ht hr hY'
      obtain ⟨_, NR, hNR, hyR, hCR⟩ := hSide J.upper ht hr hY
      apply memW12_near_shellLocalInterface hh hh' hc hm J u D hGraph hNL hNR hyL hyR hCL hCR
      intro z hz hz₀
      obtain ⟨t, r, ht, hr, hzU⟩ := J.common_side z hz hz₀
      have hzL : z = sphericalLateralEdge c h J.lower.edge.val (t, r) := by rwa [J.common_edge]
      calc
        u J.lower.1 z = G.grid.cellSide J.lower.edge (WithLp.toLp 2 ![t, r - (1 - h)]) :=
          (hSide J.lower ht hr hzL).1
        _ = u J.upper.1 z := by
          rw [J.common_edge]
          exact (hSide J.upper ht hr hzU).1.symm
  have hGlobal : MemW12 (sphericalShellDomain h) w E := sphericalShell_memW12_of_off_cornerLines c h hWLp
    (fun i => (hDLp i).mono_measure Measure.restrict_le_self) hBound hLocal
  exact ⟨⟨A, hA, hAD, W, hGlobal, hBound⟩⟩

end Thesis
