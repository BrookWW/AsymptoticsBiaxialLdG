module

public import Thesis.Interpolation.ProjectedMeshSquareBoundary
public import Thesis.Interpolation.SphericalShellBudgets
import HarmonicMaps.EnergyLemmas

/-! The inner square fillings and their combined estimate on the common mesh. -/

public section

noncomputable section

open HarmonicMaps MeasureTheory Set
open scoped ENNReal Matrix.Norms.Frobenius

namespace Thesis

variable {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}

private theorem sum_meshSquareEdgeDerivativeEnergy_le (G : PenalizedSphereFaces a B h v hv)
    (hSmall : h ≤ 1 / 32) :
    (∑ f, meshSquareEdgeDerivativeEnergy G f) ≤
      2 * ∑ e, ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2 := by
  classical
  let E (e : ↥(cubeBoundaryEdges G.grid.level)) := ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2
  have hE (e : ↥(cubeBoundaryEdges G.grid.level)) : 0 ≤ E e := integral_nonneg fun _ => sq_nonneg _
  have hc (i : Fin 3) : G.grid.center i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(G.grid.offset_mem i).1, (G.grid.offset_mem i).2.le.trans hSmall⟩
  have hSides : (∑ s : ShellSideIndex G.grid.level, E s.edge) ≤ 2 * ∑ e, E e := by
    rw [← Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (ShellSideIndex G.grid.level)))
      (t := (Finset.univ : Finset ↥(cubeBoundaryEdges G.grid.level))) (g := ShellSideIndex.edge)
        (fun _ _ => Finset.mem_univ _) E, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by
      exact_mod_cast shellSide_fiber_card_le_two G.ht_pos (hSmall.trans (by norm_num)) hc G.grid.radius_mem e) (hE e)
  simp only [meshSquareEdgeDerivativeEnergy]
  simpa only [ShellSideIndex.edge, Fintype.sum_prod_type, E] using hSides

/-- All actual inner faces can be filled after the projected boundaries
are null, with one sum bound before the choice of mesh or boundary datum. -/
theorem exists_projectedCellInnerFamily (a : BulkCoefficients)
    (hAngle : External.SquareBoundaryAngularSobolev) (hTransport : External.UnitSquareDiskSobolevPullback)
    (hCircular : External.PeriodicAngularSobolev) (hP : External.QuaternionSpherePoincare 2 (le_refl 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}
      (G : PenalizedSphereFaces a B h v hv) {C : ℝ}, h ≤ 1 / 32 → 0 ≤ C →
      ∀ (D : ∀ f : ShellCellIndex G.grid.level, ProjectedMeshSquareBoundary G f C),
      (∀ f, let q := squareVacuumBoundaryLoop a (D f).boundary
        q.Homotopic (ContinuousMap.const NativeCircle (q nativeCircleLoopBase))) →
      ∃ I : ∀ f : ShellCellIndex G.grid.level, ProjectedCellInnerFace G f,
        (∀ f, ∃ U : Set Plane, IsOpen U ∧ (∀ x : UnitSquareBoundary, unitToPhysicalCellFace h x.val ∈ U) ∧
          ContinuousOn (I f).field U ∧ ∀ i p (x : Domain 1), x 0 ∈ Icc (-1 : ℝ) 1 →
            (I f).field (unitToPhysicalCellFace h (unitCellFaceSlice i x (if p then 1 else -1))) =
              frobeniusCoordinateEquiv (G.grid.projectedEdge (tensorSquareCoordinateEdge f i p) (unitEdgeToPhysical h x))) ∧
        (ENNReal.ofReal (1 / 2 : ℝ) * ∑ f, HarmonicMaps.dirichletEnergy (I f).derivative
          (tensorGridOpenParameterBox 2 h).val) ≤
            ENNReal.ofReal (K * C * h * ∑ e, ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2) := by
  classical
  obtain ⟨K, hK, hFill⟩ := exists_projectedCellInnerFace_with_collar a hAngle hTransport hCircular hP
  refine ⟨K, hK, ?_⟩
  intro B h v hv G C hSmall hC D hNull
  have hEach (f : ShellCellIndex G.grid.level) := hFill G f (D f) (hNull f)
  choose I hCollar hEnergy using hEach
  refine ⟨I, hCollar, ?_⟩
  let E (f : ShellCellIndex G.grid.level) :=
    ∫ x in (tensorGridOpenParameterBox 2 h).val, hsNormSq ((I f).derivative x)
  have hNonneg (f : ShellCellIndex G.grid.level) : 0 ≤ E f := integral_nonneg fun _ => hsNormSq_nonneg _
  have hEq (f : ShellCellIndex G.grid.level) :
      HarmonicMaps.dirichletEnergy (I f).derivative (tensorGridOpenParameterBox 2 h).val = ENNReal.ofReal (E f) :=
    HarmonicMaps.dirichletEnergy_eq_ofReal_integral (I f).memW12.integrable_hsNormSq
  simp only [hEq]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun f _ => hNonneg f), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply ENNReal.ofReal_le_ofReal
  have hSum : (∑ f, E f) ≤ (K * C * h) * ∑ f, meshSquareEdgeDerivativeEnergy G f := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun f _ => hEnergy f
  have hk : 0 ≤ K * C * h := mul_nonneg (mul_nonneg hK.le hC) G.ht_pos.le
  calc
    _ ≤ (1 / 2 : ℝ) * ((K * C * h) * ∑ f, meshSquareEdgeDerivativeEnergy G f) :=
      mul_le_mul_of_nonneg_left hSum (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ((K * C * h) * (2 * ∑ e, ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sum_meshSquareEdgeDerivativeEnergy_le G hSmall) hk)
        (by norm_num)
    _ = _ := by ring

end Thesis
