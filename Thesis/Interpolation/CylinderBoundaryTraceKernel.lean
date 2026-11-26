module

public import Thesis.Interpolation.CylinderRadialZeroExtension
public import Thesis.Interpolation.ConvexZeroTrace
import Thesis.Upstream.MinimizingSobolev
import Thesis.Foundation.WeakGradient

/-! The intrinsic zero-trace characterization on the actual translated cylinder. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

private theorem cylinderRecoveryCoordinates_convexCombination
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c x y : Point) {a b : ℝ} (hab : a + b = 1) :
    cylinderRecoveryCoordinates B c (a • x + b • y) =
      a • cylinderRecoveryCoordinates B c x + b • cylinderRecoveryCoordinates B c y := by
  have h : a • x + b • y - c = a • (x - c) + b • (y - c) := by
    rw [smul_sub, smul_sub]
    calc
      _ = a • x + b • y - (a + b) • c := by rw [hab, one_smul]
      _ = _ := by rw [add_smul]; abel
  unfold cylinderRecoveryCoordinates
  rw [h]
  simp [recoveryReferenceSplit, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply]

private theorem convex_translatedAxisCylinder
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R lo hi : ℝ) :
    Convex ℝ (translatedAxisCylinder c (B 2) R lo hi) := by
  rw [translatedAxisCylinder_eq_recoveryCoordinates_preimage]
  have h : Convex ℝ (ball (0 : Plane) R ×ˢ Ioo lo hi) := (convex_ball (0 : Plane) R).prod (convex_Ioo lo hi)
  intro x hx y hy a b ha hb hab
  change cylinderRecoveryCoordinates B c (a • x + b • y) ∈ ball (0 : Plane) R ×ˢ Ioo lo hi
  rw [cylinderRecoveryCoordinates_convexCombination B c x y hab]
  exact h hx hy ha hb hab

end Thesis.MeasureGeometry

namespace Thesis

open Thesis.MeasureGeometry

/-- Matching actual cylinder traces give an intrinsic zero-trace difference.
The proof uses the original weak graph, finite a.e. height cover, and exact
zero extension before contracting and mollifying inside the cylinder. -/
theorem cylinderBoundaryTraceKernel : External.CylinderBoundaryTraceKernel := by
  intro B c R lo hi hR hI u v Du Dv hu hv P Q hP hQ hLo hHi n l h hSub hCover hSides
  let U := translatedAxisCylinderDomain B c R lo hi
  let w := u - v
  let D := Du - Dv
  have hwH : MemH1 U.val w D := hu.sub hv
  have hw : MemW12 U (frobeniusField w) (frobeniusGradient D) := (memH1_iff_memW12 U w D).mp hwH
  have hFrob : frobeniusField w = frobeniusField u - frobeniusField v := by
    funext x
    exact frobeniusCoordinateEquiv.toLinearEquiv.map_sub (u x) (v x)
  have hPQ : RepresentsCylinderHeightL2Trace B c (frobeniusField w) (P - Q) := by
    rw [hFrob]
    exact hP.sub hQ
  have hLow : (P - Q) ⟨lo, le_rfl, hI.le⟩ = 0 := sub_eq_zero.mpr hLo
  have hHigh : (P - Q) ⟨hi, hI.le, le_rfl⟩ = 0 := sub_eq_zero.mpr hHi
  choose L S hL hS hLS using hSides
  let T (i : Fin n) := L i - S i
  have hT (i : Fin n) : RepresentsCylinderSideL2Trace B c (frobeniusField w) (T i) := by
    rw [hFrob]
    exact (hL i).sub (hS i)
  have hWallZero (i : Fin n) : T i ⟨R, half_le_self hR.le, le_rfl⟩ = 0 := sub_eq_zero.mpr (hLS i)
  have hGlobal : MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain 3)
      (U.val.indicator (frobeniusField w)) (U.val.indicator (frobeniusGradient D)) :=
    memW12_cylinder_zeroExtend B c hR hI (frobeniusField w) (frobeniusGradient D) hw (P - Q)
      hPQ hLow hHigh l h hSub hCover T hT hWallZero
  let z := c + axisChart B (0, (lo + hi) / 2)
  have hz : z ∈ U.val := by
    apply (mem_translatedAxisCylinder_iff_recoveryCoordinates B c R lo hi z).2
    rw [show cylinderRecoveryCoordinates B c z = (0, (lo + hi) / 2) from cylinderRecoveryCoordinates_axisChart B c _]
    exact ⟨mem_ball_self hR, ⟨by linarith only [hI], by linarith only [hI]⟩⟩
  have hCompact : IsCompact (closure U.val) := by
    have hClosed : IsCompact (translatedClosedAxisCylinder c (B 2) R lo hi) :=
      isCompact_translatedClosedAxisCylinder (B.orthonormal.norm_eq_one 2) R lo hi
    exact hClosed.of_isClosed_subset isClosed_closure
      (closure_minimal (translatedAxisCylinder_subset_closed _ _ _ _ _) hClosed.isClosed)
  apply (hasZeroTrace_iff_hasZeroBoundaryValues U w D).mpr
  exact hasZeroBoundaryValues_of_convex_zeroExtension U (convex_translatedAxisCylinder B c R lo hi)
    hCompact hz hw hGlobal

end Thesis

end
