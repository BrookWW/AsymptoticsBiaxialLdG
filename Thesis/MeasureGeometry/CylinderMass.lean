module

public import Thesis.MeasureGeometry.ApproximateTangent
import Mathlib.Topology.UrysohnsLemma

/-! Cylinder masses at a weighted line tangent. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace Thesis.MeasureGeometry

/-- The axial coordinate relative to a unit tangent direction. -/
def cylinderHeight (e x : Point) : ℝ := inner ℝ e x

/-- Distance to the axis of the cylinder with unit tangent direction. -/
def cylinderTransverseRadius (e x : Point) : ℝ := ‖x - cylinderHeight e x • e‖

def openAxisCylinder (e : Point) (r lo hi : ℝ) : Set Point :=
  {x | cylinderTransverseRadius e x < r ∧ lo < cylinderHeight e x ∧ cylinderHeight e x < hi}

def closedAxisCylinder (e : Point) (r lo hi : ℝ) : Set Point :=
  {x | cylinderTransverseRadius e x ≤ r ∧ lo ≤ cylinderHeight e x ∧ cylinderHeight e x ≤ hi}

theorem continuous_cylinderHeight (e : Point) : Continuous (cylinderHeight e) :=
  continuous_const.inner continuous_id

theorem continuous_cylinderTransverseRadius (e : Point) : Continuous (cylinderTransverseRadius e) :=
  (continuous_id.sub ((continuous_cylinderHeight e).smul continuous_const)).norm

theorem isOpen_openAxisCylinder (e : Point) (r lo hi : ℝ) : IsOpen (openAxisCylinder e r lo hi) :=
  (isOpen_lt (continuous_cylinderTransverseRadius e) continuous_const).inter
    ((isOpen_lt continuous_const (continuous_cylinderHeight e)).inter
      (isOpen_lt (continuous_cylinderHeight e) continuous_const))

theorem isClosed_closedAxisCylinder (e : Point) (r lo hi : ℝ) : IsClosed (closedAxisCylinder e r lo hi) :=
  (isClosed_le (continuous_cylinderTransverseRadius e) continuous_const).inter
    ((isClosed_le continuous_const (continuous_cylinderHeight e)).inter
      (isClosed_le (continuous_cylinderHeight e) continuous_const))

theorem closedAxisCylinder_subset_closedBall {e : Point} (he : ‖e‖ = 1) (r lo hi : ℝ) :
    closedAxisCylinder e r lo hi ⊆ closedBall 0 (r + |lo| + |hi|) := by
  intro x hx
  change cylinderTransverseRadius e x ≤ r ∧ lo ≤ cylinderHeight e x ∧ cylinderHeight e x ≤ hi at hx
  have hAbs : |cylinderHeight e x| ≤ |lo| + |hi| := by
    apply abs_le.mpr
    constructor <;> linarith only [hx.2.1, hx.2.2, abs_nonneg lo, abs_nonneg hi,
      abs_neg lo ▸ le_abs_self (-lo), le_abs_self hi]
  have hVec : (x - cylinderHeight e x • e) + cylinderHeight e x • e = x := sub_add_cancel _ _
  have hNorm := norm_add_le (x - cylinderHeight e x • e) (cylinderHeight e x • e)
  rw [hVec, norm_smul, Real.norm_eq_abs, he, mul_one] at hNorm
  rw [mem_closedBall, dist_zero_right]
  change ‖x‖ ≤ r + |lo| + |hi|
  have hxR : ‖x - cylinderHeight e x • e‖ ≤ r := hx.1
  exact hNorm.trans (by linarith only [hxR, hAbs])

theorem isCompact_closedAxisCylinder {e : Point} (he : ‖e‖ = 1) (r lo hi : ℝ) :
    IsCompact (closedAxisCylinder e r lo hi) :=
  (isCompact_closedBall _ _).of_isClosed_subset (isClosed_closedAxisCylinder e r lo hi)
    (closedAxisCylinder_subset_closedBall he r lo hi)

theorem openAxisCylinder_subset_closedAxisCylinder (e : Point) (r lo hi : ℝ) :
    openAxisCylinder e r lo hi ⊆ closedAxisCylinder e r lo hi :=
  fun _ h => ⟨h.1.le, h.2.1.le, h.2.2.le⟩

theorem closedAxisCylinder_subset_openAxisCylinder (e : Point)
    {r₀ lo₀ hi₀ r₁ lo₁ hi₁ : ℝ} (hr : r₀ < r₁) (hl : lo₁ < lo₀) (hh : hi₀ < hi₁) :
    closedAxisCylinder e r₀ lo₀ hi₀ ⊆ openAxisCylinder e r₁ lo₁ hi₁ :=
  fun _ h => ⟨h.1.trans_lt hr, hl.trans_le h.2.1, h.2.2.trans_lt hh⟩

theorem cylinderHeight_smul_unit {e : Point} (he : ‖e‖ = 1) (t : ℝ) :
    cylinderHeight e (t • e) = t := by
  rw [cylinderHeight, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
  ring

theorem cylinderTransverseRadius_smul_unit {e : Point} (he : ‖e‖ = 1) (t : ℝ) :
    cylinderTransverseRadius e (t • e) = 0 := by
  rw [cylinderTransverseRadius, cylinderHeight_smul_unit he, sub_self, norm_zero]

/-- Each open cylinder cuts the axis in an interval of exactly its height. -/
theorem hausdorffOne_axis_openCylinder {e : Point} (he : ‖e‖ = 1) {r : ℝ} (hr : 0 < r)
    (lo hi : ℝ) :
    (HausdorffOne.restrict ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point))
      (openAxisCylinder e r lo hi) = ENNReal.ofReal (hi - lo) := by
  have hImage : openAxisCylinder e r lo hi ∩ ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point) =
      (fun t : ℝ => t • e) '' Ioo lo hi := by
    ext x
    constructor
    · rintro ⟨hx, heSpan⟩
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp heSpan
      exact ⟨t, by simpa only [openAxisCylinder, mem_setOf_eq, mem_Ioo, cylinderHeight_smul_unit he] using hx.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨?_, Submodule.smul_mem _ _ (Submodule.subset_span (mem_singleton e))⟩
      change cylinderTransverseRadius e (t • e) < r ∧ lo < cylinderHeight e (t • e) ∧ cylinderHeight e (t • e) < hi
      rw [cylinderTransverseRadius_smul_unit he, cylinderHeight_smul_unit he]
      exact ⟨hr, ht.1, ht.2⟩
  rw [Measure.restrict_apply (isOpen_openAxisCylinder e r lo hi).measurableSet, hImage,
    hausdorffMeasure_smul_right_image, hausdorffMeasure_real, Real.volume_Ioo,
    show ‖e‖₊ = 1 from NNReal.eq he, one_smul]

/-- Including the two end points leaves the same exact axial mass. -/
theorem hausdorffOne_axis_closedCylinder {e : Point} (he : ‖e‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (lo hi : ℝ) :
    (HausdorffOne.restrict ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point))
      (closedAxisCylinder e r lo hi) = ENNReal.ofReal (hi - lo) := by
  have hImage : closedAxisCylinder e r lo hi ∩ ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point) =
      (fun t : ℝ => t • e) '' Icc lo hi := by
    ext x
    constructor
    · rintro ⟨hx, heSpan⟩
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp heSpan
      exact ⟨t, by simpa only [closedAxisCylinder, mem_setOf_eq, mem_Icc, cylinderHeight_smul_unit he] using hx.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨?_, Submodule.smul_mem _ _ (Submodule.subset_span (mem_singleton e))⟩
      change cylinderTransverseRadius e (t • e) ≤ r ∧ lo ≤ cylinderHeight e (t • e) ∧ cylinderHeight e (t • e) ≤ hi
      rw [cylinderTransverseRadius_smul_unit he, cylinderHeight_smul_unit he]
      exact ⟨hr, ht.1, ht.2⟩
  rw [Measure.restrict_apply (isClosed_closedAxisCylinder e r lo hi).measurableSet, hImage,
    hausdorffMeasure_smul_right_image, hausdorffMeasure_real, Real.volume_Icc,
    show ‖e‖₊ = 1 from NNReal.eq he, one_smul]

end Thesis.MeasureGeometry
