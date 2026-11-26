module

public import Thesis.Variational.SmoothDomainTraceChart
public import Thesis.Variational.GlobalLimit
import Mathlib.Geometry.Euclidean.Volume.Measure
import StratificationTheory.Foundation.CylinderCoordinateMeasure

/-! The surface measure of a smooth wall and its horizontal coordinate measure. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ENNReal NNReal Topology

namespace Thesis

private theorem euclideanHausdorffMeasure_image_le_of_lipschitz
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y]
    {f : X → Y} {K : ℝ≥0} (h : LipschitzWith K f) (s : Set X) :
    Measure.euclideanHausdorffMeasure 2 (f '' s) ≤ (K : ℝ≥0∞)^2 * Measure.euclideanHausdorffMeasure 2 s := by
  have hL := h.hausdorffMeasure_image_le (by norm_num : 0 ≤ (2 : ℝ)) s
  rw [ENNReal.rpow_two] at hL
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [mul_left_comm]
  exact mul_le_mul_right hL _

private theorem euclideanHausdorffMeasure_preimage_le_of_antilipschitz
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y]
    {f : X → Y} {K : ℝ≥0} (h : AntilipschitzWith K f) (s : Set Y) :
    Measure.euclideanHausdorffMeasure 2 (f ⁻¹' s) ≤ (K : ℝ≥0∞)^2 * Measure.euclideanHausdorffMeasure 2 s := by
  have hL := h.hausdorffMeasure_preimage_le (by norm_num : 0 ≤ (2 : ℝ)) s
  rw [ENNReal.rpow_two] at hL
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [mul_left_comm]
  exact mul_le_mul_right hL _

namespace SmoothDomainEpigraphBox

variable {Ω : Set Point} (B : SmoothDomainEpigraphBox Ω)

abbrev wallBase := B.planeDomain.val

abbrev wallBaseMeasure : Measure B.wallBase := Measure.euclideanHausdorffMeasure 2

theorem wallBaseMeasure_coe :
    MeasurePreserving (Subtype.val : B.wallBase → Plane) B.wallBaseMeasure (volume.restrict B.wallBase) := by
  refine ⟨measurable_subtype_coe,?_⟩
  rw [isometry_subtype_coe.map_euclideanHausdorffMeasure, Subtype.range_coe, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]

theorem wallCoordinates_mem {y : Plane} (hy : y ∈ B.wallBase) :
    (((y 0,y 1),0) : EpigraphCoordinates) ∈ closedBall 0 B.radius :=
  epigraphCoordinates_mem_closedBall_iff.2
    ⟨⟨⟨hy.1.1.le,hy.1.2.le⟩,⟨hy.2.1.le,hy.2.2.le⟩⟩,
      ⟨neg_nonpos.mpr B.radius_pos.le,B.radius_pos.le⟩⟩

/-- The actual parametrization of this chart's part of the frontier. -/
@[expose] def wallMap (y : B.wallBase) : frontier Ω :=
  ⟨B.normalParameter (y.val,0), (B.frontier_iff _ (B.wallCoordinates_mem y.property)).2 rfl⟩

theorem wallMap_lipschitz : LipschitzWith B.lip B.wallMap := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have hPair : dist (((y.val 0,y.val 1),0) : EpigraphCoordinates) ((z.val 0,z.val 1),0) ≤ dist y z := by
    rw [Prod.dist_eq, Prod.dist_eq, dist_self, max_eq_left (le_max_of_le_left dist_nonneg)]
    apply max_le
    · change dist (y.val 0) (z.val 0) ≤ dist (y.val : Plane) z.val
      rw [dist_eq_norm, dist_eq_norm]
      exact PiLp.norm_apply_le (y.val-z.val) 0
    · change dist (y.val 1) (z.val 1) ≤ dist (y.val : Plane) z.val
      rw [dist_eq_norm, dist_eq_norm]
      exact PiLp.norm_apply_le (y.val-z.val) 1
  exact (B.chart_lipschitz.dist_le_mul _ (B.wallCoordinates_mem y.property)
    _ (B.wallCoordinates_mem z.property)).trans (mul_le_mul_of_nonneg_left hPair B.lip.coe_nonneg)

theorem wallMap_antilipschitz : AntilipschitzWith (2 * B.inverseLip) B.wallMap := by
  apply antilipschitzWith_iff_le_mul_dist.mpr
  intro y z
  let a : EpigraphCoordinates := ((y.val 0,y.val 1),0)
  let b : EpigraphCoordinates := ((z.val 0,z.val 1),0)
  have hI := B.chart_inverse_lipschitz.dist_le_mul (B.chart a) ⟨a,B.wallCoordinates_mem y.property,rfl⟩
    (B.chart b) ⟨b,B.wallCoordinates_mem z.property,rfl⟩
  rw [B.chart.symm_apply_apply, B.chart.symm_apply_apply] at hI
  have hPlane : dist y z ≤ (2 : ℝ) * dist a b := by
    let T := dist a b
    have hT : 0 ≤ T := dist_nonneg
    have hPoint (j : Fin 2) : ‖(y.val-z.val) j‖ ≤ T := by
      fin_cases j
      · change dist (y.val 0) (z.val 0) ≤ dist a b
        exact (le_max_left _ _).trans (le_max_left _ _)
      · change dist (y.val 1) (z.val 1) ≤ dist a b
        exact (le_max_right _ _).trans (le_max_left _ _)
    change dist (y.val : Plane) z.val ≤ 2 * T
    rw [dist_eq_norm]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have h0 := pow_le_pow_left₀ (norm_nonneg _) (hPoint 0) 2
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hPoint 1) 2
    simp only [Real.norm_eq_abs, sq_abs] at h0 h1
    nlinarith only [h0,h1,sq_nonneg T]
  have h := hPlane.trans (mul_le_mul_of_nonneg_left hI (by norm_num))
  push_cast
  exact h.trans_eq (by change _ = (2 * (B.inverseLip : ℝ)) * dist (B.chart a) (B.chart b); ring)

theorem range_wallMap :
    range B.wallMap = (Subtype.val : frontier Ω → Point) ⁻¹' (B.physicalRectangle (-B.radius) B.radius).val := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    let p : Plane × ℝ := (y.val,0)
    let a := normalCoordinateEquiv.symm (p.1, EuclideanSpace.single (0 : Fin 1) p.2)
    have hA : a ∈ (B.flatRectangle (-B.radius) B.radius).val := by
      change (normalCoordinateEquiv a).1 ∈ B.wallBase ∧ (normalCoordinateEquiv a).2 0 ∈ Ioo (-B.radius) B.radius
      simp only [a, ContinuousLinearEquiv.apply_symm_apply, p, PiLp.single_apply, if_true]
      exact ⟨y.property,neg_lt_zero.mpr B.radius_pos,B.radius_pos⟩
    exact ⟨a,hA,B.normalEuclideanChart_apply p⟩
  · intro hx
    obtain ⟨a,ha,haeq⟩ := hx
    let p : Plane × ℝ := ((normalCoordinateEquiv a).1,(normalCoordinateEquiv a).2 0)
    have hE : normalCoordinateEquiv.symm (p.1,EuclideanSpace.single 0 p.2) = a :=
      cylinder_coordinates_inverse_left 2 a
    have hChart : B.normalParameter p = (x : Point) := by
      rw [← B.normalEuclideanChart_apply p, hE, haeq]
    have ha' : (((p.1 0,p.1 1),p.2) : EpigraphCoordinates) ∈ closedBall 0 B.radius :=
      epigraphCoordinates_mem_closedBall_iff.2
        ⟨⟨⟨ha.1.1.1.le,ha.1.1.2.le⟩,⟨ha.1.2.1.le,ha.1.2.2.le⟩⟩, ⟨ha.2.1.le,ha.2.2.le⟩⟩
    have hFront : B.chart ((p.1 0,p.1 1),p.2) ∈ frontier Ω := by
      change B.normalParameter p ∈ frontier Ω
      rw [hChart]
      exact x.property
    have ht : p.2 = 0 := (B.frontier_iff _ ha').1 hFront
    refine ⟨⟨p.1,ha.1⟩, Subtype.ext ?_⟩
    change B.normalParameter (p.1,0) = (x : Point)
    rw [← ht]
    exact hChart

theorem isOpen_range_wallMap : IsOpen (range B.wallMap) := by
  rw [B.range_wallMap]
  exact (B.physicalRectangle (-B.radius) B.radius).property.preimage continuous_subtype_val

theorem measurableEmbedding_wallMap : MeasurableEmbedding B.wallMap :=
  (B.wallMap_antilipschitz.isEmbedding B.wallMap_lipschitz.continuous).measurableEmbedding
    B.isOpen_range_wallMap.measurableSet

theorem surfaceMeasure_le_map_wallBase :
    (frontierSurfaceMeasure Ω).restrict (range B.wallMap) ≤
      (B.lip : ℝ≥0∞)^2 • Measure.map B.wallMap B.wallBaseMeasure := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.map_apply B.wallMap_lipschitz.continuous.measurable hs,
    ← image_preimage_eq_inter_range]
  exact euclideanHausdorffMeasure_image_le_of_lipschitz B.wallMap_lipschitz _

theorem map_wallBase_le_surfaceMeasure :
    Measure.map B.wallMap B.wallBaseMeasure ≤ ((2 * B.inverseLip : ℝ≥0) : ℝ≥0∞)^2 •
      (frontierSurfaceMeasure Ω).restrict (range B.wallMap) := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.smul_apply, Measure.restrict_apply hs, Measure.map_apply B.wallMap_lipschitz.continuous.measurable hs,
    ← preimage_inter_range]
  exact euclideanHausdorffMeasure_preimage_le_of_antilipschitz B.wallMap_antilipschitz _

theorem mem_range_wallMap_center {x : frontier Ω} (hB : B.chart (0 : EpigraphCoordinates) = x) :
    x ∈ range B.wallMap := by
  rw [B.range_wallMap]
  exact B.normalChart_mem_zero hB B.radius_pos

end SmoothDomainEpigraphBox

end Thesis
