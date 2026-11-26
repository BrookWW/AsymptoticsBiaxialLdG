module

public import Thesis.MeasureGeometry.CylinderRegularSide
public import Thesis.MeasureGeometry.CylinderSliceEnergy
public import Thesis.MeasureGeometry.PlanarSmoothLowerBound

/-! Dilation and translation of the same physical axial cylinders. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal RealInnerProductSpace Topology

namespace Thesis.MeasureGeometry

theorem cylinderHeight_smul (e y : Point) (s : ℝ) :
    cylinderHeight e (s • y) = s * cylinderHeight e y := by
  rw [cylinderHeight, real_inner_smul_right, cylinderHeight]

/-- Translating and isotropically dilating the normalized cylinder
preserves its chosen axis and scales all three parameters. -/
theorem image_smul_openAxisCylinder (x e : Point) {s : ℝ} (hs : 0 < s)
    (r lo hi : ℝ) :
    (fun y : Point => x + s • y) '' openAxisCylinder e r lo hi =
      translatedAxisCylinder x e (s * r) (s * lo) (s * hi) := by
  ext p
  constructor
  · rintro ⟨y, hy, rfl⟩
    change x + s • y - x ∈ openAxisCylinder e (s * r) (s * lo) (s * hi)
    rw [add_sub_cancel_left]
    change cylinderTransverseRadius e (s • y) < s * r ∧ s * lo < cylinderHeight e (s • y) ∧
      cylinderHeight e (s • y) < s * hi
    rw [cylinderTransverseRadius_smul_of_nonneg e y hs.le, cylinderHeight_smul]
    exact ⟨mul_lt_mul_of_pos_left hy.1 hs, mul_lt_mul_of_pos_left hy.2.1 hs,
      mul_lt_mul_of_pos_left hy.2.2 hs⟩
  · intro hp
    let y := s⁻¹ • (p - x)
    have hMul : s • y = p - x := by simp [y, smul_smul, mul_inv_cancel₀ hs.ne']
    have hRad : cylinderTransverseRadius e (p - x) = s * cylinderTransverseRadius e y := by
      rw [← hMul, cylinderTransverseRadius_smul_of_nonneg e y hs.le]
    have hAx : cylinderHeight e (p - x) = s * cylinderHeight e y := by
      rw [← hMul, cylinderHeight_smul]
    have hp' : cylinderTransverseRadius e (p - x) < s * r ∧
        s * lo < cylinderHeight e (p - x) ∧ cylinderHeight e (p - x) < s * hi := hp
    rw [hRad, hAx] at hp'
    refine ⟨y, ?_, ?_⟩
    · exact ⟨(mul_lt_mul_iff_right₀ hs).mp hp'.1, (mul_lt_mul_iff_right₀ hs).mp hp'.2.1,
        (mul_lt_mul_iff_right₀ hs).mp hp'.2.2⟩
    · change x + s • y = p
      rw [hMul, add_comm x, sub_add_cancel]

/-- The physical parameter recovery used with independently moving end heights. -/
theorem translatedAxisCylinder_eq_dilate_div (x e : Point) {s : ℝ} (hs : 0 < s)
    (r lo hi : ℝ) :
    translatedAxisCylinder x e r lo hi =
      (fun y : Point => x + s • y) '' openAxisCylinder e (r / s) (lo / s) (hi / s) := by
  have h (a : ℝ) : s * (a / s) = a := (mul_comm _ _).trans (div_mul_cancel₀ a hs.ne')
  rw [image_smul_openAxisCylinder x e hs, h r, h lo, h hi]

theorem axisChart_smul (B : OrthonormalBasis (Fin 3) ℝ Point) (s : ℝ) (y : Plane) (z : ℝ) :
    axisChart B (s • y, s * z) = s • axisChart B (y, z) := by
  unfold axisChart
  rw [show WithLp.toLp 2 (s • y, s * z) = s • WithLp.toLp 2 (y,z) from rfl,
    map_smul, map_smul]

/-- Choose a fixed physical radius whose entire lateral cylinder, including
its two rims, lies in one compact regular subset. -/
theorem eventually_exists_fixed_regular_lateral_radius
    {Ω Spt : Set Point} (hΩ : IsOpen Ω) {μ : Measure Point} [IsFiniteMeasure μ] [μ.OuterRegular]
    (hLoc : LocallyFiniteIn (Ω \ μ.support) Spt) {η : ℝ} (hη : 0 < η)
    (hD : ∀ x ∈ Ω ∩ μ.support, ∃ θ ≥ η / 2, Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ))
    {x : Point} (hx : x ∈ Ω) (B : OrthonormalBasis (Fin 3) ℝ Point)
    {b : ℝ} (hFlat : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun s => SupportingAnalysis.blownUpMeasure (d := 1) x s μ)
      (ENNReal.ofReal b • HausdorffOne.restrict ((Submodule.span ℝ {B 2} : Submodule ℝ Point) : Set Point)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ∃ ρ ∈ Ioo (δ * s) (2 * δ * s), ∃ K : Set Point,
      IsCompact K ∧ K ⊆ (Ω \ μ.support) \ Spt ∧
        ∀ z ∈ Icc (-s) s, ∀ w : NativeCircle, x + axisChart B (ρ • w.val, z) ∈ K := by
  have he := B.orthonormal.norm_eq_one 2
  filter_upwards [eventually_exists_compact_regular_lateral_band hΩ hLoc hη hD hx he hFlat hδ,
    self_mem_nhdsWithin] with s hs hPos
  obtain ⟨r₀, r₁, hr₀, hr₀₁, hr₁, hKc, hKR⟩ := hs
  let r := (r₀ + r₁) / 2
  have hrL : r₀ < r := by dsimp only [r]; linarith only [hr₀₁]
  have hrH : r < r₁ := by dsimp only [r]; linarith only [hr₀₁]
  have hr : 0 < r := hδ.trans (hr₀.trans hrL)
  let ρ := s * r
  refine ⟨ρ, ⟨?_, ?_⟩, _, hKc, hKR, ?_⟩
  · simpa only [ρ, mul_comm s] using mul_lt_mul_of_pos_left (hr₀.trans hrL) hPos
  · simpa only [ρ, mul_comm s] using mul_lt_mul_of_pos_left (hrH.trans hr₁) hPos
  intro z hz w
  let y := axisChart B (r • w.val, z / s)
  have hR : cylinderTransverseRadius (B 2) y = r := by
    change cylinderTransverseRadius (B 2) (axisChart B (r • w.val, z / s)) = r
    rw [cylinderTransverseRadius_axisChart, planar_norm_on_circle hr.le]
  have hH : cylinderHeight (B 2) y = z / s := cylinderHeight_axisChart B _ _
  have hY : y ∈ closedAxisAnnularCylinder (B 2) r₀ r₁ (-1) 1 := by
    change (cylinderTransverseRadius (B 2) y ≤ r₁ ∧ -1 ≤ cylinderHeight (B 2) y ∧
      cylinderHeight (B 2) y ≤ 1) ∧ r₀ ≤ cylinderTransverseRadius (B 2) y
    rw [hR, hH]
    refine ⟨⟨hrH.le, (le_div_iff₀ hPos).mpr ?_, (div_le_one hPos).mpr hz.2⟩, hrL.le⟩
    simpa only [neg_mul, one_mul] using hz.1
  refine ⟨y, hY, ?_⟩
  change x + s • axisChart B (r • w.val, z / s) = _
  rw [← axisChart_smul, smul_smul, mul_comm s (z / s), div_mul_cancel₀ z hPos.ne']

end Thesis.MeasureGeometry
