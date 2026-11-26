module

public import Thesis.MeasureGeometry.RelativeMeridians
public import Thesis.MeasureGeometry.MeridianCoordinates

/-! The radius of a round meridian in the local affine line complement. -/

@[expose] public section

noncomputable section

open Metric Set StratificationTheory
open scoped ContDiff

namespace Thesis.MeasureGeometry

theorem orthogonalMeridian_mem_ball (B : OrthonormalBasis (Fin 3) ℝ Point)
    (x : Point) {r R : ℝ} (hr : 0 ≤ r) (hR : r < R) (z : NativeCircle) :
    x + r • axisChartPlane B z.val ∈ ball x R := by
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr,
    norm_axisChartPlane, mem_sphere_zero_iff_norm.mp z.property, mul_one]
  exact hR

theorem orthogonalMeridian_transverse_nonzero (B : OrthonormalBasis (Fin 3) ℝ Point)
    (x : Point) {r : ℝ} (hr : 0 < r) (z : NativeCircle) :
    axisChartTransverseCoordinates B (x + r • axisChartPlane B z.val - x) ≠ 0 := by
  rw [add_sub_cancel_left, map_smul, axisChartTransverseCoordinates_axisChartPlane]
  exact fun h => by
    have hz := mem_sphere_zero_iff_norm.mp z.property
    rw [(smul_eq_zero.mp h).resolve_left hr.ne', norm_zero] at hz
    exact zero_ne_one hz

/-- Two admissible round meridians of one local line germ give the same
free homotopy class of the actual limit even in the presence of isolated
point singularities between the two radii. -/
theorem orthogonal_meridians_homotopic_of_local_axis
    (hAvoid : External.RelativeAnnulusPointAvoidance) (a : BulkCoefficients)
    {Ω S Spt : Set Point} (hΩ : IsOpen Ω) (hS : IsClosed S)
    (hLoc : LocallyFiniteIn (Ω \ S) Spt) {Q : Point → S0}
    (hQ : ContinuousOn Q ((Ω \ S) \ Spt)) (hVac : MapsTo Q ((Ω \ S) \ Spt) (vacuum a))
    (B : OrthonormalBasis (Fin 3) ℝ Point) (x : Point)
    {R r₀ r₁ : ℝ} (hBΩ : ball x R ⊆ Ω)
    (hGerm : ∀ y ∈ ball x R, y ∈ S ↔ axisChartTransverseCoordinates B (y-x) = 0)
    (hr₀ : r₀ ∈ Ioo 0 R) (hr₁ : r₁ ∈ Ioo 0 R)
    (hSafe : ∀ z : NativeCircle, x + r₀ • axisChartPlane B z.val ∉ Spt ∧
      x + r₁ • axisChartPlane B z.val ∉ Spt)
    (b₀ b₁ : C(NativeCircle, vacuum a))
    (hb₀ : ∀ z, (b₀ z).val = Q (x + r₀ • axisChartPlane B z.val))
    (hb₁ : ∀ z, (b₁ z).val = Q (x + r₁ • axisChartPlane B z.val)) :
    b₀.Homotopic b₁ := by
  let r (t : ℝ) := (1-t)*r₀ + t*r₁
  have hRadius (t : unitInterval) : r t.val ∈ Ioo 0 R := by
    have ht₀ : 0 ≤ t.val := t.property.1
    have ht₁ : 0 ≤ 1-t.val := sub_nonneg.mpr t.property.2
    exact convex_Ioo (0 : ℝ) R hr₀ hr₁ ht₁ ht₀ (by ring)
  let E := axisChartPlane B
  let F (p : unitInterval × NativeCircle) := x + r p.1.val • E p.2.val
  have hRcts : Continuous r := (continuous_const.sub continuous_id).mul continuous_const |>.add
    (continuous_id.mul continuous_const)
  have hFcts : Continuous F := continuous_const.add
    ((hRcts.comp (continuous_subtype_val.comp continuous_fst)).smul
      (E.continuous.comp (continuous_subtype_val.comp continuous_snd)))
  let H : C(unitInterval × NativeCircle, Point) := ⟨F,hFcts⟩
  have hFW (p : unitInterval × NativeCircle) : H p ∈ Ω \ S := by
    have h := hRadius p.1
    have hBall := orthogonalMeridian_mem_ball B x h.1.le h.2 p.2
    exact ⟨hBΩ hBall, fun hS => orthogonalMeridian_transverse_nonzero B x h.1 p.2
      ((hGerm _ hBall).mp hS)⟩
  have hSmooth : SmoothNativeAnnulus H := by
    let G (p : ℝ × ℝ) := x + r p.1 • E (circleNativeParam p.2).val
    have hR' : ContDiff ℝ ∞ r := by dsimp only [r]; fun_prop
    have hG : ContDiff ℝ ∞ G := contDiff_const.add
      ((hR'.comp contDiff_fst).smul (E.contDiff.comp
        (contDiff_circleNativeParam_val_infty.comp contDiff_snd)))
    exact ⟨G,hG.contDiffOn,fun _ _ => rfl⟩
  have h₀ (z : NativeCircle) : H (0,z) = x + r₀ • E z.val := by simp [H,F,r]
  have h₁ (z : NativeCircle) : H (1,z) = x + r₁ • E z.val := by simp [H,F,r]
  exact nativeVacuum_homotopic_of_regular_annulus hAvoid a (hΩ.sdiff hS) hLoc hQ hVac H hSmooth
    hFW (fun z => by rw [h₀,h₁]; exact hSafe z) b₀ b₁
    (fun z => (hb₀ z).trans (congrArg Q (h₀ z)).symm)
    (fun z => (hb₁ z).trans (congrArg Q (h₁ z)).symm)

end Thesis.MeasureGeometry
