module

public import Thesis.MeasureGeometry.TransverseMeridian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! Relative openness of the interior of a smooth disk embedded in a sphere. -/

public section

noncomputable section

open Filter Metric Set
open scoped ContDiff RealInnerProductSpace Topology

namespace Thesis.MeasureGeometry

private theorem sphere_eq_of_transverseCoordinates_eq_of_positive_height
    (B : OrthonormalBasis (Fin 3) ℝ Point) {c u v : Point} {R : ℝ}
    (hu : u ∈ sphere c R) (hv : v ∈ sphere c R)
    (huH : 0 < cylinderHeight (B 2) (u-c)) (hvH : 0 < cylinderHeight (B 2) (v-c))
    (hN : axisChartTransverseCoordinates B (u-c) = axisChartTransverseCoordinates B (v-c)) :
    u = v := by
  let N := axisChartTransverseCoordinates B
  let H := cylinderHeight (B 2)
  have hSq (x : Point) (hX : x ∈ sphere c R) : ‖N (x-c)‖^2 + H (x-c)^2 = R^2 := by
    have hNorm : ‖x-c‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hX
    rw [← norm_axisChart_sq B, axisChart_reassemble, hNorm]
  have hU := hSq u hu
  have hV := hSq v hv
  change N (u-c) = N (v-c) at hN
  rw [hN] at hU
  have hP : H (u-c)^2 = H (v-c)^2 := by linarith only [hU,hV]
  have hH : H (u-c) = H (v-c) := (sq_eq_sq₀ huH.le hvH.le).mp hP
  have hEq : u-c = v-c := by
    calc
      _ = axisChart B (N (u-c),H (u-c)) := (axisChart_reassemble B (u-c)).symm
      _ = axisChart B (N (v-c),H (v-c)) := by rw [hN,hH]
      _ = _ := axisChart_reassemble B (v-c)
  exact sub_left_injective hEq

/-- The derivative of an embedded spherical disk is orthogonal to the physical radius. -/
theorem sphericalDisk_fderiv_orthogonal_radius {c : Point} {R : ℝ} {d : Plane → Point}
    (hd : IsSmoothDiskEmbedding d) (hSphere : MapsTo d Disk (sphere c R))
    {y : Plane} (hy : y ∈ ball (0 : Plane) 1) (v : Plane) :
    inner ℝ (d y-c) (fderiv ℝ d y v) = 0 := by
  have hN := isOpen_ball.mem_nhds hy
  have hD : ContDiffAt ℝ 1 d y := ((hd.1.of_le (by decide)) y (ball_subset_closedBall hy)).contDiffAt
    (mem_of_superset hN ball_subset_closedBall)
  have hDC : HasFDerivAt (fun z => d z - c) (fderiv ℝ d y) y :=
    ((hD.differentiableAt one_ne_zero).hasFDerivAt).sub_const c
  have hConst : (fun z => ‖d z - c‖^2) =ᶠ[𝓝 y] fun _ => R^2 := by
    filter_upwards [hN] with z hz
    have hNorm : ‖d z-c‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hSphere (ball_subset_closedBall hz)
    rw [hNorm]
  have hConstD : fderiv ℝ (fun _ : Plane => R^2) y = 0 := fderiv_const_apply _
  have hZero := hDC.norm_sq.fderiv.symm.trans (hConst.fderiv_eq.trans hConstD)
  have hZ := congrArg (fun L : Plane →L[ℝ] ℝ => L v) hZero
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, two_smul, zero_apply] at hZ
  linarith only [hZ]

/-- The interior image of any smooth embedded disk lying on the actual
sphere is open relative to that sphere. -/
theorem isOpen_sphericalDiskInterior {c : Point} {R : ℝ} (hR : 0 < R)
    {d : Plane → Point} (hd : IsSmoothDiskEmbedding d) (hSphere : MapsTo d Disk (sphere c R)) :
    IsOpen (((↑) : sphere c R → Point) ⁻¹' (d '' ball (0 : Plane) 1)) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨y,hy,he⟩ := hx
  have hxN : ‖d y-c‖ = R := by
    simpa only [mem_sphere,dist_eq_norm] using hSphere (ball_subset_closedBall hy)
  let e := R⁻¹ • (d y-c)
  have heN : ‖e‖ = 1 := by
    change ‖R⁻¹ • (d y-c)‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le), hxN, inv_mul_cancel₀ hR.ne']
  obtain ⟨B,hB⟩ := exists_axis_orthonormalBasis heN
  have hRad : d y-c = R • B 2 := by
    rw [hB]
    change d y-c = R • (R⁻¹ • (d y-c))
    rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
  have hTrans : B 2 ∉ LinearMap.range (fderiv ℝ d y).toLinearMap := by
    rintro ⟨v,hv⟩
    have h := sphericalDisk_fderiv_orthogonal_radius hd hSphere hy v
    change fderiv ℝ d y v = B 2 at hv
    rw [hv,hRad,real_inner_smul_left,real_inner_self_eq_norm_sq,B.orthonormal.norm_eq_one 2,one_pow,mul_one] at h
    exact hR.ne' h
  let N := axisChartTransverseCoordinates B
  let H := cylinderHeight (B 2)
  let A := N.comp (fderiv ℝ d y)
  have hA : Function.Injective A := transverse_meridian_normal_derivative_injective B hd hy hTrans
  let L : Plane ≃L[ℝ] Plane := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA)
    (LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective (f := A.toLinearMap) hA))
  let g (z : Plane) := N (d z-c)
  have hBall := isOpen_ball.mem_nhds hy
  have hD : ContDiffAt ℝ 1 d y := ((hd.1.of_le (by decide)) y (ball_subset_closedBall hy)).contDiffAt
    (mem_of_superset hBall ball_subset_closedBall)
  have hg : HasStrictFDerivAt g (L : Plane →L[ℝ] Plane) y :=
    N.hasStrictFDerivAt.comp y ((hD.hasStrictFDerivAt one_ne_zero).sub_const c)
  let h (z : Point) := H (z-c)
  have hh : Continuous h := (continuous_cylinderHeight (B 2)).comp (continuous_id.sub continuous_const)
  have hyH : 0 < h (d y) := by
    change 0 < cylinderHeight (B 2) (d y-c)
    rw [hRad, cylinderHeight, real_inner_smul_right, real_inner_self_eq_norm_sq,
      B.orthonormal.norm_eq_one 2, one_pow, mul_one]
    exact hR
  let U := ball (0 : Plane) 1 ∩ (h ∘ d) ⁻¹' Ioi (0 : ℝ)
  have hU : U ∈ 𝓝 y := inter_mem hBall
    ((hh.continuousAt.comp hD.continuousAt).preimage_mem_nhds (Ioi_mem_nhds hyH))
  have hgU : g '' U ∈ 𝓝 (g y) := hg.map_nhds_eq_of_equiv ▸ Filter.image_mem_map hU
  let t (z : sphere c R) := N (z.val-c)
  have ht : Continuous t := N.continuous.comp (continuous_subtype_val.sub continuous_const)
  have hY : g y = t x := congrArg (fun z : Point => N (z-c)) he
  have hTx : t ⁻¹' (g '' U) ∈ 𝓝 x :=
    ht.continuousAt.preimage_mem_nhds (hY ▸ hgU)
  have hhx : 0 < h x.val := he ▸ hyH
  have hHx : (h ∘ Subtype.val : sphere c R → ℝ) ⁻¹' Ioi (0 : ℝ) ∈ 𝓝 x :=
    (hh.comp continuous_subtype_val).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hhx)
  filter_upwards [hTx,hHx] with z hz hzH
  obtain ⟨w,hw,hwz⟩ := hz
  have hEq : d w = z.val := sphere_eq_of_transverseCoordinates_eq_of_positive_height B
    (hSphere (ball_subset_closedBall hw.1)) z.property hw.2 hzH hwz
  exact ⟨w,hw.1,hEq⟩

end Thesis.MeasureGeometry
