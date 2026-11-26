module

public import Thesis.Variational.SmoothDomainTraceChart
public import Thesis.Upstream.EuclideanGradientTransform

/-! Smooth volume-preserving boundary patches for the Dirichlet Laplacian. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal RealInnerProductSpace

namespace Thesis

@[expose] def upperCoordinateHalfSpace : OpenDomain 3 :=
  ⟨{ x | 0 < x 2 }, isOpen_lt continuous_const (EuclideanSpace.proj 2).continuous⟩

theorem upperCoordinateHalfSpace_convex : Convex ℝ upperCoordinateHalfSpace.val :=
  convex_halfSpace_gt (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).toLinearMap.isLinear 0

theorem upperCoordinateHalfSpace_invariant {i : Fin 3} (hi : i ≠ 2) (x : Point) (t : ℝ) :
    x+t • EuclideanSpace.single i 1 ∈ upperCoordinateHalfSpace.val ↔
      x ∈ upperCoordinateHalfSpace.val := by
  change 0 < (x+t • EuclideanSpace.single i (1 : ℝ) : Point) 2 ↔ 0 < x 2
  simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,if_neg hi.symm,smul_zero,add_zero]

theorem upperCoordinateHalfSpace_inter_ball_nonempty {R : ℝ} (hR : 0 < R) :
    (ball (0 : Point) R ∩ upperCoordinateHalfSpace.val).Nonempty := by
  refine ⟨(R/2) • EuclideanSpace.single 2 1,?_⟩
  constructor
  · rw [mem_ball_zero_iff,norm_smul,PiLp.norm_single,Real.norm_of_nonneg (half_pos hR).le,norm_one,mul_one]
    exact half_lt_self hR
  · change 0 < ((R/2) • EuclideanSpace.single 2 1 : Point) 2
    simpa only [PiLp.smul_apply,PiLp.single_apply,if_true,smul_eq_mul,mul_one] using half_pos hR

theorem SmoothDomainEpigraphBox.normalEuclideanChart_zero {U : Set Point}
    (B : SmoothDomainEpigraphBox U) : B.normalEuclideanChart 0 = B.chart 0 := by
  have h := B.normalEuclideanChart_apply (0 : Plane × ℝ)
  have hS : EuclideanSpace.single (0 : Fin 1) (0 : ℝ) = 0 := by
    apply PiLp.ext
    intro i
    simp [PiLp.single_apply]
  have hZ : normalCoordinateEquiv.symm ((0 : Plane),EuclideanSpace.single 0 (0 : ℝ)) =
      (0 : Point) := by rw [hS,Prod.mk_zero_zero,map_zero]
  change B.normalEuclideanChart 0 = B.chart ((0,0),0)
  simpa [Prod.fst_zero,Prod.snd_zero,hZ,normalParameter] using h

theorem SmoothDomainEpigraphBox.normalEuclideanChart_mem_domain_iff_of_mem_closedBall
    {U : Set Point} (B : SmoothDomainEpigraphBox U) {x : Point}
    (hx : x ∈ closedBall (0 : Point) (B.radius/2)) :
    B.normalEuclideanChart x ∈ U ↔ x ∈ upperCoordinateHalfSpace.val := by
  have hNorm := mem_closedBall_zero_iff.mp hx
  have hCoord (i : Fin 3) : |x i| < B.radius := by
    simpa only [Real.norm_eq_abs] using ((PiLp.norm_apply_le x i).trans hNorm).trans_lt
      (half_lt_self B.radius_pos)
  have h1 : (normalCoordinateEquiv x).1 0 = x 0 := rfl
  have h2 : (normalCoordinateEquiv x).1 1 = x 1 := rfl
  have h3 : (normalCoordinateEquiv x).2 0 = x 2 := rfl
  have hBox : x ∈ (B.flatRectangle (-B.radius) B.radius).val := by
    change (((normalCoordinateEquiv x).1 0 ∈ Ioo (-B.radius) B.radius) ∧
      ((normalCoordinateEquiv x).1 1 ∈ Ioo (-B.radius) B.radius)) ∧
      ((normalCoordinateEquiv x).2 0 ∈ Ioo (-B.radius) B.radius)
    rw [h1,h2,h3]
    exact ⟨⟨abs_lt.mp (hCoord 0),abs_lt.mp (hCoord 1)⟩,abs_lt.mp (hCoord 2)⟩
  change B.normalEuclideanChart x ∈ U ↔ 0 < x 2
  rw [B.normalEuclideanChart_mem_domain_iff le_rfl le_rfl hBox,h3]

end Thesis
