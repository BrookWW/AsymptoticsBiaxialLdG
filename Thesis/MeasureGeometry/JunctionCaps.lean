module

public import Thesis.MeasureGeometry.MeridianCoordinates
public import Thesis.MeasureGeometry.JunctionWord
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Smooth transverse caps on the actual small sphere of a junction. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal RealInnerProductSpace Topology

namespace Thesis.MeasureGeometry

/-- A spherical cap parametrized by its normal-plane projection. -/
def capDiskEmbedding (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (R τ : ℝ) (y : Plane) : Point :=
  c + R • (axisChartPlane B (τ • y) + Real.sqrt (1 - τ ^ 2 * ‖y‖ ^ 2) • B 2)

theorem capDiskEmbedding_zero (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R τ : ℝ) :
    capDiskEmbedding B c R τ 0 = c + R • B 2 := by
  simp [capDiskEmbedding]

theorem capDiskEmbedding_proj (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (R τ : ℝ) (y : Plane) :
    axisChartTransverseCoordinates B (capDiskEmbedding B c R τ y - c) = (R * τ) • y := by
  rw [capDiskEmbedding, add_sub_cancel_left, map_smul, map_add,
    axisChartTransverseCoordinates_axisChartPlane, map_smul,
    axisChartTransverseCoordinates_axis_vector, smul_zero, add_zero, smul_smul]

private theorem capDiskEmbedding_smooth_near_disk (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (R : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (hτ₁ : τ < 1) :
    ∃ U : Set Plane, IsOpen U ∧ Disk ⊆ U ∧ ContDiffOn ℝ ∞ (capDiskEmbedding B c R τ) U := by
  let f (y : Plane) := 1 - τ ^ 2 * ‖y‖ ^ 2
  have hSq : ContDiff ℝ ∞ (fun y : Plane => ‖y‖ ^ 2) := by
    simp_rw [← real_inner_self_eq_norm_sq]
    exact contDiff_inner.comp (contDiff_id.prodMk contDiff_id)
  have hF : ContDiff ℝ ∞ f := contDiff_const.sub (contDiff_const.mul hSq)
  let U := {y : Plane | 0 < f y}
  have hU : IsOpen U := isOpen_lt continuous_const hF.continuous
  have hIn : Disk ⊆ U := by
    intro y hy
    change 0 < 1 - τ ^ 2 * ‖y‖ ^ 2
    have hy' : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
    have hY : ‖y‖ ^ 2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg y) hy' 2
    have hT : τ ^ 2 < 1 := by simpa only [one_pow] using (sq_lt_sq₀ hτ zero_le_one).mpr hτ₁
    have h := mul_le_mul_of_nonneg_left hY (sq_nonneg τ)
    rw [mul_one] at h
    linarith only [hT, h]
  have hSqrt : ContDiffOn ℝ ∞ Real.sqrt (Ioi (0 : ℝ)) := by
    intro x hx
    exact (Real.contDiffAt_sqrt (mem_Ioi.mp hx).ne').contDiffWithinAt
  have hHeight : ContDiffOn ℝ ∞ (fun y => Real.sqrt (f y)) U :=
    hSqrt.comp hF.contDiffOn (fun _ hx => hx)
  have hY : ContDiff ℝ ∞ (fun y : Plane => axisChartPlane B (τ • y)) := by
    exact (axisChartPlane B).contDiff.comp ((τ • ContinuousLinearMap.id ℝ Plane).contDiff)
  refine ⟨U, hU, hIn, ?_⟩
  exact contDiffOn_const.add ((hY.contDiffOn.add (hHeight.smul contDiffOn_const)).const_smul R)

theorem capDiskEmbedding_mem_sphere (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R τ : ℝ} (hR : 0 < R) (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1) :
    MapsTo (capDiskEmbedding B c R τ) Disk (sphere c R) := by
  intro y hy
  have hy₁ : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
  have hY : ‖y‖ ^ 2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg y) hy₁ 2
  have hT : τ ^ 2 < 1 := by simpa only [one_pow] using (sq_lt_sq₀ hτ₀ zero_le_one).mpr hτ₁
  have hYτ := mul_le_mul_of_nonneg_left hY (sq_nonneg τ)
  rw [mul_one] at hYτ
  have hPos : 0 ≤ 1 - τ ^ 2 * ‖y‖ ^ 2 := by linarith only [hT, hYτ]
  rw [mem_sphere, dist_eq_norm, capDiskEmbedding, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le]
  rw [← axisChart_eq_plane_add_axis]
  have hN : ‖axisChart B (τ • y, Real.sqrt (1 - τ ^ 2 * ‖y‖ ^ 2))‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [norm_axisChart_sq, norm_smul, Real.norm_of_nonneg hτ₀, mul_pow, Real.sq_sqrt hPos]
    ring
  rw [hN, mul_one]

theorem capDiskEmbedding_smooth_embedding_transverse
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (hτ₁ : τ < 1) :
    IsSmoothDiskEmbedding (capDiskEmbedding B c R τ) ∧
      B 2 ∉ LinearMap.range (fderiv ℝ (capDiskEmbedding B c R τ) 0).toLinearMap := by
  let d := capDiskEmbedding B c R τ
  let N := axisChartTransverseCoordinates B
  obtain ⟨U, hU, hDU, hSmooth⟩ := capDiskEmbedding_smooth_near_disk B c R hτ.le hτ₁
  have hProj (y : Plane) : N (d y - c) = (R * τ) • y := capDiskEmbedding_proj B c R τ y
  have hDeriv (y : Plane) (hy : y ∈ Disk) : DifferentiableAt ℝ d y := by
    have hD : ContDiffOn ℝ 1 d U := hSmooth.of_le (by decide)
    exact ((hD y (hDU hy)).contDiffAt (hU.mem_nhds (hDU hy))).differentiableAt one_ne_zero
  have hNDeriv (y : Plane) (hy : y ∈ Disk) (z : Plane) :
      N (fderiv ℝ d y z) = (R * τ) • z := by
    have hand : HasFDerivAt (fun w => d w - c) (fderiv ℝ d y) y :=
      (hDeriv y hy).hasFDerivAt.sub_const c
    have hf := (N.hasFDerivAt.comp y hand).fderiv
    have hF : (N ∘ fun w => d w - c) = ⇑((R * τ) • ContinuousLinearMap.id ℝ Plane) := funext hProj
    rw [hF, ContinuousLinearMap.fderiv] at hf
    exact congrArg (fun L : Plane →L[ℝ] Plane => L z) hf.symm
  have hScalar : R * τ ≠ 0 := (mul_pos hR hτ).ne'
  have hInject : Function.Injective (fun w : Plane => (R * τ) • w) :=
    smul_right_injective Plane hScalar
  refine ⟨⟨hSmooth.mono hDU, ?_, ?_⟩, ?_⟩
  · intro y hy z hz hEq
    change d y = d z at hEq
    apply hInject
    change (R * τ) • y = (R * τ) • z
    rw [← hProj y, ← hProj z, hEq]
  · intro y hy
    have hInterior : (interior Disk).Nonempty :=
      ⟨0, interior_maximal ball_subset_closedBall isOpen_ball (mem_ball_self zero_lt_one)⟩
    have hyUnique := uniqueDiffOn_convex (convex_closedBall (0 : Plane) 1) hInterior y hy
    rw [fderivWithin_eq_fderiv hyUnique (hDeriv y hy)]
    intro z w hEq
    apply hInject
    change (R * τ) • z = (R * τ) • w
    rw [← hNDeriv y hy z, ← hNDeriv y hy w, hEq]
  · intro h
    obtain ⟨z, hEq⟩ := h
    have h0 : (0 : Plane) ∈ Disk := mem_closedBall_self zero_le_one
    have hz0 := hNDeriv 0 h0 z
    change fderiv ℝ d 0 z = B 2 at hEq
    rw [hEq, axisChartTransverseCoordinates_axis_vector] at hz0
    have hz : z = 0 := hInject (hz0.symm.trans (smul_zero _).symm)
    rw [hz, map_zero] at hEq
    exact (norm_ne_zero_iff.1 (by rw [B.orthonormal.norm_eq_one 2]; exact one_ne_zero)) hEq.symm

theorem capDiskEmbedding_dist_le (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R τ : ℝ} (hR : 0 < R) (hτ : 0 ≤ τ) (hτ₁ : τ ≤ 1) (y : Plane) (hy : y ∈ Disk) :
    dist (capDiskEmbedding B c R τ y) (c + R • B 2) ≤ 2 * R * τ := by
  let t := τ ^ 2 * ‖y‖ ^ 2
  have hy' : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
  have ht₀ : 0 ≤ t := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have htτ : t ≤ τ ^ 2 := by
    dsimp only [t]
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y) hy' 2) (sq_nonneg τ)
    simpa only [one_pow, mul_one] using h
  have ht₁ : t ≤ 1 := htτ.trans (by simpa only [one_pow] using pow_le_pow_left₀ hτ hτ₁ 2)
  have hS := Real.sqrt_le_sqrt (show (1 - t) ≤ 1 by linarith only [ht₀])
  rw [Real.sqrt_one] at hS
  have hMin : 1 - t ≤ Real.sqrt (1 - t) := by
    apply (sq_le_sq₀ (sub_nonneg.mpr ht₁) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (sub_nonneg.mpr ht₁)]
    nlinarith only [mul_nonneg ht₀ (sub_nonneg.mpr ht₁)]
  have hN : ‖axisChartPlane B (τ • y)‖ ≤ τ := by
    rw [norm_axisChartPlane, norm_smul, Real.norm_of_nonneg hτ]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hy' hτ
  have hE : ‖(Real.sqrt (1 - t) - 1) • B 2‖ ≤ τ := by
    rw [norm_smul, B.orthonormal.norm_eq_one 2, mul_one, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hS)]
    have hτ₂ : τ ^ 2 ≤ τ := by nlinarith only [mul_nonneg hτ (sub_nonneg.mpr hτ₁)]
    linarith only [hMin, htτ, hτ₂]
  rw [dist_eq_norm, capDiskEmbedding]
  have hEq : c + R • (axisChartPlane B (τ • y) + Real.sqrt (1 - τ ^ 2 * ‖y‖ ^ 2) • B 2) -
      (c + R • B 2) =
      R • (axisChartPlane B (τ • y) + (Real.sqrt (1 - t) - 1) • B 2) := by
    simp only [t, sub_smul, one_smul, smul_add, smul_sub]
    abel
  rw [hEq, norm_smul, Real.norm_of_nonneg hR.le]
  exact (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hN hE)) hR.le).trans_eq (by ring)

/-- Disjoint transverse smooth caps around the distinct radial intersections
of the actual sphere and the edge network. -/
theorem exists_disjoint_transverse_junction_caps
    (c : Point) {R : ℝ} (hR : 0 < R) {q : ℕ} (v : Fin q → Point)
    (hv : ∀ i, ‖v i‖ = 1) (hInj : Function.Injective v) :
    ∃ d : Fin q → Plane → Point,
      (∀ i, IsSmoothDiskEmbedding (d i) ∧ MapsTo (d i) Disk (sphere c R) ∧
        d i 0 = c + R • v i ∧ v i ∉ LinearMap.range (fderiv ℝ (d i) 0).toLinearMap) ∧
      Pairwise (fun i j => Disjoint (d i '' Disk) (d j '' Disk)) := by
  classical
  choose B hB using fun i => exists_axis_orthonormalBasis (hv i)
  let x (i : Fin q) := c + R • v i
  have hX : Function.Injective x := by
    intro i j h
    exact hInj (smul_right_injective Point hR.ne' (add_left_cancel h))
  have hδ : ∃ δ > (0 : ℝ), ∀ i j : Fin q, i ≠ j → δ < dist (x i) (x j) := by
    have hAll : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), ∀ i j : Fin q, i ≠ j → δ < dist (x i) (x j) := by
      apply eventually_all.mpr
      intro i
      apply eventually_all.mpr
      intro j
      by_cases h : i = j
      · exact Eventually.of_forall (fun _ hj => (hj h).elim)
      · have hEv : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < dist (x i) (x j) :=
          nhdsWithin_le_nhds (Iio_mem_nhds (dist_pos.mpr (hX.ne h)))
        exact hEv.mono (fun _ hδ _ => hδ)
    have hP : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    obtain ⟨δ, hδ, hA⟩ := (hP.and hAll).exists
    exact ⟨δ, hδ, hA⟩
  obtain ⟨δ, hδ₀, hδ⟩ := hδ
  let τ := min (1 / 4 : ℝ) (δ / (8 * R))
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hδ₀ (mul_pos (by norm_num) hR))
  have hτ₁ : τ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hτR : 2 * R * τ ≤ δ / 4 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hR)).mp (min_le_right (1 / 4 : ℝ) (δ / (8 * R)))
    dsimp only [τ]
    nlinarith only [h]
  let d (i : Fin q) := capDiskEmbedding (B i) c R τ
  refine ⟨d, ?_, ?_⟩
  · intro i
    have h := capDiskEmbedding_smooth_embedding_transverse (B i) c hR hτ hτ₁
    exact ⟨h.1, capDiskEmbedding_mem_sphere (B i) c hR hτ.le hτ₁,
      (capDiskEmbedding_zero (B i) c R τ).trans (by rw [hB i]), hB i ▸ h.2⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨y, hy, hY⟩ := hz
    obtain ⟨w, hw, hW⟩ := hz'
    have hDi := capDiskEmbedding_dist_le (B i) c hR hτ.le hτ₁.le y hy
    have hDj := capDiskEmbedding_dist_le (B j) c hR hτ.le hτ₁.le w hw
    rw [show capDiskEmbedding (B i) c R τ y = z from hY, hB i] at hDi
    rw [show capDiskEmbedding (B j) c R τ w = z from hW, hB j] at hDj
    have hTri : dist (x i) (x j) ≤ dist z (x i) + dist z (x j) := dist_triangle_left _ _ _
    linarith only [hδ i j hij, hTri, hDi.trans hτR, hDj.trans hτR, hδ₀]

end Thesis.MeasureGeometry
