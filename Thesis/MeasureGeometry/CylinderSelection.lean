module

public import Thesis.MeasureGeometry.MovingCylinderMass

/-! Choosing a compact interval of lateral radii away from the line support. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace Thesis.MeasureGeometry

private def transversePart (e x : Point) : Point := x - cylinderHeight e x • e

private theorem norm_transversePart_le {e : Point} (he : ‖e‖ = 1) (x : Point) :
    ‖transversePart e x‖ ≤ ‖x‖ := by
  have hOrth : inner ℝ (transversePart e x) e = 0 := by
    rw [transversePart, inner_sub_left, real_inner_smul_left, real_inner_comm e x,
      real_inner_self_eq_norm_sq, he, cylinderHeight]
    ring
  have hSum : transversePart e x + cylinderHeight e x • e = x := sub_add_cancel _ _
  have hSq := norm_add_sq_real (transversePart e x) (cylinderHeight e x • e)
  rw [hSum, real_inner_smul_right, hOrth, mul_zero, mul_zero, add_zero] at hSq
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith only [hSq, sq_nonneg ‖cylinderHeight e x • e‖]

/-- Orthogonal transverse radius changes by at most the ambient distance. -/
theorem lipschitzWith_cylinderTransverseRadius {e : Point} (he : ‖e‖ = 1) :
    LipschitzWith 1 (cylinderTransverseRadius e) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hLin : transversePart e x - transversePart e y = transversePart e (x - y) := by
    simp only [transversePart, cylinderHeight, inner_sub_right, sub_smul]
    abel
  change dist ‖transversePart e x‖ ‖transversePart e y‖ ≤ (1 : ℝ) * dist x y
  rw [one_mul, dist_eq_norm x y]
  refine (dist_norm_norm_le _ _).trans ?_
  rw [hLin]
  exact norm_transversePart_le he _

/-- An interval longer than a compact set's Hausdorff length contains a
nonempty closed subinterval of radii missing its entire projection. -/
theorem exists_closed_axisRadius_interval_avoiding_compact
    {K : Set Point} (hK : IsCompact K) (x : Point) {e : Point} (he : ‖e‖ = 1)
    {R₀ R₁ : ℝ} (hLen : HausdorffOne K < ENNReal.ofReal (R₁ - R₀)) :
    ∃ s t : ℝ, R₀ < s ∧ s < t ∧ t < R₁ ∧
      Disjoint (Icc s t) ((fun y => cylinderTransverseRadius e (y - x)) '' K) := by
  let f (y : Point) := cylinderTransverseRadius e (y - x)
  have hIso : Isometry (fun y : Point => y - x) := by
    apply Isometry.of_dist_eq
    intro y z
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  have hf : LipschitzWith 1 f := by
    simpa only [f, one_mul, Function.comp_def] using (lipschitzWith_cylinderTransverseRadius he).comp hIso.lipschitz
  have hMiss : (Ioo R₀ R₁ \ f '' K).Nonempty := by
    by_contra! h
    have hSub : Ioo R₀ R₁ ⊆ f '' K := by
      intro t ht
      by_contra ht'
      have hmem : t ∈ Ioo R₀ R₁ \ f '' K := ⟨ht, ht'⟩
      rw [h] at hmem
      exact (Set.notMem_empty t) hmem
    have hM := hf.hausdorffMeasure_image_le (d := 1) zero_le_one K
    have hM' : (volume : Measure ℝ) (f '' K) ≤ HausdorffOne K := by
      simpa only [hausdorffMeasure_real, ENNReal.coe_one, ENNReal.one_rpow, one_mul] using hM
    have hp := (measure_mono (μ := (volume : Measure ℝ)) hSub).trans hM'
    rw [Real.volume_Ioo] at hp
    exact hLen.not_ge hp
  have hG : IsOpen (Ioo R₀ R₁ \ f '' K) := isOpen_Ioo.sdiff (hK.image hf.continuous).isClosed
  obtain ⟨z, hz⟩ := hMiss
  obtain ⟨d, hd, hdG⟩ := Metric.isOpen_iff.mp hG z hz
  have hSub : Icc (z - d / 2) (z + d / 2) ⊆ Ioo R₀ R₁ \ f '' K := by
    intro t ht
    apply hdG
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith only [ht.1, ht.2, hd]
  refine ⟨z - d / 2, z + d / 2, ?_, by linarith, ?_, ?_⟩
  · exact (hSub (left_mem_Icc.2 (by linarith))).1.1
  · exact (hSub (right_mem_Icc.2 (by linarith))).1.2
  · exact disjoint_left.mpr fun _ ht => (hSub ht).2

/-- A sufficiently light compact annular cylinder has a band of closed
lateral radii missing the actual line support. -/
theorem exists_closed_axisRadius_interval_avoiding_lineSupport
    (μ : Measure Point) [IsFiniteMeasure μ] [μ.OuterRegular]
    {Ω A : Set Point} (hA : IsCompact A) (hAΩ : A ⊆ Ω)
    {η : ℝ} (hη : 0 < η)
    (hD : ∀ x ∈ Ω ∩ μ.support, ∃ θ ≥ η / 2, Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ))
    (x : Point) {e : Point} (he : ‖e‖ = 1)
    {R₀ R₁ : ℝ} (hSmall : ENNReal.ofReal (40 / η) * μ A < ENNReal.ofReal (R₁ - R₀)) :
    ∃ s t : ℝ, R₀ < s ∧ s < t ∧ t < R₁ ∧
      ∀ y ∈ A, cylinderTransverseRadius e (y - x) ∈ Icc s t → y ∉ μ.support := by
  let K := A ∩ μ.support
  have hK : IsCompact K := hA.inter_right μ.isClosed_support
  have hKΩ : K ⊆ Ω ∩ μ.support := inter_subset_inter hAΩ Subset.rfl
  have hLen := hausdorffOne_le_of_positive_oneDensity μ hKΩ hη hD
  have hLen' : HausdorffOne K < ENNReal.ofReal (R₁ - R₀) :=
    (hLen.trans (mul_le_mul_right (measure_mono inter_subset_left) _)).trans_lt hSmall
  obtain ⟨s, t, hs, hst, ht, hDisj⟩ := exists_closed_axisRadius_interval_avoiding_compact hK x he hLen'
  refine ⟨s, t, hs, hst, ht, fun y hy hyr hyL => ?_⟩
  exact (disjoint_left.mp hDisj) hyr ⟨y, ⟨hy, hyL⟩, rfl⟩

end Thesis.MeasureGeometry
