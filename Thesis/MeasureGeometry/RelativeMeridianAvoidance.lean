module

public import Thesis.MeasureGeometry.RelativeMeridians
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! Boundary-fixed point avoidance by a small translation with a time factor. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace Thesis.MeasureGeometry

private def annulusTranslationFactor (t : ℝ) : ℝ := t * (1-t)

private theorem annulusTranslationFactor_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < annulusTranslationFactor t :=
  mul_pos ht.1 (sub_pos.mpr ht.2)

private theorem dimH_annulus_badTranslations {G : ℝ × ℝ → Point}
    (hG : ContDiffOn ℝ ∞ G (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ))) (p : Point) :
    dimH ((fun s : ℝ × ℝ => (annulusTranslationFactor s.1)⁻¹ • (p - G s)) ''
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ))) ≤ 2 := by
  let W := Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)
  let T (s : ℝ × ℝ) := (annulusTranslationFactor s.1)⁻¹ • (p - G s)
  have hw : W ⊆ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := prod_mono Ioo_subset_Icc_self Subset.rfl
  have hB : ContDiff ℝ 1 (fun s : ℝ × ℝ => annulusTranslationFactor s.1) := by
    unfold annulusTranslationFactor
    exact contDiff_fst.mul (contDiff_const.sub contDiff_fst)
  have hOneInf : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by decide
  have hG₁ : ContDiffOn ℝ 1 G W := (hG.of_le hOneInf).mono hw
  have hT : ContDiffOn ℝ 1 T W := (hB.contDiffOn.inv
    (fun _ hx => (annulusTranslationFactor_pos hx.1).ne')).smul
      (contDiffOn_const.sub hG₁)
  have hDim : dimH W ≤ 2 := by
    calc
      _ ≤ dimH (univ : Set (ℝ × ℝ)) := dimH_mono (subset_univ _)
      _ = 2 := by rw [Real.dimH_univ_eq_finrank]; simp [Module.finrank_prod]
  exact (hT.dimH_image_le ((convex_Ioo _ _).prod convex_univ) Subset.rfl).trans hDim

/-- A boundary-fixed perturbation stays in the prescribed open set and
avoids every specified point. The excluded translations are smooth
two-dimensional images in the ambient three-dimensional space. -/
theorem relativeAnnulusPointAvoidance : External.RelativeAnnulusPointAvoidance := by
  classical
  intro U hU P F hSmooth hFU hEnd
  obtain ⟨G,hG,hGF⟩ := hSmooth
  let W := Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)
  let bad : Set Point := ⋃ p : ↥P, (fun s : ℝ × ℝ =>
    (annulusTranslationFactor s.1)⁻¹ • (p.val-G s)) '' W
  have hBad : dimH bad ≤ 2 := by
    rw [dimH_iUnion]
    exact iSup_le fun p => dimH_annulus_badTranslations hG p.val
  have hDim : dimH bad < Module.finrank ℝ Point := by
    have h3 : Module.finrank ℝ Point = 3 := finrank_euclideanSpace_fin
    rw [h3]
    exact hBad.trans_lt (by norm_num)
  have hDense := dense_compl_of_dimH_lt_finrank hDim
  letI : CompactSpace NativeCircle := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let K := range F
  have hK : IsCompact K := isCompact_range F.continuous
  have hKU : K ⊆ U := by rintro _ ⟨x,rfl⟩; exact hFU x
  obtain ⟨δ,hδ,hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨v,hvBad,hvBall⟩ := hDense.exists_mem_open isOpen_ball
    ⟨(0 : Point),mem_ball_self hδ⟩
  have hvNorm : ‖v‖ < δ := mem_ball_zero_iff.mp hvBall
  let F' (x : unitInterval × NativeCircle) := F x + annulusTranslationFactor x.1.val • v
  have hT : Continuous (fun x : unitInterval × NativeCircle => x.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hF' : Continuous F' := F.continuous.add ((hT.mul (continuous_const.sub hT)).smul continuous_const)
  let H : C(unitInterval × NativeCircle, Point) := ⟨F',hF'⟩
  have hH₀ (z : NativeCircle) : H (0,z) = F (0,z) := by
    change F (0,z) + annulusTranslationFactor 0 • v = F (0,z)
    simp [annulusTranslationFactor]
  have hH₁ (z : NativeCircle) : H (1,z) = F (1,z) := by
    change F (1,z) + annulusTranslationFactor 1 • v = F (1,z)
    simp [annulusTranslationFactor]
  refine ⟨H, ?_, fun z => ⟨hH₀ z,hH₁ z⟩⟩
  rintro ⟨t,z⟩
  have ht₀ : 0 ≤ t.val := t.property.1
  have ht₁ : t.val ≤ 1 := t.property.2
  have hβ₀ : 0 ≤ annulusTranslationFactor t.val := mul_nonneg ht₀ (sub_nonneg.mpr ht₁)
  have hβ₁ : annulusTranslationFactor t.val ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (sub_le_self (1 : ℝ) ht₀) ht₀
    dsimp only [annulusTranslationFactor]
    simpa only [mul_one] using h.trans (by simpa only [mul_one] using ht₁)
  have hHU : H (t,z) ∈ U := by
    apply hδU (thickening_subset_cthickening _ _ _)
    apply mem_thickening_iff.mpr
    refine ⟨F (t,z), mem_range_self _, ?_⟩
    rw [dist_eq_norm]
    change ‖F (t,z) + annulusTranslationFactor t.val • v - F (t,z)‖ < δ
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hβ₀]
    exact (mul_le_of_le_one_left (norm_nonneg _) hβ₁).trans_lt hvNorm
  refine ⟨hHU, ?_⟩
  by_cases htZero : t.val = 0
  · have ht : t = 0 := Subtype.ext htZero
    rw [ht,hH₀]
    exact (hEnd z).1
  by_cases htOne : t.val = 1
  · have ht : t = 1 := Subtype.ext htOne
    rw [ht,hH₁]
    exact (hEnd z).2
  have ht : t.val ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht₀ (Ne.symm htZero),lt_of_le_of_ne ht₁ htOne⟩
  intro hp
  let p : ↥P := ⟨H (t,z),hp⟩
  obtain ⟨u,hu⟩ := circleNativeParam_closed_surjective z
  have hGz : G (t.val,u.val) = F (t,z) := (hGF t u.val).trans (congrArg (fun x => F (t,x)) hu)
  have hEq : p.val - G (t.val,u.val) = annulusTranslationFactor t.val • v := by
    rw [hGz]
    change F (t,z) + annulusTranslationFactor t.val • v - F (t,z) = _
    rw [add_sub_cancel_left]
  apply hvBad
  refine mem_iUnion.mpr ⟨p, (t.val,u.val), ⟨ht,mem_univ _⟩, ?_⟩
  change (annulusTranslationFactor t.val)⁻¹ • (p.val - G (t.val,u.val)) = v
  rw [hEq,smul_smul,inv_mul_cancel₀ (annulusTranslationFactor_pos ht).ne',one_smul]

end Thesis.MeasureGeometry
