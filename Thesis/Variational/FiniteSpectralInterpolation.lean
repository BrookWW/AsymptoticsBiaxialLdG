module

public import Thesis.Variational.FractionalDisplacement
import Thesis.Variational.H10FractionalEmbedding

/-! Quadratic interpolation for finite mode sums on a smooth domain. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Matrix.Norms.Frobenius

namespace Thesis

private theorem eLpNorm_two_sq_Lp_tensor {U : Set Point} (p : Lp S0 2 (volume.restrict U)) :
    eLpNorm p 2 (volume.restrict U) ^ 2 = ENNReal.ofReal (‖p‖ ^ 2) := by
  rw [eLpNorm_two_sq_eq_tensor_lintegral,lintegral_sq_norm_lp]

private theorem translationEnergy_le_finite_split
    {U : Set Point} {ι : Type*} (a : ι → Lp S0 2 (volume.restrict U))
    (μ b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hμ : ∀ i, 0 ≤ μ i)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hTrans : ∀ (u : Point → S0) (D : Point → Gradient) (hu : MemH1 U u D)
      (z : Point), z ∈ ball (0 : Point) (diam U+1) →
      restrictedTranslationEnergy U u z ≤ ENNReal.ofReal
        (A * ‖z‖ ^ 2 * ‖(hu.1.toLp u,fun j => (hu.2.1 j).toLp (fun x => D x j))‖ ^ 2))
    (hValue : ∀ (F : Finset ι) (c : ι → ℝ),
      ‖∑ i ∈ F, c i • a i‖ ^ 2 ≤ ∑ i ∈ F, μ i*b i*c i^2)
    (hGraph : ∀ (F : Finset ι) (c : ι → ℝ),
      ∃ (D : Point → Gradient) (h : MemH1 U (⇑(∑ i ∈ F, c i • a i)) D),
        ‖(h.1.toLp (⇑(∑ i ∈ F, c i • a i)), fun j => (h.2.1 j).toLp (fun x => D x j))‖ ^ 2 ≤
          B * ∑ i ∈ F, b i*c i^2)
    (F : Finset ι) (c : ι → ℝ) {z : Point} (hz : z ∈ ball (0 : Point) (diam U+1)) :
    restrictedTranslationEnergy U (⇑(∑ i ∈ F, c i • a i)) z ≤
      ENNReal.ofReal (2*(A*B+4)) * (∑ i ∈ F, ENNReal.ofReal (b i*c i^2*min (‖z‖^2) (μ i))) := by
  classical
  let l := F.filter (fun i => ‖z‖ ^ 2 ≤ μ i)
  let h := F.filter (fun i => ¬ ‖z‖ ^ 2 ≤ μ i)
  let u := ∑ i ∈ l, c i • a i
  let v := ∑ i ∈ h, c i • a i
  let w := ∑ i ∈ F, c i • a i
  have hw : u+v = w := Finset.sum_filter_add_sum_filter_not F (fun i => ‖z‖^2 ≤ μ i) (fun i => c i • a i)
  have hEa : (w : Point → S0) =ᵐ[volume.restrict U] (u : Point → S0) + (v : Point → S0) :=
    hw ▸ (Lp.coeFn_add u v)
  obtain ⟨D,hU,hNorm⟩ := hGraph l c
  let W (i : ι) := b i*c i^2
  have hW (i : ι) : 0 ≤ W i := mul_nonneg (hb i) (sq_nonneg _)
  let L := ‖z‖ ^ 2 * ∑ i ∈ l, W i
  let H := ∑ i ∈ h, μ i * W i
  have hL : 0 ≤ L := mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => hW i)
  have hH : 0 ≤ H := Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (hW i)
  have hA' := mul_nonneg hA hB
  have hLow : restrictedTranslationEnergy U (⇑u) z ≤ ENNReal.ofReal (A*B*L) := by
    refine (hTrans (⇑u) D hU z hz).trans (ENNReal.ofReal_le_ofReal ?_)
    have hh := mul_le_mul_of_nonneg_left hNorm (mul_nonneg hA (sq_nonneg ‖z‖))
    exact hh.trans_eq (by unfold L W; ring)
  have hHigh : restrictedTranslationEnergy U (⇑v) z ≤ ENNReal.ofReal (4*H) := by
    refine (restrictedTranslationEnergy_le_L2 z (Lp.memLp v)).trans ?_
    rw [eLpNorm_two_sq_Lp_tensor,← ENNReal.ofReal_ofNat,← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by simpa only [H,W,mul_assoc] using hValue h c)
      (by norm_num))
  have hSum : L + H = ∑ i ∈ F, W i * min (‖z‖ ^ 2) (μ i) := by
    unfold L H
    rw [Finset.mul_sum]
    simp only [l,h,Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : ‖z‖ ^ 2 ≤ μ i
    · simp only [if_pos hi,if_neg (not_not.mpr hi),add_zero,min_eq_left hi,mul_comm]
    · simp only [if_neg hi,if_pos hi,zero_add,min_eq_right (le_of_not_ge hi),mul_comm]
  rw [restrictedTranslationEnergy_congr_ae hEa]
  have hS : 0 ≤ 2*(A*B+4) := by positivity
  calc
    _ ≤ 2 * (restrictedTranslationEnergy U (⇑u) z + restrictedTranslationEnergy U (⇑v) z) :=
      restrictedTranslationEnergy_add_le z (Lp.memLp u) (Lp.memLp v)
    _ ≤ 2 * (ENNReal.ofReal (A*B*L) + ENNReal.ofReal (4*H)) :=
      mul_le_mul_right (add_le_add hLow hHigh) _
    _ = ENNReal.ofReal (2 * (A*B*L + 4*H)) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hA' hL) (mul_nonneg (by norm_num) hH),
        ← ENNReal.ofReal_ofNat,← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ ENNReal.ofReal ((2*(A*B+4)) * (L+H)) := ENNReal.ofReal_le_ofReal (by
      nlinarith only [mul_nonneg hA' hH,hL])
    _ = _ := by
      rw [hSum,ENNReal.ofReal_mul hS,ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact mul_nonneg (hW i) (le_min (sq_nonneg _) (hμ i))

private theorem lintegral_weighted_min_kernel
    {ι : Type*} (F : Finset ι) (s : ℝ) (μ b : ι → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hμ : ∀ i, 0 < μ i) (hb : ∀ i, 0 ≤ b i)
    {D : ℝ≥0∞} (hD : D < ⊤)
    (hScale : ∀ μ : ℝ, 0 < μ → (∫⁻ z : Point, ENNReal.ofReal (fractionalTranslationKernel s μ z)) =
      D * ENNReal.ofReal (μ ^ (1-s))) :
    (∫⁻ z : Point, (ENNReal.ofReal K * ∑ i ∈ F, ENNReal.ofReal (b i * min (‖z‖ ^ 2) (μ i))) *
      ENNReal.ofReal ((‖z‖ ^ (3+2*s))⁻¹)) =
      ENNReal.ofReal (K * D.toReal * (∑ i ∈ F, b i * μ i ^ (1-s))) := by
  let k (i : ι) (z : Point) := ENNReal.ofReal (fractionalTranslationKernel s (μ i) z)
  have hk (i : ι) : Measurable (k i) := ENNReal.measurable_ofReal.comp (fractionalTranslationKernel_measurable _ _)
  have hPoint (z : Point) :
      (ENNReal.ofReal K * ∑ i ∈ F, ENNReal.ofReal (b i * min (‖z‖ ^ 2) (μ i))) *
        ENNReal.ofReal ((‖z‖ ^ (3+2*s))⁻¹) =
      ENNReal.ofReal K * ∑ i ∈ F, ENNReal.ofReal (b i) * k i z := by
    rw [mul_assoc,Finset.sum_mul]
    apply congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal K * x)
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_mul (hb i),mul_assoc,← ENNReal.ofReal_mul (le_min (sq_nonneg _) (hμ i).le)]
    rfl
  simp_rw [hPoint]
  have hF : Measurable (fun z => ∑ i ∈ F, ENNReal.ofReal (b i) * k i z) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (hk i))
  have hTSum : (∫⁻ z : Point, ∑ i ∈ F, ENNReal.ofReal (b i) * k i z) =
      ∑ i ∈ F, ∫⁻ z : Point, ENNReal.ofReal (b i) * k i z :=
    lintegral_finsetSum (f := fun i z => ENNReal.ofReal (b i) * k i z)
      F (fun i _ => measurable_const.mul (hk i))
  rw [lintegral_const_mul'' _ hF.aemeasurable,hTSum]
  have hInt (i : ι) : (∫⁻ z, ENNReal.ofReal (b i) * k i z) =
      D * ENNReal.ofReal (b i * μ i ^ (1-s)) := by
    rw [lintegral_const_mul'' _ (hk i).aemeasurable]
    change ENNReal.ofReal (b i) * (∫⁻ z, ENNReal.ofReal (fractionalTranslationKernel s (μ i) z)) = _
    rw [hScale (μ i) (hμ i),ENNReal.ofReal_mul (hb i),mul_left_comm]
  simp_rw [hInt]
  rw [← Finset.mul_sum]
  have hS : (∑ i ∈ F, ENNReal.ofReal (b i * μ i^(1-s))) =
      ENNReal.ofReal (∑ i ∈ F, b i * μ i^(1-s)) :=
    (ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hb i) (Real.rpow_nonneg (hμ i).le _))).symm
  rw [hS,← ENNReal.ofReal_toReal hD.ne,← mul_assoc,
    ← ENNReal.ofReal_mul hK,← ENNReal.ofReal_mul (mul_nonneg hK ENNReal.toReal_nonneg)]
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

/-- A family with square (L^2) bound weighted by (mu_i b_i) and
square (H^1) graph bound weighted by (b_i) has intrinsic (H^s)
energy weighted by (mu_i^{1-s}b_i). -/
theorem exists_fractionalEnergy_le_finite_modes {U : Set Point} (hU : IsSmoothDomain U)
    {ι : Type*} (a : ι → Lp S0 2 (volume.restrict U)) (μ b : ι → ℝ)
    (s : ℝ) (hs : 0 < s) (hs₁ : s < 1)
    (M B : ℝ) (hM : 0 < M) (hB : 0 ≤ B) (hμ : ∀ i, 0 < μ i ∧ μ i ≤ M) (hb : ∀ i, 0 ≤ b i)
    (hValue : ∀ (F : Finset ι) (c : ι → ℝ),
      ‖∑ i ∈ F, c i • a i‖ ^ 2 ≤ ∑ i ∈ F, μ i*b i*c i^2)
    (hGraph : ∀ (F : Finset ι) (c : ι → ℝ),
      ∃ (D : Point → Gradient) (h : MemH1 U (⇑(∑ i ∈ F, c i • a i)) D),
        ‖(h.1.toLp (⇑(∑ i ∈ F, c i • a i)), fun j => (h.2.1 j).toLp (fun x => D x j))‖ ^ 2 ≤
          B * ∑ i ∈ F, b i*c i^2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Finset ι) (c : ι → ℝ),
      fractionalEnergy s U (⇑(∑ i ∈ F, c i • a i)) ≤
        ENNReal.ofReal (C * ∑ i ∈ F, μ i^(1-s)*b i*c i^2) := by
  obtain ⟨A,hA,hTrans⟩ := hU.exists_restrictedTranslationEnergy_le_memH1_graph
  obtain ⟨D,hD,hScale⟩ := exists_fractionalTranslationKernel_integral s hs hs₁
  let K := 2*(A*B+4)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let C := M^s + K*D.toReal
  have hC : 0 ≤ C := add_nonneg (Real.rpow_nonneg hM.le _) (mul_nonneg hK ENNReal.toReal_nonneg)
  refine ⟨C,hC,?_⟩
  intro F c
  let W (i : ι) := b i*c i^2
  let P := ∑ i ∈ F, c i • a i
  let R := ∑ i ∈ F, W i * μ i^(1-s)
  have hW (i : ι) : 0 ≤ W i := mul_nonneg (hb i) (sq_nonneg _)
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => mul_nonneg (hW i) (Real.rpow_nonneg (hμ i).1.le _)
  let T (z : Point) := ENNReal.ofReal K * ∑ i ∈ F, ENNReal.ofReal (W i * min (‖z‖^2) (μ i))
  have hT (z : Point) (hz : z ∈ ball (0 : Point) (diam U+1)) :
      restrictedTranslationEnergy U (⇑P) z ≤ T z :=
    translationEnergy_le_finite_split a μ b hb (fun i => (hμ i).1.le) A B hA.le hB hTrans hValue hGraph F c hz
  have hL : eLpNorm P 2 (volume.restrict U) ^ 2 ≤ ENNReal.ofReal (M^s * R) := by
    rw [eLpNorm_two_sq_Lp_tensor]
    apply ENNReal.ofReal_le_ofReal
    refine (hValue F c).trans ?_
    unfold R
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi : μ i = μ i ^ s * μ i ^ (1-s) := by
      rw [← Real.rpow_add (hμ i).1,add_sub_cancel,Real.rpow_one]
    calc
      _ = μ i * W i := by unfold W; ring
      _ = μ i^s * (W i * μ i^(1-s)) := by
        calc
          _ = (μ i^s * μ i^(1-s)) * W i := congrArg (· * W i) hi
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hμ i).1.le (hμ i).2 hs.le)
        (mul_nonneg (hW i) (Real.rpow_nonneg (hμ i).1.le _))
  have hWeighted :=
    lintegral_weighted_min_kernel F s μ W K hK (fun i => (hμ i).1) hW hD hScale
  have hF := fractionalEnergy_le_of_restrictedTranslationEnergy_bound hU.1 s (Lp.memLp P) T hT
  have hRest : (∫⁻ z in ball (0 : Point) (diam U+1), T z * ENNReal.ofReal ((‖z‖ ^ (3+2*s))⁻¹)) ≤
      ENNReal.ofReal (K*D.toReal*R) :=
    (lintegral_mono' Measure.restrict_le_self le_rfl).trans hWeighted.le
  refine hF.trans ((add_le_add hL hRest).trans_eq ?_)
  rw [← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg hM.le _) hR)
    (mul_nonneg (mul_nonneg hK ENNReal.toReal_nonneg) hR)]
  congr 1
  have hEq : R = ∑ i ∈ F, μ i^(1-s)*b i*c i^2 := by
    apply Finset.sum_congr rfl
    intro i _
    unfold W
    ring
  rw [← hEq]
  unfold C
  ring

end Thesis
