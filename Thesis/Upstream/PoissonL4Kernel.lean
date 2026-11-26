module

public import Thesis.Definitions
import HarmonicMaps.Analysis.AffineBallMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import StratificationTheory.Foundation.DominatedL2Pullback

/-! The three-dimensional Newton kernel and the local L⁴ Hölder bounds. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ENNReal NNReal

namespace Thesis

/-- Exact (L^p) change of variables on the affine preimage of a measurable
region, with the original derivative- and forcing-norm normalization. -/
theorem eLpNorm_affine_preimage {E : Type*} [NormedAddCommGroup E] (a b : Point)
    {t : ℝ} (ht : 0 < t) (S : Set Point) {p : ℝ≥0∞} (hp : p ≠ ⊤) (f : Point → E) :
    let F (x : Point) := a + t • (x - b)
    eLpNorm (f ∘ F) p (volume.restrict (F ⁻¹' S)) =
      ENNReal.ofReal ((t ^ 3)⁻¹) ^ (1 / p).toReal * eLpNorm f p (volume.restrict S) := by
  intro F
  have hF : MeasurableEmbedding F := affineBall_measurableEmbedding a b ht.ne'
  rw [← hF.eLpNorm_map_measure, ← hF.restrict_map, affineBall_map_volume a b ht,
    Measure.restrict_smul, eLpNorm_smul_measure_of_ne_top hp, smul_eq_mul]

/-- Finite (L^p) membership under the same affine change of variables. -/
theorem memLp_affine_preimage {E : Type*} [NormedAddCommGroup E] (a b : Point)
    {t : ℝ} (ht : 0 < t) (S : Set Point) {p : ℝ≥0∞} {f : Point → E}
    (hf : MemLp f p (volume.restrict S)) :
    let F (x : Point) := a + t • (x - b)
    MemLp (f ∘ F) p (volume.restrict (F ⁻¹' S)) := by
  intro F
  have hF : MeasurableEmbedding F := affineBall_measurableEmbedding a b ht.ne'
  have hMap : Measure.map F (volume.restrict (F ⁻¹' S)) =
      ENNReal.ofReal ((t ^ 3)⁻¹) • volume.restrict S := by
    rw [← hF.restrict_map, affineBall_map_volume a b ht, Measure.restrict_smul]
  have hMem := hf.smul_measure (c := ENNReal.ofReal ((t ^ 3)⁻¹)) ENNReal.ofReal_ne_top
  exact (hMap.symm ▸ hMem).comp_of_map hF.measurable.aemeasurable

/-- The exponent conjugate to four, for the inverse-square Newton kernel. -/
abbrev poissonL4Conjugate : ℝ≥0∞ := ENNReal.ofReal (4 / 3 : ℝ)

private theorem poissonL4Conjugate_toReal : poissonL4Conjugate.toReal = 4 / 3 :=
  ENNReal.toReal_ofReal (by norm_num)

private theorem poissonL4Conjugate_div_toReal : (1 / poissonL4Conjugate).toReal = 3 / 4 := by
  rw [ENNReal.toReal_div, ENNReal.toReal_one, poissonL4Conjugate_toReal]
  norm_num

private theorem poissonL4Conjugate_ne_zero : poissonL4Conjugate ≠ 0 :=
  ENNReal.ofReal_ne_zero_iff.mpr (by norm_num : (0 : ℝ) < 4 / 3)

/-- The inverse power that appears in pointwise potential bounds. -/
@[expose] def poissonInversePower (s : ℝ) (z : Point) : ℝ := ‖z‖ ^ (-s)

theorem poissonInversePower_nonneg (s : ℝ) (z : Point) : 0 ≤ poissonInversePower s z :=
  Real.rpow_nonneg (norm_nonneg _) _

theorem measurable_poissonInversePower (s : ℝ) : Measurable (poissonInversePower s) :=
  measurable_norm.pow measurable_const

private theorem poissonInversePower_rpow (s p : ℝ) (z : Point) :
    (poissonInversePower s z) ^ p = poissonInversePower (s * p) z := by
  dsimp only [poissonInversePower]
  rw [← Real.rpow_mul (norm_nonneg z), neg_mul]

private theorem poissonInversePower_smul (s : ℝ) {t : ℝ} (ht : 0 ≤ t) (z : Point) :
    poissonInversePower s (t • z) = t ^ (-s) * poissonInversePower s z := by
  dsimp only [poissonInversePower]
  rw [norm_smul, Real.norm_of_nonneg ht, Real.mul_rpow ht (norm_nonneg _)]

private theorem poissonInversePower_memLp_conjugate_unit {s : ℝ} (hs : s < 9 / 4) :
    MemLp (poissonInversePower s) poissonL4Conjugate (volume.restrict (ball (0 : Point) 2)) := by
  let μ := (volume : Measure Point).restrict (ball (0 : Point) 2)
  have hInt : Integrable (poissonInversePower (s*(4/3))) μ := by
    apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := s * (4/3))
      (by rw [finrank_euclideanSpace_fin]; norm_num)
      (by rw [finrank_euclideanSpace_fin]; norm_num; linarith only [hs])
    · exact Eventually.of_forall fun z => by
        rw [one_mul, Real.norm_of_nonneg (poissonInversePower_nonneg _ _)]
        exact le_rfl
    · exact (measurable_poissonInversePower _).aestronglyMeasurable
  refine ⟨(measurable_poissonInversePower _).aestronglyMeasurable, ?_⟩
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top poissonL4Conjugate_ne_zero ENNReal.ofReal_ne_top).2
  have heq : (fun z => ‖poissonInversePower s z‖ₑ ^ poissonL4Conjugate.toReal) =
      fun z => ENNReal.ofReal (poissonInversePower (s*(4/3)) z) := by
    funext z
    rw [poissonL4Conjugate_toReal, ← ofReal_norm,
      Real.norm_of_nonneg (poissonInversePower_nonneg _ _)]
    exact (ENNReal.ofReal_rpow_of_nonneg (poissonInversePower_nonneg s z)
      (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans
        (congrArg ENNReal.ofReal (poissonInversePower_rpow s (4/3) z))
  rw [heq]
  have hFin : (∫⁻ z, ‖poissonInversePower (s*(4/3)) z‖ₑ ∂μ) < ⊤ :=
    hInt.hasFiniteIntegral
  simpa only [← ofReal_norm, Real.norm_of_nonneg (poissonInversePower_nonneg _ _)] using hFin

private theorem poissonInversePower_memLp_conjugate_radius (s : ℝ) (hs : s < 9 / 4) {r : ℝ} (hr : 0 < r) :
    MemLp (poissonInversePower s) poissonL4Conjugate (volume.restrict (ball (0 : Point) (2*r))) := by
  let g := poissonInversePower s
  have ht : 0 < r⁻¹ := inv_pos.mpr hr
  have hS : (fun x : Point => (0 : Point) + r⁻¹ • (x-0)) ⁻¹' ball (0 : Point) 2 =
      ball (0 : Point) (2*r) := by
    ext x
    exact (affineBall_mem_ball_iff 0 0 ht 2 x).trans
      (by rw [div_inv_eq_mul])
  have hg := memLp_affine_preimage (0 : Point) 0 ht (ball 0 2) (poissonInversePower_memLp_conjugate_unit hs)
  dsimp only at hg
  rw [hS] at hg
  have hF : (poissonInversePower s ∘ fun x : Point => 0 + r⁻¹ • (x - 0)) = r ^ s • g := by
    funext x
    simp only [Function.comp_apply, sub_zero, zero_add, Pi.smul_apply, smul_eq_mul]
    rw [poissonInversePower_smul s ht.le, Real.inv_rpow hr.le, Real.rpow_neg hr.le, inv_inv]
  have h := hg.ae_eq (Eventually.of_forall (congrFun hF))
  have hs : r ^ (-s) • (r ^ s • g) = g := by
    rw [smul_smul, ← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero, one_smul]
  have h' := h.const_smul (r ^ (-s))
  rw [hs] at h'
  exact h'

private theorem poissonInversePower_conjugate_radius_eq (s : ℝ) {r : ℝ} (hr : 0 < r) :
    (eLpNorm (poissonInversePower s) poissonL4Conjugate (volume.restrict (ball (0 : Point) (2*r)))).toReal =
      r ^ (9 / 4 - s) *
        (eLpNorm (poissonInversePower s) poissonL4Conjugate (volume.restrict (ball (0 : Point) 2))).toReal := by
  let K := poissonInversePower s
  let F (x : Point) := (0 : Point) + r⁻¹ • (x-0)
  have ht : 0 < r⁻¹ := inv_pos.mpr hr
  have hS : F ⁻¹' ball (0 : Point) 2 = ball (0 : Point) (2*r) := by
    ext x
    exact (affineBall_mem_ball_iff 0 0 ht 2 x).trans (by rw [div_inv_eq_mul])
  have hK : K = r ^ (-s) • (K ∘ F) := by
    funext x
    simp only [F, Function.comp_apply, sub_zero, zero_add, Pi.smul_apply, smul_eq_mul]
    dsimp only [K]
    rw [poissonInversePower_smul s ht.le, Real.inv_rpow hr.le, Real.rpow_neg hr.le, inv_inv, ← mul_assoc,
      inv_mul_cancel₀ (Real.rpow_pos_of_pos hr _).ne', one_mul]
  change (eLpNorm K poissonL4Conjugate (volume.restrict (ball (0 : Point) (2*r)))).toReal = _
  conv_lhs => rw [hK]
  rw [eLpNorm_const_smul, ← hS, eLpNorm_affine_preimage _ _ ht _ ENNReal.ofReal_ne_top K,
    ← ofReal_norm, Real.norm_of_nonneg (Real.rpow_nonneg hr.le _),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hr.le _), ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity), inv_pow, inv_inv, poissonL4Conjugate_div_toReal]
  rw [← Real.rpow_natCast_mul hr.le]
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) * (3 / 4) = 9 / 4 by norm_num]
  rw [← mul_assoc, ← Real.rpow_add hr]
  rw [show -s + 9 / 4 = 9 / 4 - s by ring]

/-- All possible translated Newton kernels on the closed ball have the
same local (L^{4/3}) estimate, with the exact dilation exponent. -/
theorem exists_poissonInversePower_conjugate_bound (s : ℝ) (hs : s < 9 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c x : Point) (r : ℝ), 0 < r → x ∈ closedBall c r →
      MemLp (fun y => poissonInversePower s (x-y)) poissonL4Conjugate (volume.restrict (ball c r)) ∧
      (eLpNorm (fun y => poissonInversePower s (x-y)) poissonL4Conjugate (volume.restrict (ball c r))).toReal ≤
        C * r ^ (9 / 4 - s) := by
  let K := poissonInversePower s
  let C := (eLpNorm K poissonL4Conjugate (volume.restrict (ball (0 : Point) 2))).toReal
  refine ⟨C, ENNReal.toReal_nonneg, ?_⟩
  intro c x r hr hx
  let F (y : Point) := x-y
  let S := ball (0 : Point) (2*r)
  have hF : MeasurePreserving F volume volume := (volume : Measure Point).measurePreserving_sub_left x
  have hInto : ball c r ⊆ F ⁻¹' S := by
    intro y hy
    change x-y ∈ ball (0 : Point) (2*r)
    rw [mem_ball_zero_iff, ← dist_eq_norm]
    have ht := dist_triangle x c y
    rw [dist_comm c y] at ht
    exact ht.trans_lt (by linarith only [mem_closedBall.1 hx, mem_ball.1 hy])
  have hDom : Measure.map F (volume.restrict (ball c r)) ≤ (1 : ℝ≥0∞) • volume.restrict S := by
    rw [one_smul]
    exact (Measure.map_mono (Measure.restrict_mono_set volume hInto) hF.measurable).trans_eq
      (hF.restrict_preimage measurableSet_ball).map_eq
  have hK := poissonInversePower_memLp_conjugate_radius s hs hr
  have hMeas : AEMeasurable F (volume.restrict (ball c r)) := hF.measurable.aemeasurable
  refine ⟨memLp_comp_of_map_le_smul hMeas ENNReal.one_ne_top hDom hK, ?_⟩
  have hL := eLpNorm_comp_le_of_map_le_smul (p := poissonL4Conjugate) hMeas hDom hK.aestronglyMeasurable
  rw [ENNReal.one_rpow, one_mul] at hL
  exact (ENNReal.toReal_mono hK.eLpNorm_ne_top hL).trans_eq
    ((poissonInversePower_conjugate_radius_eq s hr).trans (mul_comm _ _))

/-- The (L^p) product estimate in real norms, expressed in the actual
Lebesgue classes consumed by the local Poisson estimates. -/
theorem integral_norm_mul_le_realLp_mul {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F] {μ : Measure X}
    {p q : ℝ} (hpq : p.HolderConjugate q) {f : X → E} {g : X → F}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal q) μ) :
    (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ≤
      (eLpNorm f (ENNReal.ofReal p) μ).toReal * (eLpNorm g (ENNReal.ofReal q) μ).toReal := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun _ => norm_nonneg _)
    hf.norm hg.norm
  have he₁ := hf.eLpNorm_eq_integral_rpow_norm
    (ENNReal.ofReal_ne_zero_iff.mpr hpq.pos) ENNReal.ofReal_ne_top
  have he₂ := hg.eLpNorm_eq_integral_rpow_norm
    (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos) ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hpq.nonneg] at he₁
  rw [ENNReal.toReal_ofReal hpq.symm.nonneg] at he₂
  rw [he₁, he₂, ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _)]
  simpa only [one_div] using h

end Thesis

end
