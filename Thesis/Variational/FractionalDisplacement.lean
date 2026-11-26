module

public import Thesis.Variational.SobolevDisplacement
import Thesis.Variational.FractionalL2Duality
import HarmonicMaps.Analysis.AffineBallMeasure
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Displacement characterization and exact scaling of the fractional translation kernel. -/

@[expose] public section

noncomputable section

open Function MeasureTheory Metric Set
open scoped ENNReal NNReal Matrix.Norms.Frobenius

namespace Thesis

private theorem nonlocal_fractionalEnergy_eq_displacements_of_measurable
    {U : Set Point} (hU : IsBoundedDomain U) (s : ℝ) {u : Point → S0} (hu : StronglyMeasurable u) :
    (∫⁻ x in U, ∫⁻ y in U, ENNReal.ofReal (‖u x - u y‖ ^ 2 / dist x y ^ (3 + 2*s))) =
      ∫⁻ z in ball (0 : Point) (diam U + 1),
        restrictedTranslationEnergy U u z * ENNReal.ofReal ((‖z‖ ^ (3+2*s))⁻¹) := by
  let V := ball (0 : Point) (diam U + 1)
  let μ := volume.restrict U
  let N (x y : Point) := ENNReal.ofReal (‖u x-u y‖ ^ 2 / dist x y ^ (3+2*s))
  let W (z : Point) := ENNReal.ofReal ((‖z‖ ^ (3+2*s))⁻¹)
  let F (x z : Point) := ENNReal.ofReal (‖u (x+z)-u x‖ ^ 2) * W z
  let H (x z : Point) := (U.indicator (N x)) (x+z)
  have hEq (x z : Point) : N x (x+z) = F x z := by
    have hd : dist x (x+z) = ‖z‖ := by rw [dist_comm,dist_eq_norm,add_sub_cancel_left]
    dsimp only [N,F,W]
    rw [hd,norm_sub_rev (u x),div_eq_mul_inv,ENNReal.ofReal_mul (sq_nonneg _)]
  have hShift (x : Point) (hx : x ∈ U) : (∫⁻ y in U, N x y) = ∫⁻ z in V, H x z := by
    rw [← lintegral_indicator hU.1.measurableSet,← lintegral_indicator measurableSet_ball]
    have hTrans : (∫⁻ z : Point, (U.indicator (N x)) (x+z)) = ∫⁻ z : Point, U.indicator (N x) z := by
      simpa only [add_comm x] using lintegral_add_right_eq_self (μ := (volume : Measure Point))
        (U.indicator (N x)) x
    rw [← hTrans]
    apply lintegral_congr
    intro z
    by_cases hz : z ∈ V
    · rw [indicator_of_mem hz]
    · have hzU : x+z ∉ U := by
        intro hy
        have hd : dist x (x+z) = ‖z‖ := by rw [dist_comm,dist_eq_norm,add_sub_cancel_left]
        have hR := dist_le_diam_of_mem hU.2.2 hx hy
        rw [hd] at hR
        exact hz (mem_ball_zero_iff.mpr (hR.trans_lt (lt_add_of_pos_right _ zero_lt_one)))
      rw [indicator_of_notMem hz]
      change U.indicator (N x) (x+z) = 0
      rw [indicator_of_notMem hzU]
  have hH : Measurable (Function.uncurry H) := by
    have hCo : Measurable (fun p : Point × Point => N p.1 (p.1+p.2)) := by
      have hA : StronglyMeasurable (fun p : Point × Point => u p.1 - u (p.1+p.2)) :=
        (hu.comp_measurable measurable_fst).sub (hu.comp_measurable (measurable_fst.add measurable_snd))
      have hB : Measurable (fun p : Point × Point => dist p.1 (p.1+p.2) ^ (3+2*s)) := by fun_prop
      exact ENNReal.measurable_ofReal.comp ((hA.norm.measurable.pow_const (2 : ℕ)).div hB)
    let T : Set (Point × Point) := (fun p : Point × Point => p.1+p.2) ⁻¹' U
    have hT : MeasurableSet T := hU.1.measurableSet.preimage (measurable_fst.add measurable_snd)
    have hFun : Function.uncurry H =
        T.indicator (fun p : Point × Point => N p.1 (p.1+p.2)) := by
      funext p
      change U.indicator (N p.1) (p.1+p.2) = T.indicator (fun p => N p.1 (p.1+p.2)) p
      by_cases hp : p.1+p.2 ∈ U
      · rw [indicator_of_mem hp,indicator_of_mem (show p ∈ T from hp)]
      · rw [indicator_of_notMem hp,indicator_of_notMem (show p ∉ T from hp)]
    rw [hFun]
    exact hCo.indicator hT
  have hInner (z : Point) :
      (∫⁻ x, H x z ∂μ) = restrictedTranslationEnergy U u z * W z := by
    let T := (fun x : Point => x+z) ⁻¹' U
    have hT : MeasurableSet T := hU.1.measurableSet.preimage (measurable_id.add measurable_const)
    have hFun : (fun x => H x z) = T.indicator (fun x => F x z) := by
      funext x
      by_cases hx : x+z ∈ U
      · change U.indicator (N x) (x+z) = T.indicator (fun x => F x z) x
        rw [indicator_of_mem hx,indicator_of_mem (show x ∈ T from hx),hEq]
      · change U.indicator (N x) (x+z) = T.indicator (fun x => F x z) x
        rw [indicator_of_notMem hx,indicator_of_notMem (show x ∉ T from hx)]
    have hM : Measurable (fun x => ENNReal.ofReal (‖u (x+z)-u x‖ ^ 2)) :=
      ENNReal.measurable_ofReal.comp (((hu.comp_measurable (measurable_id.add measurable_const)).sub hu).norm.measurable.pow_const _)
    rw [hFun,lintegral_indicator hT,show μ.restrict T = volume.restrict (translationIntersection U z) by
      dsimp only [μ]
      rw [Measure.restrict_restrict hT,translationIntersection,inter_comm]]
    exact lintegral_mul_const (W z) hM
  calc
    _ = ∫⁻ x in U, ∫⁻ z in V, H x z :=
      setLIntegral_congr_fun hU.1.measurableSet hShift
    _ = ∫⁻ z in V, ∫⁻ x, H x z ∂μ := lintegral_lintegral_swap hH.aemeasurable
    _ = _ := by simp_rw [hInner]; rfl

/-- The intrinsic fractional energy is bounded by integrating any
pointwise majorant for the squared restricted translations. -/
theorem fractionalEnergy_le_of_restrictedTranslationEnergy_bound
    {U : Set Point} (hU : IsBoundedDomain U) (s : ℝ) {u : Point → S0}
    (hu : MemLp u 2 (volume.restrict U)) (K : Point → ℝ≥0∞)
    (hK : ∀ z ∈ ball (0 : Point) (diam U + 1), restrictedTranslationEnergy U u z ≤ K z) :
    fractionalEnergy s U u ≤ eLpNorm u 2 (volume.restrict U) ^ 2 +
      ∫⁻ z in ball (0 : Point) (diam U + 1), K z * ENNReal.ofReal ((‖z‖ ^ (3+2*s))⁻¹) := by
  let v := hu.aestronglyMeasurable.mk u
  have huv : u =ᵐ[volume.restrict U] v := hu.aestronglyMeasurable.ae_eq_mk
  have hv : StronglyMeasurable v := hu.aestronglyMeasurable.stronglyMeasurable_mk
  rw [fractionalEnergy_congr_ae huv,eLpNorm_congr_ae huv]
  unfold fractionalEnergy
  rw [← eLpNorm_two_sq_eq_tensor_lintegral,
    nonlocal_fractionalEnergy_eq_displacements_of_measurable hU s hv]
  exact add_le_add_right (setLIntegral_mono' measurableSet_ball fun z hz =>
    mul_le_mul_left ((restrictedTranslationEnergy_congr_ae huv z).symm.le.trans (hK z hz)) _) _

/-- The radial kernel that encodes the minimum of the (L^2) and
first-derivative translation estimates. -/
def fractionalTranslationKernel (s μ : ℝ) (z : Point) : ℝ :=
  min (‖z‖ ^ (2 : ℕ)) μ / ‖z‖ ^ (3+2*s)

theorem fractionalTranslationKernel_measurable (s μ : ℝ) :
    Measurable (fractionalTranslationKernel s μ) := by
  unfold fractionalTranslationKernel
  fun_prop

theorem fractionalTranslationKernel_nonneg (s : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) (z : Point) :
    0 ≤ fractionalTranslationKernel s μ z :=
  div_nonneg (le_min (sq_nonneg _) hμ) (Real.rpow_nonneg (norm_nonneg _) _)

private theorem integrable_fractionalTranslationKernel_unit (s : ℝ)
    (hs : 0 < s) (hs₁ : s < 1) : Integrable (fractionalTranslationKernel s 1) volume := by
  let f (r : ℝ) := min (r ^ (2 : ℕ)) (1 : ℝ) / r ^ (3+2*s)
  change Integrable (f ‖·‖) (volume : Measure Point)
  apply (integrable_fun_norm_addHaar (volume : Measure Point)).2
  have hDim : Module.finrank ℝ Point - 1 = 2 := by simp [Point]
  rw [hDim]
  let g (r : ℝ) := r ^ (2 : ℕ) * f r
  change IntegrableOn g (Ioi (0 : ℝ))
  have h0 : IntegrableOn g (Ioc (0 : ℝ) 1) := by
    apply (integrableOn_Ioc_iff_integrableOn_Ioo (by finiteness)).2
    have hI : IntegrableOn (fun r : ℝ => r ^ (1-2*s)) (Ioo (0 : ℝ) 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith only [hs₁])
    refine hI.congr_fun (fun r hr => ?_) measurableSet_Ioo
    symm
    have hr0 : 0 < r := hr.1
    dsimp only [g,f]
    rw [min_eq_left (pow_le_one₀ hr0.le hr.2.le), ← mul_div_assoc, ← pow_add, ← Real.rpow_natCast,
      ← Real.rpow_sub hr0]
    congr 1
    push_cast
    ring
  have h1 : IntegrableOn g (Ioi (1 : ℝ)) := by
    have hI : IntegrableOn (fun r : ℝ => r ^ (-1-2*s)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith only [hs]) zero_lt_one
    refine hI.congr_fun (fun r hr => ?_) measurableSet_Ioi
    symm
    have hr0 : 0 < r := zero_lt_one.trans hr
    dsimp only [g,f]
    rw [min_eq_right (one_le_pow₀ hr.le), mul_one_div, ← Real.rpow_natCast,← Real.rpow_sub hr0]
    congr 1
    push_cast
    ring
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact h0.union h1

private theorem fractionalTranslationKernel_scale (s : ℝ) {a : ℝ} (ha : 0 < a) (z : Point) :
    fractionalTranslationKernel s (a ^ 2) (a • z) =
      a ^ (-1-2*s) * fractionalTranslationKernel s 1 z := by
  by_cases hz : z = 0
  · subst z
    simp only [smul_zero,fractionalTranslationKernel,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),
      min_eq_left (sq_nonneg a),min_eq_left zero_le_one,zero_div,mul_zero]
  have hN : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hMin : min ((a*‖z‖)^2) (a^2) = a^2 * min (‖z‖^2) (1 : ℝ) := by
    rw [mul_pow]
    by_cases h : ‖z‖ ^ 2 ≤ 1
    · have H : a ^ 2 * ‖z‖ ^ 2 ≤ a ^ 2 := by
        exact (mul_le_mul_of_nonneg_left h (sq_nonneg a)).trans_eq (mul_one _)
      rw [min_eq_left H, min_eq_left h]
    · have H : a ^ 2 ≤ a ^ 2 * ‖z‖ ^ 2 := le_mul_of_one_le_right (sq_nonneg _) (not_le.mp h).le
      rw [min_eq_right H,min_eq_right (not_le.mp h).le,mul_one]
  unfold fractionalTranslationKernel
  rw [norm_smul,Real.norm_of_nonneg ha.le,hMin,Real.mul_rpow ha.le hN.le,mul_div_mul_comm]
  have hPow : a^2 / a^(3+2*s) = a^(-1-2*s) := by
    rw [← Real.rpow_natCast,← Real.rpow_sub ha]
    congr 1
    push_cast
    ring
  rw [hPow]

/-- The full displacement integral scales by the exact spectral mass power. -/
theorem exists_fractionalTranslationKernel_integral (s : ℝ) (hs : 0 < s) (hs₁ : s < 1) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ μ : ℝ, 0 < μ →
      (∫⁻ z : Point, ENNReal.ofReal (fractionalTranslationKernel s μ z)) =
        C * ENNReal.ofReal (μ ^ (1-s)) := by
  let C := ∫⁻ z : Point, ENNReal.ofReal (fractionalTranslationKernel s 1 z)
  have hC : C < ⊤ := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fractionalTranslationKernel_nonneg s zero_le_one))).1
      (integrable_fractionalTranslationKernel_unit s hs hs₁).2
  refine ⟨C,hC,?_⟩
  intro μ hμ
  let a := Real.sqrt μ
  have ha : 0 < a := Real.sqrt_pos.2 hμ
  have haμ : a^2 = μ := Real.sq_sqrt hμ.le
  have hMap : Measure.map (fun z : Point => a•z) volume = ENNReal.ofReal ((a^3)⁻¹) • volume := by
    simpa only [zero_add,sub_zero] using HarmonicMaps.affineBall_map_volume (n := 3) 0 0 ha
  let K (z : Point) := ENNReal.ofReal (fractionalTranslationKernel s μ z)
  have hK : Measurable K := ENNReal.measurable_ofReal.comp (fractionalTranslationKernel_measurable _ _)
  have hChange : (∫⁻ z : Point, K (a•z)) = ENNReal.ofReal ((a^3)⁻¹) * ∫⁻ z, K z := by
    rw [← lintegral_map hK (by fun_prop : Measurable (fun z : Point => a•z)), hMap,lintegral_smul_measure,smul_eq_mul]
  have hFact (z : Point) : K (a•z) =
      ENNReal.ofReal (a ^ (-1-2*s)) * ENNReal.ofReal (fractionalTranslationKernel s 1 z) := by
    dsimp only [K]
    rw [← haμ,fractionalTranslationKernel_scale s ha,ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]
  calc
    _ = ENNReal.ofReal (a^3) * (∫⁻ z : Point, K (a•z)) := by
      rw [hChange, ← mul_assoc,← ENNReal.ofReal_mul (pow_nonneg ha.le _),mul_inv_cancel₀ (pow_ne_zero _ ha.ne'),
        ENNReal.ofReal_one,one_mul]
    _ = ENNReal.ofReal (a^3) * (ENNReal.ofReal (a^(-1-2*s)) * C) := by
      simp_rw [hFact]
      apply congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal (a^3) * x)
      have hM : Measurable (fun z => ENNReal.ofReal (fractionalTranslationKernel s 1 z)) :=
        ENNReal.measurable_ofReal.comp (fractionalTranslationKernel_measurable s 1)
      exact lintegral_const_mul'' _ hM.aemeasurable
    _ = _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul (pow_nonneg ha.le _)]
      have hPower : a^3 * a^(-1-2*s) = μ^(1-s) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add ha, ← haμ,
          ← Real.rpow_natCast_mul ha.le]
        congr 1
        push_cast
        ring
      rw [hPower,mul_comm]

end Thesis
