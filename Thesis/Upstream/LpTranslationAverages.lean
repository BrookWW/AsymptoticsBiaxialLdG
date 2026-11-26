module

public import Thesis.Definitions
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Prod

/-! Contraction of (L^p) under probability averages of translations. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace Thesis

private theorem rpow_norm_integral_le_integral_rpow_norm {T E : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure T} [IsProbabilityMeasure μ] {f : T → E} (hf : Integrable f μ)
    {p : ℝ} (hp : 1 ≤ p) (hfp : Integrable (fun t => ‖f t‖^p) μ) :
    ‖∫ t, f t ∂μ‖^p ≤ ∫ t, ‖f t‖^p ∂μ := by
  have hN := norm_integral_le_integral_norm (μ := μ) f
  have hJ := (convexOn_rpow hp).map_integral_le (Real.continuous_rpow_const (zero_le_one.trans hp)).continuousOn
    isClosed_Ici (Eventually.of_forall fun _ => norm_nonneg _) hf.norm hfp
  exact (Real.rpow_le_rpow (norm_nonneg _) hN (zero_le_one.trans hp)).trans hJ

/-- The norm of a probability average is bounded by a uniform norm of its slices. -/
theorem memLp_parameterAverage_le {T E : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure T) [IsProbabilityMeasure μ]
    {P : Point → T → E} (hP : StronglyMeasurable (Function.uncurry P)) {p : ℝ} (hp : 1 ≤ p)
    {R : ℝ≥0∞} (hR : R ≠ ⊤) (hSlice : ∀ᵐ t ∂μ,
      eLpNorm (fun x => P x t) (ENNReal.ofReal p) (volume : Measure Point) ≤ R) :
    MemLp (fun x => ∫ t, P x t ∂μ) (ENNReal.ofReal p) (volume : Measure Point) ∧
      eLpNorm (fun x => ∫ t, P x t ∂μ) (ENNReal.ofReal p) volume ≤ R := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have hpN : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp₀).ne'
  let F (x : Point) (t : T) := ‖P x t‖ₑ^p
  have hF : Measurable (Function.uncurry F) := hP.enorm.pow_const p
  have hMass : (∫⁻ x, ∫⁻ t, F x t ∂μ) ≤ R^p := by
    rw [lintegral_lintegral_swap (μ := volume) (ν := μ) (f := F) hF.aemeasurable]
    have hE : ∀ᵐ t ∂μ, (∫⁻ x, F x t) ≤ R^p := by
      filter_upwards [hSlice] with t ht
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpN ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hp₀.le,one_div] at ht
      exact (ENNReal.rpow_inv_le_iff hp₀).1 ht
    exact (lintegral_mono_ae hE).trans_eq (by simp)
  have hFinite : (∫⁻ x, ∫⁻ t, F x t ∂μ) < ⊤ :=
    hMass.trans_lt (ENNReal.rpow_lt_top_of_nonneg hp₀.le hR)
  have hPt : ∀ᵐ x ∂(volume : Measure Point), ‖∫ t, P x t ∂μ‖ₑ^p ≤ ∫⁻ t, F x t ∂μ := by
    have hOuter : Measurable (fun x => ∫⁻ t, F x t ∂μ) := hF.lintegral_prod_right'
    filter_upwards [ae_lt_top hOuter hFinite.ne] with x hx
    have hMeas : StronglyMeasurable (P x) := hP.comp_measurable (measurable_const.prodMk measurable_id)
    have hPL : MemLp (P x) (ENNReal.ofReal p) μ := by
      refine ⟨hMeas.aestronglyMeasurable,?_⟩
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpN ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hp₀.le]
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hx.ne
    have hI : Integrable (P x) μ := hPL.integrable (by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    have hI' : Integrable (fun t => ‖P x t‖^p) μ := by
      simpa only [ENNReal.toReal_ofReal hp₀.le] using hPL.integrable_norm_rpow hpN ENNReal.ofReal_ne_top
    have he (w : E) : ‖w‖ₑ^p = ENNReal.ofReal (‖w‖^p) := by
      rw [← ofReal_norm,ENNReal.ofReal_rpow_of_nonneg (norm_nonneg w) hp₀.le]
    change ‖∫ t, P x t ∂μ‖ₑ^p ≤ ∫⁻ t, ‖P x t‖ₑ^p ∂μ
    simp_rw [he]
    rw [← ofReal_integral_eq_lintegral_ofReal hI'
      (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)]
    exact ENNReal.ofReal_le_ofReal (rpow_norm_integral_le_integral_rpow_norm hI hp hI')
  have hBound : eLpNorm (fun x => ∫ t, P x t ∂μ) (ENNReal.ofReal p) volume ≤ R := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpN ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp₀.le,one_div]
    exact (ENNReal.rpow_inv_le_iff hp₀).2 ((lintegral_mono_ae hPt).trans hMass)
  exact ⟨⟨(hP.integral_prod_right (ν := μ)).aestronglyMeasurable,hBound.trans_lt hR.lt_top⟩,hBound⟩

/-- Probability translation averages preserve (L^p) with operator norm at most one. -/
theorem memLp_translationAverage_le {T E : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure T) [IsProbabilityMeasure μ]
    {θ : T → Point} (hθ : Measurable θ) {f : Point → E} (hf : StronglyMeasurable f)
    {p : ℝ} (hp : 1 ≤ p) (hfLp : MemLp f (ENNReal.ofReal p) (volume : Measure Point)) :
    MemLp (fun x => ∫ t, f (x+θ t) ∂μ) (ENNReal.ofReal p) (volume : Measure Point) ∧
      eLpNorm (fun x => ∫ t, f (x+θ t) ∂μ) (ENNReal.ofReal p) volume ≤
        eLpNorm f (ENNReal.ofReal p) volume := by
  refine memLp_parameterAverage_le μ ?_ hp hfLp.eLpNorm_ne_top ?_
  · exact hf.comp_measurable (measurable_fst.add (hθ.comp measurable_snd))
  · apply Eventually.of_forall
    intro t
    exact (eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
      (measurePreserving_add_right volume (θ t))).le

/-- Averaging a bounded strongly measurable function against a probability
of translation vectors contracts its real (L^p) seminorm. -/
theorem eLpNorm_translationAverage_le {T E : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure T) [IsProbabilityMeasure μ]
    {θ : T → Point} (hθ : Measurable θ) {f : Point → E} (hf : StronglyMeasurable f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x => ∫ t, f (x+θ t) ∂μ) (ENNReal.ofReal p) volume ≤
      eLpNorm f (ENNReal.ofReal p) volume := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have hpN : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp₀).ne'
  let F (x : Point) (t : T) := ENNReal.ofReal (‖f (x+θ t)‖^p)
  have hF : Measurable (Function.uncurry F) := by
    have hP : Measurable (fun z : Point × T => z.1+θ z.2) := measurable_fst.add (hθ.comp measurable_snd)
    exact ((hf.comp_measurable hP).norm.measurable.pow_const p).ennreal_ofReal
  have hPt (x : Point) : ENNReal.ofReal (‖∫ t, f (x+θ t) ∂μ‖^p) ≤ ∫⁻ t, F x t ∂μ := by
    have hG : StronglyMeasurable (fun t => f (x+θ t)) := hf.comp_measurable (measurable_const.add hθ)
    have hI : Integrable (fun t => f (x+θ t)) μ :=
      Integrable.of_bound hG.aestronglyMeasurable M (Eventually.of_forall fun t => hM (x+θ t))
    have hPow : StronglyMeasurable (fun t => ‖f (x+θ t)‖^p) :=
      (Real.continuous_rpow_const hp₀.le).comp_stronglyMeasurable hG.norm
    have hI' : Integrable (fun t => ‖f (x+θ t)‖^p) μ :=
      Integrable.of_bound hPow.aestronglyMeasurable (M^p) (Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact Real.rpow_le_rpow (norm_nonneg _) (hM (x+θ t)) hp₀.le)
    change ENNReal.ofReal (‖∫ t, f (x+θ t) ∂μ‖^p) ≤ ∫⁻ t, ENNReal.ofReal (‖f (x+θ t)‖^p) ∂μ
    rw [← ofReal_integral_eq_lintegral_ofReal hI' (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)]
    exact ENNReal.ofReal_le_ofReal (rpow_norm_integral_le_integral_rpow_norm hI hp hI')
  have hInt : (∫⁻ x, ∫⁻ t, F x t ∂μ) = ∫⁻ x, ENNReal.ofReal (‖f x‖^p) := by
    rw [lintegral_lintegral_swap (μ := volume) (ν := μ) (f := F) hF.aemeasurable]
    have hEq (t : T) : (∫⁻ x, F x t) = ∫⁻ x, ENNReal.ofReal (‖f x‖^p) :=
      (measurePreserving_add_right volume (θ t)).lintegral_comp ((hf.norm.measurable.pow_const p).ennreal_ofReal)
    simp only [hEq,lintegral_const,measure_univ,mul_one]
  repeat rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpN ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hp₀.le]
  apply ENNReal.rpow_le_rpow _ (div_nonneg zero_le_one hp₀.le)
  have hEq (w : E) : ‖w‖ₑ^p = ENNReal.ofReal (‖w‖^p) := by
    rw [← ofReal_norm,ENNReal.ofReal_rpow_of_nonneg (norm_nonneg w) hp₀.le]
  simp_rw [hEq]
  exact (lintegral_mono hPt).trans_eq hInt

/-- A nonnegative Lebesgue kernel of mass one gives the same contraction. -/
theorem eLpNorm_probabilityKernelConvolution_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k : Point → ℝ}
    (hk : Measurable k) (hk₀ : ∀ x, 0 ≤ k x) (hki : Integrable k) (hk₁ : (∫ x, k x)=1)
    {f : Point → E} (hf : StronglyMeasurable f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x => ∫ t, k t • f (x-t)) (ENNReal.ofReal p) volume ≤
      eLpNorm f (ENNReal.ofReal p) volume := by
  let μ := volume.withDensity (fun t : Point => ENNReal.ofReal (k t))
  letI : IsProbabilityMeasure μ := ⟨by
    dsimp only [μ]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hki (Eventually.of_forall hk₀),hk₁,ENNReal.ofReal_one]⟩
  have h := eLpNorm_translationAverage_le μ (θ := Neg.neg) measurable_neg hf hM hp
  refine (le_of_eq ?_).trans h
  apply congrArg (fun g : Point → E => eLpNorm g (ENNReal.ofReal p) volume)
  funext x
  dsimp only [μ]
  rw [integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hk₀ _),sub_eq_add_neg]

end Thesis

end
