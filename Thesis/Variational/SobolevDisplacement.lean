module

public import Thesis.Variational.SmoothDomainQuantitativeExtension
import Thesis.Variational.H10FractionalEmbedding
import Thesis.Upstream.MinimizingSobolev
import StratificationTheory.Compactness.SobolevTranslationBound
import HarmonicMaps.Analysis.VariableMollificationL2

/-! Translation estimates retaining both points of the actual smooth domain. -/

@[expose] public section

noncomputable section

open Filter Function HarmonicMaps MeasureTheory Metric Set Topology
open scoped ENNReal NNReal Matrix.Norms.Frobenius

namespace Thesis

local instance displacementTensorENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

/-- Original points whose translates also belong to the domain. -/
def translationIntersection (U : Set Point) (z : Point) : Set Point :=
  U ∩ (fun x => x + z) ⁻¹' U

/-- The squared translation error, integrated only over pairs in the domain. -/
def restrictedTranslationEnergy (U : Set Point) (u : Point → S0) (z : Point) : ℝ≥0∞ :=
  ∫⁻ x in translationIntersection U z, ENNReal.ofReal (‖u (x + z) - u x‖ ^ 2)

private theorem measurePreserving_add_right_restrict_preimage (U : Set Point) (z : Point) :
    MeasurePreserving (fun x : Point => x + z)
      (volume.restrict ((fun x : Point => x + z) ⁻¹' U)) (volume.restrict U) :=
  (measurePreserving_add_right (volume : Measure Point) z).restrict_preimage_emb
    (Homeomorph.addRight z).isClosedEmbedding.measurableEmbedding U

private theorem translate_ae_eq_on_intersection {U : Set Point} (z : Point)
    {u v : Point → S0} (h : u =ᵐ[volume.restrict U] v) :
    (fun x => u (x + z)) =ᵐ[volume.restrict (translationIntersection U z)]
      (fun x => v (x + z)) := by
  have h' := (measurePreserving_add_right_restrict_preimage U z).quasiMeasurePreserving.ae h
  exact h'.filter_mono (ae_mono (Measure.restrict_mono_set volume inter_subset_right))

/-- A translation budget is independent of the choice of map representative. -/
theorem restrictedTranslationEnergy_congr_ae {U : Set Point} {u v : Point → S0}
    (h : u =ᵐ[volume.restrict U] v) (z : Point) :
    restrictedTranslationEnergy U u z = restrictedTranslationEnergy U v z := by
  apply lintegral_congr_ae
  filter_upwards [translate_ae_eq_on_intersection z h,
    h.filter_mono (ae_mono (Measure.restrict_mono_set volume inter_subset_left))] with x hx hy
  rw [hx,hy]

private theorem memLp_translated_on_intersection {U : Set Point} (z : Point)
    {u : Point → S0} (hu : MemLp u 2 (volume.restrict U)) :
    MemLp (fun x => u (x + z)) 2 (volume.restrict (translationIntersection U z)) :=
  (hu.comp_measurePreserving (measurePreserving_add_right_restrict_preimage U z)).mono_measure
    (Measure.restrict_mono_set volume inter_subset_right)

private theorem square_norm_add_le {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a+b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2).trans
    (by nlinarith only [sq_nonneg (‖a‖ - ‖b‖)])

/-- A sum can be split into its two translation budgets at the original points. -/
theorem restrictedTranslationEnergy_add_le {U : Set Point} {u v : Point → S0} (z : Point)
    (hu : MemLp u 2 (volume.restrict U)) (hv : MemLp v 2 (volume.restrict U)) :
    restrictedTranslationEnergy U (u+v) z ≤
      2 * (restrictedTranslationEnergy U u z + restrictedTranslationEnergy U v z) := by
  let μ := volume.restrict (translationIntersection U z)
  let a (x : Point) := ENNReal.ofReal (‖u (x+z)-u x‖ ^ 2)
  let b (x : Point) := ENNReal.ofReal (‖v (x+z)-v x‖ ^ 2)
  have hμ := Measure.restrict_mono_set (volume : Measure Point) (show translationIntersection U z ⊆ U from inter_subset_left)
  have ha : AEMeasurable a μ := ENNReal.measurable_ofReal.comp_aemeasurable
    (((memLp_translated_on_intersection z hu).sub (hu.mono_measure hμ)).1.norm.aemeasurable.pow_const _)
  have hb : AEMeasurable b μ := ENNReal.measurable_ofReal.comp_aemeasurable
    (((memLp_translated_on_intersection z hv).sub (hv.mono_measure hμ)).1.norm.aemeasurable.pow_const _)
  calc
    _ ≤ ∫⁻ x, 2 * (a x + b x) ∂μ := by
      apply lintegral_mono
      intro x
      have h : (u+v) (x+z) - (u+v) x = (u (x+z)-u x) + (v (x+z)-v x) := by
        simp only [Pi.add_apply]; abel
      simp only [h,a,b,← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      exact (ENNReal.ofReal_le_ofReal (square_norm_add_le (u (x+z)-u x) (v (x+z)-v x))).trans_eq
        (by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat])
    _ = _ := by
      change (∫⁻ x, 2 * (a+b) x ∂μ) = _
      rw [lintegral_const_mul'' _ (ha.add hb)]
      simp only [Pi.add_apply, lintegral_add_left' ha]
      rfl

/-- A pure (L^2) bound controls the cropped translation budget. -/
theorem restrictedTranslationEnergy_le_L2 {U : Set Point} {u : Point → S0} (z : Point)
    (hu : MemLp u 2 (volume.restrict U)) :
    restrictedTranslationEnergy U u z ≤ 4 * eLpNorm u 2 (volume.restrict U) ^ 2 := by
  let μ := volume.restrict (translationIntersection U z)
  let a (x : Point) := ENNReal.ofReal (‖u (x+z)‖ ^ 2)
  let b (x : Point) := ENNReal.ofReal (‖u x‖ ^ 2)
  have hμ := Measure.restrict_mono_set (volume : Measure Point) (show translationIntersection U z ⊆ U from inter_subset_left)
  have ha : AEMeasurable a μ := ENNReal.measurable_ofReal.comp_aemeasurable
    ((memLp_translated_on_intersection z hu).1.norm.aemeasurable.pow_const (2 : ℕ))
  have hb : AEMeasurable b μ := ENNReal.measurable_ofReal.comp_aemeasurable
    ((hu.mono_measure hμ).1.norm.aemeasurable.pow_const (2 : ℕ))
  have h1 : (∫⁻ x, a x ∂μ) ≤ eLpNorm u 2 (volume.restrict U) ^ 2 := by
    let τ : Point → Point := fun x => x + z
    have he : MeasurableEmbedding τ := (Homeomorph.addRight z).isClosedEmbedding.measurableEmbedding
    have hs := measurePreserving_add_right_restrict_preimage U z
    calc
      _ ≤ ∫⁻ x in τ ⁻¹' U, a x :=
        lintegral_mono' (Measure.restrict_mono_set volume inter_subset_right) le_rfl
      _ = ∫⁻ x in U, b x := hs.lintegral_comp_emb he b
      _ = _ := (eLpNorm_two_sq_eq_tensor_lintegral _ _).symm
  have h2 : (∫⁻ x, b x ∂μ) ≤ eLpNorm u 2 (volume.restrict U) ^ 2 := by
    rw [eLpNorm_two_sq_eq_tensor_lintegral]
    exact lintegral_mono' hμ le_rfl
  calc
    _ ≤ ∫⁻ x, 2 * (a x + b x) ∂μ := by
      apply lintegral_mono
      intro x
      have h := square_norm_add_le (u (x+z)) (-(u x))
      rw [← sub_eq_add_neg,norm_neg] at h
      simp only [a,b,← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      exact (ENNReal.ofReal_le_ofReal h).trans_eq
        (by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat])
    _ ≤ 2 * (eLpNorm u 2 (volume.restrict U) ^ 2 + eLpNorm u 2 (volume.restrict U) ^ 2) := by
      change (∫⁻ x, 2 * (a+b) x ∂μ) ≤ _
      rw [lintegral_const_mul'' _ (ha.add hb)]
      simp only [Pi.add_apply, lintegral_add_left' ha]
      exact mul_le_mul_right (add_le_add h1 h2) _
    _ = _ := by rw [← two_mul,← mul_assoc]; norm_num

private theorem ball_translationEnergy_le_graph_norm
    {R R' : ℝ} (hR' : 0 < R') {z : Point} (hz : R + ‖z‖ < R')
    {w : Point → S0} {D : Point → Thesis.Gradient}
    (hw : MemH1 (ball (0 : Point) R') w D) :
    (∫⁻ x in ball (0 : Point) R, ENNReal.ofReal (‖w (x+z) - w x‖ ^ 2)) ≤
      ENNReal.ofReal (3 * ‖z‖ ^ 2 * ‖(hw.1.toLp w,fun i => (hw.2.1 i).toLp (fun x => D x i))‖ ^ 2) := by
  let W := ball (0 : Point) R'
  let B := ball (0 : Point) R
  let P : H1Graph W := (hw.1.toLp w,fun i => (hw.2.1 i).toLp (fun x => D x i))
  have hN : MemW12 (ballDomain (0 : Point) R') (frobeniusField w) (frobeniusGradient D) :=
    (memH1_iff_memW12 (ballDomain (0 : Point) R') _ _).mp hw
  have hR := StratificationTheory.Compactness.memW12_translation_L2_square_le
    (0 : Point) hR' z hz hN
  have hShift : B ⊆ (fun x : Point => x+z) ⁻¹' W := by
    intro x hx
    apply mem_ball_zero_iff.mpr
    exact (norm_add_le _ _).trans_lt ((add_lt_add_of_lt_of_le (mem_ball_zero_iff.mp hx) le_rfl).trans hz)
  have hSmall : B ⊆ W := ball_subset_ball (by linarith only [hz,norm_nonneg z])
  have hΔ : MemLp (fun x => w (x+z) - w x) 2 (volume.restrict B) :=
    ((hw.1.comp_measurePreserving (measurePreserving_add_right_restrict_preimage W z)).mono_measure
      (Measure.restrict_mono_set volume hShift)).sub (hw.1.mono_measure (Measure.restrict_mono_set volume hSmall))
  have hDiffEq (x : Point) : ‖frobeniusField w (x+z) - frobeniusField w x‖ ^ 2 =
      ‖w (x+z)-w x‖ ^ 2 := by
    change ‖frobeniusCoordinateEquiv _ - frobeniusCoordinateEquiv _‖ ^ 2 = _
    rw [← map_sub,LinearIsometryEquiv.norm_map]
  simp_rw [hDiffEq] at hR
  have hD (i : Fin 3) : (∫ x in W, ‖D x i‖ ^ 2) = ‖P.2 i‖ ^ 2 := by
    rw [Lp.norm_toLp]
    exact integral_norm_sq_eq_eLpNorm_two_toReal_sq (hw.2.1 i)
  have hRHS : (∫ x in W, hsNormSq (frobeniusGradient D x)) ≤ 3 * ‖P‖ ^ 2 := by
    have hEq (x : Point) : hsNormSq (frobeniusGradient D x) = ∑ i, ‖D x i‖ ^ 2 := by
      simp only [hsNormSq,frobeniusGradient,LinearIsometryEquiv.norm_map]
    calc
      _ = ∑ i : Fin 3, ∫ x in W, ‖D x i‖ ^ 2 := by
        simp_rw [hEq]
        exact integral_finsetSum _ (fun i _ => (hw.2.1 i).integrable_norm_pow (by decide))
      _ = ∑ i : Fin 3, ‖P.2 i‖ ^ 2 := Finset.sum_congr rfl fun i _ => hD i
      _ ≤ ∑ _i : Fin 3, ‖P‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
          ((norm_le_pi_norm P.2 i).trans (le_max_right ‖P.1‖ _)) 2
      _ = _ := by simp [nsmul_eq_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal (hΔ.integrable_norm_pow (by decide))
    (Eventually.of_forall fun _ => sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  exact hR.trans ((mul_le_mul_of_nonneg_left hRHS (sq_nonneg _)).trans_eq (by ring))

/-- The actual smooth-domain extension and the concentric-ball Sobolev
translation bound control every displacement that can occur in the domain. -/
theorem IsSmoothDomain.exists_restrictedTranslationEnergy_le_memH1_graph
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Point → S0) (D : Point → Thesis.Gradient) (hu : MemH1 U u D),
      ∀ z ∈ ball (0 : Point) (diam U + 1),
        restrictedTranslationEnergy U u z ≤
          ENNReal.ofReal (C * ‖z‖ ^ 2 *
             ‖(hu.1.toLp u,fun i => (hu.2.1 i).toLp (fun x => D x i))‖ ^ 2) := by
  obtain ⟨R,hR,hSub⟩ := hU.1.2.2.subset_ball_lt 0 (0 : Point)
  let R' := R + (diam U + 1) + 1
  have hR' : 0 < R' := by dsimp only [R']; linarith only [hR,diam_nonneg (s := U)]
  have hU' : U ⊆ ball (0 : Point) R' :=
    hSub.trans (ball_subset_ball (by dsimp only [R']; linarith only [diam_nonneg (s := U)]))
  obtain ⟨B,hB,hExt⟩ := hU.exists_memH1_extension_bound hU' isOpen_ball Metric.isBounded_ball
  refine ⟨3*B^2,by positivity,?_⟩
  intro u D hu z hz
  obtain ⟨w,G,hw,hA,_,hNorm⟩ := hExt u D hu
  have hRect : R+‖z‖ < R' := by
    have t := mem_ball_zero_iff.mp hz
    dsimp only [R']
    linarith only [t]
  have hCut : translationIntersection U z ⊆ ball (0 : Point) R := inter_subset_left.trans hSub
  rw [restrictedTranslationEnergy_congr_ae hA.symm z]
  calc
    _ ≤ ∫⁻ x in ball (0 : Point) R, ENNReal.ofReal (‖w (x+z)-w x‖ ^ 2) :=
      lintegral_mono' (Measure.restrict_mono_set volume hCut) le_rfl
    _ ≤ _ := (ball_translationEnergy_le_graph_norm hR' hRect hw).trans (ENNReal.ofReal_le_ofReal (by
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hNorm 2)
        (by positivity : 0 ≤ 3 * ‖z‖ ^ 2)).trans_eq (by ring)))

end Thesis
