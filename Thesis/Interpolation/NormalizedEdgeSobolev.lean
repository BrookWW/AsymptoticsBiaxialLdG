module

public import Thesis.Interpolation.PenalizedEdge
import StratificationTheory.Foundation.IntervalWeakRepresentative
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The actual absolute-continuous edge field in centered square coordinates. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Thesis

@[expose] def normalizedEdgeParameter (h t : ℝ) : ℝ := (h / 2) * t + h / 2

theorem normalizedEdgeParameter_mem_closed {h t : ℝ} (hh : 0 < h) (ht : t ∈ Icc (-1 : ℝ) 1) :
    normalizedEdgeParameter h t ∈ Icc 0 h := by
  have hβ := (half_pos hh).le
  constructor <;> dsimp only [normalizedEdgeParameter]
  · nlinarith [mul_le_mul_of_nonneg_left ht.1 hβ]
  · nlinarith [mul_le_mul_of_nonneg_left ht.2 hβ]

private theorem normalizedEdgeParameter_preimage {h : ℝ} (hh : 0 < h) :
    normalizedEdgeParameter h ⁻¹' Ioo 0 h = Ioo (-1 : ℝ) 1 := by
  ext x
  change (0 < (h / 2) * x + h / 2 ∧ (h / 2) * x + h / 2 < h) ↔ -1 < x ∧ x < 1
  have hβ := half_pos hh
  have hLo : (h / 2) * (-1) < (h / 2) * x ↔ -1 < x := mul_lt_mul_iff_of_pos_left hβ
  have hHi : (h / 2) * x < (h / 2) * 1 ↔ x < 1 := mul_lt_mul_iff_of_pos_left hβ
  constructor
  · intro h
    exact ⟨hLo.1 (by linarith only [h.1]), hHi.1 (by linarith only [h.2])⟩
  · intro h
    exact ⟨by linarith only [hLo.2 h.1], by linarith only [hHi.2 h.2]⟩

private theorem normalizedEdgeParameter_map_restrict {h : ℝ} (hh : 0 < h) :
    Measure.map (normalizedEdgeParameter h) (volume.restrict (Ioo (-1 : ℝ) 1)) =
      ENNReal.ofReal (h / 2)⁻¹ • volume.restrict (Ioo 0 h) := by
  let β := h / 2
  have hβ : 0 < β := half_pos hh
  let e := (Homeomorph.smul (Units.mk0 β hβ.ne')).trans (Homeomorph.addRight β)
  have hEmb : MeasurableEmbedding (normalizedEdgeParameter h) := e.isClosedEmbedding.measurableEmbedding
  have hVol : Measure.map (normalizedEdgeParameter h) volume = ENNReal.ofReal β⁻¹ • (volume : Measure ℝ) := by
    change Measure.map ((fun x : ℝ => x + β) ∘ (fun x : ℝ => β * x)) volume = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop)]
    change Measure.map (fun x : ℝ => x + β) (Measure.map (fun x : ℝ => β • x) volume) = _
    rw [Measure.map_addHaar_smul volume hβ.ne', Measure.map_smul, (measurePreserving_add_right volume β).map_eq]
    simp only [Module.finrank_self, pow_one, abs_of_pos (inv_pos.2 hβ)]
  rw [← normalizedEdgeParameter_preimage hh, ← hEmb.restrict_map, hVol, Measure.restrict_smul]

/-- Integration of a scalar density in the centered edge parameter. -/
theorem integral_normalizedEdgeParameter {h : ℝ} (hh : 0 < h) (p : ℝ → ℝ) :
    (∫ t in Ioo (-1 : ℝ) 1, p (normalizedEdgeParameter h t)) =
      (h / 2)⁻¹ * ∫ t in Ioo (0 : ℝ) h, p t := by
  let β := h / 2
  have hβ : 0 < β := half_pos hh
  let e := (Homeomorph.smul (Units.mk0 β hβ.ne')).trans (Homeomorph.addRight β)
  have hEmb : MeasurableEmbedding (normalizedEdgeParameter h) := e.isClosedEmbedding.measurableEmbedding
  change (∫ t, p (normalizedEdgeParameter h t) ∂volume.restrict (Ioo (-1 : ℝ) 1)) = _
  rw [← hEmb.integral_map p, normalizedEdgeParameter_map_restrict hh, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.2 hβ.le), smul_eq_mul]

/-- The centered parameter has the actual rescaled derivative and the exact
factor `h/2` in the squared derivative integral. -/
theorem normalizedEdge_sobolev_data {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {h : ℝ} (hh : 0 < h) {u g : ℝ → E} (hg : MemLp g 2 (volume.restrict (Ioo 0 h)))
    (hInc : ∀ s ∈ Icc (0 : ℝ) h, ∀ t ∈ Icc (0 : ℝ) h, u t - u s = ∫ x in s..t, g x) :
    let U := u ∘ normalizedEdgeParameter h
    let G := fun x => (h / 2) • g (normalizedEdgeParameter h x)
    AbsolutelyContinuousOnInterval U (-1) 1 ∧ MemLp (deriv U) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) ∧
      deriv U =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] G ∧
      (∫ x in Ioo (-1 : ℝ) 1, ‖deriv U x‖ ^ 2) = (h / 2) * ∫ x in Ioo (0 : ℝ) h, ‖g x‖ ^ 2 := by
  intro U G
  let μ := volume.restrict (Ioo (-1 : ℝ) 1)
  let ν := volume.restrict (Ioo (0 : ℝ) h)
  let β := h / 2
  have hβ : 0 < β := half_pos hh
  let A := normalizedEdgeParameter h
  let e := (Homeomorph.smul (Units.mk0 β hβ.ne')).trans (Homeomorph.addRight β)
  have hEmb : MeasurableEmbedding A := e.isClosedEmbedding.measurableEmbedding
  have hMap : Measure.map A μ = ENNReal.ofReal β⁻¹ • ν := normalizedEdgeParameter_map_restrict hh
  have hLp : MemLp G 2 μ := by
    have h := hg.smul_measure (c := ENNReal.ofReal β⁻¹) ENNReal.ofReal_ne_top
    rw [← hMap] at h
    exact (h.comp_of_map hEmb.measurable.aemeasurable).const_smul β
  have hI : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1, U t - U s = ∫ x in s..t, G x := by
    intro s hs t ht
    rw [show (∫ x in s..t, G x) = ∫ x in A s..A t, g x by
      dsimp only [G, A, normalizedEdgeParameter, β]
      rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_add]]
    exact hInc _ (normalizedEdgeParameter_mem_closed hh hs) _ (normalizedEdgeParameter_mem_closed hh ht)
  have hDer : deriv U =ᵐ[μ] G :=
    (ae_hasDerivAt_of_interval_increments (by norm_num : (-1 : ℝ) < 1) hLp hI).mono (fun _ h => h.deriv)
  have hAC : AbsolutelyContinuousOnInterval U (-1) 1 := by
    let V (t : ℝ) := U (-1) + ∫ x in (-1 : ℝ)..t, G x
    have hInt := StratificationTheory.intervalIntegrable_of_memLp_two (by norm_num : (-1 : ℝ) ≤ 1) hLp
    have hV : AbsolutelyContinuousOnInterval V (-1) 1 := by
      have h := StratificationTheory.intervalPrimitive_absolutelyContinuous hInt left_mem_uIcc
      rw [absolutelyContinuousOnInterval_iff] at h ⊢
      simpa only [V, dist_add_left] using h
    rw [absolutelyContinuousOnInterval_iff] at hV ⊢
    intro ε hε
    obtain ⟨δ, hδ, hL⟩ := hV ε hε
    refine ⟨δ, hδ, fun I hMeet hSmall => ?_⟩
    have hEq (x : ℝ) (hx : x ∈ uIcc (-1 : ℝ) 1) : U x = V x := by
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      have hi := hI (-1) (by norm_num) x hx
      dsimp only [V]
      exact (sub_eq_iff_eq_add.mp hi).trans (add_comm _ _)
    refine lt_of_eq_of_lt (Finset.sum_congr rfl fun i hi => ?_) (hL I hMeet hSmall)
    rw [hEq _ (hMeet.1 i hi).1, hEq _ (hMeet.1 i hi).2]
  refine ⟨hAC, hLp.ae_eq hDer.symm, hDer, ?_⟩
  have hEq := integral_congr_ae (hDer.mono fun x hx => congrArg (fun k : E => ‖k‖ ^ 2) hx)
  change (∫ x, ‖deriv U x‖ ^ 2 ∂μ) = β * ∫ x, ‖g x‖ ^ 2 ∂ν
  rw [hEq]
  change (∫ x, ‖β • g (A x)‖ ^ 2 ∂μ) = β * ∫ x, ‖g x‖ ^ 2 ∂ν
  simp only [norm_smul, Real.norm_of_nonneg hβ.le, mul_pow]
  rw [integral_const_mul, ← hEmb.integral_map (fun x : ℝ => ‖g x‖ ^ 2), hMap,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hβ.le), smul_eq_mul, ← mul_assoc]
  have hPow : β ^ 2 * β⁻¹ = β := by field_simp
  rw [hPow]

end Thesis
