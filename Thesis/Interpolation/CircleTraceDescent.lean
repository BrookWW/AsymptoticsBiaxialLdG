module

public import StratificationTheory.Foundation.CircleNativeMeasure
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Descent of a continuous angular trace with matching endpoint values. -/

public section

noncomputable section

open HarmonicMaps Metric Set StratificationTheory Topology

namespace Thesis

abbrev AngularInterval := Icc (-Real.pi) Real.pi

private theorem circleNativeParam_repr (t : ℝ) : (circleNativeParam t).val =
    Complex.orthonormalBasisOneI.repr ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) := by
  ext i
  fin_cases i <;> simp [circleNativeParam_coe, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem circleNativeParam_neg_pi : circleNativeParam (-Real.pi) = circleNativeParam Real.pi := by
  apply Subtype.ext
  simp only [circleNativeParam_coe, Real.cos_neg, Real.sin_neg, Real.sin_pi, neg_zero]

theorem circleNativeParam_closed_surjective :
    Function.Surjective (fun t : AngularInterval => circleNativeParam t.val) := by
  intro x
  let e := Complex.orthonormalBasisOneI.repr
  let z := e.symm x.val
  have hx : ‖x.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using x.property
  have hz : ‖z‖ = 1 := (e.symm.norm_map x.val).trans hx
  let t : AngularInterval := ⟨z.arg, (Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
  refine ⟨t, Subtype.ext ?_⟩
  have hTravel := Complex.norm_mul_cos_add_sin_mul_I z
  rw [hz, Complex.ofReal_one, one_mul] at hTravel
  have h : (Real.cos z.arg : ℂ) + (Real.sin z.arg : ℂ) * Complex.I = z := by
    simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using hTravel
  rw [circleNativeParam_repr, show t.val = z.arg from rfl, h]
  exact e.apply_symm_apply x.val

theorem circleNativeParam_injOn_Ioc : InjOn circleNativeParam (Ioc (-Real.pi) Real.pi) := by
  intro s hs t ht h
  have he := congrArg Subtype.val h
  rw [circleNativeParam_repr, circleNativeParam_repr] at he
  have hArg := congrArg Complex.arg (Complex.orthonormalBasisOneI.repr.injective he)
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin, Complex.arg_cos_add_sin_mul_I hs,
    Complex.arg_cos_add_sin_mul_I ht] using hArg

private theorem equal_of_circleNativeParam_eq {X : Type*} (u : AngularInterval → X)
    (hEnd : u ⟨-Real.pi, le_rfl, by linarith [Real.pi_pos]⟩ =
      u ⟨Real.pi, by linarith [Real.pi_pos], le_rfl⟩)
    (s t : AngularInterval) (h : circleNativeParam s.val = circleNativeParam t.val) : u s = u t := by
  let π' : AngularInterval := ⟨Real.pi, by linarith [Real.pi_pos], le_rfl⟩
  let p (r : AngularInterval) : AngularInterval := if r.val = -Real.pi then π' else r
  have hp_mem (r : AngularInterval) : (p r).val ∈ Ioc (-Real.pi) Real.pi := by
    dsimp only [p]
    split_ifs with hr
    · exact ⟨by change -Real.pi < Real.pi; linarith [Real.pi_pos], le_rfl⟩
    · exact ⟨lt_of_le_of_ne r.property.1 (Ne.symm hr), r.property.2⟩
  have hp_circle (r : AngularInterval) : circleNativeParam (p r).val = circleNativeParam r.val := by
    dsimp only [p]
    split_ifs with hr
    · exact hr.symm ▸ circleNativeParam_neg_pi.symm
    · rfl
  have hp_u (r : AngularInterval) : u (p r) = u r := by
    dsimp only [p]
    split_ifs with hr
    · have hLeft : r = ⟨-Real.pi, le_rfl, by linarith [Real.pi_pos]⟩ := Subtype.ext hr
      rw [hLeft]
      exact hEnd.symm
    · rfl
  have hp_eq : p s = p t := Subtype.ext
    (circleNativeParam_injOn_Ioc (hp_mem s) (hp_mem t) ((hp_circle s).trans (h.trans (hp_circle t).symm)))
  exact (hp_u s).symm.trans ((congrArg u hp_eq).trans (hp_u t))

/-- A continuous trace with equal angular endpoints descends to the same
Euclidean circle as in the native surface energy. -/
theorem exists_circleTrace_descent {X : Type*} [TopologicalSpace X]
    (u : C(AngularInterval, X))
    (hEnd : u ⟨-Real.pi, le_rfl, by linarith [Real.pi_pos]⟩ =
      u ⟨Real.pi, by linarith [Real.pi_pos], le_rfl⟩) :
    ∃ v : C(sphere (0 : Domain 2) 1, X), ∀ t : AngularInterval,
      v (circleNativeParam t.val) = u t := by
  let p : AngularInterval → sphere (0 : Domain 2) 1 := fun t => circleNativeParam t.val
  have hSurj : Function.Surjective p := circleNativeParam_closed_surjective
  let v (x : sphere (0 : Domain 2) 1) := u (Classical.choose (hSurj x))
  have hId (t : AngularInterval) : v (p t) = u t := equal_of_circleNativeParam_eq u hEnd _ _
    (Classical.choose_spec (hSurj (p t)))
  letI : CompactSpace AngularInterval := isCompact_iff_compactSpace.1 isCompact_Icc
  have hp : Continuous p := continuous_circleNativeParam.comp continuous_subtype_val
  have hQuot : IsQuotientMap p := hp.isClosedMap.isQuotientMap hp hSurj
  have hv : Continuous v := hQuot.continuous_iff.2 (by rw [show v ∘ p = u from funext hId]; exact u.continuous)
  exact ⟨⟨v, hv⟩, hId⟩

end Thesis
