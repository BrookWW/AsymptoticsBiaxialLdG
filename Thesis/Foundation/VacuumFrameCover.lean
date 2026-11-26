module

public import Thesis.Foundation.VacuumFrame
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-! The four director signs form the fibers of the actual frame covering. -/

@[expose] public section

noncomputable section

open Set Topology
open scoped Matrix.Norms.Frobenius

namespace Thesis

/-- Independent signs of the first and second directors. -/
abbrev VacuumFrameSigns := ℤˣ × ℤˣ

/-- The signed unit integer considered as a real scalar. -/
def directorSign (u : ℤˣ) : ℝ := ((u : ℤ) : ℝ)

private theorem directorSign_eq_or (u : ℤˣ) : directorSign u = 1 ∨ directorSign u = -1 := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact Or.inl (by simp [directorSign])
  · exact Or.inr (by simp [directorSign])

theorem norm_directorSign (u : ℤˣ) : ‖directorSign u‖ = 1 := by
  rcases directorSign_eq_or u with h | h <;> simp only [h, norm_neg, norm_one]

instance vacuumFrameSignAction : MulAction VacuumFrameSigns VacuumFrame where
  smul g f := ⟨(directorSign g.1 • f.val.1, directorSign g.2 • f.val.2), by
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_smul, norm_directorSign, f.property.1, mul_one]
    · rw [norm_smul, norm_directorSign, f.property.2.1, mul_one]
    · rw [real_inner_smul_left, real_inner_smul_right, f.property.2.2, mul_zero, mul_zero]⟩
  one_smul f := by
    apply Subtype.ext
    change (directorSign 1 • f.val.1, directorSign 1 • f.val.2) = f.val
    simp [directorSign]
  mul_smul g g' f := by
    apply Subtype.ext
    change (directorSign (g.1 * g'.1) • f.val.1, directorSign (g.2 * g'.2) • f.val.2) =
      (directorSign g.1 • (directorSign g'.1 • f.val.1), directorSign g.2 • (directorSign g'.2 • f.val.2))
    simp only [directorSign, Units.val_mul, Int.cast_mul, smul_smul]

instance vacuumFrameContinuousSign : ContinuousConstSMul VacuumFrameSigns VacuumFrame where
  continuous_const_smul g := by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_fst.comp continuous_subtype_val).const_smul (directorSign g.1)).prodMk
      ((continuous_snd.comp continuous_subtype_val).const_smul (directorSign g.2))

theorem directorSign_injective : Function.Injective directorSign := by
  intro s t h
  change ((s : ℤ) : ℝ) = ((t : ℤ) : ℝ) at h
  exact Units.ext (Int.cast_injective h)

instance vacuumFrameFreeSign : IsCancelSMul VacuumFrameSigns VacuumFrame where
  right_cancel' g g' f h := by
    have hn : f.val.1 ≠ 0 := by
      intro hz
      have hNorm := f.property.1
      rw [hz, norm_zero] at hNorm
      exact zero_ne_one hNorm
    have hm : f.val.2 ≠ 0 := by
      intro hz
      have hNorm := f.property.2.1
      rw [hz, norm_zero] at hNorm
      exact zero_ne_one hNorm
    have h₁ := congrArg (fun x : VacuumFrame => x.val.1) h
    have h₂ := congrArg (fun x : VacuumFrame => x.val.2) h
    exact Prod.ext (directorSign_injective (smul_left_injective ℝ hn h₁))
      (directorSign_injective (smul_left_injective ℝ hm h₂))

theorem exists_directorSign_smul_of_sign {E : Type*} [AddCommGroup E] [Module ℝ E]
    {x y : E} (h : x = y ∨ x = -y) :
    ∃ u : ℤˣ, directorSign u • y = x := by
  rcases h with rfl | rfl
  · exact ⟨1, by simp [directorSign]⟩
  · exact ⟨-1, by simp [directorSign]⟩

theorem directorSign_smul_eq_or_neg {E : Type*} [AddCommGroup E] [Module ℝ E] (g : ℤˣ) (x : E) :
    directorSign g • x = x ∨ directorSign g • x = -x := by
  rcases directorSign_eq_or g with h | h
  · exact Or.inl (by rw [h, one_smul])
  · exact Or.inr (by rw [h, neg_smul, one_smul])

theorem vacuumFrameProjection_eq_iff_orbit (a : BulkCoefficients) {f g : VacuumFrame} :
    vacuumFrameProjection a f = vacuumFrameProjection a g ↔ f ∈ MulAction.orbit VacuumFrameSigns g := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := (vacuumFrameProjection_eq_iff_signs a f g).1 h
    obtain ⟨s, hs⟩ := exists_directorSign_smul_of_sign h₁
    obtain ⟨t, ht⟩ := exists_directorSign_smul_of_sign h₂
    exact ⟨(s, t), Subtype.ext (Prod.ext hs ht)⟩
  · rintro ⟨g', rfl⟩
    exact (vacuumFrameProjection_eq_iff_signs a (g' • g) g).2
      ⟨directorSign_smul_eq_or_neg g'.1 g.val.1, directorSign_smul_eq_or_neg g'.2 g.val.2⟩

/-- The actual frame map is the quotient covering for the free action of
the two director signs. -/
theorem vacuumFrameProjection_isQuotientCoveringMap (a : BulkCoefficients) :
    IsQuotientCoveringMap (vacuumFrameProjection a) VacuumFrameSigns := by
  have hCont := continuous_vacuumFrameProjection a
  have hQ : IsQuotientMap (vacuumFrameProjection a) :=
    hCont.isClosedMap.isQuotientMap hCont (vacuumFrameProjection_surjective a)
  exact hQ.isQuotientCoveringMap_of_properlyDiscontinuousSMul (vacuumFrameProjection_eq_iff_orbit a)

theorem vacuumFrameProjection_isCoveringMap (a : BulkCoefficients) :
    IsCoveringMap (vacuumFrameProjection a) :=
  (vacuumFrameProjection_isQuotientCoveringMap a).isCoveringMap

theorem vacuumFrameProjection_card_fiber (a : BulkCoefficients) (A : vacuum a) :
    Nat.card ((vacuumFrameProjection a) ⁻¹' {A}) = 4 := by
  obtain ⟨f, hf⟩ := vacuumFrameProjection_surjective a A
  have H := (vacuumFrameProjection_isQuotientCoveringMap a).fiberEquivGroup
    (⟨f, hf⟩ : (vacuumFrameProjection a) ⁻¹' {A})
  rw [Nat.card_congr H, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_units_int]

end Thesis
