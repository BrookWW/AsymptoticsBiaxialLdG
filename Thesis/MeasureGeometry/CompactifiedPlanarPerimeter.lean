module

public import Thesis.MeasureGeometry.PlanarPerimeterCircle
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-! The outer perimeter contracts through the point at infinity. -/

public section

noncomputable section

open Filter OnePoint Set
open scoped Topology unitInterval

namespace Thesis.MeasureGeometry

/-- The restriction of a continuous map on a compactified planar domain to its finite points. -/
@[expose] def compactifiedPlaneRestriction {a : BulkCoefficients}
    {W : Set (OnePoint (ℝ × ℝ))} (Q : C(W,vacuum a)) :
    C({x : ℝ × ℝ | (x : OnePoint (ℝ × ℝ)) ∈ W},vacuum a) :=
  ⟨fun x => Q ⟨x.val,x.property⟩,
    Q.continuous.comp ((OnePoint.continuous_coe.comp continuous_subtype_val).subtype_mk _)⟩

/-- Every point of the perimeter of a centered square has the same
maximum norm. -/
theorem norm_rectangularPerimeter_centered_square {A : ℝ} (hA : 0 ≤ A) (u : unitInterval) :
    ‖rectangularPerimeter (-A) A (-A) A u‖ = A := by
  let p := rectangularPerimeter (-A) A (-A) A u
  have hOrder : -A ≤ A := by linarith only [hA]
  have hp : p ∈ Icc (-A) A ×ˢ Icc (-A) A := rectangularPerimeter_mem_closed hOrder hOrder u
  have hUpper : max |p.1| |p.2| ≤ A :=
    max_le (abs_le.mpr hp.1) (abs_le.mpr hp.2)
  have hLower : A ≤ max |p.1| |p.2| := by
    have hs := rectangularPerimeter_side (-A) A (-A) A u
    have hPosF : p.1 = A → A ≤ max |p.1| |p.2| := fun h =>
      (le_of_eq ((congrArg abs h).trans (abs_of_nonneg hA)).symm).trans (le_max_left _ _)
    have hPosS : p.2 = A → A ≤ max |p.1| |p.2| := fun h =>
      (le_of_eq ((congrArg abs h).trans (abs_of_nonneg hA)).symm).trans (le_max_right _ _)
    have hNegF : p.1 = -A → A ≤ max |p.1| |p.2| := by
      intro h
      have he : |p.1| = A := by rw [h,abs_neg,abs_of_nonneg hA]
      exact he.symm.le.trans (le_max_left _ _)
    have hNegS : p.2 = -A → A ≤ max |p.1| |p.2| := by
      intro h
      have he : |p.2| = A := by rw [h,abs_neg,abs_of_nonneg hA]
      exact he.symm.le.trans (le_max_right _ _)
    split_ifs at hs
    · exact hPosS hs
    · exact hNegF hs
    · exact hNegS hs
    · exact hPosF hs
  exact le_antisymm hUpper hLower

private def perimeterRadialOut (A : ℝ) (s : unitInterval × unitInterval) :
    OnePoint (ℝ × ℝ) :=
  if s.1 = 1 then ∞ else
    ↑((1-s.1.val)⁻¹ • rectangularPerimeter (-A) A (-A) A s.2 : ℝ × ℝ)

private theorem continuous_perimeterRadialOut {A : ℝ} (hA : 0 < A) :
    Continuous (perimeterRadialOut A) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : s.1 = 1
  · have hS0 : (s.1 : ℝ) = 1 := by rw [hs]; rfl
    change Tendsto (perimeterRadialOut A) (𝓝 s) (𝓝 (perimeterRadialOut A s))
    rw [perimeterRadialOut,if_pos hs,Tendsto,OnePoint.le_nhds_infty]
    intro K _ hK
    obtain ⟨C,hC⟩ := hK.isBounded.exists_norm_le
    let C₀ := max C 0 + 1
    have hC₀ : 0 < C₀ := lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (le_max_right _ _))
    have hC₁ : C < C₀ := (le_max_left _ _).trans_lt (lt_add_one _)
    have hS : Tendsto (fun p : unitInterval × unitInterval => 1 - p.1.val) (𝓝 s) (𝓝 0) := by
      have hCts : Continuous (fun p : unitInterval × unitInterval => 1 - p.1.val) :=
        continuous_const.sub (continuous_subtype_val.comp continuous_fst)
      simpa only [hS0,sub_self] using hCts.continuousAt (x := s) |>.tendsto
    change ∀ᶠ p in 𝓝 s, perimeterRadialOut A p ∈ (↑) '' Kᶜ ∪ {∞}
    filter_upwards [hS (Iio_mem_nhds (div_pos hA hC₀))] with p hp
    by_cases hp1 : p.1 = 1
    · rw [perimeterRadialOut,if_pos hp1]
      exact Or.inr rfl
    · rw [perimeterRadialOut,if_neg hp1]
      apply Or.inl
      refine ⟨_,?_,rfl⟩
      intro hMem
      have hPos : 0 < 1-p.1.val := sub_pos.mpr
        (p.1.property.2.lt_of_ne (fun h => hp1 (Subtype.ext h)))
      have hN := hC _ hMem
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hPos.le),
        norm_rectangularPerimeter_centered_square hA.le,inv_mul_eq_div] at hN
      have hUpper : C₀ * (1-p.1.val) < A := by
        rw [mul_comm]
        exact (lt_div_iff₀ hC₀).mp hp
      exact (not_lt_of_ge hN) (hC₁.trans ((lt_div_iff₀ hPos).mpr hUpper))
  · have hS : ∀ᶠ p : unitInterval × unitInterval in 𝓝 s, p.1 ≠ 1 :=
      (continuous_fst.continuousAt (x := s)).eventually_ne hs
    let F (p : unitInterval × unitInterval) : ℝ × ℝ :=
      (1-p.1.val)⁻¹ • rectangularPerimeter (-A) A (-A) A p.2
    have hS0 : (s.1 : ℝ) ≠ 1 := fun h => hs (Subtype.ext h)
    have hCts : ContinuousAt F s :=
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).continuousAt.inv₀
        (sub_ne_zero.mpr (Ne.symm hS0))).smul
      ((rectangularPerimeter (-A) A (-A) A).continuous.comp continuous_snd).continuousAt
    have hLeft := OnePoint.continuous_coe.continuousAt (x := F s) |>.comp hCts
    apply hLeft.congr
    filter_upwards [hS] with p hp
    rw [perimeterRadialOut,if_neg hp]
    rfl

/-- If every point outside the open square and the point at infinity belong
to the compactified domain, the character of the square perimeter is zero. -/
theorem rectangularLightParity_zero_of_compactified {a : BulkCoefficients} (v : Sphere3)
    {W : Set (OnePoint (ℝ × ℝ))} (Q : C(W,vacuum a)) {A : ℝ} (hA : 0 < A)
    (hInf : (∞ : OnePoint (ℝ × ℝ)) ∈ W)
    (hW : ∀ p : ℝ × ℝ, A ≤ ‖p‖ → (p : OnePoint (ℝ × ℝ)) ∈ W)
    (hP : ∀ s, ((rectangularPerimeter (-A) A (-A) A s : ℝ × ℝ) : OnePoint (ℝ × ℝ)) ∈ W) :
    vacuumPathLightParity a v (mappedPathOn (compactifiedPlaneRestriction Q)
      (rectangularPerimeter (-A) A (-A) A) hP) = 0 := by
  let P := rectangularPerimeter (-A) A (-A) A
  have hIn (s : unitInterval × unitInterval) : perimeterRadialOut A s ∈ W := by
    by_cases hs : s.1 = 1
    · rw [perimeterRadialOut,if_pos hs]
      exact hInf
    · rw [perimeterRadialOut,if_neg hs]
      apply hW
      have hPos : 0 < 1-s.1.val := sub_pos.mpr
        (s.1.property.2.lt_of_ne (fun h => hs (Subtype.ext h)))
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hPos.le),
        norm_rectangularPerimeter_centered_square hA.le,inv_mul_eq_div]
      apply (le_div_iff₀ hPos).mpr
      nlinarith only [mul_nonneg hA.le s.1.property.1]
  let F : C(unitInterval × unitInterval,vacuum a) :=
    ⟨fun s => Q ⟨perimeterRadialOut A s,hIn s⟩,
      Q.continuous.comp ((continuous_perimeterRadialOut hA).subtype_mk _)⟩
  rw [← vacuumPathLightParity_refl a v (Q ⟨∞,hInf⟩)]
  apply vacuumPathLightParity_of_periodic_square _ _ _ _ F
  · intro u
    apply congrArg Q
    apply Subtype.ext
    change perimeterRadialOut A (0,u) = (P u : OnePoint (ℝ × ℝ))
    rw [perimeterRadialOut,if_neg (show (0 : unitInterval) ≠ 1 from zero_ne_one)]
    simp [P]
  · intro u
    apply congrArg Q
    apply Subtype.ext
    change perimeterRadialOut A (1,u) = ∞
    rw [perimeterRadialOut,if_pos rfl]
  · intro u
    apply congrArg Q
    apply Subtype.ext
    change perimeterRadialOut A (u,0) = perimeterRadialOut A (u,1)
    rw [perimeterRadialOut,perimeterRadialOut]
    split_ifs
    · rfl
    · rw [P.source,P.target]

end Thesis.MeasureGeometry
