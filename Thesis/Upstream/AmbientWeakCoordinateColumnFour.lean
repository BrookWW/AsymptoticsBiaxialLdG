module

public import Thesis.Upstream.AmbientWeakPartialLpBounds

/-! Fourth-integrable weak coordinate columns and the smooth product rule. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

/-- A displayed coordinate weak derivative with square- and
fourth-integrable value and derivative. -/
structure HasWeakAmbientCoordinateColumnFour {n q : ℕ} (U : Set (Domain n)) (i : Fin n)
    (u D : Domain n → Ambient q) : Prop where
  valueTwo : MemLp u 2 (volume.restrict U)
  valueFour : MemLp u 4 (volume.restrict U)
  derivativeTwo : MemLp D 2 (volume.restrict U)
  derivativeFour : MemLp D 4 (volume.restrict U)
  weak : IsWeakAmbientCoordinatePartial U i u D

theorem HasWeakAmbientCoordinateColumnFour.sub {n q : ℕ} {U : Set (Domain n)}
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)] {i : Fin n}
    {u v D E : Domain n → Ambient q}
    (hu : HasWeakAmbientCoordinateColumnFour U i u D)
    (hv : HasWeakAmbientCoordinateColumnFour U i v E) :
    HasWeakAmbientCoordinateColumnFour U i (u-v) (D-E) :=
  ⟨hu.valueTwo.sub hv.valueTwo,hu.valueFour.sub hv.valueFour,
    hu.derivativeTwo.sub hv.derivativeTwo,hu.derivativeFour.sub hv.derivativeFour,
    hu.weak.sub hv.weak hu.valueTwo hv.valueTwo hu.derivativeTwo hv.derivativeTwo⟩

theorem HasWeakAmbientCoordinateColumnFour.congr_value_ae {n q : ℕ} {U : Set (Domain n)} {i : Fin n}
    {u v D : Domain n → Ambient q}
    (hu : HasWeakAmbientCoordinateColumnFour U i u D) (hEq : u =ᵐ[volume.restrict U] v) :
    HasWeakAmbientCoordinateColumnFour U i v D :=
  ⟨MemLp.ae_eq hEq hu.valueTwo,MemLp.ae_eq hEq hu.valueFour,
    hu.derivativeTwo,hu.derivativeFour,hu.weak.congr_ae hEq EventuallyEq.rfl⟩

theorem HasWeakAmbientCoordinateColumnFour.finset_sum {n q : ℕ} {U : Set (Domain n)}
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)] {i : Fin n}
    {ι : Type*} (s : Finset ι) {u D : ι → Domain n → Ambient q}
    (h : ∀ j ∈ s, HasWeakAmbientCoordinateColumnFour U i (u j) (D j)) :
    HasWeakAmbientCoordinateColumnFour U i (fun x => ∑ j ∈ s, u j x) (fun x => ∑ j ∈ s, D j x) :=
  ⟨memLp_finsetSum s (fun j hj => (h j hj).valueTwo),
    memLp_finsetSum s (fun j hj => (h j hj).valueFour),
    memLp_finsetSum s (fun j hj => (h j hj).derivativeTwo),
    memLp_finsetSum s (fun j hj => (h j hj).derivativeFour),
    IsWeakAmbientCoordinatePartial.finset_sum s (fun j hj => (h j hj).weak)
      (fun j hj => (h j hj).valueTwo) (fun j hj => (h j hj).derivativeTwo)⟩

/-- On a bounded patch the smooth factor and its derivative are bounded,
so multiplication retains both exponents of the actual graph. -/
theorem HasWeakAmbientCoordinateColumnFour.smul_smooth {n q : ℕ} {U : Set (Domain n)}
    (hU : MeasurableSet U) (hB : Bornology.IsBounded U) {i : Fin n}
    {u D : Domain n → Ambient q} (hu : HasWeakAmbientCoordinateColumnFour U i u D)
    {a : Domain n → ℝ} (ha : ContDiff ℝ ∞ a) :
    HasWeakAmbientCoordinateColumnFour U i (fun x => a x • u x)
      (fun x => coordinateDerivative a ha i x • u x + a x • D x) := by
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict U) :=
    isFiniteMeasure_restrict.mpr hB.measure_lt_top.ne
  have hTop {b : Domain n → ℝ} (hb : Continuous b) : MemLp b ⊤ (volume.restrict U) := by
    obtain ⟨C,hC⟩ := hB.isCompact_closure.exists_bound_of_continuousOn hb.continuousOn
    exact memLp_top_of_bound hb.aestronglyMeasurable C
      ((ae_restrict_mem hU).mono fun x hx => hC x (subset_closure hx))
  have haTop := hTop ha.continuous
  have hDaTop : MemLp (coordinateDerivative a ha i) ⊤ (volume.restrict U) :=
    hTop ((ha.continuous_fderiv (by simp)).clm_apply continuous_const)
  exact ⟨hu.valueTwo.smul (r := 2) haTop,hu.valueFour.smul (r := 4) haTop,
    (hu.valueTwo.smul (r := 2) hDaTop).add (hu.derivativeTwo.smul (r := 2) haTop),
    (hu.valueFour.smul (r := 4) hDaTop).add (hu.derivativeFour.smul (r := 4) haTop),
    hu.weak.smul_smooth hu.valueTwo hu.derivativeTwo ha haTop hDaTop⟩

end Thesis
