module

public import Thesis.Upstream.AmbientWeakDivergenceCoordinate
public import Thesis.Upstream.LocalSobolevGradientTransport
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! The strong displayed coordinate equation of a weak elliptic graph. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

/-- Finite square-integrable weak divergence columns add up almost
everywhere to the actual forcing in the distributional equation. -/
theorem HasWeakPackedDivergenceEq.ae_eq_sum_coordinatePartials {n q : ℕ}
    {U : Set (Domain n)} (hU : IsOpen U) [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U)]
    {P : Domain n → HarmonicMaps.Gradient n q} {f : Domain n → Ambient q}
    (h : HasWeakPackedDivergenceEq U (fun x => packAmbientGradient (P x)) f)
    (hP : ∀ j, MemLp (fun x => P x j) 2 (volume.restrict U))
    (hf : MemLp f 2 (volume.restrict U)) {G : Domain n → HarmonicMaps.Gradient n q}
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U))
    (hWeak : ∀ j, IsWeakAmbientCoordinatePartial U j (fun x => P x j) (fun x => G x j)) :
    (fun x => ∑ j : Fin n, G x j) =ᵐ[volume.restrict U] f := by
  let g (x : Domain n) := ∑ j : Fin n, G x j
  have hg : MemLp g 2 (volume.restrict U) := memLp_finsetSum _ (fun j _ => hG j)
  have hLocal : LocallyIntegrableOn (g-f) U volume :=
    IntegrableOn.locallyIntegrableOn ((hg.sub hf).integrable (by norm_num))
  have hz : ∀ᵐ x ∂volume, x ∈ U → (g-f) x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hLocal
    intro φ hφ hφc hφs
    have ht := scalar_test_identity_of_packed_divergence h hP hf hφ hφc hφs
    have htest (j : Fin n) := hWeak j φ hφ hφc hφs
    simp_rw [htest,Finset.sum_neg_distrib] at ht
    have hEq := neg_injective ht
    have hφTop := hφ.continuous.memLp_top_of_hasCompactSupport hφc (volume.restrict U)
    have hInt (j : Fin n) : Integrable (fun x => φ x • G x j) (volume.restrict U) :=
      ((hG j).integrable (by norm_num)).smul_of_top_right hφTop
    have hGI : Integrable (fun x => φ x • g x) (volume.restrict U) :=
      (hg.integrable (by norm_num)).smul_of_top_right hφTop
    have hFI : Integrable (fun x => φ x • f x) (volume.restrict U) :=
      (hf.integrable (by norm_num)).smul_of_top_right hφTop
    have hPair : (∫ x in U, φ x • g x) = ∫ x in U, φ x • f x := by
      dsimp only [g]
      simp_rw [Finset.smul_sum]
      rw [integral_finsetSum _ (fun j _ => hInt j)]
      exact hEq
    have hZero : (∫ x in U, φ x • (g-f) x) = 0 := by
      simp_rw [Pi.sub_apply,smul_sub]
      rw [integral_sub hGI hFI,hPair,sub_self]
    rw [← hZero]
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h)),zero_smul]
  apply (ae_restrict_iff' hU.measurableSet).2
  filter_upwards [hz] with x hx hxu
  exact sub_eq_zero.mp (hx hxu)

/-- The smooth coefficient matrix and the actual weak second columns
give the nondivergence expression on a bounded open patch. -/
theorem HasWeakPackedDivergenceEq.metric_strongEquation {n q : ℕ} (U : OpenDomain n)
    (hU : Bornology.IsBounded U.val) {D : Domain n → HarmonicMaps.Gradient n q}
    {H : Domain n → Fin n → HarmonicMaps.Gradient n q} {f : Domain n → Ambient q}
    (hD : ∀ j, MemW12 U (fun x => D x j) (fun x => H x j))
    (hf : MemLp f 2 (volume.restrict U.val))
    (A : Domain n → Fin n → Fin n → ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hEq : HasWeakPackedDivergenceEq U.val
      (fun x => packAmbientGradient (fun i => ∑ j : Fin n, A x i j • D x j)) f) :
    (fun x => ∑ i : Fin n, ∑ j : Fin n,
      (coordinateDerivative (fun y => A y i j) (hA i j) i x • D x j + A x i j • H x j i))
      =ᵐ[volume.restrict U.val] f := by
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val) :=
    isFiniteMeasure_restrict.mpr hU.measure_lt_top.ne
  let P (x : Domain n) (i : Fin n) := ∑ j : Fin n, A x i j • D x j
  let Q (i j : Fin n) (x : Domain n) := coordinateDerivative (fun y => A y i j) (hA i j) i x • D x j +
    A x i j • H x j i
  let G (x : Domain n) (i : Fin n) := ∑ j : Fin n, Q i j x
  have hTop {a : Domain n → ℝ} (ha : Continuous a) : MemLp a ⊤ (volume.restrict U.val) := by
    obtain ⟨M,hM⟩ := hU.isCompact_closure.exists_bound_of_continuousOn ha.continuousOn
    exact memLp_top_of_bound ha.aestronglyMeasurable M
      ((ae_restrict_mem U.property.measurableSet).mono fun x hx => hM x (subset_closure hx))
  have hCut (i j : Fin n) : MemLp (fun x => A x i j) ⊤ (volume.restrict U.val) :=
    hTop (hA i j).continuous
  have hCutD (i j : Fin n) :
      MemLp (coordinateDerivative (fun y => A y i j) (hA i j) i) ⊤ (volume.restrict U.val) :=
    hTop (((hA i j).continuous_fderiv (by simp)).clm_apply continuous_const)
  have hPLp (i j : Fin n) : MemLp (fun x => A x i j • D x j) 2 (volume.restrict U.val) :=
    ((hD j).2.1).smul (r := (2 : ℝ≥0∞)) (hCut i j)
  have hQLp (i j : Fin n) : MemLp (Q i j) 2 (volume.restrict U.val) :=
    (((hD j).2.1).smul (r := (2 : ℝ≥0∞)) (hCutD i j)).add
      (((hD j).2.2 i).smul (r := (2 : ℝ≥0∞)) (hCut i j))
  have hQ (i j : Fin n) : IsWeakAmbientCoordinatePartial U.val i
      (fun x => A x i j • D x j) (Q i j) :=
    IsWeakAmbientCoordinatePartial.smul_smooth ((hD j).1.2.2 i) (hD j).2.1 ((hD j).2.2 i)
      (hA i j) (hCut i j) (hCutD i j)
  have hP (i : Fin n) : MemLp (fun x => P x i) 2 (volume.restrict U.val) :=
    memLp_finsetSum _ (fun j _ => hPLp i j)
  have hG (i : Fin n) : MemLp (fun x => G x i) 2 (volume.restrict U.val) :=
    memLp_finsetSum _ (fun j _ => hQLp i j)
  have hGP (i : Fin n) : IsWeakAmbientCoordinatePartial U.val i (fun x => P x i) (fun x => G x i) :=
    IsWeakAmbientCoordinatePartial.finset_sum _ (fun j _ => hQ i j) (fun j _ => hPLp i j) (fun j _ => hQLp i j)
  exact HasWeakPackedDivergenceEq.ae_eq_sum_coordinatePartials U.property hEq hP hf hG hGP

end Thesis
