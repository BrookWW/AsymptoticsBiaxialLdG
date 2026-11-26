module

public import Thesis.Upstream.LocalSobolevGradientTransport

/-! Back transport of the second weak columns through the inverse chart. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

/-- A second weak graph proved in flat coordinates yields an actual weak
graph of the original displayed gradient. The bound includes the first
columns because the inverse chart has varying coefficients. -/
theorem exists_memW12_secondColumns_of_gradientPullback {n q : ℕ}
    (F : Domain n ≃ₜ Domain n) (hF : ContDiff ℝ ∞ (F : Domain n → Domain n))
    (hInv : ContDiff ℝ ∞ (F.symm : Domain n → Domain n))
    (V W : OpenDomain n) (hBound : Bornology.IsBounded V.val)
    (hInto : MapsTo F.symm V.val W.val)
    (hMP : MeasurePreserving F.symm (volume.restrict V.val) (volume.restrict W.val)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (D : Domain n → HarmonicMaps.Gradient n q)
        (H : Domain n → Fin n → HarmonicMaps.Gradient n q) (E : ℝ),
        (∀ j, MemW12 W (fun x => ambientGradientPullback F D x j) (fun x => H x j)) →
        (∀ j, lpNorm (fun x => ambientGradientPullback F D x j) 2 (volume.restrict W.val) ≤ E) →
        (∀ j i, lpNorm (fun x => H x j i) 2 (volume.restrict W.val) ≤ E) →
        ∃ G : Domain n → Fin n → HarmonicMaps.Gradient n q,
          ∀ j, MemW12 V (fun x => D x j) (fun x => G x j) ∧
            ∀ i, lpNorm (fun x => G x j i) 2 (volume.restrict V.val) ≤ C*E := by
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict V.val) :=
    isFiniteMeasure_restrict.mpr hBound.measure_lt_top.ne
  obtain ⟨L,hL,hTransport⟩ := exists_memW12_local_volumePreserving_pullback (q := q)
    F.symm hInv V W hBound hInto hMP
  let a (jk : Fin n × Fin n) (x : Domain n) :=
    fderiv ℝ F.symm x (EuclideanSpace.single jk.1 1) jk.2
  have hA (jk : Fin n × Fin n) : ContDiff ℝ ∞ (a jk) :=
    (EuclideanSpace.proj jk.2).contDiff.comp
      ((hInv.fderiv_right (by simp)).clm_apply contDiff_const)
  have hDA (p : (Fin n × Fin n) × Fin n) :
      Continuous (coordinateDerivative (a p.1) (hA p.1) p.2) :=
    ((hA p.1).continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨B,hB,hBAll⟩ := exists_uniform_abs_bound_on_compact hBound.isCompact_closure a
    (fun j => (hA j).continuous)
  obtain ⟨M,hM,hMAll⟩ := exists_uniform_abs_bound_on_compact hBound.isCompact_closure
    (fun p : (Fin n × Fin n) × Fin n => coordinateDerivative (a p.1) (hA p.1) p.2) hDA
  let A := max B M
  have hA0 : 0 ≤ A := hB.trans (le_max_left _ _)
  have hVal (j k : Fin n) (x : Domain n) (hx : x ∈ V.val) : |a (j,k) x| ≤ A :=
    (hBAll (j,k) x (subset_closure hx)).trans (le_max_left _ _)
  have hDer (j k i : Fin n) (x : Domain n) (hx : x ∈ V.val) :
      |coordinateDerivative (a (j,k)) (hA (j,k)) i x| ≤ A :=
    (hMAll ((j,k),i) x (subset_closure hx)).trans (le_max_right _ _)
  let C := (n : ℝ)*A*(1+L)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro D H E hW hWE hHE
  let d (k : Fin n) (x : Domain n) := ambientGradientPullback F D (F.symm x) k
  let G (k : Fin n) := ambientGradientPullback F.symm (fun x => H x k)
  have hDtrans (k : Fin n) := hTransport (hW k) E (hHE k)
  have hd (k : Fin n) : MemW12 V (d k) (G k) := (hDtrans k).1
  have hdN (k : Fin n) : lpNorm (d k) 2 (volume.restrict V.val) ≤ E :=
    (hDtrans k).2.1.le.trans (hWE k)
  let e (j k i : Fin n) (x : Domain n) :=
    coordinateDerivative (a (j,k)) (hA (j,k)) i x • d k x + a (j,k) x • G k x i
  have haTop (j k : Fin n) : MemLp (a (j,k)) ∞ (volume.restrict V.val) :=
    contDiff_norm_bound_memLp_top V.property.measurableSet (hA (j,k)).continuous (hVal j k)
  have hdaTop (j k i : Fin n) :
      MemLp (coordinateDerivative (a (j,k)) (hA (j,k)) i) ∞ (volume.restrict V.val) :=
    contDiff_norm_bound_memLp_top V.property.measurableSet (hDA ((j,k),i)) (hDer j k i)
  have hValueLp (j k : Fin n) : MemLp (fun x => a (j,k) x • d k x) 2 (volume.restrict V.val) :=
    (hd k).2.1.smul (r := (2 : ℝ≥0∞)) (haTop j k)
  have he (j k i : Fin n) :
      MemLp (e j k i) 2 (volume.restrict V.val) ∧
      lpNorm (e j k i) 2 (volume.restrict V.val) ≤ A*(1+L)*E ∧
      IsWeakAmbientCoordinatePartial V.val i (fun x => a (j,k) x • d k x) (e j k i) := by
    obtain ⟨hLp,hLpN⟩ := lpNorm_smoothCoefficient_derivative_le V.property.measurableSet
      (hd k).2.1 ((hd k).2.2 i) (hA (j,k)) A hA0 (hVal j k) (hDer j k i)
    refine ⟨hLp,hLpN.trans ?_,?_⟩
    · refine (mul_le_mul_of_nonneg_left (add_le_add (hdN k) ((hDtrans k).2.2 i)) hA0).trans_eq ?_
      ring
    · exact IsWeakAmbientCoordinatePartial.smul_smooth ((hd k).1.2.2 i)
        (hd k).2.1 ((hd k).2.2 i) (hA (j,k)) (haTop j k) (hdaTop j k i)
  let K (x : Domain n) (j i : Fin n) := ∑ k : Fin n, e j k i x
  have hRewrite (j : Fin n) : (fun x => ∑ k : Fin n, a (j,k) x • d k x) = fun x => D x j :=
    funext fun x => ambientGradientPullback_symm_pullback F hF hInv D x j
  have hK (j i : Fin n) := lpNorm_finsetSum_le_card_mul Finset.univ
    (fun k _ => (he j k i).1) (fun k _ => (he j k i).2.1)
  refine ⟨K,fun j => ⟨?_,fun i => ?_⟩⟩
  · apply memW12_of_ambient_coordinate_partials V
    · rw [← hRewrite j]
      exact memLp_finsetSum _ (fun k _ => hValueLp j k)
    · exact fun i => (hK j i).1
    · intro i
      rw [← hRewrite j]
      exact IsWeakAmbientCoordinatePartial.finset_sum Finset.univ
        (fun k _ => (he j k i).2.2) (fun k _ => hValueLp j k) (fun k _ => (he j k i).1)
  · simpa only [K,C,Finset.card_univ,Fintype.card_fin,mul_assoc] using (hK j i).2

end Thesis
