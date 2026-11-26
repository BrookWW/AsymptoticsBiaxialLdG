module

public import Thesis.Upstream.AmbientWeakCoordinateColumnFour
public import Thesis.Upstream.LocalSobolevGradientTransport
import HarmonicMaps.Analysis.SobolevAECongruence

/-! Normal completion of the third weak graph in a flat elliptic chart. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

private theorem weakAmbientHessian_symm {n q : ℕ} (V : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict V.val)]
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    {H : Domain n → Fin n → HarmonicMaps.Gradient n q}
    (hu : HasWeakGradient V u D)
    (hD : ∀ i, MemW12 V (fun x => D x i) (fun x => H x i))
    (i j : Fin n) :
    (fun x => H x i j) =ᵐ[volume.restrict V.val] fun x => H x j i := by
  have hOther : MemW12 V (fun x => D x i) (fun x k => H x k i) :=
    memW12_of_ambient_coordinate_partials V (hD i).2.1
      (fun k => (hD k).2.2 i)
      (fun k => IsWeakAmbientCoordinatePartial.mixed hu ((hD k).1.2.2 i))
  exact ((hD i).1.ae_eq hOther.1).mono (fun x hx => congrFun hx j)

/-- Tangential third derivatives, the differentiated forcing, and the
strong elliptic equation recover every original third weak column. The
only unrecovered entry is the all-normal derivative, solved by dividing
the normal diagonal coefficient in the differentiated equation. -/
theorem exists_thirdWeakColumns_four_of_tangential_metric {n q : ℕ} (V : OpenDomain n)
    (hV : Bornology.IsBounded V.val) (p : Fin n)
    {u f : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    {H : Domain n → Fin n → HarmonicMaps.Gradient n q}
    (hu : HasWeakGradient V u D)
    (hD : ∀ j, MemW12 V (fun x => D x j) (fun x => H x j))
    (hD₄ : ∀ j, MemLp (fun x => D x j) 4 (volume.restrict V.val))
    (hH₄ : ∀ i j, MemLp (fun x => H x i j) 4 (volume.restrict V.val))
    {Fp : Domain n → Ambient q} (hF : HasWeakAmbientCoordinateColumnFour V.val p f Fp)
    (A : Domain n → Fin n → Fin n → ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hNon : ∀ x ∈ V.val, A x p p ≠ 0)
    (hInv : ContDiff ℝ ∞ (fun x => (A x p p)⁻¹))
    (hEq : (fun x => ∑ i : Fin n, ∑ j : Fin n,
      (coordinateDerivative (fun y => A y i j) (hA i j) i x • D x j + A x i j • H x j i))
      =ᵐ[volume.restrict V.val] f)
    (T : {k : Fin n // k ≠ p} → Domain n → Fin n → HarmonicMaps.Gradient n q)
    (hT : ∀ k i j, HasWeakAmbientCoordinateColumnFour V.val k.val (fun x => H x i j) (fun x => T k x i j)) :
    ∃ K : Domain n → Fin n → Fin n → HarmonicMaps.Gradient n q,
      ∀ i j, MemW12 V (fun x => H x i j) (fun x => K x i j) ∧
        ∀ k, MemLp (fun x => K x i j k) 4 (volume.restrict V.val) := by
  classical
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict V.val) :=
    isFiniteMeasure_restrict.mpr hV.measure_lt_top.ne
  let N (i j : Fin n) (x : Domain n) :=
    if hj : j ≠ p then T ⟨j,hj⟩ x i p else if hi : i ≠ p then T ⟨i,hi⟩ x p p else 0
  have hN (i j : Fin n) (h : i ≠ p ∨ j ≠ p) :
      HasWeakAmbientCoordinateColumnFour V.val p (fun x => H x i j) (N i j) := by
    by_cases hj : j ≠ p
    · have ht := hT ⟨j,hj⟩ i p
      have hW := IsWeakAmbientCoordinatePartial.mixed (hD i).1 ht.weak
      simpa only [N,dif_pos hj] using
        (show HasWeakAmbientCoordinateColumnFour V.val p (fun x => H x i j) (fun x => T ⟨j,hj⟩ x i p) from
          ⟨(hD i).2.2 j,hH₄ i j,ht.derivativeTwo,ht.derivativeFour,hW⟩)
    · have hi : i ≠ p := h.resolve_right hj
      have hj' : j = p := not_ne_iff.mp hj
      subst j
      have ht := hT ⟨i,hi⟩ p p
      have hW := IsWeakAmbientCoordinatePartial.mixed (hD p).1 ht.weak
      have hData : HasWeakAmbientCoordinateColumnFour V.val p
          (fun x => H x p i) (fun x => T ⟨i,hi⟩ x p p) :=
        ⟨(hD p).2.2 i,hH₄ p i,ht.derivativeTwo,ht.derivativeFour,hW⟩
      simpa only [N,dif_neg (not_not_intro rfl),dif_pos hi] using
        hData.congr_value_ae (weakAmbientHessian_symm V hu hD p i)
  have hFirst (j : Fin n) :
      HasWeakAmbientCoordinateColumnFour V.val p (fun x => D x j) (fun x => H x j p) :=
    ⟨(hD j).2.1,hD₄ j,(hD j).2.2 p,hH₄ j p,(hD j).1.2.2 p⟩
  let Pairs := Fin n × Fin n
  let S : Finset Pairs := Finset.univ
  let R := S.erase (p,p)
  let a (m : Pairs) (x : Domain n) := A x m.1 m.2
  let b (m : Pairs) := coordinateDerivative (a m) (hA m.1 m.2) m.1
  have hb (m : Pairs) : ContDiff ℝ ∞ (b m) :=
    ((hA m.1 m.2).fderiv_right (by simp)).clm_apply contDiff_const
  let L (x : Domain n) := ∑ m ∈ S, b m x • D x m.2
  let dL (x : Domain n) := ∑ m ∈ S,
    (coordinateDerivative (b m) (hb m) p x • D x m.2 + b m x • H x m.2 p)
  have hL : HasWeakAmbientCoordinateColumnFour V.val p L dL :=
    HasWeakAmbientCoordinateColumnFour.finset_sum S (fun m _ =>
      (hFirst m.2).smul_smooth V.property.measurableSet hV (hb m))
  have hRpair (m : Pairs) (hm : m ∈ R) : m.2 ≠ p ∨ m.1 ≠ p := by
    have he : m ≠ (p,p) := (Finset.mem_erase.mp hm).1
    by_contra h
    obtain ⟨h₂,h₁⟩ := not_or.mp h
    exact he (Prod.ext (not_ne_iff.mp h₁) (not_ne_iff.mp h₂))
  let W (x : Domain n) := ∑ m ∈ R, a m x • H x m.2 m.1
  let dW (x : Domain n) := ∑ m ∈ R,
    (coordinateDerivative (a m) (hA m.1 m.2) p x • H x m.2 m.1 + a m x • N m.2 m.1 x)
  have hW : HasWeakAmbientCoordinateColumnFour V.val p W dW :=
    HasWeakAmbientCoordinateColumnFour.finset_sum R (fun m hm =>
      (hN m.2 m.1 (hRpair m hm)).smul_smooth V.property.measurableSet hV (hA m.1 m.2))
  let Z := f-L-W
  let dZ := Fp-dL-dW
  have hZ : HasWeakAmbientCoordinateColumnFour V.val p Z dZ := (hF.sub hL).sub hW
  let I (x : Domain n) := (A x p p)⁻¹
  let E (x : Domain n) := coordinateDerivative I hInv p x • Z x + I x • dZ x
  have hActual : (fun x => I x • Z x) =ᵐ[volume.restrict V.val] fun x => H x p p := by
    filter_upwards [hEq,ae_restrict_mem (μ := volume) V.property.measurableSet] with x he hx
    have he' : L x + (∑ m : Pairs, a m x • H x m.2 m.1) = f x := by
      simp only [L,S,a,b,Pairs,Fintype.sum_prod_type] at *
      simpa only [Finset.sum_add_distrib] using he
    have hAdd : (∑ m : Pairs, a m x • H x m.2 m.1) = A x p p • H x p p + W x :=
      (Finset.add_sum_erase S (fun m => a m x • H x m.2 m.1) (Finset.mem_univ (p,p))).symm
    have hz : Z x = A x p p • H x p p := by
      change f x-L x-W x = _
      rw [hAdd] at he'
      rw [← he']
      abel
    change (A x p p)⁻¹ • Z x = _
    rw [hz,smul_smul,inv_mul_cancel₀ (hNon x hx),one_smul]
  have hNpp : HasWeakAmbientCoordinateColumnFour V.val p (fun x => H x p p) E :=
    (hZ.smul_smooth V.property.measurableSet hV hInv).congr_value_ae hActual
  let K (x : Domain n) (i j k : Fin n) :=
    if hk : k ≠ p then T ⟨k,hk⟩ x i j else if i = p ∧ j = p then E x else N i j x
  have hK (i j k : Fin n) :
      HasWeakAmbientCoordinateColumnFour V.val k (fun x => H x i j) (fun x => K x i j k) := by
    by_cases hk : k ≠ p
    · simpa only [K,dif_pos hk] using hT ⟨k,hk⟩ i j
    · have hk' : k = p := not_ne_iff.mp hk
      subst k
      by_cases h : i = p ∧ j = p
      · obtain ⟨rfl,rfl⟩ := h
        simpa only [K,dif_neg (not_not_intro rfl),if_true,and_self] using hNpp
      · simpa only [K,dif_neg (not_not_intro rfl),if_neg h] using hN i j (not_and_or.mp h)
  refine ⟨K,fun i j => ⟨?_,fun k => (hK i j k).derivativeFour⟩⟩
  exact memW12_of_ambient_coordinate_partials V ((hD i).2.2 j)
    (fun k => (hK i j k).derivativeTwo) (fun k => (hK i j k).weak)

end Thesis
