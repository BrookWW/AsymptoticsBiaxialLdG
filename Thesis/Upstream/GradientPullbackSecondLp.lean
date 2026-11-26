module

public import Thesis.Upstream.GradientPullbackSecondColumns
import StratificationTheory.Foundation.SmoothOpenDomainSobolevPullback

/-! Transport of the fourth-integrable second weak columns back to physical coordinates. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set StratificationTheory
open scoped BigOperators ContDiff ENNReal

namespace Thesis

private theorem memLp_top_continuous_bounded_patch {n : ℕ} (V : OpenDomain n)
    (hV : Bornology.IsBounded V.val) {f : Domain n → ℝ} (hf : Continuous f) :
    MemLp f ⊤ (volume.restrict V.val) := by
  obtain ⟨C,hC⟩ := hV.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  exact memLp_top_of_bound hf.aestronglyMeasurable C
    ((ae_restrict_mem V.property.measurableSet).mono fun x hx => hC x (subset_closure hx))

theorem memLp_ambientGradientPullback_columns {n q : ℕ} {p : ℝ≥0∞}
    (F : Domain n ≃ₜ Domain n) (hF : ContDiff ℝ ∞ (F : Domain n → Domain n))
    (V W : OpenDomain n) (hV : Bornology.IsBounded V.val)
    (hMP : MeasurePreserving F (volume.restrict V.val) (volume.restrict W.val))
    {D : Domain n → HarmonicMaps.Gradient n q}
    (hD : ∀ j, MemLp (fun x => D x j) p (volume.restrict W.val)) (i : Fin n) :
    MemLp (fun x => ambientGradientPullback F D x i) p (volume.restrict V.val) := by
  unfold ambientGradientPullback
  apply memLp_finsetSum
  intro j _
  have hC : MemLp (fun x => fderiv ℝ F x (EuclideanSpace.single i 1) j) ⊤ (volume.restrict V.val) :=
    memLp_top_continuous_bounded_patch V hV
      ((EuclideanSpace.proj j).continuous.comp ((hF.continuous_fderiv (by simp)).clm_apply continuous_const))
  exact ((hD j).comp_measurePreserving hMP).smul (r := p) hC

/-- If the displayed flat first and second weak columns belong to a
second exponent, the same physical second weak columns do as well. -/
theorem memW12_secondColumns_withLp_of_gradientPullback {n q : ℕ} {p : ℝ≥0∞}
    (F : Domain n ≃ₜ Domain n) (hF : ContDiff ℝ ∞ (F : Domain n → Domain n))
    (hInv : ContDiff ℝ ∞ (F.symm : Domain n → Domain n))
    (V W : OpenDomain n) (hBound : Bornology.IsBounded V.val)
    (hInto : MapsTo F.symm V.val W.val)
    (hMP : MeasurePreserving F.symm (volume.restrict V.val) (volume.restrict W.val))
    (D : Domain n → HarmonicMaps.Gradient n q)
    (H : Domain n → Fin n → HarmonicMaps.Gradient n q)
    (hW : ∀ j, MemW12 W (fun x => ambientGradientPullback F D x j) (fun x => H x j))
    (hD : ∀ j, MemLp (fun x => ambientGradientPullback F D x j) p (volume.restrict W.val))
    (hH : ∀ j i, MemLp (fun x => H x j i) p (volume.restrict W.val)) :
    ∃ K : Domain n → Fin n → HarmonicMaps.Gradient n q,
      ∀ j, MemW12 V (fun x => D x j) (fun x => K x j) ∧
        ∀ i, MemLp (fun x => K x j i) p (volume.restrict V.val) := by
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict V.val) :=
    isFiniteMeasure_restrict.mpr hBound.measure_lt_top.ne
  let d (j : Fin n) (x : Domain n) := ambientGradientPullback F D (F.symm x) j
  let G (j : Fin n) := ambientGradientPullback F.symm (fun x => H x j)
  obtain ⟨M,hM⟩ := hBound.isCompact_closure.exists_bound_of_continuousOn
    (hInv.continuous_fderiv (by simp)).continuousOn
  have hWeak (j : Fin n) : MemW12 V (d j) (G j) := by
    apply memW12_smooth_open_domain_pullback (hW j) V F.symm hInv.contDiffOn hInto M
      (fun x hx => hM x (subset_closure hx)) 1 ENNReal.one_ne_top
    rw [one_smul,hMP.map_eq]
  have hd (j : Fin n) : MemLp (d j) p (volume.restrict V.val) :=
    (hD j).comp_measurePreserving hMP
  have hG (j i : Fin n) : MemLp (fun x => G j x i) p (volume.restrict V.val) :=
    memLp_ambientGradientPullback_columns F.symm hInv V W hBound hMP (hH j) i
  let a (j k : Fin n) (x : Domain n) := fderiv ℝ F.symm x (EuclideanSpace.single j 1) k
  have ha (j k : Fin n) : ContDiff ℝ ∞ (a j k) := (EuclideanSpace.proj k).contDiff.comp
    ((hInv.fderiv_right (by simp)).clm_apply contDiff_const)
  have haTop (j k : Fin n) : MemLp (a j k) ⊤ (volume.restrict V.val) :=
    memLp_top_continuous_bounded_patch V hBound (ha j k).continuous
  have hdaTop (j k i : Fin n) :
      MemLp (coordinateDerivative (a j k) (ha j k) i) ⊤ (volume.restrict V.val) :=
    memLp_top_continuous_bounded_patch V hBound
      (((ha j k).continuous_fderiv (by simp)).clm_apply continuous_const)
  let e (j k i : Fin n) (x : Domain n) :=
    coordinateDerivative (a j k) (ha j k) i x • d k x + a j k x • G k x i
  have hE (j k i : Fin n) : MemLp (e j k i) p (volume.restrict V.val) :=
    ((hd k).smul (r := p) (hdaTop j k i)).add ((hG k i).smul (r := p) (haTop j k))
  have hE₂ (j k i : Fin n) : MemLp (e j k i) 2 (volume.restrict V.val) :=
    ((hWeak k).2.1.smul (r := 2) (hdaTop j k i)).add (((hWeak k).2.2 i).smul (r := 2) (haTop j k))
  have hWeakVal (j k : Fin n) : MemLp (fun x => a j k x • d k x) 2 (volume.restrict V.val) :=
    (hWeak k).2.1.smul (r := 2) (haTop j k)
  have hWeakPart (j k i : Fin n) :
      IsWeakAmbientCoordinatePartial V.val i (fun x => a j k x • d k x) (e j k i) :=
    IsWeakAmbientCoordinatePartial.smul_smooth ((hWeak k).1.2.2 i)
      (hWeak k).2.1 ((hWeak k).2.2 i) (ha j k) (haTop j k) (hdaTop j k i)
  let K (x : Domain n) (j i : Fin n) := ∑ k : Fin n, e j k i x
  have hRewrite (j : Fin n) : (fun x => ∑ k : Fin n, a j k x • d k x) = fun x => D x j :=
    funext fun x => ambientGradientPullback_symm_pullback F hF hInv D x j
  refine ⟨K,fun j => ⟨?_,fun i => memLp_finsetSum _ (fun k _ => hE j k i)⟩⟩
  apply memW12_of_ambient_coordinate_partials V
  · rw [← hRewrite j]
    exact memLp_finsetSum _ (fun k _ => hWeakVal j k)
  · exact fun i => memLp_finsetSum _ (fun k _ => hE₂ j k i)
  · intro i
    rw [← hRewrite j]
    exact IsWeakAmbientCoordinatePartial.finset_sum _ (fun k _ => hWeakPart j k i)
      (fun k _ => hWeakVal j k) (fun k _ => hE₂ j k i)

end Thesis
