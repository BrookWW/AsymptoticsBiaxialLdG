module

public import Thesis.Variational.FlatWallWeakHessianCutoff
public import Thesis.Upstream.AmbientStrongNondivergence

/-! The actual strong forcing after a smooth metric cutoff. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

/-- The first-order term obtained by expanding the smooth divergence metric. -/
@[expose] def flatWeakMetricLowerRow {q : ℕ} (A : Point → Fin 3 → Fin 3 → ℝ)
    (D : Point → HarmonicMaps.Gradient 3 q) (x : Point) : Ambient q :=
  ∑ i : Fin 3, ∑ j : Fin 3, coordDeriv i (fun y => A y i j) x • D x j

/-- The contribution to a second weak derivative from differentiating a cutoff. -/
@[expose] def weakMetricCutoffCross {q : ℕ} (χ : Point → ℝ) (u : Point → Ambient q)
    (D : Point → HarmonicMaps.Gradient 3 q) (x : Point) (i j : Fin 3) : Ambient q :=
  coordDeriv j (coordDeriv i χ) x • u x+
    coordDeriv i χ x • D x j+coordDeriv j χ x • D x i

/-- The nondivergence forcing of the cut-off field on the original flat side. -/
@[expose] def flatWeakMetricCutoffForcing {q : ℕ} (A : Point → Fin 3 → Fin 3 → ℝ)
    (χ : Point → ℝ) (u f : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q)
    (x : Point) : Ambient q :=
  χ x • (f x-flatWeakMetricLowerRow A D x) +
    ∑ i : Fin 3, ∑ j : Fin 3, A x j i • weakMetricCutoffCross χ u D x i j

private theorem memLp_top_continuous_on_bounded {V : Set Point} (hV : MeasurableSet V)
    (hB : Bornology.IsBounded V) {g : Point → ℝ} (hg : Continuous g) :
    MemLp g ⊤ (volume.restrict V) := by
  obtain ⟨C,hC⟩ := hB.isCompact_closure.exists_bound_of_continuousOn hg.continuousOn
  exact memLp_top_of_bound hg.aestronglyMeasurable C
    ((ae_restrict_mem hV).mono fun x hx => hC x (subset_closure hx))

/-- The cut-off forcing belongs to each original data exponent on every
bounded patch on which the value and first columns have that exponent. -/
theorem memLp_flatWeakMetricCutoffForcing {q : ℕ} {V : Set Point} (hV : MeasurableSet V)
    (hB : Bornology.IsBounded V)
    {A : Point → Fin 3 → Fin 3 → ℝ} (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    {χ : Point → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {u f : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q} {p : ℝ≥0∞}
    (hu : MemLp u p (volume.restrict V)) (hf : MemLp f p (volume.restrict V))
    (hD : ∀ i, MemLp (fun x => D x i) p (volume.restrict V)) :
    MemLp (flatWeakMetricCutoffForcing A χ u f D) p (volume.restrict V) := by
  have hder {g : Point → ℝ} (hg : ContDiff ℝ ∞ g) (j : Fin 3) : ContDiff ℝ ∞ (coordDeriv j g) :=
    (hg.fderiv_right (by simp)).clm_apply contDiff_const
  have hTop {g : Point → ℝ} (hg : Continuous g) : MemLp g ⊤ (volume.restrict V) :=
    memLp_top_continuous_on_bounded hV hB hg
  have hLo : MemLp (flatWeakMetricLowerRow A D) p (volume.restrict V) := by
    apply memLp_finsetSum
    intro i _
    apply memLp_finsetSum
    intro j _
    exact (hD j).smul (r := p) (hTop (hder (hA i j) i).continuous)
  have hCross (i j : Fin 3) : MemLp (fun x => weakMetricCutoffCross χ u D x i j) p (volume.restrict V) :=
    ((hu.smul (r := p) (hTop (hder (hder hχ i) j).continuous)).add
      ((hD j).smul (r := p) (hTop (hder hχ i).continuous))).add
      ((hD i).smul (r := p) (hTop (hder hχ j).continuous))
  have hHi : MemLp (fun x => ∑ i : Fin 3, ∑ j : Fin 3, A x j i • weakMetricCutoffCross χ u D x i j)
      p (volume.restrict V) := by
    apply memLp_finsetSum
    intro i _
    apply memLp_finsetSum
    intro j _
    exact (hCross i j).smul (r := p) (hTop (hA j i).continuous)
  exact ((hf.sub hLo).smul (r := p) (hTop hχ.continuous)).add hHi

private theorem metric_cutoff_hessian_linearization {q : ℕ} (A : Point → Fin 3 → Fin 3 → ℝ)
    (χ : Point → ℝ) (u : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q)
    (H : Point → Fin 3 → HarmonicMaps.Gradient 3 q) (x : Point) :
    (∑ i : Fin 3, ∑ j : Fin 3, A x j i • localWeakCutoffHessian χ u D H x i j) =
      χ x • (∑ i : Fin 3, ∑ j : Fin 3, A x i j • H x j i) +
        ∑ i : Fin 3, ∑ j : Fin 3, A x j i • weakMetricCutoffCross χ u D x i j := by
  have hTerm (i j : Fin 3) : A x j i • localWeakCutoffHessian χ u D H x i j =
      χ x • (A x j i • H x i j)+A x j i • weakMetricCutoffCross χ u D x i j := by
    simp only [localWeakCutoffHessian,weakMetricCutoffCross,smul_add,smul_smul,mul_comm]
    abel
  simp only [hTerm,Finset.sum_add_distrib]
  simp only [Finset.smul_sum]
  congr 1
  exact (Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))) (t := Finset.univ))

/-- The trace of the actual cut-off Hessian equals its local forcing plus
the deviation of the weighted trace from the Euclidean trace. -/
theorem flatWeakMetricCutoff_strong_trace {q : ℕ}
    (A : Point → Fin 3 → Fin 3 → ℝ) (χ : Point → ℝ)
    (u f : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q)
    (H : Point → Fin 3 → HarmonicMaps.Gradient 3 q) (x : Point)
    (hEq : (∑ i : Fin 3, ∑ j : Fin 3,
      (coordDeriv i (fun y => A y i j) x • D x j + A x i j • H x j i)) = f x) :
    (∑ i : Fin 3, localWeakCutoffHessian χ u D H x i i) =
      flatWeakMetricCutoffForcing A χ u f D x +
        ∑ i : Fin 3, ∑ j : Fin 3,
          ((if i = j then 1 else 0)-A x j i) • localWeakCutoffHessian χ u D H x i j := by
  classical
  let J := localWeakCutoffHessian χ u D H
  have hWeighted : (∑ i : Fin 3, ∑ j : Fin 3, A x i j • H x j i) =
      f x-flatWeakMetricLowerRow A D x := by
    simp only [Finset.sum_add_distrib,flatWeakMetricLowerRow] at hEq ⊢
    rw [← hEq,add_sub_cancel_left]
  have hLin : (∑ i : Fin 3, ∑ j : Fin 3, A x j i • J x i j) =
      flatWeakMetricCutoffForcing A χ u f D x := by
    rw [metric_cutoff_hessian_linearization, hWeighted]
    rfl
  have hDiagonal (i : Fin 3) :
      (∑ j : Fin 3, (if i = j then (1 : ℝ) else 0) • J x i j) = J x i i := by
    simp only [ite_smul,one_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  change (∑ i : Fin 3, J x i i) = flatWeakMetricCutoffForcing A χ u f D x +
    ∑ i : Fin 3, ∑ j : Fin 3, ((if i = j then 1 else 0)-A x j i) • J x i j
  simp only [sub_smul,Finset.sum_sub_distrib,hDiagonal]
  rw [hLin]
  abel

end Thesis
