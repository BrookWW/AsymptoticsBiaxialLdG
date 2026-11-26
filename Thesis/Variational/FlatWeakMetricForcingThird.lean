module

public import Thesis.Variational.FlatWeakMetricCutoffForcing
import HarmonicMaps.Analysis.SobolevDifference
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! The differentiated forcing of a compact flat Dirichlet Hessian graph. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

structure MemW12Four {q : ℕ} (V : OpenDomain 3) (u : Point → Ambient q)
    (D : Point → HarmonicMaps.Gradient 3 q) : Prop where
  weak : MemW12 V u D
  valueFour : MemLp u 4 (volume.restrict V.val)
  columnFour : ∀ i, MemLp (fun x => D x i) 4 (volume.restrict V.val)

theorem MemW12Four.add {q : ℕ} {V : OpenDomain 3}
    {u v : Point → Ambient q} {D E : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12Four V u D) (hv : MemW12Four V v E) :
    MemW12Four V (fun x => u x+v x) (fun x i => D x i+E x i) :=
  ⟨memW12_add_pair hu.weak hv.weak,
    hu.valueFour.add hv.valueFour,fun i => (hu.columnFour i).add (hv.columnFour i)⟩

theorem MemW12Four.sub {q : ℕ} {V : OpenDomain 3}
    {u v : Point → Ambient q} {D E : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12Four V u D) (hv : MemW12Four V v E) :
    MemW12Four V (fun x => u x-v x) (fun x i => D x i-E x i) :=
  ⟨hu.weak.sub hv.weak,hu.valueFour.sub hv.valueFour,fun i => (hu.columnFour i).sub (hv.columnFour i)⟩

theorem MemW12Four.finsetSum {q : ℕ} {V : OpenDomain 3} {ι : Type*} (s : Finset ι)
    {u : ι → Point → Ambient q} {D : ι → Point → HarmonicMaps.Gradient 3 q}
    (h : ∀ j ∈ s, MemW12Four V (u j) (D j)) :
    MemW12Four V (fun x => ∑ j ∈ s, u j x) (fun x i => ∑ j ∈ s, D j x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change MemW12Four V (0 : Point → Ambient q) (0 : Point → HarmonicMaps.Gradient 3 q)
    exact ⟨MemW12.zero V,MemLp.zero,fun _ => MemLp.zero⟩
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

private theorem memLp_four_mul_relative_cutoff {q : ℕ} {V W : OpenDomain 3}
    {u : Point → Ambient q} (hu : MemLp u 4 (volume.restrict (V.val∩W.val)))
    {χ : Point → ℝ} (hχ : MemLp χ ⊤ (volume.restrict V.val)) (hχS : tsupport χ ⊆ W.val) :
    MemLp (fun x => χ x • u x) 4 (volume.restrict V.val) := by
  have hμ : (volume.restrict V.val).restrict W.val = volume.restrict (V.val∩W.val) := by
    rw [Measure.restrict_restrict W.property.measurableSet,inter_comm]
  have hExt : MemLp (W.val.indicator u) 4 (volume.restrict V.val) :=
    (memLp_indicator_iff_restrict W.property.measurableSet).2 (hμ.symm ▸ hu)
  refine MemLp.ae_eq ?_ (hExt.smul (r := 4) hχ)
  apply Eventually.of_forall
  intro x
  change χ x • W.val.indicator u x = χ x • u x
  by_cases hx : x ∈ W.val
  · rw [indicator_of_mem hx]
  · simp only [image_eq_zero_of_notMem_tsupport (fun h => hx (hχS h)),zero_smul]

private theorem MemW12Four.smul_relative_cutoff {q : ℕ} {V W : OpenDomain 3}
    (hW : Bornology.IsBounded W.val) {u : Point → Ambient q}
    {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12Four ⟨V.val∩W.val,V.property.inter W.property⟩ u D)
    {χ : Point → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hχS : tsupport χ ⊆ W.val) :
    MemW12Four V (fun x => χ x • u x)
      (fun x i => coordDeriv i χ x • u x+χ x • D x i) := by
  have hTop := hχ.continuous.memLp_top_of_hasCompactSupport hc (volume.restrict V.val)
  refine ⟨memW12_smul_relative_cutoff hW hu.weak hχ hc hχS,
    memLp_four_mul_relative_cutoff hu.valueFour hTop hχS,fun i => ?_⟩
  have hD : ContDiff ℝ ∞ (coordDeriv i χ) := (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hcD : HasCompactSupport (coordDeriv i χ) := hc.fderiv_apply ℝ (axis i)
  exact (memLp_four_mul_relative_cutoff hu.valueFour
    (hD.continuous.memLp_top_of_hasCompactSupport hcD _) ((tsupport_fderiv_apply_subset ℝ (axis i)).trans hχS)).add
    (memLp_four_mul_relative_cutoff (hu.columnFour i) hTop hχS)

/-- The cutoff forcing inherits one actual weak derivative in both
exponents from the original force and its first two weak graph levels. -/
theorem exists_weakGradient_four_flatWeakMetricCutoffForcing {q : ℕ} (W : OpenDomain 3)
    (hW : Bornology.IsBounded W.val)
    (A : Point → Fin 3 → Fin 3 → ℝ) (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    {χ : Point → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hχS : tsupport χ ⊆ W.val)
    {u f : Point → Ambient q} {D F : Point → HarmonicMaps.Gradient 3 q}
    {H : Point → Fin 3 → HarmonicMaps.Gradient 3 q}
    (hSource : let V : OpenDomain 3 := ⟨upperCoordinateHalfSpace.val∩W.val,upperCoordinateHalfSpace.property.inter W.property⟩
      MemW12 V u D ∧ MemLp u 4 (volume.restrict V.val) ∧
      (∀ i, MemLp (fun x => D x i) 4 (volume.restrict V.val)) ∧
      (∀ i, MemW12 V (fun x => D x i) (fun x => H x i)) ∧
      (∀ i j, MemLp (fun x => H x i j) 4 (volume.restrict V.val)) ∧
      MemW12 V f F ∧ MemLp f 4 (volume.restrict V.val) ∧
      (∀ i, MemLp (fun x => F x i) 4 (volume.restrict V.val))) :
    ∃ E : Point → HarmonicMaps.Gradient 3 q,
      MemW12 upperCoordinateHalfSpace (flatWeakMetricCutoffForcing A χ u f D) E ∧
      MemLp (flatWeakMetricCutoffForcing A χ u f D) 4 (volume.restrict upperCoordinateHalfSpace.val) ∧
      ∀ i, MemLp (fun x => E x i) 4 (volume.restrict upperCoordinateHalfSpace.val) := by
  obtain ⟨hu,hu₄,hD₄,hD,hH₄,hf,hf₄,hF₄⟩ := hSource
  let S := upperCoordinateHalfSpace
  let V : OpenDomain 3 := ⟨S.val∩W.val,S.property.inter W.property⟩
  have hu' : MemW12Four V u D := ⟨hu,hu₄,hD₄⟩
  have hf' : MemW12Four V f F := ⟨hf,hf₄,hF₄⟩
  have hD' (i : Fin 3) : MemW12Four V (fun x => D x i) (fun x => H x i) :=
    ⟨hD i,hD₄ i,hH₄ i⟩
  have hder {a : Point → ℝ} (ha : ContDiff ℝ ∞ a) (i : Fin 3) :
      ContDiff ℝ ∞ (coordDeriv i a) := (ha.fderiv_right (by simp)).clm_apply contDiff_const
  let b (i j : Fin 3) := coordDeriv i (fun x => A x i j)
  let cL (i j : Fin 3) (x : Point) := χ x*b i j x
  let cU (i j : Fin 3) (x : Point) := A x j i*coordDeriv j (coordDeriv i χ) x
  let cD (i j : Fin 3) (x : Point) := A x j i*coordDeriv i χ x
  let cE (i j : Fin 3) (x : Point) := A x j i*coordDeriv j χ x
  have hb (i j : Fin 3) : ContDiff ℝ ∞ (b i j) := hder (hA i j) i
  have hχD (i : Fin 3) : tsupport (coordDeriv i χ) ⊆ W.val :=
    (tsupport_fderiv_apply_subset ℝ (axis i)).trans hχS
  have hχDD (i j : Fin 3) : tsupport (coordDeriv j (coordDeriv i χ)) ⊆ W.val :=
    (tsupport_fderiv_apply_subset ℝ (axis j)).trans (hχD i)
  have hL (i j : Fin 3) := (hD' j).smul_relative_cutoff hW
    (hχ.mul (hb i j)) hc.mul_right (tsupport_mul_subset_left.trans hχS)
  have hU (i j : Fin 3) := hu'.smul_relative_cutoff hW
    ((hA j i).mul (hder (hder hχ i) j))
    ((hc.fderiv_apply ℝ (axis i)).fderiv_apply ℝ (axis j)).mul_left
    (tsupport_mul_subset_right.trans (hχDD i j))
  have hC (i j : Fin 3) := (hD' j).smul_relative_cutoff hW
    ((hA j i).mul (hder hχ i)) ((hc.fderiv_apply ℝ (axis i)).mul_left)
    (tsupport_mul_subset_right.trans (hχD i))
  have hE (i j : Fin 3) := (hD' i).smul_relative_cutoff hW
    ((hA j i).mul (hder hχ j)) ((hc.fderiv_apply ℝ (axis j)).mul_left)
    (tsupport_mul_subset_right.trans (hχD j))
  let L (x : Point) := ∑ m : Fin 3 × Fin 3, cL m.1 m.2 x • D x m.2
  let B (x : Point) := ∑ m : Fin 3 × Fin 3,
    (cU m.1 m.2 x • u x+cD m.1 m.2 x • D x m.2+cE m.1 m.2 x • D x m.1)
  have hL' := MemW12Four.finsetSum (V := S) Finset.univ (fun m : Fin 3 × Fin 3 => fun _ => hL m.1 m.2)
  have hB' := MemW12Four.finsetSum (V := S) Finset.univ
    (fun m : Fin 3 × Fin 3 => fun _ => ((hU m.1 m.2).add (hC m.1 m.2)).add (hE m.1 m.2))
  have hG := (((hf'.smul_relative_cutoff hW hχ hc hχS).sub hL').add hB')
  have hAlg : (fun x => χ x • f x-L x+B x) = flatWeakMetricCutoffForcing A χ u f D := by
    funext x
    dsimp only [L,B,flatWeakMetricCutoffForcing,flatWeakMetricLowerRow,weakMetricCutoffCross,cL,cU,cD,cE,b]
    simp only [Fintype.sum_prod_type,smul_sub,Finset.smul_sum,smul_add,smul_smul]
  have hh : MemW12Four S (fun x => χ x • f x-L x+B x) _ := hG
  rw [hAlg] at hh
  exact ⟨_,hh.weak,hh.valueFour,hh.columnFour⟩

/-- The cut-off forcing is supported by the original compact cutoff. -/
theorem tsupport_flatWeakMetricCutoffForcing_subset {q : ℕ}
    (A : Point → Fin 3 → Fin 3 → ℝ) (χ : Point → ℝ)
    (u f : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q) :
    tsupport (flatWeakMetricCutoffForcing A χ u f D) ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hx'
  have hz : χ x=0 := image_eq_zero_of_notMem_tsupport hx'
  have hD (i : Fin 3) : coordDeriv i χ x=0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx' ((tsupport_fderiv_apply_subset ℝ (axis i)) h))
  have hDD (i j : Fin 3) : coordDeriv j (coordDeriv i χ) x=0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hx' ((tsupport_fderiv_apply_subset ℝ (axis i))
        ((tsupport_fderiv_apply_subset ℝ (axis j)) h)))
  exact hx (by simp only [flatWeakMetricCutoffForcing,weakMetricCutoffCross,hz,hD,hDD,
    zero_smul,smul_zero,zero_add,Finset.sum_const_zero])

theorem hasCompactSupport_flatWeakMetricCutoffForcing {q : ℕ}
    (A : Point → Fin 3 → Fin 3 → ℝ) {χ : Point → ℝ} (hc : HasCompactSupport χ)
    (u f : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q) :
    HasCompactSupport (flatWeakMetricCutoffForcing A χ u f D) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_flatWeakMetricCutoffForcing_subset A χ u f D)

end Thesis
