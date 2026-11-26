module

public import Thesis.Variational.SmoothDomainLocalPoissonH2
import Thesis.Interpolation.OpenOverlapGluing

/-! Finite-cover assembly of the global Dirichlet second weak graph. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ENNReal

namespace Thesis

private theorem lpNorm_two_restrict_union_le {q : ℕ} {U V : Set Point} {z : Point → Ambient q}
    (hU : MemLp z 2 (volume.restrict U)) (hV : MemLp z 2 (volume.restrict V))
    (hUV : MemLp z 2 (volume.restrict (U ∪ V))) :
    lpNorm z 2 (volume.restrict (U ∪ V)) ≤
      lpNorm z 2 (volume.restrict U)+lpNorm z 2 (volume.restrict V) := by
  have hSqU := (memLp_two_iff_integrable_sq_norm hU.1).1 hU
  have hSqV := (memLp_two_iff_integrable_sq_norm hV.1).1 hV
  have hSq := integral_mono_measure (Measure.restrict_union_le (μ := volume) U V)
    (Eventually.of_forall fun x : Point => sq_nonneg ‖z x‖) (hSqU.add_measure hSqV)
  rw [integral_add_measure hSqU hSqV,← ambient_lpNorm_two_sq hUV,← ambient_lpNorm_two_sq hU,
    ← ambient_lpNorm_two_sq hV] at hSq
  have h₁ : 0 ≤ lpNorm z 2 (volume.restrict U) := lpNorm_nonneg
  have h₂ : 0 ≤ lpNorm z 2 (volume.restrict V) := lpNorm_nonneg
  apply (sq_le_sq₀ lpNorm_nonneg (add_nonneg h₁ h₂)).1
  nlinarith only [hSq,mul_nonneg h₁ h₂]

private theorem HasLocalSecondWeakColumns.union {q : ℕ} {U V : OpenDomain 3}
    {D : Point → HarmonicMaps.Gradient 3 q} {B₁ B₂ : ℝ}
    (hU : HasLocalSecondWeakColumns U D B₁) (hV : HasLocalSecondWeakColumns V D B₂) :
    HasLocalSecondWeakColumns ⟨U.val ∪ V.val,U.property.union V.property⟩ D (B₁+B₂) := by
  classical
  obtain ⟨G,hG⟩ := hU
  obtain ⟨H,hH⟩ := hV
  let W : OpenDomain 3 := ⟨U.val ∪ V.val,U.property.union V.property⟩
  let K (x : Point) := if x ∈ U.val then G x else H x
  have hD (j : Fin 3) : MemW12 W (fun x => D x j) (fun x => K x j) := by
    have hh := memW12_openOverlap_piecewise (Ω := W) (hG j).1 (hH j).1
      (subset_refl _) (fun _ _ => rfl)
    simpa only [ite_self,ite_apply,K] using hh
  refine ⟨K,fun j => ⟨hD j,fun i => ?_⟩⟩
  have hAE₁ : (fun x => G x j) =ᵐ[volume.restrict U.val] fun x => K x j := by
    filter_upwards [ae_restrict_mem U.property.measurableSet] with x hx
    simp only [K,if_pos hx]
  have hAE₂ : (fun x => H x j) =ᵐ[volume.restrict V.val] fun x => K x j := by
    let S : OpenDomain 3 := ⟨U.val ∩ V.val,U.property.inter V.property⟩
    have hWeak₁ : HasWeakGradient S (fun x => D x j) (fun x => G x j) :=
      (hG j).1.1.mono inter_subset_left
    have hWeak₂ : HasWeakGradient S (fun x => D x j) (fun x => H x j) :=
      (hH j).1.1.mono inter_subset_right
    have hAgree : ∀ᵐ x ∂volume.restrict V.val, x ∈ U.val → G x j = H x j := by
      apply (ae_restrict_iff' U.property.measurableSet).1
      rw [Measure.restrict_restrict U.property.measurableSet]
      exact hWeak₁.ae_eq hWeak₂
    filter_upwards [hAgree] with x hx
    change H x j = (if x ∈ U.val then G x else H x) j
    by_cases h : x ∈ U.val
    · rw [if_pos h,hx h]
    · rw [if_neg h]
  have hCol₁ := hAE₁.mono fun x hx => congrFun hx i
  have hCol₂ := hAE₂.mono fun x hx => congrFun hx i
  refine (lpNorm_two_restrict_union_le (MemLp.ae_eq hCol₁ ((hG j).1.2.2 i))
    (MemLp.ae_eq hCol₂ ((hH j).1.2.2 i)) ((hD j).2.2 i)).trans ?_
  rw [← ambient_lpNorm_congr_ae hCol₁,← ambient_lpNorm_congr_ae hCol₂]
  exact add_le_add ((hG j).2 i) ((hH j).2 i)

private theorem hasLocalSecondWeakColumns_finsetUnion {q : ℕ} {ι : Type*}
    (s : Finset ι) (V : ι → OpenDomain 3) (B : ι → ℝ) {D : Point → HarmonicMaps.Gradient 3 q}
    (h : ∀ j ∈ s, HasLocalSecondWeakColumns (V j) D (B j)) :
    HasLocalSecondWeakColumns
      ⟨⋃ j ∈ s, (V j).val,isOpen_iUnion (fun j => isOpen_iUnion fun _ => (V j).property)⟩
      D (∑ j ∈ s, B j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hEmpty : (⋃ j ∈ (∅ : Finset ι), (V j).val) = ∅ := by simp
    have hGraph : HasLocalSecondWeakColumns (⟨∅,isOpen_empty⟩ : OpenDomain 3) D 0 := by
      refine ⟨0,fun j => ⟨?_,fun i => ?_⟩⟩
      · simp only [MemW12,HasWeakGradient,Measure.restrict_empty]
        exact ⟨⟨by simp [LocallyIntegrableOn],fun _ => by simp [LocallyIntegrableOn],by simp⟩,
          by simp,by simp⟩
      · simp
    simpa only [hEmpty,Finset.sum_empty] using hGraph
  | insert j s hj hi =>
    have he : (⋃ i ∈ insert j s, (V i).val) = (V j).val ∪ ⋃ i ∈ s, (V i).val := by
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
    have h₁ := h j (Finset.mem_insert_self _ _)
    have h₂ := hi (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa only [he,Finset.sum_insert hj] using h₁.union h₂

/-- Every weak Dirichlet Poisson field on a bounded smooth domain has the
displayed global second weak gradient. The coefficient is fixed by the
domain and is uniform over the zero-extended data. -/
theorem exists_smoothDomain_global_secondWeakColumns {q : ℕ}
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u f : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q},
        AmbientDirichletPoissonData U u D f →
        HasLocalSecondWeakColumns ⟨U,hU.1.1⟩ D (C*ambientPoissonL2Size D f) := by
  classical
  let K := closure U
  have hK : IsCompact K := hU.1.2.2.isCompact_closure
  have hLocal (a : K) := exists_smoothDomain_local_secondWeakColumns (q := q) hU a.property
  choose O C h using hLocal
  have hCover : K ⊆ ⋃ a : K, (O a).val := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,(h ⟨x,hx⟩).1⟩
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover (fun a => (O a).val) (fun a => (O a).property) hCover
  let V (a : K) : OpenDomain 3 := ⟨(O a).val ∩ U,(O a).property.inter hU.1.1⟩
  have hAll : (⋃ a ∈ I, (V a).val) = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨a,ha⟩ := mem_iUnion.mp hx
      obtain ⟨_,hxa⟩ := mem_iUnion.mp ha
      exact hxa.2
    · intro hx
      obtain ⟨a,ha⟩ := mem_iUnion.mp (hI (subset_closure hx))
      obtain ⟨haI,hxa⟩ := mem_iUnion.mp ha
      exact mem_iUnion.mpr ⟨a,mem_iUnion.mpr ⟨haI,hxa,hx⟩⟩
  refine ⟨∑ a ∈ I, C a,Finset.sum_nonneg (fun a _ => (h a).2.1),?_⟩
  intro u f D hData
  have hAllGraph := hasLocalSecondWeakColumns_finsetUnion I V (fun a => C a*ambientPoissonL2Size D f)
    (fun a _ => (h a).2.2 hData)
  simpa only [hAll,Finset.sum_mul] using hAllGraph

end Thesis
