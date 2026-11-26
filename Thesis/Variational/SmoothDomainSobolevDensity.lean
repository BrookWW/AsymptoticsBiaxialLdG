module

public import Thesis.Variational.SmoothDomainTraceChart
import StratificationTheory.Foundation.CompactSobolevCutoff
import HarmonicMaps.Analysis.SobolevSmoothDensity
import HarmonicMaps.Analysis.SobolevAECongruence
import HarmonicMaps.Analysis.SobolevDifference
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Smooth approximation of actual finite weak graphs on a smooth domain. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set Topology
open scoped BigOperators ContDiff ENNReal Manifold

namespace Thesis

private theorem memW12_sum {q : ℕ} {V : OpenDomain 3} {ι : Type*}
    (I : Finset ι) {f : ι → Point → Ambient q} {D : ι → Point → HarmonicMaps.Gradient 3 q}
    (h : ∀ i ∈ I, MemW12 V (f i) (D i)) :
    MemW12 V (∑ i ∈ I, f i) (∑ i ∈ I, D i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (MemW12.zero V : MemW12 V (0 : Point → Ambient q) 0)
  | @insert i I hi ih =>
    have h₁ := h i (Finset.mem_insert_self _ _)
    have h₂ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have h₀ : MemW12 V (0 : Point → Ambient q) 0 := MemW12.zero V
    have hAdd := h₁.sub (h₀.sub h₂)
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    change MemW12 V (f i + ∑ j ∈ I, f j) (fun x j => D i x j + (∑ k ∈ I, D k) x j)
    simpa only [Pi.zero_apply, zero_sub, sub_neg_eq_add] using hAdd

private theorem exists_bounded_local_extension_around_closure {Ω : Set Point} (hΩ : IsSmoothDomain Ω)
    {q : ℕ} {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 ⟨Ω,hΩ.1.1⟩ u D) {x : Point} (hx : x ∈ closure Ω) :
    ∃ (V : OpenDomain 3) (w : Point → Ambient q) (G : Point → HarmonicMaps.Gradient 3 q),
      x ∈ V.val ∧ Bornology.IsBounded V.val ∧ MemW12 V w G ∧ EqOn w u (Ω ∩ V.val) := by
  by_cases hxΩ : x ∈ Ω
  · exact ⟨⟨Ω,hΩ.1.1⟩,u,D,hxΩ,hΩ.1.2.2,hu,fun _ _ => rfl⟩
  · have hFront : x ∈ frontier Ω := by
      rw [frontier, hΩ.1.1.interior_eq]
      exact ⟨hx,hxΩ⟩
    obtain ⟨B,hB⟩ := hΩ.exists_epigraph_box hFront
    obtain ⟨δ,hδ,hδB,w,G,hw,hAgree⟩ := B.exists_local_reflected_memW12 hΩ.1.1 B.radius_pos le_rfl hu
    exact ⟨B.physicalRectangle (-δ) δ,w,G, B.normalChart_mem_zero hB hδ,
      B.isBounded_physicalRectangle (neg_le_neg hδB) hδB,hw,hAgree⟩

/-- A smooth bounded domain admits a global extension of each actual weak
graph. The extension agrees with the original map throughout the domain
and with its original weak columns almost everywhere there. -/
theorem IsSmoothDomain.exists_global_memW12_extension {Ω : Set Point} (hΩ : IsSmoothDomain Ω)
    {q : ℕ} {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 ⟨Ω,hΩ.1.1⟩ u D) :
    ∃ (w : Point → Ambient q) (G : Point → HarmonicMaps.Gradient 3 q),
      MemW12 ⟨univ,isOpen_univ⟩ w G ∧ EqOn w u Ω ∧ G =ᵐ[volume.restrict Ω] D := by
  classical
  let K := closure Ω
  have hK : IsCompact K := hΩ.1.2.2.isCompact_closure
  have hLocal (x : K) := exists_bounded_local_extension_around_closure hΩ hu x.property
  choose V w G hMem hBound hGraph hAgree using hLocal
  have hCover : K ⊆ ⋃ x : K, (V x).val := fun x hx => mem_iUnion.2 ⟨⟨x,hx⟩,hMem ⟨x,hx⟩⟩
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover (fun x : K => (V x).val) (fun x => (V x).property) hCover
  have hFinCover : K ⊆ ⋃ i : I, (V i).val := by rwa [iUnion_subtype]
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Point)
    isClosed_closure (fun i : I => (V i).val) (fun i => (V i).property) hFinCover
  let χ (i : I) (x : Point) := ρ i x
  have hχ (i : I) : ContDiff ℝ ∞ (χ i) := (ρ i).contMDiff.contDiff
  let f (i : I) (x : Point) := χ i x • w i x
  let A (i : I) (x : Point) (j : Fin 3) :=
    coordinateDerivative (χ i) (hχ i) j x • w i x + χ i x • G i x j
  have hPieces (i : I) : MemW12 ⟨univ,isOpen_univ⟩ (f i) (A i) := by
    have hComp : HasCompactSupport (χ i) :=
      (hBound i).isCompact_closure.of_isClosed_subset (isClosed_tsupport (χ i)) ((hρ i).trans subset_closure)
    exact (hGraph i).to_memW12Loc.smoothCutoff_univ (hχ i) hComp (hρ i)
  let F := ∑ i : I, f i
  let DF := ∑ i : I, A i
  have hExt : MemW12 ⟨univ,isOpen_univ⟩ F DF := memW12_sum Finset.univ (fun i _ => hPieces i)
  have hEq : EqOn F u Ω := by
    intro x hx
    have hPart (i : I) : f i x = χ i x • u x := by
      by_cases hxV : x ∈ (V i).val
      · exact congrArg (fun a : Ambient q => χ i x • a) (hAgree i ⟨hx,hxV⟩)
      · have hZero : χ i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxV (hρ i h))
        simp only [f,hZero,zero_smul]
    change (∑ i : I, f i) x = u x
    simp only [Finset.sum_apply, hPart, ← Finset.sum_smul]
    have hSum : ∑ i : I, χ i x = 1 := ρ.sum_finsupport' x (subset_closure hx) (Finset.subset_univ _)
    rw [hSum,one_smul]
  have hFae : F =ᵐ[volume.restrict Ω] u :=
    (ae_restrict_mem hΩ.1.1.measurableSet).mono (fun _ hx => hEq hx)
  refine ⟨F,DF,hExt,hEq,?_⟩
  exact (hExt.1.mono (subset_univ Ω)).ae_eq_of_ae_eq_map hu.1 hFae

/-- Globally smooth maps approximate both the original map and all its
weak columns strongly on the actual smooth domain. -/
theorem IsSmoothDomain.exists_smooth_memW12_approximation {Ω : Set Point} (hΩ : IsSmoothDomain Ω)
    {q : ℕ} {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 ⟨Ω,hΩ.1.1⟩ u D) :
    ∃ (f : ℕ → Point → Ambient q) (hf : ∀ n, ContDiff ℝ ∞ (f n)),
      (∀ n, MemW12 ⟨Ω,hΩ.1.1⟩ (f n) (fun x i => coordinateDerivative (f n) (hf n) i x)) ∧
      Tendsto (fun n => eLpNorm (f n - u) 2 (volume.restrict Ω)) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun n => eLpNorm (fun x => coordinateDerivative (f n) (hf n) i x - D x i)
        2 (volume.restrict Ω)) atTop (𝓝 0) := by
  obtain ⟨w,G,hw,hEq,hGrad⟩ := hΩ.exists_global_memW12_extension hu
  obtain ⟨R,hR,hSub⟩ := hΩ.1.2.2.subset_ball_lt 0 (0 : Point)
  let V := ballDomain (0 : Point) R
  have univW : MemLp w 2 volume := by simpa only [Measure.restrict_univ] using hw.2.1
  have univG (i : Fin 3) : MemLp (fun x => G x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hw.2.2 i
  have hW : MemW12 V w G := ⟨hw.1.mono (subset_univ _), univW.mono_measure Measure.restrict_le_self,
    fun i => (univG i).mono_measure Measure.restrict_le_self⟩
  obtain ⟨f,hf,hfW,hfconv,hDconv⟩ := hW.smoothDensity_memW12_ball hR
  have hμ := Measure.restrict_mono_set volume hSub
  refine ⟨f,hf,fun n => ⟨(hfW n).1.mono hSub, (hfW n).2.1.mono_measure hμ,
    fun i => ((hfW n).2.2 i).mono_measure hμ⟩, ?_,?_⟩
  · have hWA : w =ᵐ[volume.restrict Ω] u := (ae_restrict_mem hΩ.1.1.measurableSet).mono (fun _ hx => hEq hx)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfconv (fun _ => zero_le)
    intro n
    change eLpNorm (f n - u) 2 (volume.restrict Ω) ≤ eLpNorm (f n - w) 2 (volume.restrict (ball 0 R))
    rw [eLpNorm_congr_ae (EventuallyEq.rfl.sub hWA.symm)]
    exact eLpNorm_mono_measure _ hμ
  · intro i
    have hGA : (fun x => G x i) =ᵐ[volume.restrict Ω] fun x => D x i :=
      hGrad.mono (fun x hx => congrFun hx i)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hDconv i) (fun _ => zero_le)
    intro n
    change eLpNorm (fun x => coordinateDerivative (f n) (hf n) i x - D x i) 2 (volume.restrict Ω) ≤
      eLpNorm (fun x => coordinateDerivative (f n) (hf n) i x - G x i) 2 (volume.restrict (ball 0 R))
    have hE : (fun x => coordinateDerivative (f n) (hf n) i x - D x i) =ᵐ[volume.restrict Ω]
        fun x => coordinateDerivative (f n) (hf n) i x - G x i :=
      hGA.mono fun x hx => congrArg (fun z => coordinateDerivative (f n) (hf n) i x - z) hx.symm
    rw [eLpNorm_congr_ae hE]
    exact eLpNorm_mono_measure _ hμ

end Thesis
