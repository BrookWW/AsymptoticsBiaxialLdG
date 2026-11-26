module

public import Thesis.Variational.WeakMorreyBoundary
import HolderToCK.Analysis.RepresentativeGluing

/-! Continuous representatives of weak maps on an actual smooth closed domain. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set Topology
open scoped ENNReal

namespace Thesis

private theorem exists_morrey_representative_near_closure
    {U : Set Point} (hU : IsSmoothDomain U) {q : ℕ} {p : ℝ} (hp : 3 < p)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 ⟨U,hU.1.1⟩ u D)
    (hD : ∀ j, MemLp (fun x => D x j) (ENNReal.ofReal p) (volume.restrict U))
    {a : Point} (ha : a ∈ closure U) :
    ∃ (W : Set Point) (v : Point → Ambient q), a ∈ W ∧ IsOpen W ∧ ContinuousOn v W ∧
      u =ᵐ[volume.restrict (U ∩ W)] v := by
  have hExtend : ∃ (V : OpenDomain 3) (w : Point → Ambient q) (G : Point → HarmonicMaps.Gradient 3 q),
      a ∈ V.val ∧ MemW12 V w G ∧ EqOn w u (U ∩ V.val) ∧
      (∀ j, MemLp (fun x => G x j) (ENNReal.ofReal p) (volume.restrict V.val)) := by
    by_cases h : a ∈ U
    · exact ⟨⟨U,hU.1.1⟩,u,D,h,hu,fun _ _ => rfl,hD⟩
    · have hFront : a ∈ frontier U := by rw [frontier,hU.1.1.interior_eq]; exact ⟨ha,h⟩
      obtain ⟨B,hB⟩ := hU.exists_epigraph_box hFront
      obtain ⟨d,hd,_,w,G,hGraph,hValue,hColumns⟩ :=
        B.exists_local_reflected_memW12_with_lp_columns hU.1.1 hu hD
      exact ⟨B.physicalRectangle (-d) d,w,G,B.normalChart_mem_zero hB hd,hGraph,hValue,hColumns⟩
  obtain ⟨V,w,G,hV,hGraph,hEq,hColumns⟩ := hExtend
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp (V.property.mem_nhds hV)
  have hMeasure := Measure.restrict_mono_set volume hBall
  have hGraph' : MemW12 (ballDomain a r) w G :=
    ⟨hGraph.1.mono hBall,hGraph.2.1.mono_measure hMeasure,fun j => (hGraph.2.2 j).mono_measure hMeasure⟩
  obtain ⟨v,hv,hC,_,_,_⟩ := exists_halfBall_holder_rep_of_weakColumns hr hp hGraph'
    (fun j => (hColumns j).mono_measure hMeasure)
  let W := ball a (r/2)
  have hW : W ⊆ V.val := (ball_subset_ball (half_le_self hr.le)).trans hBall
  have hEq' : u =ᵐ[volume.restrict (U ∩ W)] w := by
    exact (ae_restrict_mem (hU.1.1.inter isOpen_ball).measurableSet).mono fun _ hx =>
      (hEq ⟨hx.1,hW hx.2⟩).symm
  exact ⟨W,v,mem_ball_self (half_pos hr),isOpen_ball,hC,
    hEq'.trans (ae_restrict_of_ae_restrict_of_subset inter_subset_right hv)⟩

/-- A weak graph with all first columns in (L^p), (p>3), admits one
continuous representative on the entire closure of a smooth bounded domain. -/
theorem IsSmoothDomain.exists_weakMorreyClosureRepresentative
    {U : Set Point} (hU : IsSmoothDomain U) {q : ℕ} {p : ℝ} (hp : 3 < p)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 ⟨U,hU.1.1⟩ u D)
    (hD : ∀ j, MemLp (fun x => D x j) (ENNReal.ofReal p) (volume.restrict U)) :
    ∃ v : Point → Ambient q, u =ᵐ[volume.restrict U] v ∧ ContinuousOn v (closure U) := by
  classical
  let K := closure U
  have hLocal (x : K) := exists_morrey_representative_near_closure hU hp hu hD x.property
  choose W v hW hOpen hC hAE using hLocal
  have hAgree (i j : K) : EqOn (v i) (v j) (K ∩ (W i ∩ W j)) := by
    let V := W i ∩ W j
    let O := U ∩ V
    have hV : IsOpen V := (hOpen i).inter (hOpen j)
    have hO : IsOpen O := hU.1.1.inter hV
    have hI : O ⊆ U ∩ W i := fun _ hx => ⟨hx.1,hx.2.1⟩
    have hJ : O ⊆ U ∩ W j := fun _ hx => ⟨hx.1,hx.2.2⟩
    have hAEi : u =ᵐ[volume.restrict O] v i := ae_restrict_of_ae_restrict_of_subset hI (hAE i)
    have hAEj : u =ᵐ[volume.restrict O] v j := ae_restrict_of_ae_restrict_of_subset hJ (hAE j)
    have hEq : v i =ᵐ[volume.restrict O] v j := hAEi.symm.trans hAEj
    have hOnO := Measure.eqOn_open_of_ae_eq hEq hO
      ((hC i).mono (hI.trans inter_subset_right)) ((hC j).mono (hJ.trans inter_subset_right))
    have hSu : O ⊆ K ∩ V := fun _ hx => ⟨subset_closure hx.1,hx.2⟩
    exact hOnO.of_subset_closure ((hC i).mono (fun _ hx => hx.2.1)) ((hC j).mono (fun _ hx => hx.2.2))
      hSu hV.closure_inter
  let f (x : Point) := if hx : x ∈ K then v ⟨x,hx⟩ x else 0
  have hSame (i : K) : EqOn f (v i) (K ∩ W i) := by
    intro x hx
    rw [show f x = v ⟨x,hx.1⟩ x from dif_pos hx.1]
    exact hAgree ⟨x,hx.1⟩ i ⟨hx.1,hW ⟨x,hx.1⟩,hx.2⟩
  have hCF : ContinuousOn f K := by
    intro x hx
    let i : K := ⟨x,hx⟩
    have hxW : x ∈ W i := hW i
    have hEq : f =ᶠ[𝓝[K] x] v i := by
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds ((hOpen i).mem_nhds hxW)] with y hy hIn
      exact hSame i ⟨hy,hIn⟩
    exact (((hC i x hxW).continuousAt ((hOpen i).mem_nhds hxW)).continuousWithinAt).congr_of_eventuallyEq
      hEq (hSame i ⟨hx,hxW⟩)
  have hCover : K ⊆ ⋃ i : K, W i := fun x hx => mem_iUnion.2 ⟨⟨x,hx⟩,hW ⟨x,hx⟩⟩
  obtain ⟨I,hI⟩ := hU.1.2.2.isCompact_closure.elim_finite_subcover W hOpen hCover
  have hUcover : U ⊆ ⋃ i ∈ I, U ∩ W i := by
    intro x hx
    obtain ⟨i,hi,hxW⟩ := mem_iUnion₂.1 (hI (subset_closure hx))
    exact mem_iUnion₂.2 ⟨i,hi,hx,hxW⟩
  refine ⟨f,ae_restrict_of_ae_restrict_of_subset hUcover ?_,hCF⟩
  apply (ae_eq_restrict_biUnion_iff (fun i : K => U ∩ W i) I.countable_toSet u f).2
  intro i _
  have hEq : f =ᵐ[volume.restrict (U ∩ W i)] v i :=
    (ae_restrict_mem (hU.1.1.inter (hOpen i)).measurableSet).mono fun _ hx =>
      hSame i ⟨subset_closure hx.1,hx.2⟩
  exact (hAE i).trans hEq.symm

end Thesis
