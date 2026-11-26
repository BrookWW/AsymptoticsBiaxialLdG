module

public import Thesis.Variational.FlatWallPoissonComparison
public import Thesis.Variational.OddWallReflection

/-! Volume transport and derivative bounds on a bounded flattened chart. -/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace Thesis.RegularWallGraphPatch

variable {U : Set Point}

@[expose] def flatPositiveBox (P : RegularWallGraphPatch U) := P.flatBox ∩ positiveWallHalf

theorem flatPositiveBox_isOpen (P : RegularWallGraphPatch U) : IsOpen P.flatPositiveBox :=
  P.flatBox_isOpen.inter isOpen_positiveWallHalf

theorem preimage_domain_neighborhood (P : RegularWallGraphPatch U) :
    P.flatChart ⁻¹' (U ∩ P.neighborhood) = P.flatPositiveBox := by
  have hn : P.flatChart ⁻¹' P.neighborhood = P.flatBox := by
    rw [← P.flatChart_image_flatBox,preimage_image_eq _ P.flatChart.injective]
  rw [preimage_inter,hn]
  ext x
  constructor
  · rintro ⟨hU,hF⟩
    exact ⟨hF,(P.flatChart_mem_domain hF).1 hU⟩
  · rintro ⟨hF,hP⟩
    exact ⟨(P.flatChart_mem_domain hF).2 hP,hF⟩

theorem flatPositiveBox_volume (P : RegularWallGraphPatch U) (hU : IsOpen U) :
    MeasurePreserving P.flatChart (volume.restrict P.flatPositiveBox)
      (volume.restrict (U ∩ P.neighborhood)) := by
  refine ⟨P.flatChart_volume.measurable,?_⟩
  rw [← P.preimage_domain_neighborhood, ← Measure.restrict_map P.flatChart_volume.measurable
    (hU.inter P.isOpen_neighborhood).measurableSet,P.flatChart_volume.map_eq]

theorem isCompact_closure_flatBox (P : RegularWallGraphPatch U) : IsCompact (closure P.flatBox) := by
  let K := closedBall (0 : Plane) P.baseRadius ×ˢ Icc (-P.halfHeight) P.halfHeight
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hComp : IsCompact (planeLinePlacement '' K) := hK.image planeLinePlacement.continuous
  apply hComp.of_isClosed_subset isClosed_closure (closure_minimal _ hComp.isClosed)
  intro z hz
  exact ⟨planeLinePlacement.symm z, ⟨ball_subset_closedBall hz.1, Ioo_subset_Icc_self hz.2⟩,
    planeLinePlacement.apply_symm_apply z⟩

/-- Forward chart derivatives are uniformly bounded on the exact flattened box. -/
theorem exists_forward_derivative_bound (P : RegularWallGraphPatch U) (hP : ContDiff ℝ 2 P.height) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ P.flatBox, ‖fderiv ℝ P.flatChart z‖ ≤ D := by
  obtain ⟨D,hD⟩ := P.isCompact_closure_flatBox.exists_bound_of_continuousOn
    ((P.flatChart_contDiff_two hP).continuous_fderiv two_ne_zero).continuousOn
  exact ⟨max D 0,le_max_right _ _,fun z hz => (hD z (subset_closure hz)).trans (le_max_left _ _)⟩

theorem flat_pullback_tsupport_subset (P : RegularWallGraphPatch U)
    {f : Point → ℝ} (hs : tsupport f ⊆ P.neighborhood) :
    tsupport (f ∘ P.flatChart) ⊆ P.flatBox := by
  intro z hz
  have hIn : P.flatChart z ∈ tsupport f := by
    by_contra h
    have hNear : ∀ᶠ v in 𝓝 z, P.flatChart v ∉ tsupport f :=
      P.flatChart.continuous.continuousAt ((isClosed_tsupport f).isOpen_compl.mem_nhds h)
    exact (notMem_tsupport_iff_eventuallyEq.mpr
      (hNear.mono fun x hx => show f (P.flatChart x) = 0 from image_eq_zero_of_notMem_tsupport hx)) hz
  obtain ⟨y,hy,he⟩ := P.flatChart_image_flatBox.symm ▸ hs hIn
  exact P.flatChart.injective he ▸ hy

theorem iteratedFDeriv_two_flat_pullback_bounded (P : RegularWallGraphPatch U)
    {f : Point → ℝ} (hf : ContDiffOn ℝ 2 f closedWallHalf) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ P.flatPositiveBox, ‖iteratedFDeriv ℝ 2 f z‖ ≤ D := by
  have hK : IsCompact (closure P.flatBox ∩ closedWallHalf) :=
    P.isCompact_closure_flatBox.inter_right closedWallHalf_isClosed
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    ((hf.continuousOn_iteratedFDerivWithin (m := 2) le_rfl closedWallHalf_uniqueDiffOn).mono inter_subset_right)
  refine ⟨max D 0,le_max_right _ _,fun z hz => ?_⟩
  have hZ : 0 < z 2 := hz.2
  have hW : closedWallHalf ∈ 𝓝 z :=
    mem_of_superset (isOpen_positiveWallHalf.mem_nhds hz.2) fun y hy => (show 0 < y 2 from hy).le
  have hEq : iteratedFDerivWithin ℝ 2 f closedWallHalf z = iteratedFDeriv ℝ 2 f z := by
    rw [← iteratedFDerivWithin_univ]
    exact iteratedFDerivWithin_congr_set (Filter.eventuallyEq_univ.mpr hW) 2
  rw [← hEq]
  exact (hD z ⟨subset_closure hz.1,hZ.le⟩).trans (le_max_left _ _)

end Thesis.RegularWallGraphPatch
