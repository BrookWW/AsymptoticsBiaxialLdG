module

public import Thesis.MeasureGeometry.PlanarSpectralCoarea
public import Thesis.MeasureGeometry.PlanarCriticalFibers

/-! From regular local coarea charts to the formula on the original open set. -/

public section

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal

namespace Thesis

private theorem measurableSet_planar_level_inter_open
    {U : Set Plane} (hU : IsOpen U) {f : Plane → ℝ} (hf : ContinuousOn f U) (t : ℝ) :
    MeasurableSet (U ∩ {x | f x = t}) := by
  have hFc : Continuous (fun x : U => f x.val) :=
    hf.comp_continuous continuous_subtype_val (fun x => x.property)
  let C : Set U := {x | f x.val = t}
  have hC : IsClosed C := isClosed_eq hFc continuous_const
  have hImg := (MeasurableEmbedding.subtype_coe hU.measurableSet).measurableSet_image' hC.measurableSet
  have hEq : Subtype.val '' C = U ∩ {x | f x = t} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · exact fun hx => ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  exact hEq ▸ hImg

private theorem exists_countable_open_chart_sequence
    {R : Set Plane} (hR : R.Nonempty) (W : R → Set Plane)
    (hW : ∀ x, IsOpen (W x)) (hxW : ∀ x, x.val ∈ W x)
    (hWR : ∀ x, W x ⊆ R) :
    ∃ a : ℕ → R, (⋃ n, W (a n)) = R := by
  classical
  letI : Nonempty R := hR.to_subtype
  obtain ⟨J, hJc, hJ⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  obtain ⟨a, ha⟩ := Set.countable_iff_exists_subset_range.1 hJc
  refine ⟨a, subset_antisymm (iUnion_subset fun n => hWR (a n)) ?_⟩
  intro x hx
  have hM : x ∈ ⋃ i, W i := mem_iUnion.2 ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  have hM' : x ∈ ⋃ i ∈ J, W i := hJ ▸ hM
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hM'
  obtain ⟨n, hn⟩ := ha hj
  exact mem_iUnion.2 ⟨n, hn.symm ▸ hxj⟩

private theorem scalarCoarea_on_regular_set_of_open_charts
    {U R : Set Plane} (hU : IsOpen U) (hRU : R ⊆ U) (f : Plane → ℝ) (hf : ContDiffOn ℝ 1 f U)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (hChart : ∀ x : R, ∃ V : Set Plane, IsOpen V ∧ x.val ∈ V ∧ V ⊆ R ∧
      ∀ E : Set Plane, MeasurableSet E → E ⊆ V →
        AEMeasurable (fun t : ℝ => Measure.hausdorffMeasure 1 (E ∩ {y | f y = t})) volume ∧
          (∫⁻ y in E, w (f y) * ENNReal.ofReal ‖fderiv ℝ f y‖) =
            ∫⁻ t : ℝ, w t * Measure.hausdorffMeasure 1 (E ∩ {y | f y = t})) :
    (∫⁻ y in R, w (f y) * ENNReal.ofReal ‖fderiv ℝ f y‖) =
      ∫⁻ t : ℝ, w t * Measure.hausdorffMeasure 1 (R ∩ {y | f y = t}) := by
  classical
  rcases eq_empty_or_nonempty R with rfl | hR
  · simp
  choose V hV hxV hVR hChartV using hChart
  obtain ⟨a, ha⟩ := exists_countable_open_chart_sequence hR V hV hxV hVR
  let W (n : ℕ) := V (a n)
  let E := disjointed W
  have hEm (n : ℕ) : MeasurableSet (E n) := MeasurableSet.disjointed (fun k => (hV (a k)).measurableSet) n
  have hEdis : Pairwise (Disjoint on E) := disjoint_disjointed W
  have hEcov : (⋃ n, E n) = R := iUnion_disjointed.trans ha
  have hEV (n : ℕ) : E n ⊆ V (a n) := disjointed_subset W n
  have hER (n : ℕ) : E n ⊆ R := (hEV n).trans (hVR (a n))
  have hPiece (n : ℕ) := hChartV (a n) (E n) (hEm n) (hEV n)
  let L (t : ℝ) := {y | f y = t}
  let H := (Measure.hausdorffMeasure 1 : Measure Plane)
  have hFiber (t : ℝ) : H (R ∩ L t) = ∑' n, H (E n ∩ L t) := by
    rw [← hEcov, iUnion_inter, measure_iUnion]
    · intro i j hij
      exact (hEdis hij).mono inter_subset_left inter_subset_left
    · intro n
      have hEq : E n ∩ L t = E n ∩ (U ∩ L t) := by
        rw [← inter_assoc, inter_eq_left.2 ((hER n).trans hRU)]
      rw [hEq]
      exact (hEm n).inter (measurableSet_planar_level_inter_open hU hf.continuousOn t)
  have hMeas (n : ℕ) : AEMeasurable (fun t => w t * H (E n ∩ L t)) volume :=
    hw.aemeasurable.mul (hPiece n).1
  calc
    _ = ∑' n, ∫⁻ y in E n, w (f y) * ENNReal.ofReal ‖fderiv ℝ f y‖ := by
      rw [← hEcov, lintegral_iUnion hEm hEdis]
    _ = ∑' n, ∫⁻ t : ℝ, w t * H (E n ∩ L t) := by
      exact tsum_congr fun n => (hPiece n).2
    _ = ∫⁻ t : ℝ, ∑' n, w t * H (E n ∩ L t) := (lintegral_tsum hMeas).symm
    _ = _ := by simp only [ENNReal.tsum_mul_left, ← hFiber]; rfl

/-- Countable regular charts and the null critical fibers give the
weighted coarea formula on the original open set. -/
theorem planarScalarCoarea_of_local_regular_charts
    (hChart : ∀ {U : Set Plane}, IsOpen U → ∀ f : Plane → ℝ, ContDiffOn ℝ 1 f U →
      ∀ x ∈ U, fderiv ℝ f x ≠ 0 →
      ∃ V : Set Plane, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∀ E : Set Plane, MeasurableSet E → E ⊆ V →
          AEMeasurable (fun t : ℝ => Measure.hausdorffMeasure 1 (E ∩ {y | f y = t})) volume ∧
            ∀ (w : ℝ → ℝ≥0∞), Measurable w →
              (∫⁻ y in E, w (f y) * ENNReal.ofReal ‖fderiv ℝ f y‖) =
                ∫⁻ t : ℝ, w t * Measure.hausdorffMeasure 1 (E ∩ {y | f y = t})) :
    External.PlanarScalarCoarea := by
  intro U hU f hf w hw
  classical
  let R := U ∩ {x | fderiv ℝ f x ≠ 0}
  let S := U ∩ {x | fderiv ℝ f x = 0}
  have h0 : IsOpen (({0} : Set (Plane →L[ℝ] ℝ))ᶜ) := isClosed_singleton.isOpen_compl
  have hR : IsOpen R := (hf.continuousOn_fderiv_of_isOpen hU le_rfl).isOpen_inter_preimage hU h0
  have hRU : R ⊆ U := inter_subset_left
  have hSR : S = U \ R := by
    ext x
    simp [S, R]
  have hSm : MeasurableSet S := hSR ▸ hU.measurableSet.diff hR.measurableSet
  have hDisj : Disjoint R S := hSR ▸ disjoint_sdiff_right
  have hPieces : U = R ∪ S := by
    rw [hSR, union_sdiff_cancel hRU]
  have hReg := scalarCoarea_on_regular_set_of_open_charts hU hRU f hf w hw (R := R) (by
    intro x
    obtain ⟨V, hV, hxV, _, hLaw⟩ := hChart hU f hf x.val x.property.1 x.property.2
    exact ⟨V ∩ R, hV.inter hR, ⟨hxV, x.property⟩, inter_subset_right,
      fun E hEm hEsub => ⟨(hLaw E hEm (hEsub.trans inter_subset_left)).1,
        (hLaw E hEm (hEsub.trans inter_subset_left)).2 w hw⟩⟩)
  have hSourceS : (∫⁻ x in S, w (f x) * ENNReal.ofReal ‖fderiv ℝ f x‖) = 0 := by
    rw [← lintegral_zero (μ := volume.restrict S)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) hSm] with x hx
    rw [hx.2, norm_zero, ENNReal.ofReal_zero, mul_zero]
  have hTarget : (fun t : ℝ => w t * Measure.hausdorffMeasure 1 (U ∩ {y | f y = t}))
      =ᵐ[volume] fun t => w t * Measure.hausdorffMeasure 1 (R ∩ {y | f y = t}) := by
    filter_upwards [ae_critical_level_hausdorffMeasure_eq_zero hU f hf] with t ht
    have he : (Measure.hausdorffMeasure 1 : Measure Plane) (U ∩ {y | f y = t}) =
        (Measure.hausdorffMeasure 1 : Measure Plane) (R ∩ {y | f y = t}) := by
      have hUeq : U ∩ {y | f y = t} = (R ∩ {y | f y = t}) ∪ (S ∩ {y | f y = t}) := by
        rw [hPieces]
        ext x
        simp only [mem_inter_iff, mem_union]
        tauto
      refine le_antisymm ?_ (measure_mono (inter_subset_inter_left _ hRU))
      rw [hUeq]
      exact (measure_union_le _ _).trans_eq (by rw [show Measure.hausdorffMeasure 1 (S ∩ {y | f y = t}) = 0 from ht,
        add_zero])
    rw [he]
  calc
    _ = ∫⁻ x in R, w (f x) * ENNReal.ofReal ‖fderiv ℝ f x‖ := by
      conv_lhs => rw [hPieces]
      rw [lintegral_union hSm hDisj, hSourceS, add_zero]
    _ = _ := hReg.trans (lintegral_congr_ae hTarget).symm

end Thesis
