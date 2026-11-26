module

public import Thesis.MeasureGeometry.SegmentFlux
public import Thesis.MeasureGeometry.SegmentTangent
import Thesis.MeasureGeometry.JunctionGeometry
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! The endpoint balance of the original associated stationary varifold. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set Function
open scoped ContDiff ENNReal Matrix.Norms.Frobenius RealInnerProductSpace Topology

namespace Thesis.MeasureGeometry

/-- Stationarity on the actual weighted segments is the sum of oriented
endpoint fluxes. The approximate-tangent field is identified on the
segments using the original cone condition. -/
theorem sum_segment_endpointFlux_eq_zero {Ω U : Set Point} {μ : Measure Point}
    {V : Measure (Point × LineProjection)} {m : ℕ} {p q : Fin m → Point} {θ : Fin m → ℝ}
    (hUΩ : closure U ⊆ Ω) (hClosed : μ.support ∩ closure U = ⋃ i, segment ℝ (p i) (q i))
    (hn : ∀ i, p i ≠ q i)
    (hSegment : ∀ i, μ.restrict (segment ℝ (p i) (q i)) =
      ENNReal.ofReal (θ i) • HausdorffOne.restrict (segment ℝ (p i) (q i)))
    (hMass : μ.restrict (closure U) =
      ∑ i, ENNReal.ofReal (θ i) • HausdorffOne.restrict (segment ℝ (p i) (q i)))
    (hAssoc : IsAssociatedVarifold Ω (Ω ∩ μ.support) μ V) (hStat : IsStationaryVarifold Ω V)
    (X : Point → Point) (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) (hXU : tsupport X ⊆ U) :
    ∑ i, max (θ i) 0 * inner ℝ (segmentDirection (p i) (q i)) (X (q i) - X (p i)) = 0 := by
  classical
  letI : BorelSpace LineProjection := ⟨rfl⟩
  obtain ⟨_, P, _, _, _, hP, hPT, hV⟩ := hAssoc
  let L (i : Fin m) := segment ℝ (p i) (q i)
  let v (i : Fin m) := segmentDirection (p i) (q i)
  let ξ := μ.restrict Ω
  let g (z : Point × LineProjection) :=
    ∑ i : Fin 3, ∑ j : Fin 3, (z.2.val i j) * coordDeriv i X z.1 j
  let f (x : Point) := g (x, P x)
  let fᵢ (i : Fin m) (z : Point) :=
    ∑ j : Fin 3, ∑ k : Fin 3, ((v i) j * (v i) k) * coordDeriv j X z k
  have hD : Continuous (fderiv ℝ X) := hX.continuous_fderiv one_ne_zero
  have hEntry (i j : Fin 3) : Continuous (fun z => coordDeriv i X z j) :=
    (EuclideanSpace.proj j).continuous.comp (hD.clm_apply continuous_const)
  have hg : Continuous g := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.continuous).comp
      (continuous_subtype_val.comp continuous_snd)).mul ((hEntry i j).comp continuous_fst)
  have hMap : AEMeasurable (fun x => (x, P x)) ξ := measurable_id.aemeasurable.prodMk hP
  have hTest := hStat X hX hXc (hXU.trans (subset_closure.trans hUΩ))
  change (∫ z, g z ∂V) = 0 at hTest
  rw [hV, integral_map hMap hg.aestronglyMeasurable] at hTest
  have hCut : (∫ x, f x ∂ξ) = ∫ x, f x ∂μ.restrict (closure U) := by
    calc
      _ = ∫ x, (closure U).indicator f x ∂ξ := by
        apply integral_congr_ae
        refine Eventually.of_forall fun x => ?_
        by_cases hx : x ∈ closure U
        · exact (indicator_of_mem hx f).symm
        · have hxs : x ∉ tsupport X := fun h => hx (subset_closure (hXU h))
          simp only [indicator_of_notMem hx, f, g, coordDeriv,
            fderiv_of_notMem_tsupport ℝ hxs, zero_apply, PiLp.zero_apply, mul_zero, Finset.sum_const_zero]
      _ = _ := by rw [integral_indicator isClosed_closure.measurableSet, Measure.restrict_restrict_of_subset hUΩ]
  have hSupp (i : Fin m) : L i ⊆ Ω ∩ μ.support := by
    intro z hz
    have h : z ∈ μ.support ∩ closure U := hClosed.symm ▸ mem_iUnion.2 ⟨i, hz⟩
    exact ⟨hUΩ h.2, h.1⟩
  have hfEq (i : Fin m) : f =ᵐ[μ.restrict (L i)] fᵢ i := by
    have hA := hPT.filter_mono (ae_mono (Measure.restrict_mono_set _ ((hSupp i).trans inter_subset_left)))
    have hMem := ae_restrict_mem (μ := μ) (isCompact_tensorSegment (p i) (q i)).measurableSet
    have hNe (z : Point) : ∀ᵐ x ∂μ.restrict (L i), x ≠ z := by
      rw [ae_iff, hSegment i]
      have hEq : {a : Point | ¬ a ≠ z} = {z} := by ext a; simp
      rw [hEq]
      letI : NullSingletonClass HausdorffOne := Measure.nullSingletonClass_hausdorff Point (by norm_num)
      have hz : (HausdorffOne.restrict (L i)) {z} = 0 := le_antisymm
        ((Measure.restrict_le_self (μ := HausdorffOne) (s := L i) {z}).trans_eq (measure_singleton z)) zero_le
      change (ENNReal.ofReal (θ i) • HausdorffOne.restrict (L i)) {z} = 0
      rw [Measure.smul_apply, hz, smul_zero]
    filter_upwards [hA, hMem, hNe (p i), hNe (q i)] with z hz hzL hzP hzQ
    have hz' := mem_openSegment_of_ne_left_right hzP.symm hzQ.symm hzL
    have hT := matrixAction_eq_of_approxTangent_openSegment (hn i) (hSupp i) hz' hz
    have hTV : matrixAction (P z).val (v i) = v i := by
      change (P z).val.toEuclideanLin (‖q i - p i‖⁻¹ • (q i - p i)) = _
      rw [map_smul]
      exact congrArg (‖q i - p i‖⁻¹ • ·) hT
    have hProj := lineProjection_entries_of_fixed_unit (P z) (norm_segmentDirection (hn i)) hTV
    simp only [f, g, fᵢ, hProj, v]
  have hInt (i : Fin m) : Integrable (fᵢ i) (HausdorffOne.restrict (L i)) := by
    have hc : Continuous (fᵢ i) :=
      continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
        (hEntry j k).const_mul _
    have hFinite : HausdorffOne (L i) < ⊤ := by
      rw [show L i = segment ℝ (p i) (q i) from rfl, hausdorffMeasure_segment]
      exact edist_lt_top _ _
    letI : IsFiniteMeasure (HausdorffOne.restrict (L i)) := isFiniteMeasure_restrict.2 hFinite.ne
    obtain ⟨M, hM⟩ := (isCompact_tensorSegment (p i) (q i)).exists_bound_of_continuousOn hc.continuousOn
    have hLp : MemLp (fᵢ i) 1 (HausdorffOne.restrict (L i)) :=
      MemLp.of_bound hc.aestronglyMeasurable M ((ae_restrict_mem
        (isCompact_tensorSegment (p i) (q i)).measurableSet).mono fun z hz => hM z hz)
    exact hLp.integrable le_rfl
  have hFi (i : Fin m) : Integrable f (ENNReal.ofReal (θ i) • HausdorffOne.restrict (L i)) := by
    have hEq : fᵢ i =ᵐ[ENNReal.ofReal (θ i) • HausdorffOne.restrict (L i)] f :=
      (hSegment i) ▸ (hfEq i).symm
    exact ((hInt i).smul_measure ENNReal.ofReal_ne_top).congr hEq
  have hEach (i : Fin m) :
      (∫ z, f z ∂(ENNReal.ofReal (θ i) • HausdorffOne.restrict (L i))) =
        max (θ i) 0 * inner ℝ (v i) (X (q i) - X (p i)) := by
    have hEq : f =ᵐ[ENNReal.ofReal (θ i) • HausdorffOne.restrict (L i)] fᵢ i :=
      (hSegment i) ▸ (hfEq i)
    rw [integral_congr_ae hEq, integral_smul_measure, ENNReal.toReal_ofReal', smul_eq_mul]
    exact congrArg (max (θ i) 0 * ·) (integral_segment_tangentialDivergence hX (hn i))
  have hZero : (∫ x, f x ∂μ.restrict (closure U)) = 0 := hCut.symm.trans hTest
  rw [hMass, integral_finsetSum_measure (fun i _ => hFi i)] at hZero
  simpa only [hEach, v] using hZero

/-- An endpoint test supported away from all other vertices gives the
vector balance at one actual interior vertex of the network. -/
theorem incident_balance_of_endpointFlux {U : Set Point} (hU : IsOpen U)
    {m : ℕ} {p q : Fin m → Point} {θ : Fin m → ℝ}
    (hn : ∀ i, p i ≠ q i) (hθ : ∀ i, 0 ≤ θ i)
    (hFlux : ∀ X : Point → Point, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
      ∑ i, max (θ i) 0 * inner ℝ (segmentDirection (p i) (q i)) (X (q i) - X (p i)) = 0)
    {x : Point} (hx : x ∈ U) :
    ∑ i : ↥(incidentSegments p q x), θ i • outwardDirection p q x i = 0 := by
  classical
  let A := (range p ∪ range q) \ {x}
  have hAFin : A.Finite := ((finite_range p).union (finite_range q)).sdiff
  have hA : IsClosed A := hAFin.isClosed
  have hxA : x ∉ A := fun h => h.2 rfl
  obtain ⟨r, hr, hBall⟩ := Metric.isOpen_iff.1 (hU.sdiff hA) x ⟨hx, hxA⟩
  let χ : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hSub : tsupport χ ⊆ U \ A :=
    χ.tsupport_eq.subset.trans ((closedBall_subset_ball (half_lt_self hr)).trans hBall)
  have hχx : χ x = 1 := χ.one_of_mem_closedBall (mem_closedBall_self χ.rIn_pos.le)
  have hχzero {z : Point} (hz : z ∈ range p ∪ range q) (hne : z ≠ x) : χ z = 0 := by
    by_contra h
    exact (hSub (subset_tsupport χ h)).2 ⟨hz, hne⟩
  let v (i : Fin m) := segmentDirection (p i) (q i)
  let g (i : Fin m) : Point :=
    if x = p i then θ i • v i else if x = q i then θ i • (-v i) else 0
  let b := ∑ i, g i
  let X (z : Point) := χ z • b
  have hXt : tsupport X ⊆ tsupport χ := tsupport_smul_subset_left _ _
  have hX : ContDiff ℝ 1 X := χ.contDiff.smul contDiff_const
  have hXc : HasCompactSupport X := χ.hasCompactSupport.isCompact.of_isClosed_subset isClosed_closure hXt
  have hXU : tsupport X ⊆ U := hXt.trans (hSub.trans sdiff_subset)
  have hAt (i : Fin m) :
      max (θ i) 0 * inner ℝ (v i) (X (q i) - X (p i)) = -inner ℝ (g i) b := by
    rw [max_eq_left (hθ i)]
    by_cases hp : x = p i
    · have hq : q i ≠ x := fun h => hn i (hp.symm.trans h.symm)
      change θ i * inner ℝ (v i) (χ (q i) • b - χ (p i) • b) = _
      rw [hχzero (Or.inr (mem_range_self i)) hq, ← hp, hχx, zero_smul, one_smul, zero_sub,
        inner_neg_right, show g i = θ i • v i by simp only [g, hp, if_true],
        real_inner_smul_left]
      ring
    · have hp₀ := hχzero (Or.inl (mem_range_self i)) (Ne.symm hp)
      by_cases hq : x = q i
      · have hVal : g i = θ i • (-v i) := by
          dsimp only [g]
          rw [if_neg hp, if_pos hq]
        change θ i * inner ℝ (v i) (χ (q i) • b - χ (p i) • b) = _
        rw [hp₀, ← hq, hχx, zero_smul, one_smul, sub_zero,
          hVal, real_inner_smul_left, inner_neg_left]
        ring
      · change θ i * inner ℝ (v i) (χ (q i) • b - χ (p i) • b) = _
        rw [hp₀, hχzero (Or.inr (mem_range_self i)) (Ne.symm hq), zero_smul, sub_self,
          show g i = 0 by simp only [g, hp, hq, if_false], inner_zero_right, inner_zero_left, mul_zero, neg_zero]
  have hNeg : -inner ℝ b b = 0 := calc
    _ = ∑ i, -inner ℝ (g i) b := by rw [Finset.sum_neg_distrib, ← sum_inner]
    _ = _ := (Finset.sum_congr rfl fun i _ => (hAt i).symm).trans (hFlux X hX hXc hXU)
  have hz : b = 0 := inner_self_eq_zero.mp (neg_eq_zero.mp hNeg)
  calc
    _ = ∑ i : ↥(incidentSegments p q x), g i := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := (Finset.mem_filter.1 i.property).2
      by_cases hp : x = p i
      · simp only [g, outwardDirection, hp, if_true]
        rfl
      · have hq := hi.resolve_left hp
        have hVal : g i = θ i • (-v i) := by
          dsimp only [g]
          rw [if_neg hp, if_pos hq]
        rw [hVal, outwardDirection, if_neg hp]
        exact (congrArg (fun z : Point => θ i • (‖p i - z‖⁻¹ • (p i - z))) hq).trans
          (congrArg (θ i • ·) (segmentDirection_reverse _ _))
    _ = ∑ i ∈ incidentSegments p q x, g i := Finset.sum_coe_sort _ _
    _ = b := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hp : x ≠ p i := fun h => hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, Or.inl h⟩)
      have hq : x ≠ q i := fun h => hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, Or.inr h⟩)
      simp only [g, hp, hq, if_false]
    _ = 0 := hz

end Thesis.MeasureGeometry
