module

public import Thesis.Variational.FlatWeakMetricFirstL4
public import Thesis.Variational.FlatWeakMetricCutoffForcing
public import Thesis.Variational.FlatWallWeakHessianEquationReflection
public import Thesis.Upstream.AmbientWeakHessianFourGain
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Local weak fourth-integrability at a flattened Dirichlet wall. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

/-- A flat weak Dirichlet graph for a metric sufficiently close to the
original Euclidean metric has fourth-integrable Hessian entries on the
inner half-ball. The original weak representatives are retained. -/
theorem exists_flat_weakMetric_fourGain :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {R : ℝ}, 0 < R →
      ∀ {u f : Point → Ambient 5} {D : Point → HarmonicMaps.Gradient 3 5}
        {H : Point → Fin 3 → HarmonicMaps.Gradient 3 5}
        {A : Point → Fin 3 → Fin 3 → ℝ},
        MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D →
        (∀ x ∈ ball (0 : Point) R, x ∉ upperCoordinateHalfSpace.val → u x=0 ∧ D x=0) →
        (∀ i, MemW12 (⟨upperCoordinateHalfSpace.val∩ball (0 : Point) R,
          upperCoordinateHalfSpace.property.inter isOpen_ball⟩ : OpenDomain 3)
          (fun x => D x i) (fun x => H x i)) →
        (∀ i ≠ (2 : Fin 3), ∃ T : Point → HarmonicMaps.Gradient 3 5,
          MemW12 (ballDomain (0 : Point) R) (fun x => D x i) T) →
        MemLp f 2 (volume : Measure Point) → MemLp f 4 (volume : Measure Point) →
        (∀ i j, ContDiff ℝ ∞ (fun x => A x i j)) →
        (∀ i j x, x ∈ ball (0 : Point) R → |(if i = j then 1 else 0)-A x j i| ≤ δ) →
        HasWeakPackedDivergenceEq (upperCoordinateHalfSpace.val∩ball (0 : Point) R)
          (fun x => packAmbientGradient (fun i => ∑ j : Fin 3, A x i j • D x j)) f →
        ∀ i j, MemLp (fun x => H x i j) 4
          (volume.restrict (upperCoordinateHalfSpace.val∩ball (0 : Point) (R/4))) := by
  obtain ⟨δ,hδ,hGain⟩ := exists_wholeSpace_ambientWeakHessian_four_gain
  refine ⟨δ,hδ,?_⟩
  intro R hR u f D H A hu hZero hUpper hT hf₂ hf₄ hA hAδ hEq
  let S := upperCoordinateHalfSpace
  let W := ballDomain (0 : Point) R
  let U : OpenDomain 3 := ⟨S.val∩W.val,S.property.inter W.property⟩
  let V := S.val∩ball (0 : Point) (R/2)
  have hVU : V ⊆ U.val := inter_subset_inter_right _ (ball_subset_ball (half_le_self hR.le))
  have hVS : V ⊆ S.val := inter_subset_left
  have hV : IsOpen V := S.property.inter isOpen_ball
  have hVB : Bornology.IsBounded V := isBounded_ball.subset inter_subset_right
  have hStrong := HasWeakPackedDivergenceEq.metric_strongEquation U
    (isBounded_ball.subset inter_subset_right) hUpper (hf₂.mono_measure Measure.restrict_le_self) A hA hEq
  have hStrong' := ae_restrict_of_ae_restrict_of_subset hVU hStrong
  obtain ⟨hu₄,hD₄⟩ := memLp_four_firstColumns_on_flat_halfBall hR hu hZero hUpper hT
  let χ₀ : ContDiffBump (0 : Point) := ⟨R/4,R/3,by positivity,by linarith only [hR]⟩
  let χ : Point → ℝ := χ₀
  have hχ : ContDiff ℝ ∞ χ := χ₀.contDiff
  have hc : HasCompactSupport χ := χ₀.hasCompactSupport
  have hχS : tsupport χ ⊆ ball (0 : Point) (R/2) :=
    χ₀.tsupport_eq.le.trans (closedBall_subset_ball (by change R/3 < R/2; linarith only [hR]))
  have hχW : tsupport χ ⊆ W.val := hχS.trans (ball_subset_ball (half_le_self hR.le))
  obtain ⟨hValue,hHess⟩ := memW12_oddFlatWallWeakHessian_cutoff_reflection W isBounded_ball hχ hc hχW
    hu hZero hUpper hT
  let J := localWeakCutoffHessian χ u D H
  let g := V.indicator (flatWeakMetricCutoffForcing A χ u f D)
  let a (i j : Fin 3) := V.indicator (fun x => (if i = j then (1:ℝ) else 0)-A x j i)
  have hg₀ : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Point) (R/2))
    intro x hx
    have hxV : x ∈ V := by
      by_contra h
      exact hx (indicator_of_notMem h _)
    exact ball_subset_closedBall hxV.2
  have hBound (i j : Fin 3) (x : Point) (_ : x ∈ S.val) : |a i j x| ≤ δ := by
    dsimp only [a]
    by_cases hx : x ∈ V
    · rw [indicator_of_mem hx]
      exact hAδ i j x (hVU hx).2
    · rw [indicator_of_notMem hx,abs_zero]
      exact hδ.le
  have ha₀ (i j : Fin 3) : HasCompactSupport (a i j) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Point) (R/2))
    intro x hx
    have hxV : x ∈ V := by
      by_contra h
      exact hx (indicator_of_notMem h _)
    exact ball_subset_closedBall hxV.2
  have haM (i j : Fin 3) : AEStronglyMeasurable (a i j) (volume : Measure Point) := by
    exact (continuous_const.sub (hA j i).continuous).aestronglyMeasurable.indicator hV.measurableSet
  have hu₂ : MemLp u 2 (volume.restrict V) :=
    (hu.2.1.mono_measure (Measure.restrict_mono_set _ (subset_univ V)))
  have hD₂ (i : Fin 3) : MemLp (fun x => D x i) 2 (volume.restrict V) :=
    ((hu.2.2 i).mono_measure (Measure.restrict_mono_set _ (subset_univ V)))
  have hg₂ : MemLp g 2 (volume : Measure Point) :=
    (memLp_indicator_iff_restrict hV.measurableSet).2
      (memLp_flatWeakMetricCutoffForcing hV.measurableSet hVB hA hχ hu₂
        (hf₂.mono_measure Measure.restrict_le_self) hD₂)
  have hg₄ : MemLp g 4 (volume : Measure Point) :=
    (memLp_indicator_iff_restrict hV.measurableSet).2
      (memLp_flatWeakMetricCutoffForcing hV.measurableSet hVB hA hχ hu₄
        (hf₄.mono_measure Measure.restrict_le_self) hD₄)
  have hSideEq :
      (fun x => ∑ i : Fin 3, J x i i) =ᵐ[volume.restrict S.val]
        fun x => g x+∑ i : Fin 3, ∑ j : Fin 3, a i j x • J x i j := by
    have hRel := (ae_restrict_iff' hV.measurableSet).1 hStrong'
    apply (ae_restrict_iff' S.property.measurableSet).2
    filter_upwards [hRel] with x hx hxS
    by_cases hxV : x ∈ V
    · have he := flatWeakMetricCutoff_strong_trace A χ u f D H x (hx hxV)
      simpa only [J,g,a,indicator_of_mem hxV] using he
    · have hJ (i j : Fin 3) : J x i j = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun x => J x i j)
          (fun h => hxV ⟨hxS,hχS (localWeakCutoffHessian_tsupport_subset χ u D H i j h)⟩)
      simp only [hJ,g,a,indicator_of_notMem hxV,zero_smul,Finset.sum_const_zero,add_zero]
  have hWholeEq := oddFlatWallWeakHessian_reflect_equation hSideEq
  have hData (i j : Fin 3) :
      AEStronglyMeasurable (reflectedFlatWeakHessianCoefficient a i j) (volume : Measure Point) ∧
        HasCompactSupport (reflectedFlatWeakHessianCoefficient a i j) :=
    ⟨reflectedFlatWeakHessianCoefficient_measurable i j ((haM i j).mono_measure Measure.restrict_le_self),
      reflectedFlatWeakHessianCoefficient_hasCompactSupport i j (ha₀ i j)⟩
  have hMem := hGain hValue hHess (oddFlatWeakForcing_hasCompactSupport hg₀)
    (oddFlatWeakForcing_memLp (hg₂.mono_measure Measure.restrict_le_self))
    (oddFlatWeakForcing_memLp (hg₄.mono_measure Measure.restrict_le_self))
    hData (abs_reflectedFlatWeakHessianCoefficient_le hδ.le hBound) hWholeEq
  let P := ball (0 : Point) (R/4)
  have hPlateau : EqOn χ (fun _ => 1) P := fun x hx => χ₀.one_of_mem_closedBall (ball_subset_closedBall hx)
  obtain ⟨_,_,hJ⟩ := localWeakCutoff_eqOn_open_plateau isOpen_ball hPlateau u D H
  intro i j
  refine MemLp.ae_eq ?_ ((hMem i j).mono_measure Measure.restrict_le_self)
  filter_upwards [ae_restrict_mem (μ := volume) (S.property.inter isOpen_ball).measurableSet] with x hx
  rw [oddFlatWallWeakHessian_eq_upper J hx.1,show J x = H x from hJ hx.2]

end Thesis
