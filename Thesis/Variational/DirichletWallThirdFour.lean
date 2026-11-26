module

public import Thesis.Variational.FlatWeakMetricLocalThird
public import Thesis.Variational.ChartedClassicalForcing
import Thesis.Variational.SmoothDomainClosedDerivative
import Thesis.Upstream.WeakLpDerivatives
import HarmonicMaps.Analysis.SobolevAECongruence

/-! Third weak regularity of the original Dirichlet graph in the physical wall chart. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

/-- The true zero extension retains its global weak graph and the actual
weak metric equation in a volume-preserving wall chart. -/
theorem AmbientDirichletPoissonData.charted_metric_graph {q : ℕ} {U : Set Point}
    (hU : IsSmoothDomain U) {u f : Point → Ambient q}
    {D : Point → HarmonicMaps.Gradient 3 q} (hData : AmbientDirichletPoissonData U u D f)
    (F : Point ≃ₜ Point) (hF : ContDiff ℝ ∞ (F : Point → Point))
    (hInv : ContDiff ℝ ∞ (F.symm : Point → Point))
    (hMP : MeasurePreserving F (volume : Measure Point) volume) (R : ℝ)
    (hDomain : ∀ x ∈ ball (0 : Point) R, F x ∈ U ↔ x ∈ upperCoordinateHalfSpace.val) :
    let D' := ambientGradientPullback F D
    let A (x : Point) := ambientGradientMetric 3 q (fderiv ℝ F.symm (F x))
    MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (u ∘ F) D' ∧
      MemLp (fun x => A x (packAmbientGradient (D' x))) 2 (volume : Measure Point) ∧
      HasWeakPackedDivergenceEq (ball (0 : Point) R∩upperCoordinateHalfSpace.val)
        (fun x => A x (packAmbientGradient (D' x))) (f ∘ F) ∧
      ∀ x ∈ ball (0 : Point) R, x ∉ upperCoordinateHalfSpace.val → (u ∘ F) x=0 ∧ D' x=0 := by
  let D' := ambientGradientPullback F D
  have hK : IsCompact (closure U) := hU.1.2.2.isCompact_closure
  obtain ⟨_,_,hPull⟩ := exists_memW12_global_volumePreserving_pullback (q := q) F hF hMP _ hK
  have hOff (x : Point) (hx : x ∉ closure U) : D x=0 :=
    (hData.outside x (fun hy => hx (subset_closure hy))).2
  obtain ⟨hu,_⟩ := hPull hData.sobolev hOff
  have hD' (j : Fin 3) : MemLp (fun x => D' x j) 2 (volume : Measure Point) := by
    simpa only [Measure.restrict_univ] using hu.2.2 j
  have hOff' (x : Point) (hx : x ∉ F ⁻¹' closure U) : D' x=0 := by
    funext j
    simp only [D',ambientGradientPullback,hOff (F x) hx,Pi.zero_apply,smul_zero,Finset.sum_const_zero]
  have hA : Continuous (fun x : Point => ambientGradientMetric 3 q (fderiv ℝ F.symm (F x))) :=
    (contDiff_ambientGradientMetric (n := 3) (q := q) (p := ∞)).continuous.comp
      ((hInv.continuous_fderiv (by simp)).comp F.continuous)
  have hFlux := memLp_ambient_coordinate_operator_of_compact_gradient hA hD' (F.isCompact_preimage.2 hK) hOff'
  have hInto : MapsTo F (ball (0 : Point) R∩upperCoordinateHalfSpace.val) U :=
    fun x hx => (hDomain x hx.1).2 hx.2
  have hEq := hData.equation.metric_pullback F hF hInv hMP hInto
  refine ⟨hu,hFlux,hEq,?_⟩
  intro x hx hxS
  have hy := hData.outside (F x) (fun h => hxS ((hDomain x hx).1 h))
  refine ⟨hy.1,funext fun j => ?_⟩
  simp only [ambientGradientPullback,hy.2,Pi.zero_apply,smul_zero,Finset.sum_const_zero]

private theorem HasWeakPackedDivergenceEq.metric_entry_form {q : ℕ}
    {U : Set Point} {D : Point → HarmonicMaps.Gradient 3 q} {f : Point → Ambient q}
    (A : Point → (Point →L[ℝ] Point))
    (h : HasWeakPackedDivergenceEq U
      (fun x => ambientGradientMetric 3 q (A x) (packAmbientGradient (D x))) f) :
    HasWeakPackedDivergenceEq U
      (fun x => packAmbientGradient (fun i => ∑ j : Fin 3, ambientGradientMetricEntry (A x) i j • D x j)) f := by
  have he : (fun x => ambientGradientMetric 3 q (A x) (packAmbientGradient (D x))) =
      fun x => packAmbientGradient (fun i => ∑ j : Fin 3, ambientGradientMetricEntry (A x) i j • D x j) := by
    funext x
    apply PiLp.ext
    intro i
    rw [ambientGradientMetric_apply_column,packAmbientGradient_apply]
    simp only [packAmbientGradient_apply]
  rwa [he] at h

/-- One fixed tangent-frame chart gives the actual third weak derivatives
of the flattened zero-trace graph in the fourth-integrable exponent. -/
theorem exists_weakDirichletPoisson_wallChart_thirdFour
    {U : Set Point} (hU : IsSmoothDomain U) {a : Point} (ha : a ∈ frontier U)
    {u f f₀ : Point → Ambient 5} {D : Point → HarmonicMaps.Gradient 3 5}
    (hData : AmbientDirichletPoissonData U u D f)
    (hf₄ : MemLp f 4 (volume : Measure Point))
    (hf₀ : ContDiffOn ℝ 1 f₀ (closure U)) (hfEq : f₀ =ᵐ[volume.restrict U] f) :
    ∃ (P : RegularWallGraphPatch U) (r : ℝ), P.center=a ∧ ContDiff ℝ ∞ P.height ∧
      0 < r ∧ ball (0 : Point) r ⊆ P.flatBox ∧
      HasWeakLpDerivatives (upperCoordinateHalfSpace.val∩ball (0 : Point) r) univ 4 3
        (u ∘ P.flatChart) := by
  obtain ⟨δ₄,hδ₄,hFour⟩ := exists_flat_weakMetric_fourGain
  obtain ⟨δ₃,hδ₃,hThird⟩ := exists_flat_weakMetric_thirdFour
  let δ := min δ₄ δ₃
  have hδ : 0 < δ := lt_min hδ₄ hδ₃
  obtain ⟨P,R,hPa,hPs,hR,hBall,hClose⟩ := hU.exists_weakSmallSlopeGraphPatch ha hδ
  let F := P.flatChart
  let S := upperCoordinateHalfSpace
  have hF : ContDiff ℝ ∞ (F : Point → Point) := P.flatChart_contDiff hPs
  have hInv : ContDiff ℝ ∞ (F.symm : Point → Point) := P.flatChart_symm_contDiff hPs
  have hMP : MeasurePreserving F (volume : Measure Point) volume := P.flatChart_volume
  have hDomain (x : Point) (hx : x ∈ ball (0 : Point) R) : F x ∈ U ↔ x ∈ S.val :=
    P.flatChart_mem_domain (hBall hx)
  obtain ⟨hu,hFlux,hWeak,hZero⟩ := hData.charted_metric_graph hU F hF hInv hMP R hDomain
  let D' := ambientGradientPullback F D
  let f' := f ∘ F
  let B (x : Point) := fderiv ℝ F.symm (F x)
  let A (x : Point) (i j : Fin 3) := ambientGradientMetricEntry (B x) i j
  have hB : ContDiff ℝ ∞ B := (hInv.fderiv_right (by simp)).comp hF
  have hA (i j : Fin 3) : ContDiff ℝ ∞ (fun x => A x i j) :=
    (contDiff_ambientGradientMetricEntry i j).comp hB
  have hf₂' : MemLp f' 2 (volume : Measure Point) := hData.force.comp_measurePreserving hMP
  have hf₄' : MemLp f' 4 (volume : Measure Point) := hf₄.comp_measurePreserving hMP
  obtain ⟨⟨H,hH⟩,hT⟩ := flatMetric_halfBall_secondGraph_and_tangential F hF hInv hR
    hu hf₂' hFlux hWeak hZero
  let r₂ := R/4
  let r₄ := r₂/4
  let r₃ := r₄/4
  have hr₂ : 0 < r₂ := by dsimp only [r₂]; positivity
  have hr₄ : 0 < r₄ := by dsimp only [r₄]; positivity
  have hr₃ : 0 < r₃ := by dsimp only [r₃]; positivity
  have hB₂ : ball (0 : Point) r₂ ⊆ ball 0 R := ball_subset_ball (by dsimp only [r₂]; linarith only [hR])
  have hB₄ : ball (0 : Point) r₄ ⊆ ball 0 r₂ := ball_subset_ball (by dsimp only [r₄]; linarith only [hr₂])
  have hB₃ : ball (0 : Point) r₃ ⊆ ball 0 r₄ := ball_subset_ball (by dsimp only [r₃]; linarith only [hr₄])
  let V₂ : OpenDomain 3 := ⟨S.val∩ball 0 r₂,S.property.inter isOpen_ball⟩
  let V₄ : OpenDomain 3 := ⟨S.val∩ball 0 r₄,S.property.inter isOpen_ball⟩
  let V₃ : OpenDomain 3 := ⟨S.val∩ball 0 r₃,S.property.inter isOpen_ball⟩
  have hV₄ : V₄.val ⊆ V₂.val := inter_subset_inter_right _ hB₄
  have hV₃ : V₃.val ⊆ V₄.val := inter_subset_inter_right _ hB₃
  have hV₄' : V₄.val ⊆ S.val∩ball (0 : Point) (r₂/2) :=
    inter_subset_inter_right _ (ball_subset_ball (by dsimp only [r₄]; linarith only [hr₂]))
  have hWeak₂ := (hWeak.mono (show V₂.val ⊆ ball (0 : Point) R∩S.val from
    fun _ hx => ⟨hB₂ hx.2,hx.1⟩)).metric_entry_form B
  have hZero₂ (x : Point) (hx : x ∈ ball (0 : Point) r₂) (hxS : x ∉ S.val) : (u ∘ F) x=0 ∧ D' x=0 :=
    hZero x (hB₂ hx) hxS
  have hH₄ := hFour hr₂ hu hZero₂ hH hT hf₂' hf₄' hA
    (fun i j x hx => (hClose i j x (hB₂ hx)).trans (min_le_left _ _)) hWeak₂
  obtain ⟨hu₄,hD₄⟩ := memLp_four_firstColumns_on_flat_halfBall hr₂ hu hZero₂ hH hT
  let H₄ (i : Fin 3) : MemW12Four V₄ (fun x => D' x i) (fun x => H x i) :=
    ⟨memW12_restrict_for_weakPoisson (hH i) hV₄,
      (hD₄ i).mono_measure (Measure.restrict_mono_set _ hV₄'),hH₄ i⟩
  have hT₄ (i : Fin 3) (hi : i ≠ 2) :
      ∃ T : Point → HarmonicMaps.Gradient 3 5, MemW12 (ballDomain (0 : Point) r₄) (fun x => D' x i) T := by
    obtain ⟨T,hT⟩ := hT i hi
    exact ⟨T,memW12_restrict_for_weakPoisson hT hB₄⟩
  have hMap₄ : MapsTo F V₄.val U := fun x hx => (hDomain x (hB₂ (hB₄ hx.2))).2 hx.1
  have hFh : ContDiff ℝ 1 (F : Point → Point) := hF.of_le (WithTop.coe_le_coe.mpr le_top)
  have hSource := memW12_charted_contDiffOn_one_force V₄ (isBounded_ball.subset inter_subset_right)
    hU.1.1 hU.uniqueDiffOn_closure F hFh hMap₄ hf₀ 4
  have hAe₄ : (f₀ ∘ F) =ᵐ[volume.restrict V₄.val] f' := by
    have hAE := hMP.quasiMeasurePreserving.ae ((ae_restrict_iff' hU.1.1.measurableSet).1 hfEq)
    filter_upwards [hAE.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem (μ := volume) V₄.property.measurableSet] with x hx hxV
    exact hx (hMap₄ hxV)
  let Df (x : Point) (i : Fin 3) := fderivWithin ℝ f₀ (closure U) (F x) (fderiv ℝ F x (axis i))
  have hfGraph : MemW12Four V₄ f' Df :=
    ⟨hSource.1.congr_ae hAe₄ EventuallyEq.rfl,MemLp.ae_eq hAe₄ hSource.2.1,hSource.2.2⟩
  have hDiag (x : Point) : 0 < A x 2 2 :=
    ambientGradientMetricEntry_diag_pos_of_rightInverse (B x) (fderiv ℝ F x)
      (fderiv_symm_comp_fderiv_homeomorph F hF hInv x) 2
  have hDInv : ContDiff ℝ ∞ (fun x => (A x 2 2)⁻¹) := (hA 2 2).inv (fun x => (hDiag x).ne')
  obtain ⟨K,hK⟩ := hThird hr₄ hu (fun x hx => hZero₂ x (hB₄ hx)) H₄ hT₄ hfGraph hA
    (fun i j x hx => (hClose i j x (hB₂ (hB₄ hx))).trans (min_le_right _ _))
    (fun x _ => (hDiag x).ne') hDInv (hWeak₂.mono hV₄)
  refine ⟨P,r₃,hPa,hPs,hr₃,hB₃.trans (hB₄.trans (hB₂.trans hBall)),?_⟩
  exact HasWeakLpDerivatives.of_memW12_thirdColumns V₃
    (memW12_restrict_for_weakPoisson hu (subset_univ _))
    (fun j => memW12_restrict_for_weakPoisson (H₄ j).weak hV₃) (fun j i => (hK j i).weak)
    (hu₄.mono_measure (Measure.restrict_mono_set _ (hV₃.trans hV₄')))
    (fun j => (H₄ j).valueFour.mono_measure (Measure.restrict_mono_set _ hV₃))
    (fun j i => (hK j i).valueFour) (fun j i k => (hK j i).columnFour k)

end Thesis
