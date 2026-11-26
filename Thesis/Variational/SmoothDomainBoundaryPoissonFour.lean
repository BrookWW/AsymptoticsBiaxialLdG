module

public import Thesis.Variational.WeakSmallSlopeWallGeometry
public import Thesis.Variational.FlatWeakMetricLocalFourGain
public import Thesis.Variational.SmoothDomainLocalPoissonH2
public import Thesis.Upstream.GradientPullbackSecondLp

/-! Fourth-integrable second weak derivatives in physical boundary neighborhoods. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal

namespace Thesis

/-- The original weak second graph has all of its displayed entries in an
additional local exponent. -/
@[expose] def HasLocalSecondWeakColumnsLp {q : ℕ} (V : OpenDomain 3)
    (D : Point → HarmonicMaps.Gradient 3 q) (p : ℝ≥0∞) : Prop :=
  ∃ H : Point → Fin 3 → HarmonicMaps.Gradient 3 q,
    ∀ j, MemW12 V (fun x => D x j) (fun x => H x j) ∧
      ∀ i, MemLp (fun x => H x j i) p (volume.restrict V.val)

theorem memW12_restrict_for_weakPoisson {q : ℕ} {V W : OpenDomain 3}
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (h : MemW12 W u D) (hV : V.val ⊆ W.val) : MemW12 V u D := by
  have hμ := Measure.restrict_mono_set (volume : Measure Point) hV
  exact ⟨h.1.mono hV,h.2.1.mono_measure hμ,fun j => (h.2.2 j).mono_measure hμ⟩

theorem flatMetric_halfBall_secondGraph_and_tangential {q : ℕ}
    (F : Point ≃ₜ Point) (hF : ContDiff ℝ ∞ (F : Point → Point))
    (hInv : ContDiff ℝ ∞ (F.symm : Point → Point)) {R : ℝ} (hR : 0 < R)
    {u f : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D) (hf : MemLp f 2 volume)
    (hFlux : MemLp (fun x => ambientGradientMetric 3 q (fderiv ℝ F.symm (F x))
      (packAmbientGradient (D x))) 2 volume)
    (hWeak : HasWeakPackedDivergenceEq (ball (0 : Point) R ∩ upperCoordinateHalfSpace.val)
      (fun x => ambientGradientMetric 3 q (fderiv ℝ F.symm (F x)) (packAmbientGradient (D x))) f)
    (hZero : ∀ x ∈ ball (0 : Point) R, x ∉ upperCoordinateHalfSpace.val → u x=0 ∧ D x=0) :
    (∃ H : Point → Fin 3 → HarmonicMaps.Gradient 3 q,
      ∀ j, MemW12 (⟨upperCoordinateHalfSpace.val∩ball (0 : Point) (R/4),
        upperCoordinateHalfSpace.property.inter isOpen_ball⟩ : OpenDomain 3)
        (fun x => D x j) (fun x => H x j)) ∧
    ∀ j ≠ (2 : Fin 3), ∃ T : Point → HarmonicMaps.Gradient 3 q,
      MemW12 (ballDomain (0 : Point) (R/4)) (fun x => D x j) T := by
  obtain ⟨_,_,hSecond⟩ := exists_flatBoundary_secondWeakColumns (q := q) F hF hInv hR
  obtain ⟨H,hH⟩ := hSecond hu hf hFlux hWeak hZero
  have hA : ContDiff ℝ ∞ (fun x : Point => ambientGradientMetric 3 q (fderiv ℝ F.symm (F x))) :=
    contDiff_ambientGradientMetric.comp ((hInv.fderiv_right (by simp)).comp hF)
  obtain ⟨ell,hell,hEll⟩ := exists_ambient_gradientMetric_chart_coercivity (q := q) F hF hInv
    (isCompact_closedBall (0 : Point) R)
  obtain ⟨_,_,hTang⟩ := exists_local_second_weak_column_invariant_direction_on_subset hR hell
    upperCoordinateHalfSpace upperCoordinateHalfSpace_convex (upperCoordinateHalfSpace_inter_ball_nonempty hR)
    _ hA hEll
  refine ⟨⟨H,fun j => by simpa only [inter_comm] using (hH j).1⟩,?_⟩
  intro j hj
  let B := ballDomain (0 : Point) (R/4)
  obtain ⟨T,hT⟩ := hTang hu hf hFlux hWeak hZero j (upperCoordinateHalfSpace_invariant hj) B.val
    B.property.measurableSet Subset.rfl
  have huB : MemW12 B u D := memW12_restrict_for_weakPoisson hu (subset_univ _)
  exact ⟨T,memW12_tangential_column_of_all_second_partials huB j
    (fun k => (hT k).1) (fun k => (hT k).2.2)⟩

/-- Any boundary point has a physical neighborhood with fourth-integrable
actual second weak derivatives for each square- and fourth-integrable
force in the zero-trace graph. -/
theorem exists_smoothDomain_boundary_secondWeakColumns_four
    {U : Set Point} (hU : IsSmoothDomain U) {a : Point} (ha : a ∈ frontier U) :
    ∃ O : OpenDomain 3, a ∈ O.val ∧
      ∀ {u f : Point → Ambient 5} {D : Point → HarmonicMaps.Gradient 3 5},
        AmbientDirichletPoissonData U u D f → MemLp f 4 (volume : Measure Point) →
        HasLocalSecondWeakColumnsLp ⟨O.val∩U,O.property.inter hU.1.1⟩ D 4 := by
  obtain ⟨δ,hδ,hGain⟩ := exists_flat_weakMetric_fourGain
  obtain ⟨F,R,hR,hF0,hF,hInv,hMP,hDomain,hClose⟩ := hU.exists_weakSmallSlopeWallChart ha hδ
  let r := R/4
  have hr : 0 < r := by dsimp only [r]; positivity
  let S := upperCoordinateHalfSpace
  let O : OpenDomain 3 := ⟨F '' ball 0 (r/4), F.isOpenMap _ isOpen_ball⟩
  let V : OpenDomain 3 := ⟨O.val∩U,O.property.inter hU.1.1⟩
  let W : OpenDomain 3 := ⟨S.val∩ball 0 (r/4), S.property.inter isOpen_ball⟩
  have hSmall : ball (0 : Point) (r/4) ⊆ ball 0 R := ball_subset_ball (by dsimp only [r]; linarith only [hR])
  have hImg : V.val = F '' W.val := by
    ext x
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hFy⟩
      exact ⟨y,⟨(hDomain y (hSmall hy)).1 hFy,hy⟩,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy.2,rfl⟩,(hDomain y (hSmall hy.2)).2 hy.1⟩
  have hPV : MapsTo F.symm V.val W.val := by
    rw [hImg]
    rintro _ ⟨y,hy,rfl⟩
    simpa only [F.symm_apply_apply] using hy
  have hMPV : MeasurePreserving F (volume.restrict W.val) (volume.restrict V.val) := by
    have he : F ⁻¹' V.val = W.val := hImg ▸ preimage_image_eq W.val F.injective
    simpa only [he] using hMP.restrict_preimage V.property.measurableSet
  have hBV : Bornology.IsBounded V.val := by
    apply ((isCompact_closedBall (0 : Point) (r/4)).image F.continuous).isBounded.subset
    exact inter_subset_left.trans (image_mono ball_subset_closedBall)
  have haO : a ∈ O.val := ⟨0,mem_ball_self (by positivity),hF0⟩
  have hK : IsCompact (closure U) := hU.1.2.2.isCompact_closure
  obtain ⟨_,_,hPull⟩ := exists_memW12_global_volumePreserving_pullback (q := 5) F hF hMP _ hK
  refine ⟨O,haO,?_⟩
  intro u f D hData hf₄
  let D' := ambientGradientPullback F D
  let f' := f ∘ F
  let K (x : Point) := fderiv ℝ F.symm (F x)
  let A (x : Point) (i j : Fin 3) := ambientGradientMetricEntry (K x) i j
  have hK' : ContDiff ℝ ∞ K := (hInv.fderiv_right (by simp)).comp hF
  have hA (i j : Fin 3) : ContDiff ℝ ∞ (fun x => A x i j) :=
    (contDiff_ambientGradientMetricEntry i j).comp hK'
  have hD₀ (x : Point) (hx : x ∉ closure U) : D x=0 :=
    (hData.outside x (fun h => hx (subset_closure h))).2
  obtain ⟨hu',_⟩ := hPull hData.sobolev hD₀
  have hf₂' : MemLp f' 2 (volume : Measure Point) := hData.force.comp_measurePreserving hMP
  have hf₄' : MemLp f' 4 (volume : Measure Point) := hf₄.comp_measurePreserving hMP
  have hD' (j : Fin 3) : MemLp (fun x => D' x j) 2 (volume : Measure Point) := by
    simpa only [Measure.restrict_univ] using hu'.2.2 j
  have hD₀' (x : Point) (hx : x ∉ F ⁻¹' closure U) : D' x=0 := by
    funext j
    simp only [D',ambientGradientPullback,hD₀ (F x) hx,Pi.zero_apply,smul_zero,Finset.sum_const_zero]
  have hFlux := memLp_ambient_coordinate_operator_of_compact_gradient
    ((contDiff_ambientGradientMetric (n := 3) (q := 5) (p := ∞)).continuous.comp hK'.continuous)
    hD' (F.isCompact_preimage.2 hK) hD₀'
  have hInto : MapsTo F (ball 0 R∩S.val) U := fun x hx => (hDomain x hx.1).2 hx.2
  have hWeak := hData.equation.metric_pullback F hF hInv hMP hInto
  have hZero (x : Point) (hx : x ∈ ball (0 : Point) R) (hxS : x ∉ S.val) :
      (u ∘ F) x=0 ∧ D' x=0 := by
    have h := hData.outside (F x) (fun hy => hxS ((hDomain x hx).1 hy))
    refine ⟨h.1,funext fun j => ?_⟩
    simp only [D',ambientGradientPullback,h.2,Pi.zero_apply,smul_zero,Finset.sum_const_zero]
  obtain ⟨⟨H,hH⟩,hT⟩ := flatMetric_halfBall_secondGraph_and_tangential F hF hInv hR
    hu' hf₂' hFlux hWeak hZero
  have hrR : ball (0 : Point) r ⊆ ball 0 R := ball_subset_ball (by dsimp only [r]; linarith only [hR])
  have hZero' (x : Point) (hx : x ∈ ball (0 : Point) r) (hxS : x ∉ S.val) :
      (u ∘ F) x=0 ∧ D' x=0 :=
    hZero x (hrR hx) hxS
  have hWeak' : HasWeakPackedDivergenceEq (S.val∩ball 0 r)
      (fun x => packAmbientGradient (fun i => ∑ j : Fin 3, A x i j • D' x j)) f' := by
    have heq := hWeak.mono (show S.val∩ball (0 : Point) r ⊆ ball 0 R∩S.val from
      fun _ hx => ⟨hrR hx.2,hx.1⟩)
    have he (x : Point) : ambientGradientMetric 3 5 (K x) (packAmbientGradient (D' x)) =
        packAmbientGradient (fun i => ∑ j : Fin 3, A x i j • D' x j) := by
      apply PiLp.ext
      intro i
      rw [ambientGradientMetric_apply_column,packAmbientGradient_apply]
      simp only [packAmbientGradient_apply,A]
    rw [← show (fun x => ambientGradientMetric 3 5 (K x) (packAmbientGradient (D' x))) =
      (fun x => packAmbientGradient (fun i => ∑ j : Fin 3, A x i j • D' x j)) from funext he]
    exact heq
  have hH₄ := hGain hr hu' hZero' hH hT hf₂' hf₄' hA (fun i j x hx => hClose i j x (hrR hx)) hWeak'
  obtain ⟨_,hD₄⟩ := memLp_four_firstColumns_on_flat_halfBall hr hu' hZero' hH hT
  have hSm : W.val ⊆ S.val∩ball (0 : Point) (r/2) :=
    inter_subset_inter_right _ (ball_subset_ball (by linarith only [hr]))
  have hSm' : W.val ⊆ S.val∩ball (0 : Point) r :=
    inter_subset_inter_right _ (ball_subset_ball (by linarith only [hr]))
  exact memW12_secondColumns_withLp_of_gradientPullback F hF hInv V W hBV hPV
    (hMPV.symm F.toMeasurableEquiv) D H
    (fun j => memW12_restrict_for_weakPoisson (hH j) hSm')
    (fun j => (hD₄ j).mono_measure (Measure.restrict_mono_set _ hSm)) hH₄

end Thesis
