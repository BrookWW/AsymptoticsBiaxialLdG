module

public import Thesis.Variational.SmoothDomainBoundaryPoissonFour
import StratificationTheory.Foundation.CompactSobolevCutoff
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! The weak fourth-integrability gain on an interior Poisson ball. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal

namespace Thesis

private theorem weakHessian_cutoff_graph_univ {q : ℕ} {W : OpenDomain 3}
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    {H : Point → Fin 3 → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 W u D)
    (hD : ∀ i, MemW12 W (fun x => D x i) (fun x => H x i))
    {χ : Point → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχS : tsupport χ ⊆ W.val) :
    MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3)
      (localWeakCutoffValue χ u) (localWeakCutoffColumns χ u D) ∧
    ∀ i, MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3)
      (fun x => localWeakCutoffColumns χ u D x i) (fun x => localWeakCutoffHessian χ u D H x i) := by
  refine ⟨hu.to_memW12Loc.smoothCutoff_univ hχ hc hχS,?_⟩
  intro i
  have hDχ : ContDiff ℝ ∞ (coordDeriv i χ) :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDχC : HasCompactSupport (coordDeriv i χ) := hc.fderiv_apply ℝ (axis i)
  have hDχS : tsupport (coordDeriv i χ) ⊆ W.val :=
    (tsupport_fderiv_apply_subset ℝ (axis i)).trans hχS
  exact memW12_add_pair (hu.to_memW12Loc.smoothCutoff_univ hDχ hDχC hDχS)
    ((hD i).to_memW12Loc.smoothCutoff_univ hχ hc hχS)

private theorem interiorWeakPoisson_firstLp_four {a : Point} {R : ℝ} (hR : 0 < R)
    {u : Point → Ambient 5} {D : Point → HarmonicMaps.Gradient 3 5}
    {H : Point → Fin 3 → HarmonicMaps.Gradient 3 5}
    (hu : MemW12 (ballDomain a R) u D)
    (hD : ∀ i, MemW12 (ballDomain a R) (fun x => D x i) (fun x => H x i)) :
    MemLp u 4 (volume.restrict (ball a (R/2))) ∧
      ∀ i, MemLp (fun x => D x i) 4 (volume.restrict (ball a (R/2))) := by
  let b : ContDiffBump a := ⟨R/2,3*R/4,by positivity,by linarith only [hR]⟩
  let χ : Point → ℝ := b
  have hχ : ContDiff ℝ ∞ χ := b.contDiff
  have hc : HasCompactSupport χ := b.hasCompactSupport
  have hχS : tsupport χ ⊆ ball a R := b.tsupport_eq.le.trans
    (closedBall_subset_ball (by change 3*R/4 < R; linarith only [hR]))
  obtain ⟨hu',hD'⟩ := weakHessian_cutoff_graph_univ hu hD hχ hc hχS
  have h₀ := memLp_four_of_compact_memW12_univ hu' (hasCompactSupport_localWeakCutoffValue hc u)
  have h₁ (i : Fin 3) := memLp_four_of_compact_memW12_univ (hD' i)
    (hasCompactSupport_localWeakCutoffColumn hc u D i)
  have hχ₁ : EqOn χ (fun _ => 1) (ball a (R/2)) := fun x hx =>
    b.one_of_mem_closedBall (ball_subset_closedBall hx)
  obtain ⟨hVal,hCol,_⟩ := localWeakCutoff_eqOn_open_plateau isOpen_ball hχ₁ u D H
  refine ⟨MemLp.ae_eq ?_ (h₀.mono_measure Measure.restrict_le_self),
    fun i => MemLp.ae_eq ?_ ((h₁ i).mono_measure Measure.restrict_le_self)⟩
  · exact (ae_restrict_mem measurableSet_ball).mono (fun _ hx => hVal hx)
  · exact (ae_restrict_mem measurableSet_ball).mono (fun _ hx => congrFun (hCol hx) i)

/-- The columns of an actual (W¹,²) gradient of a weak Poisson field are
fourth-integrable on the inner ball whenever the force is. -/
theorem memLp_four_interiorWeakPoisson_secondColumns {a : Point} {R : ℝ} (hR : 0 < R)
    {u f : Point → Ambient 5} {D : Point → HarmonicMaps.Gradient 3 5}
    {H : Point → Fin 3 → HarmonicMaps.Gradient 3 5}
    (hu : MemW12 (ballDomain a R) u D)
    (hD : ∀ i, MemW12 (ballDomain a R) (fun x => D x i) (fun x => H x i))
    (hf₂ : MemLp f 2 (volume.restrict (ball a R)))
    (hf₄ : MemLp f 4 (volume.restrict (ball a R)))
    (hEq : HasWeakPackedDivergenceEq (ball a R) (fun x => packAmbientGradient (D x)) f) :
    ∀ i j, MemLp (fun x => H x i j) 4 (volume.restrict (ball a (R/4))) := by
  classical
  let W := ballDomain a R
  let V := ball a (R/2)
  have hVW : V ⊆ W.val := ball_subset_ball (half_le_self hR.le)
  have hV₂ : (volume : Measure Point).restrict V ≤ volume.restrict W.val :=
    Measure.restrict_mono_set _ hVW
  letI : IsFiniteMeasure ((volume : Measure Point).restrict (ball a R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let G (x : Point) (i : Fin 3) := H x i i
  have hStrong := HasWeakPackedDivergenceEq.ae_eq_sum_coordinatePartials
    (U := ball a R) isOpen_ball hEq hu.2.2 hf₂ (G := G)
    (fun i => (hD i).2.2 i) (fun i => (hD i).1.2.2 i)
  have hStrong' := ae_restrict_of_ae_restrict_of_subset hVW hStrong
  obtain ⟨hu₄,hD₄⟩ := interiorWeakPoisson_firstLp_four hR hu hD
  let b : ContDiffBump a := ⟨R/4,R/3,by positivity,by linarith only [hR]⟩
  let χ : Point → ℝ := b
  let A (_ : Point) (i j : Fin 3) : ℝ := if i = j then 1 else 0
  have hA (i j : Fin 3) : ContDiff ℝ ∞ (fun x => A x i j) := contDiff_const
  have hχ : ContDiff ℝ ∞ χ := b.contDiff
  have hc : HasCompactSupport χ := b.hasCompactSupport
  have hχS : tsupport χ ⊆ V := b.tsupport_eq.le.trans
    (closedBall_subset_ball (by change R/3 < R/2; linarith only [hR]))
  obtain ⟨hu',hD'⟩ := weakHessian_cutoff_graph_univ hu hD hχ hc (hχS.trans hVW)
  let J := localWeakCutoffHessian χ u D H
  let g := V.indicator (flatWeakMetricCutoffForcing A χ u f D)
  have hg₀ : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall a (R/2))
    intro x hx
    have hV : x ∈ V := by
      by_contra h
      exact hx (indicator_of_notMem h _)
    exact ball_subset_closedBall hV
  have hg₂ : MemLp g 2 (volume : Measure Point) :=
    (memLp_indicator_iff_restrict measurableSet_ball).2
      (memLp_flatWeakMetricCutoffForcing measurableSet_ball isBounded_ball hA hχ
        (hu.2.1.mono_measure hV₂) (hf₂.mono_measure hV₂) (fun i => (hu.2.2 i).mono_measure hV₂))
  have hg₄ : MemLp g 4 (volume : Measure Point) :=
    (memLp_indicator_iff_restrict measurableSet_ball).2
      (memLp_flatWeakMetricCutoffForcing measurableSet_ball isBounded_ball hA hχ
        hu₄ (hf₄.mono_measure hV₂) hD₄)
  have hDiag (x : Point) (i j : Fin 3) : coordDeriv i (fun y => A y i j) x = 0 :=
    DFunLike.congr_fun (hasFDerivAt_const ((if i = j then 1 else 0) : ℝ) x).fderiv _
  have hTrace : (fun x => ∑ i : Fin 3, J x i i) =ᵐ[(volume : Measure Point)] g := by
    have hEx := (ae_restrict_iff' measurableSet_ball).1 hStrong'
    filter_upwards [hEx] with x hx
    by_cases hxV : x ∈ V
    · have he := flatWeakMetricCutoff_strong_trace A χ u f D H x (by
        simpa only [hDiag,zero_smul,zero_add,A,ite_smul,one_smul,zero_smul,
          Finset.sum_ite_eq,Finset.mem_univ,if_true,G] using hx hxV)
      have ha (i j : Fin 3) : (if i = j then (1:ℝ) else 0)-A x j i = 0 := by
        by_cases h : i = j
        · subst j
          simp [A]
        · simp only [A,if_neg h,if_neg (Ne.symm h),sub_self]
      simpa only [g,indicator_of_mem hxV,J,ha,zero_smul,Finset.sum_const_zero,add_zero] using he
    · have hJ (i j : Fin 3) : J x i j=0 :=
        image_eq_zero_of_notMem_tsupport (f := fun x => J x i j)
          (fun h => hxV (hχS (localWeakCutoffHessian_tsupport_subset χ u D H i j h)))
      simp only [hJ,g,indicator_of_notMem hxV,Finset.sum_const_zero]
  obtain ⟨δ,hδ,hGain⟩ := exists_wholeSpace_ambientWeakHessian_four_gain
  have hGain' := hGain (a := fun _ _ _ => 0) hu' hD' hg₀ hg₂ hg₄
    (fun i j => ⟨aestronglyMeasurable_const,by
      change HasCompactSupport (0 : Point → ℝ); exact HasCompactSupport.zero⟩)
    (fun i j x => by simpa only [abs_zero] using hδ.le)
    (by simpa only [zero_smul,Finset.sum_const_zero,add_zero] using hTrace)
  have hχ₁ : EqOn χ (fun _ => 1) (ball a (R/4)) := fun x hx =>
    b.one_of_mem_closedBall (ball_subset_closedBall hx)
  obtain ⟨_,_,hJ⟩ := localWeakCutoff_eqOn_open_plateau isOpen_ball hχ₁ u D H
  intro i j
  refine MemLp.ae_eq ?_ ((hGain' i j).mono_measure Measure.restrict_le_self)
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_ball] with x hx
  exact congrFun (congrFun (hJ hx) i) j

end Thesis
