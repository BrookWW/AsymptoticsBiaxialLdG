module

public import Thesis.Variational.FlatWeakMetricForcingThird
public import Thesis.Variational.SmoothDomainBoundaryPoissonFour
public import Thesis.Variational.LocalEllipticThirdNormalColumn
import Thesis.Upstream.TangentialWeakHessian
import Thesis.Upstream.WeakCoordinateDifferenceQuotientLp
import Thesis.Upstream.WholeSpaceLaplacianTestDensity
import Thesis.Upstream.WeakLpDerivatives

/-! One more weak derivative of the actual flat Dirichlet graph. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal NNReal

namespace Thesis

private theorem hasCompactSupport_oddWeakCutoffHessian {q : ℕ}
    {χ : Point → ℝ} (hc : HasCompactSupport χ)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    {H : Point → Fin 3 → HarmonicMaps.Gradient 3 q} (i j : Fin 3) :
    HasCompactSupport (fun x => oddFlatWallWeakHessian (localWeakCutoffHessian χ u D H) x i j) := by
  let Q (x : Point) := localWeakCutoffHessian χ u D H x i j
  let G := upperCoordinateHalfSpace.val.indicator Q
  have hQ : HasCompactSupport Q := hc.of_isClosed_subset (isClosed_tsupport _)
    (localWeakCutoffHessian_tsupport_subset χ u D H i j)
  have hG : HasCompactSupport G := hQ.mono (by
    intro x hx hn
    exact hx (by by_cases h : x ∈ upperCoordinateHalfSpace.val <;> simp [G,h,hn]))
  have hR := hG.comp_homeomorph normalReflection.toHomeomorph
  exact hG.sub (hR.smul_left (f := fun _ => flatReflectionSign i*flatReflectionSign j))

private theorem lpNorm_four_difference_le_weakPartial {q : ℕ}
    {f e : Point → Ambient q} (hf : MemLp f 2 (volume : Measure Point)) (hc : HasCompactSupport f)
    (he₂ : MemLp e 2 (volume : Measure Point)) (he₄ : MemLp e 4 (volume : Measure Point))
    {k : Fin 3} (hDer : IsWeakAmbientCoordinatePartial univ k f e) (t : ℝ) :
    lpNorm (ambientDifferenceQuotient k t f) 4 (volume : Measure Point) ≤ lpNorm e 4 volume := by
  obtain ⟨hLp,hNorm⟩ := ambientDifferenceQuotient_eLpNorm_le_weakPartial hf hc he₂ hDer
    (p := 4) (by norm_num) (by simpa only [ENNReal.ofReal_ofNat] using he₄) t
  rw [ENNReal.ofReal_ofNat] at hLp hNorm
  rw [← toReal_eLpNorm hLp.1,← toReal_eLpNorm he₄.1]
  exact ENNReal.toReal_mono he₄.eLpNorm_ne_top hNorm

/-- The actual fourth-integrable second graph of a flat Dirichlet field
has fourth-integrable third columns on a smaller half-ball, when its
elliptic forcing has one additional weak derivative in that exponent. -/
theorem exists_flat_weakMetric_thirdFour :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {R : ℝ}, 0 < R →
      ∀ {u f : Point → Ambient 5} {D F : Point → HarmonicMaps.Gradient 3 5}
        {H : Point → Fin 3 → HarmonicMaps.Gradient 3 5}
        {A : Point → Fin 3 → Fin 3 → ℝ},
      MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D →
      (∀ x ∈ ball (0 : Point) R, x ∉ upperCoordinateHalfSpace.val → u x=0 ∧ D x=0) →
      (∀ i, MemW12Four ⟨upperCoordinateHalfSpace.val∩ball (0 : Point) R,
        upperCoordinateHalfSpace.property.inter isOpen_ball⟩ (fun x => D x i) (fun x => H x i)) →
      (∀ i ≠ (2 : Fin 3), ∃ T : Point → HarmonicMaps.Gradient 3 5,
        MemW12 (ballDomain (0 : Point) R) (fun x => D x i) T) →
      MemW12Four ⟨upperCoordinateHalfSpace.val∩ball (0 : Point) R,
        upperCoordinateHalfSpace.property.inter isOpen_ball⟩ f F →
      (∀ i j, ContDiff ℝ ∞ (fun x => A x i j)) →
      (∀ i j x, x ∈ ball (0 : Point) R → |(if i = j then 1 else 0)-A x j i| ≤ δ) →
      (∀ x ∈ ball (0 : Point) R, A x 2 2 ≠ 0) →
      ContDiff ℝ ∞ (fun x => (A x 2 2)⁻¹) →
      HasWeakPackedDivergenceEq (upperCoordinateHalfSpace.val∩ball (0 : Point) R)
        (fun x => packAmbientGradient (fun i => ∑ j : Fin 3, A x i j • D x j)) f →
      let P : OpenDomain 3 := ⟨upperCoordinateHalfSpace.val∩ball (0 : Point) (R/4),
        upperCoordinateHalfSpace.property.inter isOpen_ball⟩
      ∃ K : Point → Fin 3 → Fin 3 → HarmonicMaps.Gradient 3 5,
        ∀ i j, MemW12Four P (fun x => H x i j) (fun x => K x i j) := by
  obtain ⟨δ,hδ,hGain⟩ := exists_wholeSpace_tangential_weakHessian_four_gain
  refine ⟨δ,hδ,?_⟩
  intro R hR u f D F H A hu hZero hH hT hf hA hClose hNon hInv hEq
  let S := upperCoordinateHalfSpace
  let W := ballDomain (0 : Point) R
  let U : OpenDomain 3 := ⟨S.val∩W.val,S.property.inter W.property⟩
  let B := ballDomain (0 : Point) (R/2)
  let V : OpenDomain 3 := ⟨S.val∩B.val,S.property.inter B.property⟩
  let P : OpenDomain 3 := ⟨S.val∩ball 0 (R/4),S.property.inter isOpen_ball⟩
  have hVU : V.val ⊆ U.val := inter_subset_inter_right _ (ball_subset_ball (half_le_self hR.le))
  have hPV : P.val ⊆ V.val := inter_subset_inter_right _ (ball_subset_ball (by linarith only [hR]))
  have hPU : P.val ⊆ U.val := hPV.trans hVU
  have hStrong := HasWeakPackedDivergenceEq.metric_strongEquation U (isBounded_ball.subset inter_subset_right)
    (fun i => (hH i).weak) hf.weak.2.1 A hA hEq
  obtain ⟨hu₄,hD₄⟩ := memLp_four_firstColumns_on_flat_halfBall hR hu hZero (fun i => (hH i).weak) hT
  let b : ContDiffBump (0 : Point) := ⟨R/4,R/3,by positivity,by linarith only [hR]⟩
  let χ : Point → ℝ := b
  have hχ : ContDiff ℝ ∞ χ := b.contDiff
  have hc : HasCompactSupport χ := b.hasCompactSupport
  have hχB : tsupport χ ⊆ B.val := b.tsupport_eq.le.trans
    (closedBall_subset_ball (by change R/3 < R/2; linarith only [hR]))
  have hχW : tsupport χ ⊆ W.val := hχB.trans (ball_subset_ball (half_le_self hR.le))
  let g := flatWeakMetricCutoffForcing A χ u f D
  obtain ⟨E,hE,hE₄,hDE₄⟩ := exists_weakGradient_four_flatWeakMetricCutoffForcing B isBounded_ball A hA hχ hc hχB
    ⟨memW12_restrict_for_weakPoisson hu (subset_univ _),hu₄,hD₄,
      fun i => memW12_restrict_for_weakPoisson (hH i).weak hVU,
      fun i j => ((hH i).columnFour j).mono_measure (Measure.restrict_mono_set _ hVU),
      memW12_restrict_for_weakPoisson hf.weak hVU,
      hf.valueFour.mono_measure (Measure.restrict_mono_set _ hVU),
      fun i => (hf.columnFour i).mono_measure (Measure.restrict_mono_set _ hVU)⟩
  have hg₀ : HasCompactSupport g := hasCompactSupport_flatWeakMetricCutoffForcing A hc u f D
  let coeffBump : ContDiffBump (0 : Point) := ⟨R/2,3*R/4,by positivity,by linarith only [hR]⟩
  let coeffCut : Point → ℝ := coeffBump
  have hCoeffSupport : tsupport coeffCut ⊆ W.val := coeffBump.tsupport_eq.le.trans
    (closedBall_subset_ball (by change 3*R/4 < R; linarith only [hR]))
  have hCoeffOne (x : Point) (hx : x ∈ B.val) : coeffCut x=1 :=
    coeffBump.one_of_mem_closedBall (ball_subset_closedBall hx)
  let a (i j : Fin 3) (x : Point) := coeffCut x*((if i = j then (1:ℝ) else 0)-A x j i)
  have ha (i j : Fin 3) : ContDiff ℝ ∞ (a i j) :=
    coeffBump.contDiff.mul (contDiff_const.sub (hA j i))
  have ha₀ (i j : Fin 3) : HasCompactSupport (a i j) := coeffBump.hasCompactSupport.mul_right
  have hBnd (i j : Fin 3) (x : Point) (_ : x ∈ S.val) : |a i j x| ≤ δ := by
    by_cases hx : x ∈ W.val
    · change |coeffCut x*((if i = j then (1:ℝ) else 0)-A x j i)| ≤ _
      rw [abs_mul,abs_of_nonneg (coeffBump.nonneg' x)]
      exact (mul_le_of_le_one_left (abs_nonneg _) coeffBump.le_one).trans (hClose i j x hx)
    · have hx₀ : coeffCut x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hCoeffSupport h))
      simpa only [a,hx₀,zero_mul,abs_zero] using hδ.le
  choose L hL using fun i j => exists_global_lipschitz_of_smooth_compact (ha i j) (ha₀ i j)
  let C := ∑ i : Fin 3, ∑ j : Fin 3, (L i j : ℝ)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _))
  have hCL (i j : Fin 3) : (L i j : ℝ) ≤ C :=
    (Finset.single_le_sum (f := fun k : Fin 3 => (L i k : ℝ)) (fun k _ => NNReal.coe_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun l : Fin 3 => ∑ k : Fin 3, (L l k : ℝ))
        (fun _ _ => Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _)) (Finset.mem_univ i))
  let J := localWeakCutoffHessian χ u D H
  obtain ⟨hVal,hJ⟩ := memW12_oddFlatWallWeakHessian_cutoff_reflection W isBounded_ball hχ hc hχW
    hu hZero (fun i => (hH i).weak) hT
  have hJc (i j : Fin 3) : HasCompactSupport (fun x => oddFlatWallWeakHessian J x i j) :=
    hasCompactSupport_oddWeakCutoffHessian hc i j
  have hEqS : (fun x => ∑ i : Fin 3, J x i i) =ᵐ[volume.restrict S.val]
      fun x => g x+∑ i : Fin 3, ∑ j : Fin 3, a i j x • J x i j := by
    have hStrongU := (ae_restrict_iff' U.property.measurableSet).1 hStrong
    apply (ae_restrict_iff' S.property.measurableSet).2
    filter_upwards [hStrongU] with x hx hxS
    by_cases hxχ : x ∈ tsupport χ
    · have hxU : x ∈ U.val := ⟨hxS,hχW hxχ⟩
      simpa only [J,g,a,hCoeffOne x (hχB hxχ),one_mul] using
        flatWeakMetricCutoff_strong_trace A χ u f D H x (hx hxU)
    · have hJ₀ (i j : Fin 3) : J x i j=0 :=
        image_eq_zero_of_notMem_tsupport (f := fun x => J x i j)
          (fun h => hxχ (localWeakCutoffHessian_tsupport_subset χ u D H i j h))
      have hg : g x=0 := image_eq_zero_of_notMem_tsupport
        (fun h => hxχ (tsupport_flatWeakMetricCutoffForcing_subset A χ u f D h))
      simp only [hJ₀,hg,smul_zero,Finset.sum_const_zero,add_zero]
  have hcG := oddFlatWeakForcing_hasCompactSupport hg₀
  have hG₂ := oddFlatWeakForcing_memLp hE.2.1
  have hG₄ := oddFlatWeakForcing_memLp hE₄
  have haM (i j : Fin 3) :
      AEStronglyMeasurable (reflectedFlatWeakHessianCoefficient a i j) (volume : Measure Point) ∧
        HasCompactSupport (reflectedFlatWeakHessianCoefficient a i j) :=
    ⟨reflectedFlatWeakHessianCoefficient_measurable i j (ha i j).continuous.aestronglyMeasurable,
      reflectedFlatWeakHessianCoefficient_hasCompactSupport i j (ha₀ i j)⟩
  have hT₃ (k : {k : Fin 3 // k ≠ 2}) : ∃ E : Point → Fin 3 → HarmonicMaps.Gradient 3 5,
      ∀ i j, HasWeakAmbientCoordinateColumnFour P.val k.val (fun x => H x i j)
        (fun x => E x i j) := by
    let e := oddFlatWeakForcing (fun x => E x k.val)
    have he₂ : MemLp e 2 (volume : Measure Point) := oddFlatWeakForcing_memLp (hE.2.2 k.val)
    have he₄ : MemLp e 4 (volume : Measure Point) := oddFlatWeakForcing_memLp (hDE₄ k.val)
    have hDer : IsWeakAmbientCoordinatePartial univ k.val (oddFlatWeakForcing g) e :=
      oddFlatWeakForcing_weakTangentialPartial hE k.property
    have hDif (t : ℝ) (_ : t ∈ Ioo (0 : ℝ) 2) (i j : Fin 3) (x : Point) :
        |ambientDifferenceQuotient k.val t (reflectedFlatWeakHessianCoefficient a i j) x| ≤ C :=
      (abs_ambientDifferenceQuotient_reflectedFlatWeakHessianCoefficient_le i j k.property
        (hL i j).lipschitzOnWith x t).trans (hCL i j)
    obtain ⟨_,K,hK,hK₄,hDK⟩ := hGain hVal hJ hJc hcG hG₂ hG₄ haM
      (abs_reflectedFlatWeakHessianCoefficient_le hδ.le hBnd)
      (oddFlatWallWeakHessian_reflect_equation hEqS) k.val C _ hC lpNorm_nonneg hDif
      (fun t _ => lpNorm_four_difference_le_weakPartial hG₂ hcG he₂ he₄ hDer t)
    have hFix : EqOn χ (fun _ => 1) (ball (0 : Point) (R/4)) :=
      fun x hx => b.one_of_mem_closedBall (ball_subset_closedBall hx)
    obtain ⟨_,_,hKeep⟩ := localWeakCutoff_eqOn_open_plateau isOpen_ball hFix u D H
    refine ⟨K,fun i j => ⟨((hH i).weak.2.2 j).mono_measure (Measure.restrict_mono_set _ hPU),
      ((hH i).columnFour j).mono_measure (Measure.restrict_mono_set _ hPU),
      ((hK i).2.2 j).mono_measure (Measure.restrict_mono_set _ (subset_univ P.val)),
      (hK₄ i j).mono_measure Measure.restrict_le_self,?_⟩⟩
    have hSame : (fun x => oddFlatWallWeakHessian J x i j) =ᵐ[volume.restrict P.val] fun x => H x i j := by
      filter_upwards [ae_restrict_mem (μ := volume) P.property.measurableSet] with x hx
      rw [oddFlatWallWeakHessian_eq_upper J hx.1,show J x=H x from hKeep hx.2]
    exact ((hDK i j).mono MeasurableSet.univ (subset_univ _)).congr_ae hSame EventuallyEq.rfl
  choose T hT' using hT₃
  have hFp : HasWeakAmbientCoordinateColumnFour P.val 2 f (fun x => F x 2) :=
    ⟨hf.weak.2.1.mono_measure (Measure.restrict_mono_set _ hPU),
      hf.valueFour.mono_measure (Measure.restrict_mono_set _ hPU),
      (hf.weak.2.2 2).mono_measure (Measure.restrict_mono_set _ hPU),
      (hf.columnFour 2).mono_measure (Measure.restrict_mono_set _ hPU),
      (hf.weak.1.mono hPU).2.2 2⟩
  obtain ⟨K,hK⟩ := exists_thirdWeakColumns_four_of_tangential_metric P
    (isBounded_ball.subset inter_subset_right) (2 : Fin 3)
    (hu.1.mono (subset_univ _))
    (fun i => memW12_restrict_for_weakPoisson (hH i).weak hPU)
    (fun i => ((hH i).valueFour).mono_measure (Measure.restrict_mono_set _ hPU))
    (fun i j => ((hH i).columnFour j).mono_measure (Measure.restrict_mono_set _ hPU))
    hFp A hA (fun x hx => hNon x (hPU hx).2) hInv
    (ae_restrict_of_ae_restrict_of_subset hPU hStrong) T hT'
  exact ⟨K,fun i j => ⟨(hK i j).1,
    ((hH i).columnFour j).mono_measure (Measure.restrict_mono_set _ hPU),(hK i j).2⟩⟩

end Thesis
