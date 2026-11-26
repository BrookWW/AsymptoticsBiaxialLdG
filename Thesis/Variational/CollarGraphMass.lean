module

public import Thesis.Variational.CollarRectangularSlabs
public import Thesis.Variational.H10FractionalEmbedding
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The zero-trace graph integrates along the physical vertical lines
of an epigraph wall chart. -/

public section

open Filter Function MeasureTheory Metric Set Topology
open scoped BigOperators ContDiff ENNReal Matrix Matrix.Norms.Frobenius NNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance collarGraphMassContinuousENorm : ContinuousENorm S0 :=
  SeminormedAddGroup.toContinuousENorm

@[expose] def wallGraphGradientSize {U : Set Point} (v : H10 U) (x : Point) : ℝ :=
  ∑ j : Fin 3, ‖h10Gradient v x j‖

private def wallClassicalGradientSize (φ : Point → S0) (x : Point) : ℝ :=
  ∑ j : Fin 3, ‖coordDeriv j φ x‖

private theorem continuous_setIntegral_norm_on_tensorL2
    {μ : Measure Point} [IsFiniteMeasure μ] (E : Set Point) :
    Continuous (fun p : Lp S0 2 μ => ∫ x in E, ‖p x‖ ∂μ) := by
  let C : ℝ≥0 := NNReal.mk (Real.sqrt (μ.real univ)) (Real.sqrt_nonneg _)
  apply (LipschitzWith.of_dist_le_mul (K := C) ?_).continuous
  intro u v
  let p := u-v
  let g (x : Point) := ‖p x‖
  have hp : MemLp g 2 μ := (Lp.memLp p).norm
  have hI : Integrable g μ := hp.integrable (by norm_num)
  have hCauchy := square_integral_le_measure_mul_integral_square hp
  have hSq : (∫ x, g x^2 ∂μ) = ‖p‖^2 := by
    have h := ofReal_integral_eq_lintegral_ofReal hp.integrable_sq (.of_forall fun _ => sq_nonneg _)
    change ENNReal.ofReal (∫ x, g x^2 ∂μ) = ∫⁻ x, ENNReal.ofReal (‖p x‖^2) ∂μ at h
    rw [lintegral_sq_norm_lp] at h
    have ht := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _),
      ENNReal.toReal_ofReal (sq_nonneg _)] at ht
    exact ht
  have hG : (∫ x, g x ∂μ) ≤ Real.sqrt (μ.real univ) * ‖p‖ := by
    rw [hSq] at hCauchy
    have h := Real.le_sqrt_of_sq_le hCauchy
    rw [Real.sqrt_mul measureReal_nonneg, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
    exact h
  have hIU : IntegrableOn (fun x => ‖u x‖) E μ := ((Lp.memLp u).integrable (by norm_num)).norm.integrableOn
  have hIV : IntegrableOn (fun x => ‖v x‖) E μ := ((Lp.memLp v).integrable (by norm_num)).norm.integrableOn
  have hLe : (∫ x in E, ‖‖u x‖ - ‖v x‖‖ ∂μ) ≤ ∫ x in E, g x ∂μ := by
    apply integral_mono_ae (hIU.sub hIV).norm hI.integrableOn
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub u v)] with x hx
    change ‖‖u x‖ - ‖v x‖‖ ≤ ‖(u-v : Lp S0 2 μ) x‖
    rw [hx]
    exact abs_norm_sub_norm_le (u x) (v x)
  calc
    _ = ‖∫ x in E, (‖u x‖ - ‖v x‖) ∂μ‖ := by rw [dist_eq_norm, integral_sub hIU hIV]
    _ ≤ ∫ x in E, ‖‖u x‖-‖v x‖‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in E, g x ∂μ := hLe
    _ ≤ ∫ x, g x ∂μ := integral_mono_measure Measure.restrict_le_self
      (.of_forall fun _ => norm_nonneg _) hI
    _ ≤ _ := by rw [dist_eq_norm]; exact hG

private theorem norm_directional_derivative_le_column_sum
    (φ : Point → S0) (x ν : Point) (hν : ‖ν‖ = 1) :
    ‖fderiv ℝ φ x ν‖ ≤ wallClassicalGradientSize φ x := by
  let D := fderiv ℝ φ x
  have hνsum : (∑ j : Fin 3, ν j • axis j) = ν := by
    apply PiLp.ext
    intro j
    fin_cases j <;> simp [axis,Fin.sum_univ_three]
  have hSum : D ν = ∑ j : Fin 3, ν j • D (axis j) := by
    conv_lhs => rw [← hνsum]
    rw [map_sum]
    simp only [map_smul]
  change ‖D ν‖ ≤ ∑ j : Fin 3, ‖D (axis j)‖
  rw [hSum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul]
  have h : ‖ν j‖ ≤ 1 := by rw [← hν]; exact PiLp.norm_apply_le ν j
  exact mul_le_of_le_one_left (norm_nonneg _) h

private theorem continuous_wallClassicalGradientSize {φ : Point → S0} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (wallClassicalGradientSize φ) := by
  have hD := hφ.continuous_fderiv (by simp)
  exact continuous_finsetSum _ fun j _ =>
    ((ContinuousLinearMap.apply ℝ S0 (axis j)).continuous.comp hD).norm

private theorem norm_smooth_at_wall_line_le_integral
    {φ : Point → S0} (hφ : ContDiff ℝ ∞ φ) (a ν : Point) (hν : ‖ν‖=1)
    (hφ₀ : φ a=0) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖φ (a+t • ν)‖ ≤ ∫ s in Ioc 0 T, wallClassicalGradientSize φ (a+s • ν) := by
  let L (s : ℝ) := a+s • ν
  let D (s : ℝ) := fderiv ℝ φ (L s) ν
  let H (s : ℝ) := wallClassicalGradientSize φ (L s)
  have hL : Continuous L := continuous_const.add (continuous_id.smul continuous_const)
  have hD : Continuous D :=
    (ContinuousLinearMap.apply ℝ S0 ν).continuous.comp ((hφ.continuous_fderiv (by simp)).comp hL)
  have hH : Continuous H := (continuous_wallClassicalGradientSize hφ).comp hL
  have hDer (s : ℝ) : HasDerivAt (φ ∘ L) (D s) s := by
    have hLd : HasDerivAt L ν s := by
      simpa only [L,id,one_smul] using ((hasDerivAt_id s).smul_const ν).const_add a
    exact ((hφ.differentiable (by simp) (L s)).hasFDerivAt).comp_hasDerivAt s hLd
  have hSeg := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hDer s) (hD.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_of_le ht] at hSeg
  have hEq : (∫ s in Ioc 0 t, D s) = φ (a+t • ν) := by
    simpa only [L, Function.comp_apply,zero_smul,add_zero,hφ₀,sub_zero] using hSeg
  calc
    _ = ‖∫ s in Ioc 0 t, D s‖ := congrArg Norm.norm hEq.symm
    _ ≤ ∫ s in Ioc 0 t, ‖D s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioc 0 t, H s :=
      integral_mono hD.norm.integrableOn_Ioc hH.integrableOn_Ioc
        (fun s => norm_directional_derivative_le_column_sum φ (L s) ν hν)
    _ ≤ _ := setIntegral_mono_set hH.integrableOn_Ioc
      (.of_forall fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (.of_forall (Ioc_subset_Ioc_right htT))

private theorem setIntegral_on_wallChartSlab_eq_product
    {U : Set Point} {b t : ℝ} (Φ : WallChartPoint ≃ₜ Point) (hΦ : MeasurePreserving Φ)
    (hSub : Φ '' wallChartSlab b t ⊆ U) (g : Point → ℝ) (hg : Integrable g volume) :
    (∫ x in Φ '' wallChartSlab b t, g x ∂volume.restrict U) =
      ∫ y in wallChartHorizontal b, ∫ s in Ioc 0 t, g (Φ (y,s)) := by
  let Q := wallChartHorizontal b
  let J := Ioc (0:ℝ) t
  have hSet : MeasurableSet (Φ '' wallChartSlab b t) :=
    Φ.toMeasurableEquiv.measurableSet_image.mpr ((measurableSet_Ioc.prod measurableSet_Ioc).prod measurableSet_Ioc)
  have hMP : MeasurableEmbedding (Φ : WallChartPoint → Point) :=
    Φ.toMeasurableEquiv.measurableEmbedding
  have hGi : Integrable (fun z => g (Φ z)) volume := (hΦ.integrable_comp_emb hMP).2 hg
  calc
    _ = ∫ x in Φ '' wallChartSlab b t, g x := by rw [Measure.restrict_restrict hSet,inter_eq_left.mpr hSub]
    _ = ∫ z in wallChartSlab b t, g (Φ z) := by
      rw [← hΦ.map_eq,hMP.setIntegral_map,preimage_image_eq _ Φ.injective]
    _ = _ := setIntegral_prod (μ := (volume : Measure (ℝ×ℝ))) (ν := (volume : Measure ℝ))
      _ hGi.integrableOn

private theorem smooth_wallChartSlab_integral_le
    {U : Set Point} (hU : IsOpen U) {b t : ℝ} (ht : 0 < t)
    (Φ : WallChartPoint ≃ₜ Point) (hΦ : MeasurePreserving Φ)
    (hSub : Φ '' wallChartSlab b t ⊆ U) (ν : Point) (hν : ‖ν‖ = 1)
    (hV : ∀ y : ℝ×ℝ, ∀ s : ℝ, Φ (y,s) = Φ (y,0)+s • ν)
    (hW : ∀ y ∈ wallChartHorizontal b, Φ (y,0) ∈ frontier U)
    {φ : Point → S0} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hSupp : tsupport φ ⊆ U) :
    (∫ x in Φ '' wallChartSlab b t, ‖φ x‖ ∂volume.restrict U) ≤
      t * ∫ x in Φ '' wallChartSlab b t, wallClassicalGradientSize φ x ∂volume.restrict U := by
  let Q := wallChartHorizontal b
  let J := Ioc (0:ℝ) t
  let V (y : ℝ×ℝ) (s : ℝ) := ‖φ (Φ (y,s))‖
  let G (y : ℝ×ℝ) (s : ℝ) := wallClassicalGradientSize φ (Φ (y,s))
  have hφI : Integrable (fun x => ‖φ x‖) volume :=
    (hφ.continuous.integrable_of_hasCompactSupport hc).norm
  have hGI : Integrable (wallClassicalGradientSize φ) volume := by
    unfold wallClassicalGradientSize
    apply integrable_finsetSum
    intro j _
    have hD : Continuous (coordDeriv j φ) :=
      (ContinuousLinearMap.apply ℝ S0 (axis j)).continuous.comp (hφ.continuous_fderiv (by simp))
    exact (hD.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (axis j))).norm
  have hVL : Integrable (Function.uncurry V) (volume : Measure WallChartPoint) :=
    (hΦ.integrable_comp_emb Φ.toMeasurableEquiv.measurableEmbedding).2 hφI
  have hGL : Integrable (Function.uncurry G) (volume : Measure WallChartPoint) :=
    (hΦ.integrable_comp_emb Φ.toMeasurableEquiv.measurableEmbedding).2 hGI
  have hVE : IntegrableOn (Function.uncurry V) (Q ×ˢ J) volume := hVL.integrableOn
  have hGE : IntegrableOn (Function.uncurry G) (Q ×ˢ J) volume := hGL.integrableOn
  have hVprod : Integrable (Function.uncurry V) ((volume.restrict Q).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact hVE
  have hGprod : Integrable (Function.uncurry G) ((volume.restrict Q).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact hGE
  have hPt (y : ℝ×ℝ) (hy : y ∈ Q) (s : ℝ) (hs : s ∈ J) :
      V y s ≤ ∫ r in J, G y r := by
    have h0 : φ (Φ (y,0)) = 0 := by
      apply Function.notMem_support.mp
      intro hx
      have hU' := hSupp (subset_closure hx)
      have hWall := hW y hy
      rw [frontier,hU.interior_eq] at hWall
      exact hWall.2 hU'
    have h := norm_smooth_at_wall_line_le_integral hφ (Φ (y,0)) ν hν h0 hs.1.le hs.2
    change ‖φ (Φ (y,s))‖ ≤ ∫ r in J, wallClassicalGradientSize φ (Φ (y,r))
    rw [hV y s]
    refine h.trans_eq ?_
    apply integral_congr_ae
    filter_upwards with r
    rw [hV y r]
  have hY (y : ℝ×ℝ) (hy : y ∈ Q) :
      (∫ s in J,V y s) ≤ t * ∫ s in J,G y s := by
    have hVc : Continuous (V y) := hφ.continuous.norm.comp (Φ.continuous.comp (continuous_const.prodMk continuous_id))
    calc
      _ ≤ ∫ s in J,(∫ r in J,G y r) := by
        apply integral_mono_ae hVc.integrableOn_Ioc (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hPt y hy s hs
      _ = _ := by
        rw [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,
          ENNReal.toReal_ofReal ht.le,smul_eq_mul]
  rw [setIntegral_on_wallChartSlab_eq_product Φ hΦ hSub _ hφI,
    setIntegral_on_wallChartSlab_eq_product Φ hΦ hSub _ hGI]
  change (∫ y in Q, ∫ s in J,V y s) ≤ t * ∫ y in Q, ∫ s in J,G y s
  rw [← integral_const_mul]
  apply integral_mono_ae hVprod.integral_prod_left (hGprod.integral_prod_left.const_mul _)
  filter_upwards [ae_restrict_mem ((measurableSet_Ioc.prod measurableSet_Ioc) : MeasurableSet Q)] with y hy
  exact hY y hy

/-- The actual zero-trace value is bounded in a physical slab by its
height times the mass of its actual weak gradient columns. -/
theorem wallChartSlab_h10Value_integral_le
    {U : Set Point} (hU : IsBoundedDomain U) {b t : ℝ} (ht : 0 < t)
    (Φ : WallChartPoint ≃ₜ Point) (hΦ : MeasurePreserving Φ)
    (hSub : Φ '' wallChartSlab b t ⊆ U) (ν : Point) (hν : ‖ν‖ = 1)
    (hV : ∀ y : ℝ×ℝ, ∀ s : ℝ, Φ (y,s) = Φ (y,0)+s • ν)
    (hW : ∀ y ∈ wallChartHorizontal b, Φ (y,0) ∈ frontier U)
    (v : H10 U) :
    (∫ x in Φ '' wallChartSlab b t, ‖h10Value v x‖ ∂volume.restrict U) ≤
      t * ∫ x in Φ '' wallChartSlab b t, wallGraphGradientSize v x ∂volume.restrict U := by
  obtain ⟨p,φ,hLim,hData⟩ := v.exists_smooth_graph_approximation
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.2.2.measure_lt_top.ne
  let E := Φ '' wallChartSlab b t
  let I (z : Lp S0 2 μ) := ∫ x in E, ‖z x‖ ∂μ
  have hI : Continuous I := continuous_setIntegral_norm_on_tensorL2 E
  let A (z : H1Graph U) := I z.1
  let B (z : H1Graph U) := ∑ j : Fin 3, I (z.2 j)
  have hA : Continuous A := hI.comp continuous_fst
  have hB : Continuous B := continuous_finsetSum _ fun j _ => hI.comp ((continuous_apply j).comp continuous_snd)
  have hEval (z : H1Graph U) :
      B z = ∫ x in E, ∑ j : Fin 3, ‖z.2 j x‖ ∂μ := by
    dsimp only [B,I]
    rw [integral_finsetSum]
    intro j _
    exact ((Lp.memLp (z.2 j)).integrable (by norm_num)).norm.integrableOn
  have hEst (n : ℕ) : A (p n) ≤ t*B (p n) := by
    obtain ⟨hφ,hC,hS,hVal,hDer⟩ := hData n
    have hL := smooth_wallChartSlab_integral_le hU.1 ht Φ hΦ hSub ν hν hV hW hφ hC hS
    have hv : A (p n) = ∫ x in E, ‖φ n x‖ ∂μ :=
      integral_congr_ae ((ae_restrict_of_ae hVal).mono fun _ hx => congrArg Norm.norm hx)
    have hd : B (p n) = ∫ x in E, wallClassicalGradientSize (φ n) x ∂μ := by
      rw [hEval]
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr (fun j => ae_restrict_of_ae (hDer j))] with x hx
      exact Finset.sum_congr rfl fun j _ => congrArg Norm.norm (hx j)
    rw [hv,hd]
    exact hL
  have hL := le_of_tendsto_of_tendsto'
    (hA.continuousAt.tendsto.comp hLim)
    ((hB.continuousAt.tendsto.comp hLim).const_mul t) hEst
  rw [hEval] at hL
  exact hL

end Thesis

end
