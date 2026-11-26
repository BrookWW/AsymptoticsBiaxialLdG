module

public import Thesis.Variational.ScalarMollificationDerivatives
public import Thesis.Upstream.WholeSpacePoissonHessianLp

/-! The whole-space Poisson estimate for fields with Lipschitz first columns. -/

public section

noncomputable section

open Filter Function HarmonicMaps HolderToCK MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Topology

namespace Thesis

private theorem norm_hessian_le_coordinate_sum
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Point) ℝ) :
    ‖T‖ ≤ ∑ i : Fin 2 → Fin 3, ‖T (axis ∘ i)‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hExp (j : Fin 2) : (∑ k : Fin 3, v j k • axis k) = v j := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,axis] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (v j)
  have hSum : T v = ∑ i : Fin 2 → Fin 3, (∏ j, v j (i j)) • T (axis ∘ i) := by
    calc
      _ = T (fun j => ∑ k : Fin 3, v j k • axis k) := congrArg T (funext hExp).symm
      _ = _ := by
        change T.toMultilinearMap (fun j => ∑ k : Fin 3, v j k • axis k) = _
        rw [MultilinearMap.map_sum]
        exact Finset.sum_congr rfl fun i _ =>
          T.toMultilinearMap.map_smul_univ (fun j => v j (i j)) (axis ∘ i)
  rw [hSum,Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul,norm_prod,mul_comm]
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => PiLp.norm_apply_le (v j) (i j)))
    (norm_nonneg _)

private theorem iteratedFDeriv_two_mollification_tendsto
    {f : Point → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hCols : ∀ j : Fin 3, ∃ L : ℝ≥0, LipschitzWith L (coordDeriv j f))
    {x : Point} (hx : ContDiffAt ℝ 2 f x) :
    Tendsto (fun n => iteratedFDeriv ℝ 2 (compactDataMollification f (compactDataApproximationScale n)) x)
      atTop (𝓝 (iteratedFDeriv ℝ 2 f x)) := by
  let H n := iteratedFDeriv ℝ 2 (compactDataMollification f (compactDataApproximationScale n)) x
  let T := iteratedFDeriv ℝ 2 f x
  have hCoord (i : Fin 2 → Fin 3) : Tendsto (fun n => H n (axis ∘ i)) atTop (𝓝 (T (axis ∘ i))) := by
    have hAxes : axis ∘ i = ![axis (i 0),axis (i 1)] := by
      funext j
      fin_cases j <;> rfl
    have hCSF : ContDiffAt ℝ 1 (coordDeriv (i 1) f) x :=
      (hx.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    have hC : ContinuousAt (coordDeriv (i 0) (coordDeriv (i 1) f)) x :=
      ((hCSF.fderiv_right (m := 0) (by norm_num)).clm_apply contDiffAt_const).continuousAt
    have hLim := compactDataMollification_tendsto_of_continuousAt
      (measurable_coordDeriv_scalar (i 0)).aestronglyMeasurable hC
    have hVal : T (axis ∘ i) = coordDeriv (i 0) (coordDeriv (i 1) f) x := by
      rw [hAxes]
      exact (fderiv_fderiv_column_eq_iteratedFDeriv_two hx (axis (i 0)) (axis (i 1))).symm
    have hSeq (n : ℕ) : H n (axis ∘ i) =
        compactDataMollification (coordDeriv (i 0) (coordDeriv (i 1) f))
          (compactDataApproximationScale n) x := by
      let h := compactDataApproximationScale n
      have hS := compactDataMollification_contDiff hf.continuous h
      dsimp only [H]
      rw [hAxes,← fderiv_fderiv_column_eq_iteratedFDeriv_two
        ((hS.of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)).contDiffAt)]
      change coordDeriv (i 0) (coordDeriv (i 1) (compactDataMollification f h)) x = _
      rw [coordDeriv_compactDataMollification_of_lipschitz hf]
      obtain ⟨L,hL⟩ := hCols (i 1)
      rw [coordDeriv_compactDataMollification_of_lipschitz hL]
    simpa only [hVal,hSeq] using hLim
  have hSum : Tendsto (fun n => ∑ i : Fin 2 → Fin 3, ‖H n (axis ∘ i) - T (axis ∘ i)‖)
      atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,Finset.sum_const_zero] using
      (tendsto_finsetSum Finset.univ fun i _ =>
        ((hCoord i).sub (tendsto_const_nhds (x := T (axis ∘ i)))).norm)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => norm_hessian_le_coordinate_sum (H n - T)) hSum

/-- The global scalar Hessian bound applies to compact Lipschitz fields with
Lipschitz columns and a classical Hessian almost everywhere. -/
theorem exists_wholeSpace_scalarPoissonHessianLp_lipschitz_columns
    (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Point → ℝ) {K : ℝ≥0}, LipschitzWith K u → HasCompactSupport u →
      (∀ j : Fin 3, ∃ L : ℝ≥0, LipschitzWith L (coordDeriv j u)) →
      (∀ᵐ x ∂(volume : Measure Point), ContDiffAt ℝ 2 u x) →
      eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 u x‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (laplacian u) (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC,hBound⟩ := exists_wholeSpace_scalarPoissonHessianLp p hp
  refine ⟨C,hC,?_⟩
  intro u K hu huS hCols hAE
  classical
  choose L hL using hCols
  have hCols (j : Fin 3) : ∃ K : ℝ≥0, LipschitzWith K (coordDeriv j u) := ⟨L j,hL j⟩
  have hLap : StronglyMeasurable (laplacian u) := by
    unfold laplacian
    exact (Finset.measurable_sum _ (fun j _ => measurable_coordDeriv_scalar j)).stronglyMeasurable
  have hLapB (x : Point) : ‖laplacian u x‖ ≤ ∑ j : Fin 3, (L j : ℝ) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => abs_coordDeriv_le_of_lipschitz (hL j) j x)
  let h := compactDataApproximationScale
  let uApprox : ℕ → Point → ℝ := fun n => compactDataMollification u (h n)
  have hDiff (n : ℕ) : ContDiff ℝ ∞ (uApprox n) :=
    compactDataMollification_contDiff hu.continuous (h n)
  refine eLpNorm_le_of_ae_tendsto_of_uniform_norm (zero_lt_one.trans hp)
    (g := fun n x => ‖iteratedFDeriv ℝ 2 (uApprox n) x‖)
    (fun n => ((hDiff n).continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).norm.aestronglyMeasurable) ?_ ?_
  · filter_upwards [hAE] with x hx
    exact (iteratedFDeriv_two_mollification_tendsto hu hCols hx).norm
  · intro n
    refine (hBound (uApprox n) (hDiff n) (compactDataMollification_hasCompactSupport huS (h n))).trans ?_
    apply mul_le_mul_right
    change eLpNorm (laplacian (compactDataMollification u (h n))) (ENNReal.ofReal p) volume ≤ _
    rw [laplacian_compactDataMollification_of_lipschitz_columns hu hCols (h n)]
    exact eLpNorm_probabilityKernelConvolution_le
      (scaledMollifierKernel_contDiff 3 (h n)).continuous.measurable
      (scaledMollifierKernel_nonneg 3 (h n)) (scaledMollifierKernel_integrable 3 (h n))
      (scaledMollifierKernel_integral_one 3 (h n)) hLap hLapB hp.le

end Thesis
