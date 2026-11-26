module

public import Thesis.Upstream.RealKernelLp
public import Thesis.Upstream.WeakLpBounds
public import SupportingAnalysis.Basics
import SupportingAnalysis.Poisson.KernelBound
import SupportingAnalysis.Poisson.SquareBound
import SupportingAnalysis.Poisson.Limits

/-! Whole-space (L^p) Hessian bounds for the actual scalar Laplacian. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ContDiff ENNReal Topology

namespace Thesis

private theorem cutoffHessian_convolution_moment_bounds (A : ℝ) (hA : 0 ≤ A)
    (hWeak : ∀ (cutoff g : Point → ℝ), ContDiff ℝ ∞ cutoff → HasCompactSupport cutoff →
      Integrable g → ∀ (i j : Fin 3) (ell : ℝ), 0 < ell →
        volume {x | ell < |realKernelConvolution (fun y => SupportingAnalysis.scalarHessian cutoff y i j) g x|} ≤
          ENNReal.ofReal (A*((∫ x, |SupportingAnalysis.laplacian cutoff x|)*(∫ x, |g x|))/ell))
    (i j : Fin 3) (n : ℕ) :
    let K := SupportingAnalysis.truncatedNewtonHessian i j n
    Continuous K ∧ HasCompactSupport K ∧
      (∀ (f : Point → ℝ), Integrable f → ∀ t : ℝ, 0 < t →
        volume {x | t < |realKernelConvolution K f x|} ≤ ENNReal.ofReal ((2*A)*(∫ x, |f x|)/t)) ∧
      (∀ (f : Point → ℝ), Integrable f → MemLp f 2 →
        (∫ x, |realKernelConvolution K f x|^2) ≤ 4*(∫ x, |f x|^2)) := by
  intro K
  let χ := SupportingAnalysis.truncatedNewtonKernel 3 n
  obtain ⟨hχ,hχc⟩ := SupportingAnalysis.truncatedNewtonKernel_smooth_compact (by decide : 0 < 3) n
  have hDer := SupportingAnalysis.smooth_compact_scalarHessian hχ hχc i j
  have hBound := SupportingAnalysis.integral_abs_laplacian_truncatedNewtonKernel_le (by decide : 0 < 3) n
  change (∫ x, |SupportingAnalysis.laplacian χ x|) ≤ 2 at hBound
  refine ⟨hDer.1.continuous,hDer.2,?_,?_⟩
  · intro f hf t ht
    refine (hWeak χ f hχ hχc hf i j t ht).trans (ENNReal.ofReal_le_ofReal ?_)
    have hI : 0 ≤ ∫ x, |f x| := integral_nonneg fun _ => abs_nonneg _
    calc
      _ = A*(∫ x, |SupportingAnalysis.laplacian χ x|)*(∫ x, |f x|)/t := by ring
      _ ≤ A*2*(∫ x, |f x|)/t := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBound hA) hI) ht.le
      _ = _ := by ring
  · intro f hf hf₂
    have h := SupportingAnalysis.integral_sq_scalarHessian_convolution_le (by decide : 0 < 3) hχ hχc hf hf₂ i j
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ => sq_nonneg _))
    exact (pow_le_pow_left₀ (integral_nonneg fun _ => abs_nonneg _) hBound 2).trans_eq (by norm_num)

private theorem exists_cutoffHessian_convolution_Lp (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 3) (n : ℕ) (f : Point → ℝ), Continuous f → HasCompactSupport f →
      eLpNorm (realKernelConvolution (SupportingAnalysis.truncatedNewtonHessian i j n) f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨A,hA,hCW⟩ := SupportingAnalysis.kernelWeakHessian 3
  have hMom (i j : Fin 3) (n : ℕ) := cutoffHessian_convolution_moment_bounds A hA hCW i j n
  let C (s : ℝ) := (s*(2*(2*A)/(s-1)+4*4/(2-s)))^(s⁻¹)
  have hC (s : ℝ) (hs : 1 < s) (hs' : s < 2) : 0 < C s := by
    have hS : 0 < s := zero_lt_one.trans hs
    have hD₁ : 0 < s-1 := sub_pos.mpr hs
    have hD₂ : 0 < 2-s := sub_pos.mpr hs'
    dsimp only [C]
    positivity
  have hLow (s : ℝ) (hs : 1 < s) (hs' : s < 2) (i j : Fin 3) (n : ℕ)
      (f : Point → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
      eLpNorm (realKernelConvolution (SupportingAnalysis.truncatedNewtonHessian i j n) f) (ENNReal.ofReal s) volume ≤
        ENNReal.ofReal (C s) * eLpNorm f (ENNReal.ofReal s) volume := by
    obtain ⟨hK,hKc,hW,hS⟩ := hMom i j n
    have h := realKernelConvolution_intermediateLp hK hKc (show 0 ≤ 2*A by positivity)
      (by norm_num : (0:ℝ) ≤ 4) hW hS hs hs' hf hfc
    have hs₀ : 0 < s := zero_lt_one.trans hs
    have hD₁ : 0 < s-1 := sub_pos.mpr hs
    have hD₂ : 0 < 2-s := sub_pos.mpr hs'
    simpa only [C, ← ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ s*(2*(2*A)/(s-1)+4*4/(2-s)))
      (inv_nonneg.mpr hs₀.le)] using h
  rcases lt_trichotomy p 2 with h | rfl | h
  · exact ⟨C p,hC p hp h,hLow p hp h⟩
  · refine ⟨(4:ℝ)^((2:ℝ)⁻¹),by positivity,?_⟩
    intro i j n f hf hfc
    obtain ⟨hK,hKc,_,hS⟩ := hMom i j n
    have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
    have hf₂ : MemLp f 2 := hf.memLp_of_hasCompactSupport hfc
    simpa only [ENNReal.ofReal_ofNat] using
      realKernelConvolution_L2 hK hKc (by norm_num : (0:ℝ) ≤ 4) hfi hf₂ (hS f hfi hf₂)
  · let q := p.conjExponent
    have hq : 1 < q := (Real.HolderConjugate.conjExponent hp).symm.lt
    have hq₂ : q < 2 := by
      change p/(p-1) < 2
      apply (div_lt_iff₀ (sub_pos.mpr hp)).2
      linarith only [h]
    refine ⟨C q,hC q hq hq₂,?_⟩
    intro i j n f hf hfc
    obtain ⟨hK,hKc,_,_⟩ := hMom i j n
    exact realKernelConvolution_dualLp hK hKc h (hC q hq hq₂).le (hLow q hq hq₂ i j n) hf hfc

/-- The whole-space estimate for each second coordinate derivative. -/
theorem exists_wholeSpace_coordinatePoissonHessianLp (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Point → ℝ), ContDiff ℝ ∞ u → HasCompactSupport u → ∀ i j : Fin 3,
      eLpNorm (fun x => SupportingAnalysis.scalarHessian u x i j) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (laplacian u) (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC,hB⟩ := exists_cutoffHessian_convolution_Lp p hp
  refine ⟨C,hC,?_⟩
  intro u hu huc i j
  obtain ⟨hD,hDc⟩ := SupportingAnalysis.smooth_compact_laplacian hu huc
  have hDi : Integrable (laplacian u) := hD.continuous.integrable_of_hasCompactSupport hDc
  let g (n : ℕ) := realKernelConvolution (SupportingAnalysis.truncatedNewtonHessian i j n) (laplacian u)
  have hC' (n : ℕ) : Continuous (g n) := by
    obtain ⟨hχ,hχc⟩ := SupportingAnalysis.truncatedNewtonKernel_smooth_compact (by decide : 0 < 3) n
    obtain ⟨hH,hHc⟩ := SupportingAnalysis.smooth_compact_scalarHessian hχ hχc i j
    exact hHc.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hH.continuous hDi.locallyIntegrable
  apply eLpNorm_le_of_ae_tendsto_of_uniform_norm (zero_lt_one.trans hp) (g := g)
    (fun n => (hC' n).aestronglyMeasurable) ?_ (fun n => hB i j n _ hD.continuous hDc)
  exact Eventually.of_forall (SupportingAnalysis.tendsto_truncatedNewtonHessian_convolution_laplacian
    (by decide : 2 ≤ 3) i j hu huc)

private theorem sum_smul_axis_eq (v : Point) : (∑ i : Fin 3, v i • axis i) = v := by
  apply PiLp.ext
  intro j
  fin_cases j <;> simp [axis,Fin.sum_univ_three]

private theorem norm_scalar_iteratedFDeriv_two_le_coordinate_sum
    {u : Point → ℝ} (hu : ContDiff ℝ ∞ u) (x : Point) :
    ‖iteratedFDeriv ℝ 2 u x‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |SupportingAnalysis.scalarHessian u x j i| := by
  let D := fderiv ℝ (fderiv ℝ u) x
  have hc : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hDF : DifferentiableAt ℝ (fderiv ℝ u) x := hc.differentiable (by simp) x
  have hAxis (i j : Fin 3) : D (axis i) (axis j) = SupportingAnalysis.scalarHessian u x j i := by
    have h := ((ContinuousLinearMap.apply ℝ ℝ (axis j)).hasFDerivAt.comp x hDF.hasFDerivAt).fderiv
    exact (DFunLike.congr_fun h (axis i)).symm
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro m
  rw [Fin.prod_univ_two,iteratedFDeriv_two_apply]
  change ‖D (m 0) (m 1)‖ ≤ _
  have hCol (i : Fin 3) : D (axis i) (m 1) =
      ∑ j : Fin 3, ((m 1 : Point) j)*SupportingAnalysis.scalarHessian u x j i := by
    calc
      _ = D (axis i) (∑ j : Fin 3, ((m 1 : Point) j) • axis j) := by rw [sum_smul_axis_eq]
      _ = _ := by simp only [map_sum,map_smul,smul_eq_mul,hAxis]
  have hEval : D (m 0) (m 1) = ∑ i : Fin 3, ∑ j : Fin 3,
      ((m 0 : Point) i*(m 1 : Point) j)*SupportingAnalysis.scalarHessian u x j i := by
    calc
      _ = D (∑ i : Fin 3, ((m 0 : Point) i) • axis i) (m 1) := by rw [sum_smul_axis_eq]
      _ = ∑ i : Fin 3, ((m 0 : Point) i) * D (axis i) (m 1) := by
        simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul]
      _ = _ := by
        simp only [hCol,Finset.mul_sum,mul_assoc]
  rw [hEval,Real.norm_eq_abs,Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul,abs_mul,mul_comm]
  have hI : |(m 0 : Point) i| ≤ ‖m 0‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (m 0) i
  have hJ : |(m 1 : Point) j| ≤ ‖m 1‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (m 1) j
  exact mul_le_mul_of_nonneg_left (mul_le_mul hI hJ (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)

private theorem eLpNorm_doubleCoordinateSum_le {d : Fin 3 → Fin 3 → Point → ℝ} {q B : ℝ≥0∞}
    (hq : 1 ≤ q) (hC : ∀ i j, Continuous (d i j)) (hD : ∀ i j, eLpNorm (d i j) q volume ≤ B) :
    eLpNorm (fun x => ∑ i : Fin 3, ∑ j : Fin 3, d i j x) q volume ≤ 9*B := by
  let f (i : Fin 3) (x : Point) := ∑ j : Fin 3, d i j x
  have hF (i : Fin 3) : Continuous (f i) := continuous_finsetSum _ fun j _ => hC i j
  have hL (i : Fin 3) : eLpNorm (f i) q volume ≤ ∑ j : Fin 3, eLpNorm (d i j) q volume := by
    have hEq : f i = ∑ j : Fin 3, d i j := by funext x; simp [f,Finset.sum_apply]
    rw [hEq]
    exact eLpNorm_sum_le (fun j _ => (hC i j).aestronglyMeasurable) hq
  have hSum : (fun x => ∑ i : Fin 3, ∑ j : Fin 3, d i j x) = ∑ i : Fin 3, f i := by
    funext x
    simp [f,Finset.sum_apply]
  rw [hSum]
  refine (eLpNorm_sum_le (fun i _ => (hF i).aestronglyMeasurable) hq).trans ?_
  refine (Finset.sum_le_sum fun i _ => (hL i).trans (Finset.sum_le_sum fun j _ => hD i j)).trans_eq ?_
  simp only [Fin.sum_univ_three]
  ring

/-- The scalar whole-space Hessian estimate in the actual Fréchet operator norm. -/
theorem exists_wholeSpace_scalarPoissonHessianLp (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Point → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 u x‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (laplacian u) (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC,hCoord⟩ := exists_wholeSpace_coordinatePoissonHessianLp p hp
  refine ⟨9*C,by positivity,?_⟩
  intro u hu huc
  let q := ENNReal.ofReal p
  let d (i j : Fin 3) (x : Point) := |SupportingAnalysis.scalarHessian u x j i|
  let h (x : Point) := ∑ i : Fin 3, ∑ j : Fin 3, d i j x
  have hC' (i j : Fin 3) : Continuous (d i j) :=
    (SupportingAnalysis.smooth_compact_scalarHessian hu huc j i).1.continuous.abs
  have hq : 1 ≤ q := by
    change 1 ≤ ENNReal.ofReal p
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hE : eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 u x‖) q volume ≤ eLpNorm h q volume := by
    apply eLpNorm_mono_ae
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (norm_nonneg _),Real.norm_of_nonneg (by dsimp only [h,d]; positivity)]
      exact norm_scalar_iteratedFDeriv_two_le_coordinate_sum hu x
  have hD (i j : Fin 3) : eLpNorm (d i j) q volume ≤ ENNReal.ofReal C*eLpNorm (laplacian u) q volume := by
    have he := eLpNorm_congr_norm_ae (p := q) (μ := (volume : Measure Point))
      (f := d i j) (g := fun x => SupportingAnalysis.scalarHessian u x j i) (Eventually.of_forall fun x => by
        simp [d,Real.norm_eq_abs])
    exact he.le.trans (hCoord u hu huc j i)
  have hh := eLpNorm_doubleCoordinateSum_le hq hC' hD
  have hm : (9 : ℝ≥0∞)*ENNReal.ofReal C = ENNReal.ofReal (9*C) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9),ENNReal.ofReal_ofNat]
  exact hE.trans (hh.trans_eq (by rw [← mul_assoc,hm]))

end Thesis

end
