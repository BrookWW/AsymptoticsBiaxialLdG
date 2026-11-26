module

public import Thesis.Upstream.WholeSpacePoissonHessianLp
import Thesis.Upstream.LpTranslationAverages
import SupportingAnalysis.Poisson.Regularization
import SupportingAnalysis.Poisson.Equation
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Approximation of compact smooth data by actual compact-test Laplacians. -/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set
open scoped BigOperators ContDiff Convolution ENNReal NNReal Topology

namespace Thesis

private def radialAverage (k : SupportingAnalysis.RadialProbabilityDensity 3) (r : ℝ)
    (f : Point → ℝ) : Point → ℝ :=
  k.scaled r ⋆[ContinuousLinearMap.mul ℝ ℝ] f

private theorem norm_radialAverage_le_integral {f : Point → ℝ} (hI : Integrable f)
    (k : SupportingAnalysis.RadialProbabilityDensity 3) {r : ℝ} (hr : 0 < r)
    {C : ℝ} (hC : ∀ x, ‖k.density x‖ ≤ C) (x : Point) :
    ‖radialAverage k r f x‖ ≤ (r^3)⁻¹ * (C * ∫ y, ‖f y‖) := by
  rw [radialAverage,convolution_mul_swap,← mul_assoc,← integral_const_mul]
  apply norm_integral_le_of_norm_le (hI.norm.const_mul ((r^3)⁻¹*C))
  exact Eventually.of_forall fun y => by
    rw [norm_mul,SupportingAnalysis.RadialProbabilityDensity.scaled,norm_mul,
      Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hC _) (inv_nonneg.mpr (pow_nonneg hr.le _))) (norm_nonneg _)

private theorem radialAverage_L1_le {f : Point → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (k : SupportingAnalysis.RadialProbabilityDensity 3) {r : ℝ}
    (hr : 0 < r) :
    (∫ x, ‖radialAverage k r f x‖) ≤ ∫ x, ‖f x‖ := by
  let g := radialAverage k r f
  have hg : Continuous g := hfc.continuous_convolution_right _
    (k.scaled_integrable hr).locallyIntegrable hf
  obtain ⟨M,hM⟩ := hfc.exists_bound_of_continuous hf
  have h := eLpNorm_probabilityKernelConvolution_le (k.scaled_smooth r).continuous.measurable
    (k.scaled_nonnegative r hr) (k.scaled_integrable hr) (k.scaled_mass hr)
    hf.stronglyMeasurable hM (p := 1) le_rfl
  have he : eLpNorm g 1 volume ≤ eLpNorm f 1 volume := by
    have hgEq : g = (fun x => ∫ t, k.scaled r t • f (x-t)) := by
      funext x
      change (k.scaled r ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x = _
      rw [convolution_mul]
      rfl
    rw [hgEq]
    simpa only [ENNReal.ofReal_one] using h
  have hN := ENNReal.toReal_mono (hf.memLp_of_hasCompactSupport (p := 1) hfc).eLpNorm_ne_top he
  simpa only [toReal_eLpNorm hg.aestronglyMeasurable,toReal_eLpNorm hf.aestronglyMeasurable,
    lpNorm_one_eq_integral_norm hg.aestronglyMeasurable,lpNorm_one_eq_integral_norm hf.aestronglyMeasurable] using hN

theorem exists_global_lipschitz_of_smooth_compact {f : Point → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ L : ℝ≥0, LipschitzWith L f := by
  obtain ⟨M,hM⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  let L : ℝ≥0 := ⟨max M 0,le_max_right _ _⟩
  refine ⟨L,lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) (fun x => ?_)⟩
  exact (hM x).trans (le_max_left _ _)

private theorem tendsto_eLpNorm_radialAverage_sub_small {f : Point → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (k : SupportingAnalysis.RadialProbabilityDensity 3)
    {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    Tendsto (fun n : ℕ => eLpNorm ((radialAverage k (((n : ℝ)+1)⁻¹) f) - f) p volume)
      atTop (𝓝 0) := by
  obtain ⟨L,hL⟩ := exists_global_lipschitz_of_smooth_compact hf hfc
  obtain ⟨r,hr⟩ := hfc.isCompact.isBounded.exists_norm_le
  let S := closedBall (0 : Point) (r+1)
  have hFS : support f ⊆ S := fun x hx =>
    mem_closedBall_zero_iff.mpr ((hr x (subset_tsupport f hx)).trans (le_add_of_nonneg_right zero_le_one))
  let ε (n : ℕ) : ℝ := ((n : ℝ)+1)⁻¹
  have hεp (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hε₁ (n : ℕ) : ε n ≤ 1 := inv_le_one_of_one_le₀
    (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let c := volume S ^ (1/p.toReal)
  have hc : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_closedBall_lt_top.ne
  have hNorm (n : ℕ) : eLpNorm (radialAverage k (ε n) f - f) p volume ≤
      ENNReal.ofReal ((L : ℝ)*ε n)*c := by
    apply eLpNorm_sub_le_of_dist_bdd volume hp measurableSet_closedBall
      (mul_nonneg L.coe_nonneg (hεp n).le) _ _ hFS
    · intro x
      have he := dist_convolution_le (μ := (volume : Measure Point)) (g := f) (x₀ := x) (z₀ := f x)
        (ε := (L : ℝ)*ε n) (mul_nonneg L.coe_nonneg (hεp n).le)
        (k.scaled_support_subset (hεp n)) (k.scaled_nonnegative (ε n) (hεp n))
        (k.scaled_mass (hεp n)) hf.continuous.aestronglyMeasurable (fun y hy =>
          (hL.dist_le_mul y x).trans
            (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le L.coe_nonneg))
      exact he
    · intro x hx
      obtain ⟨y,hy,z,hz,rfl⟩ :=
        (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)) hx
      apply mem_closedBall_zero_iff.mpr
      refine (norm_add_le _ _).trans ?_
      have hy' := mem_ball_zero_iff.mp (k.scaled_support_subset (hεp n) hy)
      linarith only [hy',hε₁ n,hr z (subset_tsupport f hz)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun _ => zero_le) hNorm
  have he := ENNReal.tendsto_ofReal (by simpa only [mul_zero] using hεlim.const_mul (L : ℝ))
  have h := ENNReal.Tendsto.mul_const (b := c) he (Or.inr hc)
  simpa only [ENNReal.ofReal_zero,zero_mul] using h

private theorem lpNorm_nat_eq_moment {f : Point → ℝ} {m : ℕ} (hm : m ≠ 0)
    (hf : AEStronglyMeasurable f volume) :
    lpNorm f (m : ℝ≥0∞) volume = (∫ x, ‖f x‖^m)^((m : ℝ)⁻¹) := by
  have h := lpNorm_eq_integral_norm_rpow_toReal (p := (m : ℝ≥0∞))
    (by exact_mod_cast hm) (ENNReal.natCast_ne_top m) hf
  simpa only [ENNReal.toReal_natCast,Real.rpow_natCast,one_div] using h

private theorem tendsto_eLpNorm_radialAverage_large {f : Point → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (k : SupportingAnalysis.RadialProbabilityDensity 3)
    {m : ℕ} (hm : 1 < m) :
    Tendsto (fun n : ℕ => eLpNorm (radialAverage k ((n : ℝ)+1) f) (m : ℝ≥0∞) volume)
      atTop (𝓝 0) := by
  let R (n : ℕ) : ℝ := (n : ℝ)+1
  have hR (n : ℕ) : 0 < R n := by dsimp only [R]; positivity
  have hI : Integrable f volume := hf.integrable_of_hasCompactSupport hfc
  have hkC : HasCompactSupport k.density := by
    rw [← k.scaled_one]
    exact k.scaled_hasCompactSupport zero_lt_one
  obtain ⟨M,hM⟩ := hkC.exists_bound_of_continuous k.smooth.continuous
  let B := max M 0*(∫ x, ‖f x‖)
  have hB : 0 ≤ B := mul_nonneg (le_max_right _ _) (integral_nonneg fun _ => norm_nonneg _)
  let A (n : ℕ) : ℝ := (R n ^ 3)⁻¹*B
  have hA₀ (n : ℕ) : 0 ≤ A n := mul_nonneg (inv_nonneg.mpr (pow_nonneg (hR n).le _)) hB
  have hAlim : Tendsto A atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (R n)⁻¹) atTop (𝓝 0) := by
      simpa only [R,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [A,inv_pow,zero_pow (by decide : (3 : ℕ) ≠ 0),zero_mul] using (hh.pow 3).mul_const B
  let g (n : ℕ) := radialAverage k (R n) f
  have hg (n : ℕ) : Continuous (g n) := hfc.continuous_convolution_right _
    (k.scaled_integrable (hR n)).locallyIntegrable hf
  have hgc (n : ℕ) : HasCompactSupport (g n) := by
    change HasCompactSupport (k.scaled (R n) ⋆[ContinuousLinearMap.mul ℝ ℝ] f)
    exact HasCompactSupport.convolution (μ := volume) (ContinuousLinearMap.mul ℝ ℝ)
      (k.scaled_hasCompactSupport (hR n)) hfc
  have hLp (n : ℕ) : MemLp (g n) (m : ℝ≥0∞) volume := (hg n).memLp_of_hasCompactSupport (hgc n)
  have hAbs (n : ℕ) (x : Point) : ‖g n x‖ ≤ A n :=
    norm_radialAverage_le_integral hI k (hR n) (fun x => (hM x).trans (le_max_left _ _)) x
  have hPower (n : ℕ) : (∫ x, ‖g n x‖^m) ≤ A n^(m-1)*(∫ x, ‖f x‖) := by
    have h₁ : Integrable (fun x => ‖g n x‖^m) volume := by
      simpa only [ENNReal.toReal_natCast,Real.rpow_natCast] using
        (hLp n).integrable_norm_pow (by exact_mod_cast (show m ≠ 0 by omega))
    have h₂ : Integrable (fun x => A n^(m-1)*‖g n x‖) volume :=
      ((hg n).integrable_of_hasCompactSupport (hgc n)).norm.const_mul (A n^(m-1))
    refine (integral_mono h₁ h₂ (fun x => ?_)).trans ?_
    · rw [show m = (m-1)+1 by omega,pow_succ]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hAbs n x) _) (norm_nonneg _)
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (radialAverage_L1_le hf hfc k (hR n)) (pow_nonneg (hA₀ n) _)
  let E (n : ℕ) := (A n^(m-1)*(∫ x, ‖f x‖))^((m : ℝ)⁻¹)
  have hElim : Tendsto E atTop (𝓝 0) := by
    have hh := (hAlim.pow (m-1)).mul_const (∫ x, ‖f x‖)
    have hm' : m-1 ≠ 0 := by omega
    have hh' : Tendsto (fun n => A n^(m-1)*(∫ x, ‖f x‖)) atTop (𝓝 0) := by
      simpa only [zero_pow hm',zero_mul] using hh
    have hPos : 0 < (m : ℝ)⁻¹ := by positivity
    simpa only [E,Function.comp_def,Real.zero_rpow hPos.ne'] using
      ((Real.continuous_rpow_const hPos.le).continuousAt (x := 0)).tendsto.comp hh'
  have hEL (n : ℕ) : eLpNorm (g n) (m : ℝ≥0∞) volume ≤ ENNReal.ofReal (E n) := by
    rw [← ofReal_lpNorm (hLp n),lpNorm_nat_eq_moment (by omega : m ≠ 0) (hg n).aestronglyMeasurable]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _)
      (hPower n) (by positivity))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hElim)
    (fun _ => zero_le) hEL

/-- One compact smooth family gives convergent actual Laplacians in every
finite integer exponent greater than one for a given compact smooth force. -/
theorem exists_compactSmooth_laplacian_test_approximation {f : Point → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ φ : ℕ → Point → ℝ, (∀ n, ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n)) ∧
      ∀ m : ℕ, 1 < m →
        Tendsto (fun n => eLpNorm (laplacian (φ n)-f) (m : ℝ≥0∞) volume) atTop (𝓝 0) := by
  let k := SupportingAnalysis.newtonRadialProbability 3
  let R (n : ℕ) : ℝ := (n : ℝ)+1
  have hR (n : ℕ) : 0 < R n := by dsimp only [R]; positivity
  let χ (n : ℕ) := SupportingAnalysis.truncatedNewtonKernel 3 n
  let φ (n : ℕ) := f ⋆[ContinuousLinearMap.mul ℝ ℝ] χ n
  have hχ (n : ℕ) := SupportingAnalysis.truncatedNewtonKernel_smooth_compact (by decide : 0 < 3) n
  have hfI : Integrable f volume := hf.continuous.integrable_of_hasCompactSupport hfc
  have hφ (n : ℕ) : ContDiff ℝ ∞ (φ n) :=
    (hχ n).2.contDiff_convolution_right _ hfI.locallyIntegrable (hχ n).1
  have hDiff (n : ℕ) : laplacian (φ n) = radialAverage k (R n)⁻¹ f - radialAverage k (R n) f := by
    funext x
    have he := SupportingAnalysis.laplacian_convolution f hfI.locallyIntegrable (hχ n).1 (hχ n).2 x
    change laplacian (φ n) x = ∫ y, f y * laplacian (χ n) (x-y) at he
    rw [he,show laplacian (χ n) = k.scaled (R n)⁻¹ - k.scaled (R n) from
      SupportingAnalysis.laplacian_truncatedNewtonKernel (by decide : 0 < 3) n]
    have hI (r : ℝ) (hr : 0 < r) : Integrable (fun y => f y*k.scaled r (x-y)) :=
      ((k.scaled_hasCompactSupport hr).convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
        hfI.locallyIntegrable (k.scaled_smooth r).continuous x).integrable
    simp only [Pi.sub_apply,mul_sub,radialAverage,convolution_mul_swap]
    rw [integral_sub (hI _ (inv_pos.mpr (hR n))) (hI _ (hR n))]
    congr 1 <;> apply integral_congr_ae <;> exact Eventually.of_forall fun _ => mul_comm _ _
  refine ⟨φ,fun n => ⟨hφ n,?_⟩,fun m hm => ?_⟩
  · exact HasCompactSupport.convolution (μ := volume) (ContinuousLinearMap.mul ℝ ℝ) hfc (hχ n).2
  have hSmall := tendsto_eLpNorm_radialAverage_sub_small hf hfc k (p := (m : ℝ≥0∞)) (ENNReal.natCast_ne_top m)
  have hLarge := tendsto_eLpNorm_radialAverage_large hf.continuous hfc k hm
  have hS := hSmall.add hLarge
  have hCont (r : ℝ) (hr : 0 < r) : Continuous (radialAverage k r f) :=
    hfc.continuous_convolution_right _ (k.scaled_integrable hr).locallyIntegrable hf.continuous
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using hS) (fun _ => zero_le)
  intro n
  dsimp only
  rw [hDiff,sub_right_comm]
  exact eLpNorm_sub_le ((hCont _ (inv_pos.mpr (hR n))).aestronglyMeasurable.sub hf.continuous.aestronglyMeasurable)
    (hCont _ (hR n)).aestronglyMeasurable (by exact_mod_cast hm.le)

end Thesis
