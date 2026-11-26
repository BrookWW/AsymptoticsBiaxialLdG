module

public import Thesis.Upstream.LpTranslationAverages
import Mathlib.Analysis.Calculus.TaylorIntegral

/-! An adjustable first-derivative bound for smooth compact scalar fields. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ContDiff ENNReal Topology

namespace Thesis

private theorem abs_axisDerivative_le_taylor_average {u : Point → ℝ} (hu : ContDiff ℝ ∞ u)
    {r : ℝ} (hr : 0 < r) (i : Fin 3) (x : Point) :
    |coordDeriv i u x| ≤ r⁻¹*(|u (x+r • axis i)|+|u x|) +
      r * (∫ t in Ioc (0:ℝ) 1, ‖iteratedFDeriv ℝ 2 u (x+t • (r • axis i))‖) := by
  let z := r • axis i
  let H (t : ℝ) := ‖iteratedFDeriv ℝ 2 u (x+t • z)‖
  let P (t : ℝ) := (1-t) • iteratedFDeriv ℝ 2 u (x+t • z) (fun _ => z)
  let R := ∫ t in Ioc (0:ℝ) 1, P t
  have hDer : u (x+z) = u x+r*coordDeriv i u x + R := by
    have hT := map_add_eq_sum_add_integral_iteratedFDeriv (x := x) (y := z) (n := 1)
      (fun t _ => (hu.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt (x := x+t • z))
    simpa [Finset.sum_range_succ,iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),P,R,z,coordDeriv,smul_eq_mul] using hT
  have hP (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) : ‖P t‖ ≤ r^2*H t := by
    have hF := (iteratedFDeriv ℝ 2 u (x+t • z)).le_opNorm (fun _ => z)
    have hz : ‖z‖ = r := by
      dsimp only [z]
      rw [norm_smul,Real.norm_of_nonneg hr.le,show ‖axis i‖=1 by simp [axis],mul_one]
    rw [Fin.prod_univ_two,hz,← pow_two] at hF
    dsimp only [P]
    rw [norm_smul,Real.norm_of_nonneg (sub_nonneg.mpr ht.2)]
    exact ((mul_le_mul_of_nonneg_right (sub_le_self _ ht.1.le) (norm_nonneg _)).trans_eq
      (one_mul _)).trans (hF.trans_eq (mul_comm _ _))
  have hHC : Continuous H := (hu.continuous_iteratedFDeriv (m := 2)
    (WithTop.coe_le_coe.mpr le_top)).norm.comp (by fun_prop)
  have hHI : Integrable H (volume.restrict (Ioc (0:ℝ) 1)) := (hHC.intervalIntegrable 0 1).1
  have hR : |R| ≤ r^2*(∫ t in Ioc (0:ℝ) 1, H t) := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hHI.const_mul (r^2)) ?_).trans_eq (integral_const_mul _ _)
    exact (ae_restrict_mem measurableSet_Ioc).mono (fun t ht => hP t ht)
  have hForm : r*coordDeriv i u x = u (x+z)-u x-R := by linarith only [hDer]
  have hD : r*|coordDeriv i u x| ≤ |u (x+z)|+|u x|+r^2*(∫ t in Ioc (0:ℝ) 1, H t) := by
    rw [show r*|coordDeriv i u x| = |r*coordDeriv i u x| by rw [abs_mul,abs_of_nonneg hr.le],hForm]
    exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) hR)
  calc
    _ ≤ (|u (x+z)|+|u x|+r^2*(∫ t in Ioc (0:ℝ) 1, H t))/r :=
      (le_div_iff₀ hr).2 (by simpa only [mul_comm |coordDeriv i u x| r] using hD)
    _ = _ := by
      dsimp only [H,z]
      field_simp

/-- The scalar derivative norm is controlled by the sum of its coordinate sizes. -/
theorem norm_fderiv_le_sum_axisDerivative (u : Point → ℝ) (x : Point) :
    ‖fderiv ℝ u x‖ ≤ ∑ i : Fin 3, |coordDeriv i u x| := by
  let D := fderiv ℝ u x
  apply ContinuousLinearMap.opNorm_le_bound D (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  intro w
  have hw : (∑ j : Fin 3, w j • axis j) = w := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,axis] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
  have hDw : D w = ∑ j : Fin 3, w j * D (axis j) := by
    calc
      _ = D (∑ j : Fin 3, w j • axis j) := by rw [hw]
      _ = _ := by simp only [map_sum,map_smul,smul_eq_mul]
  rw [hDw, Real.norm_eq_abs,Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul,mul_comm]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w j) (abs_nonneg _)

private theorem eLpNorm_nonnegative_const_mul (a : ℝ) (ha : 0 ≤ a) (g : Point → ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun x => a*g x) q volume = ENNReal.ofReal a*eLpNorm g q volume := by
  have hEq : (fun x => a*g x) = a • g := by funext x; rfl
  rw [hEq,eLpNorm_const_smul,← ofReal_norm,Real.norm_of_nonneg ha]

private theorem eLpNorm_axisDerivative_le_taylor_average {u : Point → ℝ} (hu : ContDiff ℝ ∞ u)
    (huc : HasCompactSupport u) {p : ℝ} (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) (i : Fin 3) :
    eLpNorm (fun x => |coordDeriv i u x|) (ENNReal.ofReal p) volume ≤
      2*ENNReal.ofReal (r⁻¹)*eLpNorm u (ENNReal.ofReal p) volume +
        ENNReal.ofReal r*eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 u x‖) (ENNReal.ofReal p) volume := by
  let q := ENNReal.ofReal p
  have hq : 1 ≤ q := by
    change 1 ≤ ENNReal.ofReal p
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  let z := r • axis i
  let μ := volume.restrict (Ioc (0:ℝ) 1)
  letI : IsProbabilityMeasure μ := ⟨by dsimp only [μ]; simp [Real.volume_Ioc]⟩
  let H (x : Point) := ‖iteratedFDeriv ℝ 2 u x‖
  let G (x : Point) := ∫ t, H (x+t • z) ∂μ
  let g (x : Point) := |u (x+z)|+|u x|
  have hH : Continuous H := (hu.continuous_iteratedFDeriv (m := 2) (WithTop.coe_le_coe.mpr le_top)).norm
  have hHc : HasCompactSupport H := (huc.iteratedFDeriv (𝕜 := ℝ) 2).norm
  obtain ⟨M,hM⟩ := hH.bounded_above_of_compact_support hHc
  have hGNorm : eLpNorm G q volume ≤ eLpNorm H q volume :=
    eLpNorm_translationAverage_le μ (θ := fun t : ℝ => t • z) (by fun_prop) hH.stronglyMeasurable hM hp
  have hGC : StronglyMeasurable G := by
    let F (x : Point) (t : ℝ) := H (x+t • z)
    have hF : Continuous (Function.uncurry F) := by
      change Continuous (fun y : Point × ℝ => H (y.1+y.2 • z))
      fun_prop
    exact hF.stronglyMeasurable.integral_prod_right (ν := μ)
  have hg : Continuous g := by dsimp only [g]; fun_prop
  have hgLp : eLpNorm g q volume ≤ (2:ℝ≥0∞)*eLpNorm u q volume := by
    let u₁ (x : Point) := |u (x+z)|
    let u₂ (x : Point) := |u x|
    have h₁ : eLpNorm u₁ q volume = eLpNorm u q volume := by
      have hd : u₁ = u₂ ∘ (fun x => x+z) := rfl
      rw [hd,eLpNorm_comp_measurePreserving hu.continuous.abs.aestronglyMeasurable
        (measurePreserving_add_right volume z)]
      simpa only [u₂,← Real.norm_eq_abs] using eLpNorm_norm (p := q) (μ := (volume : Measure Point)) u
    have h₂ : eLpNorm u₂ q volume = eLpNorm u q volume := by
      simpa only [u₂,← Real.norm_eq_abs] using eLpNorm_norm (p := q) (μ := (volume : Measure Point)) u
    have hc₁ : Continuous u₁ := by dsimp only [u₁]; fun_prop
    have hc₂ : Continuous u₂ := hu.continuous.abs
    have hBound := eLpNorm_add_le (μ := (volume : Measure Point))
      hc₁.aestronglyMeasurable hc₂.aestronglyMeasurable hq
    simpa only [show g = u₁+u₂ from rfl,h₁,h₂,two_mul] using hBound
  have hMono : eLpNorm (fun x => |coordDeriv i u x|) q volume ≤
      eLpNorm ((r⁻¹ • g)+(r • G)) q volume := by
    apply eLpNorm_mono_ae
    refine Eventually.of_forall fun x => ?_
    have hA : 0 ≤ r⁻¹*g x+r*G x := by
      have hg₀ : 0 ≤ g x := add_nonneg (abs_nonneg _) (abs_nonneg _)
      have hG₀ : 0 ≤ G x := integral_nonneg fun _ => norm_nonneg _
      positivity
    change ‖|coordDeriv i u x|‖ ≤ ‖r⁻¹*g x+r*G x‖
    rw [Real.norm_of_nonneg (abs_nonneg _),Real.norm_of_nonneg hA]
    exact abs_axisDerivative_le_taylor_average hu hr i x
  refine hMono.trans ((eLpNorm_add_le (hg.const_smul _).aestronglyMeasurable
    (hGC.const_smul _).aestronglyMeasurable hq).trans ?_)
  have hr₁ : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  simp only [eLpNorm_const_smul,← ofReal_norm,Real.norm_of_nonneg hr.le,Real.norm_of_nonneg hr₁]
  exact (add_le_add (mul_le_mul_right hgLp (ENNReal.ofReal r⁻¹))
    (mul_le_mul_right hGNorm (ENNReal.ofReal r))).trans_eq (by ring)

/-- For every positive coefficient on the second derivative, a uniform
whole-space interpolation estimate controls the first derivative. -/
theorem exists_wholeSpace_scalarGradientInterpolation (p δ : ℝ) (hp : 1 < p) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Point → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal δ*eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 u x‖) (ENNReal.ofReal p) volume +
          ENNReal.ofReal C*eLpNorm u (ENNReal.ofReal p) volume := by
  let r := δ/3
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr₁ : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  refine ⟨6*r⁻¹,by positivity,?_⟩
  intro u hu huc
  let q := ENNReal.ofReal p
  have hq : 1 ≤ q := by
    change 1 ≤ ENNReal.ofReal p
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  let d (i : Fin 3) (x : Point) := |coordDeriv i u x|
  have hD (i : Fin 3) : Continuous (d i) :=
    (((hu.continuous_fderiv (by simp)).clm_apply continuous_const)).abs
  have hB (i : Fin 3) := eLpNorm_axisDerivative_le_taylor_average hu huc hp.le hr i
  have hLe : eLpNorm (fderiv ℝ u) q volume ≤ eLpNorm (∑ i : Fin 3, d i) q volume := by
    apply eLpNorm_mono_ae
    refine Eventually.of_forall fun x => ?_
    rw [Finset.sum_apply,Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
    exact norm_fderiv_le_sum_axisDerivative u x
  refine hLe.trans ((eLpNorm_sum_le (fun i _ => (hD i).aestronglyMeasurable) hq).trans ?_)
  refine (Finset.sum_le_sum (fun i _ => hB i)).trans_eq ?_
  have hR : (3:ℝ≥0∞)*ENNReal.ofReal r = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    dsimp only [r]
    ring
  have hL : (6:ℝ≥0∞)*ENNReal.ofReal r⁻¹ = ENNReal.ofReal (6*r⁻¹) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 6),ENNReal.ofReal_ofNat]
  rw [← hR,← hL]
  simp only [Fin.sum_univ_three]
  ring

end Thesis

end
