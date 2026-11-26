module

public import Thesis.Upstream.AmbientSobolevDifferenceQuotient
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import HarmonicMaps.Analysis.VariableMollificationL2

/-! Compact smooth tests converge in global (L^2) under coordinate difference quotients. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Topology

namespace Thesis

private theorem exists_norm_fderiv_le_of_compactSmooth {n q : ℕ}
    {φ : Domain n → Ambient q} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ≥0, ∀ x : Domain n, ‖fderiv ℝ φ x‖ ≤ C := by
  have hSupport := (hc.fderiv ℝ)
  obtain ⟨M,hM⟩ := hSupport.exists_bound_of_continuousOn
    (hφ.continuous_fderiv (by simp)).continuousOn
  let C : ℝ≥0 := ⟨max M 0,le_max_right _ _⟩
  refine ⟨C,fun x => ?_⟩
  by_cases hx : x ∈ tsupport (fderiv ℝ φ)
  · exact (hM x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    exact C.coe_nonneg

private theorem ambientDifferenceQuotient_norm_le {n q : ℕ}
    {φ : Domain n → Ambient q} {C : ℝ≥0} (hLip : LipschitzWith C φ)
    (i : Fin n) (h : ℝ) (x : Domain n) : ‖ambientDifferenceQuotient i h φ x‖ ≤ C := by
  by_cases hz : h = 0
  · simp only [ambientDifferenceQuotient,hz,inv_zero,zero_smul,norm_zero]
    exact C.coe_nonneg
  have hN : ‖φ (x+h • EuclideanSpace.single i 1)-φ x‖ ≤ (C : ℝ) * |h| := by
    have hDist := hLip.dist_le_mul (x+h • (EuclideanSpace.single i 1 : Domain n)) x
    have he : ‖x + h • (EuclideanSpace.single i 1 : Domain n) - x‖ = |h| := by
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,PiLp.norm_single,norm_one,mul_one]
    rw [dist_eq_norm,dist_eq_norm,he] at hDist
    exact hDist
  change ‖h⁻¹ • (φ (x+h • EuclideanSpace.single i 1)-φ x)‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_inv]
  calc
    _ ≤ |h|⁻¹ * ((C : ℝ) * |h|) := mul_le_mul_of_nonneg_left hN (inv_nonneg.mpr (abs_nonneg _))
    _ = C := by rw [mul_left_comm,inv_mul_cancel₀ (abs_ne_zero.mpr hz),mul_one]

/-- For a compact smooth test the normalized differences converge to the
displayed derivative in the same whole-space (L^2) norm. -/
theorem tendsto_ambientDifferenceQuotient_smooth_L2 {n q : ℕ}
    {φ : Domain n → Ambient q} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (i : Fin n) {h : ℕ → ℝ} (h0 : Tendsto h atTop (𝓝 0)) (hNe : ∀ k, h k ≠ 0) :
    Tendsto (fun k => eLpNorm
      (ambientDifferenceQuotient i (h k) φ - fun x => coordinateDerivative φ hφ i x)
      2 (volume : Measure (Domain n))) atTop (𝓝 0) := by
  let e : Domain n := EuclideanSpace.single i 1
  let d (x : Domain n) := coordinateDerivative φ hφ i x
  let q (k : ℕ) := ambientDifferenceQuotient i (h k) φ
  have he : ‖e‖ = 1 := by simp only [e,PiLp.norm_single,norm_one]
  have hdC : Continuous d :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdc : HasCompactSupport d := hc.fderiv_apply ℝ e
  have hdLp : MemLp d 2 volume := hdC.memLp_of_hasCompactSupport hdc
  have hφLp : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hqLp (k : ℕ) : MemLp (q k) 2 volume := memLp_ambientDifferenceQuotient hφLp i (h k)
  have hPoint (x : Domain n) : Tendsto (fun k => q k x) atTop (𝓝 (d x)) := by
    let P (s : ℝ) := x + s • e
    have hP : HasDerivAt P e 0 := by
      simpa only [P,id_eq,one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
    have hZ : P 0 = x := by simp [P]
    have hD := ((hφ.differentiable (by simp) (P 0)).hasFDerivAt).comp_hasDerivAt 0 hP
    have hEv : Tendsto h atTop (𝓝[≠] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.2 ⟨h0,Eventually.of_forall fun k => hNe k⟩
    have ht := hD.tendsto_slope_zero.comp hEv
    simpa only [Function.comp_def,P,hZ,zero_add,zero_smul,add_zero,q,
      ambientDifferenceQuotient,d,coordinateDerivative,e] using ht
  obtain ⟨C,hC⟩ := exists_norm_fderiv_le_of_compactSmooth hφ hc
  have hLip : LipschitzWith C φ :=
    lipschitzWith_of_nnnorm_fderiv_le (hφ.differentiable (by simp)) (fun x => hC x)
  have hqB (k : ℕ) (x : Domain n) : ‖q k x‖ ≤ C :=
    ambientDifferenceQuotient_norm_le hLip _ _ _
  have hdB (x : Domain n) : ‖d x‖ ≤ C := by
    change ‖fderiv ℝ φ x e‖ ≤ _
    exact ((fderiv ℝ φ x).le_opNorm e).trans (by rw [he,mul_one]; exact hC x)
  obtain ⟨A,hA⟩ := (Metric.isBounded_range_of_tendsto _ h0).exists_norm_le
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  let B := max R 0+max A 0+1
  let K := closedBall (0 : Domain n) B
  have hOut (x : Domain n) (hx : x ∉ K) : φ x = 0 ∧ d x = 0 ∧ ∀ k, q k x = 0 := by
    have hxR : B < ‖x‖ := not_le.mp (by simpa only [K,mem_closedBall_zero_iff] using hx)
    have hRlt : R < ‖x‖ := by
      dsimp only [B] at hxR
      linarith only [le_max_left R 0, le_max_right A 0,hxR]
    have hSupp : x ∉ tsupport φ := fun h => (not_lt_of_ge (hR _ h)) hRlt
    have hφ₀ := image_eq_zero_of_notMem_tsupport hSupp
    have hd₀ : d x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hSupp ((tsupport_fderiv_apply_subset ℝ e) h))
    refine ⟨hφ₀,hd₀,fun k => ?_⟩
    have hφ₁ : φ (x+h k • e) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxS
      have hy := hR _ hxS
      have hShift : ‖h k • e‖ ≤ A := by
        rw [norm_smul,he,mul_one]
        exact hA _ (mem_range_self k)
      have hNx : ‖x‖ ≤ ‖x+h k • e‖ + ‖h k • e‖ := by
        simpa only [add_sub_cancel_right] using norm_sub_le (x+h k • e) (h k • e)
      dsimp only [B] at hxR
      linarith only [hy,hShift,hNx,hxR,le_max_left R 0,le_max_left A 0]
    change (h k)⁻¹ • (φ (x+h k • e)-φ x) = _
    rw [hφ₁,hφ₀,sub_self,smul_zero]
  let M (x : Domain n) := K.indicator (fun _ => (2*(C : ℝ))^2) x
  have hM : Integrable M volume :=
    ((integrableOn_const (μ := (volume : Measure (Domain n))) (C := (2*(C : ℝ))^2)
      (isCompact_closedBall (0 : Domain n) B).measure_lt_top.ne).integrable_indicator
      isClosed_closedBall.measurableSet)
  have hBound (k : ℕ) (x : Domain n) : ‖‖q k x-d x‖^2‖ ≤ M x := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    change ‖q k x-d x‖^2 ≤ K.indicator (fun _ => (2*(C : ℝ))^2) x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
        ((add_le_add (hqB k x) (hdB x)).trans_eq (two_mul _).symm)) 2
    · rw [indicator_of_notMem hx,(hOut x hx).2.2 k,(hOut x hx).2.1,sub_self,norm_zero]
      simp
  apply tendsto_eLpNorm_two_zero_of_integral_norm_sq (fun k => (hqLp k).sub hdLp)
  have hMeas (k : ℕ) : AEStronglyMeasurable (fun x => ‖q k x-d x‖^2) volume :=
    (((hqLp k).sub hdLp).aestronglyMeasurable.norm.pow 2)
  have hL : ∀ᵐ x : Domain n, Tendsto (fun k => ‖q k x-d x‖^2) atTop (𝓝 0) :=
    Eventually.of_forall fun x => by
      simpa only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] using
        ((hPoint x).sub_const (d x)).norm.pow 2
  simpa only [Pi.sub_apply,integral_zero] using
    tendsto_integral_of_dominated_convergence M hMeas hM
      (fun k => Eventually.of_forall (hBound k)) hL

end Thesis
