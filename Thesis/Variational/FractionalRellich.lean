module

public import Thesis.Variational.FractionalFiniteAverages
public import Thesis.Variational.FractionalEnergyInterpolation
public import Thesis.Variational.FractionalL2Duality
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Intrinsic fractional compactness on the actual smooth bounded domain. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem exists_uniform_fractionalEnergy_bound
    {U : Set Point} (t : ℝ) (u : ℕ → Point → S0) (hM : ∀ n, MemHs t U (u n))
    (hB : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ᶠ n in atTop, fractionalEnergy t U (u n) ≤ C) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, fractionalEnergy t U (u n) ≤ C := by
  obtain ⟨C,hC,hEv⟩ := hB
  obtain ⟨N,hN⟩ := eventually_atTop.mp hEv
  let B := ∑ n ∈ Finset.range N, fractionalEnergy t U (u n)
  have hB₁ : B < ⊤ := ENNReal.sum_lt_top.mpr fun n _ => (hM n).2
  refine ⟨C+B, ENNReal.add_lt_top.2 ⟨hC,hB₁⟩,?_⟩
  intro n
  by_cases hn : n < N
  · exact (Finset.single_le_sum (f := fun n => fractionalEnergy t U (u n))
      (fun _ _ => zero_le) (Finset.mem_range.mpr hn)).trans (self_le_add_left _ _)
  · exact (hN n (le_of_not_gt hn)).trans (self_le_add_right _ _)

private theorem memHs_of_L2_tendsto_and_bounded_energy
    {U : Set Point} (t : ℝ) {u : ℕ → Lp S0 2 (volume.restrict U)} {v : Lp S0 2 (volume.restrict U)}
    {C : ℝ≥0∞} (hC : C < ⊤) (hLim : Tendsto u atTop (𝓝 v))
    (hBound : ∀ᶠ n in atTop, fractionalEnergy t U (u n) ≤ C) : MemHs t U v := by
  obtain ⟨κ,hκ,hAe⟩ := (tendstoInMeasure_of_tendsto_Lp hLim).exists_seq_tendsto_ae
  have hV : AEStronglyMeasurable (v : Point → S0) (volume.restrict U) := Lp.aestronglyMeasurable v
  have hEn := nonlocal_energy_bounded_of_tendsto_ae t
    (fun n => Lp.aestronglyMeasurable (u (κ n))) hV hAe (hκ.tendsto_atTop.eventually hBound)
  have hL : (∫⁻ x in U, ENNReal.ofReal (‖v x‖ ^ 2)) < ⊤ :=
    (lintegral_sq_norm_lp (volume.restrict U) v).trans_lt ENNReal.ofReal_lt_top
  exact ⟨hV, ENNReal.add_lt_top.2 ⟨hL,hEn.trans_lt hC⟩⟩

private theorem tendsto_fractionalEnergy_of_L2_and_higher_bound
    {U : Set Point} (hU : IsBoundedDomain U) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (u : ℕ → Point → S0) (hM : ∀ n, AEStronglyMeasurable (u n) (volume.restrict U))
    (hL : Tendsto (fun n => eLpNorm (u n) 2 (volume.restrict U) ^ 2) atTop (𝓝 0))
    {C : ℝ≥0∞} (hC : C < ⊤) (hB : ∀ᶠ n in atTop, fractionalEnergy t U (u n) ≤ C) :
    Tendsto (fun n => fractionalEnergy s U (u n)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro δ hδ
  have hHalf : 0 < δ/2 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨r,hr,_,hSmall⟩ := exists_small_positive_ofReal_rpow_mul
    (by linarith : 0 < 2*(t-s)) zero_lt_one hC hHalf
  let B := 1 + ENNReal.ofReal (2 / r ^ (3 + 2 * s)) * (2 * volume U)
  have hVol : volume U < ⊤ := hU.2.2.measure_lt_top
  have hB₁ : B < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top (by simp) hVol)⟩
  have hRest : Tendsto (fun n => B * (eLpNorm (u n) 2 (volume.restrict U) ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (ENNReal.continuous_const_mul hB₁.ne).continuousAt.tendsto.comp hL
  filter_upwards [hB, ENNReal.tendsto_nhds_zero.1 hRest (δ/2) hHalf] with n hn hR
  have hMain : ENNReal.ofReal (r ^ (2*(t-s))) * fractionalEnergy t U (u n) ≤ δ/2 :=
    ((mul_le_mul' le_rfl hn).trans_eq (mul_comm _ _)).trans hSmall.le
  calc
    _ ≤ ENNReal.ofReal (r ^ (2*(t-s))) * fractionalEnergy t U (u n) +
        B * (eLpNorm (u n) 2 (volume.restrict U) ^ 2) :=
      fractionalEnergy_le_interpolation (u n) (hM n) hs hst hr
    _ ≤ δ / 2 + δ / 2 := add_le_add hMain hR
    _ = δ := ENNReal.add_halves δ

private theorem eLpNorm_difference_tensor_sq_eq_dist
    {μ : Measure Point} (p v : Lp S0 2 μ) {u : Point → S0} (hU : (p : Point → S0) =ᵐ[μ] u) :
    eLpNorm (u - (v : Point → S0)) 2 μ ^ 2 = ENNReal.ofReal (dist p v ^ 2) := by
  rw [eLpNorm_two_sq_eq_tensor_lintegral, dist_eq_norm, ← lintegral_sq_norm_lp μ (p-v)]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub p v, hU] with x hx hpx
  have h : (p-v : Lp S0 2 μ) x = (u-(v : Point → S0)) x :=
    hx.trans (congrArg (· - v x) hpx)
  rw [h]

/-- Native fractional Rellich compactness for the frozen intrinsic
norms, with a single subsequence and no boundary extension premise. -/
theorem fractionalSobolevCompactEmbedding : External.FractionalSobolevCompactEmbedding := by
  intro U hU s t hs hst _ u hM hB
  obtain ⟨C,hC,hCseq⟩ := exists_uniform_fractionalEnergy_bound t u hM hB
  let μ := volume.restrict U
  have hLp (n : ℕ) : MemLp (u n) 2 μ :=
    memLp_two_of_finite_tensor_square (hM n).1 ((self_le_add_right _ _).trans_lt (hM n).2)
  let p (n : ℕ) : Lp S0 2 μ := (hLp n).toLp (u n)
  have hP (n : ℕ) : (p n : Point → S0) =ᵐ[μ] u n := (hLp n).coeFn_toLp
  have hB' (n : ℕ) : fractionalEnergy t U (p n) ≤ C :=
    (fractionalEnergy_congr_ae (hP n)).le.trans (hCseq n)
  have hPos : 0 < t := hs.trans hst
  obtain ⟨κ,v,hκ,hLim⟩ := exists_L2_subsequence_of_bounded_fractionalEnergy hU t hPos p C hC hB'
  have hV : MemHs t U v :=
    memHs_of_L2_tendsto_and_bounded_energy t hC hLim (.of_forall fun n => hB' (κ n))
  let w (n : ℕ) : Point → S0 := u (κ n) - (v : Point → S0)
  have hDist : Tendsto (fun n => dist (p (κ n)) v) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, dist_self] using
      hLim.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (𝓝 v))
  have hL : Tendsto (fun n => eLpNorm (w n) 2 μ ^ 2) atTop (𝓝 0) := by
    have h : Tendsto (fun n => ENNReal.ofReal (dist (p (κ n)) v ^ 2)) atTop (𝓝 0) := by
      simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0), ENNReal.ofReal_zero]
        using ENNReal.tendsto_ofReal (hDist.pow 2)
    refine h.congr' (.of_forall fun n => ?_)
    exact (eLpNorm_difference_tensor_sq_eq_dist (p (κ n)) v (hP (κ n))).symm
  have hUpper (n : ℕ) := memHs_and_fractionalEnergy_sub_le (hM (κ n)) hV
  let D := 2 * C + 2 * fractionalEnergy t U v
  have hD : D < ⊤ := ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top (by simp) hC, ENNReal.mul_lt_top (by simp) hV.2⟩
  have hBoundDiff : ∀ᶠ n in atTop, fractionalEnergy t U (w n) ≤ D := .of_forall fun n =>
    (hUpper n).2.trans (add_le_add (mul_le_mul' le_rfl (hCseq (κ n))) le_rfl)
  refine ⟨κ,(v : Point → S0),hκ,?_⟩
  refine ⟨fun n => (hM (κ n)).of_exponent_lt_bounded hU.1 hs hst,
    hV.of_exponent_lt_bounded hU.1 hs hst,?_⟩
  exact tendsto_fractionalEnergy_of_L2_and_higher_bound hU.1 hs hst w
    (fun n => (hUpper n).1.1) hL hD hBoundDiff

end Thesis

end
