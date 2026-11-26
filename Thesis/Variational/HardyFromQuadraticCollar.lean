module

public import Thesis.Definitions
import Mathlib.Analysis.SpecificLimits.Basic

/-! Quadratic physical collar mass gives the inverse-distance integral. -/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem exists_dyadic_shell {d : ℝ} (hd : 0 < d) (hd₁ : d < 1) :
    ∃ n : ℕ, (1/2:ℝ)^n/2 ≤ d ∧ d < (1/2:ℝ)^n := by
  let r (n : ℕ) := (1/2:ℝ)^n
  have hLim : Tendsto r atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h : ∃ n, r n ≤ d := ((hLim.eventually_lt tendsto_const_nhds hd).mono fun _ hn => hn.le).exists
  let m := Nat.find h
  have hm : r m ≤ d := Nat.find_spec h
  have hm₀ : 0 < m := by
    by_contra! h0
    have hm0 : m = 0 := Nat.le_zero.mp h0
    have hr0 : r m = 1 := by simp [hm0,r]
    exact (not_le_of_gt hd₁) (hr0 ▸ hm)
  let n := m-1
  have hn : n+1=m := Nat.sub_add_cancel hm₀
  have hlt : n < m := by omega
  have he : r m = r n/2 := by rw [← hn]; dsimp only [r]; rw [pow_succ]; ring
  exact ⟨n,he ▸ hm,lt_of_not_ge (Nat.find_min h hlt)⟩

private def dyadicLayerTerm {X : Type*} (d g : X → ℝ) (n : ℕ) (x : X) : ℝ≥0∞ :=
  let r := (1/2:ℝ)^n
  {y | d y < r}.indicator (fun y => ENNReal.ofReal ((2/r)*g y)) x

private theorem ofReal_div_le_dyadicLayerSeries {X : Type*} (d g : X → ℝ) (x : X)
    (hd : 0 < d x) (hg : 0 ≤ g x) :
    ENNReal.ofReal (g x/d x) ≤ ENNReal.ofReal (g x) + ∑' n, dyadicLayerTerm d g n x := by
  by_cases h₁ : 1 ≤ d x
  · exact (ENNReal.ofReal_le_ofReal (div_le_self hg h₁)).trans (self_le_add_right _ _)
  obtain ⟨n,hn,hn'⟩ := exists_dyadic_shell hd (lt_of_not_ge h₁)
  let r := (1/2:ℝ)^n
  have hr : 0 < r := pow_pos (by norm_num) _
  have hR : g x/d x ≤ (2/r)*g x :=
    (div_le_div_of_nonneg_left hg (half_pos hr) hn).trans_eq (by ring)
  refine (ENNReal.ofReal_le_ofReal hR).trans ?_
  have hx : x ∈ {y | d y < r} := hn'
  have hTerm : ENNReal.ofReal ((2/r)*g x) = dyadicLayerTerm d g n x := by
    change ENNReal.ofReal ((2/r)*g x) = {y | d y < r}.indicator (fun y => ENNReal.ofReal ((2/r)*g y)) x
    rw [indicator_of_mem hx]
  rw [hTerm]
  exact (ENNReal.le_tsum n).trans (self_le_add_left _ _)

/-- The actual inverse-distance integral follows from an integrated
quadratic collar estimate. -/
theorem inverseDistance_integrable_and_integral_le_of_quadratic_collar
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (d g : X → ℝ)
    (hD : Measurable d) (hd : ∀ᵐ x ∂μ, 0 < d x)
    (hg : Integrable g μ) (hg₀ : ∀ x, 0 ≤ g x) (M : ℝ) (hM : 0 ≤ M)
    (hLayer : ∀ t : ℝ, 0 < t → (∫ x in {x | d x < t}, g x ∂μ) ≤ M*t^2) :
    Integrable (fun x => g x/d x) μ ∧
      (∫ x, g x/d x ∂μ) ≤ (∫ x, g x ∂μ) + 4*M := by
  let F (x : X) := g x/d x
  have hF : AEStronglyMeasurable F μ :=
    (hg.aestronglyMeasurable.aemeasurable.div hD.aemeasurable).aestronglyMeasurable
  have hF₀ : 0 ≤ᵐ[μ] F := hd.mono fun x hx => div_nonneg (hg₀ x) hx.le
  have hMeas (n : ℕ) : AEMeasurable (dyadicLayerTerm d g n) μ := by
    unfold dyadicLayerTerm
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      ((hg.aestronglyMeasurable.aemeasurable).const_mul _)).indicator (measurableSet_lt hD measurable_const)
  have hInt (n : ℕ) : (∫⁻ x, dyadicLayerTerm d g n x ∂μ) ≤
      ENNReal.ofReal ((2*M)*(1/2:ℝ)^n) := by
    let r := (1/2:ℝ)^n
    have hr : 0 < r := pow_pos (by norm_num) _
    let S := {x | d x < r}
    have hS : MeasurableSet S := measurableSet_lt hD measurable_const
    have hG : IntegrableOn (fun x => (2/r)*g x) S μ := hg.integrableOn.const_mul _
    change (∫⁻ x, S.indicator (fun x => ENNReal.ofReal ((2/r)*g x)) x ∂μ) ≤ _
    rw [lintegral_indicator hS,← ofReal_integral_eq_lintegral_ofReal hG (.of_forall fun x =>
      mul_nonneg (div_nonneg (by norm_num) hr.le) (hg₀ x)),integral_const_mul]
    apply ENNReal.ofReal_le_ofReal
    refine (mul_le_mul_of_nonneg_left (hLayer r hr) (div_nonneg (by norm_num) hr.le)).trans_eq ?_
    change (2/r)*(M*r^2)=(2*M)*r
    field_simp [hr.ne']
  have hSum : (∑' n : ℕ, ENNReal.ofReal ((2*M)*(1/2:ℝ)^n)) = ENNReal.ofReal (4*M) := by
    have hR := hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : (1/2:ℝ) < 1)
    have hm := hR.mul_left (2*M)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hm.summable,hm.tsum_eq]
    apply congrArg ENNReal.ofReal
    norm_num
    ring
  have hG0 : 0 ≤ ∫ x, g x ∂μ := integral_nonneg hg₀
  have hBound : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal ((∫ x, g x ∂μ)+4*M) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (g x)+∑' n, dyadicLayerTerm d g n x ∂μ := by
        apply lintegral_mono_ae
        exact hd.mono fun x hx => ofReal_div_le_dyadicLayerSeries d g x hx (hg₀ x)
      _ = ENNReal.ofReal (∫ x, g x ∂μ) + ∑' n, ∫⁻ x, dyadicLayerTerm d g n x ∂μ := by
        have hG : AEMeasurable (fun x => ENNReal.ofReal (g x)) μ :=
          ENNReal.measurable_ofReal.comp_aemeasurable hg.aestronglyMeasurable.aemeasurable
        rw [lintegral_add_left' hG,
          ← ofReal_integral_eq_lintegral_ofReal hg (.of_forall hg₀),lintegral_tsum hMeas]
      _ ≤ ENNReal.ofReal (∫ x, g x ∂μ) + ENNReal.ofReal (4*M) :=
        add_le_add le_rfl ((ENNReal.tsum_le_tsum hInt).trans_eq hSum)
      _ = _ := (ENNReal.ofReal_add hG0 (mul_nonneg (by norm_num) hM)).symm
  have hIntegrable : Integrable F μ := by
    refine ⟨hF,?_⟩
    change (∫⁻ x, ‖F x‖ₑ ∂μ) < ⊤
    have hEq : (fun x => ‖F x‖ₑ) =ᵐ[μ] fun x => ENNReal.ofReal (F x) := by
      filter_upwards [hF₀] with x hx
      rw [← ofReal_norm,Real.norm_of_nonneg hx]
    rw [lintegral_congr_ae hEq]
    exact hBound.trans_lt ENNReal.ofReal_lt_top
  rw [← ofReal_integral_eq_lintegral_ofReal hIntegrable hF₀] at hBound
  exact ⟨hIntegrable,(ENNReal.ofReal_le_ofReal_iff (add_nonneg hG0 (by positivity))).1 hBound⟩

end Thesis

end
