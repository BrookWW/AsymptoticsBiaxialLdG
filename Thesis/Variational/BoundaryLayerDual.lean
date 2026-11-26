module

public import Thesis.Variational.FractionalTransposition
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Semiring

/-! Exponential boundary layers tested against the actual Dirichlet space. -/

public section

open Filter MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem summable_shifted_quadratic_exponential {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ => Real.exp (-c * k) * (k + 1 : ℝ)^2) := by
  have h := ((Real.summable_pow_mul_exp_neg_nat_mul 2 hc).comp_injective Nat.succ_injective).mul_left (Real.exp c)
  apply h.congr
  intro k
  simp only [Function.comp_apply, Nat.cast_succ]
  calc
    _ = (Real.exp c * Real.exp (-c * (k + 1 : ℝ))) * (k + 1 : ℝ)^2 := by ring
    _ = _ := by rw [← Real.exp_add, show c + -c * (k + 1 : ℝ) = -c * k by ring]

private def exponentialLayerTerm {X : Type*} (d g : X → ℝ) (c ε : ℝ) (k : ℕ) : X → ℝ≥0∞ :=
  {x | d x < (k + 1 : ℝ) * ε}.indicator (fun x => ENNReal.ofReal (Real.exp (-c * k) * g x))

private theorem exponential_weight_le_layer_series {X : Type*} (d g : X → ℝ) (c ε : ℝ)
    (hc : 0 < c) (hε : 0 < ε) (x : X) (hD : 0 ≤ d x) (hG : 0 ≤ g x) :
    ENNReal.ofReal (Real.exp (-c * d x / ε) * g x) ≤ ∑' k, exponentialLayerTerm d g c ε k x := by
  let k := ⌊d x / ε⌋₊
  have h₁ : (k : ℝ) ≤ d x / ε := Nat.floor_le (div_nonneg hD hε.le)
  have h₂ : d x / ε < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk : x ∈ {x | d x < (k + 1 : ℝ) * ε} := (div_lt_iff₀ hε).1 h₂
  have hE : Real.exp (-c * d x / ε) ≤ Real.exp (-c * k) := by
    apply Real.exp_monotone
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonpos_left h₁ (neg_nonpos.mpr hc.le)
  refine (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hE hG)).trans ?_
  rw [← Set.indicator_of_mem hk (fun y => ENNReal.ofReal (Real.exp (-c * k) * g y))]
  exact ENNReal.le_tsum k

private theorem integrable_exponential_weight {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {d g : X → ℝ} (hD : Measurable d) (hd : ∀ x, 0 ≤ d x) (hg : Integrable g μ)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    Integrable (fun x => Real.exp (-c * d x / ε) * g x) μ := by
  apply hg.norm.mono'
  · exact ((measurable_const.mul hD).div_const ε).exp.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · filter_upwards [] with x
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    refine (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr ?_) (norm_nonneg _)).trans_eq (one_mul _)
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (hd x)) hε.le

private theorem lintegral_exponentialLayerTerm_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {d g : X → ℝ} (hD : Measurable d) (hg : Integrable g μ) (hG : ∀ x, 0 ≤ g x)
    {c ε M : ℝ} (hε : 0 < ε)
    (hLayer : ∀ t : ℝ, 0 < t → (∫ x in {x | d x < t}, g x ∂μ) ≤ M * t^2) (k : ℕ) :
    (∫⁻ x, exponentialLayerTerm d g c ε k x ∂μ) ≤
      ENNReal.ofReal (M * ε^2 * (Real.exp (-c * k) * (k + 1 : ℝ)^2)) := by
  let V := {x | d x < (k + 1 : ℝ) * ε}
  have hV : MeasurableSet V := measurableSet_lt hD measurable_const
  have hInt : IntegrableOn g V μ := hg.integrableOn
  change (∫⁻ x, V.indicator (fun y => ENNReal.ofReal (Real.exp (-c * k) * g y)) x ∂μ) ≤ _
  rw [lintegral_indicator hV, ← ofReal_integral_eq_lintegral_ofReal (hInt.const_mul _)
    (Eventually.of_forall fun x => mul_nonneg (Real.exp_nonneg _) (hG x)),
    integral_const_mul]
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left
    (hLayer ((k + 1 : ℝ) * ε) (mul_pos (by positivity) hε)) (Real.exp_nonneg (-c*k))
  exact h.trans_eq (by ring)

/-- Quadratic layer mass gives an \(\varepsilon^2\) bound for the
exponentially decaying weight. The constant depends only on its decay rate. -/
theorem exists_integral_exponential_weight_le_of_layer_mass (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X) (d g : X → ℝ),
      Measurable d → (∀ x, 0 ≤ d x) → Integrable g μ → (∀ x, 0 ≤ g x) →
      ∀ M : ℝ, 0 ≤ M → (∀ t : ℝ, 0 < t → (∫ x in {x | d x < t}, g x ∂μ) ≤ M * t^2) →
        ∀ ε : ℝ, 0 < ε → (∫ x, Real.exp (-c * d x / ε) * g x ∂μ) ≤ C * M * ε^2 := by
  let G (k : ℕ) := Real.exp (-c * k) * (k + 1 : ℝ)^2
  let C := ∑' k, G k
  have hC : 0 ≤ C := tsum_nonneg fun k => by dsimp only [G]; positivity
  have hSum : Summable G := summable_shifted_quadratic_exponential hc
  refine ⟨C, hC, ?_⟩
  intro X hX μ d g hD hd hg hG M hM hLayer ε hε
  let F (x : X) := Real.exp (-c * d x / ε) * g x
  have hF : Integrable F μ := integrable_exponential_weight hD hd hg hc hε
  have hFm (k : ℕ) : AEMeasurable (exponentialLayerTerm d g c ε k) μ := by
    unfold exponentialLayerTerm
    exact (ENNReal.measurable_ofReal.comp_aemeasurable ((hg.aestronglyMeasurable.aemeasurable).const_mul _)).indicator
      (measurableSet_lt hD measurable_const)
  have hENN : ENNReal.ofReal (∫ x, F x ∂μ) ≤ ENNReal.ofReal (C * M * ε^2) := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (F x) ∂μ := ofReal_integral_eq_lintegral_ofReal hF
        (Eventually.of_forall fun x => mul_nonneg (Real.exp_nonneg _) (hG x))
      _ ≤ ∫⁻ x, ∑' k, exponentialLayerTerm d g c ε k x ∂μ :=
        lintegral_mono fun x => exponential_weight_le_layer_series d g c ε hc hε x (hd x) (hG x)
      _ = ∑' k, ∫⁻ x, exponentialLayerTerm d g c ε k x ∂μ := lintegral_tsum hFm
      _ ≤ ∑' k, ENNReal.ofReal (M * ε^2 * G k) := ENNReal.tsum_le_tsum
        (lintegral_exponentialLayerTerm_le hD hg hG hε hLayer)
      _ = _ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by dsimp only [G]; positivity)
          (hSum.mul_left (M * ε^2)), tsum_mul_left]
        congr 1
        dsimp only [C]
        ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hENN

/-- A bulk forcing with the actual inverse-distance and exponential
profiles has the \(O(\varepsilon^2)\) Dirichlet dual bound. -/
theorem exists_fractional_dirichlet_forcing_bound_of_layer_profile
    (hHardy : External.DirichletFractionalHardyAndCollar)
    {U : Set Point} (hU : IsSmoothDomain U) (s c : ℝ) (hs : 0 < s) (hs₁ : s < 1/2) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Point → S0) (D ε : ℝ), 0 ≤ D → 0 < ε →
      AEStronglyMeasurable F (volume.restrict U) →
      (∀ x ∈ U, ‖F x‖ ≤ D * (ε^2 / Metric.infDist x (frontier U) +
        Real.exp (-c * Metric.infDist x (frontier U) / ε))) →
      HasFractionalDirichletForcingBound s U F (K * D * ε^2) := by
  obtain ⟨C₁, hC₁, hHard⟩ := hHardy U hU s hs hs₁
  obtain ⟨C₂, hC₂, hExp⟩ := exists_integral_exponential_weight_le_of_layer_mass c hc
  let K := C₁ * (1 + C₂)
  have hK : 0 ≤ K := mul_nonneg hC₁ (by positivity)
  refine ⟨K, hK, ?_⟩
  intro F D ε hD hε hF hProfile
  refine ⟨by positivity, ?_⟩
  intro w hw
  let μ := volume.restrict U
  let d (x : Point) := Metric.infDist x (frontier U)
  let g (x : Point) := ‖h10Value w x‖
  let N := dirichletFractionalTestNorm s U w
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hDist : Measurable d := (Metric.continuous_infDist_pt (frontier U)).measurable
  have hDist₀ (x : Point) : 0 ≤ d x := Metric.infDist_nonneg
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  have hg : Integrable g μ := ((Lp.memLp w.val.1).integrable (by norm_num)).norm
  have hg₀ (x : Point) : 0 ≤ g x := norm_nonneg _
  obtain ⟨⟨hIntHard, hBoundHard⟩, hLayer⟩ := hHard w hw
  have hLayer' (t : ℝ) (ht : 0 < t) : (∫ x in {x | d x < t}, g x ∂μ) ≤ (C₁ * N) * t^2 := by
    have hSet : MeasurableSet {x | d x < t} := measurableSet_lt hDist measurable_const
    rw [Measure.restrict_restrict hSet]
    have hB := hLayer t ht
    have hI : {x | d x < t} ∩ U = U ∩ {x | d x < t} := inter_comm _ _
    rw [hI]
    exact hB.trans_eq (by ring)
  have hIexp : Integrable (fun x => Real.exp (-c * d x / ε) * g x) μ :=
    integrable_exponential_weight hDist hDist₀ hg hc hε
  have hBexp : (∫ x in U, Real.exp (-c * d x / ε) * g x) ≤ C₂ * (C₁*N) * ε^2 :=
    hExp μ d g hDist hDist₀ hg hg₀ (C₁*N) (mul_nonneg hC₁ hN) hLayer' ε hε
  let H (x : Point) := D * (ε^2 * (g x / d x) + Real.exp (-c * d x / ε) * g x)
  have hIH : Integrable H μ := ((hIntHard.const_mul (ε^2)).add hIexp).const_mul D
  let P (x : Point) := frobeniusS0 (F x) (h10Value w x)
  have hPa : AEStronglyMeasurable P μ := by
    let E := frobeniusCoordinateEquiv
    have h₁ := E.continuous.comp_aestronglyMeasurable hF
    have h₂ := E.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable w.val.1)
    have hh := h₁.inner (𝕜 := ℝ) h₂
    exact hh.congr (Eventually.of_forall fun x => frobeniusCoordinateEquiv_inner (F x) (h10Value w x))
  have hPH : ∀ᵐ x ∂μ, ‖P x‖ ≤ H x := by
    filter_upwards [ae_restrict_mem (μ := volume) hU.1.1.measurableSet] with x hx
    have hFrob := abs_real_inner_le_norm (frobeniusCoordinateEquiv (F x))
      (frobeniusCoordinateEquiv (h10Value w x))
    rw [frobeniusCoordinateEquiv_inner, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at hFrob
    rw [Real.norm_eq_abs]
    apply hFrob.trans
    exact (mul_le_mul_of_nonneg_right (hProfile x hx) (hg₀ x)).trans_eq (by dsimp only [H, g, d]; ring)
  have hPI : Integrable P μ := hIH.mono' hPa hPH
  calc
    _ ≤ ∫ x in U, ‖P x‖ := norm_integral_le_integral_norm P
    _ ≤ ∫ x in U, H x := integral_mono_ae hPI.norm hIH hPH
    _ = D * (ε^2 * (∫ x in U, g x / d x) + ∫ x in U, Real.exp (-c * d x / ε) * g x) := by
      unfold H
      rw [integral_const_mul, integral_add (hIntHard.const_mul (ε^2)) hIexp, integral_const_mul]
    _ ≤ D * (ε^2 * (C₁*N) + C₂ * (C₁*N) * ε^2) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hBoundHard (sq_nonneg _)) hBexp) hD
    _ = (K * D * ε^2) * dirichletFractionalTestNorm s U w := by dsimp only [K, N]; ring

end Thesis

end
