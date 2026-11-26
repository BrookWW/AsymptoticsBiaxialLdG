module

public import Thesis.MeasureGeometry.CylinderLowerLimit
public import Thesis.MeasureGeometry.CylinderEndHeights
public import Thesis.Variational.GlobalComparison

/-! Minimality and normalization of a trace-matched cylinder competitor. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

/-- Local minimality is shared by the original weak map and its actual
classical representative with the verified weak columns. -/
theorem localEnergyMinimizer_congr_ae
    {a : BulkCoefficients} {ε : ElasticScale} {Ω : Set Point}
    {u v : Point → S0} {D G : Point → Gradient} (h : IsLocalEnergyMinimizer a ε Ω u D)
    (hu : u =ᵐ[volume.restrict Ω] v) (hD : D =ᵐ[volume.restrict Ω] G) :
    IsLocalEnergyMinimizer a ε Ω v G := by
  constructor
  · intro U hU hUΩ
    exact (h.1 U hU hUΩ).congr_ae
      (ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hUΩ.2) hu)
      (ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hUΩ.2) hD)
  · intro x r hr hB w J hw hT
    have hu' : u =ᵐ[volume.restrict (ball x r)] v :=
      ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hB) hu
    have hD' : D =ᵐ[volume.restrict (ball x r)] G :=
      ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hB) hD
    rw [← energy_congr_of_ae a ε hu' hD']
    exact h.2 x r hr hB w J hw (hT.congr_ae EventuallyEq.rfl hu'.symm EventuallyEq.rfl hD'.symm)

/-- A genuine competitor with the original trace gives the normalized upper
comparison, uniformly over the selected two end heights. Only the coefficient
of the cap energy contributes a persistent error. -/
theorem eventually_normalizedCylinder_upper_of_trace_matched_competitors
    (a : BulkCoefficients) {Ω : Set Point} (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {r s cap e K : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r < s) (hBall : closedBall c (2 * s) ⊆ Ω)
    (he : 0 ≤ e) (hK : 0 ≤ K)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hMin : ∀ n, IsLocalEnergyMinimizer a (ε n) Ω (Q n) (ClassicalGradient (Q n)))
    (hF : ∀ n, energy a (ε n) Ω (Q n) (ClassicalGradient (Q n)) < ⊤)
    (ν : ℕ → Measure Point)
    (hν : ∀ n, ν n = normalizedEnergyMeasure a (ε n) Ω (Q n) (ClassicalGradient (Q n)))
    (hRecover : ∃ A ≥ (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ lo ∈ Ioo (-s) (-(s / 2)), ∀ hi ∈ Ioo (s / 2) s,
        planarSmoothEnergy a (ε n) (cylinderSliceMap B c (Q n) lo) r +
          planarSmoothEnergy a (ε n) (cylinderSliceMap B c (Q n) hi) r ≤ cap * Real.log (1 / (ε n : ℝ)) →
        let S := translatedAxisCylinder c (B 2) r lo hi
        ∃ (w : Point → S0) (Dw : Point → Gradient),
          SameTrace S w (Q n) Dw (ClassicalGradient (Q n)) ∧
          energy a (ε n) S w Dw ≤ ENNReal.ofReal
            ((hi - lo) * e * Real.log (r / (ε n : ℝ)) + K * r * Real.log (1 / (ε n : ℝ)) + A)) :
    ∀ ξ > 0, ∀ᶠ n : ℕ in atTop,
      ∀ lo ∈ Ioo (-s) (-(s / 2)), ∀ hi ∈ Ioo (s / 2) s,
        planarSmoothEnergy a (ε n) (cylinderSliceMap B c (Q n) lo) r +
          planarSmoothEnergy a (ε n) (cylinderSliceMap B c (Q n) hi) r ≤ cap * Real.log (1 / (ε n : ℝ)) →
        ((ν n) (translatedAxisCylinder c (B 2) r lo hi)).toReal / (hi - lo) ≤
          e + K * (r / (hi - lo)) + ξ := by
  obtain ⟨A, hA, hRec⟩ := hRecover
  intro ξ hξ
  let L (n : ℕ) := Real.log (1 / (ε n : ℝ))
  let l (n : ℕ) := Real.log (r / (ε n : ℝ))
  have hL (n : ℕ) : 0 < L n := log_inv_scale_pos (ε n)
  have hLlim : Tendsto L atTop atTop := by
    have hInv : Tendsto (fun n => (ε n : ℝ)⁻¹) atTop atTop := by
      apply tendsto_inv_nhdsGT_zero.comp
      exact tendsto_nhdsWithin_iff.mpr ⟨hε, Eventually.of_forall (fun n => (ε n).property.1)⟩
    simpa only [L, Function.comp_def, one_div] using Real.tendsto_log_atTop.comp hInv
  have hl : Tendsto (fun n => l n / L n) atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ρ hρ
    have h := eventually_log_radius_ratio_close (fun n => (ε n).property.1) hε hr (le_refl r) hρ
    exact h.mono fun n hn => by simpa only [Real.dist_eq, l, L] using hn r ⟨le_rfl, le_rfl⟩
  let V (n : ℕ) := e * (l n / L n) + (A / s) * (L n)⁻¹
  have hV : Tendsto V atTop (𝓝 e) := by
    have h := (hl.const_mul e).add ((tendsto_inv_atTop_zero.comp hLlim).const_mul (A / s))
    simpa only [V, Function.comp_def, mul_one, mul_zero, add_zero] using h
  have hUpper := hV.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hξ))
  filter_upwards [hRec, hUpper, hε.eventually_lt_const hr] with n hN hVn hScale
  intro lo hlo hi hhi hCap
  let S := translatedAxisCylinder c (B 2) r lo hi
  let H := hi - lo
  have hH : s ≤ H := by dsimp only [H]; linarith only [hlo.2, hhi.1]
  have hH₀ : 0 < H := hs.trans_le hH
  have hS' : S ⊆ translatedClosedAxisCylinder c (B 2) r (-s) s := by
    intro x hx
    change x - c ∈ openAxisCylinder (B 2) r lo hi at hx
    change x - c ∈ closedAxisCylinder (B 2) r (-s) s
    exact ⟨hx.1.le, hlo.1.le.trans hx.2.1.le, hx.2.2.le.trans hhi.2.le⟩
  have hSBall : S ⊆ ball c (2 * s) := hS'.trans (closedCylinder_centered_height_subset_ball B c hs hrs)
  have hSΩ : S ⊆ Ω := hSBall.trans (ball_subset_closedBall.trans hBall)
  have hS : IsOpen S := isOpen_translatedAxisCylinder _ _ _ _ _
  obtain ⟨w, Dw, hT, hE⟩ := hN lo hlo hi hhi hCap
  have hCmp := (hMin n).energy_le_on_open_subregion (hF n) (mul_pos (by norm_num) hs) hBall hS hSBall hT
  let E := energy a (ε n) S (Q n) (ClassicalGradient (Q n))
  have hln : 0 ≤ l n := Real.log_nonneg ((one_le_div (ε n).property.1).mpr hScale.le)
  have hE₀ : 0 ≤ H * e * l n + K * r * L n + A :=
    add_nonneg (add_nonneg (mul_nonneg (mul_nonneg hH₀.le he) hln)
      (mul_nonneg (mul_nonneg hK hr.le) (hL n).le)) hA
  have hVol : E.toReal ≤ H * e * l n + K * r * L n + A :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hCmp.trans hE)).trans_eq (ENNReal.toReal_ofReal hE₀)
  have hMass : ((ν n) S).toReal = E.toReal / L n := by
    rw [hν n, normalizedEnergyMeasure_apply a _ _ _ _ hS.measurableSet,
      inter_eq_left.mpr hSΩ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (hL n).le),
      div_eq_mul_inv, mul_comm]
  have hDiv : ((ν n) S).toReal / H ≤
      (H * e * l n + K * r * L n + A) / (L n * H) := by
    rw [hMass, div_div]
    exact div_le_div_of_nonneg_right hVol (mul_nonneg (hL n).le hH₀.le)
  have hEq : (H * e * l n + K * r * L n + A) / (L n * H) =
      e * (l n / L n) + K * (r / H) + (A / H) * (L n)⁻¹ := by
    field_simp [hH₀.ne', (hL n).ne']
  rw [hEq] at hDiv
  have hErr : (A / H) * (L n)⁻¹ ≤ (A / s) * (L n)⁻¹ :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hA hs hH) (inv_nonneg.mpr (hL n).le)
  change ((ν n) S).toReal / H ≤ _
  dsimp only [V] at hVn
  linarith only [hDiv, hErr, hVn]

/-- The dimension-three recovery budget separates the persistent cap term
from the fixed core and lateral energies. The additive term is allowed
to depend on the chosen physical cylinder. -/
theorem cylinderRecovery_energy_budget (a : BulkCoefficients) {s r ε H Hmid e cap K Ccore Cside : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεr : ε ≤ r / 2)
    (hHmid : 0 ≤ Hmid) (hMid : Hmid ≤ H) (hH : H ≤ 2 * s)
    (he : 0 ≤ e) (heκ : e ≤ 2 * kappaStar a) (hK : 0 ≤ K)
    (hCcore : 0 ≤ Ccore)
    {E Ecore Eside Ecaps : ℝ}
    (hE : E ≤ Ecore + Eside + Ecaps)
    (hCore : Ecore ≤ Hmid * (e * Real.log ((r / 2) / ε) + Ccore))
    (hSide : Eside ≤ Cside)
    (hCaps : Ecaps ≤ K * r * (cap * Real.log (1 / ε) +
      2 * (e * Real.log ((r / 2) / ε) + Ccore) + Cside)) :
    E ≤ H * e * Real.log (r / ε) +
      (K * (cap + 4 * kappaStar a)) * r * Real.log (1 / ε) +
      (2 * s * Ccore + Cside + K * r * (4 * kappaStar a * |Real.log (r / 2)| + 2 * Ccore + Cside)) := by
  let L := Real.log (1 / ε)
  let l := Real.log (r / ε)
  let l₀ := Real.log ((r / 2) / ε)
  have hr₂ : 0 < r / 2 := half_pos hr
  have hl₀ : 0 ≤ l₀ := Real.log_nonneg ((one_le_div hε).mpr hεr)
  have hlr : l₀ ≤ l := Real.log_le_log (div_pos hr₂ hε)
    (div_le_div_of_nonneg_right (by linarith only [hr]) hε.le)
  have hLogDiff : l₀ = L + Real.log (r / 2) := by
    dsimp only [l₀, L]
    rw [Real.log_div hr₂.ne' hε.ne', one_div, Real.log_inv]
    ring
  have hCore' : Ecore ≤ H * e * l + 2 * s * Ccore := by
    have h₁ := mul_le_mul_of_nonneg_right hMid (mul_nonneg he hl₀)
    have h₂ := mul_le_mul_of_nonneg_left hlr (mul_nonneg (hMid.trans' hHmid) he)
    have h₃ := mul_le_mul_of_nonneg_right (hMid.trans hH) hCcore
    linarith only [hCore, h₁, h₂, h₃]
  have hEbound : e * l₀ ≤ 2 * kappaStar a * (L + |Real.log (r / 2)|) := by
    have hS : l₀ ≤ L + |Real.log (r / 2)| := by
      rw [hLogDiff]
      exact add_le_add_right (le_abs_self _) _
    exact (mul_le_mul_of_nonneg_right heκ hl₀).trans
      (mul_le_mul_of_nonneg_left hS (mul_nonneg (by norm_num) (kappaStar_pos a).le))
  have hCaps' : Ecaps ≤ K * r * ((cap + 4 * kappaStar a) * L +
      (4 * kappaStar a * |Real.log (r / 2)| + 2 * Ccore + Cside)) := by
    apply hCaps.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK hr.le)
    linarith only [hEbound]
  dsimp only [l, L] at hCore' hCaps'
  linarith only [hE, hCore', hSide, hCaps']

end Thesis.MeasureGeometry
