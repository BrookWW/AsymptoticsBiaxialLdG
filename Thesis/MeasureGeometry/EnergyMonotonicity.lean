module

public import Thesis.Variational.Pohozaev
public import Thesis.MeasureGeometry.EnergyMeasure
public import Thesis.MeasureGeometry.LineDensity

/-! Interior monotonicity of normalized energy measures and their weak limits. -/

public section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Frobenius

namespace Thesis

theorem energy_congr_of_ae {Ω : Set Point} {u v : Point → S0} {D G : Point → Gradient}
    (a : BulkCoefficients) (ε : ElasticScale) (huv : u =ᵐ[volume.restrict Ω] v)
    (hDG : D =ᵐ[volume.restrict Ω] G) : energy a ε Ω u D = energy a ε Ω v G := by
  unfold energy
  apply lintegral_congr_ae
  filter_upwards [huv, hDG] with x h₁ h₂
  rw [h₁, h₂]

/-- The normalized ball ratio is unchanged by passage to the smooth
representative with its actual classical gradient. -/
theorem normalizedEnergyMeasure_ballRatio_monotoneOn (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {u v : Point → S0} {D : Point → Gradient}
    (huv : u =ᵐ[volume.restrict Ω] v) (hD : D =ᵐ[volume.restrict Ω] ClassicalGradient v)
    (hv : ContDiffOn ℝ ∞ v Ω)
    (hEuler : ∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian v x : S0).val = bulkGradient a (v x))
    {c : Point} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall c R ⊆ Ω) :
    MonotoneOn (fun r => (normalizedEnergyMeasure a ε Ω u D (Metric.ball c r)).toReal / (2 * r))
      (Ioc 0 R) := by
  let L := Real.log (1 / (ε : ℝ))
  have hL : 0 < L := log_inv_scale_pos ε
  have hEq (r : ℝ) (hr : r ∈ Ioc 0 R) :
      (normalizedEnergyMeasure a ε Ω u D (Metric.ball c r)).toReal / (2 * r) =
      (L⁻¹ / 2) * ((energy a ε (Metric.ball c r) v (ClassicalGradient v)).toReal / r) := by
    have hs : Metric.ball c r ⊆ Ω :=
      Metric.ball_subset_closedBall.trans ((Metric.closedBall_subset_closedBall hr.2).trans hball)
    have hμ := Measure.restrict_mono_set (volume : Measure Point) hs
    rw [normalizedEnergyMeasure_apply a ε Ω u D Metric.isOpen_ball.measurableSet,
      inter_eq_left.mpr hs, energy_congr_of_ae a ε (huv.filter_mono (ae_mono hμ))
        (hD.filter_mono (ae_mono hμ)), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hL.le)]
    change L⁻¹ * _ / (2 * r) = _
    ring
  intro s hs r hr hsr
  change (normalizedEnergyMeasure a ε Ω u D (Metric.ball c s)).toReal / (2 * s) ≤
    (normalizedEnergyMeasure a ε Ω u D (Metric.ball c r)).toReal / (2 * r)
  rw [hEq s hs, hEq r hr]
  exact mul_le_mul_of_nonneg_left
    (normalized_classicalBallEnergy_monotoneOn a ε hΩ hv hEuler hR hball hs hr hsr)
    (div_nonneg (inv_nonneg.mpr hL.le) (by norm_num))

namespace MeasureGeometry

/-- Interior monotonicity survives the limit along the same actual energy
sequence, with closed balls in the limit density. -/
theorem oneDensity_monotoneOn_of_penalizedLimit (a : BulkCoefficients)
    {Ω : Set Point} (hΩ : IsOpen Ω) {ε : ℕ → ElasticScale}
    {u v : ℕ → Point → S0} {D : ℕ → Point → Gradient}
    (huv : ∀ n, u n =ᵐ[volume.restrict Ω] v n)
    (hD : ∀ n, D n =ᵐ[volume.restrict Ω] ClassicalGradient (v n))
    (hv : ∀ n, ContDiffOn ℝ ∞ (v n) Ω)
    (hEuler : ∀ n, ∀ x ∈ Ω, (ε n : ℝ) ^ 2 • (laplacian (v n) x : S0).val =
      bulkGradient a (v n x)) {μ : ℕ → FiniteMeasure Point} {ν : FiniteMeasure Point}
    (hμ : ∀ n, (μ n : Measure Point) = normalizedEnergyMeasure a (ε n) Ω (u n) (D n))
    (hν : Tendsto μ atTop (𝓝 ν)) {c : Point} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall c R ⊆ Ω) : MonotoneOn (oneDensity ν c) (Ioo 0 R) := by
  apply monotoneOn_oneDensity_of_weakConvergence hν c
  intro n
  rw [hμ n]
  exact (normalizedEnergyMeasure_ballRatio_monotoneOn a (ε n) hΩ (huv n) (hD n)
    (hv n) (hEuler n) hR hball).mono Ioo_subset_Ioc_self

end MeasureGeometry

end Thesis

end
