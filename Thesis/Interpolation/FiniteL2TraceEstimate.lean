module

public import StratificationTheory.Foundation.CoordinateL2Trace

/-! Quantitative endpoint estimates for the original finite-product trace. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set StratificationTheory
open scoped ContDiff ENNReal Topology

namespace Thesis

private theorem integral_finiteLp_time_curve_norm_sq {X : Type*} [MeasurableSpace X] {q : ℕ}
    (σ : Measure X) [IsFiniteMeasure σ] [IsSeparable σ] {a b : ℝ} {f : X × ℝ → Ambient q}
    (hf : MemLp f 2 (σ.prod (volume.restrict (Icc a b))))
    (F : ℝ → Lp (Ambient q) 2 σ)
    (hF : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∃ ht : MemLp (fun x => f (x, t)) 2 σ, F t = ht.toLp _) :
    (∫ t in Ioo a b, ‖F t‖ ^ 2) = ∫ p, ‖f p‖ ^ 2 ∂σ.prod (volume.restrict (Icc a b)) := by
  obtain ⟨G, _, hG, hInt⟩ := exists_finite_lp_two_time_curve σ a b hf
  have hEq : F =ᵐ[volume.restrict (Icc a b)] G := by
    filter_upwards [hF, hG] with t htF htG
    obtain ⟨_, h₁⟩ := htF
    obtain ⟨_, h₂⟩ := htG
    exact h₁.trans h₂.symm
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc, integral_congr_ae (hEq.mono fun _ h => by rw [h])]
  exact hInt

/-- The continuous representative of actual product weak data has a uniform
square-norm bound up to both endpoints in terms of the original cylinder data. -/
theorem exists_finite_L2_trace_with_endpoint_estimate {X : Type*} [MeasurableSpace X] {q : ℕ}
    (σ : Measure X) [IsFiniteMeasure σ] [IsSeparable σ] {a b : ℝ} (hab : a < b)
    {f g : X × ℝ → Ambient q}
    (hf : MemLp f 2 (σ.prod (volume.restrict (Icc a b))))
    (hg : MemLp g 2 (σ.prod (volume.restrict (Icc a b))))
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∀ᵐ x ∂σ, (∫ t in Icc a b, deriv φ t • f (x, t)) = -(∫ t in Icc a b, φ t • g (x, t))) :
    ∃ H : C(Icc a b, Lp (Ambient q) 2 σ),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
        ∃ htLp : MemLp (fun x => f (x, t)) 2 σ, H ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp _) ∧
      ∀ t : Icc a b, ‖H t‖ ^ 2 ≤ (2 / (b - a)) * (∫ p, ‖f p‖ ^ 2 ∂σ.prod (volume.restrict (Icc a b))) +
        2 * (b - a) * (∫ p, ‖g p‖ ^ 2 ∂σ.prod (volume.restrict (Icc a b))) := by
  obtain ⟨F, G, hF, hG, hFs, hGs, hWeak⟩ := exists_finite_lp_two_time_curves_with_weak_identity σ a b hf hg hw
  have hMono : volume.restrict (Ioo a b) ≤ volume.restrict (Icc a b) :=
    Measure.restrict_mono_set volume Ioo_subset_Icc_self
  obtain ⟨H, hH, _⟩ := banach_interval_weakDerivative_exists_unique_continuous_representative hab
    (hF.mono_measure hMono) (hG.mono_measure hMono) (fun φ hφ hcφ hsφ => (hWeak φ hφ hcφ hsφ).2.2)
  refine ⟨H, ?_, ?_⟩
  · have hFs' := (ae_restrict_iff' measurableSet_Ioo).mp (hFs.filter_mono (ae_mono hMono))
    filter_upwards [hH.1, hFs'] with t htH htF ht
    obtain ⟨hLp, hRaw⟩ := htF ht
    exact ⟨hLp, (htH ht).trans hRaw⟩
  · intro t
    have hFnorm := integral_finiteLp_time_curve_norm_sq σ hf F hFs
    have hGnorm := integral_finiteLp_time_curve_norm_sq σ hg G hGs
    simpa only [hFnorm, hGnorm] using hH.2.2.2.2 t

end Thesis

end
