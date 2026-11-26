module

public import SupportingAnalysis.Euclidean

/-! Weak L¹ scalar convolution bounds are invariant under mass-preserving dilations. -/

@[expose] public section

open MeasureTheory Set Metric
open scoped Convolution ENNReal Pointwise

set_option autoImplicit false

namespace SupportingAnalysis

/-- A weak L¹ bound includes measurability of the convolution for each L¹ input. -/
def WeakScalarConvolutionBound {d : ℕ} (k : E d → ℝ) (v : ℝ) : Prop :=
  ∀ g : E d → ℝ, Integrable g →
    AEMeasurable (k ⋆[ContinuousLinearMap.mul ℝ ℝ] g) volume ∧
      ∀ t : ℝ, 0 < t →
        volume {p : E d | t < |(k ⋆[ContinuousLinearMap.mul ℝ ℝ] g) p|} ≤
          ENNReal.ofReal (v * (∫ p, |g p|) / t)

/-- Mass-preserving dilation of a scalar kernel. -/
noncomputable def massPreservingKernelDilation {d : ℕ} (w : ℝ) (k : E d → ℝ) :
    E d → ℝ :=
  fun p => (w ^ d)⁻¹ * k (w⁻¹ • p)

theorem massPreservingKernelDilation_convolution_smul {d : ℕ}
    (k g : E d → ℝ) {w : ℝ} (hw : 0 < w) (q : E d) :
    (massPreservingKernelDilation w k ⋆[ContinuousLinearMap.mul ℝ ℝ] g) (w • q) =
      (k ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun p => g (w • p))) q := by
  let F : E d → ℝ := fun p => k p * g (w • (q - p))
  have harg (p : E d) :
      k (w⁻¹ • p) * g (w • q - p) = F (w⁻¹ • p) := by
    simp only [F, smul_sub, smul_smul, mul_inv_cancel₀ hw.ne', one_smul]
  simp only [convolution_mul, massPreservingKernelDilation, mul_assoc, harg]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume F hw.le]
  have hrank : Module.finrank ℝ (E d) = d := by simp [E]
  simp [hrank, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d hw.ne'), F]

theorem massPreservingKernelDilation_convolution_eq_comp {d : ℕ}
    (k g : E d → ℝ) {w : ℝ} (hw : 0 < w) :
    (massPreservingKernelDilation w k ⋆[ContinuousLinearMap.mul ℝ ℝ] g) =
      (fun q => (k ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun p => g (w • p))) q) ∘ (w⁻¹ • ·) := by
  funext p
  have hp : w • (w⁻¹ • p) = p := by simp [smul_smul, mul_inv_cancel₀ hw.ne']
  have h := massPreservingKernelDilation_convolution_smul k g hw (w⁻¹ • p)
  simpa only [hp, Function.comp_apply] using h

theorem weakScalarConvolutionBound_massPreservingKernelDilation {d : ℕ}
    {k : E d → ℝ} {v : ℝ} (hk : WeakScalarConvolutionBound k v)
    {w : ℝ} (hw : 0 < w) :
    WeakScalarConvolutionBound (massPreservingKernelDilation w k) v := by
  intro g hg
  let gW : E d → ℝ := fun p => g (w • p)
  have hgW : Integrable gW :=
    (integrable_comp_smul_iff volume g hw.ne').mpr hg
  obtain ⟨hgmeas, hgtail⟩ := hk gW hgW
  let f : E d → ℝ := k ⋆[ContinuousLinearMap.mul ℝ ℝ] gW
  have heq : (massPreservingKernelDilation w k ⋆[ContinuousLinearMap.mul ℝ ℝ] g) =
      f ∘ (w⁻¹ • ·) :=
    massPreservingKernelDilation_convolution_eq_comp k g hw
  refine ⟨?_, fun t ht => ?_⟩
  · rw [heq]
    exact hgmeas.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hw.ne'))
  have hrank : Module.finrank ℝ (E d) = d := by simp [E]
  have hmass : (∫ x, |gW x|) = (w ^ d)⁻¹ * ∫ x, |g x| := by
    simpa only [hrank, smul_eq_mul] using
      Measure.integral_comp_smul_of_nonneg (volume : Measure (E d)) (fun x => |g x|) w (hR := hw.le)
  have htailq : volume {q : E d | t < |f q|} ≤ ENNReal.ofReal (v * (∫ q, |gW q|) / t) :=
    hgtail t ht
  rw [heq]
  change volume ((w⁻¹ • ·) ⁻¹' {q : E d | t < |f q|}) ≤ _
  rw [Measure.addHaar_preimage_smul volume (inv_ne_zero hw.ne'), hrank,
    inv_pow, inv_inv, abs_of_pos (pow_pos hw _)]
  calc
    _ ≤ ENNReal.ofReal (w ^ d) * ENNReal.ofReal (v * (∫ q, |gW q|) / t) := by
      gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (pow_nonneg hw.le _), hmass]
      congr 1
      field_simp [pow_ne_zero d hw.ne']

/-- Pointwise localization of a scalar convolution to a set containing all relevant input points. -/
theorem scalarConvolution_indicator_eq_of_support {d : ℕ} {k g : E d → ℝ}
    {S : Set (E d)} {p : E d}
    (hS : ∀ y ∈ Function.support k, p - y ∈ S) :
    (k ⋆[ContinuousLinearMap.mul ℝ ℝ] S.indicator g) p =
      (k ⋆[ContinuousLinearMap.mul ℝ ℝ] g) p := by
  simp only [convolution_mul]
  congr 1
  funext y
  by_cases hy : y ∈ Function.support k
  · rw [indicator_of_mem (hS y hy)]
  · simp [Function.notMem_support.mp hy]

/-- The support of a dilated compact kernel lies in the correspondingly dilated ball. -/
theorem support_massPreservingKernelDilation_subset {d : ℕ}
    {k : E d → ℝ} {C w : ℝ} (hk : Function.support k ⊆ ball 0 C) (hw : 0 < w) :
    Function.support (massPreservingKernelDilation w k) ⊆ ball 0 (C * w) := by
  intro y hy
  have hky : w⁻¹ • y ∈ Function.support k := by
    intro hzero
    exact hy (by simp [massPreservingKernelDilation, hzero])
  have hyC : ‖w⁻¹ • y‖ < C := (mem_ball_zero_iff).mp (hk hky)
  apply mem_ball_zero_iff.mpr
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hw.le)] at hyC
  rwa [inv_mul_lt_iff₀ hw, mul_comm] at hyC

end SupportingAnalysis
