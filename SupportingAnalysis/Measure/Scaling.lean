module

public import SupportingAnalysis.Euclidean

/-! Affine change of variables for Euclidean integrals and norms. -/

@[expose] public section

open MeasureTheory Set Metric
open scoped BigOperators ContDiff ENNReal

set_option autoImplicit false

namespace SupportingAnalysis

/-- The positive dilation and translation taking normalized coordinates to ambient ones. -/
noncomputable def domainDilation {m : ℕ} (a : E m) {R : ℝ} (hR : 0 < R) : E m ≃ₜ E m where
  toFun x := a + R • x
  invFun x := R⁻¹ • (x - a)
  left_inv x := by simp [smul_smul, inv_mul_cancel₀ hR.ne']
  right_inv x := by simp [smul_smul, mul_inv_cancel₀ hR.ne']
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem domainDilation_apply {m : ℕ} (a : E m) {R : ℝ} (hR : 0 < R)
    (x : E m) : domainDilation a hR x = a + R • x := rfl

@[simp] theorem domainDilation_symm_apply {m : ℕ} (a : E m) {R : ℝ} (hR : 0 < R)
    (x : E m) : (domainDilation a hR).symm x = R⁻¹ • (x - a) := rfl

theorem dist_domainDilation {m : ℕ} (a : E m) {R : ℝ} (hR : 0 < R) (x y : E m) :
    dist (domainDilation a hR x) (domainDilation a hR y) = R * dist x y := by
  simp only [domainDilation_apply, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hR]

theorem map_volume_domainDilation {m : ℕ} (a : E m) {R : ℝ} (hR : 0 < R) :
    Measure.map (domainDilation a hR) volume =
      ENNReal.ofReal (R ^ m)⁻¹ • (volume : Measure (E m)) := by
  change Measure.map ((a + ·) ∘ (R • ·)) volume = _
  rw [← Measure.map_map (measurable_const_add a) (measurable_const_smul R),
    Measure.map_addHaar_smul volume hR.ne', Measure.map_smul, map_add_left_eq_self]
  simp [abs_of_pos, pow_pos hR]

theorem map_restrict_volume_domainDilation {m : ℕ} (a : E m) {R : ℝ} (hR : 0 < R)
    (Ω : Set (E m)) :
    Measure.map (domainDilation a hR) (volume.restrict (domainDilation a hR ⁻¹' Ω)) =
      ENNReal.ofReal (R ^ m)⁻¹ • volume.restrict Ω := by
  have h := (domainDilation a hR).toMeasurableEquiv.restrict_map volume Ω
  simp only [Homeomorph.toMeasurableEquiv_coe] at h
  rw [← h, map_volume_domainDilation, Measure.restrict_smul]

theorem integral_comp_domainDilation {m : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (a : E m) {R : ℝ} (hR : 0 < R) (Ω : Set (E m))
    (f : E m → F) :
    (∫ x in domainDilation a hR ⁻¹' Ω, f (domainDilation a hR x)) =
      (R ^ m)⁻¹ • (∫ x in Ω, f x) := by
  have h := (domainDilation a hR).toMeasurableEquiv.measurableEmbedding.integral_map
    (μ := volume.restrict (domainDilation a hR ⁻¹' Ω)) f
  simp only [Homeomorph.toMeasurableEquiv_coe] at h
  rw [← h, map_restrict_volume_domainDilation,
    integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

theorem memLp_comp_domainDilation {m : ℕ} {F : Type*} [NormedAddCommGroup F]
    (a : E m) {R : ℝ} (hR : 0 < R) (Ω : Set (E m)) {f : E m → F} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict Ω)) :
    MemLp (f ∘ domainDilation a hR) p (volume.restrict (domainDilation a hR ⁻¹' Ω)) := by
  apply (domainDilation a hR).toMeasurableEquiv.memLp_map_measure_iff.mp
  rw [Homeomorph.toMeasurableEquiv_coe, map_restrict_volume_domainDilation]
  exact hf.smul_measure ENNReal.ofReal_ne_top


end SupportingAnalysis
