module

public import StratificationTheory.Foundation.InverseDilationLpTrace
import StratificationTheory.Foundation.LpTwoMeasureRestriction

/-! Continuous inverse dilation of varying native (L^2) trace classes. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ENNReal Topology

namespace Thesis

private theorem isometry_zeroExtensionLp {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {S : Set (Domain n)} (hS : MeasurableSet S) :
    Isometry (fun v : Lp E 2 (volume.restrict S) =>
      (memLp_zeroExtension hS (Lp.memLp v)).toLp (S.indicator v)) := by
  apply Isometry.of_dist_eq
  intro u v
  let μ := (volume : Measure (Domain n)).restrict S
  have hu : MemLp (⇑u) 2 μ := Lp.memLp u
  have hv : MemLp (⇑v) 2 μ := Lp.memLp v
  have huZ := memLp_zeroExtension hS hu
  have hvZ := memLp_zeroExtension hS hv
  change dist (huZ.toLp (S.indicator u)) (hvZ.toLp (S.indicator v)) = dist u v
  rw [dist_eq_norm, dist_eq_norm, ← huZ.toLp_sub hvZ, Lp.norm_toLp]
  have hZ : S.indicator (⇑u : Domain n → E) - S.indicator (⇑v : Domain n → E) =
      S.indicator ((⇑u : Domain n → E) - (⇑v : Domain n → E)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [hZ, eLpNorm_indicator_eq_eLpNorm_restrict hS]
  have hClass : (hu.sub hv).toLp (⇑u - ⇑v) = u - v := by
    rw [hu.toLp_sub hv, Lp.toLp_coeFn u hu, Lp.toLp_coeFn v hv]
  have hNorm := Lp.norm_toLp (⇑u - ⇑v : Domain n → E) (hu.sub hv)
  rw [hClass] at hNorm
  exact hNorm.symm

private theorem dist_inverseDilationLp_le {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (u v : Lp E 2 (volume : Measure (Domain n)))
    (hu : MemLp (fun x : Domain n => u (r⁻¹ • x)) 2 volume)
    (hv : MemLp (fun x : Domain n => v (r⁻¹ • x)) 2 volume) :
    dist (hu.toLp _) (hv.toLp _) ≤ dist u v := by
  have hu₀ := Lp.memLp u
  have hv₀ := Lp.memLp v
  have hD := eLpNorm_comp_centeredDilation (hu₀.sub hv₀) (0 : Domain n) (inv_ne_zero hr.ne')
  simp only [zero_add, sub_zero, Pi.sub_apply, ← inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hr.le n)] at hD
  have hFactor : ENNReal.ofReal (r ^ n) ^ (1 / 2 : ℝ) ≤ 1 := by
    have hPow : ENNReal.ofReal (r ^ n) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (pow_le_one₀ hr.le hr₁)
    simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow hPow (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [dist_eq_norm, dist_eq_norm, ← hu.toLp_sub hv, Lp.norm_toLp]
  have hR : ‖u - v‖ = (eLpNorm (⇑u - ⇑v : Domain n → E) 2 volume).toReal := by
    have hClass : (hu₀.sub hv₀).toLp (⇑u - ⇑v) = u - v := by
      rw [hu₀.toLp_sub hv₀, Lp.toLp_coeFn u hu₀, Lp.toLp_coeFn v hv₀]
    have hNorm := Lp.norm_toLp (⇑u - ⇑v : Domain n → E) (hu₀.sub hv₀)
    rw [hClass] at hNorm
    exact hNorm
  rw [hR]
  apply ENNReal.toReal_mono (hu₀.sub hv₀).eLpNorm_ne_top
  change eLpNorm (fun x : Domain n => u (r⁻¹ • x) - v (r⁻¹ • x)) 2 volume ≤ _
  rw [hD]
  exact mul_le_of_le_one_left' hFactor

/-- A continuous native trace can be pulled to a fixed contained subface
by the actual inverse radial dilation at every varying radius. -/
theorem exists_continuous_varying_inverseDilation_L2 {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {S U : Set (Domain n)}
    (hS : MeasurableSet S) (hU : MeasurableSet U) {ρ : ℝ} (hρ : 0 < ρ)
    (F : C(Icc ρ 1, Lp E 2 (volume.restrict S)))
    (hContain : ∀ r : Icc ρ 1, ∀ x ∈ U, r.val⁻¹ • x ∈ S) :
    ∃ G : C(Icc ρ 1, Lp E 2 (volume.restrict U)), ∀ r : Icc ρ 1,
      ∃ hLp : MemLp (fun x : Domain n => F r (r.val⁻¹ • x)) 2 (volume.restrict U),
        G r = hLp.toLp _ := by
  let ν := (volume : Measure (Domain n)).restrict S
  let μ := (volume : Measure (Domain n)).restrict U
  let Z₀ (v : Lp E 2 ν) : Lp E 2 (volume : Measure (Domain n)) :=
    (memLp_zeroExtension hS (Lp.memLp v)).toLp (S.indicator v)
  have hZIso : Isometry Z₀ := isometry_zeroExtensionLp hS
  let Z (r : Icc ρ 1) := Z₀ (F r)
  have hZ : Continuous Z := hZIso.continuous.comp F.continuous
  have hR (r : Icc ρ 1) : 0 < r.val := hρ.trans_le r.property.1
  have hD (r : Icc ρ 1) (v : Lp E 2 (volume : Measure (Domain n))) :
      MemLp (fun x : Domain n => v (r.val⁻¹ • x)) 2 volume := by
    simpa only [zero_add, sub_zero] using memLp_comp_centeredDilation (Lp.memLp v) (0 : Domain n)
      (inv_ne_zero (hR r).ne')
  let D (r : Icc ρ 1) (v : Lp E 2 (volume : Measure (Domain n))) : Lp E 2 (volume : Measure (Domain n)) :=
    (hD r v).toLp _
  have hDFixed (v : Lp E 2 (volume : Measure (Domain n))) : Continuous fun r => D r v := by
    obtain ⟨P, hP⟩ := exists_continuous_inverse_dilation_L2 (Lp.memLp v)
    let j : Icc ρ 1 → {r : ℝ // 0 < r} := fun r => ⟨r.val, hR r⟩
    have hj : Continuous j := continuous_subtype_val.subtype_mk _
    have hEqual : (fun r => D r v) = P ∘ j := by
      funext r
      obtain ⟨_, hr⟩ := hP (j r)
      exact hr.symm
    rw [hEqual]
    exact P.continuous.comp hj
  let W (r : Icc ρ 1) := D r (Z r)
  have hW : Continuous W := by
    apply continuous_iff_continuousAt.mpr
    intro r₀
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hNear₁ := Metric.tendsto_nhds.mp (hZ.continuousAt (x := r₀)) (ε / 2) (half_pos hε)
    have hNear₂ := Metric.tendsto_nhds.mp ((hDFixed (Z r₀)).continuousAt (x := r₀)) (ε / 2) (half_pos hε)
    filter_upwards [hNear₁, hNear₂] with r hr₁ hr₂
    have hDiff : dist (D r (Z r)) (D r (Z r₀)) ≤ dist (Z r) (Z r₀) :=
      dist_inverseDilationLp_le (hR r) r.property.2 (Z r) (Z r₀) (hD r _) (hD r _)
    have hTri := dist_triangle (D r (Z r)) (D r (Z r₀)) (D r₀ (Z r₀))
    change dist (D r (Z r)) (D r₀ (Z r₀)) < ε
    linarith only [hDiff, hTri, hr₁, hr₂]
  have hμ : μ ≤ (volume : Measure (Domain n)) := Measure.restrict_le_self
  let A : Lp E 2 (volume : Measure (Domain n)) →L[ℝ] Lp E 2 μ :=
    Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by norm_num) (by simpa only [one_smul] using hμ)
  refine ⟨⟨A ∘ W, A.continuous.comp hW⟩, ?_⟩
  intro r
  have hAE : ∀ᵐ x ∂ν, Z r x = F r x := by
    have hZ₀ := (memLp_zeroExtension hS (Lp.memLp (F r))).coeFn_toLp
    filter_upwards [hZ₀.filter_mono (ae_mono Measure.restrict_le_self), ae_restrict_mem hS] with x hx hxS
    exact hx.trans (Set.indicator_of_mem hxS _)
  have hRaw : (fun x => Z r (r.val⁻¹ • x)) =ᵐ[μ] (fun x => F r (r.val⁻¹ • x)) :=
    ae_inverse_dilation_property_on_subset hS hU (fun x => (Z r x, F r x))
      (fun z : E × E => z.1 = z.2) (hR r).ne' (hContain r) hAE
  let hSmall := (hD r (Z r)).mono_measure hμ
  let hRawL := hSmall.ae_eq hRaw
  refine ⟨hRawL, ?_⟩
  change A ((hD r (Z r)).toLp _) = hRawL.toLp _
  exact (lp_two_measure_restriction_toLp hμ _ (hD r (Z r)) hSmall).trans
    (MemLp.toLp_congr hSmall hRawL hRaw)

end Thesis

end
