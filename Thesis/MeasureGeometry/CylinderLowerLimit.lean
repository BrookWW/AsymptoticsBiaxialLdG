module

public import Thesis.MeasureGeometry.CylinderLateralLimit
public import Thesis.MeasureGeometry.CylinderLateralClass
public import Thesis.MeasureGeometry.CylinderQuantization
public import Thesis.MeasureGeometry.EnergyMeasure

/-! The normalized lower cylinder comparison on a fixed regular side. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

/-- Evaluation uses the original normalized energy measure rather than
an independently selected energy limit. -/
theorem toReal_normalizedEnergyMeasure_eq_classical_integral
    (a : BulkCoefficients) (ε : ElasticScale) {Ω S : Set Point} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    {Q : Point → S0}
    (hInt : IntegrableOn (fun x => energyDensity a ε (Q x) (ClassicalGradient Q x)) S) :
    (normalizedEnergyMeasure a ε Ω Q (ClassicalGradient Q) S).toReal =
      (∫ x in S, energyDensity a ε (Q x) (ClassicalGradient Q x)) / Real.log (1 / (ε : ℝ)) := by
  have hLog : 0 < Real.log (1 / (ε : ℝ)) :=
    Real.log_pos ((lt_div_iff₀ ε.property.1).2 (by simpa only [one_mul] using ε.property.2))
  rw [normalizedEnergyMeasure_apply a ε Ω Q (ClassicalGradient Q) hS, inter_eq_left.mpr hSΩ,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hLog.le), energy]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => energyDensity_nonneg a ε (Q x) (ClassicalGradient Q x)) hInt.1]
  simp only [div_eq_mul_inv]
  exact mul_comm _ _

private theorem closed_translatedCylinder_mono_height (c e : Point) (r : ℝ) {a b lo hi : ℝ}
    (hlo : a ≤ lo) (hhi : hi ≤ b) :
    translatedClosedAxisCylinder c e r lo hi ⊆ translatedClosedAxisCylinder c e r a b := by
  intro x hx
  exact ⟨hx.1, hlo.trans hx.2.1, hx.2.2.trans hhi⟩

/-- The lower comparison holds at the fixed regular lateral radius and
for every admissible choice of the two end heights, on the same sequence. -/
theorem exists_eventually_normalizedCylinder_lower_of_regularSide
    (hcoarea : External.PlanarScalarCoarea) (hAngular : External.PeriodicAngularSobolev)
    (a : BulkCoefficients) {M : ℝ} (hM : 0 ≤ M)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {Ω K : Set Point} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {r bottom top : ℝ} (hr : 0 < r) (hHeight : bottom < top)
    (hCyl : translatedClosedAxisCylinder c (B 2) r bottom top ⊆ Ω)
    (hSide : ∀ z ∈ Icc bottom top, ∀ w : NativeCircle, c + axisChart B (r • w.val, z) ∈ K)
    {Q₀ : Point → S0} {Q : ℕ → Point → S0}
    (hQ₀ : ContinuousOn Q₀ K) (hVac : MapsTo Q₀ K (vacuum a))
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω) (hConv : TendstoUniformlyOn Q Q₀ atTop K)
    (ε : ℕ → ElasticScale) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hBound : ∀ n x, x ∈ Ω → ‖Q n x‖ ≤ M)
    {D₀ : ℝ}
    (hED : ∀ n x, x ∈ K → energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ D₀)
    (ν : ℕ → Measure Point)
    (hν : ∀ n, ν n = normalizedEnergyMeasure a (ε n) Ω (Q n) (ClassicalGradient (Q n))) :
    ∃ q₀ : C(NativeCircle, vacuum a),
      (∀ w, (q₀ w).val = Q₀ (c + axisChart B (r • w.val, (bottom + top) / 2))) ∧
      ∀ ξ > 0, ∀ᶠ n : ℕ in atTop, ∀ lo hi : ℝ, bottom ≤ lo → lo < hi → hi ≤ top →
        nativeVacuumCircleCost a q₀ - ξ ≤
          ((ν n) (translatedAxisCylinder c (B 2) r lo hi)).toReal / (hi - lo) := by
  obtain ⟨C, _, hLower⟩ := exists_classical_cylinder_lower hcoarea hAngular a M hM
  obtain ⟨p, hp, hStable⟩ := exists_stable_projectedMeridians_of_uniform_convergence a B c
    hK hHeight.le hSide hQ₀ hVac (fun n => (hQ n).continuousOn.mono hKΩ) hConv
  refine ⟨p, hp, ?_⟩
  intro ξ hξ
  let e := nativeVacuumCircleCost a p
  have hg₀ : ∀ᶠ g : ℝ in 𝓝[<] (1 : ℝ), 0 < g := nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)
  have hgc : ContinuousAt (fun g : ℝ => e * g ^ 2) 1 := by fun_prop
  have hgp : ∀ᶠ g : ℝ in 𝓝[<] (1 : ℝ), e - ξ < e * g ^ 2 := by
    have h : Tendsto (fun g : ℝ => e * g ^ 2) (𝓝[<] (1 : ℝ)) (𝓝 e) := by
      simpa only [one_pow, mul_one] using
        (hgc.tendsto.mono_left (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds))
    exact h.eventually (eventually_gt_nhds (sub_lt_self _ hξ))
  have hg₁' : ∀ᶠ g : ℝ in 𝓝[<] (1 : ℝ), g < 1 := self_mem_nhdsWithin
  obtain ⟨g, hg₀', hg₁, hξg⟩ := (hg₀.and (hg₁'.and hgp)).exists
  have hg : g ∈ Ioo (0 : ℝ) 1 := ⟨hg₀', hg₁⟩
  let D := r ^ 2 * D₀ * (2 * Real.pi)
  let L (n : ℕ) := Real.log (1 / (ε n : ℝ))
  let l (n : ℕ) := Real.log (r / (ε n : ℝ))
  have hL (n : ℕ) : 0 < L n := Real.log_pos ((lt_div_iff₀ (ε n).property.1).2
    (by simpa only [one_mul] using (ε n).property.2))
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
  let U (n : ℕ) := e * g ^ 2 * (l n / L n) - (C + Real.log 80 * D) * (L n)⁻¹
  have hUlim : Tendsto U atTop (𝓝 (e * g ^ 2)) := by
    have hab := (hl.const_mul (e * g ^ 2)).sub
      ((tendsto_inv_atTop_zero.comp hLlim).const_mul (C + Real.log 80 * D))
    simpa only [U, Function.comp_def, mul_one, mul_zero, sub_zero] using hab
  have hU := hUlim.eventually (eventually_gt_nhds hξg)
  have hSmall := hε.eventually_lt_const (show 0 < r / 80 by positivity)
  filter_upwards [hStable g hg, hSmall, hU] with n hn hεn hUn
  intro lo hi hlo hih hhi
  let S := translatedAxisCylinder c (B 2) r lo hi
  let V := translatedClosedAxisCylinder c (B 2) r lo hi
  have hVΩ : V ⊆ Ω := (closed_translatedCylinder_mono_height c (B 2) r hlo hhi).trans hCyl
  have hSΩ : S ⊆ Ω := (translatedAxisCylinder_subset_closed _ _ _ _ _).trans hVΩ
  have hS : MeasurableSet S := (isOpen_translatedAxisCylinder _ _ _ _ _).measurableSet
  have hCut : Icc lo hi ⊆ Icc bottom top := fun z hz => ⟨hlo.trans hz.1, hz.2.trans hhi⟩
  have hLat := integrable_cylinderLateralSliceCost_and_bound a (ε n) B c hΩ (hQ n) hr.le
    (fun z hz w => hKΩ (hSide z (hCut hz) w)) (fun z hz w => hED n _ (hSide z (hCut hz) w))
  have hGap (z : ℝ) (hz : z ∈ Ioo lo hi) (w : NativeCircle) :
      g ≤ normalizedSpectralGap a (cylinderSliceMap B c (Q n) z (r • w.val)) :=
    (hn z (hCut (Ioo_subset_Icc_self hz))).1 w
  have hClass (z : ℝ) (hz : z ∈ Ioo lo hi) :
      ∃ q : C(NativeCircle, vacuum a), nativeVacuumCircleCost a q = e ∧
        ∀ w, q w = spectralVacuumPoint a (cylinderSliceMap B c (Q n) z (r • w.val)) := by
    obtain ⟨q, hq, hHom⟩ := (hn z (hCut (Ioo_subset_Icc_self hz))).2
    exact ⟨q, (nativeVacuumCircleCost_homotopic a hHom).symm, hq⟩
  have hE := hLower B c hΩ (Q n) (hQ n) hr hih hg₀' (ε n) hεn hVΩ
    (fun x hx => hBound n x (hVΩ hx)) hGap e hClass hLat.1
  let PS := ∫ z in Ioo lo hi, cylinderLateralSliceCost a (ε n) r B c (Q n) z
  have hLat' : PS ≤ (hi - lo) * D := by
    have hInt : IntegrableOn (fun _ : ℝ => D) (Ioo lo hi) :=
      integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have h := setIntegral_mono_on hLat.1 hInt measurableSet_Ioo (fun z hz => hLat.2 z (Ioo_subset_Icc_self hz))
    rw [setIntegral_const, Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hih.le),
      smul_eq_mul] at h
    exact h
  have hLog80 : 0 ≤ Real.log 80 := Real.log_nonneg (by norm_num)
  let E := ∫ x in S, energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x)
  have hAbsorb : (hi - lo) * (e * g ^ 2 * l n - (C + Real.log 80 * D)) ≤ E := by
    have hP := mul_le_mul_of_nonneg_left hLat' hLog80
    change (hi - lo) * (e * g ^ 2 * l n - C) ≤ E + Real.log 80 * PS at hE
    linarith only [hE, hP]
  have hDiv := div_le_div_of_nonneg_right hAbsorb (mul_pos (sub_pos.mpr hih) (hL n)).le
  have hEq : (hi - lo) * (e * g ^ 2 * l n - (C + Real.log 80 * D)) / ((hi - lo) * L n) = U n := by
    dsimp only [U]
    field_simp [(sub_ne_zero.mpr hih.ne'), (hL n).ne']
  rw [hEq] at hDiv
  have hEClosed : IntegrableOn (fun x => energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x)) V :=
    ((continuousOn_classicalEnergyDensity hΩ a (ε n) (hQ n)).mono hVΩ).integrableOn_compact
      (isCompact_translatedClosedAxisCylinder (B.orthonormal.norm_eq_one 2) _ _ _)
  have hEInt : IntegrableOn (fun x => energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x)) S :=
    hEClosed.mono_set (translatedAxisCylinder_subset_closed _ _ _ _ _)
  have hMass : ((ν n) S).toReal = E / L n := by
    rw [hν n]
    exact toReal_normalizedEnergyMeasure_eq_classical_integral a (ε n) hS hSΩ hEInt
  change e - ξ ≤ ((ν n) S).toReal / (hi - lo)
  have hDbl : E / L n / (hi - lo) = E / ((hi - lo) * L n) := by
    field_simp [(hL n).ne', sub_ne_zero.mpr hih.ne']
  rw [hMass, hDbl]
  exact hUn.le.trans hDiv

end Thesis.MeasureGeometry
