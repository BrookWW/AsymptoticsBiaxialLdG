module

public import Thesis.MeasureGeometry.CylinderRescaling
public import Thesis.MeasureGeometry.CylinderEndHeights
public import Thesis.MeasureGeometry.CylinderLowerLimit

/-! The same-sequence passage from the upper cylinder recovery to
quantization of the original energy measure. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

theorem eventual_log_scale_ge_one {ε : ℕ → ElasticScale}
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 1 ≤ Real.log (1 / (ε n : ℝ)) := by
  have hInv : Tendsto (fun n => (ε n : ℝ)⁻¹) atTop atTop := by
    apply tendsto_inv_nhdsGT_zero.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨hε, Eventually.of_forall (fun n => (ε n).property.1)⟩
  have hLog : Tendsto (fun n => Real.log (1 / (ε n : ℝ))) atTop atTop := by
    simpa only [Function.comp_def, one_div] using Real.tendsto_log_atTop.comp hInv
  exact tendsto_atTop.mp hLog 1

private theorem closed_centeredCylinder_with_small_radius_inside
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {r s : ℝ} (hrs : r < s) :
    translatedClosedAxisCylinder c (B 2) r (-s) s ⊆ ball c (2 * s) := by
  intro x hx
  let y := x - c
  change y ∈ closedAxisCylinder (B 2) r (-s) s at hx
  have hA : |cylinderHeight (B 2) y| ≤ s := abs_le.mpr hx.2
  have hN := norm_add_le (y - cylinderHeight (B 2) y • B 2) (cylinderHeight (B 2) y • B 2)
  rw [sub_add_cancel, norm_smul, Real.norm_eq_abs, B.orthonormal.norm_eq_one 2, mul_one] at hN
  have hR : ‖y - cylinderHeight (B 2) y • B 2‖ ≤ r := hx.1
  rw [mem_ball, dist_eq_norm]
  change ‖y‖ < 2 * s
  linarith only [hN, hA, hR, hrs]

/-- A cylinder upper recovery with the actual endcap energy and regular
lateral data closes the density comparison. The measure and the elastic
sequence in every comparison are the original ones. -/
theorem densityQuantized_of_regularCylinder_upper_recovery
    (hcoarea : External.PlanarScalarCoarea) (hAngular : External.PeriodicAngularSobolev)
    (a : BulkCoefficients) {Ω Spt : Set Point} (hΩ : IsOpen Ω)
    {μ : Measure Point} [IsFiniteMeasure μ] [μ.OuterRegular]
    (hμ : μ (closure Ω)ᶜ = 0)
    {f : Point → ℝ≥0∞} (hf : Measurable f)
    (hRep : μ.restrict Ω = (HausdorffOne.restrict (Ω ∩ μ.support)).withDensity f)
    (hRect : CountablyRectifiableOne (Ω ∩ μ.support)) (hLen : HausdorffOne (Ω ∩ μ.support) < ⊤)
    {η : ℝ} (hη : 0 < η)
    (hD : ∀ x ∈ Ω ∩ μ.support, ∃ θ ≥ η / 2, Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ))
    (hLoc : LocallyFiniteIn (Ω \ μ.support) Spt)
    {M : ℝ} (hM : 0 ≤ M) (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (Q₀ : Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω)
    (hEuler : ∀ n x, x ∈ Ω → (ε n : ℝ) ^ 2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x))
    (hBound : ∀ n x, x ∈ Ω → ‖Q n x‖ ≤ M)
    (hEnergy : ∀ n, energy a (ε n) Ω (Q n) (ClassicalGradient (Q n)) ≤
      ENNReal.ofReal (M * (Real.log (1 / (ε n : ℝ)) + 1)))
    (hQ₀ : ContinuousOn Q₀ ((Ω \ μ.support) \ Spt))
    (hVac : MapsTo Q₀ ((Ω \ μ.support) \ Spt) (vacuum a))
    (hDensity : ∀ K : Set Point, IsCompact K → K ⊆ (Ω \ μ.support) \ Spt → ∃ D > (0 : ℝ),
      ∀ n x, x ∈ K → energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ D)
    (hConv : ∀ K : Set Point, IsCompact K → K ⊆ (Ω \ μ.support) \ Spt → TendstoUniformlyOn Q Q₀ atTop K)
    (ν : ℕ → Measure Point) (hνfin : ∀ n, IsFiniteMeasure (ν n))
    (hν : ∀ n, ν n = normalizedEnergyMeasure a (ε n) Ω (Q n) (ClassicalGradient (Q n)))
    (hWeak : WeakStarOnClosure Ω ν μ)
    (hUpper : ∀ cap : ℝ, 0 ≤ cap → ∃ C ≥ (0 : ℝ),
      ∀ (B : OrthonormalBasis (Fin 3) ℝ Point) (x : Point) {r s : ℝ}, 0 < r → 0 < s → r < s →
        closedBall x (2 * s) ⊆ Ω →
        ∀ K : Set Point, IsCompact K → K ⊆ (Ω \ μ.support) \ Spt →
          (∀ z ∈ Icc (-s) s, ∀ w : NativeCircle, x + axisChart B (r • w.val, z) ∈ K) →
          ∀ p : C(NativeCircle, vacuum a),
            (∀ w, (p w).val = Q₀ (x + axisChart B (r • w.val, 0))) →
            ∀ ξ > 0, ∀ᶠ n : ℕ in atTop,
              ∀ lo ∈ Ioo (-s) (-(s / 2)), ∀ hi ∈ Ioo (s / 2) s,
                planarSmoothEnergy a (ε n) (cylinderSliceMap B x (Q n) lo) r +
                  planarSmoothEnergy a (ε n) (cylinderSliceMap B x (Q n) hi) r ≤
                    cap * Real.log (1 / (ε n : ℝ)) →
                ((ν n) (translatedAxisCylinder x (B 2) r lo hi)).toReal / (hi - lo) ≤
                  nativeVacuumCircleCost a p + C * (r / (hi - lo)) + ξ) :
    DensityQuantized a μ (Ω ∩ μ.support) := by
  have hS : MeasurableSet (Ω ∩ μ.support) := hΩ.measurableSet.inter μ.isClosed_support.measurableSet
  have hνsupp (n : ℕ) : ν n (closure Ω)ᶜ = 0 := by
    rw [hν n]
    exact normalizedEnergyMeasure_compl_closure a (ε n) Ω (Q n) (ClassicalGradient (Q n))
  have hTang := ae_flat_energy_line_and_density hΩ hS inter_subset_left hRect hLen hη hD hf hRep
  filter_upwards [hTang, ae_restrict_mem hS] with x hx hxS
  obtain ⟨e, b, he, hb, hFlat, hDen⟩ := hx
  obtain ⟨B, hB⟩ := exists_axis_orthonormalBasis he
  obtain ⟨R', hR', hR'Ω⟩ := Metric.isOpen_iff.mp hΩ x hxS.1
  let R := R' / 2
  have hR : 0 < R := half_pos hR'
  have hOuter : closedBall x R ⊆ Ω :=
    (closedBall_subset_ball (by dsimp [R]; linarith only [hR'])).trans hR'Ω
  let cap := 16 * M / R
  have hCap₀ : 0 ≤ cap := div_nonneg (mul_nonneg (by norm_num) hM) hR.le
  obtain ⟨C, hC, hUpperC⟩ := hUpper cap hCap₀
  let A := 2 * C + 1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hFlatB : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun s => SupportingAnalysis.blownUpMeasure (d := 1) x s μ)
      (ENNReal.ofReal b • HausdorffOne.restrict ((Submodule.span ℝ {B 2} : Submodule ℝ Point) : Set Point)) := by
    simpa only [hB] using hFlat
  refine ⟨b, ?_, hDen⟩
  apply axialDensity_mem_quantized_of_cylinder_comparison hνfin hνsupp hμ hWeak he hb hFlat a hA
    (δ₀ := 1 / 4) (by norm_num)
  intro δ hδ
  have hBands := eventually_exists_fixed_regular_lateral_radius hΩ hLoc hη hD hxS.1 B hFlatB hδ.1
  filter_upwards [hBands, eventually_mem_positive_interval (half_pos hR)] with s hBand hs
  obtain ⟨r, hr, K, hK, hKR, hSide⟩ := hBand
  have hr₀ : 0 < r := (mul_pos hδ.1 hs.1).trans hr.1
  have hrs : r < s := hr.2.trans (by
    have hh : 2 * δ < 1 := by linarith only [hδ.2]
    simpa only [one_mul] using (mul_lt_mul_of_pos_right hh hs.1))
  have hRs : 2 * s ≤ R := by linarith only [hs.2]
  have hBall := (closedBall_subset_closedBall hRs).trans hOuter
  have hCyl : translatedClosedAxisCylinder x (B 2) r (-s) s ⊆ Ω :=
    (closed_centeredCylinder_with_small_radius_inside B x hrs).trans (ball_subset_closedBall.trans hBall)
  have hKΩ : K ⊆ Ω := hKR.trans (sdiff_subset.trans sdiff_subset)
  obtain ⟨D, _, hED⟩ := hDensity K hK hKR
  obtain ⟨p, hp, hLower⟩ := exists_eventually_normalizedCylinder_lower_of_regularSide hcoarea hAngular
    a hM B x hΩ hK hKΩ hr₀ (by linarith only [hs.1]) hCyl hSide (hQ₀.mono hKR)
    (hVac.mono_left hKR) hQ (hConv K hK hKR) ε hε hBound hED ν hν
  have hp₀ (w : NativeCircle) : (p w).val = Q₀ (x + axisChart B (r • w.val, 0)) := by
    simpa only [neg_add_cancel, zero_div] using hp w
  let k := nativeVacuumCircleCost a p
  have hk : k ∈ ({0, kappaStar a, 2 * kappaStar a} : Set ℝ) := nativeVacuumCircleCost_mem_three a p
  filter_upwards [hLower δ hδ.1, hUpperC B x hr₀ hs.1 hrs hBall K hK hKR hSide p hp₀ δ hδ.1,
    eventual_log_scale_ge_one hε] with n hLn hUn hLog
  obtain ⟨lo, hlo, hi, hhi, hEnd⟩ := good_classical_endHeights_of_logarithmic_ball_bound
    a (ε n) B x hΩ (hQ n) (hEuler n) hM hs.1 hrs hRs hOuter hLog (hEnergy n)
  have hH : s ≤ hi - lo := by linarith only [hlo.2, hhi.1]
  have hLoHi : lo < hi := by linarith only [hH, hs.1]
  have hrbound : r / (hi - lo) ≤ 2 * δ := by
    apply (div_le_iff₀ (sub_pos.mpr hLoHi)).mpr
    exact hr.2.le.trans (mul_le_mul_of_nonneg_left hH (mul_nonneg (by norm_num) hδ.1.le))
  have hU := hUn lo hlo hi hhi hEnd
  have hL := hLn lo hi hlo.1.le hLoHi hhi.2.le
  have hError : |((ν n) (translatedAxisCylinder x (B 2) r lo hi)).toReal / (hi - lo) - k| ≤ A * δ := by
    have h := mul_le_mul_of_nonneg_left hrbound hC
    dsimp only [A]
    apply abs_le.mpr
    constructor
    · change k - δ ≤ ((ν n) (translatedAxisCylinder x (B 2) r lo hi)).toReal / (hi - lo) at hL
      nlinarith only [hL, mul_nonneg hC hδ.1.le]
    · change ((ν n) (translatedAxisCylinder x (B 2) r lo hi)).toReal / (hi - lo) ≤ k + C * (r / (hi - lo)) + δ at hU
      linarith only [hU, h]
  refine ⟨r / s, ?_, lo / s, ?_, hi / s, ?_, k, hk, ?_⟩
  · exact ⟨(le_div_iff₀ hs.1).mpr hr.1.le, (div_le_iff₀ hs.1).mpr hr.2.le⟩
  · refine ⟨(le_div_iff₀ hs.1).mpr (by simpa only [neg_mul, one_mul] using hlo.1.le),
      (div_le_iff₀ hs.1).mpr ?_⟩
    linarith only [hlo.2]
  · refine ⟨(le_div_iff₀ hs.1).mpr ?_, (div_le_one hs.1).mpr hhi.2.le⟩
    linarith only [hhi.1]
  · have hMul : s * (hi / s - lo / s) = hi - lo := by
      field_simp [hs.1.ne']
    rw [← hB, ← translatedAxisCylinder_eq_dilate_div x (B 2) hs.1, hMul]
    exact hError

end Thesis.MeasureGeometry
