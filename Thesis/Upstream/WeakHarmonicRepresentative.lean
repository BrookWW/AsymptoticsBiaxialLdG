module

public import HolderToCK.Analysis.Poisson.WeakHarmonicSmooth
import HolderToCK.Analysis.RepresentativeGluing
import HarmonicMaps.Analysis.InteriorSobolevApproximation
import HarmonicMaps.Analysis.SobolevAECongruence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Native continuous representatives of Euclidean weak harmonic maps. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Laplacian Topology

namespace HolderToCK

private theorem tendsto_integral_norm_sub_of_tendsto_eLpNorm_two
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X} [IsFiniteMeasure μ]
    {u : X → E} {v : ℕ → X → E} (hu : MemLp u 2 μ) (hv : ∀ k, MemLp (v k) 2 μ)
    (h : Tendsto (fun k => eLpNorm (v k-u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖v k x-u x‖ ∂μ) atTop (𝓝 0) := by
  let C := μ univ ^ (1/2 : ℝ)
  have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ)
  have hUpper : Tendsto (fun k => eLpNorm (v k-u) 2 μ * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const h (Or.inr hC)
  have hL₁ : Tendsto (fun k => eLpNorm (v k-u) 1 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun _ => bot_le)
    intro k
    have he := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
      (by norm_num) (((hv k).sub hu).aestronglyMeasurable)
    have hExp : 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = 1/2 := by norm_num
    rw [hExp] at he
    exact he
  have hReal : Tendsto (fun k => (eLpNorm (v k-u) 1 μ).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hL₁
  apply hReal.congr
  intro k
  change _ = ∫ x, ‖(v k-u) x‖ ∂μ
  rw [integral_norm_eq_lintegral_enorm (((hv k).sub hu).aestronglyMeasurable),
    eLpNorm_one_eq_lintegral_enorm]

private theorem harmonicMollification_sub_mean_bound
    {n q : ℕ} (hn : 2 ≤ n) {c : Domain n} {R : ℝ} (hR : 0 < R)
    {u m : Domain n → Ambient q} (hu : IntegrableOn u (ball c (R/2)))
    (hm : ContDiff ℝ ∞ m) (hΔ : ∀ x ∈ ball c (3*R/4), Laplacian.laplacian m x = 0) :
    let h : PositiveRadius := ⟨R/4,div_pos hR (by norm_num)⟩
    let C := (volume.real (ball (0 : Domain n) h.val))⁻¹
    ∀ y ∈ ball c (R/4),
      dist (m y) (C • ∫ x in ball y h.val, u x) ≤
        C * ∫ x in ball c (R/2), ‖m x-u x‖ := by
  intro h C y hy
  have hY (x : Domain n) (hx : x ∈ closedBall y h.val) : x ∈ ball c (R/2) := by
    have hx' : dist x y ≤ R/4 := mem_closedBall.mp hx
    have hy' : dist y c < R/4 := mem_ball.mp hy
    exact mem_ball.mpr ((dist_triangle x y c).trans_lt (by linarith only [hx',hy']))
  have hLarge : closedBall y h.val ⊆ ball c (3*R/4) :=
    fun x hx => ball_subset_ball (by linarith only [hR]) (hY x hx)
  have hBall : ball y h.val ⊆ ball c (R/2) := fun x hx => hY x (ball_subset_closedBall hx)
  have hMass : (volume : Measure (Domain n)).real (ball y h.val) =
      (volume : Measure (Domain n)).real (ball (0 : Domain n) h.val) := by
    rw [measureReal_def,measureReal_def,
      Measure.addHaar_ball_of_pos volume y h.property,
      Measure.addHaar_ball_of_pos volume (0 : Domain n) h.property]
  have hMean := HarmonicMaps.harmonic_ball_meanValue hn y h _ isOpen_ball hLarge
    m hm.contDiffOn (fun x hx => hΔ x (hLarge (ball_subset_closedBall hx)))
  rw [hMass] at hMean
  have hmB : IntegrableOn m (ball c (R/2)) :=
    (hm.continuous.continuousOn.integrableOn_compact (isCompact_closedBall c (R/2))).mono_set
      ball_subset_closedBall
  have hI : IntegrableOn (fun x => ‖m x-u x‖) (ball c (R/2)) := (hmB.sub hu).norm
  have hC : 0 ≤ C := inv_nonneg.mpr ENNReal.toReal_nonneg
  rw [dist_eq_norm,hMean,← smul_sub,← integral_sub (hmB.mono_set hBall) (hu.mono_set hBall),
    norm_smul,Real.norm_of_nonneg hC]
  apply mul_le_mul_of_nonneg_left _ hC
  calc
    _ ≤ ∫ x in ball y h.val, ‖m x-u x‖ := norm_integral_le_integral_norm _
    _ ≤ _ := setIntegral_mono_set hI
      (Eventually.of_forall fun x => norm_nonneg _) (Eventually.of_forall hBall)

/-- A weak harmonic map on a ball has a continuous representative on
the concentric quarter ball, obtained from the actual fixed ball average. -/
theorem WeakPoissonOn.exists_continuousRepresentative_on_quarter_ball
    {n q : ℕ} (hn : 2 ≤ n) {c : Domain n} {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn (ballDomain c R) Du (fun _ => 0))
    (hu : MemW12 (ballDomain c R) u Du) :
    ∃ v : Domain n → Ambient q, u =ᵐ[volume.restrict (ball c (R/4))] v ∧
      ContinuousOn v (ball c (R/4)) := by
  let h : ℕ → PositiveRadius := fun k => ⟨(R/8) / ((k : ℝ)+1),by positivity⟩
  let M : ℕ → Domain n → Ambient q := fun k =>
    euclideanMollification (ballDomain c R) u hu.integrable_ball (h k)
  have hhR (k : ℕ) : (h k).val ≤ R/8 := by
    change (R/8) / ((k : ℝ)+1) ≤ R/8
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ)+1)).mpr
    have h : 0 ≤ (R/8) * (k : ℝ) := by positivity
    nlinarith only [h]
  have hscale : Tendsto (fun k => (h k).val) atTop (𝓝 0) := by
    simpa only [h,div_eq_mul_inv,one_mul,mul_zero] using
      (tendsto_const_nhds (x := R/8)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  have hFilter : Tendsto h atTop (comap (fun t : PositiveRadius => t.val) (𝓝 (0 : ℝ))) :=
    tendsto_comap_iff.mpr hscale
  have hMol (k : ℕ) : ContDiff ℝ ∞ (M k) ∧
      ∀ y ∈ ball c (3*R/4), Laplacian.laplacian (M k) y = 0 := by
    have hMargin : 3*R/4 + (h k).val/2 ≤ R := by linarith only [hhR k,hR]
    have hm := hEq.mollification_laplacian_ball hu 0
      (Eventually.of_forall fun y => by simp only [norm_zero,zero_mul,le_refl]) (h k) hMargin
    exact ⟨hm.1,fun y hy => by simpa only [Pi.zero_apply,smul_zero,integral_zero] using hm.2 y hy⟩
  let S := ball c (R/2)
  let T := ball c (R/4)
  let μ : Measure (Domain n) := volume.restrict S
  let ν : Measure (Domain n) := volume.restrict T
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have huS : MemLp u 2 μ := hu.2.1.mono_measure
    (Measure.restrict_mono (ball_subset_ball (half_lt_self hR).le) le_rfl)
  have hmS (k : ℕ) : MemLp (M k) 2 μ := by
    obtain ⟨A,hA⟩ := (isCompact_closedBall c (R/2)).exists_bound_of_continuousOn
      (hMol k).1.continuous.continuousOn
    exact MemLp.of_bound (hMol k).1.continuous.aestronglyMeasurable A
      ((ae_restrict_mem measurableSet_ball).mono fun y hy => hA y (ball_subset_closedBall hy))
  have hL₂ : Tendsto (fun k => eLpNorm (M k-u) 2 μ) atTop (𝓝 0) := by
    change Tendsto (fun k => eLpNorm (fun x => M k x-u x) 2 (volume.restrict (ball c (R/2)))) atTop (𝓝 0)
    simpa only [Function.comp_def,M] using
      (hu.tendsto_eLpNorm_mollification_inner_ball (half_lt_self hR)).comp hFilter
  have hErr : Tendsto (fun k => ∫ x in S, ‖M k x-u x‖) atTop (𝓝 0) :=
    tendsto_integral_norm_sub_of_tendsto_eLpNorm_two huS hmS hL₂
  let C := (volume.real (ball (0 : Domain n) (R/4)))⁻¹
  let v (y : Domain n) : Ambient q := C • ∫ x in ball y (R/4), u x
  have hCv : Tendsto (fun k => C * ∫ x in S, ‖M k x-u x‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hErr.const_mul C
  have hUni : TendstoUniformlyOn M v atTop T := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [hCv.eventually_lt_const hδ] with k hk y hy
    rw [dist_comm]
    exact (harmonicMollification_sub_mean_bound hn hR (huS.integrable (by norm_num))
      (hMol k).1 (hMol k).2 y hy).trans_lt hk
  have hνμ : ν ≤ μ := Measure.restrict_mono (ball_subset_ball (by linarith only [hR])) le_rfl
  have hL₂' : Tendsto (fun k => eLpNorm (M k-u) 2 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL₂ (fun _ => bot_le)
      (fun k => eLpNorm_mono_measure _ hνμ)
  have hInMeasure : TendstoInMeasure ν M atTop u :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun k => ((hmS k).mono_measure hνμ).aestronglyMeasurable)
      (huS.mono_measure hνμ).aestronglyMeasurable hL₂'
  obtain ⟨σ,hσ,hσu⟩ := hInMeasure.exists_seq_tendsto_ae
  have hAE : u =ᵐ[ν] v := by
    filter_upwards [hσu,ae_restrict_mem (μ := volume) (measurableSet_ball (x := c) (ε := R/4))]
      with y hu' hy
    have hv' := (hUni.tendsto_at hy).comp hσ.tendsto_atTop
    exact tendsto_nhds_unique hu' hv'
  exact ⟨v,hAE,hUni.continuousOn
    (Eventually.of_forall fun k => (hMol k).1.continuous.continuousOn).frequently⟩

/-- Every weak harmonic map has a continuous representative on its
actual open domain, without a prior representative regularity assumption. -/
theorem WeakPoissonOn.exists_continuousRepresentative_of_zero
    {n q : ℕ} (hn : 2 ≤ n) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn Ω Du (fun _ => 0)) (hu : MemW12Loc Ω u Du) :
    ∃ v : Domain n → Ambient q, u =ᵐ[volume.restrict Ω.val] v ∧ ContinuousOn v Ω.val := by
  classical
  have hLocal (x : Ω.val) : ∃ r > (0 : ℝ), closedBall x.val r ⊆ Ω.val := by
    obtain ⟨r,hr,hB⟩ := Metric.isOpen_iff.mp Ω.property x.val x.property
    exact ⟨r/2,half_pos hr,(closedBall_subset_ball (half_lt_self hr)).trans hB⟩
  choose r hr hR using hLocal
  let U (x : Ω.val) := ball x.val (r x/4)
  have hV (x : Ω.val) : ∃ v : Domain n → Ambient q,
      u =ᵐ[volume.restrict (U x)] v ∧ ContinuousOn v (U x) :=
    (hEq.mono (ball_subset_closedBall.trans (hR x))).exists_continuousRepresentative_on_quarter_ball
      hn (hr x) (hu.memW12_ball (hR x))
  choose v hvAE hvC using hV
  have hCov : Ω.val ⊆ ⋃ x, U x := fun x hx => mem_iUnion.mpr
    ⟨⟨x,hx⟩,mem_ball_self (div_pos (hr ⟨x,hx⟩) (by norm_num))⟩
  obtain ⟨w,hwC,hwAE,_⟩ := continuous_representatives_glue u Ω.val Ω.property U v
    (fun _ => isOpen_ball) hvC (fun x => (hvAE x).symm) hCov
  exact ⟨w,hwAE.symm,hwC⟩

/-- The same original weak harmonic Sobolev graph has a classical
smooth harmonic representative in the open domain. -/
theorem WeakPoissonOn.exists_smoothRepresentative_of_zero
    {n q : ℕ} (hn : 2 ≤ n) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn Ω Du (fun _ => 0)) (hu : MemW12Loc Ω u Du) :
    ∃ v : Domain n → Ambient q, u =ᵐ[volume.restrict Ω.val] v ∧
      ContDiffOn ℝ ∞ v Ω.val ∧ ∀ x ∈ Ω.val, Laplacian.laplacian v x = 0 := by
  obtain ⟨v,hv,hC⟩ := hEq.exists_continuousRepresentative_of_zero hn hu
  exact ⟨v,hv,hEq.contDiffOn_of_continuous_weak_harmonic hn Ω (hu.congr_ae hv EventuallyEq.rfl) hC⟩

end HolderToCK
