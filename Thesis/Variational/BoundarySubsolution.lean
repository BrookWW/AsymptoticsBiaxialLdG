module

public import Thesis.External.SubsolutionMeanValue
public import Thesis.Variational.ProjectedLaplacian
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Smooth constant extension of a scalar subsolution across the physical wall. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff

set_option autoImplicit false
noncomputable section

namespace Thesis

private def clipSlope (k η x : ℝ) : ℝ := Real.smoothTransition ((x - k) / η)

private def smoothClip (k η x : ℝ) : ℝ :=
  k + η + ∫ y in k..x, clipSlope k η y

private theorem contDiff_clipSlope (k η : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (clipSlope k η) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const η)

private theorem smoothClip_hasDerivAt (k η x : ℝ) : HasDerivAt (smoothClip k η) (clipSlope k η x) x := by
  have hC := (contDiff_clipSlope k η).continuous
  have h := intervalIntegral.integral_hasDerivAt_right
    (hC.intervalIntegrable k x) hC.stronglyMeasurable.stronglyMeasurableAtFilter hC.continuousAt
  exact h.const_add (k + η)

private theorem contDiff_smoothClip (k η : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (smoothClip k η) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (smoothClip_hasDerivAt k η x).differentiableAt, ?_⟩
  have h : deriv (smoothClip k η) = clipSlope k η :=
    funext fun x => (smoothClip_hasDerivAt k η x).deriv
  rw [h]
  exact contDiff_clipSlope k η

private theorem smoothClip_eq_const {k η x : ℝ} (hη : 0 < η) (hx : x ≤ k) :
    smoothClip k η x = k + η := by
  have h : (∫ y in k..x, clipSlope k η y) = ∫ _ in k..x, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_ge hx] at hy
    exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy.2) hη.le)
  rw [smoothClip, h, intervalIntegral.integral_zero, add_zero]

private theorem smoothClip_bounds {k η x : ℝ} (hk : 0 ≤ k) (hη : 0 < η) (hx : 0 ≤ x) :
    x ≤ smoothClip k η x ∧ smoothClip k η x ≤ x + (k + η) := by
  by_cases h : x ≤ k
  · rw [smoothClip_eq_const hη h]
    exact ⟨h.trans (le_add_of_nonneg_right hη.le), le_add_of_nonneg_left hx⟩
  have hxk : k ≤ x := (lt_of_not_ge h).le
  have hC := (contDiff_clipSlope k η).continuous
  have hUp : (∫ y in k..x, clipSlope k η y) ≤ x - k := by
    have h := intervalIntegral.integral_mono_on hxk (hC.intervalIntegrable k x)
      (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) (fun y _ => Real.smoothTransition.le_one _)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using h
  have hLow : x ≤ k + η + ∫ y in k..x, clipSlope k η y := by
    by_cases hEnd : x ≤ k + η
    · exact hEnd.trans (le_add_of_nonneg_right (intervalIntegral.integral_nonneg hxk
        fun y _ => Real.smoothTransition.nonneg _))
    · have hxE : k + η ≤ x := (lt_of_not_ge hEnd).le
      have hOne : (∫ y in (k + η)..x, clipSlope k η y) = x - (k + η) := by
        calc
          _ = ∫ _ in (k + η)..x, (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro y hy
            rw [uIcc_of_le hxE] at hy
            exact Real.smoothTransition.one_of_one_le ((le_div_iff₀ hη).mpr (by linarith only [hy.1]))
          _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hC.intervalIntegrable k (k + η)) (hC.intervalIntegrable (k + η) x), hOne]
      have hp : 0 ≤ ∫ y in k..(k + η), clipSlope k η y :=
        intervalIntegral.integral_nonneg (le_add_of_nonneg_right hη.le) (fun y _ => Real.smoothTransition.nonneg _)
      linarith only [hp]
  exact ⟨hLow, by dsimp only [smoothClip]; linarith only [hUp, hk]⟩

private theorem smoothClip_derivative_bounds {k η : ℝ} (hη : 0 < η) (x : ℝ) :
    0 ≤ deriv (smoothClip k η) x ∧ deriv (smoothClip k η) x ≤ 1 ∧
      0 ≤ deriv (deriv (smoothClip k η)) x := by
  have hD : deriv (smoothClip k η) = clipSlope k η :=
    funext fun x => (smoothClip_hasDerivAt k η x).deriv
  rw [hD]
  have hM : Monotone (clipSlope k η) := Real.smoothTransition.monotone.comp
    (fun x y hxy => div_le_div_of_nonneg_right (sub_le_sub_right hxy k) hη.le)
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _, hM.deriv_nonneg⟩

private theorem fderiv_fderiv_real_apply {f : ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) f) (x v : ℝ) :
    ((fderiv ℝ (fderiv ℝ f) x) v) v = deriv (deriv f) x * v ^ 2 := by
  let J := fderiv ℝ f
  let L := ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)
  have hJ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) J := hf.fderiv_right (by simp)
  have hDet := (L.hasFDerivAt (x := J x)).comp x ((hJ.differentiable (by simp) x).hasFDerivAt)
  have hD : (L ∘ J) = deriv f := funext fun _ => fderiv_apply_one_eq_deriv
  rw [hD] at hDet
  have h := hDet.hasDerivAt.deriv
  change deriv (deriv f) x = ((fderiv ℝ J x) 1) 1 at h
  have hv : v = v • (1 : ℝ) := by simp only [smul_eq_mul, mul_one]
  change ((fderiv ℝ J x) v) v = _
  have hJv : (fderiv ℝ J x) v = v • (fderiv ℝ J x) 1 :=
    (congrArg (fderiv ℝ J x) hv).trans (map_smul _ _ _)
  have hv' : ((fderiv ℝ J x) 1) v = v * ((fderiv ℝ J x) 1) 1 :=
    (congrArg ((fderiv ℝ J x) 1) hv).trans (map_smul _ _ _)
  rw [hJv, smul_apply, smul_eq_mul, hv', ← h]
  ring

theorem laplacian_real_comp_smooth
    {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) f)
    {U : Set Point} (hU : IsOpen U) {w : Point → ℝ} (hw : ContDiffOn ℝ 2 w U)
    {x : Point} (hx : x ∈ U) :
    laplacian (f ∘ w) x = deriv f (w x) * laplacian w x +
      deriv (deriv f) (w x) * ∑ j, (coordDeriv j w x) ^ 2 := by
  rw [laplacian_comp_smooth_map hf hU hw hx]
  rw [fderiv_eq_smul_deriv, smul_eq_mul, mul_comm (laplacian w x), Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => fderiv_fderiv_real_apply hf _ _

theorem laplacian_eq_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : Point → E} {x : Point}
    (h : f =ᶠ[𝓝 x] g) : laplacian f x = laplacian g x := by
  unfold laplacian
  refine Finset.sum_congr rfl fun j _ => ?_
  have hD : coordDeriv j f =ᶠ[𝓝 x] coordDeriv j g := by
    filter_upwards [eventually_eventually_nhds.mpr h] with y hy
    have hy' : f =ᶠ[𝓝 y] g := hy
    exact DFunLike.congr_fun hy'.fderiv_eq (axis j)
  exact DFunLike.congr_fun hD.fderiv_eq (axis j)

/-- A scalar linear subsolution can be smoothly capped from below and
extended by the cap value across a wall on which its trace is bounded.
The error in the pointwise upper envelope is (2eta). -/
theorem exists_smooth_capped_subsolution_for_physical_wall
    {U : Set Point} (hU : IsOpen U) (c : Point) {r : ℝ} {A a η : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hη : 0 < η) {w : Point → ℝ}
    (hwC : ContinuousOn w (closure U ∩ Metric.ball c r))
    (hw : ContDiffOn ℝ 2 w (U ∩ Metric.ball c r))
    (hPos : ∀ x ∈ U ∩ Metric.ball c r, 0 ≤ w x)
    (hTrace : ∀ x ∈ frontier U ∩ Metric.ball c r, w x ≤ a)
    (hLap : ∀ x ∈ U ∩ Metric.ball c r, -laplacian w x ≤ A * w x) :
    ∃ f : Point → ℝ, ContDiffOn ℝ 2 f (Metric.ball c r) ∧
      (∀ x ∈ Metric.ball c r, 0 ≤ f x ∧ -laplacian f x ≤ A * f x) ∧
      (∀ x ∈ closure U ∩ Metric.ball c r, w x ≤ f x) ∧
      ∀ x ∈ Metric.ball c r, f x ≤ U.indicator w x + (a + 2 * η) := by
  classical
  let k := a + η
  let φ := smoothClip k η
  let f := U.piecewise (φ ∘ w) (fun _ => k + η)
  have hφ := contDiff_smoothClip k η
  have hk : 0 ≤ k := add_nonneg ha hη.le
  have hK : 0 ≤ k + η := add_nonneg hk hη.le
  have hfIn (x : Point) (hx : x ∈ U) : f =ᶠ[𝓝 x] φ ∘ w := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact piecewise_eq_of_mem U (φ ∘ w) (fun _ => k + η) hy
  have hfOut (x : Point) (hx : x ∈ Metric.ball c r) (hxU : x ∉ U) :
      f =ᶠ[𝓝 x] (fun _ => k + η) := by
    by_cases hC : x ∈ closure U
    · have hF : x ∈ frontier U := by rw [frontier, hU.interior_eq]; exact ⟨hC, hxU⟩
      have hwx : w x < k := (hTrace x ⟨hF, hx⟩).trans_lt (lt_add_of_pos_right _ hη)
      have hSmall : ∀ᶠ y in 𝓝[closure U ∩ Metric.ball c r] x, w y < k :=
        (hwC x ⟨hC, hx⟩).tendsto (Iio_mem_nhds hwx)
      filter_upwards [eventually_nhdsWithin_iff.mp hSmall, Metric.isOpen_ball.mem_nhds hx] with y hy hyB
      by_cases hyU : y ∈ U
      · rw [show f y = φ (w y) from piecewise_eq_of_mem U _ _ hyU]
        exact smoothClip_eq_const hη (hy ⟨subset_closure hyU, hyB⟩).le
      · exact piecewise_eq_of_notMem U _ _ hyU
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hC] with y hy
      exact piecewise_eq_of_notMem U _ _ (fun h => hy (subset_closure h))
  have hf (x : Point) (hx : x ∈ Metric.ball c r) : ContDiffAt ℝ 2 f x := by
    by_cases h : x ∈ U
    · have hC : ContDiffAt ℝ 2 w x :=
        (hw x ⟨h, hx⟩).contDiffAt ((hU.inter Metric.isOpen_ball).mem_nhds ⟨h, hx⟩)
      exact (((hφ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt).comp x hC).congr_of_eventuallyEq
        (hfIn x h)
    · exact contDiffAt_const.congr_of_eventuallyEq (hfOut x hx h)
  refine ⟨f, fun x hx => (hf x hx).contDiffWithinAt, ?_, ?_, ?_⟩
  · intro x hx
    by_cases h : x ∈ U
    · have hEq : f x = φ (w x) := piecewise_eq_of_mem U _ _ h
      have hw₀ := hPos x ⟨h, hx⟩
      have hB := (smoothClip_bounds hk hη hw₀).1
      refine ⟨hEq.symm ▸ hw₀.trans hB, ?_⟩
      rw [laplacian_eq_of_eventuallyEq (hfIn x h), laplacian_real_comp_smooth hφ (hU.inter Metric.isOpen_ball)
        hw ⟨h, hx⟩, hEq]
      obtain ⟨hD₁, hD₂, hD₃⟩ := smoothClip_derivative_bounds (k := k) hη (w x)
      have hS : 0 ≤ ∑ j : Fin 3, (coordDeriv j w x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h1 := mul_le_mul_of_nonneg_left (hLap x ⟨h, hx⟩) hD₁
      have h2 := mul_le_mul_of_nonneg_right hD₂ (mul_nonneg hA hw₀)
      have h3 := mul_le_mul_of_nonneg_left hB hA
      nlinarith only [h1, h2, h3, mul_nonneg hD₃ hS]
    · have hEq : f x = k + η := piecewise_eq_of_notMem U _ _ h
      refine ⟨hEq.symm ▸ hK, ?_⟩
      have hConst : laplacian (fun _ : Point => k + η) x = 0 := by
        have hc (j : Fin 3) (a : ℝ) : coordDeriv j (fun _ : Point => a) = fun _ => 0 := by
          funext y
          exact DFunLike.congr_fun (hasFDerivAt_const a y).fderiv (axis j)
        simp only [laplacian, hc, Finset.sum_const_zero]
      rw [laplacian_eq_of_eventuallyEq (hfOut x hx h), hConst, neg_zero, hEq]
      exact mul_nonneg hA hK
  · intro x hx
    by_cases h : x ∈ U
    · rw [show f x = φ (w x) from piecewise_eq_of_mem U _ _ h]
      exact (smoothClip_bounds hk hη (hPos x ⟨h, hx.2⟩)).1
    · have hF : x ∈ frontier U := by rw [frontier, hU.interior_eq]; exact ⟨hx.1, h⟩
      rw [show f x = k + η from piecewise_eq_of_notMem U _ _ h]
      exact (hTrace x ⟨hF, hx.2⟩).trans (by dsimp only [k]; linarith only [hη])
  · intro x hx
    by_cases h : x ∈ U
    · rw [show f x = φ (w x) from piecewise_eq_of_mem U _ _ h, indicator_of_mem h]
      exact ((smoothClip_bounds hk hη (hPos x ⟨h, hx⟩)).2).trans_eq (by dsimp only [k]; ring)
    · rw [show f x = k + η from piecewise_eq_of_notMem U _ _ h, indicator_of_notMem h, zero_add]
      dsimp only [k]
      linarith

/-- The scalar subsolution estimate on a cut ball includes its physical
trace bound, and applies at every center in the closure of the domain. -/
theorem exists_capped_meanValue_bound_on_boundary_cap
    (hMean : External.ClassicalScalarSubsolutionMeanValue) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set Point), IsOpen U → ∀ c ∈ closure U,
      ∀ r ∈ Ioc (0 : ℝ) 1, ∀ (w : Point → ℝ) (a : ℝ), 0 ≤ a →
        ContinuousOn w (closure U ∩ Metric.ball c r) →
        ContDiffOn ℝ 2 w (U ∩ Metric.ball c r) →
        IntegrableOn w (U ∩ Metric.ball c r) volume →
        (∀ x ∈ U ∩ Metric.ball c r, 0 ≤ w x) →
        (∀ x ∈ frontier U ∩ Metric.ball c r, w x ≤ a) →
        (∀ x ∈ U ∩ Metric.ball c r, -laplacian w x ≤ A * w x) →
        w c ≤ C * (r⁻¹ ^ 3 * (∫ x in U ∩ Metric.ball c r, w x) + a) := by
  obtain ⟨C₀, hC₀, hM⟩ := hMean A hA
  let κ := Real.pi * 4 / 3
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  let C := C₀ * max 1 κ
  have hC : 0 < C := mul_pos hC₀ (zero_lt_one.trans_le (le_max_left _ _))
  refine ⟨C, hC, ?_⟩
  intro U hU c hc r hr w a ha hwC hw hI hPos hTrace hLap
  let V := Metric.ball c r
  have hV : IsOpen V := Metric.isOpen_ball
  have hFin : volume V < ⊤ :=
    (measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall c r).measure_lt_top
  have hInd : IntegrableOn (U.indicator w) V volume := by
    apply (integrable_indicator_iff hU.measurableSet).mpr
    change Integrable w ((volume.restrict V).restrict U)
    rw [Measure.restrict_restrict hU.measurableSet]
    exact hI
  have hVol : (volume V).toReal = κ * r ^ 3 := by
    change (volume (Metric.ball c r)).toReal = _
    rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hr.1.le,
      ← ENNReal.ofReal_mul (pow_nonneg hr.1.le 3), ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hr.1.le 3) hκ.le)]
    ring
  have hIpos : 0 ≤ ∫ x in U ∩ Metric.ball c r, w x := by
    apply integral_nonneg_of_ae
    exact (ae_restrict_mem (hU.inter hV).measurableSet).mono hPos
  have hUpper (η : ℝ) (hη : 0 < η) :
      w c ≤ C₀ * (r⁻¹ ^ 3 * (∫ x in U ∩ Metric.ball c r, w x) + κ * (a + 2 * η)) := by
    obtain ⟨f, hf, hF, hFLower, hFUpper⟩ := exists_smooth_capped_subsolution_for_physical_wall
      hU c hA ha hη hwC hw hPos hTrace hLap
    have hEnv : IntegrableOn (fun x => U.indicator w x + (a + 2 * η)) V volume :=
      hInd.add (integrableOn_const hFin.ne)
    have hFI : IntegrableOn f V volume := by
      apply Integrable.mono hEnv (hf.continuousOn.aestronglyMeasurable hV.measurableSet)
      filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      have h0 := (hF x hx).1
      have hUp := hFUpper x hx
      rw [Real.norm_eq_abs, abs_of_nonneg h0, Real.norm_eq_abs,
        abs_of_nonneg (h0.trans hUp)]
      exact hUp
    have hIntegral : (∫ x in V, f x) ≤ (∫ x in U ∩ Metric.ball c r, w x) + κ * r ^ 3 * (a + 2 * η) := by
      have hUp := setIntegral_mono_on hFI hEnv hV.measurableSet hFUpper
      change (∫ x in V, f x) ≤ ∫ x in V, (U.indicator w) x + (a + 2 * η) at hUp
      rw [integral_add hInd (integrableOn_const hFin.ne), setIntegral_indicator hU.measurableSet,
        inter_comm V U, setIntegral_const, smul_eq_mul, show (volume.real V) = κ * r ^ 3 from hVol] at hUp
      exact hUp
    have hCen := hFLower c ⟨hc, Metric.mem_ball_self hr.1⟩
    have hM' := hM c r hr f hf hFI (fun x hx => (hF x hx).1) (fun x hx => (hF x hx).2)
    have hCoef : 0 ≤ C₀ * r⁻¹ ^ 3 := mul_nonneg hC₀.le (pow_nonneg (inv_nonneg.mpr hr.1.le) _)
    calc
      _ ≤ f c := hCen
      _ ≤ C₀ * r⁻¹ ^ 3 * (∫ x in V, f x) := hM'
      _ ≤ C₀ * r⁻¹ ^ 3 * ((∫ x in U ∩ Metric.ball c r, w x) + κ * r ^ 3 * (a + 2 * η)) :=
        mul_le_mul_of_nonneg_left hIntegral hCoef
      _ = _ := by field_simp [hr.1.ne']
  have hExact : w c ≤ C₀ * (r⁻¹ ^ 3 * (∫ x in U ∩ Metric.ball c r, w x) + κ * a) := by
    apply le_of_forall_pos_le_add
    intro d hd
    let η := d / (2 * C₀ * κ)
    have hη : 0 < η := div_pos hd (by positivity)
    have hProd : 2 * C₀ * κ * η = d := by dsimp only [η]; field_simp
    have hh := hUpper η hη
    linarith only [hh, hProd]
  have hA₀ : 0 ≤ r⁻¹ ^ 3 * (∫ x in U ∩ Metric.ball c r, w x) :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr hr.1.le) _) hIpos
  have hIn : r⁻¹ ^ 3 * (∫ x in U ∩ Metric.ball c r, w x) + κ * a ≤
      max 1 κ * (r⁻¹ ^ 3 * (∫ x in U ∩ Metric.ball c r, w x) + a) := by
    rw [mul_add]
    exact add_le_add (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 κ) hA₀)
      (mul_le_mul_of_nonneg_right (le_max_right 1 κ) ha)
  exact hExact.trans ((mul_le_mul_of_nonneg_left hIn hC₀.le).trans_eq (mul_assoc _ _ _).symm)

end Thesis

end
