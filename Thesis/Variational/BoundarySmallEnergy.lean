module

public import Thesis.Variational.BoundaryTube
public import Thesis.External.BoundaryPoisson
import Thesis.Variational.ScaledDefects
import HarmonicMaps.Analysis.AffineBallMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The weighted maximum and radius estimates in boundary small-energy regularity. -/

public section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem boundary_radius_balance
    {C C₀ E δ R L : ℝ} (hC : 0 < C) (hL : 0 ≤ L) (hE : 0 ≤ E) (hR : 0 < R)
    (hInv : C * C₀⁻¹ < 1 / 8)
    (hSmall : E + δ ^ 2 < 1 / 8)
    (hTail : C * ((E + δ ^ 2) ^ (1 / 3 : ℝ) + (E + δ ^ 2) +
      (E + δ ^ 2) ^ (5 / 6 : ℝ) + L * (E + δ ^ 2) ^ (2 / 3 : ℝ)) < 1 / 4)
    (hComp : ∀ r : ℝ, 0 < r → r < R / 10 → r < 1 →
      1 ≤ C * (C₀⁻¹ + (E + δ ^ 2) / r ^ 2 + E + r * Real.sqrt E + L * r ^ 2)) :
    R ^ 2 ≤ 800 * C * (E + δ ^ 2) := by
  let F := E + δ ^ 2
  have hF : 0 ≤ F := add_nonneg hE (sq_nonneg _)
  have hEF : E ≤ F := le_add_of_nonneg_right (sq_nonneg _)
  change R ^ 2 ≤ 800 * C * F
  rcases hF.eq_or_lt with h0 | hFpos
  · let r := min (R / 20) (min (1 / 2) (1 / (1 + 4 * C * L)))
    have hr : 0 < r := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hrR : r < R / 10 := (min_le_left _ _).trans_lt (by linarith only [hR])
    have hr₁ : r < 1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
    have hrM : r ≤ 1 / (1 + 4 * C * L) := (min_le_right _ _).trans (min_le_right _ _)
    have hPL := (le_div_iff₀ (by positivity : 0 < 1 + 4 * C * L)).mp hrM
    have hrL : C * L * r ≤ 1 / 4 := by linarith only [hPL, hr]
    have hrE : C * L * r ^ 2 ≤ 1 / 4 := by
      have h := mul_le_mul_of_nonneg_left hr₁.le (mul_nonneg (mul_nonneg hC.le hL) hr.le)
      nlinarith only [h, hrL]
    have hE0 : E = 0 := le_antisymm (hEF.trans_eq h0.symm) hE
    have h := hComp r hr hrR hr₁
    change 1 ≤ C * (C₀⁻¹ + F / r ^ 2 + E + r * Real.sqrt E + L * r ^ 2) at h
    simp only [← h0, hE0, zero_div, add_zero, Real.sqrt_zero, mul_zero] at h
    linarith only [hInv, h, hrE]
  · let s := F ^ (1 / 3 : ℝ)
    have hs : 0 < s := Real.rpow_pos_of_pos hFpos _
    have hCube : s ^ 3 = F := by
      calc
        _ = s ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast s 3).symm
        _ = F ^ ((1 / 3 : ℝ) * ((3 : ℕ) : ℝ)) := (Real.rpow_mul hF ((1 / 3 : ℝ)) _).symm
        _ = F := by norm_num
    have hsHalf : s < 1 / 2 := by
      by_contra hh
      have hP := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_of_not_gt hh) 3
      rw [hCube] at hP
      linarith only [hP, hSmall]
    have hRatio : F / s ^ 2 = s := by
      apply (div_eq_iff (sq_pos_of_pos hs).ne').mpr
      rw [← hCube]
      ring
    have hProd : s * Real.sqrt F = F ^ (5 / 6 : ℝ) := by
      change F ^ (1 / 3 : ℝ) * Real.sqrt F = _
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hFpos]
      norm_num
    have hSq : s ^ 2 = F ^ (2 / 3 : ℝ) := by
      change (F ^ (1 / 3 : ℝ)) ^ 2 = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul hF]
      norm_num
    have hsTail (r : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) :
        C * (E + r * Real.sqrt E + L * r ^ 2) ≤
          C * (s + F + F ^ (5 / 6 : ℝ) + L * F ^ (2 / 3 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      have hTerm := (mul_le_mul hrs (Real.sqrt_le_sqrt hEF) (Real.sqrt_nonneg _) hs.le)
      rw [hProd] at hTerm
      have hSqBound := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs 2) hL
      rw [hSq] at hSqBound
      linarith only [hEF, hTerm, hs, hSqBound]
    have hRBound : R / 10 ≤ s := by
      by_contra hN
      have hTest := hComp s hs (lt_of_not_ge hN) (hsHalf.trans (by norm_num))
      change 1 ≤ C * (C₀⁻¹ + F / s ^ 2 + E + s * Real.sqrt E + L * s ^ 2) at hTest
      rw [hRatio, hSq] at hTest
      have hTerm := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEF) hs.le) hC.le
      rw [hProd] at hTerm
      have hEt := mul_le_mul_of_nonneg_left hEF hC.le
      change C * (s + F + F ^ (5 / 6 : ℝ) + L * F ^ (2 / 3 : ℝ)) < 1 / 4 at hTail
      linarith only [hTest, hTerm, hEt, hTail, hInv]
    let r := R / 20
    have hr : 0 < r := by dsimp only [r]; positivity
    have hrR : r < R / 10 := by dsimp only [r]; linarith only [hR]
    have hrs : r ≤ s := hrR.le.trans hRBound
    have hTest := hComp r hr hrR (hrs.trans_lt (hsHalf.trans (by norm_num)))
    change 1 ≤ C * (C₀⁻¹ + F / r ^ 2 + E + r * Real.sqrt E + L * r ^ 2) at hTest
    have hRate : F / r ^ 2 = 400 * F / R ^ 2 := by
      dsimp only [r]
      field_simp [hR.ne']
      ring
    rw [hRate] at hTest
    have ht := hsTail r hr.le hrs
    change C * (s + F + F ^ (5 / 6 : ℝ) + L * F ^ (2 / 3 : ℝ)) < 1 / 4 at hTail
    have hKey : (1 / 2 : ℝ) ≤ C * (400 * F / R ^ 2) := by
      linarith only [hTest, ht, hTail, hInv]
    have hKey' : (1 / 2 : ℝ) ≤ (400 * C * F) / R ^ 2 := by
      convert hKey using 1
      ring
    have hFinal := (le_div_iff₀ (sq_pos_of_pos hR)).mp hKey'
    linarith only [hFinal]

/-- The two radius tests absorb a quadratic radius error in the boundary
maximum argument. -/
theorem exists_boundary_smallEnergy_radius_balance_threshold_of_quadratic_error
    {C L : ℝ} (hC : 0 < C) (hL : 0 ≤ L) :
    ∃ C₀ F₀ : ℝ, 1 ≤ C₀ ∧ 0 < F₀ ∧
      ∀ {E δ R : ℝ}, 0 ≤ E → 0 < R → E + δ ^ 2 < F₀ →
        (∀ r : ℝ, 0 < r → r < R / 10 → r < 1 →
          1 ≤ C * (C₀⁻¹ + (E + δ ^ 2) / r ^ 2 + E + r * Real.sqrt E + L * r ^ 2)) →
        R ^ 2 ≤ 800 * C * (E + δ ^ 2) := by
  let C₀ := 8 * C + 1
  have hC₀ : 1 ≤ C₀ := by dsimp only [C₀]; linarith only [hC]
  have hPos : 0 < C₀ := zero_lt_one.trans_le hC₀
  have hInv : C * C₀⁻¹ < 1 / 8 := by
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ hPos).mpr
    dsimp only [C₀]
    linarith
  let p (x : ℝ) := C * (x ^ (1 / 3 : ℝ) + x + x ^ (5 / 6 : ℝ) + L * x ^ (2 / 3 : ℝ))
  have hp : Continuous p := ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 3)).add
    continuous_id |>.add (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 5 / 6)) |>.add
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2 / 3)).const_mul L)).const_mul C
  have hp0 : p 0 < 1 / 4 := by simp only [p, Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0),
    Real.zero_rpow (by norm_num : (5 / 6 : ℝ) ≠ 0),
    Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), add_zero, mul_zero]; norm_num
  have hNear := hp.continuousAt.eventually_lt continuousAt_const hp0
  obtain ⟨B, hB, hBound⟩ := Metric.mem_nhds_iff.mp hNear
  let F₀ := min B (1 / 8)
  refine ⟨C₀, F₀, hC₀, lt_min hB (by norm_num), ?_⟩
  intro E δ R hE hR hF hComp
  have hNear' : E + δ ^ 2 ∈ Metric.ball (0 : ℝ) B := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (add_nonneg hE (sq_nonneg _))]
    exact hF.trans_le (min_le_left _ _)
  exact boundary_radius_balance hC hL hE hR hInv (hF.trans_le (min_le_right _ _)) (hBound hNear') hComp

/-- The source radius bound without an additional quadratic error. -/
theorem exists_boundary_smallEnergy_radius_balance_threshold
    {C : ℝ} (hC : 0 < C) :
    ∃ C₀ F₀ : ℝ, 1 ≤ C₀ ∧ 0 < F₀ ∧
      ∀ {E δ R : ℝ}, 0 ≤ E → 0 < R → E + δ ^ 2 < F₀ →
        (∀ r : ℝ, 0 < r → r < R / 10 → r < 1 →
          1 ≤ C * (C₀⁻¹ + (E + δ ^ 2) / r ^ 2 + E + r * Real.sqrt E)) →
        R ^ 2 ≤ 800 * C * (E + δ ^ 2) := by
  simpa only [zero_mul, add_zero] using
    exists_boundary_smallEnergy_radius_balance_threshold_of_quadratic_error hC (L := 0) (by norm_num)

/-- A nonnegative weighted maximum on the closed cap is attained. If
positive, it controls the energy on the closed half-margin cap at the
maximizer, including its physical-boundary points. -/
theorem exists_boundary_weighted_energy_maximizer
    {U : Set Point} {c : Point} (hc : c ∈ closure U) {r : ℝ} (hr : 0 < r)
    {w : Point → ℝ} (hw : ContinuousOn w (closure U ∩ Metric.closedBall c r))
    {b : ℝ} (hb : 0 ≤ b) :
    let K := closure U ∩ Metric.closedBall c r
    let F (x : Point) := (r - dist x c) ^ 2 * max (w x - b) 0
    ∃ z ∈ K, 0 ≤ F z ∧ IsMaxOn F K z ∧
      (0 < F z → dist z c < r ∧ b < w z ∧
        ∀ y ∈ closure U ∩ Metric.closedBall z ((r - dist z c) / 2), w y ≤ 4 * w z) := by
  let K := closure U ∩ Metric.closedBall c r
  let F (x : Point) := (r - dist x c) ^ 2 * max (w x - b) 0
  have hK : IsCompact K := (isCompact_closedBall c r).inter_left isClosed_closure
  have hNE : K.Nonempty := ⟨c, hc, Metric.mem_closedBall_self hr.le⟩
  have hDist : Continuous (fun x : Point => r - dist x c) :=
    continuous_const.sub (continuous_id.dist continuous_const)
  have hF : ContinuousOn F K :=
    (hDist.continuousOn.pow 2).mul ((hw.sub continuousOn_const).sup continuousOn_const)
  obtain ⟨z, hz, hMax⟩ := hK.exists_isMaxOn hNE hF
  have hNon : 0 ≤ F z := mul_nonneg (sq_nonneg _) (le_max_right _ _)
  refine ⟨z, hz, hNon, hMax, ?_⟩
  intro hp
  have hzDist : dist z c ≤ r := hz.2
  have hMargin : 0 < r - dist z c := by
    rcases (sub_nonneg.mpr hzDist).eq_or_lt with heq | hpos
    · have : F z = 0 := by simp only [F, ← heq, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]
      exact (hp.ne' this).elim
    · exact hpos
  have hwb : b < w z := by
    by_contra hn
    have : F z = 0 := by simp only [F, max_eq_right (sub_nonpos.mpr (le_of_not_gt hn)), mul_zero]
    exact hp.ne' this
  refine ⟨sub_pos.mp hMargin, hwb, ?_⟩
  intro y hy
  have hyDist : dist y z ≤ (r - dist z c) / 2 := hy.2
  have hTriangle := dist_triangle y z c
  have hHalf : (r - dist z c) / 2 ≤ r - dist y c := by linarith only [hyDist, hTriangle]
  have hyK : y ∈ K := ⟨hy.1, Metric.mem_closedBall.mpr (by linarith only [hHalf, hMargin])⟩
  by_cases hwy : w y ≤ b
  · linarith only [hwy, hwb, hb]
  · have hwy' : 0 ≤ w y - b := sub_nonneg.mpr (le_of_not_ge hwy)
    have hMaxY := hMax hyK
    change (r - dist y c) ^ 2 * max (w y - b) 0 ≤ (r - dist z c) ^ 2 * max (w z - b) 0 at hMaxY
    rw [max_eq_left hwy', max_eq_left (sub_pos.mpr hwb).le] at hMaxY
    have hPos : 0 < ((r - dist z c) / 2) ^ 2 := sq_pos_of_pos (half_pos hMargin)
    have hSq := pow_le_pow_left₀ (half_pos hMargin).le hHalf 2
    have hCmp := (mul_le_mul_of_nonneg_right hSq hwy').trans hMaxY
    have hCancel : w y - b ≤ 4 * (w z - b) := (mul_le_mul_iff_right₀ hPos).mp (by
      convert hCmp using 1; ring)
    linarith only [hCancel, hb]

/-- The physical-wall specialization uses the derivative within the actual
closure. Intersecting the derivative set with the outer open ball preserves
that derivative at every point of the smaller cap. -/
theorem exists_physical_wall_poisson_gradient_bound
    (h : External.ZeroTraceBoundaryPoissonL4GradientEstimate)
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧
      ∀ c ∈ frontier U, ∀ r ∈ Ioo 0 R, ∀ (u f : Point → ℝ),
        let D := U ∩ Metric.ball c r
        ContDiffOn ℝ 2 u (closure U ∩ Metric.ball c r) →
        EqOn u (fun _ => 0) (frontier U ∩ Metric.ball c r) →
        (∀ x ∈ D, laplacian u x = f x) →
        MemLp (fderiv ℝ u) 2 (volume.restrict D) →
        MemLp f 4 (volume.restrict D) →
        ∀ x ∈ frontier U ∩ Metric.ball c (r / 2),
          ‖fderivWithin ℝ u (closure U) x‖ ≤
            C * (r ^ (-3 / 2 : ℝ) * (eLpNorm (fderiv ℝ u) 2 (volume.restrict D)).toReal +
              r ^ (1 / 4 : ℝ) * (eLpNorm f 4 (volume.restrict D)).toReal) := by
  obtain ⟨R, C, hR, hC, hBound⟩ := h U hU
  refine ⟨R, C, hR, hC, ?_⟩
  intro c hc r hr u f
  dsimp only
  intro hu ht hf hg hLp x hx
  have hB := hBound c hc r hr u f hu ht hf hg hLp x ⟨frontier_subset_closure hx.1, hx.2⟩
  have hHalf : r / 2 ≤ r := by linarith only [hr.1]
  have hNear : Metric.ball c r ∈ 𝓝 x :=
    Metric.isOpen_ball.mem_nhds ((Metric.ball_subset_ball hHalf) hx.2)
  simpa only [fderivWithin_inter hNear] using hB

/-- A Morrey energy bound for interior centers extends to all centers in
the actual closure, keeping each comparison radius fixed in the limit. -/
theorem morrey_lintegral_bound_at_closure_center
    {U : Set Point} {w : Point → ℝ≥0∞} {c : Point} {R E : ℝ}
    (h : ∀ x ∈ U ∩ Metric.ball c R, ∀ r ∈ Ioo 0 R,
      (∫⁻ y in U ∩ Metric.ball x r, w y) ≤ ENNReal.ofReal (E * r))
    {x : Point} (hx : x ∈ closure U ∩ Metric.ball c R)
    {r : ℝ} (hr : r ∈ Ioo 0 R) :
    (∫⁻ y in U ∩ Metric.ball x r, w y) ≤ ENNReal.ofReal (E * r) := by
  have hLim : Tendsto (fun t : ℝ => ENNReal.ofReal (E * t)) (𝓝[>] r) (𝓝 (ENNReal.ofReal (E * r))) :=
    (ENNReal.tendsto_ofReal (continuous_const.mul continuous_id).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  apply ge_of_tendsto hLim
  have hNear : ∀ᶠ t in 𝓝[>] r, t < R := nhdsWithin_le_nhds (Iio_mem_nhds hr.2)
  have hAbove : ∀ᶠ t in 𝓝[>] r, r < t := self_mem_nhdsWithin
  filter_upwards [hAbove, hNear] with t hrt htR
  have hMargin : 0 < R - dist x c := sub_pos.mpr (Metric.mem_ball.mp hx.2)
  obtain ⟨z, hz, hDist⟩ := Metric.mem_closure_iff.mp hx.1
    (min (t - r) (R - dist x c)) (lt_min (sub_pos.mpr hrt) hMargin)
  have hzMem : z ∈ Metric.ball c R := by
    have hT := dist_triangle z x c
    have hSmall := hDist.trans_le (min_le_right (t - r) (R - dist x c))
    rw [dist_comm x z] at hSmall
    exact Metric.mem_ball.mpr (by linarith only [hT, hSmall])
  have hSub : U ∩ Metric.ball x r ⊆ U ∩ Metric.ball z t := by
    intro y hy
    have hT := dist_triangle y x z
    have hSmall := hDist.trans_le (min_le_left (t - r) (R - dist x c))
    exact ⟨hy.1, Metric.mem_ball.mpr (by linarith only [hT, hSmall, Metric.mem_ball.mp hy.2])⟩
  exact (lintegral_mono_set hSub).trans (h z ⟨hz, hzMem⟩ t ⟨hr.1.trans hrt, htR⟩)

/-- In dimension three a dilation with spatial factor `t` and energy
density factor `t²` preserves normalized energy on the corresponding caps. -/
theorem normalized_lintegral_affine_boundary_cap
    {U : Set Point} (hU : MeasurableSet U) (c : Point)
    {t ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ) (w : Point → ℝ≥0∞) :
    let A (y : Point) := c + t • y
    ENNReal.ofReal (ρ⁻¹) *
        (∫⁻ y in (A ⁻¹' U) ∩ Metric.ball 0 ρ, ENNReal.ofReal (t ^ 2) * w (A y)) =
      ENNReal.ofReal ((t * ρ)⁻¹) * ∫⁻ x in U ∩ Metric.ball c (t * ρ), w x := by
  let A (y : Point) := c + t • y
  let U₁ := A ⁻¹' U
  let g := U.indicator w
  have hA : Measurable A := (continuous_const.add (continuous_id.const_smul t)).measurable
  have hU₁ : MeasurableSet U₁ := hU.preimage hA
  have hG : (fun y => g (A y)) = U₁.indicator (fun y => w (A y)) := by
    funext y
    by_cases hy : A y ∈ U
    · simp only [g, Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ U₁ from hy)]
    · simp only [g, Set.indicator_of_notMem hy, Set.indicator_of_notMem (show y ∉ U₁ from hy)]
  have hI := HarmonicMaps.lintegral_affineBall (n := 3) c (0 : Point) ht (t * ρ) g
  have hRad : (t * ρ) / t = ρ := by field_simp [ht.ne']
  rw [hRad] at hI
  simp only [sub_zero] at hI
  change (∫⁻ y in Metric.ball (0 : Point) ρ, g (A y)) =
    ENNReal.ofReal ((t ^ 3)⁻¹) * ∫⁻ x in Metric.ball c (t * ρ), g x at hI
  rw [hG, lintegral_indicator hU₁, Measure.restrict_restrict hU₁,
    show g = U.indicator w from rfl, lintegral_indicator hU, Measure.restrict_restrict hU] at hI
  change ENNReal.ofReal ρ⁻¹ *
      (∫⁻ y in U₁ ∩ Metric.ball (0 : Point) ρ, ENNReal.ofReal (t ^ 2) * w (A y)) =
    ENNReal.ofReal ((t * ρ)⁻¹) * ∫⁻ x in U ∩ Metric.ball c (t * ρ), w x
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hI, ← mul_assoc, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hρ.le),
    ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hρ.le) (sq_nonneg t))]
  congr 2
  field_simp [ht.ne', hρ.ne']

/-- A spatial affine dilation multiplies each actual derivative column
by its dilation factor. -/
theorem coordDeriv_affine_dilation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : Point → E} (c : Point) (t : ℝ) (y : Point)
    (hu : DifferentiableAt ℝ u (c + t • y)) (i : Fin 3) :
    coordDeriv i (fun z => u (c + t • z)) y = t • coordDeriv i u (c + t • y) := by
  let A (z : Point) := c + t • z
  have hA : HasFDerivAt A (t • ContinuousLinearMap.id ℝ Point) y :=
    ((hasFDerivAt_id y).const_smul t).const_add c
  have hD := hu.hasFDerivAt.comp y hA
  change fderiv ℝ (u ∘ A) y (axis i) = t • fderiv ℝ u (A y) (axis i)
  rw [hD.fderiv, ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul]

/-- The Laplacian of a classical field acquires the square of the spatial
affine dilation factor. -/
theorem laplacian_affine_dilation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Set Point} (hW : IsOpen W) {u : Point → E} (hu : ContDiffOn ℝ 2 u W)
    (c : Point) (t : ℝ) {y : Point} (hy : c + t • y ∈ W) :
    laplacian (fun z => u (c + t • z)) y = t ^ 2 • laplacian u (c + t • y) := by
  let A (z : Point) := c + t • z
  have hA : HasFDerivAt A (t • ContinuousLinearMap.id ℝ Point) y :=
    ((hasFDerivAt_id y).const_smul t).const_add c
  have hNear : ∀ᶠ z in 𝓝 y, A z ∈ W := hA.continuousAt.tendsto (hW.mem_nhds hy)
  unfold laplacian
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hDiNear : (coordDeriv i (u ∘ A)) =ᶠ[𝓝 y] (fun z => t • coordDeriv i u (A z)) := by
    filter_upwards [hNear] with z hz
    exact coordDeriv_affine_dilation c t z
      (((hu (A z) hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by norm_num)) i
  have huAt : ContDiffAt ℝ 2 u (A y) := (hu _ hy).contDiffAt (hW.mem_nhds hy)
  have hDiff := differentiableAt_coordDeriv_of_contDiffAt huAt i
  have hComp := ((hDiff.hasFDerivAt.comp y hA).const_smul t).congr_of_eventuallyEq hDiNear
  change fderiv ℝ (coordDeriv i (u ∘ A)) y (axis i) = t ^ 2 • fderiv ℝ (coordDeriv i u) (A y) (axis i)
  rw [hComp.fderiv, smul_apply, ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_smul, pow_two]

/-- The rescaled equation uses the positive real scale ε / t.
It preserves the same material force when the spatial dilation is t. -/
theorem penalized_eulerLagrange_affine_dilation
    (a : BulkCoefficients) (ε : ElasticScale)
    {W : Set Point} (hW : IsOpen W) {Q : Point → S0} (hQ : ContDiffOn ℝ 2 Q W)
    (hEuler : ∀ x ∈ W, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x))
    (c : Point) {t : ℝ} (ht : 0 < t) {y : Point} (hy : c + t • y ∈ W) :
    ((ε : ℝ) / t) ^ 2 • (↑(laplacian (fun z => Q (c + t • z)) y) : Tensor) =
      bulkGradient a (Q (c + t • y)) := by
  rw [laplacian_affine_dilation hW hQ c t hy]
  change ((ε : ℝ) / t) ^ 2 • (t ^ 2 • (↑(laplacian Q (c + t • y)) : Tensor)) = _
  rw [smul_smul, ← mul_pow, div_mul_cancel₀ _ ht.ne']
  exact hEuler _ hy

/-- The literal rescaled classical energy density is multiplied by the
square of the spatial factor, with the same bulk potential. -/
theorem penalized_energyDensity_affine_dilation
    (a : BulkCoefficients) (ε : ElasticScale) {Q : Point → S0} (c : Point)
    {t : ℝ} (ht : 0 < t) {y : Point} (hQ : DifferentiableAt ℝ Q (c + t • y)) :
    (1 / 2 : ℝ) * gradientNormSq (ClassicalGradient (fun z => Q (c + t • z)) y) +
        (((ε : ℝ) / t)⁻¹) ^ 2 * bulkPotential a (Q (c + t • y)) =
      t ^ 2 * energyDensity a ε (Q (c + t • y)) (ClassicalGradient Q (c + t • y)) := by
  have hGrad : gradientNormSq (ClassicalGradient (fun z => Q (c + t • z)) y) =
      t ^ 2 * gradientNormSq (ClassicalGradient Q (c + t • y)) := by
    simp only [gradientNormSq_eq_sum_norm_sq, ClassicalGradient, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coordDeriv_affine_dilation c t y hQ, norm_smul, Real.norm_of_nonneg ht.le, mul_pow]
  rw [hGrad, energyDensity, inv_div]
  have hScale : (t / (ε : ℝ)) ^ 2 = t ^ 2 * (ε : ℝ)⁻¹ ^ 2 := by rw [div_eq_mul_inv, mul_pow]
  rw [hScale]
  ring

end Thesis

end
