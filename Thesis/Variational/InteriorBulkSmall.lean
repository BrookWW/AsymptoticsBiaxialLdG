module

public import Thesis.Variational.BoundaryEnergy
public import Thesis.Variational.Pohozaev
public import Thesis.External.SubsolutionMeanValue
public import Thesis.Foundation.VacuumTube
import Thesis.Variational.BoundaryPoissonEstimate
import Thesis.Variational.BoundarySmallEnergy
import Thesis.Variational.EnergyEstimate
import Thesis.Interpolation.PenalizedEdge

/-! Compact interior convergence of the bulk potential for strongly convergent
penalized solutions away from the limiting singularities. -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal NNReal Matrix.Norms.Frobenius

noncomputable section

namespace Thesis

private theorem normalizedEnergy_ball_eq_ofReal_div (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    {x : Point} {r : ℝ} (hr : 0 < r) (hBall : closedBall x r ⊆ Ω) :
    ENNReal.ofReal r⁻¹ * energy a ε (ball x r) Q (ClassicalGradient Q) =
      ENNReal.ofReal ((energy a ε (ball x r) Q (ClassicalGradient Q)).toReal / r) := by
  have hI := integrableOn_classicalEnergyDensity_ball a ε hΩ hQ hBall
  have hE : energy a ε (ball x r) Q (ClassicalGradient Q) ≠ ⊤ := by
    unfold energy
    rw [← ofReal_integral_eq_lintegral_ofReal hI
      (Eventually.of_forall fun y => energyDensity_nonneg a ε (Q y) (ClassicalGradient Q y))]
    exact ENNReal.ofReal_ne_top
  rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hr.le), ENNReal.ofReal_toReal hE]

/-- A single comparison radius works at every point of a compact regular
interior set. Interior monotonicity propagates the energy bound to all smaller
radii. -/
theorem exists_interior_uniform_small_normalized_energy (a : BulkCoefficients)
    {Ω K : Set Point} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKsub : K ⊆ Ω)
    {q : Point → S0} (hq : ContDiffOn ℝ 2 q Ω)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0)
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω)
    (hEuler : ∀ n x, x ∈ Ω → (ε n : ℝ) ^ 2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x))
    (hStrong : StrongH1Loc Ω Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q))
    (hBulkLp : ∀ W, IsOpen W → CompactlyContained W Ω → ∀ n,
      MemLp (fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n x)) 1 (volume.restrict W))
    (hBulk : ∀ W, IsOpen W → CompactlyContained W Ω →
      Tendsto (fun n => eLpNorm (fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n x))
        1 (volume.restrict W)) atTop (𝓝 0))
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ R > (0 : ℝ), (∀ x ∈ K, closedBall x R ⊆ Ω) ∧ ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ s ∈ Ioc 0 R,
        ENNReal.ofReal s⁻¹ * energy a (ε n) (ball x s) (Q n) (ClassicalGradient (Q n)) < ENNReal.ofReal τ := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKsub
  let W := thickening δ K
  have hClosure : closure W ⊆ cthickening δ K := closure_thickening_subset_cthickening δ K
  have hWΩ : CompactlyContained W Ω := ⟨hK.cthickening.of_isClosed_subset isClosed_closure hClosure,
    hClosure.trans hδΩ⟩
  have hKW : K ⊆ W := self_subset_thickening hδ K
  have hW := hStrong W isOpen_thickening hWΩ
  obtain ⟨R₀, M, hR₀, hM, hB⟩ := exists_boundary_collar_base_radius_bound
    (Ω := W) isOpen_thickening hΩ (hq.mono inter_subset_right) hK
    (fun x hx => ⟨subset_closure (hKW hx), hKsub hx⟩) hW.2.1.2.1 EventuallyEq.rfl
  let J := (M / 2) * (Real.pi * 4 / 3)
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hJlim : Tendsto (fun t : ℝ => J * t ^ 2) (𝓝 0) (𝓝 0) := by
    have hC : ContinuousAt (fun t : ℝ => J * t ^ 2) 0 := by fun_prop
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using hC.tendsto
  obtain ⟨ρ, hρ, hρJ⟩ := Metric.mem_nhds_iff.mp (hJlim (Iio_mem_nhds (by positivity : 0 < τ / 3)))
  let R := min ρ (min δ R₀) / 2
  have hMin : 0 < min ρ (min δ R₀) := lt_min hρ (lt_min hδ hR₀)
  have hR : 0 < R := half_pos hMin
  have hRρ : R < ρ := (half_lt_self hMin).trans_le (min_le_left _ _)
  have hRδ : R < δ := (half_lt_self hMin).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hRR₀ : R < R₀ := (half_lt_self hMin).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hJR : J * R ^ 2 < τ / 3 := hρJ (by simpa [Real.dist_eq, abs_of_pos hR] using hRρ)
  have hBall (x : Point) (hx : x ∈ K) : closedBall x R ⊆ W :=
    (closedBall_subset_cthickening hx R).trans (cthickening_subset_thickening' hδ hRδ K)
  have hDef := tendsto_energyDensityDefect_zero_of_strongH1 a ε hW
    (hBulkLp W isOpen_thickening hWΩ) (hBulk W isOpen_thickening hWΩ)
  have hThreshold : 0 < ENNReal.ofReal (R * (τ / 3)) := by positivity
  refine ⟨R, hR, fun x hx => (hBall x hx).trans (subset_closure.trans hWΩ.2), ?_⟩
  filter_upwards [hDef (Iio_mem_nhds hThreshold)] with n hN x hx s hs
  have hWball := hBall x hx
  have hΩball := hWball.trans (subset_closure.trans hWΩ.2)
  have hSub := Metric.ball_subset_closedBall.trans hWball
  have hBase := hB x hx R ⟨hR, hRR₀⟩ a (ε n) (Q n) (ClassicalGradient (Q n))
  rw [inter_eq_right.mpr hSub] at hBase
  have hFactor : ENNReal.ofReal R⁻¹ * ENNReal.ofReal (R * (τ / 3)) = ENNReal.ofReal (τ / 3) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hR.le), ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  have hNle : ENNReal.ofReal R⁻¹ * energyDensityDefect a (ε n) W (Q n) (ClassicalGradient (Q n))
      (ClassicalGradient q) ≤ ENNReal.ofReal (τ / 3) :=
    (mul_le_mul_right (show _ ≤ ENNReal.ofReal (R * (τ / 3)) from hN.le) _).trans_eq hFactor
  have hMono := normalized_classicalBallEnergy_monotoneOn a (ε n) hΩ (hQ n) (hEuler n) hR hΩball
  have hsΩ := (closedBall_subset_closedBall hs.2).trans hΩball
  calc
    _ ≤ ENNReal.ofReal R⁻¹ * energy a (ε n) (ball x R) (Q n) (ClassicalGradient (Q n)) := by
      rw [normalizedEnergy_ball_eq_ofReal_div a (ε n) hΩ (hQ n) hs.1 hsΩ,
        normalizedEnergy_ball_eq_ofReal_div a (ε n) hΩ (hQ n) hR hΩball]
      exact ENNReal.ofReal_le_ofReal (hMono hs ⟨hR, le_rfl⟩ hs.2)
    _ ≤ ENNReal.ofReal (τ / 3) + ENNReal.ofReal (τ / 3) :=
      hBase.trans (add_le_add hNle (ENNReal.ofReal_le_ofReal hJR.le))
    _ < _ := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ τ / 3) (by positivity : 0 ≤ τ / 3)]
      exact (ENNReal.ofReal_lt_ofReal_iff hτ).mpr (by linarith)

local instance interiorFieldDerivativeNorm : Norm (Point →L[ℝ] S0) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ) (E := Point) (F := S0)

/-- The scale times the bulk potential is uniformly Lipschitz on each interior
ball controlled by the same range and scaled gradient bounds. -/
theorem exists_lipschitzOnWith_scaledBulkPotential_on_ball (a : BulkCoefficients)
    (M : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ L : ℝ≥0, ∀ (ε : ElasticScale) (Q : Point → S0) (x : Point) (R : ℝ),
      ContDiffOn ℝ 1 Q (ball x R) →
      (∀ y ∈ ball x R, ‖Q y‖ ≤ M) →
      (∀ y ∈ ball x R, (ε : ℝ) * Real.sqrt (gradientNormSq (ClassicalGradient Q y)) ≤ B) →
      LipschitzOnWith L (fun y => (ε : ℝ) * bulkPotential a (Q y)) (ball x R) := by
  obtain ⟨L₀, hL₀⟩ := (contDiff_bulkPotential a).contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : S0) M) (isCompact_closedBall _ _)
  refine ⟨L₀ * ⟨B, hB⟩, ?_⟩
  intro ε Q x R hQ hRange hGrad
  have hε := ε.property.1
  let N : ℝ≥0 := ⟨B / (ε : ℝ), div_nonneg hB hε.le⟩
  have hLip : LipschitzOnWith N Q (ball x R) := by
    apply (convex_ball x R).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y hy => ((hQ y hy).contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
    intro y hy
    change ‖fderiv ℝ Q y‖ ≤ B / (ε : ℝ)
    apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hB hε.le)
    intro z
    have hz := norm_gradientFromColumns_le (ClassicalGradient Q y) z
    rw [gradientFromColumns_classicalGradient, mul_comm ‖z‖] at hz
    exact hz.trans (mul_le_mul_of_nonneg_right ((le_div_iff₀ hε).2
      ((mul_comm _ _).trans_le (hGrad y hy))) (norm_nonneg _))
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  have hF := hL₀.dist_le_mul (Q y) (mem_closedBall_zero_iff.mpr (hRange y hy))
    (Q z) (mem_closedBall_zero_iff.mpr (hRange z hz))
  have hProd := hLip.dist_le_mul y hy z hz
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hε]
  rw [Real.dist_eq] at hF
  calc
    _ ≤ (ε : ℝ) * ((L₀ : ℝ) * dist (Q y) (Q z)) := mul_le_mul_of_nonneg_left hF hε.le
    _ ≤ (ε : ℝ) * ((L₀ : ℝ) * ((N : ℝ) * dist y z)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hProd L₀.2) hε.le
    _ = _ := by
      change (ε : ℝ) * ((L₀ : ℝ) * ((B / (ε : ℝ)) * dist y z)) = ((L₀ : ℝ) * B) * dist y z
      field_simp

/-- A fixed positive bulk peak forces a positive lower bound for the
normalized energy on a ball whose radius is proportional to the elastic scale. -/
theorem normalized_energy_microscopic_ball_lower_of_interior_bulk_peak
    (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0) (x : Point)
    {L : ℝ≥0} {R d : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hLip : LipschitzOnWith L (fun y => (ε : ℝ) * bulkPotential a (Q y)) (ball x R))
    (hPeak : d ≤ bulkPotential a (Q x)) :
    let c := d / (2 * ((L : ℝ) + 1))
    let r := c * (ε : ℝ)
    r ≤ R → ENNReal.ofReal ((d / 2) * (Real.pi * 4 / 3) * c ^ 2) ≤
      ENNReal.ofReal r⁻¹ * energy a ε (ball x r) Q (ClassicalGradient Q) := by
  let c := d / (2 * ((L : ℝ) + 1))
  let r := c * (ε : ℝ)
  let b := (ε : ℝ)⁻¹ ^ 2 * (d / 2)
  change r ≤ R → ENNReal.ofReal ((d / 2) * (Real.pi * 4 / 3) * c ^ 2) ≤
    ENNReal.ofReal r⁻¹ * energy a ε (ball x r) Q (ClassicalGradient Q)
  intro hrR
  have hε := ε.property.1
  have hc : 0 < c := by dsimp only [c]; positivity
  have hr : 0 < r := mul_pos hc hε
  have hb : 0 ≤ b := mul_nonneg (sq_nonneg _) (half_pos hd).le
  have hLow (y : Point) (hy : y ∈ ball x r) : d / 2 ≤ bulkPotential a (Q y) := by
    have hDist := hLip.dist_le_mul y (ball_subset_ball hrR hy) x (mem_ball_self hR)
    rw [Real.dist_eq] at hDist
    have hC : ((L : ℝ) + 1) * r = (ε : ℝ) * (d / 2) := by
      dsimp only [r, c]
      field_simp
    have hLR := (mul_le_mul (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1))
      (mem_ball.mp hy).le dist_nonneg (by positivity : 0 ≤ (L : ℝ) + 1)).trans_eq hC
    have hOsc := (neg_le_neg (hDist.trans hLR)).trans
      (neg_abs_le ((ε : ℝ) * bulkPotential a (Q y) - (ε : ℝ) * bulkPotential a (Q x)))
    apply (mul_le_mul_iff_right₀ hε).mp
    linarith only [hOsc, mul_le_mul_of_nonneg_left hPeak hε.le]
  have hElow : ENNReal.ofReal b * volume (ball x r) ≤
      energy a ε (ball x r) Q (ClassicalGradient Q) := by
    rw [energy, ← Measure.restrict_apply_univ, ← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
    apply ENNReal.ofReal_le_ofReal
    unfold energyDensity
    rw [gradientNormSq_eq_sum_norm_sq]
    exact (mul_le_mul_of_nonneg_left (hLow y hy) (sq_nonneg _)).trans
      (le_add_of_nonneg_left (by positivity))
  calc
    ENNReal.ofReal ((d / 2) * (Real.pi * 4 / 3) * c ^ 2) =
        ENNReal.ofReal r⁻¹ * (ENNReal.ofReal b * volume (ball x r)) := by
      rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hr.le,
        ← ENNReal.ofReal_mul (pow_nonneg hr.le 3), ← ENNReal.ofReal_mul hb,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
      congr 1
      dsimp only [r, b]
      field_simp [hc.ne', hε.ne']
    _ ≤ _ := mul_le_mul_right hElow _

/-- Uniform convergence of the actual bulk potential to zero on compact
regular interior sets. The elastic solutions also approach the vacuum
uniformly there. -/
theorem eventually_uniform_interior_bulk_and_vacuum_small
    (a : BulkCoefficients) {Ω K : Set Point} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKsub : K ⊆ Ω)
    (hEstimate : InteriorPoissonGradientEstimate) {M : ℝ}
    {q : Point → S0} (hq : ContDiffOn ℝ 2 q Ω)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω)
    (hEuler : ∀ n x, x ∈ Ω → (ε n : ℝ) ^ 2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x))
    (hBound : ∀ n x, x ∈ Ω → ‖Q n x‖ ≤ max 0 M)
    (hStrong : StrongH1Loc Ω Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q))
    (hBulkLp : ∀ W, IsOpen W → CompactlyContained W Ω → ∀ n,
      MemLp (fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n x)) 1 (volume.restrict W))
    (hBulk : ∀ W, IsOpen W → CompactlyContained W Ω →
      Tendsto (fun n => eLpNorm (fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n x))
        1 (volume.restrict W)) atTop (𝓝 0)) :
    (∀ d : ℝ, 0 < d → ∀ᶠ n in atTop, ∀ x ∈ K, bulkPotential a (Q n x) < d) ∧
    (∀ d : ℝ, 0 < d → ∀ᶠ n in atTop, ∀ x ∈ K, infDist (Q n x) (vacuum a) < d) := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKsub
  have hKδ : CompactlyContained (cthickening δ K) Ω := by
    rw [CompactlyContained, isClosed_cthickening.closure_eq]
    exact ⟨hK.cthickening, hδΩ⟩
  obtain ⟨B, hB, hScaled⟩ := exists_uniform_scaledGradient_bound a hΩ hKδ hEstimate M
  obtain ⟨L, hLip⟩ := exists_lipschitzOnWith_scaledBulkPotential_on_ball a (max 0 M) hB.le
  have hVac : ∀ d : ℝ, 0 < d → ∀ᶠ n in atTop, ∀ x ∈ K, bulkPotential a (Q n x) < d := by
    intro d hd
    let c := d / (2 * ((L : ℝ) + 1))
    let τ := (d / 2) * (Real.pi * 4 / 3) * c ^ 2
    have hc : 0 < c := by dsimp only [c]; positivity
    have hτ : 0 < τ := by dsimp only [τ]; positivity
    obtain ⟨R, hR, _, hEnergy⟩ := exists_interior_uniform_small_normalized_energy a hΩ hK hKsub hq ε Q
      hQ hEuler hStrong hBulkLp hBulk τ hτ
    have hRad : Tendsto (fun n => c * (ε n : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hε
    filter_upwards [hEnergy, hRad (Iio_mem_nhds (lt_min hR hδ))] with n hn hm x hx
    by_contra! hPeak
    have hCell := (ball_subset_closedBall (x := x) (ε := δ)).trans (closedBall_subset_cthickening hx δ)
    have hL := hLip (ε n) (Q n) x δ (((contDiffOn_infty.mp (hQ n)) 1).mono (hCell.trans hδΩ))
      (fun y hy => hBound n y (hδΩ (hCell hy)))
      (fun y hy => hScaled (ε n) (Q n) (hQ n) (hBound n) (hEuler n) y (hCell hy))
    have hLower := normalized_energy_microscopic_ball_lower_of_interior_bulk_peak a (ε n) (Q n) x
      hδ hd hL hPeak (hm.le.trans (min_le_right _ _))
    exact not_lt_of_ge hLower (hn x hx _ ⟨mul_pos hc (ε n).2.1, hm.le.trans (min_le_left _ _)⟩)
  refine ⟨hVac, ?_⟩
  obtain ⟨C, hC, hDistance⟩ := vacuumDistance_sq_le_bulkPotential_of_norm_le a (max 0 M)
  intro d hd
  filter_upwards [hVac (d ^ 2 / C) (div_pos (sq_pos_of_pos hd) hC)] with n hn x hx
  have hQrange := hBound n x (hKsub hx)
  have hUp := hDistance (Q n x) hQrange
  have hCancel : C * (d ^ 2 / C) = d ^ 2 := by field_simp
  have hDown := (mul_lt_mul_of_pos_left (hn x hx) hC).trans_eq hCancel
  exact (sq_lt_sq₀ infDist_nonneg hd.le).mp (hUp.trans_lt hDown)

private theorem energy_at_normalized_interior_peak
    (hMean : External.ClassicalScalarSubsolutionMeanValue) {A : ℝ} (hA : 0 ≤ A) :
    ∃ H > (0 : ℝ), ∀ {Ω : Set Point}, IsOpen Ω → ∀ {w : Point → ℝ},
      ContDiffOn ℝ 2 w Ω → ∀ {z : Point} {t : ℝ}, 0 < t →
      closedBall z t ⊆ Ω → t ^ 2 * w z = 1 →
      (∀ x ∈ Ω, 0 ≤ w x) →
      (∀ x ∈ Ω, -laplacian w x ≤ A * (w x) ^ 2) →
      (∀ x ∈ ball z t, w x ≤ 4 * w z) →
      let g (y : Point) := t ^ 2 * w (z + t • y)
      1 ≤ H * ∫ y in ball (0 : Point) 1, g y := by
  obtain ⟨H, hH, hMV⟩ := hMean (4 * A) (by positivity)
  refine ⟨H, hH, ?_⟩
  intro Ω hΩ w hw z t ht hBall hNorm hPos hQuad hBound
  let Z (y : Point) := z + t • y
  let g (y : Point) := t ^ 2 * w (Z y)
  let V := ball (0 : Point) 1
  have hZd : ContDiff ℝ 2 Z := contDiff_const.add (contDiff_id.const_smul t)
  have hDist (y : Point) : dist (Z y) z = t * ‖y‖ := by
    rw [dist_eq_norm, show Z y - z = t • y from add_sub_cancel_left _ _,
      norm_smul, Real.norm_of_nonneg ht.le]
  have hMapC : MapsTo Z (closedBall 0 1) Ω := fun y hy => hBall (by
    rw [mem_closedBall, hDist]
    have hy' : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hy' ht.le)
  have hMapV : MapsTo Z V (ball z t) := fun y hy => by
    rw [mem_ball, hDist]
    have hy' : ‖y‖ < 1 := by simpa only [V, mem_ball, dist_zero_right] using hy
    simpa only [mul_one] using mul_lt_mul_of_pos_left hy' ht
  have hG : ContDiffOn ℝ 2 (w ∘ Z) V :=
    hw.comp hZd.contDiffOn (fun y hy => hMapC (ball_subset_closedBall hy))
  have hG' : ContDiffOn ℝ 2 g V := by
    simpa only [g, Function.comp_apply, smul_eq_mul] using hG.const_smul (t ^ 2)
  have hGC : ContinuousOn g (closedBall 0 1) :=
    (hw.continuousOn.comp hZd.continuous.continuousOn hMapC).const_mul _
  have hI : IntegrableOn g V volume :=
    (hGC.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hN (y : Point) (hy : y ∈ V) : 0 ≤ g y := mul_nonneg (sq_nonneg t)
    (hPos (Z y) (hMapC (ball_subset_closedBall hy)))
  have hL (y : Point) (hy : y ∈ V) : -laplacian g y ≤ (4 * A) * g y := by
    have hy' := hMapC (ball_subset_closedBall hy)
    have hLap : laplacian g y = t ^ 4 * laplacian w (Z y) := by
      change laplacian (fun x => t ^ 2 • (w ∘ Z) x) y = _
      rw [laplacian_const_smul isOpen_ball hG hy]
      have hD : laplacian (w ∘ Z) y = t ^ 2 • laplacian w (Z y) :=
        laplacian_affine_dilation hΩ hw z t hy'
      rw [hD, smul_eq_mul, smul_eq_mul]
      ring
    have hL' : -laplacian g y ≤ A * (g y) ^ 2 := by
      rw [hLap]
      dsimp only [g]
      nlinarith only [mul_le_mul_of_nonneg_left (hQuad (Z y) hy') (pow_nonneg ht.le 4)]
    have hUp : g y ≤ 4 := by
      dsimp only [g]
      nlinarith only [hNorm, mul_le_mul_of_nonneg_left (hBound (Z y) (hMapV hy)) (sq_nonneg t)]
    have hLin := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hUp (hN y hy)) hA
    exact hL'.trans (by nlinarith only [hLin])
  have hG0 : g 0 = 1 := by simpa only [g, Z, smul_zero, add_zero] using hNorm
  have hMV' := hMV 0 1 ⟨zero_lt_one, le_rfl⟩ g hG' hI hN hL
  simpa only [hG0, inv_one, one_pow, mul_one] using hMV'

private theorem interior_peak_normalized_energy_le_four
    (a : BulkCoefficients) (ε : ElasticScale) {c z : Point} {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (ht' : t ≤ r / 4) (hz : z ∈ ball c (3 * r / 4)) {Q : Point → S0}
    (hQ : ContDiffOn ℝ ∞ Q (ball c r))
    (hEuler : ∀ x ∈ ball c r, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x)) :
    let e (x : Point) := energyDensity a ε (Q x) (ClassicalGradient Q x)
    ENNReal.ofReal (∫ y in ball (0 : Point) 1, t ^ 2 * e (z + t • y)) ≤
      4 * (ENNReal.ofReal r⁻¹ * energy a ε (ball c r) Q (ClassicalGradient Q)) := by
  let U := ball c r
  let Z (y : Point) := z + t • y
  let e (x : Point) := energyDensity a ε (Q x) (ClassicalGradient Q x)
  let g (y : Point) := t ^ 2 * e (Z y)
  have hBall : closedBall z (r / 4) ⊆ U := fun x hx => by
    apply mem_ball.mpr
    linarith only [mem_closedBall.mp hx, mem_ball.mp hz, dist_triangle x z c]
  have hdt (y : Point) : dist (Z y) z = t * ‖y‖ := by
    rw [dist_eq_norm, show Z y - z = t • y from add_sub_cancel_left _ _,
      norm_smul, Real.norm_of_nonneg ht.le]
  have hZ : MapsTo Z (closedBall 0 1) U := fun y hy =>
    hBall (mem_closedBall.mpr (by
      have hy' : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
      rw [hdt]
      exact (mul_le_mul_of_nonneg_left hy' ht.le).trans (by simpa only [mul_one] using ht')))
  have hZd : ContDiff ℝ 2 Z := contDiff_const.add (contDiff_id.const_smul t)
  have hGc : ContinuousOn g (closedBall 0 1) :=
    (((contDiffOn_classicalEnergyDensity a ε isOpen_ball hQ).continuousOn.comp hZd.continuous.continuousOn hZ).const_mul _)
  have hI : IntegrableOn g (ball (0 : Point) 1) volume :=
    (hGc.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hGpos (y : Point) : 0 ≤ g y :=
    mul_nonneg (sq_nonneg t) (energyDensity_nonneg a ε _ _)
  have hScale : ENNReal.ofReal (∫ y in ball (0 : Point) 1, g y) =
      ENNReal.ofReal t⁻¹ * energy a ε (ball z t) Q (ClassicalGradient Q) := by
    rw [ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hGpos)]
    have hJ := normalized_lintegral_affine_boundary_cap (U := univ) MeasurableSet.univ z
      ht zero_lt_one (fun y => ENNReal.ofReal (e y))
    simpa only [preimage_univ, univ_inter, inv_one, ENNReal.ofReal_one, one_mul, mul_one,
      ← ENNReal.ofReal_mul (sq_nonneg t), g, Z, e, energy] using hJ
  have hR : 0 < r / 4 := by positivity
  have hMono := normalized_classicalBallEnergy_monotoneOn a ε isOpen_ball hQ hEuler hR hBall
  have htU := (closedBall_subset_closedBall ht').trans hBall
  change ENNReal.ofReal (∫ y in ball (0 : Point) 1, g y) ≤ _
  rw [hScale]
  calc
    _ ≤ ENNReal.ofReal (r / 4)⁻¹ * energy a ε (ball z (r / 4)) Q (ClassicalGradient Q) := by
      rw [normalizedEnergy_ball_eq_ofReal_div a ε isOpen_ball hQ ht htU,
        normalizedEnergy_ball_eq_ofReal_div a ε isOpen_ball hQ hR hBall]
      exact ENNReal.ofReal_le_ofReal (hMono ⟨ht, ht'⟩ ⟨hR, le_rfl⟩ ht')
    _ ≤ ENNReal.ofReal (r / 4)⁻¹ * energy a ε (ball c r) Q (ClassicalGradient Q) :=
      mul_le_mul_right (lintegral_mono' (Measure.restrict_mono_set _
        (ball_subset_closedBall.trans hBall)) le_rfl) _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_ofNat (n := 4), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      congr 2
      field_simp

/-- Small normalized interior energy and membership in the fixed vacuum tube
give the scale-invariant energy-density bound on the half-radius ball. -/
theorem exists_interior_smallEnergy_density_bound (a : BulkCoefficients)
    (hMean : External.ClassicalScalarSubsolutionMeanValue) :
    ∃ δ E₀ : ℝ, 0 < δ ∧ 0 < E₀ ∧
      ∀ (ε : ElasticScale) (c : Point) (r : ℝ), 0 < r →
        ∀ Q : Point → S0, ContDiffOn ℝ ∞ Q (ball c r) →
          (∀ x ∈ ball c r, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x)) →
          (∀ x ∈ ball c r, Q x ∈ vacuumTube a δ) →
          ENNReal.ofReal r⁻¹ * energy a ε (ball c r) Q (ClassicalGradient Q) < ENNReal.ofReal E₀ →
          ∀ x ∈ ball c (r / 2), r ^ 2 * energyDensity a ε (Q x) (ClassicalGradient Q x) ≤ 256 := by
  obtain ⟨δ, A, hδ, hA, hBochner⟩ := exists_near_vacuum_classicalEnergyDensity_bochner_bound a
  obtain ⟨H, hH, hPeak⟩ := energy_at_normalized_interior_peak hMean hA.le
  let E₀ := (8 * H)⁻¹
  have hE₀ : 0 < E₀ := inv_pos.mpr (by positivity)
  refine ⟨δ, E₀, hδ, hE₀, ?_⟩
  intro ε c r hr Q hQ hEq hTube hE x hx
  let U := ball c r
  let w (x : Point) := energyDensity a ε (Q x) (ClassicalGradient Q x)
  let R := 3 * r / 4
  have hR : 0 < R := by dsimp only [R]; positivity
  have hRr : R < r := by dsimp only [R]; linarith
  have hRsub : closedBall c R ⊆ U := fun y hy => mem_ball.mpr ((mem_closedBall.mp hy).trans_lt hRr)
  have hw := contDiffOn_classicalEnergyDensity a ε isOpen_ball hQ
  have hw₂ := (contDiffOn_infty.mp hw) 2
  have hwc : ContinuousOn w (closure (univ : Set Point) ∩ closedBall c R) :=
    hw.continuousOn.mono (fun y hy => hRsub hy.2)
  obtain ⟨z, hz, _, hMax, hMaxLocal⟩ := exists_boundary_weighted_energy_maximizer
    (U := univ) (show c ∈ closure (univ : Set Point) by simp) hR hwc (b := 0) le_rfl
  let m := (R - dist z c) ^ 2 * w z
  have hwPos (y : Point) : 0 ≤ w y := energyDensity_nonneg a ε _ _
  simp only [sub_zero, max_eq_left (hwPos _)] at hMaxLocal hMax
  have hm : m ≤ 16 := by
    by_contra! hBig
    obtain ⟨hzR, hα, hLocal⟩ := hMaxLocal (show 0 < m from (by norm_num : (0 : ℝ) < 16).trans hBig)
    let α := w z
    let t := (Real.sqrt α)⁻¹
    have hα' : 0 < α := hα
    have hsqrt : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα'
    have ht : 0 < t := inv_pos.mpr hsqrt
    have hNorm : t ^ 2 * w z = 1 := by
      change ((Real.sqrt α)⁻¹) ^ 2 * α = 1
      rw [inv_pow, Real.sq_sqrt hα'.le, inv_mul_cancel₀ hα'.ne']
    have hMargin : 0 < R - dist z c := sub_pos.mpr hzR
    have hGeom : 4 * t < R - dist z c := by
      have hM' : (4 : ℝ) ^ 2 < ((R - dist z c) * Real.sqrt α) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hα'.le]
        norm_num
        exact hBig
      have h := (sq_lt_sq₀ (by norm_num) (mul_nonneg hMargin.le hsqrt.le)).mp hM'
      change 4 * (Real.sqrt α)⁻¹ < _
      rwa [← div_eq_mul_inv, div_lt_iff₀ hsqrt]
    have ht' : t ≤ r / 4 := by
      dsimp only [R] at hGeom
      linarith only [hGeom, dist_nonneg (x := z) (y := c), hr]
    have hz' : z ∈ ball c (3 * r / 4) := hzR
    have hBall : closedBall z t ⊆ U := fun y hy => mem_ball.mpr (by
      dsimp only [R] at hzR
      linarith only [hzR, ht', mem_closedBall.mp hy, dist_triangle y z c])
    have htMargin : t ≤ (R - dist z c) / 2 := by linarith only [hGeom, ht]
    have hLocal' (y : Point) (hy : y ∈ ball z t) : w y ≤ 4 * w z :=
      hLocal y ⟨by simp, (closedBall_subset_closedBall htMargin) (ball_subset_closedBall hy)⟩
    have hMean' := hPeak isOpen_ball hw₂ ht hBall hNorm (fun y _ => hwPos y)
      (fun y hy => hBochner ε U isOpen_ball Q hQ hEq y hy (hTube y hy)) hLocal'
    have hBound := (interior_peak_normalized_energy_le_four a ε hr ht ht' hz' hQ hEq).trans
      (mul_le_mul_right hE.le 4)
    rw [← ENNReal.ofReal_ofNat (n := 4), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)] at hBound
    have hInt := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 4 * E₀)).mp hBound
    have hContr := mul_le_mul_of_nonneg_left hInt hH.le
    have hHalf : H * (4 * E₀) = 1 / 2 := by dsimp only [E₀]; field_simp; norm_num
    rw [hHalf] at hContr
    exact (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2) (hMean'.trans hContr)
  have hxR : x ∈ closedBall c R := mem_closedBall.mpr (by
    have h := mem_ball.mp hx
    dsimp only [R]
    linarith)
  have hMargin : r / 4 ≤ R - dist x c := by
    have h := mem_ball.mp hx
    dsimp only [R]
    linarith
  have hP := (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : 0 ≤ r / 4)
    hMargin 2) (hwPos x)).trans ((hMax ⟨by simp, hxR⟩).trans hm)
  change r ^ 2 * w x ≤ _
  nlinarith only [hP]

/-- The classical energy densities of the strongly convergent sequence are
uniformly bounded on every compact regular interior set. -/
theorem exists_uniform_interior_energyDensity_bound
    (a : BulkCoefficients) {Ω K : Set Point} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKsub : K ⊆ Ω)
    (hEstimate : InteriorPoissonGradientEstimate) (hMean : External.ClassicalScalarSubsolutionMeanValue)
    {M : ℝ} {q : Point → S0} (hq : ContDiffOn ℝ 2 q Ω)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω)
    (hEuler : ∀ n x, x ∈ Ω → (ε n : ℝ) ^ 2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x))
    (hBound : ∀ n x, x ∈ Ω → ‖Q n x‖ ≤ max 0 M)
    (hStrong : StrongH1Loc Ω Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q))
    (hBulk : ConvergesScaledPotentialLoc a Ω ε Q) :
    ∃ C > (0 : ℝ), ∀ n x, x ∈ K → energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ C := by
  classical
  let w (n : ℕ) (x : Point) := energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x)
  obtain ⟨δ, E₀, hδ, hE₀, hSmall⟩ := exists_interior_smallEnergy_density_bound a hMean
  obtain ⟨R, hR, _, hE⟩ := exists_interior_uniform_small_normalized_energy a hΩ hK hKsub hq ε Q
    hQ hEuler hStrong (fun W hW hWO => (hBulk W hW hWO).1) (fun W hW hWO => (hBulk W hW hWO).2) E₀ hE₀
  obtain ⟨d, hd, hdΩ⟩ := hK.exists_cthickening_subset_open hΩ hKsub
  have hNear := (eventually_uniform_interior_bulk_and_vacuum_small a hΩ hK.cthickening hdΩ hEstimate
    hq ε Q hε hQ hEuler hBound hStrong (fun W hW hWO => (hBulk W hW hWO).1)
    (fun W hW hWO => (hBulk W hW hWO).2)).2 δ hδ
  let ρ := min R d
  have hρ : 0 < ρ := lt_min hR hd
  have hTail : ∀ᶠ n in atTop, ∀ x ∈ K, w n x ≤ 256 / ρ ^ 2 := by
    filter_upwards [hE, hNear] with n hn hVac x hx
    have hB : ball x ρ ⊆ cthickening d K := Metric.ball_subset_closedBall.trans
      ((closedBall_subset_closedBall (min_le_right R d)).trans (closedBall_subset_cthickening hx d))
    have hW := hSmall (ε n) x ρ hρ (Q n) ((hQ n).mono (hB.trans hdΩ))
      (fun y hy => hEuler n y (hdΩ (hB hy))) (fun y hy => hVac y (hB hy))
      (hn x hx ρ ⟨hρ, min_le_left _ _⟩) x (mem_ball_self (half_pos hρ))
    exact (le_div_iff₀ (sq_pos_of_pos hρ)).mpr ((mul_comm _ _).le.trans hW)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hTail
  have hIni (n : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖w n x‖ ≤ C :=
    hK.exists_bound_of_continuousOn ((contDiffOn_classicalEnergyDensity a (ε n) hΩ (hQ n)).continuousOn.mono hKsub)
  choose C hC using hIni
  let T := ∑ n ∈ Finset.range N, max (C n) 0
  have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hBase : 0 < 256 / ρ ^ 2 := div_pos (by norm_num) (sq_pos_of_pos hρ)
  refine ⟨256 / ρ ^ 2 + T, add_pos_of_pos_of_nonneg hBase hT, ?_⟩
  intro n x hx
  by_cases hn : N ≤ n
  · exact (hN n hn x hx).trans (le_add_of_nonneg_right hT)
  · have hn' := Finset.mem_range.mpr (lt_of_not_ge hn)
    have hCn : max (C n) 0 ≤ T := Finset.single_le_sum (fun i _ => le_max_right (C i) 0) hn'
    exact (le_abs_self (w n x)).trans
      ((by simpa [Real.norm_eq_abs] using hC n x hx : |w n x| ≤ C n).trans
        ((le_max_left _ _).trans (hCn.trans (le_add_of_nonneg_left hBase.le))))

private theorem lipschitzOnWith_of_gradientNormSq_bound_on_ball {u : Point → S0}
    {c : Point} {r B : ℝ}
    (hu : ContDiffOn ℝ 1 u (ball c r))
    (hGrad : ∀ x ∈ ball c r, gradientNormSq (ClassicalGradient u x) ≤ B) :
    LipschitzOnWith (Real.toNNReal (Real.sqrt B)) u (ball c r) := by
  apply (convex_ball c r).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x hx => ((hu x hx).contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
  intro x hx
  change ‖fderiv ℝ u x‖ ≤ (Real.toNNReal (Real.sqrt B) : ℝ)
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro z
  calc
    _ = ‖gradientFromColumns (ClassicalGradient u x) z‖ :=
      congrArg (fun w : S0 => ‖w‖) (gradientFromColumns_classicalGradient u x z).symm
    _ ≤ _ := (norm_gradientFromColumns_le _ _).trans
      ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hGrad x hx)) (norm_nonneg _)).trans_eq (mul_comm _ _))

/-- Local strong convergence and the uniform gradient bounds determine the
uniform limit on every regular compact set. -/
theorem tendstoUniformlyOn_of_strongH1Loc_of_interior_gradient_bound
    {Ω K : Set Point} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKsub : K ⊆ Ω)
    {q : Point → S0} {Q : ℕ → Point → S0} (hq : ContDiffOn ℝ 2 q Ω)
    (hQ : ∀ n, ContDiffOn ℝ 1 (Q n) Ω)
    (hStrong : StrongH1Loc Ω Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q))
    (hGrad : ∀ K', IsCompact K' → K' ⊆ Ω → ∃ B ≥ (0 : ℝ), ∀ n x, x ∈ K' →
      gradientNormSq (ClassicalGradient (Q n) x) ≤ B) :
    TendstoUniformlyOn Q q atTop K := by
  obtain ⟨O, G, hO, hKO, _, _, hqGrad⟩ := exists_gradientNormSq_bound_on_compact_collar
    hΩ hΩ (hq.mono inter_subset_right) hK (fun x hx => ⟨subset_closure (hKsub hx), hKsub hx⟩)
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open (hΩ.inter hO) (fun x hx => ⟨hKsub hx, hKO hx⟩)
  let K' := cthickening δ K
  let W := thickening δ K
  have hCl : closure W ⊆ K' := closure_thickening_subset_cthickening δ K
  have hWΩ : CompactlyContained W Ω := ⟨hK.cthickening.of_isClosed_subset isClosed_closure hCl,
    hCl.trans (hδO.trans inter_subset_left)⟩
  have hW := (hStrong W isOpen_thickening hWΩ).2.2
  obtain ⟨B, _, hBW⟩ := hGrad K' hK.cthickening (hδO.trans inter_subset_left)
  let L := Real.sqrt B + Real.sqrt G
  have hL : 0 ≤ L := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine tendstoUniformlyOn_iff.mpr ?_
  intro d hd
  let ρ := min (δ / 2) (d / (2 * (L + 1)))
  have hρ : 0 < ρ := lt_min (half_pos hδ) (div_pos hd (by positivity))
  have hρδ : ρ ≤ δ := (min_le_left _ _).trans (half_le_self hδ.le)
  let τ := ENNReal.ofReal ((d / 2) ^ 2) * ENNReal.ofReal (ρ ^ 3 * (Real.pi * 4 / 3))
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  filter_upwards [hW (Iio_mem_nhds hτ)] with n hn x hx
  by_contra! hPeak
  have hBallW : ball x ρ ⊆ W :=
    (ball_subset_ball hρδ).trans (ball_subset_thickening hx δ)
  have hBall : ball x ρ ⊆ K' := hBallW.trans (thickening_subset_cthickening _ _)
  have hBallΩ := hBall.trans (hδO.trans inter_subset_left)
  have hLQ := lipschitzOnWith_of_gradientNormSq_bound_on_ball ((hQ n).mono hBallΩ)
    (fun y hy => hBW n y (hBall hy))
  have hLq := lipschitzOnWith_of_gradientNormSq_bound_on_ball
    ((hq.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).mono hBallΩ)
    (fun y hy => hqGrad y (hδO (hBall hy)))
  have hLow (y : Point) (hy : y ∈ ball x ρ) : d / 2 ≤ ‖Q n y - q y‖ := by
    have hxB := mem_ball_self (x := x) hρ
    have hP := hLQ.dist_le_mul y hy x hxB
    have hq' := hLq.dist_le_mul x hxB y hy
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)] at hP hq'
    rw [dist_comm x y] at hq'
    have hTri := (dist_triangle (q x) (q y) (Q n x)).trans
      (add_le_add le_rfl (dist_triangle (q y) (Q n y) (Q n x)))
    have hDist : L * dist y x ≤ d / 2 := by
      have hD := (mem_ball.mp hy).le.trans (min_le_right (δ / 2) _)
      refine (mul_le_mul (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)) hD
        dist_nonneg (by positivity : 0 ≤ L + 1)).trans_eq ?_
      field_simp
    rw [dist_comm (q y) (Q n y), dist_eq_norm (Q n y) (q y)] at hTri
    dsimp only [L] at hDist
    linarith only [hPeak, hTri, hP, hq', hDist]
  have hBound : τ ≤ h1Deviation W (Q n) q (ClassicalGradient (Q n)) (ClassicalGradient q) := by
    have hV : volume (ball x ρ) = ENNReal.ofReal (ρ ^ 3 * (Real.pi * 4 / 3)) := by
      rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hρ.le,
        ← ENNReal.ofReal_mul (pow_nonneg hρ.le 3)]
    calc
      τ = ∫⁻ _ in ball x ρ, ENNReal.ofReal ((d / 2) ^ 2) := by
        rw [lintegral_const, Measure.restrict_apply_univ, hV]
      _ ≤ ∫⁻ y in ball x ρ, ENNReal.ofReal (‖Q n y - q y‖ ^ 2 +
          ∑ j, ‖ClassicalGradient (Q n) y j - ClassicalGradient q y j‖ ^ 2) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
        exact ENNReal.ofReal_le_ofReal ((pow_le_pow_left₀ (half_pos hd).le (hLow y hy) 2).trans
          (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)))
      _ ≤ _ := h1Deviation_mono hBallW
  exact not_lt_of_ge hBound hn

/-- The energy-density bound and the strong limit identify the actual
sequence in local classical order zero. -/
theorem convergesC0Loc_of_strongH1Loc_of_regular_penalized_solutions
    (a : BulkCoefficients) {Ω : Set Point} (hΩ : IsOpen Ω)
    (hEstimate : InteriorPoissonGradientEstimate) (hMean : External.ClassicalScalarSubsolutionMeanValue)
    {M : ℝ} {q : Point → S0} (hq : ContDiffOn ℝ 2 q Ω)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω)
    (hEuler : ∀ n x, x ∈ Ω → (ε n : ℝ) ^ 2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x))
    (hBound : ∀ n x, x ∈ Ω → ‖Q n x‖ ≤ max 0 M)
    (hStrong : StrongH1Loc Ω Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q))
    (hBulk : ConvergesScaledPotentialLoc a Ω ε Q) :
    ConvergesCjLoc 0 Ω Q q := by
  refine ⟨fun n => (contDiffOn_infty.mp (hQ n)) 0, hq.of_le (by norm_num), ?_⟩
  intro k hk K hK hKsub
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
  subst k
  have hQ₁ (n : ℕ) : ContDiffOn ℝ 1 (Q n) Ω := (contDiffOn_infty.mp (hQ n)) 1
  have hGrad : ∀ K', IsCompact K' → K' ⊆ Ω → ∃ B ≥ (0 : ℝ), ∀ n x, x ∈ K' →
      gradientNormSq (ClassicalGradient (Q n) x) ≤ B := by
    intro K' hK' hK'Ω
    obtain ⟨C, hC, hE⟩ := exists_uniform_interior_energyDensity_bound a hΩ hK' hK'Ω hEstimate hMean
      hq ε Q hε hQ hEuler hBound hStrong hBulk
    refine ⟨2 * C, by positivity, ?_⟩
    intro n x hx
    have hU := hE n x hx
    unfold energyDensity at hU
    have hP := mul_nonneg (sq_nonneg (ε n : ℝ)⁻¹) (bulkPotential_nonneg a (Q n x))
    linarith only [hU, hP]
  have h := tendstoUniformlyOn_of_strongH1Loc_of_interior_gradient_bound hΩ hK hKsub hq hQ₁ hStrong hGrad
  have h' := tendstoUniformlyOn_iff.mp h
  refine tendstoUniformlyOn_iff.mpr ?_
  intro d hd
  filter_upwards [h' d hd] with n hn x hx
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
    LinearIsometryEquiv.dist_map] using hn x hx

end Thesis

end
