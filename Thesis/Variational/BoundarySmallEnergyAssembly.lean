module

public import Thesis.Variational.BoundarySmallEnergy
public import Thesis.Variational.BoundarySubsolution
public import Thesis.Variational.BoundaryPhysicalGradient
import Thesis.Variational.EnergyEstimate
import Thesis.StressEnergy

/-! The weighted maximum argument on the actual rescaled boundary cap. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

/-- The rescaled trace comparison and the quadratic interior inequality
give the quantitative bound on the half-radius cap. -/
theorem exists_boundary_smallEnergy_bound_of_rescaled_trace
    (hMean : External.ClassicalScalarSubsolutionMeanValue)
    {Cᵢ Cᵦ : ℝ} (hCᵢ : 0 ≤ Cᵢ) (hCᵦ : 0 < Cᵦ) :
    ∃ T F₀ C : ℝ, 1 ≤ T ∧ 0 < F₀ ∧ 0 < C ∧
      ∀ (U : Set Point), IsOpen U → ∀ c ∈ closure U, ∀ r : ℝ, 0 < r →
        ∀ (w : Point → ℝ) (b E δ : ℝ), 0 ≤ E → E + δ ^ 2 < F₀ →
          ContinuousOn w (closure U ∩ Metric.closedBall c r) →
          ContDiffOn ℝ 2 w (U ∩ Metric.ball c r) →
          (∀ x ∈ U ∩ Metric.ball c r, 0 ≤ w x ∧ -laplacian w x ≤ Cᵢ * (w x) ^ 2) →
          (∀ x ∈ U ∩ Metric.ball c r, ∀ s ∈ Ioo 0 r,
            (∫⁻ y in U ∩ Metric.ball x s, ENNReal.ofReal (w y)) ≤ ENNReal.ofReal (E * s)) →
          (∀ z ∈ closure U ∩ Metric.ball c r, T * b ^ 2 < w z →
            (∀ y ∈ closure U ∩ Metric.closedBall z ((r - dist z c) / 2), w y ≤ 4 * w z) →
              let t := (Real.sqrt (w z))⁻¹
              let Z (x : Point) := z + t • x
              let U₁ := Z ⁻¹' U
              ∀ ρ : ℝ, 0 < ρ → ρ < ((r - dist z c) / 2 / t) / 10 → ρ < 1 →
                ∀ y ∈ frontier U₁ ∩ Metric.ball 0 ρ,
                  t ^ 2 * w (Z y) ≤ Cᵦ * (T⁻¹ + (E + δ ^ 2) / ρ ^ 2 + E + ρ * Real.sqrt E + ρ ^ 2)) →
          ∀ x ∈ U ∩ Metric.ball c (r / 2), w x ≤ C * (b ^ 2 + r⁻¹ ^ 2 * (E + δ ^ 2)) := by
  obtain ⟨M, hM, hMV⟩ := exists_capped_meanValue_bound_on_boundary_cap hMean
    (A := 4 * Cᵢ) (mul_nonneg (by norm_num) hCᵢ)
  let K := M * (Cᵦ + 1)
  have hK : 0 < K := mul_pos hM (by positivity)
  obtain ⟨T, F₀, hT, hF₀, hBalance⟩ :=
    exists_boundary_smallEnergy_radius_balance_threshold_of_quadratic_error hK (L := 1) (by norm_num)
  let C := T + 12800 * K
  have hC : 0 < C := add_pos_of_pos_of_nonneg (zero_lt_one.trans_le hT) (by positivity)
  refine ⟨T, F₀, C, hT, hF₀, hC, ?_⟩
  intro U hU c hc r hr w b E δ hE hSmall hwC hw hBochner hMorrey hTrace x hx
  let b₀ := T * b ^ 2
  have hb₀ : 0 ≤ b₀ := mul_nonneg (zero_le_one.trans hT) (sq_nonneg _)
  obtain ⟨z, hz, hM₀, hzMax, hzLocal⟩ := exists_boundary_weighted_energy_maximizer hc hr hwC hb₀
  let m := (r - dist z c) ^ 2 * max (w z - b₀) 0
  have hm : m ≤ 3200 * K * (E + δ ^ 2) := by
    rcases hM₀.eq_or_lt with hZero | hPos
    · change 0 = m at hZero
      rw [← hZero]
      positivity
    obtain ⟨hzDist, hzPos, hzBound⟩ := hzLocal hPos
    let α := w z
    have hα : 0 < α := hb₀.trans_lt hzPos
    let t := (Real.sqrt α)⁻¹
    have ht : 0 < t := inv_pos.mpr (Real.sqrt_pos.mpr hα)
    have htα : t ^ 2 * α = 1 := by
      dsimp only [t]
      rw [inv_pow, Real.sq_sqrt hα.le, inv_mul_cancel₀ hα.ne']
    let R := (r - dist z c) / 2 / t
    have hMargin : 0 < (r - dist z c) / 2 := half_pos (sub_pos.mpr hzDist)
    have hR : 0 < R := div_pos hMargin ht
    let Z (y : Point) := z + t • y
    let U₁ := Z ⁻¹' U
    let w₁ (y : Point) := t ^ 2 * w (Z y)
    have hZc : Continuous Z := continuous_const.add (continuous_id.const_smul t)
    have hZd : ContDiff ℝ 2 Z := contDiff_const.add (contDiff_id.const_smul t)
    have hU₁ : IsOpen U₁ := hU.preimage hZc
    have hZ0 : Z 0 = z := by simp only [Z, smul_zero, add_zero]
    let L := (Homeomorph.smul (Units.mk0 t ht.ne')).trans (Homeomorph.addLeft z)
    have hL : (L : Point → Point) = Z := by
      funext y
      rfl
    have hCl : Z ⁻¹' closure U = closure U₁ := by
      rw [← hL, L.preimage_closure]
      simp only [hL, U₁]
    have hCenter : (0 : Point) ∈ closure U₁ := by
      rw [← hCl]
      change Z 0 ∈ closure U
      rw [hZ0]
      exact hz.1
    have hw₁0 : w₁ 0 = 1 := by
      change t ^ 2 * w (Z 0) = 1
      rw [hZ0]
      exact htα
    have hNormZ (y : Point) : ‖Z y - z‖ = t * ‖y‖ := by
      change ‖z + t • y - z‖ = _
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
    have hIneq (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ < R / 10) (hρ₁ : ρ < 1) :
        1 ≤ K * (T⁻¹ + (E + δ ^ 2) / ρ ^ 2 + E + ρ * Real.sqrt E + 1 * ρ ^ 2) := by
      let V := U₁ ∩ Metric.ball (0 : Point) ρ
      have hV : IsOpen V := hU₁.inter Metric.isOpen_ball
      have hs : t * ρ < (r - dist z c) / 2 := by
        have hρR' : ρ < R := hρR.trans (by linarith only [hR])
        have h := (lt_div_iff₀ ht).mp hρR'
        exact (mul_comm t ρ).le.trans_lt h
      have hOriginal (y : Point) (hy : y ∈ Metric.closedBall (0 : Point) ρ) :
          Z y ∈ Metric.closedBall z ((r - dist z c) / 2) ∧ Z y ∈ Metric.ball c r := by
        have hY : ‖y‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
        have hDist : dist (Z y) z < (r - dist z c) / 2 := by
          rw [dist_eq_norm, hNormZ]
          exact (mul_le_mul_of_nonneg_left hY ht.le).trans_lt hs
        have hTri := dist_triangle (Z y) z c
        exact ⟨hDist.le, by change dist (Z y) c < r; linarith only [hzDist, hDist, hTri]⟩
      have hMapC : MapsTo Z (closure U₁ ∩ Metric.closedBall 0 ρ) (closure U ∩ Metric.closedBall c r) := by
        intro y hy
        have hY : Z y ∈ closure U := by
          have hyy : y ∈ Z ⁻¹' closure U := hCl.symm ▸ hy.1
          exact hyy
        exact ⟨hY, Metric.ball_subset_closedBall (hOriginal y hy.2).2⟩
      have hMapV : MapsTo Z V (U ∩ Metric.ball c r) := fun y hy =>
        ⟨hy.1, (hOriginal y (Metric.ball_subset_closedBall hy.2)).2⟩
      have hWc : ContinuousOn w₁ (closure U₁ ∩ Metric.closedBall 0 ρ) :=
        (hwC.comp hZc.continuousOn hMapC).const_mul _
      have hWc' : ContDiffOn ℝ 2 (w ∘ Z) V := hw.comp hZd.contDiffOn hMapV
      have hWd : ContDiffOn ℝ 2 w₁ V := by
        simpa only [w₁, Function.comp_apply, smul_eq_mul] using hWc'.const_smul (t ^ 2)
      have hWpos (y : Point) (hy : y ∈ V) : 0 ≤ w₁ y :=
        mul_nonneg (sq_nonneg _) (hBochner _ (hMapV hy)).1
      have hWup (y : Point) (hy : y ∈ V) : w₁ y ≤ 4 := by
        have hY := hzBound (Z y) ⟨subset_closure hy.1, (hOriginal y (Metric.ball_subset_closedBall hy.2)).1⟩
        have h := mul_le_mul_of_nonneg_left hY (sq_nonneg t)
        change t ^ 2 * w (Z y) ≤ _
        nlinarith only [h, htα]
      have hWlap (y : Point) (hy : y ∈ V) : -laplacian w₁ y ≤ (4 * Cᵢ) * w₁ y := by
        have hLap : laplacian w₁ y = t ^ 4 * laplacian w (Z y) := by
          change laplacian (fun q => t ^ 2 • (w ∘ Z) q) y = _
          rw [laplacian_const_smul hV hWc' hy]
          have hZlap : laplacian (w ∘ Z) y = t ^ 2 • laplacian w (Z y) :=
            laplacian_affine_dilation (hU.inter Metric.isOpen_ball) hw z t (hMapV hy)
          rw [hZlap,
            smul_eq_mul, smul_eq_mul]
          ring
        have h := mul_le_mul_of_nonneg_left ((hBochner _ (hMapV hy)).2) (pow_nonneg ht.le 4)
        have h' : -laplacian w₁ y ≤ Cᵢ * (w₁ y) ^ 2 := by
          rw [hLap]
          dsimp only [w₁, Z]
          nlinarith only [h]
        exact h'.trans (by
          have hI := mul_le_mul_of_nonneg_right (hWup y hy) (hWpos y hy)
          nlinarith only [mul_le_mul_of_nonneg_left hI hCᵢ])
      have hCompact : IsCompact (closure U₁ ∩ Metric.closedBall (0 : Point) ρ) :=
        (isCompact_closedBall _ _).inter_left isClosed_closure
      have hIn : IntegrableOn w₁ V volume := (hWc.integrableOn_compact hCompact).mono_set
        (fun _ hy => ⟨subset_closure hy.1, Metric.ball_subset_closedBall hy.2⟩)
      have hIE : ρ⁻¹ ^ 3 * (∫ y in V, w₁ y) ≤ E / ρ ^ 2 := by
        have hs' : t * ρ ∈ Ioo (0 : ℝ) r := ⟨mul_pos ht hρ, hs.trans (by linarith only [hr, dist_nonneg (x := z) (y := c)])⟩
        have hM' := morrey_lintegral_bound_at_closure_center hMorrey ⟨hz.1, hzDist⟩ hs'
        have hScaled := normalized_lintegral_affine_boundary_cap hU.measurableSet z ht hρ
          (fun y => ENNReal.ofReal (w y))
        change ENNReal.ofReal ρ⁻¹ * (∫⁻ y in V, ENNReal.ofReal (t ^ 2) * ENNReal.ofReal (w (Z y))) =
          ENNReal.ofReal ((t * ρ)⁻¹) * ∫⁻ y in U ∩ Metric.ball z (t * ρ), ENNReal.ofReal (w y) at hScaled
        simp_rw [← ENNReal.ofReal_mul (sq_nonneg t)] at hScaled
        have hFI : ENNReal.ofReal (ρ⁻¹ * ∫ y in V, w₁ y) ≤ ENNReal.ofReal E := by
          rw [ENNReal.ofReal_mul (inv_nonneg.mpr hρ.le),
            ofReal_integral_eq_lintegral_ofReal hIn ((ae_restrict_mem hV.measurableSet).mono hWpos)]
          refine hScaled.le.trans ((mul_le_mul_right hM' _).trans_eq ?_)
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hs'.1.le)]
          congr 1
          field_simp [hs'.1.ne']
        have hRatio := (ENNReal.ofReal_le_ofReal_iff hE).mp hFI
        have hR' := mul_le_mul_of_nonneg_left hRatio (sq_nonneg ρ⁻¹)
        calc
          _ = ρ⁻¹ ^ 2 * (ρ⁻¹ * ∫ y in V, w₁ y) := by ring
          _ ≤ ρ⁻¹ ^ 2 * E := hR'
          _ = _ := by rw [div_eq_mul_inv, inv_pow, mul_comm]
      let S := T⁻¹ + (E + δ ^ 2) / ρ ^ 2 + E + ρ * Real.sqrt E + ρ ^ 2
      have hS : 0 ≤ S := by dsimp only [S]; positivity
      have hTrace' : ∀ y ∈ frontier U₁ ∩ Metric.ball 0 ρ, w₁ y ≤ Cᵦ * S :=
        hTrace z ⟨hz.1, hzDist⟩ hzPos hzBound ρ hρ hρR hρ₁
      have hMV' := hMV U₁ hU₁ 0 hCenter ρ ⟨hρ, hρ₁.le⟩ w₁ (Cᵦ * S) (mul_nonneg hCᵦ.le hS)
        (hWc.mono (fun _ hy => ⟨hy.1, Metric.ball_subset_closedBall hy.2⟩)) hWd hIn hWpos hTrace' hWlap
      rw [hw₁0] at hMV'
      have hES : E / ρ ^ 2 ≤ S := by
        have hE' : E / ρ ^ 2 ≤ (E + δ ^ 2) / ρ ^ 2 :=
          div_le_div_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg δ)) (sq_nonneg ρ)
        change E / ρ ^ 2 ≤ T⁻¹ + (E + δ ^ 2) / ρ ^ 2 + E + ρ * Real.sqrt E + ρ ^ 2
        linarith only [hE', hE, sq_nonneg ρ, inv_nonneg.mpr (zero_le_one.trans hT),
          mul_nonneg hρ.le (Real.sqrt_nonneg E)]
      calc
        (1 : ℝ) ≤ M * (ρ⁻¹ ^ 3 * (∫ y in V, w₁ y) + Cᵦ * S) := hMV'
        _ ≤ M * (S + Cᵦ * S) := mul_le_mul_of_nonneg_left
          (add_le_add (hIE.trans hES) le_rfl) hM.le
        _ = _ := by dsimp only [K, S]; ring
    have hRBound := hBalance hE hR hSmall hIneq
    have hmR : m ≤ 4 * R ^ 2 := by
      change (r - dist z c) ^ 2 * max (α - b₀) 0 ≤ _
      rw [max_eq_left (sub_nonneg.mpr hzPos.le)]
      have hA : α - b₀ ≤ α := sub_le_self _ hb₀
      refine (mul_le_mul_of_nonneg_left hA (sq_nonneg _)).trans_eq ?_
      dsimp only [R]
      have hαt : α = (t ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right htα
      rw [hαt]
      field_simp [ht.ne']
      ring
    nlinarith only [hRBound, hmR]
  have hxK : x ∈ closure U ∩ Metric.closedBall c r := ⟨subset_closure hx.1,
    Metric.ball_subset_closedBall ((Metric.ball_subset_ball (by linarith only [hr])) hx.2)⟩
  have hMargin : r / 2 ≤ r - dist x c := by
    have hDist := Metric.mem_ball.mp hx.2
    linarith only [hDist]
  have hX := hzMax hxK
  change (r - dist x c) ^ 2 * max (w x - b₀) 0 ≤ m at hX
  have hTmax := (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (half_pos hr).le hMargin 2)
    (le_max_right (w x - b₀) 0)).trans (hX.trans hm)
  have hr₂ : 0 < (r / 2) ^ 2 := sq_pos_of_pos (half_pos hr)
  have hB : w x - b₀ ≤ 3200 * K * (E + δ ^ 2) / (r / 2) ^ 2 := by
    apply (le_div_iff₀ hr₂).mpr
    rw [mul_comm (w x - b₀)]
    exact (mul_le_mul_of_nonneg_left (le_max_left (w x - b₀) 0) hr₂.le).trans hTmax
  have hRatio : 3200 * K * (E + δ ^ 2) / (r / 2) ^ 2 = 12800 * K * (r⁻¹ ^ 2 * (E + δ ^ 2)) := by
    field_simp [hr.ne']
    ring
  rw [hRatio] at hB
  have hbV : 0 ≤ b ^ 2 := sq_nonneg _
  have hEV : 0 ≤ r⁻¹ ^ 2 * (E + δ ^ 2) := mul_nonneg (sq_nonneg _) (add_nonneg hE (sq_nonneg _))
  change w x ≤ (T + 12800 * K) * (b ^ 2 + r⁻¹ ^ 2 * (E + δ ^ 2))
  change w x - T * b ^ 2 ≤ _ at hB
  nlinarith only [hB, mul_nonneg (zero_le_one.trans hT) hEV, mul_nonneg (by positivity : 0 ≤ 12800 * K) hbV]

private theorem five_sum_sq_le (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e)]

/-- Boundary small-energy regularity for the actual classical Dirichlet
solutions used in the expansion. The trace scale comes from the explicit
gradient and Laplacian bounds of its extension on the physical cap. -/
theorem exists_boundary_classical_smallEnergy_bound
    (hPoisson : External.ZeroTraceBoundaryPoissonL4GradientEstimate)
    (hMean : External.ClassicalScalarSubsolutionMeanValue)
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ R δ₀ E₀ C : ℝ, 0 < R ∧ 0 < δ₀ ∧ 0 < E₀ ∧ 0 < C ∧
      ∀ c ∈ frontier U, ∀ r ∈ Ioo 0 R, ∀ (ε : ElasticScale) (Q b : Point → S0)
        (B₁ B₂ E d : ℝ), 0 ≤ B₁ → 0 ≤ B₂ → 0 ≤ E → E < E₀ → 0 ≤ d → d < δ₀ →
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U → ContDiffOn ℝ 2 Q (closure U) →
        ContDiffOn ℝ 2 b (closure U) → EqOn Q b (frontier U) →
        (∀ y ∈ frontier U, b y ∈ vacuum a) →
        (∀ y ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian Q y) : Tensor) = bulkGradient a (Q y)) →
        (∀ y ∈ U ∩ Metric.ball c r, Metric.infDist (Q y) (vacuum a) ≤ d) →
        (∀ y ∈ U ∩ Metric.ball c r, ∀ s ∈ Ioo 0 r,
          energy a ε (U ∩ Metric.ball y s) Q (ClassicalGradient Q) ≤ ENNReal.ofReal (E * s)) →
        (∀ y ∈ closure U ∩ Metric.ball c r, ∀ v : Point,
          ‖(fderivWithin ℝ b (closure U) y) v‖ ≤ B₁ * ‖v‖) →
        (∀ y ∈ U ∩ Metric.ball c r, ‖laplacian b y‖ ≤ B₂) →
        ∀ y ∈ U ∩ Metric.ball c (r / 2),
          energyDensity a ε (Q y) (ClassicalGradient Q y) ≤
            C * ((B₁ + r * B₂) ^ 2 + r⁻¹ ^ 2 * (E + d ^ 2)) := by
  obtain ⟨R, δb, K, hR, hδb, hK, hWall⟩ := exists_scaled_physical_wall_derivative_bound hPoisson a hU
  obtain ⟨δi, I, hδi, hI, hInt⟩ := exists_near_vacuum_classicalEnergyDensity_bochner_bound a
  let B := (15 / 2 : ℝ) * K ^ 2
  have hB : 0 < B := mul_pos (by norm_num) (sq_pos_of_pos hK)
  obtain ⟨T, F₀, hC, hT, hF₀, hC₀, hBound⟩ :=
    exists_boundary_smallEnergy_bound_of_rescaled_trace hMean hI.le hB
  let δ₀ := min (min δi δb) (Real.sqrt (F₀ / 2))
  have hδ₀ : 0 < δ₀ := lt_min (lt_min hδi hδb) (Real.sqrt_pos.mpr (half_pos hF₀))
  refine ⟨R, δ₀, F₀ / 2, hC, hR, hδ₀, half_pos hF₀, hC₀, ?_⟩
  intro c hc r hr ε Q b B₁ B₂ E d hB₁ hB₂ hE hEF hd hdδ hQ hClose hb hTrace hVac hEuler hNear
    hMorrey hData hbΔ x hx
  let w (y : Point) := energyDensity a ε (Q y) (closureGradient U Q y)
  let e (y : Point) := energyDensity a ε (Q y) (ClassicalGradient Q y)
  let b₀ := B₁ + r * B₂
  have hwEq : EqOn w e U := by
    intro y hy
    change energyDensity a ε (Q y) (closureGradient U Q y) =
      energyDensity a ε (Q y) (ClassicalGradient Q y)
    rw [closureGradient_eq_classicalGradient hU.1.1 hClose hy]
  have hwC : ContinuousOn w (closure U ∩ Metric.closedBall c r) :=
    (continuousOn_closureEnergyDensity a ε hU.uniqueDiffOn_closure hClose).mono inter_subset_left
  have hEd : ContDiffOn ℝ 2 e U :=
    (contDiffOn_classicalEnergyDensity a ε hU.1.1 hQ).of_le (WithTop.coe_le_coe.mpr le_top)
  have hwd : ContDiffOn ℝ 2 w (U ∩ Metric.ball c r) :=
    (hEd.congr hwEq).mono inter_subset_left
  have hIr : ∀ y ∈ U ∩ Metric.ball c r, 0 ≤ w y ∧ -laplacian w y ≤ I * (w y) ^ 2 := by
    intro y hy
    have hyNear : Q y ∈ vacuumTube a δi :=
      (hNear y hy).trans_lt (hdδ.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
    have hElap : laplacian w y = laplacian e y := by
      apply laplacian_eq_of_eventuallyEq
      filter_upwards [hU.1.1.mem_nhds hy.1] with z hz
      exact hwEq hz
    rw [hwEq hy.1, hElap]
    exact ⟨energyDensity_nonneg a ε _ _, hInt ε U hU.1.1 Q hQ hEuler y hy.1 hyNear⟩
  have hMass : ∀ y ∈ U ∩ Metric.ball c r, ∀ s ∈ Ioo 0 r,
      (∫⁻ x in U ∩ Metric.ball y s, ENNReal.ofReal (w x)) ≤ ENNReal.ofReal (E * s) := by
    intro y hy s hs
    have hEq : (∫⁻ x in U ∩ Metric.ball y s, ENNReal.ofReal (w x)) =
        energy a ε (U ∩ Metric.ball y s) Q (ClassicalGradient Q) := by
      unfold energy
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hU.1.1.inter Metric.isOpen_ball).measurableSet] with z hz
      exact congrArg ENNReal.ofReal (hwEq hz.1)
    exact hEq.le.trans (hMorrey y hy s hs)
  have hF : E + d ^ 2 < F₀ := by
    have hD := hdδ.trans_le (min_le_right _ _)
    have hSq := (sq_lt_sq₀ hd (Real.sqrt_nonneg _)).mpr hD
    rw [Real.sq_sqrt (half_pos hF₀).le] at hSq
    linarith only [hSq, hEF]
  have hResult := hBound U hU.1.1 c (frontier_subset_closure hc) r hr.1 w b₀ E d hE hF hwC hwd hIr hMass
  have hTraceBound :
      ∀ z ∈ closure U ∩ Metric.ball c r, T * b₀ ^ 2 < w z →
        (∀ y ∈ closure U ∩ Metric.closedBall z ((r - dist z c) / 2), w y ≤ 4 * w z) →
        let t := (Real.sqrt (w z))⁻¹
        let Z (x : Point) := z + t • x
        let U₁ := Z ⁻¹' U
        ∀ ρ : ℝ, 0 < ρ → ρ < ((r - dist z c) / 2 / t) / 10 → ρ < 1 →
          ∀ y ∈ frontier U₁ ∩ Metric.ball 0 ρ,
            t ^ 2 * w (Z y) ≤ B * (T⁻¹ + (E + d ^ 2) / ρ ^ 2 + E + ρ * Real.sqrt E + ρ ^ 2) := by
    intro z hz hZmax hZbound
    let α := w z
    let t := (Real.sqrt α)⁻¹
    let Z (y : Point) := z + t • y
    let U₁ := Z ⁻¹' U
    let r₂ := (r - dist z c) / 2
    change ∀ ρ : ℝ, 0 < ρ → ρ < (r₂ / t) / 10 → ρ < 1 → _
    intro ρ hρ hρr _ y hy
    have hT₀ : 0 < T := zero_lt_one.trans_le hT
    have hα : 0 < α := (mul_nonneg hT₀.le (sq_nonneg b₀)).trans_lt hZmax
    have ht : 0 < t := inv_pos.mpr (Real.sqrt_pos.mpr hα)
    have htα : t ^ 2 * α = 1 := by
      dsimp only [t]
      rw [inv_pow, Real.sq_sqrt hα.le, inv_mul_cancel₀ hα.ne']
    let s := t * ρ
    have hs : 0 < s := mul_pos ht hρ
    have hr₂ : 0 < r₂ := half_pos (sub_pos.mpr (Metric.mem_ball.mp hz.2))
    have hv : 2 * s < r₂ := by
      have h := (lt_div_iff₀ (by norm_num : 0 < (10 : ℝ))).mp hρr
      have h' := (lt_div_iff₀ ht).mp h
      dsimp only [s]
      nlinarith only [h', mul_pos ht hρ]
    have hsR : s < R := by
      have hD := dist_nonneg (x := z) (y := c)
      dsimp only [r₂] at hv
      linarith only [hv, hs, hD, hr.2, hr.1]
    have h2s : (2 * s) ∈ Ioo 0 r := by
      refine ⟨mul_pos (by norm_num) hs, ?_⟩
      have hD := dist_nonneg (x := z) (y := c)
      dsimp only [r₂] at hv
      linarith only [hv, hD, hr.1]
    let a₀ := Z y
    have ha₀ : a₀ ∈ frontier U := by
      let L := (Homeomorph.smul (Units.mk0 t ht.ne')).trans (Homeomorph.addLeft z)
      have hL : (L : Point → Point) = Z := by funext x; rfl
      have hL' : Z ⁻¹' frontier U = frontier U₁ := by
        rw [← hL, L.preimage_frontier]
        simp only [hL, U₁]
      have h := hy.1
      rw [← hL'] at h
      exact h
    have haDist : dist a₀ z < s := by
      have hY : ‖y‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hy.2
      change ‖z + t • y - z‖ < _
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
      exact mul_lt_mul_of_pos_left hY ht
    have hOuter : Metric.ball a₀ s ⊆ Metric.ball z (2 * s) := by
      intro q hq
      have hTri := dist_triangle q a₀ z
      have hR' := Metric.mem_ball.mp hq
      exact Metric.mem_ball.mpr (by linarith only [hTri, hR', haDist])
    have hOuter' : Metric.ball z (2 * s) ⊆ Metric.closedBall z r₂ :=
      (Metric.ball_subset_ball hv.le).trans Metric.ball_subset_closedBall
    have hCap : Metric.ball a₀ s ⊆ Metric.ball c r := by
      intro q hq
      have hTri := dist_triangle q z c
      have hD : dist q z ≤ r₂ := hOuter' (hOuter hq)
      have hzD := Metric.mem_ball.mp hz.2
      dsimp only [r₂] at hD
      exact Metric.mem_ball.mpr (by linarith only [hTri, hD, hzD])
    let V := U ∩ Metric.ball a₀ s
    let G (q : Point) := gradientNormSq (ClassicalGradient Q q)
    have hWg (q : Point) (hq : q ∈ U) : G q ≤ 2 * w q := by
      rw [hwEq hq]
      have hP := mul_nonneg (sq_nonneg (ε : ℝ)⁻¹) (bulkPotential_nonneg a (Q q))
      change G q ≤ 2 * ((1 / 2 : ℝ) * G q + (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q q))
      linarith only [hP]
    have hUb (q : Point) (hq : q ∈ V) : Metric.infDist (Q q) (vacuum a) ≤ d ∧ G q ≤ 8 / t ^ 2 := by
      have hg := (hWg q hq.1).trans (mul_le_mul_of_nonneg_left
        (hZbound q ⟨subset_closure hq.1, hOuter' (hOuter hq.2)⟩) (by norm_num : (0 : ℝ) ≤ 2))
      have hEq : α = (t ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right htα
      refine ⟨hNear q ⟨hq.1, hCap hq.2⟩, ?_⟩
      rw [div_eq_mul_inv, ← hEq]
      nlinarith only [hg]
    have hVmass : (∫⁻ q in V, ENNReal.ofReal (G q)) ≤ ENNReal.ofReal (4 * E * s) := by
      have hM := morrey_lintegral_bound_at_closure_center hMass hz h2s
      have hVsub : V ⊆ U ∩ Metric.ball z (2 * s) := fun q hq => ⟨hq.1, hOuter hq.2⟩
      calc
        _ ≤ ∫⁻ q in V, ENNReal.ofReal (2 * w q) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem (hU.1.1.inter Metric.isOpen_ball).measurableSet] with q hq
          exact ENNReal.ofReal_le_ofReal (hWg q hq.1)
        _ = ENNReal.ofReal 2 * ∫⁻ q in V, ENNReal.ofReal (w q) := by
          simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (E * (2 * s)) :=
          mul_le_mul_right ((lintegral_mono_set hVsub).trans hM) _
        _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; congr 1; ring
    have hScaled (v : Point) :
        t * ‖(fderivWithin ℝ Q (closure U) a₀) v‖ ≤
        K * (t * b₀ + d / ρ + Real.sqrt E / ρ + Real.sqrt (ρ * Real.sqrt E) + ρ) * ‖v‖ := by
      have h := hWall a₀ ha₀ t ρ ht hρ hsR ε Q b d E B₁ B₂ hd
        (hdδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))) hE hB₁ hB₂
        hClose hb hTrace hVac (fun q hq => hEuler q hq.1) hUb hVmass
        (fun q hq => hData q ⟨hq.1, hCap hq.2⟩) (fun q hq => hbΔ q ⟨hq.1, hCap hq.2⟩) v
      have hB' : B₁ + s * B₂ ≤ b₀ := add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (by dsimp only [r₂] at hv; linarith only [hv, hs, dist_nonneg (x := z) (y := c)]) hB₂)
      have hT' := mul_le_mul_of_nonneg_left hB' ht.le
      have hOrd : t * (B₁ + s * B₂) + d / ρ + Real.sqrt E / ρ + Real.sqrt (ρ * Real.sqrt E) + ρ ≤
          t * b₀ + d / ρ + Real.sqrt E / ρ + Real.sqrt (ρ * Real.sqrt E) + ρ := by linarith only [hT']
      exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hOrd hK.le) (norm_nonneg _))
    let S := T⁻¹ + (E + d ^ 2) / ρ ^ 2 + E + ρ * Real.sqrt E + ρ ^ 2
    let P := t * b₀ + d / ρ + Real.sqrt E / ρ + Real.sqrt (ρ * Real.sqrt E) + ρ
    have hB₀ : 0 ≤ b₀ := add_nonneg hB₁ (mul_nonneg hr.1.le hB₂)
    have hP : 0 ≤ P := by dsimp only [P]; positivity
    have hTb : (t * b₀) ^ 2 ≤ T⁻¹ := by
      have hh := mul_le_mul_of_nonneg_left hZmax.le (sq_nonneg t)
      change t ^ 2 * (T * b₀ ^ 2) ≤ t ^ 2 * α at hh
      rw [htα] at hh
      rw [← one_div]
      exact (le_div_iff₀ hT₀).mpr (by nlinarith only [hh])
    have hP₂ : P ^ 2 ≤ 5 * S := by
      have h5 := five_sum_sq_le (t * b₀) (d / ρ) (Real.sqrt E / ρ) (Real.sqrt (ρ * Real.sqrt E)) ρ
      rw [div_pow, div_pow, Real.sq_sqrt hE, Real.sq_sqrt (mul_nonneg hρ.le (Real.sqrt_nonneg E))] at h5
      change P ^ 2 ≤ _ at h5
      dsimp only [S]
      rw [add_div]
      linarith only [h5, hTb, hE]
    have hWwall : w a₀ = (1 / 2 : ℝ) * gradientNormSq (closureGradient U Q a₀) := by
      have hV : Q a₀ ∈ vacuum a := by rw [hTrace ha₀]; exact hVac _ ha₀
      change energyDensity a ε (Q a₀) (closureGradient U Q a₀) = _
      rw [energyDensity, (bulkPotential_eq_zero_iff a _).mpr hV, mul_zero, add_zero]
    have hCol (i : Fin 3) : t ^ 2 * ‖closureGradient U Q a₀ i‖ ^ 2 ≤ K ^ 2 * (5 * S) := by
      have hvNorm : ‖axis i‖ = 1 := by simp [axis]
      have h := hScaled (axis i)
      rw [hvNorm, mul_one] at h
      change t * ‖closureGradient U Q a₀ i‖ ≤ K * P at h
      have hSq := (sq_le_sq₀ (mul_nonneg ht.le (norm_nonneg _)) (mul_nonneg hK.le hP)).mpr h
      rw [mul_pow, mul_pow] at hSq
      exact hSq.trans (mul_le_mul_of_nonneg_left hP₂ (sq_nonneg K))
    change t ^ 2 * w a₀ ≤ B * S
    rw [hWwall, gradientNormSq_eq_sum_norm_sq, ← mul_assoc, mul_comm (t ^ 2) (1 / 2 : ℝ), mul_assoc, Finset.mul_sum]
    have hSum : (∑ i : Fin 3, t ^ 2 * ‖closureGradient U Q a₀ i‖ ^ 2) ≤
        ∑ _ : Fin 3, K ^ 2 * (5 * S) := Finset.sum_le_sum fun j _ => hCol j
    norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hSum
    dsimp only [B]
    linarith only [hSum]
  have hh := hResult hTraceBound x hx
  rwa [hwEq hx.1] at hh

end Thesis

end
