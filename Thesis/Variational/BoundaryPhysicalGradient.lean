module

public import Thesis.Variational.BoundaryBarrier
public import Thesis.Variational.BoundaryPoissonEstimate
public import Thesis.Variational.BoundaryMorreyNorms
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! The scaled derivative on the physical wall for the boundary maximum argument. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius RealInnerProductSpace

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem fderivWithin_apply_eq_normal_of_zero_wall
    {U : Set Point} (hU : IsSmoothDomain U) {a ν : Point}
    (hNormal : HasRegularOutwardNormalAt U a ν) {Z : Point → S0}
    (hZ : ContDiffOn ℝ 1 Z (closure U)) (hTrace : EqOn Z (fun _ => 0) (frontier U))
    (v : Point) :
    (fderivWithin ℝ Z (closure U) a) v =
      (inner ℝ v ν) • (fderivWithin ℝ Z (closure U) a) ν := by
  let D := fderivWithin ℝ Z (closure U) a
  let w := v - (inner ℝ v ν) • ν
  have hw : inner ℝ w ν = 0 := by
    change inner ℝ (v - (inner ℝ v ν) • ν) ν = 0
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hNormal.2.1, one_pow, mul_one, sub_self]
  obtain ⟨γ, hγ0, hγD, hγW⟩ := hU.exists_boundary_curve_of_inner_eq_zero hNormal hw
  have hD := hasDerivAt_comp_boundaryCurve hZ hNormal.1 hγ0 hγD hγW
  have hConst : (Z ∘ γ) =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := hγW.mono fun _ ht => hTrace ht
  have hZero := hD.unique ((hasDerivAt_const 0 (0 : S0)).congr_of_eventuallyEq hConst)
  rw [gradientFromColumns_closureGradient] at hZero
  change D (v - (inner ℝ v ν) • ν) = 0 at hZero
  rw [map_sub, map_smul] at hZero
  exact sub_eq_zero.mp hZero

/-- The wall derivative is controlled at the physical radius (t
ho).
The data bounds are the gradient and Laplacian of the trace extension.
The normal defect and the projected map are estimated separately. -/
theorem exists_scaled_physical_wall_derivative_bound
    (hPoisson : External.ZeroTraceBoundaryPoissonL4GradientEstimate)
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ R δ C : ℝ, 0 < R ∧ 0 < δ ∧ 0 < C ∧
      ∀ c ∈ frontier U, ∀ (t ρ : ℝ), 0 < t → 0 < ρ → t * ρ < R →
        ∀ (ε : ElasticScale) (Q b : Point → S0) (d E B₁ B₂ : ℝ),
          0 ≤ d → d < δ → 0 ≤ E → 0 ≤ B₁ → 0 ≤ B₂ →
          let r := t * ρ
          let D := U ∩ Metric.ball c r
          let G (y : Point) := gradientNormSq (ClassicalGradient Q y)
          ContDiffOn ℝ 2 Q (closure U) → ContDiffOn ℝ 2 b (closure U) →
          EqOn Q b (frontier U) → (∀ y ∈ frontier U, b y ∈ vacuum a) →
          (∀ y ∈ D, (ε : ℝ) ^ 2 • (↑(laplacian Q y) : Tensor) = bulkGradient a (Q y)) →
          (∀ y ∈ D, Metric.infDist (Q y) (vacuum a) ≤ d ∧ G y ≤ 8 / t ^ 2) →
          (∫⁻ y in D, ENNReal.ofReal (G y)) ≤ ENNReal.ofReal (4 * E * r) →
          (∀ y ∈ closure U ∩ Metric.ball c r, ∀ v : Point,
            ‖(fderivWithin ℝ b (closure U) y) v‖ ≤ B₁ * ‖v‖) →
          (∀ y ∈ D, ‖laplacian b y‖ ≤ B₂) →
          ∀ v : Point,
            t * ‖(fderivWithin ℝ Q (closure U) c) v‖ ≤
              C * (t * (B₁ + r * B₂) + d / ρ + Real.sqrt E / ρ +
                Real.sqrt (ρ * Real.sqrt E) + ρ) * ‖v‖ := by
  obtain ⟨p, δZ, C_Z, hδZ, hCZ, hδTp, hDefect⟩ := exists_regularized_vacuum_defect_laplacian_bound a
  obtain ⟨R₁, δP, C_P, N, hR₁, hδP, hCP, hN, hProj⟩ :=
    exists_projected_gradient_bound_on_physical_wall hPoisson a p hU
  obtain ⟨R₂, C_B, hR₂, hCB, hBarrier⟩ := hU.exists_wall_normalDerivative_bound_for_regularized_defect
  obtain ⟨ν, _, hNormal⟩ := hU.exists_smooth_outward_normal_extension
  let R := min R₁ R₂
  let δ := min δZ δP
  let κ := Real.pi * 4 / 3
  let K₄ := (2048 : ℝ) ^ (1 / 4 : ℝ)
  have hκ : 0 ≤ κ := by dsimp only [κ]; positivity
  have hκ₂ : 0 ≤ κ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hκ _
  have hκ₄ : 0 ≤ κ ^ (1 / 4 : ℝ) := Real.rpow_nonneg hκ _
  have hK₄ : 0 ≤ K₄ := Real.rpow_nonneg (by norm_num) _
  let L := 1 + C_P * (2 * N + κ ^ (1 / 2 : ℝ) + N * K₄ + κ ^ (1 / 4 : ℝ))
  let J := C_B * (1 + 8 * C_Z)
  let C := L + J
  have hL : 0 < L := by dsimp only [L]; positivity
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  refine ⟨R, δ, C, lt_min hR₁ hR₂, lt_min hδZ hδP, add_pos_of_pos_of_nonneg hL hJ, ?_⟩
  intro c hc t ρ ht hρ hr ε Q b d E B₁ B₂ hd hdδ hE hB₁ hB₂
  let r := t * ρ
  let D := U ∩ Metric.ball c r
  let V := closure U ∩ Metric.ball c r
  let G (y : Point) := gradientNormSq (ClassicalGradient Q y)
  change ContDiffOn ℝ 2 Q (closure U) → _ → _ → _ → _ → _ → _ → _ → _ → _
  intro hQ hb hTrace hVac hEuler hTube hMass hData hLapB v
  have hr₀ : 0 < r := mul_pos ht hρ
  have hr₁ : r < R₁ := hr.trans_le (min_le_left _ _)
  have hr₂ : r < R₂ := hr.trans_le (min_le_right _ _)
  have hD : IsOpen D := hU.1.1.inter Metric.isOpen_ball
  have hDCl : D ⊆ closure U := fun _ hy => subset_closure hy.1
  let P := p.extend ∘ Q
  let Z (y : Point) := Q y - P y
  have hP : ContDiffOn ℝ 2 P (closure U) :=
    (p.contDiff_extend.of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hQ
  have hZ : ContDiffOn ℝ 2 Z (closure U) := hQ.sub hP
  have hZTrace : EqOn Z (fun _ => 0) (frontier U) := by
    intro y hy
    have hV := hVac y hy
    have hTube' := vacuum_subset_vacuumTube a p.radius_pos hV
    change Q y - p.extend (Q y) = 0
    rw [hTrace hy, p.extend_eq ⟨b y, hTube'⟩, p.project_of_mem hV, sub_self]
  have hq (y : Point) (hy : y ∈ D) : Q y ∈ vacuumTube a δZ ∧ Q y ∈ vacuumTube a δP := by
    have h := (hTube y hy).1.trans_lt hdδ
    exact ⟨h.trans_le (min_le_left _ _), h.trans_le (min_le_right _ _)⟩
  have hNear (y : Point) (hy : y ∈ D) : ‖Z y‖ ≤ d := by
    have hTp : Q y ∈ vacuumTube a p.radius := (hq y hy).1.trans_le hδTp
    change ‖Q y - p.extend (Q y)‖ ≤ d
    rw [p.extend_eq ⟨Q y, hTp⟩, ← dist_eq_norm, p.dist_eq_infDist ⟨Q y, hTp⟩]
    exact (hTube y hy).1
  have hZClose : ContinuousOn Z (closure D) := hZ.continuousOn.mono (closure_mono inter_subset_left)
  have hZSup (x : Point) (hx : x ∈ closure D) : ‖Z x‖ ≤ d := by
    have hC : ContinuousWithinAt (fun y => ‖Z y‖) D x :=
      ((hZClose.norm) x hx).mono subset_closure
    exact closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact hNear y hy) isClosed_Iic
      (hC.mem_closure_image hx)
  let F := C_Z * (8 / t ^ 2)
  have hF : 0 ≤ F := mul_nonneg hCZ.le (by positivity)
  have hReg (η : ℝ) (hη : 0 < η) (x : Point) (hx : x ∈ D) :
      -laplacian (regularizedFrobeniusNorm η ∘ Z) x ≤ F :=
    (hDefect (ε : ℝ) η ε.2.1 hη D hD Q (hQ.mono hDCl) x hx (hq x hx).1 (hEuler x hx)).trans
      (mul_le_mul_of_nonneg_left (hTube x hx).2 hCZ.le)
  let DZ := fderivWithin ℝ Z (closure U) c
  have hcZ : HasFDerivWithinAt Z DZ (closure U) c :=
    ((hZ c (frontier_subset_closure hc)).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  have hn := hNormal c hc
  have hZν := hBarrier c hc r ⟨hr₀, hr₂⟩ (ν c) hn d F hd hF Z DZ hZClose
    (hZ.mono hDCl) hcZ (hZTrace.mono inter_subset_left) hZSup hReg
  have hZlhs : t * ‖DZ v‖ ≤ J * (d / ρ + ρ) * ‖v‖ := by
    have hEq := fderivWithin_apply_eq_normal_of_zero_wall hU hn (hZ.of_le (by norm_num)) hZTrace v
    have hAbs := abs_real_inner_le_norm v (ν c)
    rw [hn.2.1, mul_one] at hAbs
    change DZ v = (inner ℝ v (ν c)) • DZ (ν c) at hEq
    rw [hEq, norm_smul, Real.norm_eq_abs]
    have hScaled : t * ‖DZ (ν c)‖ ≤ C_B * (d / ρ + 8 * C_Z * ρ) := by
      refine (mul_le_mul_of_nonneg_left hZν ht.le).trans_eq ?_
      dsimp only [r, F]
      field_simp [ht.ne', hρ.ne']
    have hAmpl : C_B * (d / ρ + 8 * C_Z * ρ) ≤ J * (d / ρ + ρ) := by
      dsimp only [J]
      nlinarith only [mul_nonneg (mul_nonneg hCB.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hCZ.le))
        (div_nonneg hd hρ.le), mul_nonneg hCB.le hρ.le]
    calc
      _ ≤ t * (‖v‖ * ‖DZ (ν c)‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAbs (norm_nonneg _)) ht.le
      _ = (t * ‖DZ (ν c)‖) * ‖v‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hScaled.trans hAmpl) (norm_nonneg _)
  have hVolume : (volume.restrict D) univ ≤ ENNReal.ofReal (κ * r ^ 3) := by
    rw [Measure.restrict_apply_univ]
    calc
      _ ≤ volume (Metric.ball c r) := measure_mono inter_subset_right
      _ = _ := by rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hr₀.le,
        ← ENNReal.ofReal_mul (pow_nonneg hr₀.le 3), mul_comm (r ^ 3)]
  have hGpos (y : Point) : 0 ≤ G y := by
    change 0 ≤ gradientNormSq (ClassicalGradient Q y)
    rw [gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  let q (y : Point) := ‖laplacian b y‖
  have hGm : AEStronglyMeasurable G (volume.restrict D) :=
    (continuousOn_classicalGradientNormSq hD (hQ.mono hDCl)).aestronglyMeasurable hD.measurableSet
  have hqm : AEStronglyMeasurable q (volume.restrict D) :=
    ((continuousOn_laplacian_of_contDiffOn_two hD (hb.mono hDCl)).norm).aestronglyMeasurable hD.measurableSet
  obtain ⟨hG₂, hG₄, hq₄, hEnvelope⟩ := scaled_boundary_morrey_envelopes ht hρ hE hB₁ hB₂ hN
    hGm hqm ((ae_restrict_mem hD.measurableSet).mono fun y hy => ⟨hGpos y, (hTube y hy).2⟩)
    ((ae_restrict_mem hD.measurableSet).mono fun y hy => ⟨norm_nonneg _, hLapB y hy⟩) hMass hVolume
  have hPr := hProj c hc r ⟨hr₀, hr₁⟩ (ε : ℝ) ε.2.1 Q b B₁ hB₁
    (hQ.mono inter_subset_left) (hb.mono inter_subset_left) (hTrace.mono inter_subset_left)
    (fun x hx => hVac x hx.1) (fun x hx => ⟨(hq x hx).2, hEuler x hx⟩) hData
    hG₂ hG₄ hq₄ c ⟨hc, Metric.mem_ball_self (half_pos hr₀)⟩ v
  have hPscaled : t * ‖(fderivWithin ℝ P (closure U) c) v‖ ≤
      L * (t * (B₁ + r * B₂) + Real.sqrt E / ρ + Real.sqrt (ρ * Real.sqrt E)) * ‖v‖ := by
    let g₂ := (eLpNorm (fun x => N * Real.sqrt (G x) + B₁) 2 (volume.restrict D)).toReal
    let g₄ := (eLpNorm (fun x => N * G x + q x) 4 (volume.restrict D)).toReal
    let W := r ^ (-3 / 2 : ℝ) * g₂ + r ^ (1 / 4 : ℝ) * g₄
    change ‖(fderivWithin ℝ P (closure U) c) v‖ ≤ (B₁ + C_P * W) * ‖v‖ at hPr
    have hW : t * W ≤ (2 * N * Real.sqrt E / ρ + t * B₁ * κ ^ (1 / 2 : ℝ)) +
        (N * K₄ * Real.sqrt (ρ * Real.sqrt E) + t * r * B₂ * κ ^ (1 / 4 : ℝ)) := hEnvelope
    have hCoef : t * (B₁ + C_P * W) ≤
        L * (t * (B₁ + r * B₂) + Real.sqrt E / ρ + Real.sqrt (ρ * Real.sqrt E)) := by
      have hW' := mul_le_mul_of_nonneg_left hW hCP.le
      have h₁ : 1 + C_P * κ ^ (1 / 2 : ℝ) ≤ L := by
        dsimp only [L]
        nlinarith only [mul_nonneg hCP.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hN),
          mul_nonneg hCP.le (mul_nonneg hN hK₄), mul_nonneg hCP.le hκ₄]
      have h₂ : C_P * κ ^ (1 / 4 : ℝ) ≤ L := by
        dsimp only [L]
        nlinarith only [mul_nonneg hCP.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hN),
          mul_nonneg hCP.le (mul_nonneg hN hK₄), mul_nonneg hCP.le hκ₂]
      have h₃ : C_P * (2 * N) ≤ L := by
        dsimp only [L]
        nlinarith only [mul_nonneg hCP.le hκ₂, mul_nonneg hCP.le hκ₄, mul_nonneg hCP.le (mul_nonneg hN hK₄)]
      have h₄ : C_P * (N * K₄) ≤ L := by
        dsimp only [L]
        nlinarith only [mul_nonneg hCP.le hκ₂, mul_nonneg hCP.le hκ₄,
          mul_nonneg hCP.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hN)]
      have hB₁' := mul_le_mul_of_nonneg_right h₁ (mul_nonneg ht.le hB₁)
      have hB₂' := mul_le_mul_of_nonneg_right h₂ (mul_nonneg (mul_nonneg ht.le hr₀.le) hB₂)
      have hN₂' := mul_le_mul_of_nonneg_right h₃ (div_nonneg (Real.sqrt_nonneg E) hρ.le)
      have hN₄' := mul_le_mul_of_nonneg_right h₄ (Real.sqrt_nonneg (ρ * Real.sqrt E))
      calc
        _ = t * B₁ + C_P * (t * W) := by ring
        _ ≤ t * B₁ + C_P * ((2 * N * Real.sqrt E / ρ + t * B₁ * κ ^ (1 / 2 : ℝ)) +
            (N * K₄ * Real.sqrt (ρ * Real.sqrt E) + t * r * B₂ * κ ^ (1 / 4 : ℝ))) :=
          add_le_add le_rfl hW'
        _ = ((1 + C_P * κ ^ (1 / 2 : ℝ)) * (t * B₁) + C_P * κ ^ (1 / 4 : ℝ) * (t * r * B₂)) +
            (C_P * (2 * N) * (Real.sqrt E / ρ) + C_P * (N * K₄) * Real.sqrt (ρ * Real.sqrt E)) := by
          simp only [div_eq_mul_inv]
          ring
        _ ≤ (L * (t * B₁) + L * (t * r * B₂)) + (L * (Real.sqrt E / ρ) + L * Real.sqrt (ρ * Real.sqrt E)) :=
          add_le_add (add_le_add hB₁' hB₂') (add_le_add hN₂' hN₄')
        _ = _ := by ring
    calc
      _ ≤ t * ((B₁ + C_P * W) * ‖v‖) := mul_le_mul_of_nonneg_left hPr ht.le
      _ = (t * (B₁ + C_P * W)) * ‖v‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCoef (norm_nonneg _)
  have hcCl : c ∈ closure U := frontier_subset_closure hc
  have hsum := (((hZ c hcCl).differentiableWithinAt (by norm_num)).hasFDerivWithinAt.add
    ((hP c hcCl).differentiableWithinAt (by norm_num)).hasFDerivWithinAt).fderivWithin
      (hU.uniqueDiffOn_closure c hcCl)
  have hsum' : (fderivWithin ℝ Q (closure U) c) v = DZ v + (fderivWithin ℝ P (closure U) c) v := by
    have hEq : Z + P = Q := funext fun y => sub_add_cancel _ _
    rw [hEq] at hsum
    exact DFunLike.congr_fun hsum v
  rw [hsum']
  have h := mul_le_mul_of_nonneg_left (norm_add_le (DZ v) ((fderivWithin ℝ P (closure U) c) v)) ht.le
  have hSum := add_le_add hZlhs hPscaled
  have hTerms : 0 ≤ t * (B₁ + r * B₂) + Real.sqrt E / ρ + Real.sqrt (ρ * Real.sqrt E) := by positivity
  have hOther : 0 ≤ d / ρ + ρ := by positivity
  change _ ≤ (L + J) * (t * (B₁ + r * B₂) + d / ρ + Real.sqrt E / ρ +
    Real.sqrt (ρ * Real.sqrt E) + ρ) * ‖v‖
  nlinarith only [h, hSum, mul_nonneg (mul_nonneg hJ hTerms) (norm_nonneg v),
    mul_nonneg (mul_nonneg hL.le hOther) (norm_nonneg v)]

end Thesis

end
