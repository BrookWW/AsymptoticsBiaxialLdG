module

public import Thesis.Variational.BoundaryDefect
import Thesis.Variational.BoundaryBarrier
import Thesis.Foundation.LinearizedBulk

/-! Uniform scaled defect estimates for solutions with vacuum boundary values. -/

public section

open Set Topology
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius NNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

theorem screened_subsolution_le_constant
    {U : Set Point} (hU : IsOpen U) (hK : IsCompact (closure U)) {w : Point → ℝ}
    (hC : ContinuousOn w (closure U)) (hD : ContDiffOn ℝ 2 w U)
    {m B : ℝ} (hm : 0 < m)
    (hWall : ∀ x ∈ frontier U, w x ≤ B)
    (hPde : ∀ x ∈ U, -laplacian w x + m * w x ≤ m * B) :
    ∀ x ∈ closure U, w x ≤ B := by
  intro x hx
  obtain ⟨y, hy, hMax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hC
  refine (hMax hx).trans ?_
  by_cases hyU : y ∈ U
  · have hLoc : IsLocalMax w y := by
      filter_upwards [hU.mem_nhds hyU] with z hz
      exact hMax (subset_closure hz)
    have hLap := laplacian_nonpos_of_isLocalMax hU hD hyU hLoc
    exact le_of_mul_le_mul_left (by linarith only [hLap, hPde y hyU]) hm
  · exact hWall y (by rw [frontier, hU.interior_eq]; exact ⟨hy, hyU⟩)

/-- The positive bulk mass gives a global (O(arepsilon^2)) distance estimate
from a bound on the actual gradient and vacuum-valued boundary data. -/
theorem exists_scaled_vacuumDistance_bound_of_vacuum_boundary (a : BulkCoefficients) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (ε : ElasticScale) (U : Set Point), IsBoundedDomain U → ∀ Q : Point → S0,
        ContDiffOn ℝ 2 Q U → ContinuousOn Q (closure U) →
        MapsTo Q (frontier U) (vacuum a) → MapsTo Q U (vacuumTube a δ) →
        (∀ x ∈ U, ε.val ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) →
        ∀ L : ℝ, 0 ≤ L → (∀ x ∈ U, gradientNormSq (ClassicalGradient Q x) ≤ L) →
          ∀ x ∈ U, Metric.infDist (Q x) (vacuum a) ≤ C * ε.val ^ 2 * L := by
  obtain ⟨p, δ₀, c, K, hδ₀, hc, hK, hp, hScreened⟩ :=
    exists_regularized_vacuum_defect_screened_laplacian_bound a
  let δ := min δ₀ 1
  refine ⟨δ, K / c, lt_min hδ₀ zero_lt_one, min_le_right _ _, div_pos hK hc, ?_⟩
  intro ε U hU Q hQ hQcl hWall hTube hPde L hL hGrad x hx
  let Z (y : Point) := Q y - p.extend (Q y)
  let B := (K / c) * ε.val ^ 2 * L
  let m := c * ε.val⁻¹ ^ 2
  have hm : 0 < m := mul_pos hc (sq_pos_of_pos (inv_pos.mpr ε.2.1))
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (div_nonneg hK.le hc.le) (sq_nonneg _)) hL
  have hProd : m * B = K * L := by
    dsimp only [m, B]
    rw [inv_pow]
    field_simp [hc.ne', ε.2.1.ne']
  have hZcl : ContinuousOn Z (closure U) :=
    hQcl.sub (p.contDiff_extend.continuous.comp_continuousOn hQcl)
  have hZ₂ : ContDiffOn ℝ 2 Z U :=
    hQ.sub ((p.contDiff_extend.of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hQ)
  have hZbound (η : ℝ) (hη : 0 < η) : regularizedFrobeniusNorm η (Z x) ≤ B := by
    let w := regularizedFrobeniusNorm η ∘ Z
    have hw := contDiff_regularizedFrobeniusNorm hη
    have hwcl : ContinuousOn w (closure U) := hw.continuous.comp_continuousOn hZcl
    have hw2 : ContDiffOn ℝ 2 w U := (hw.of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hZ₂
    have hwWall (y : Point) (hy : y ∈ frontier U) : w y ≤ B := by
      have hVac := hWall hy
      have hFix : p.extend (Q y) = Q y :=
        (p.extend_eq ⟨Q y, vacuum_subset_vacuumTube a p.radius_pos hVac⟩).trans
          (congrArg Subtype.val (p.project_of_mem hVac))
      change regularizedFrobeniusNorm η (Q y - p.extend (Q y)) ≤ B
      rwa [hFix, sub_self, regularizedFrobeniusNorm_zero hη.le]
    have hwPde (y : Point) (hy : y ∈ U) : -laplacian w y + m * w y ≤ m * B := by
      have hTube' : Q y ∈ vacuumTube a δ₀ := (hTube hy).trans_le (min_le_left δ₀ 1)
      rw [hProd]
      exact (hScreened ε.val η ε.2.1 hη U hU.1 Q hQ y hy hTube' (hPde y hy)).trans
        (mul_le_mul_of_nonneg_left (hGrad y hy) hK.le)
    exact screened_subsolution_le_constant hU.1 hU.2.2.isCompact_closure hwcl hw2 hm hwWall hwPde
      x (subset_closure hx)
  have hz : ‖Z x‖ ≤ B := by
    by_contra hn
    have hη : 0 < (‖Z x‖ - B) / 2 := half_pos (sub_pos.mpr (lt_of_not_ge hn))
    have hw := hZbound _ hη
    have hNorm := (regularizedFrobeniusNorm_nonneg_le hη.le (Z x)).2.2
    linarith only [hw, hNorm, hη]
  have hInside : Q x ∈ vacuumTube a p.radius := (hTube hx).trans_le ((min_le_left δ₀ 1).trans hp)
  have hDist : ‖Z x‖ = Metric.infDist (Q x) (vacuum a) := by
    change ‖Q x - p.extend (Q x)‖ = _
    rw [← dist_eq_norm, p.extend_eq ⟨Q x, hInside⟩]
    exact p.dist_eq_infDist ⟨Q x, hInside⟩
  exact hDist ▸ hz

private theorem exists_material_defects_le_vacuumDistance (a : BulkCoefficients) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : S0, Metric.infDist A (vacuum a) ≤ 1 →
      ‖bulkForce a A‖ ≤ C * Metric.infDist A (vacuum a) ∧
      |((A : Tensor)^2).trace - 2 * vacuumRadius a ^ 2| ≤ C * Metric.infDist A (vacuum a) ∧
      |((A : Tensor)^3).trace| ≤ C * Metric.infDist A (vacuum a) ∧
      Real.sqrt (bulkPotential a A) ≤ C * Metric.infDist A (vacuum a) := by
  let R := Real.sqrt 2 * vacuumRadius a + 1
  let F (A : S0) := (bulkForce a A, vacuumInvariants A)
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) F :=
    (contDiff_bulkForce a).prodMk contDiff_vacuumInvariants
  obtain ⟨L, hL⟩ := hF.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : S0) R) (isCompact_closedBall _ _)
  obtain ⟨K, hK, hPot⟩ := exists_bulkPotential_local_upper a
  let C := (L : ℝ) + Real.sqrt K + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hLC : (L : ℝ) ≤ C := by dsimp only [C]; linarith only [Real.sqrt_nonneg K]
  have hKC : Real.sqrt K ≤ C := by dsimp only [C]; linarith only [L.coe_nonneg]
  refine ⟨C, hC, ?_⟩
  intro A hA
  let P := (spectralVacuumPoint a A).val
  let d := Metric.infDist A (vacuum a)
  have hP : P ∈ vacuum a := (spectralVacuumPoint a A).property
  have hd : ‖A - P‖ = d :=
    (dist_eq_norm A P).symm.trans (spectralVacuumPoint_dist_eq_infDist a A)
  have hA' : ‖A - P‖ ≤ 1 := hd.trans_le hA
  have hPR : ‖P‖ ≤ R := by
    rw [vacuum_norm hP]
    dsimp only [R]
    linarith
  have hAR : ‖A‖ ≤ R := by
    calc
      _ = ‖(A - P) + P‖ := by rw [sub_add_cancel]
      _ ≤ ‖A - P‖ + ‖P‖ := norm_add_le _ _
      _ ≤ R := by rw [vacuum_norm hP]; dsimp only [R]; linarith only [hA']
  have hLip := hL.dist_le_mul A (mem_closedBall_zero_iff.mpr hAR)
    P (mem_closedBall_zero_iff.mpr hPR)
  rcases vacuum_traces hP with ⟨hP₂, hP₃⟩
  have hFP : bulkForce a P = 0 := bulkForce_eq_zero_of_mem_vacuum hP
  have hF' : ‖F A - F P‖ ≤ C * d := by
    rw [dist_eq_norm, dist_eq_norm A P, hd] at hLip
    exact hLip.trans (mul_le_mul_of_nonneg_right hLC Metric.infDist_nonneg)
  have hNorm : ‖F A - F P‖ = max ‖bulkForce a A‖
      (max |((A : Tensor)^2).trace - 2 * vacuumRadius a ^ 2| |((A : Tensor)^3).trace|) := by
    change ‖((bulkForce a A, vacuumInvariants A) - (bulkForce a P, vacuumInvariants P))‖ = _
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, hFP, sub_zero,
      vacuumInvariants, hP₂, hP₃, Real.norm_eq_abs]
  rw [hNorm] at hF'
  refine ⟨(le_max_left _ _).trans hF', (le_max_left _ _).trans ((le_max_right _ _).trans hF'),
    (le_max_right _ _).trans ((le_max_right _ _).trans hF'), ?_⟩
  have hSqrt := Real.sqrt_le_sqrt (hPot P hP A hA')
  rw [Real.sqrt_mul hK.le, Real.sqrt_sq (norm_nonneg _), hd] at hSqrt
  exact hSqrt.trans (mul_le_mul_of_nonneg_right hKC Metric.infDist_nonneg)

theorem sum_scaledDefects_le_scaled_vacuumDistance (a : BulkCoefficients) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ElasticScale) (Q : Point → S0) (x : Point),
      Metric.infDist (Q x) (vacuum a) ≤ 1 →
      ε.val ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x) →
      ‖laplacian Q x‖ + (ε.val ^ 2)⁻¹ * Real.sqrt (bulkPotential a (Q x)) +
        |scaledNormDefect a ε (Q x)| + ‖scaledCubicDefect a ε (Q x)‖ ≤
          C * (ε.val ^ 2)⁻¹ * Metric.infDist (Q x) (vacuum a) := by
  obtain ⟨K, hK, hMat⟩ := exists_material_defects_le_vacuumDistance a
  let R := Real.sqrt 2 * vacuumRadius a + 1
  have hR : 0 ≤ R := by dsimp only [R]; have := (vacuumRadius_pos a).le; positivity
  let M := 3 + R / 2 + ‖(1 : Tensor)‖ / 3
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨M * K, mul_pos hM hK, ?_⟩
  intro ε Q x hd hEuler
  let A := Q x
  let d := Metric.infDist A (vacuum a)
  let s := (ε.val ^ 2)⁻¹
  let H := s * (K * d)
  have hs : 0 ≤ s := inv_nonneg.mpr (sq_nonneg _)
  obtain ⟨hForce, hNorm, hTrace, hPot⟩ := hMat A hd
  have hAR : ‖A‖ ≤ R := by
    let P := (spectralVacuumPoint a A).val
    have hP : P ∈ vacuum a := (spectralVacuumPoint a A).property
    have hAP : ‖A - P‖ = d :=
      (dist_eq_norm A P).symm.trans (spectralVacuumPoint_dist_eq_infDist a A)
    calc
      _ = ‖(A - P) + P‖ := by rw [sub_add_cancel]
      _ ≤ ‖A - P‖ + ‖P‖ := norm_add_le _ _
      _ ≤ R := by rw [hAP, vacuum_norm hP]; dsimp only [R]; linarith only [hd]
  have hΔ : laplacian Q x = s • bulkForce a A := by
    have hEq : ε.val ^ 2 • laplacian Q x = bulkForce a A := Subtype.ext hEuler
    rw [← hEq, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ ε.2.1.ne'), one_smul]
  have hL : ‖laplacian Q x‖ ≤ H := by
    rw [hΔ, norm_smul, Real.norm_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left hForce hs
  have hN : |scaledNormDefect a ε A| ≤ H := by
    change |s * (((A : Tensor)^2).trace - 2 * vacuumRadius a ^ 2)| ≤ H
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left hNorm hs
  have hT : |scaledCubicTrace a ε A| ≤ H := by
    rw [scaledCubicTrace_eq, abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left hTrace hs
  have hP : s * Real.sqrt (bulkPotential a A) ≤ H := mul_le_mul_of_nonneg_left hPot hs
  have hY : ‖scaledCubicDefect a ε A‖ ≤ H * (R / 2 + ‖(1 : Tensor)‖ / 3) := by
    rw [scaledCubicDefect_eq_scalar_parts]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    have h₁ := mul_le_mul (div_le_div_of_nonneg_right hN (by norm_num : (0 : ℝ) ≤ 2))
      hAR (norm_nonneg (A : Tensor)) (div_nonneg ((abs_nonneg _).trans hN) (by norm_num))
    have h₂ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hT (by norm_num : (0 : ℝ) ≤ 3))
      (norm_nonneg (1 : Tensor))
    exact (add_le_add h₁ h₂).trans_eq (by ring)
  calc
    _ ≤ H + H + H + H * (R / 2 + ‖(1 : Tensor)‖ / 3) :=
      add_le_add (add_le_add (add_le_add hL hP) hN) hY
    _ = (M * K) * (ε.val ^ 2)⁻¹ * d := by dsimp only [M, H, s]; ring

/-- Bounded gradient and vacuum boundary data control all of the scaled
defects and the unscaled Laplacian uniformly in the elastic parameter. -/
theorem exists_uniform_scaledDefect_bound_of_vacuum_boundary (a : BulkCoefficients) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (ε : ElasticScale) (U : Set Point), IsBoundedDomain U → ∀ Q : Point → S0,
        ContDiffOn ℝ 2 Q U → ContinuousOn Q (closure U) →
        MapsTo Q (frontier U) (vacuum a) → MapsTo Q U (vacuumTube a δ) →
        (∀ x ∈ U, ε.val ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) →
        ∀ L : ℝ, 0 ≤ L → (∀ x ∈ U, gradientNormSq (ClassicalGradient Q x) ≤ L) →
          ∀ x ∈ U,
            ‖laplacian Q x‖ + (ε.val ^ 2)⁻¹ * Real.sqrt (bulkPotential a (Q x)) +
              |scaledNormDefect a ε (Q x)| + ‖scaledCubicDefect a ε (Q x)‖ ≤ C * L := by
  obtain ⟨δ, K, hδ, hδ₁, hK, hDist⟩ := exists_scaled_vacuumDistance_bound_of_vacuum_boundary a
  obtain ⟨B, hB, hMat⟩ := sum_scaledDefects_le_scaled_vacuumDistance a
  refine ⟨δ, B * K, hδ, mul_pos hB hK, ?_⟩
  intro ε U hU Q hQ hQc hWall hTube hPde L hL hG x hx
  have hTube' : Metric.infDist (Q x) (vacuum a) < δ := hTube hx
  have hPre := hMat ε Q x (hTube'.le.trans hδ₁) (hPde x hx)
  have hD := hDist ε U hU Q hQ hQc hWall hTube hPde L hL hG x hx
  refine hPre.trans ((mul_le_mul_of_nonneg_left hD (mul_nonneg hB.le (inv_nonneg.mpr (sq_nonneg _)))).trans_eq ?_)
  field_simp [ε.2.1.ne']

end Thesis

end
