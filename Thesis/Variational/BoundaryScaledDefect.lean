module

public import Thesis.Variational.InteriorScaledDefect
import Thesis.Variational.BoundaryPohozaev
import Thesis.Foundation.ModifiedSpectralGap
import Mathlib.Topology.Order.ExtrClosure

/-! Uniform normal defect estimates on caps with physical vacuum data. -/

public section

open Filter Set Topology
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

theorem exists_scaled_vacuumDistance_bound_at_cap_center (a : BulkCoefficients) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (ε : ElasticScale) {U : Set Point}, IsOpen U → ∀ (Q : Point → S0) (x : Point), x ∈ U →
        ∀ R : ℝ, 0 < R →
          let V := U ∩ Metric.ball x R
          ContDiffOn ℝ 2 Q V → ContinuousOn Q (closure V) →
          MapsTo Q (frontier U ∩ Metric.closedBall x R) (vacuum a) →
          MapsTo Q V (vacuumTube a δ) →
          (∀ y ∈ V, ε.val ^ 2 • (↑(laplacian Q y) : Tensor) = bulkGradient a (Q y)) →
          ∀ L : ℝ, 0 ≤ L → (∀ y ∈ V, gradientNormSq (ClassicalGradient Q y) ≤ L) →
            Metric.infDist (Q x) (vacuum a) ≤ C * ε.val ^ 2 * (L + R⁻¹ ^ 2) := by
  obtain ⟨p, δ₀, c, K, hδ₀, hc, hK, hTubeP, hScreened⟩ :=
    exists_regularized_vacuum_defect_screened_laplacian_bound a
  let δ := min δ₀ 1
  let C := max (K / c) (6 * δ / c)
  have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
  have hδ₁ : δ ≤ 1 := min_le_right _ _
  have hδp : δ ≤ p.radius := (min_le_left _ _).trans hTubeP
  have hC : 0 < C := (div_pos hK hc).trans_le (le_max_left _ _)
  refine ⟨δ, C, hδ, hδ₁, hC, ?_⟩
  intro ε U hU Q x hx R hR V hQ hQc hWall hTube hEq L hL hG
  have hV : IsOpen V := hU.inter Metric.isOpen_ball
  have hxV : x ∈ V := ⟨hx, Metric.mem_ball_self hR⟩
  let Z (y : Point) := Q y - p.extend (Q y)
  let m := c * ε.val⁻¹ ^ 2
  let B := (K * L + 6*δ/R^2) / m
  have hm : 0 < m := mul_pos hc (sq_pos_of_pos (inv_pos.mpr ε.2.1))
  have hZ (y : Point) (hy : y ∈ V) : ‖Z y‖ = Metric.infDist (Q y) (vacuum a) := by
    have hQy : Metric.infDist (Q y) (vacuum a) < δ := hTube hy
    have hp : Q y ∈ vacuumTube a p.radius := hQy.trans_le hδp
    change ‖Q y - p.extend (Q y)‖ = _
    rw [← dist_eq_norm, p.extend_eq ⟨Q y, hp⟩]
    exact p.dist_eq_infDist ⟨Q y, hp⟩
  have hZc : ContinuousOn Z (closure V) :=
    hQc.sub (p.contDiff_extend.continuous.comp_continuousOn hQc)
  have hZ₂ : ContDiffOn ℝ 2 Z V :=
    hQ.sub ((p.contDiff_extend.of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hQ)
  have hB (η : ℝ) (hη : 0 < η) : regularizedFrobeniusNorm η (Z x) ≤ B := by
    let w := regularizedFrobeniusNorm η ∘ Z
    have hw := contDiff_regularizedFrobeniusNorm hη
    have hwc : ContinuousOn w (closure V) := hw.continuous.comp_continuousOn hZc
    have hw₂ : ContDiffOn ℝ 2 w V := (hw.of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hZ₂
    have hwV (y : Point) (hy : y ∈ V) : w y ≤ δ :=
      (regularizedFrobeniusNorm_nonneg_le hη.le (Z y)).2.1.trans
        ((hZ y hy).trans_lt (show Metric.infDist (Q y) (vacuum a) < δ from hTube hy)).le
    have hwCl (y : Point) (hy : y ∈ closure V) : w y ≤ δ :=
      ContinuousWithinAt.closure_le hy ((hwc y hy).mono subset_closure) continuousWithinAt_const hwV
    have hW (y : Point) (hy : y ∈ frontier V) : w y ≤ (δ / R^2) * ‖y-x‖ ^ 2 := by
      have hSphere (hys : y ∈ Metric.sphere x R) : w y ≤ (δ / R^2) * ‖y-x‖ ^ 2 := by
        have hD : ‖y - x‖ = R := by
          rw [← dist_eq_norm]
          exact Metric.mem_sphere.mp hys
        rw [hD, div_mul_cancel₀ _ (pow_ne_zero _ hR.ne')]
        exact hwCl y (frontier_subset_closure hy)
      rcases frontier_slice_subset hU x hR hy with (hySphere | hyWall) | hySeam
      · exact hSphere hySphere.2
      · have hVac := hWall ⟨hyWall.1, Metric.ball_subset_closedBall hyWall.2⟩
        have hFix : p.extend (Q y) = Q y :=
          (p.extend_eq ⟨Q y, vacuum_subset_vacuumTube a p.radius_pos hVac⟩).trans
            (congrArg Subtype.val (p.project_of_mem hVac))
        change regularizedFrobeniusNorm η (Q y - p.extend (Q y)) ≤ _
        rw [hFix, sub_self, regularizedFrobeniusNorm_zero hη.le]
        positivity
      · exact hSphere hySeam.2
    have hwPde (y : Point) (hy : y ∈ V) : -laplacian w y + m * w y ≤ K * L := by
      have hTube' : Q y ∈ vacuumTube a δ₀ :=
        (show Metric.infDist (Q y) (vacuum a) < δ from hTube hy).trans_le (min_le_left δ₀ 1)
      exact (hScreened ε.val η ε.2.1 hη V hV Q hQ y hy hTube' (hEq y hy)).trans
        (mul_le_mul_of_nonneg_left (hG y hy) hK.le)
    exact screened_subsolution_le_at_cap_center hV hR hm (mul_nonneg hK.le hL) hδ.le
      inter_subset_right (subset_closure hxV) hwc hw₂ hW hwPde
  have hZB : ‖Z x‖ ≤ B := by
    by_contra hNot
    have hη : 0 < (‖Z x‖ - B) / 2 := half_pos (sub_pos.mpr (lt_of_not_ge hNot))
    have hNear := hB _ hη
    have hNorm := (regularizedFrobeniusNorm_nonneg_le hη.le (Z x)).2.2
    linarith only [hNear, hNorm, hη]
  calc
    _ = ‖Z x‖ := (hZ x hxV).symm
    _ ≤ B := hZB
    _ = ε.val ^ 2 * ((K/c) * L + (6*δ/c) * R⁻¹ ^ 2) := by
      dsimp only [B, m]
      rw [inv_pow, inv_pow]
      field_simp [hc.ne', hR.ne', ε.2.1.ne']
    _ ≤ C * ε.val ^ 2 * (L + R⁻¹ ^ 2) := by
      rw [mul_comm C, mul_assoc, mul_add C]
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hL)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))) (sq_nonneg _)

theorem exists_uniform_scaledDefect_bound_at_cap_center (a : BulkCoefficients) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (ε : ElasticScale) {U : Set Point}, IsOpen U → ∀ (Q : Point → S0) (x : Point), x ∈ U →
        ∀ R : ℝ, 0 < R →
          let V := U ∩ Metric.ball x R
          ContDiffOn ℝ 2 Q V → ContinuousOn Q (closure V) →
          MapsTo Q (frontier U ∩ Metric.closedBall x R) (vacuum a) →
          MapsTo Q V (vacuumTube a δ) →
          (∀ y ∈ V, ε.val ^ 2 • (↑(laplacian Q y) : Tensor) = bulkGradient a (Q y)) →
          ∀ L : ℝ, 0 ≤ L → (∀ y ∈ V, gradientNormSq (ClassicalGradient Q y) ≤ L) →
            ‖laplacian Q x‖ + (ε.val ^ 2)⁻¹ * Real.sqrt (bulkPotential a (Q x)) +
              |scaledNormDefect a ε (Q x)| + ‖scaledCubicDefect a ε (Q x)‖ ≤ C * (L + R⁻¹ ^ 2) := by
  obtain ⟨δ, B, hδ, hδ₁, hB, hDist⟩ := exists_scaled_vacuumDistance_bound_at_cap_center a
  obtain ⟨M, hM, hMat⟩ := sum_scaledDefects_le_scaled_vacuumDistance a
  refine ⟨δ, M * B, hδ, mul_pos hM hB, ?_⟩
  intro ε U hU Q x hx R hR V hQ hQc hWall hTube hEq L hL hG
  have hxV : x ∈ U ∩ Metric.ball x R := ⟨hx, Metric.mem_ball_self hR⟩
  have hDx := hDist ε hU Q x hx R hR hQ hQc hWall hTube hEq L hL hG
  have hT : Metric.infDist (Q x) (vacuum a) < δ := hTube hxV
  refine (hMat ε Q x (hT.le.trans hδ₁) (hEq x hxV)).trans
    ((mul_le_mul_of_nonneg_left hDx (mul_nonneg hM.le (inv_nonneg.mpr (sq_nonneg _)))).trans_eq ?_)
  field_simp [ε.2.1.ne']

/-- An eventual energy-density cap on a regular wall neighborhood gives
eventual uniform gradient and Laplacian bounds on the smaller neighborhood. -/
theorem exists_eventual_gradient_laplacian_bound_on_smaller_wall_neighborhood
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U) {c : Point} {r L : ℝ}
    (hr : 0 < r) (hL : 0 ≤ L)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ 2 (Q n) (closure U))
    (hWall : ∀ n, MapsTo (Q n) (frontier U) (vacuum a))
    (hEq : ∀ n, ∀ x ∈ U, (ε n : ℝ)^2 • (↑(laplacian (Q n) x) : Tensor) = bulkGradient a (Q n x))
    (hEnergy : ∀ᶠ n in atTop, ∀ x ∈ U ∩ Metric.ball c r,
      energyDensity a (ε n) (Q n x) (ClassicalGradient (Q n) x) ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ x ∈ U ∩ Metric.ball c (r / 2),
      ‖laplacian (Q n) x‖ + gradientNormSq (ClassicalGradient (Q n) x) ≤ C := by
  obtain ⟨δ, K, hδ, hK, hDefect⟩ := exists_uniform_scaledDefect_bound_at_cap_center a
  obtain ⟨b, hb, hBulk⟩ := exists_bulkPotential_ge_global_vacuumDist_sq a
  let R := r / 2
  let M := K * (2 * L + R⁻¹ ^ 2)
  have hR : 0 < R := half_pos hr
  have hSmall : ∀ᶠ n in atTop, (ε n : ℝ)^2 * L < b * δ^2 := by
    have h := (hε.pow 2).mul_const L
    rw [zero_pow two_ne_zero, zero_mul] at h
    exact h.eventually_lt_const (mul_pos hb (sq_pos_of_pos hδ))
  refine ⟨M + 2*L, add_nonneg (mul_nonneg hK.le (add_nonneg (by positivity) (sq_nonneg _)))
    (by positivity), ?_⟩
  filter_upwards [hEnergy, hSmall] with n hn hs x hx
  have hIn (y : Point) (hy : y ∈ U ∩ Metric.ball x R) : y ∈ U ∩ Metric.ball c r := by
    refine ⟨hy.1, ?_⟩
    have hDy : dist y x < R := hy.2
    have hDx : dist x c < r / 2 := hx.2
    exact (dist_triangle y x c).trans_lt (by dsimp only [R] at hDy; linarith only [hDy, hDx])
  have hGrad (y : Point) (hy : y ∈ U ∩ Metric.ball c r) :
      gradientNormSq (ClassicalGradient (Q n) y) ≤ 2 * L := by
    have hNonneg : 0 ≤ (ε n : ℝ)⁻¹^2 * bulkPotential a (Q n y) :=
      mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _)
    have h := hn y hy
    unfold energyDensity at h
    linarith only [h, hNonneg]
  have hTube (y : Point) (hy : y ∈ U ∩ Metric.ball x R) : (Q n) y ∈ vacuumTube a δ := by
    have h := hn y (hIn y hy)
    unfold energyDensity at h
    have hg : 0 ≤ gradientNormSq (ClassicalGradient (Q n) y) := by
      rw [gradientNormSq_eq_sum_norm_sq]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hFB : (ε n : ℝ)⁻¹^2 * bulkPotential a (Q n y) ≤ L := by linarith only [h, hg]
    have hFB' : bulkPotential a (Q n y) ≤ (ε n : ℝ)^2 * L := by
      have hScale : (ε n : ℝ)^2 * (ε n : ℝ)⁻¹^2 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (ε n).2.1.ne', one_pow]
      have h := mul_le_mul_of_nonneg_left hFB (sq_nonneg (ε n : ℝ))
      rwa [← mul_assoc, hScale, one_mul] at h
    have hSmall := ((hBulk (Q n y)).trans hFB').trans_lt hs
    change Metric.infDist (Q n y) (vacuum a) < δ
    exact (sq_lt_sq₀ Metric.infDist_nonneg hδ.le).mp (lt_of_mul_lt_mul_left hSmall hb.le)
  have hDef := hDefect (ε n) hU (Q n) x hx.1 R hR
    ((hQ n).mono (inter_subset_left.trans subset_closure))
    ((hQ n).continuousOn.mono (closure_mono inter_subset_left))
    ((hWall n).mono_left inter_subset_left) hTube (fun y hy => hEq n y hy.1)
    (2 * L) (by positivity) (fun y hy => hGrad y (hIn y hy))
  have hLap : ‖laplacian (Q n) x‖ ≤ M := by
    have hp := mul_nonneg (inv_nonneg.mpr (sq_nonneg ((ε n : ℝ)))) (Real.sqrt_nonneg (bulkPotential a (Q n x)))
    dsimp only [M]
    linarith only [hDef, hp, abs_nonneg (scaledNormDefect a (ε n) (Q n x)),
      norm_nonneg (scaledCubicDefect a (ε n) (Q n x))]
  exact add_le_add hLap (hGrad x ⟨hx.1, (Metric.ball_subset_ball (half_lt_self hr).le) hx.2⟩)

end Thesis

end
