module

public import Thesis.Variational.ScaledDefectBound
import Thesis.Variational.BoundaryBarrier

/-! Interior positive-mass comparison for the true vacuum distance and the
scaled defects of the biaxial equation. -/

public section

open Set Topology Metric
open scoped ContDiff Matrix.Norms.Frobenius

noncomputable section

namespace Thesis

/-- A quadratic barrier bounds a screened subsolution at the center of a
cap with a prescribed quadratic envelope on its frontier. -/
theorem screened_subsolution_le_at_cap_center
    {V : Set Point} (hV : IsOpen V) {x : Point} {R m F M : ℝ}
    (hR : 0 < R) (hm : 0 < m) (hF : 0 ≤ F) (hM : 0 ≤ M)
    (hSub : V ⊆ ball x R) (hx : x ∈ closure V) {w : Point → ℝ}
    (hwC : ContinuousOn w (closure V)) (hw : ContDiffOn ℝ 2 w V)
    (hWall : ∀ y ∈ frontier V, w y ≤ (M / R ^ 2) * ‖y - x‖ ^ 2)
    (hPde : ∀ y ∈ V, -laplacian w y + m * w y ≤ F) :
    w x ≤ (F + 6 * M / R ^ 2) / m := by
  let A := M / R ^ 2
  let B := (F + 6 * M / R ^ 2) / m
  let f (y : Point) := w y - A • ‖y - x‖ ^ 2
  have hA : 0 ≤ A := div_nonneg hM (sq_pos_of_pos hR).le
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hSq : ContDiff ℝ 2 (fun y : Point => ‖y - x‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hf : ContDiffOn ℝ 2 f V := hw.sub (hSq.contDiffOn.const_smul A)
  have hFront (y : Point) (hy : y ∈ frontier V) : f y ≤ B :=
    (sub_nonpos.mpr (hWall y hy)).trans hB
  have hW (y : Point) (hy : y ∈ V) : -laplacian f y + m * f y ≤ m * B := by
    have hLap : laplacian f y = laplacian w y - A * 6 := by
      change laplacian (fun z => w z - A • ‖z - x‖ ^ 2) y = _
      rw [laplacian_sub_of_contDiffOn hV hw (hSq.contDiffOn.const_smul A) hy,
        laplacian_const_smul hV hSq.contDiffOn hy, laplacian_norm_sub_sq, smul_eq_mul]
    have hMass : m * B = F + 6 * A := by dsimp only [B, A]; field_simp
    have hAbs : 0 ≤ m * (A * ‖y - x‖ ^ 2) := by positivity
    change -laplacian f y + m * (w y - A * ‖y - x‖ ^ 2) ≤ m * B
    linarith only [hLap, hMass, hPde y hy, hAbs]
  have hK : IsCompact (closure V) := (isCompact_closedBall x R).of_isClosed_subset isClosed_closure
    (closure_minimal (hSub.trans ball_subset_closedBall) isClosed_closedBall)
  have hFC : ContinuousOn f (closure V) := hwC.sub (hSq.continuous.continuousOn.const_smul A)
  have hBound := screened_subsolution_le_constant hV hK hFC hf hm hFront hW x hx
  simpa only [f, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), smul_zero, sub_zero] using hBound

/-- The centered barrier on a full ball with a constant boundary bound. -/
theorem screened_subsolution_le_at_ball_center
    {Ω : Set Point} {x : Point} {R m F M : ℝ}
    (hR : 0 < R) (hm : 0 < m) (hF : 0 ≤ F) (hM : 0 ≤ M)
    (hBall : closedBall x R ⊆ Ω) {w : Point → ℝ} (hw : ContDiffOn ℝ 2 w Ω)
    (hWall : ∀ y ∈ sphere x R, w y ≤ M)
    (hPde : ∀ y ∈ ball x R, -laplacian w y + m * w y ≤ F) :
    w x ≤ (F + 6 * M / R ^ 2) / m := by
  have hC : closure (ball x R) = closedBall x R := closure_ball _ hR.ne'
  refine screened_subsolution_le_at_cap_center isOpen_ball hR hm hF hM subset_rfl
    (subset_closure (mem_ball_self hR)) (hw.continuousOn.mono (hC.symm ▸ hBall))
    (hw.mono (ball_subset_closedBall.trans hBall)) ?_ hPde
  intro y hy
  rw [frontier_ball _ hR.ne'] at hy
  have hy' : ‖y - x‖ = R := by rwa [mem_sphere, dist_eq_norm] at hy
  rw [hy', div_mul_cancel₀ _ (pow_ne_zero _ hR.ne')]
  exact hWall y hy

/-- A local bound on the classical gradient gives an order-ε²
bound on the true distance to the vacuum inside the half-radius ball. -/
theorem exists_scaled_vacuumDistance_bound_on_interior_ball (a : BulkCoefficients) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (ε : ElasticScale) (c : Point) (r : ℝ), 0 < r →
        ∀ Q : Point → S0, ContDiffOn ℝ 2 Q (ball c r) → MapsTo Q (ball c r) (vacuumTube a δ) →
          (∀ x ∈ ball c r, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x)) →
          ∀ G : ℝ, 0 ≤ G → (∀ x ∈ ball c r, gradientNormSq (ClassicalGradient Q x) ≤ G) →
            ∀ x ∈ ball c (r / 2), infDist (Q x) (vacuum a) ≤ C * (ε : ℝ) ^ 2 * (G + r⁻¹ ^ 2) := by
  obtain ⟨p, δ₀, k, K, hδ₀, hk, hK, hp, hScreen⟩ :=
    exists_regularized_vacuum_defect_screened_laplacian_bound a
  let δ := min δ₀ 1
  let C := (K + 24) / k
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨δ, C, lt_min hδ₀ zero_lt_one, min_le_right _ _, hC, ?_⟩
  intro ε c r hr Q hQ hTube hEq G hG hGrad x hx
  let U := ball c r
  let R := r / 2
  let m := k * (ε : ℝ)⁻¹ ^ 2
  let Z (y : Point) := Q y - p.extend (Q y)
  let B := (K * G + 6 * 1 / R ^ 2) / m
  have hε := ε.property.1
  have hm : 0 < m := mul_pos hk (sq_pos_of_pos (inv_pos.mpr hε))
  have hR : 0 < R := half_pos hr
  have hBall : closedBall x R ⊆ U := fun y hy => mem_ball.mpr (by
    have hxy : dist y x ≤ r / 2 := mem_closedBall.mp hy
    have hxc : dist x c < r / 2 := mem_ball.mp hx
    linarith only [dist_triangle y x c, hxy, hxc])
  have hDir (y : Point) (hy : y ∈ U) : ‖Z y‖ = infDist (Q y) (vacuum a) := by
    have hP : Q y ∈ vacuumTube a p.radius :=
      (hTube hy).trans_le ((min_le_left δ₀ 1).trans hp)
    change ‖Q y - p.extend (Q y)‖ = _
    rw [← dist_eq_norm, p.extend_eq ⟨Q y, hP⟩]
    exact p.dist_eq_infDist ⟨Q y, hP⟩
  have hZ : ContDiffOn ℝ 2 Z U :=
    hQ.sub ((p.contDiff_extend.of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hQ)
  have hηB (η : ℝ) (hη : 0 < η) : regularizedFrobeniusNorm η (Z x) ≤ B := by
    let w := regularizedFrobeniusNorm η ∘ Z
    have hw : ContDiffOn ℝ 2 w U :=
      ((contDiff_regularizedFrobeniusNorm hη).of_le (WithTop.coe_le_coe.mpr le_top)).comp_contDiffOn hZ
    have hWall (y : Point) (hy : y ∈ sphere x R) : w y ≤ 1 := by
      have hyU := hBall (sphere_subset_closedBall hy)
      exact (regularizedFrobeniusNorm_nonneg_le hη.le (Z y)).2.1.trans (by
        rw [hDir y hyU]
        exact (hTube hyU).le.trans (min_le_right δ₀ 1))
    have hPde (y : Point) (hy : y ∈ ball x R) : -laplacian w y + m * w y ≤ K * G := by
      have hyU := hBall (ball_subset_closedBall hy)
      have hT : Q y ∈ vacuumTube a δ₀ := (hTube hyU).trans_le (min_le_left δ₀ 1)
      exact (hScreen (ε : ℝ) η hε hη U isOpen_ball Q hQ y hyU hT (hEq y hyU)).trans
        (mul_le_mul_of_nonneg_left (hGrad y hyU) hK.le)
    exact screened_subsolution_le_at_ball_center hR hm (mul_nonneg hK.le hG) zero_le_one
      hBall hw hWall hPde
  have hNorm : ‖Z x‖ ≤ B := by
    by_contra! hNot
    have hη : 0 < (‖Z x‖ - B) / 2 := half_pos (sub_pos.mpr hNot)
    linarith only [hηB _ hη, (regularizedFrobeniusNorm_nonneg_le hη.le (Z x)).2.2, hNot]
  have hFormula : B = (ε : ℝ) ^ 2 / k * (K * G + 24 * r⁻¹ ^ 2) := by
    dsimp only [B, R, m]
    field_simp [hr.ne', hk.ne', hε.ne']
    ring
  have hxU := hBall (mem_closedBall_self hR.le)
  rw [hDir x hxU, hFormula] at hNorm
  calc
    _ ≤ _ := hNorm
    _ ≤ (ε : ℝ) ^ 2 / k * ((K + 24) * (G + r⁻¹ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (sq_nonneg _) hk.le)
      nlinarith only [mul_nonneg hK.le (sq_nonneg r⁻¹), hG]
    _ = _ := by dsimp only [C]; ring

/-- The interior scaled-defect bound for the actual Laplacian, bulk potential,
squared-trace error and cubic tensor defect, with one material constant. -/
theorem exists_uniform_scaledDefect_bound_on_interior_ball (a : BulkCoefficients) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (ε : ElasticScale) (c : Point) (r : ℝ), 0 < r →
        ∀ Q : Point → S0, ContDiffOn ℝ 2 Q (ball c r) → MapsTo Q (ball c r) (vacuumTube a δ) →
          (∀ x ∈ ball c r, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x)) →
          ∀ G : ℝ, 0 ≤ G → (∀ x ∈ ball c r, gradientNormSq (ClassicalGradient Q x) ≤ G) →
            ∀ x ∈ ball c (r / 2), ‖laplacian Q x‖ +
              ((ε : ℝ) ^ 2)⁻¹ * Real.sqrt (bulkPotential a (Q x)) +
              |scaledNormDefect a ε (Q x)| + ‖scaledCubicDefect a ε (Q x)‖ ≤ C * (G + r⁻¹ ^ 2) := by
  obtain ⟨δ, D, hδ, hδ', hD, hDistance⟩ := exists_scaled_vacuumDistance_bound_on_interior_ball a
  obtain ⟨C, hC, hDefect⟩ := sum_scaledDefects_le_scaled_vacuumDistance a
  refine ⟨δ, C * D, hδ, mul_pos hC hD, ?_⟩
  intro ε c r hr Q hQ hTube hEq G hG hGrad x hx
  have hxU := ball_subset_ball (half_le_self hr.le) hx
  have hDist := hDistance ε c r hr Q hQ hTube hEq G hG hGrad x hx
  have hD₁ : infDist (Q x) (vacuum a) ≤ 1 := (hTube hxU).le.trans hδ'
  refine (hDefect ε Q x hD₁ (hEq x hxU)).trans ?_
  have hE : ((ε : ℝ) ^ 2)⁻¹ * ((ε : ℝ) ^ 2) = 1 := inv_mul_cancel₀ (pow_ne_zero _ ε.2.1.ne')
  calc
    _ ≤ (C * ((ε : ℝ) ^ 2)⁻¹) * (D * (ε : ℝ) ^ 2 * (G + r⁻¹ ^ 2)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hDist
        (mul_nonneg hC.le (inv_nonneg.mpr (sq_nonneg (ε : ℝ))))
    _ = (C * D) * (((ε : ℝ) ^ 2)⁻¹ * ((ε : ℝ) ^ 2)) * (G + r⁻¹ ^ 2) := by ring
    _ = _ := by rw [hE, mul_one]

end Thesis

end
