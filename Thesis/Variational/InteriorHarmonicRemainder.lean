module

public import Thesis.Variational.InteriorBiaxialBootstrap
public import Thesis.Variational.ProjectedHarmonicRemainder
public import Thesis.Variational.InteriorRegularityBounds
public import Thesis.Variational.WeightedInteriorDerivatives

/-! The full interior harmonic-map remainder, including the scalar
identity component. -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Thesis

/-- Every differentiated screened correction has the same factor of the
elastic scale squared on the smaller ball. -/
theorem screened_coordinateDerivative_le_scaleSq {c : Point} {r ρ ε m A B : ℝ}
    (hρr : ρ < r) (hε : 0 < ε) (hm : 0 < m) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {w F : Point → ℝ} (hw : ContDiffOn ℝ ∞ w (ball c r)) (hF : ContDiffOn ℝ ∞ F (ball c r))
    (hEq : ∀ y ∈ ball c r, -ε ^ 2 * laplacian w y + m * w y = ε ^ 2 * F y)
    (k : ℕ) (i : Fin k → Fin 3)
    (hwB : ∀ y ∈ ball c r, |iteratedCoordinateDerivative k i w y| ≤ B)
    (hFA : ∀ y ∈ ball c r, |iteratedCoordinateDerivative k i F y| ≤ A) :
    ∀ x ∈ ball c ρ, |iteratedCoordinateDerivative k i w x| ≤
      ε ^ 2 * (A / m + 6 * B / (m * ((r - ρ) / 2) ^ 2)) := by
  let R := (r - ρ) / 2
  have hR : 0 < R := half_pos (sub_pos.mpr hρr)
  have hb (x : Point) (hx : x ∈ ball c ρ) : closedBall x R ⊆ ball c r :=
    fun y hy => mem_ball.mpr (by
      have hy' : dist y x ≤ (r - ρ) / 2 := mem_closedBall.mp hy
      linarith only [hy', mem_ball.mp hx, dist_triangle y x c, hρr])
  let v := iteratedCoordinateDerivative k i w
  let G := iteratedCoordinateDerivative k i F
  let U := ball c r
  have hv : ContDiffOn ℝ ∞ v U := contDiffOn_iteratedCoordinateDerivative isOpen_ball hw k i
  have hE : EqOn (fun y => (-ε ^ 2) • laplacian w y + m • w y) (fun y => ε ^ 2 • F y) U :=
    fun y hy => hEq y hy
  have hDE (y : Point) (hy : y ∈ U) : -ε ^ 2 * laplacian v y + m * v y = ε ^ 2 * G y := by
    have hDiff := iteratedCoordinateDerivative_congr_open isOpen_ball hE k i hy
    have hL := contDiffOn_classical_laplacian_infty isOpen_ball hw
    rw [iteratedCoordinateDerivative_add isOpen_ball (hL.const_smul _) (hw.const_smul _) k i hy,
      iteratedCoordinateDerivative_const_smul isOpen_ball hL _ k i hy,
      iteratedCoordinateDerivative_const_smul isOpen_ball hw _ k i hy,
      iteratedCoordinateDerivative_const_smul isOpen_ball hF _ k i hy,
      ← laplacian_iteratedCoordinateDerivative_scalar isOpen_ball hw k i hy] at hDiff
    exact hDiff
  intro x hx
  have hWall (y : Point) (hy : y ∈ sphere x R) : |v y| ≤ B :=
    hwB y (hb x hx (sphere_subset_closedBall hy))
  have hPde (y : Point) (hy : y ∈ ball x R) : |-ε ^ 2 * laplacian v y + m * v y| ≤ ε ^ 2 * A := by
    have hyU := hb x hx (ball_subset_closedBall hy)
    rw [hDE y hyU, abs_mul, abs_of_nonneg (sq_nonneg ε)]
    exact mul_le_mul_of_nonneg_left (hFA y hyU) (sq_nonneg _)
  have hComp := screened_solution_abs_le_at_ball_center isOpen_ball hR (sq_pos_of_pos hε) hm
    (mul_nonneg (sq_nonneg ε) hA) hB (hb x hx) ((contDiffOn_infty.mp hv) 2) hWall hPde
  change |v x| ≤ _
  calc
    _ ≤ ε ^ 2 * A / m + B * min 1 (6 * ε ^ 2 / (m * R ^ 2)) := hComp
    _ ≤ ε ^ 2 * A / m + B * (6 * ε ^ 2 / (m * R ^ 2)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (min_le_right _ _) hB)
    _ = _ := by dsimp only [R]; ring

private abbrev InteriorBiaxialState := ℝ × S0 × Gradient × ScalarDefectPair

private def interiorBiaxialState (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0)
    (x : Point) : InteriorBiaxialState :=
  ((ε : ℝ) ^ 2, Q x, ClassicalGradient Q x, scalarDefectPair a ε (Q x))

private theorem contDiffOn_interiorBiaxialState (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω) :
    ContDiffOn ℝ ∞ (interiorBiaxialState a ε Q) Ω :=
  contDiffOn_const.prodMk (hQ.prodMk
    ((contDiffOn_pi.mpr (contDiffOn_coordDeriv_infty hΩ hQ)).prodMk
      ((contDiff_scalarDefectPair a ε).comp_contDiffOn hQ)))

private theorem exists_weighted_interiorBiaxialState_bounds (a : BulkCoefficients)
    (hEstimate : InteriorPoissonGradientEstimate) (j : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (r t d : ℝ), 0 < t → t < r → 0 < d → d ≤ 1 → d ≤ r - t →
      ∀ (ε : ElasticScale) (c : Point) (Q : Point → S0),
      ContDiffOn ℝ ∞ Q (ball c r) →
      (∀ y ∈ ball c r, (ε : ℝ) ^ 2 • (laplacian Q y : S0).val = bulkGradient a (Q y)) →
      (∀ y ∈ ball c r, |scaledNormDefect a ε (Q y)| ≤ C₀ ∧ |scaledCubicTrace a ε (Q y)| ≤ C₀ ∧
        Real.sqrt (gradientNormSq (ClassicalGradient Q y)) ≤ C₀) →
      ∀ x ∈ ball c t, ∀ k ≤ j, ∀ i : Fin k → Fin 3,
        ‖iteratedCoordinateDerivative k i (interiorBiaxialState a ε Q) x‖ ≤ C * d⁻¹ ^ k := by
  classical
  have hA (k : Fin (j + 1)) := exists_interior_classical_biaxial_derivative_bound a hEstimate k.val C₀ hC₀
  choose A hApos hEst using hA
  let R₀ := Real.sqrt (2 * vacuumRadius a ^ 2 + C₀)
  let B (k : Fin (j + 1)) := 2 * A k
  let C := 1 + R₀ + ∑ k : Fin (j + 1), B k
  have hB (k : Fin (j + 1)) : 0 ≤ B k := mul_nonneg (by norm_num) (hApos k).le
  have hSum : 0 ≤ ∑ k : Fin (j + 1), B k := Finset.sum_nonneg fun k _ => hB k
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hSum, Real.sqrt_nonneg (2 * vacuumRadius a ^ 2 + C₀)]
  have hBC (k : Fin (j + 1)) : B k ≤ C :=
    (Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ k)).trans
      (le_add_of_nonneg_left (by dsimp only [R₀]; positivity))
  refine ⟨C, hC, ?_⟩
  intro r t d ht htr hd hd₁ hdGap ε c Q hQ hEuler hBase x hx k hk i
  let Ω := ball c r
  let w (y : Point) := scalarDefectPair a ε (Q y)
  let b := (ε : ℝ) ^ 2
  have hxΩ : x ∈ Ω := ball_subset_ball htr.le hx
  have hInv : 1 ≤ d⁻¹ := (one_le_inv₀ hd).2 hd₁
  have hPow (n : ℕ) : 1 ≤ d⁻¹ ^ n := one_le_pow₀ hInv
  have hD (l : ℕ) (hl : l ≤ j) :
      ‖iteratedFDeriv ℝ l (scaledNormDefect a ε ∘ Q) x‖ +
        ‖iteratedFDeriv ℝ l (scaledCubicTrace a ε ∘ Q) x‖ +
        ‖iteratedFDeriv ℝ (l + 1) Q x‖ ≤ C * d⁻¹ ^ l := by
    let l' : Fin (j + 1) := ⟨l, Nat.lt_succ_of_le hl⟩
    have hPower : (r - t)⁻¹ ^ l ≤ d⁻¹ ^ l :=
      pow_le_pow_left₀ (inv_nonneg.mpr (sub_nonneg.mpr htr.le))
        ((inv_le_inv₀ (sub_pos.mpr htr) hd).2 hdGap) l
    calc
      _ ≤ A l' * (1 + (r - t)⁻¹ ^ l) := hEst l' ε c r t ht htr Q hQ hEuler hBase x hx
      _ ≤ A l' * (d⁻¹ ^ l + d⁻¹ ^ l) :=
        mul_le_mul_of_nonneg_left (add_le_add (hPow l) hPower) (hApos l').le
      _ = B l' * d⁻¹ ^ l := by dsimp only [B]; ring
      _ ≤ C * d⁻¹ ^ l := mul_le_mul_of_nonneg_right (hBC l') (zero_le_one.trans (hPow l))
  have hP : ContDiffOn ℝ ∞ (ClassicalGradient Q) Ω :=
    contDiffOn_pi.mpr (contDiffOn_coordDeriv_infty isOpen_ball hQ)
  have hw : ContDiffOn ℝ ∞ w Ω := (contDiff_scalarDefectPair a ε).comp_contDiffOn hQ
  have hC₀' : 0 ≤ C := zero_le_one.trans hC
  have hCk : 0 ≤ C * d⁻¹ ^ k := mul_nonneg hC₀' (zero_le_one.trans (hPow k))
  have hβ : 0 ≤ b ∧ b ≤ 1 := ⟨sq_nonneg _, (pow_le_pow_left₀ ε.2.1.le ε.2.2.le 2).trans_eq (one_pow 2)⟩
  have hβC : ‖b‖ ≤ C := by rw [Real.norm_of_nonneg hβ.1]; exact hβ.2.trans hC
  have hQd : ‖iteratedCoordinateDerivative k i Q x‖ ≤ C * d⁻¹ ^ k := by
    cases k with
    | zero =>
        have h : ‖Q x‖ ≤ R₀ := by
          apply Real.le_sqrt_of_sq_le
          rw [norm_sq_eq_trace_sq, trace_sq_eq_scaledNormDefect a ε (Q x)]
          have hh : scaledNormDefect a ε (Q x) ≤ C₀ := (le_abs_self _).trans (hBase x hxΩ).1
          exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left hh hβ.1).trans
            (mul_le_of_le_one_left hC₀ hβ.2))
        change ‖Q x‖ ≤ C * d⁻¹ ^ (0 : ℕ)
        simpa only [pow_zero, mul_one] using h.trans (show R₀ ≤ C by
          dsimp only [C]
          linarith only [hSum])
    | succ l =>
        have h := hD l (Nat.le_of_succ_le hk)
        have hQ' : ‖iteratedFDeriv ℝ (l + 1) Q x‖ ≤ C * d⁻¹ ^ l := by
          linarith only [h, norm_nonneg (iteratedFDeriv ℝ l (scaledNormDefect a ε ∘ Q) x),
            norm_nonneg (iteratedFDeriv ℝ l (scaledCubicTrace a ε ∘ Q) x)]
        exact (norm_coordinateDerivative_le_norm_iteratedFDeriv isOpen_ball hQ _ i hxΩ).trans
          (hQ'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hInv (Nat.le_succ _)) hC₀'))
  have hPd : ‖iteratedCoordinateDerivative k i (ClassicalGradient Q) x‖ ≤ C * d⁻¹ ^ k := by
    apply norm_coordinateDerivative_pi_le isOpen_ball hP k i hxΩ hCk
    intro l
    have h := hD k hk
    have hQ' : ‖iteratedFDeriv ℝ (k + 1) Q x‖ ≤ C * d⁻¹ ^ k := by
      linarith only [h, norm_nonneg (iteratedFDeriv ℝ k (scaledNormDefect a ε ∘ Q) x),
        norm_nonneg (iteratedFDeriv ℝ k (scaledCubicTrace a ε ∘ Q) x)]
    change ‖iteratedCoordinateDerivative k i (coordDeriv l Q) x‖ ≤ C * d⁻¹ ^ k
    rw [← iteratedCoordinateDerivative_snoc k i l Q]
    exact (norm_coordinateDerivative_le_norm_iteratedFDeriv isOpen_ball hQ _ _ hxΩ).trans hQ'
  have hWd : ‖iteratedCoordinateDerivative k i w x‖ ≤ C * d⁻¹ ^ k := by
    apply norm_coordinateDerivative_pi_le isOpen_ball hw k i hxΩ hCk
    intro l
    have h := hD k hk
    fin_cases l
    · have hhs : ContDiffOn ℝ ∞ (scaledNormDefect a ε ∘ Q) Ω :=
        contDiffOn_pi.mp hw (0 : Fin 2)
      have hH : ‖iteratedFDeriv ℝ k (scaledNormDefect a ε ∘ Q) x‖ ≤ C * d⁻¹ ^ k := by
        linarith only [h, norm_nonneg (iteratedFDeriv ℝ (k + 1) Q x),
          norm_nonneg (iteratedFDeriv ℝ k (scaledCubicTrace a ε ∘ Q) x)]
      exact (norm_coordinateDerivative_le_norm_iteratedFDeriv isOpen_ball hhs k i hxΩ).trans hH
    · have hts : ContDiffOn ℝ ∞ (scaledCubicTrace a ε ∘ Q) Ω :=
        contDiffOn_pi.mp hw (1 : Fin 2)
      have hT : ‖iteratedFDeriv ℝ k (scaledCubicTrace a ε ∘ Q) x‖ ≤ C * d⁻¹ ^ k := by
        linarith only [h, norm_nonneg (iteratedFDeriv ℝ (k + 1) Q x),
          norm_nonneg (iteratedFDeriv ℝ k (scaledNormDefect a ε ∘ Q) x)]
      exact (norm_coordinateDerivative_le_norm_iteratedFDeriv isOpen_ball hts k i hxΩ).trans hT
  exact norm_coordDerivative_pair_le isOpen_ball contDiffOn_const
    (hQ.prodMk (hP.prodMk hw)) k i hxΩ
    ((norm_coordDerivative_const_le hC₀' hβC k i x).trans
      (le_mul_of_one_le_right hC₀' (hPow k)))
    (norm_coordDerivative_pair_le isOpen_ball hQ (hP.prodMk hw) k i hxΩ hQd
      (norm_coordDerivative_pair_le isOpen_ball hP hw k i hxΩ hPd hWd))

private def interiorDefectData (a : BulkCoefficients) (l : Fin 2) (z : InteriorBiaxialState) : ℝ × ℝ × ℝ :=
  let b := biaxialGradientSource (z.2.1, z.2.2.1) l
  (z.2.2.2 l - b / scalarDefectMass a l, b, biaxialDefectCorrection a (z.1, z.2.2.2) l)

private theorem contDiff_interiorDefectData (a : BulkCoefficients) (l : Fin 2) :
    ContDiff ℝ ∞ (interiorDefectData a l) := by
  let L : ScalarDefectPair →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) l
  have hA : ContDiff ℝ ∞ (fun z : InteriorBiaxialState => z.2.1) := contDiff_snd.fst
  have hD : ContDiff ℝ ∞ (fun z : InteriorBiaxialState => z.2.2.1) := contDiff_snd.snd.fst
  have hW : ContDiff ℝ ∞ (fun z : InteriorBiaxialState => z.2.2.2) := contDiff_snd.snd.snd
  have hB : ContDiff ℝ ∞ (fun z : InteriorBiaxialState => biaxialGradientSource (z.2.1, z.2.2.1) l) :=
    L.contDiff.comp (contDiff_biaxialGradientSource.comp (hA.prodMk hD))
  have hC : ContDiff ℝ ∞ (fun z : InteriorBiaxialState => biaxialDefectCorrection a (z.1, z.2.2.2) l) :=
    L.contDiff.comp ((contDiff_biaxialDefectCorrection a).comp (contDiff_fst.prodMk hW))
  have hDiv : ContDiff ℝ ∞ (fun z : InteriorBiaxialState =>
      biaxialGradientSource (z.2.1, z.2.2.1) l / scalarDefectMass a l) := by
    simp only [div_eq_mul_inv]
    exact hB.mul contDiff_const
  exact ((L.contDiff.comp hW).sub hDiv).prodMk (hB.prodMk hC)

private def normalizedAdjustedDefectPair (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0)
    (x : Point) : ScalarDefectPair :=
  fun l => ((ε : ℝ) ^ 2)⁻¹ * (interiorDefectData a l (interiorBiaxialState a ε Q x)).1

private theorem interiorDefectData_adjusted (a : BulkCoefficients) (ε : ElasticScale)
    (Q : Point → S0) (x : Point) :
    (interiorDefectData a 0 (interiorBiaxialState a ε Q x)).1 = adjustedNormDefect a ε Q x ∧
    (interiorDefectData a 1 (interiorBiaxialState a ε Q x)).1 = adjustedCubicDefect a ε Q x := by
  have hRad : bulkRadialCoefficient a ≠ 0 := (bulkRadialCoefficient_pos a).ne'
  have ha6 : a.a6' ≠ 0 := a.a6'_pos.ne'
  have hr : vacuumRadius a ≠ 0 := (vacuumRadius_pos a).ne'
  constructor
  · change scaledNormDefect a ε (Q x) -
      (-2 * gradientNormSq (ClassicalGradient Q x)) / bulkRadialMass a =
        scaledNormDefect a ε (Q x) +
          (1 / (2 * bulkRadialCoefficient a * vacuumRadius a ^ 2)) * gradientNormSq (ClassicalGradient Q x)
    rw [bulkRadialMass]
    field_simp [hRad, hr]
    ring
  · let G := cubicGradientContraction (Q x) (ClassicalGradient Q x)
    change scaledCubicTrace a ε (Q x) - (-6 * G) / bulkBiaxialMass a =
      scaledCubicTrace a ε (Q x) + (3 / (a.a6' * vacuumRadius a ^ 4)) * G
    rw [bulkBiaxialMass]
    field_simp [ha6, hr]
    ring

private theorem contDiffOn_normalizedAdjustedDefectPair (a : BulkCoefficients) (ε : ElasticScale)
    {Q : Point → S0} {U : Set Point} (hU : IsOpen U) (hQ : ContDiffOn ℝ ∞ Q U) :
    ContDiffOn ℝ ∞ (normalizedAdjustedDefectPair a ε Q) U := by
  apply contDiffOn_pi.mpr
  intro l
  exact contDiffOn_const.mul
    (((contDiff_interiorDefectData a l).comp_contDiffOn (contDiffOn_interiorBiaxialState a ε hU hQ)).fst)

private theorem interiorDefectData_screened (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hEuler : ∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x))
    (l : Fin 2) {x : Point} (hx : x ∈ Ω) :
    let f := interiorDefectData a l ∘ interiorBiaxialState a ε Q
    let m := scalarDefectMass a l;
    -(ε : ℝ) ^ 2 * laplacian (fun y => (f y).1) x + m * (f x).1 =
      (ε : ℝ) ^ 2 * ((f x).2.2 + m⁻¹ * laplacian (fun y => (f y).2.1) x) := by
  let f := interiorDefectData a l ∘ interiorBiaxialState a ε Q
  let W (y : Point) := scalarDefectPair a ε (Q y) l
  let B (y : Point) := (f y).2.1
  let C (y : Point) := (f y).2.2
  let m := scalarDefectMass a l
  have hm : 0 < m := (lt_min (bulkRadialMass_pos a) (bulkBiaxialMass_pos a)).trans_le (scalarDefectMass_lower a l)
  have hW : ContDiffOn ℝ ∞ W Ω :=
    contDiffOn_pi.mp ((contDiff_scalarDefectPair a ε).comp_contDiffOn hQ) l
  have hB : ContDiffOn ℝ ∞ B Ω :=
    ((contDiff_interiorDefectData a l).comp_contDiffOn (contDiffOn_interiorBiaxialState a ε hΩ hQ)).snd.fst
  have hRaw := (classical_biaxial_poisson_screened_system a ε hΩ ((contDiffOn_infty.mp hQ) 2) hx
    (hEuler x hx)).2 l
  change -(ε : ℝ) ^ 2 * laplacian W x + m * W x = B x + (ε : ℝ) ^ 2 * C x at hRaw
  have hFun : (fun y => (f y).1) = fun y => W y - m⁻¹ • B y := by
    funext y
    change W y - B y / m = W y - m⁻¹ * B y
    rw [div_eq_mul_inv, mul_comm]
  have hW₂ := (contDiffOn_infty.mp hW) 2
  have hB₂ := (contDiffOn_infty.mp hB) 2
  change -(ε : ℝ) ^ 2 * laplacian (fun y => (f y).1) x + m * (f x).1 =
    (ε : ℝ) ^ 2 * (C x + m⁻¹ * laplacian B x)
  rw [hFun, laplacian_sub_of_contDiffOn hΩ hW₂ (hB₂.const_smul _) hx,
    laplacian_const_smul hΩ hB₂ hx, smul_eq_mul]
  have hPoint : (f x).1 = W x - m⁻¹ * B x := congrFun hFun x
  rw [hPoint, mul_sub m, ← mul_assoc m, mul_inv_cancel₀ hm.ne', one_mul]
  linarith only [hRaw]

private theorem abs_coordinateDerivative_laplacian_le {U : Set Point} (hU : IsOpen U)
    {f : Point → ℝ} (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) (i : Fin k → Fin 3)
    {x : Point} (hx : x ∈ U) {M : ℝ}
    (hM : ∀ v : Fin (k + 2) → Fin 3, |iteratedCoordinateDerivative (k + 2) v f x| ≤ M) :
    |iteratedCoordinateDerivative k i (laplacian f) x| ≤ 3 * M := by
  rw [← laplacian_iteratedCoordinateDerivative_scalar hU hf k i hx, laplacian]
  calc
    _ ≤ ∑ d : Fin 3, |coordDeriv d (coordDeriv d (iteratedCoordinateDerivative k i f)) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 3, M := by
      apply Finset.sum_le_sum
      intro d _
      have hI : iteratedCoordinateDerivative (k + 2) (Fin.cons d (Fin.cons d i)) f =
          coordDeriv d (coordDeriv d (iteratedCoordinateDerivative k i f)) := by
        simp only [iteratedCoordinateDerivative, Fin.cons_zero, Fin.tail_cons]
      simpa only [hI] using hM (Fin.cons d (Fin.cons d i))
    _ = _ := by simp [nsmul_eq_mul]

private theorem abs_coordinateDerivative_triple_components_le {U : Set Point} (hU : IsOpen U)
    {f : Point → ℝ × ℝ × ℝ} (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) (i : Fin k → Fin 3)
    {x : Point} (hx : x ∈ U) {M : ℝ} (hM : ‖iteratedCoordinateDerivative k i f x‖ ≤ M) :
    |iteratedCoordinateDerivative k i (fun y => (f y).1) x| ≤ M ∧
      |iteratedCoordinateDerivative k i (fun y => (f y).2.1) x| ≤ M ∧
      |iteratedCoordinateDerivative k i (fun y => (f y).2.2) x| ≤ M := by
  let p₁ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  let p₂ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  let p₃ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  have h₁ := iteratedCoordinateDerivative_compCLM hU hf p₁ k i hx
  have h₂ := iteratedCoordinateDerivative_compCLM hU hf p₂ k i hx
  have h₃ := iteratedCoordinateDerivative_compCLM hU hf p₃ k i hx
  change iteratedCoordinateDerivative k i (fun y => (f y).1) x = (iteratedCoordinateDerivative k i f x).1 at h₁
  change iteratedCoordinateDerivative k i (fun y => (f y).2.1) x = (iteratedCoordinateDerivative k i f x).2.1 at h₂
  change iteratedCoordinateDerivative k i (fun y => (f y).2.2) x = (iteratedCoordinateDerivative k i f x).2.2 at h₃
  rw [h₁, h₂, h₃]
  rw [Prod.norm_def, Prod.norm_def] at hM
  exact ⟨(le_max_left _ _).trans hM, (le_max_left _ _).trans ((le_max_right _ _).trans hM),
    (le_max_right _ _).trans ((le_max_right _ _).trans hM)⟩

private theorem exists_weighted_normalizedAdjustedDefectPair_bound (a : BulkCoefficients) (j : ℕ)
    (M : ℝ) (hM : 1 ≤ M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (r ρ d : ℝ), ρ < r → 0 < d → d ≤ 1 → d ≤ (r - ρ) / 2 →
      ∀ (ε : ElasticScale) (c : Point) (Q : Point → S0),
      ContDiffOn ℝ ∞ Q (ball c r) →
      (∀ y ∈ ball c r, (ε : ℝ) ^ 2 • (laplacian Q y : S0).val = bulkGradient a (Q y)) →
      (∀ y ∈ ball c r, ∀ k ≤ j + 2, ∀ i : Fin k → Fin 3,
        ‖iteratedCoordinateDerivative k i (interiorBiaxialState a ε Q) y‖ ≤ M * d⁻¹ ^ k) →
      ∀ y ∈ ball c ρ, ∀ k ≤ j, ∀ i : Fin k → Fin 3,
        ‖iteratedCoordinateDerivative k i (normalizedAdjustedDefectPair a ε Q) y‖ ≤ C * d⁻¹ ^ (k + 2) := by
  classical
  have hB (l : Fin 2) := exists_weighted_coordinateDerivatives_comp_bound (interiorDefectData a l)
    (contDiff_interiorDefectData a l) (j + 2) M hM
  choose B hBpos hData using hB
  let T := ∑ l : Fin 2, B l
  let μ := min (bulkRadialMass a) (bulkBiaxialMass a)
  let A := T + μ⁻¹ * (3 * T)
  let C := 1 + A / μ + 6 * T / μ
  have hμ : 0 < μ := lt_min (bulkRadialMass_pos a) (bulkBiaxialMass_pos a)
  have hT : 0 ≤ T := Finset.sum_nonneg fun l _ => (hBpos l).le
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 1 ≤ C := by
    dsimp only [C]
    linarith only [div_nonneg hA hμ.le, div_nonneg (mul_nonneg (by norm_num : 0 ≤ (6 : ℝ)) hT) hμ.le]
  refine ⟨C, hC, ?_⟩
  intro r ρ d hρr hd hd₁ hdR ε c Q hQ hEuler hState x hx k hk i
  let R := (r - ρ) / 2
  have hR : 0 < R := half_pos (sub_pos.mpr hρr)
  have hInv : 1 ≤ d⁻¹ := (one_le_inv₀ hd).2 hd₁
  have hP : ∀ n : ℕ, 0 ≤ d⁻¹ ^ n := fun n => pow_nonneg (inv_nonneg.mpr hd.le) n
  have hPow : d⁻¹ ^ k ≤ d⁻¹ ^ (k + 2) := pow_le_pow_right₀ hInv (by omega)
  have hRPow : (R ^ 2)⁻¹ ≤ d⁻¹ ^ 2 := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hR.le) ((inv_le_inv₀ hR hd).2 hdR) 2
  let Ω := ball c r
  let Z := interiorBiaxialState a ε Q
  have hZ := contDiffOn_interiorBiaxialState a ε isOpen_ball hQ
  let b := (ε : ℝ) ^ 2
  have hb : 0 < b := sq_pos_of_pos ε.2.1
  have hxΩ : x ∈ Ω := ball_subset_ball hρr.le hx
  have hN := contDiffOn_normalizedAdjustedDefectPair a ε isOpen_ball hQ
  apply norm_coordinateDerivative_pi_le isOpen_ball hN k i hxΩ
    (mul_nonneg (zero_le_one.trans hC) (hP _))
  intro l
  let m := scalarDefectMass a l
  let f := interiorDefectData a l ∘ Z
  let U (y : Point) := (f y).1
  let F (y : Point) := (f y).2.1
  let G (y : Point) := (f y).2.2
  let H (y : Point) := G y + m⁻¹ • laplacian F y
  have hμm : μ ≤ m := scalarDefectMass_lower a l
  have hm : 0 < m := hμ.trans_le hμm
  have hf : ContDiffOn ℝ ∞ f Ω := (contDiff_interiorDefectData a l).comp_contDiffOn hZ
  have hUs : ContDiffOn ℝ ∞ U Ω := hf.fst
  have hFs : ContDiffOn ℝ ∞ F Ω := hf.snd.fst
  have hGs : ContDiffOn ℝ ∞ G Ω := hf.snd.snd
  have hLapF := contDiffOn_classical_laplacian_infty isOpen_ball hFs
  have hHs : ContDiffOn ℝ ∞ H Ω := hGs.add (hLapF.const_smul _)
  have hD (y : Point) (hy : y ∈ Ω) (n : ℕ) (hn : n ≤ j + 2) (a : Fin n → Fin 3) :
      |iteratedCoordinateDerivative n a U y| ≤ T * d⁻¹ ^ n ∧
        |iteratedCoordinateDerivative n a F y| ≤ T * d⁻¹ ^ n ∧
        |iteratedCoordinateDerivative n a G y| ≤ T * d⁻¹ ^ n := by
    have hF := (hData l isOpen_ball hZ y hy d hd (hState y hy) n hn a).trans
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun l _ => (hBpos l).le) (Finset.mem_univ l)) (hP _))
    exact abs_coordinateDerivative_triple_components_le isOpen_ball hf n a hy hF
  have hH (y : Point) (hy : y ∈ Ω) :
      |iteratedCoordinateDerivative k i H y| ≤ A * d⁻¹ ^ (k + 2) := by
    have hEq : |iteratedCoordinateDerivative k i (laplacian F) y| ≤ 3 * (T * d⁻¹ ^ (k + 2)) :=
      abs_coordinateDerivative_laplacian_le isOpen_ball hFs k i hy
        (fun j' => (hD y hy (k + 2) (Nat.add_le_add_right hk 2) j').2.1)
    change |iteratedCoordinateDerivative k i (fun y => G y + m⁻¹ • laplacian F y) y| ≤ _
    rw [iteratedCoordinateDerivative_add isOpen_ball hGs (hLapF.const_smul _) k i hy,
      iteratedCoordinateDerivative_const_smul isOpen_ball hLapF _ k i hy, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hm.le)]
    calc
      _ ≤ T * d⁻¹ ^ (k + 2) + μ⁻¹ * (3 * (T * d⁻¹ ^ (k + 2))) :=
        add_le_add ((hD y hy k (hk.trans (by omega)) i).2.2.trans
          (mul_le_mul_of_nonneg_left hPow hT))
          (mul_le_mul ((inv_le_inv₀ hm hμ).mpr hμm) hEq (abs_nonneg _) (inv_nonneg.mpr hμ.le))
      _ = A * d⁻¹ ^ (k + 2) := by dsimp only [A]; ring
  have hEq (y : Point) (hy : y ∈ Ω) : -(ε : ℝ) ^ 2 * laplacian U y + m * U y = (ε : ℝ) ^ 2 * H y :=
    interiorDefectData_screened a ε isOpen_ball hQ hEuler l hy
  have hBound := screened_coordinateDerivative_le_scaleSq hρr ε.2.1 hm
    (mul_nonneg hA (hP _)) (mul_nonneg hT (hP _)) hUs hHs hEq k i
    (fun y hy => (hD y hy k (hk.trans (by omega)) i).1) hH x hx
  change ‖iteratedCoordinateDerivative k i (fun y => b⁻¹ • U y) x‖ ≤ _
  rw [iteratedCoordinateDerivative_const_smul isOpen_ball hUs _ k i hxΩ, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hb.le)]
  calc
    _ ≤ b⁻¹ * (b * (A * d⁻¹ ^ (k + 2) / m + 6 * (T * d⁻¹ ^ k) / (m * R ^ 2))) :=
      mul_le_mul_of_nonneg_left hBound (inv_nonneg.mpr hb.le)
    _ = A * d⁻¹ ^ (k + 2) / m + 6 * (T * d⁻¹ ^ k) / (m * R ^ 2) := by
      rw [← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul]
    _ ≤ A * d⁻¹ ^ (k + 2) / μ + 6 * (T * d⁻¹ ^ k) / (μ * R ^ 2) :=
      add_le_add (div_le_div_of_nonneg_left (mul_nonneg hA (hP _)) hμ hμm)
        (div_le_div_of_nonneg_left (by positivity) (mul_pos hμ (sq_pos_of_pos hR))
          (mul_le_mul_of_nonneg_right hμm (sq_nonneg R)))
    _ = A / μ * d⁻¹ ^ (k + 2) + (6 * T / μ * d⁻¹ ^ k) * (R ^ 2)⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ A / μ * d⁻¹ ^ (k + 2) + (6 * T / μ * d⁻¹ ^ k) * d⁻¹ ^ 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hRPow (by positivity))
    _ = (A / μ + 6 * T / μ) * d⁻¹ ^ (k + 2) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (hP _)

private def harmonicRemainderPolynomial (a : BulkCoefficients)
    (z : InteriorBiaxialState × ScalarDefectPair) : Tensor :=
  let Q := z.1.2.1
  let D := z.1.2.2.1
  let h := z.1.2.2.2 0
  let u := z.2 0
  let v := z.2 1
  symmetricTraceless.subtypeL ((bulkRadialCoefficient a * u) • Q + (a.a6 * h ^ 2) • Q +
    (a.a6' * v) • traceFreeSquare Q) +
    (h / vacuumRadius a ^ 4 * cubicGradientContraction Q D) • (1 : Tensor)

private theorem contDiff_harmonicRemainderPolynomial (a : BulkCoefficients) :
    ContDiff ℝ ∞ (harmonicRemainderPolynomial a) := by
  let X := InteriorBiaxialState × ScalarDefectPair
  have hQ : ContDiff ℝ ∞ (fun z : X => z.1.2.1) := contDiff_fst.snd.fst
  have hD : ContDiff ℝ ∞ (fun z : X => z.1.2.2.1) := contDiff_fst.snd.snd.fst
  have hW : ContDiff ℝ ∞ (fun z : X => z.1.2.2.2) := contDiff_fst.snd.snd.snd
  let L (l : Fin 2) : ScalarDefectPair →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) l
  have hh : ContDiff ℝ ∞ (fun z : X => z.1.2.2.2 0) := (L 0).contDiff.comp hW
  have hu : ContDiff ℝ ∞ (fun z : X => z.2 0) := (L 0).contDiff.comp contDiff_snd
  have hv : ContDiff ℝ ∞ (fun z : X => z.2 1) := (L 1).contDiff.comp contDiff_snd
  have hC : ContDiff ℝ ∞ (fun z : X => cubicGradientContraction z.1.2.1 z.1.2.2.1) := by
    have hS : ContDiff ℝ ∞ (fun z : X => biaxialGradientSource (z.1.2.1, z.1.2.2.1) 1) :=
      (L 1).contDiff.comp (contDiff_biaxialGradientSource.comp (hQ.prodMk hD))
    have hEq : (fun z : X => cubicGradientContraction z.1.2.1 z.1.2.2.1) =
        fun z => (-1 / 6 : ℝ) * biaxialGradientSource (z.1.2.1, z.1.2.2.1) 1 := by
      funext z
      change cubicGradientContraction z.1.2.1 z.1.2.2.1 = _ * (-6 * cubicGradientContraction z.1.2.1 z.1.2.2.1)
      ring
    rw [hEq]
    exact contDiff_const.mul hS
  have hMain : ContDiff ℝ ∞ (fun z : X =>
      (bulkRadialCoefficient a * z.2 0) • z.1.2.1 + (a.a6 * (z.1.2.2.2 0) ^ 2) • z.1.2.1 +
        (a.a6' * z.2 1) • traceFreeSquare z.1.2.1) :=
    (((contDiff_const.mul hu).smul hQ).add
      ((contDiff_const.mul (hh.pow 2)).smul hQ)).add
      ((contDiff_const.mul hv).smul (contDiff_traceFreeSquare.comp hQ))
  have hScalar : ContDiff ℝ ∞ (fun z : X =>
      z.1.2.2.2 0 / vacuumRadius a ^ 4 * cubicGradientContraction z.1.2.1 z.1.2.2.1) := by
    simp only [div_eq_mul_inv]
    exact (hh.mul contDiff_const).mul hC
  exact (symmetricTraceless.subtypeL.contDiff.comp hMain).add (hScalar.smul contDiff_const)

private theorem harmonicRemainder_eq_scaleSq_mul_polynomial (a : BulkCoefficients)
    (ε : ElasticScale) (Q : Point → S0) :
    harmonicRemainder a ε Q = fun x => (ε : ℝ) ^ 2 •
      harmonicRemainderPolynomial a (interiorBiaxialState a ε Q x, normalizedAdjustedDefectPair a ε Q x) := by
  funext x
  let β := (ε : ℝ) ^ 2
  let h := scaledNormDefect a ε (Q x)
  let u := adjustedNormDefect a ε Q x
  let v := adjustedCubicDefect a ε Q x
  let U := normalizedAdjustedDefectPair a ε Q x 0
  let V := normalizedAdjustedDefectPair a ε Q x 1
  let G := cubicGradientContraction (Q x) (ClassicalGradient Q x)
  have hβ : β ≠ 0 := pow_ne_zero 2 ε.2.1.ne'
  have hU : U = β⁻¹ * u := congrArg (β⁻¹ * ·) (interiorDefectData_adjusted a ε Q x).1
  have hV : V = β⁻¹ * v := congrArg (β⁻¹ * ·) (interiorDefectData_adjusted a ε Q x).2
  have h₁ : β * (bulkRadialCoefficient a * U) = bulkRadialCoefficient a * u := by
    rw [hU]
    calc
      _ = (β * β⁻¹) * (bulkRadialCoefficient a * u) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hβ, one_mul]
  have h₂ : β * (a.a6 * h ^ 2) = a.a6 * β * h ^ 2 := by ring
  have h₃ : β * (a.a6' * V) = a.a6' * v := by
    rw [hV]
    calc
      _ = (β * β⁻¹) * (a.a6' * v) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hβ, one_mul]
  have h₄ : β * (h / vacuumRadius a ^ 4 * G) = β / vacuumRadius a ^ 4 * h * G := by ring
  change symmetricTraceless.subtypeL ((bulkRadialCoefficient a * u) • Q x +
      (a.a6 * β * h ^ 2) • Q x + (a.a6' * v) • traceFreeSquare (Q x)) +
      (β / vacuumRadius a ^ 4 * h * G) • (1 : Tensor) =
    β • (symmetricTraceless.subtypeL ((bulkRadialCoefficient a * U) • Q x +
      (a.a6 * h ^ 2) • Q x + (a.a6' * V) • traceFreeSquare (Q x)) +
      (h / vacuumRadius a ^ 4 * G) • (1 : Tensor))
  simp only [map_add, map_smul, smul_add, smul_smul, h₁, h₂, h₃, h₄]

private def weightedHarmonicRemainderPolynomial (a : BulkCoefficients)
    (z : ℝ × InteriorBiaxialState × ScalarDefectPair) : Tensor :=
  harmonicRemainderPolynomial a z.2 +
    (z.1 - 1) • harmonicRemainderPolynomial a (z.2.1, 0)

private theorem contDiff_weightedHarmonicRemainderPolynomial (a : BulkCoefficients) :
    ContDiff ℝ ∞ (weightedHarmonicRemainderPolynomial a) :=
  ((contDiff_harmonicRemainderPolynomial a).comp contDiff_snd).add
    ((contDiff_fst.sub contDiff_const).smul
      ((contDiff_harmonicRemainderPolynomial a).comp (contDiff_snd.fst.prodMk contDiff_const)))

private theorem weightedHarmonicRemainderPolynomial_smul (a : BulkCoefficients)
    (r : ℝ) (Z : InteriorBiaxialState) (W : ScalarDefectPair) :
    weightedHarmonicRemainderPolynomial a (r, Z, r • W) =
      r • harmonicRemainderPolynomial a (Z, W) := by
  have h₀ : bulkRadialCoefficient a * (r * W 0) = r * (bulkRadialCoefficient a * W 0) := by ring
  have h₁ : a.a6' * (r * W 1) = r * (a.a6' * W 1) := by ring
  let A := a.a6 * Z.2.2.2 0 ^ 2
  let B := Z.2.2.2 0 / vacuumRadius a ^ 4 * cubicGradientContraction Z.2.1 Z.2.2.1
  have h₂ : (r - 1) * A = r * A - A := by ring
  have h₃ : (r - 1) * B = r * B - B := by ring
  simp only [weightedHarmonicRemainderPolynomial, harmonicRemainderPolynomial,
    Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero, zero_smul, zero_add, add_zero,
    map_add, map_smul, smul_add, smul_smul, h₀, h₁]
  change (r * (bulkRadialCoefficient a * W 0)) • symmetricTraceless.subtypeL Z.2.1 +
      A • symmetricTraceless.subtypeL Z.2.1 +
      (r * (a.a6' * W 1)) • symmetricTraceless.subtypeL (traceFreeSquare Z.2.1) +
      B • (1 : Tensor) + (((r - 1) * A) • symmetricTraceless.subtypeL Z.2.1 +
        ((r - 1) * B) • (1 : Tensor)) =
    (r * (bulkRadialCoefficient a * W 0)) • symmetricTraceless.subtypeL Z.2.1 +
      (r * A) • symmetricTraceless.subtypeL Z.2.1 +
      (r * (a.a6' * W 1)) • symmetricTraceless.subtypeL (traceFreeSquare Z.2.1) +
      (r * B) • (1 : Tensor)
  rw [h₂, h₃, sub_smul, sub_smul]
  abel

/-- Uniform full remainder bound on a smaller ball, with the two
derivative powers from the screened source explicit in the radius. -/
theorem exists_weighted_interior_harmonicRemainder_coordinate_bound (a : BulkCoefficients)
    (hEstimate : InteriorPoissonGradientEstimate) (j : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C > (0 : ℝ), ∀ (r ρ d : ℝ), 0 < ρ → ρ < r → 0 < d → d ≤ 1 →
      d ≤ (r - ρ) / 4 → ∀ (ε : ElasticScale) (c : Point) (Q : Point → S0),
      ContDiffOn ℝ ∞ Q (ball c r) →
      (∀ x ∈ ball c r, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x)) →
      (∀ x ∈ ball c r, |scaledNormDefect a ε (Q x)| ≤ C₀ ∧ |scaledCubicTrace a ε (Q x)| ≤ C₀ ∧
        Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ C₀) →
      ∀ x ∈ ball c ρ, ∀ i : Fin j → Fin 3,
        ‖iteratedCoordinateDerivative j i (harmonicRemainder a ε Q) x‖ ≤
          C * (ε : ℝ) ^ 2 * d⁻¹ ^ (j + 2) := by
  obtain ⟨M, hM, hState⟩ := exists_weighted_interiorBiaxialState_bounds a hEstimate (j + 2) C₀ hC₀
  obtain ⟨N, hN, hAdj⟩ := exists_weighted_normalizedAdjustedDefectPair_bound a j M hM
  have hMN : 1 ≤ M + N := hM.trans (le_add_of_nonneg_right (zero_le_one.trans hN))
  obtain ⟨C, hC, hPoly⟩ := exists_weighted_coordinateDerivatives_comp_bound
    (weightedHarmonicRemainderPolynomial a) (contDiff_weightedHarmonicRemainderPolynomial a) j (M + N) hMN
  refine ⟨C, hC, ?_⟩
  intro r ρ d hρ hρr hd hd₁ hdGap ε c Q hQ hEuler hBase x hx i
  let t := (ρ + r) / 2
  have ht : 0 < t := by dsimp only [t]; linarith
  have hρt : ρ < t := by dsimp only [t]; linarith
  have htr : t < r := by dsimp only [t]; linarith
  have hd₁Gap : d ≤ r - t := by dsimp only [t]; linarith
  have hd₂Gap : d ≤ (t - ρ) / 2 := by dsimp only [t]; linarith
  let Z := interiorBiaxialState a ε Q
  let W := normalizedAdjustedDefectPair a ε Q
  let U (y : Point) := d ^ 2 • W y
  let S (y : Point) := (d ^ 2, Z y, U y)
  have hZ := contDiffOn_interiorBiaxialState a ε isOpen_ball hQ
  have hW := contDiffOn_normalizedAdjustedDefectPair a ε isOpen_ball hQ
  have hU : ContDiffOn ℝ ∞ U (ball c r) := hW.const_smul _
  have hS : ContDiffOn ℝ ∞ S (ball c ρ) :=
    (contDiffOn_const.prodMk (hZ.prodMk hU)).mono (ball_subset_ball hρr.le)
  have hM' := hState r t d ht htr hd hd₁ hd₁Gap ε c Q hQ hEuler hBase
  have hAdj' := hAdj t ρ d hρt hd hd₁ hd₂Gap ε c Q (hQ.mono (ball_subset_ball htr.le))
    (fun y hy => hEuler y (ball_subset_ball htr.le hy)) hM'
  have hInv : 1 ≤ d⁻¹ := (one_le_inv₀ hd).2 hd₁
  have hScale (k : ℕ) : d ^ 2 * (N * d⁻¹ ^ (k + 2)) = N * d⁻¹ ^ k := by
    rw [pow_add, inv_pow d 2]
    calc
      _ = N * d⁻¹ ^ k * (d ^ 2 * (d ^ 2)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ hd.ne'), mul_one]
  have hSbounds (k : ℕ) (hk : k ≤ j) (w : Fin k → Fin 3) :
      ‖iteratedCoordinateDerivative k w S x‖ ≤ (M + N) * d⁻¹ ^ k := by
    have hxR := ball_subset_ball hρr.le hx
    have hPow : 0 ≤ d⁻¹ ^ k := pow_nonneg (inv_nonneg.mpr hd.le) _
    have hUW : ‖iteratedCoordinateDerivative k w U x‖ ≤ N * d⁻¹ ^ k := by
      change ‖iteratedCoordinateDerivative k w (fun y => d ^ 2 • W y) x‖ ≤ _
      rw [iteratedCoordinateDerivative_const_smul isOpen_ball hW _ k w hxR, norm_smul,
        Real.norm_of_nonneg (sq_nonneg _)]
      exact (mul_le_mul_of_nonneg_left (hAdj' x hx k hk w) (sq_nonneg _)).trans_eq (hScale k)
    have hB : 0 ≤ (M + N) * d⁻¹ ^ k := mul_nonneg (zero_le_one.trans hMN) hPow
    have hD : ‖d ^ 2‖ ≤ (M + N) * d⁻¹ ^ k := by
      rw [Real.norm_of_nonneg (sq_nonneg d)]
      exact ((pow_le_pow_left₀ hd.le hd₁ 2).trans_eq (one_pow _)).trans
        (hMN.trans (le_mul_of_one_le_right (zero_le_one.trans hMN) (one_le_pow₀ hInv)))
    exact norm_coordDerivative_pair_le isOpen_ball contDiffOn_const (hZ.prodMk hU) k w hxR
      (norm_coordDerivative_const_le hB hD k w x)
      (norm_coordDerivative_pair_le isOpen_ball hZ hU k w hxR
        ((hM' x (ball_subset_ball hρt.le hx) k (hk.trans (by omega)) w).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (zero_le_one.trans hN)) hPow))
        (hUW.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (zero_le_one.trans hM)) hPow)))
  have hP := hPoly isOpen_ball hS x hx d hd hSbounds j le_rfl i
  have hPs : ContDiffOn ℝ ∞ (weightedHarmonicRemainderPolynomial a ∘ S) (ball c ρ) :=
    (contDiff_weightedHarmonicRemainderPolynomial a).comp_contDiffOn hS
  have hR : harmonicRemainder a ε Q = fun y => ((ε : ℝ) ^ 2 * (d ^ 2)⁻¹) •
      (weightedHarmonicRemainderPolynomial a ∘ S) y := by
    funext y
    rw [congrFun (harmonicRemainder_eq_scaleSq_mul_polynomial a ε Q) y]
    change _ = _ • weightedHarmonicRemainderPolynomial a (d ^ 2, Z y, d ^ 2 • W y)
    rw [weightedHarmonicRemainderPolynomial_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hd.ne'), mul_one]
  rw [hR, iteratedCoordinateDerivative_const_smul isOpen_ball hPs _ j i hx, norm_smul,
    Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (sq_nonneg _)))]
  refine (mul_le_mul_of_nonneg_left hP (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (sq_nonneg _)))).trans_eq ?_
  rw [pow_add, inv_pow d 2]
  ring

/-- Order-by-order interior estimates for the exact full remainder in the
ambient harmonic-map equation. -/
theorem exists_interior_harmonicRemainder_coordinate_bound (a : BulkCoefficients)
    (hEstimate : InteriorPoissonGradientEstimate) (j : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (r ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) :
    ∃ C > (0 : ℝ), ∀ (ε : ElasticScale) (c : Point) (Q : Point → S0),
      ContDiffOn ℝ ∞ Q (ball c r) →
      (∀ x ∈ ball c r, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x)) →
      (∀ x ∈ ball c r, |scaledNormDefect a ε (Q x)| ≤ C₀ ∧ |scaledCubicTrace a ε (Q x)| ≤ C₀ ∧
        Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ C₀) →
      ∀ x ∈ ball c ρ, ∀ i : Fin j → Fin 3,
        ‖iteratedCoordinateDerivative j i (harmonicRemainder a ε Q) x‖ ≤ C * (ε : ℝ) ^ 2 := by
  obtain ⟨C, hC, hWeighted⟩ := exists_weighted_interior_harmonicRemainder_coordinate_bound
    a hEstimate j C₀ hC₀
  let d := min 1 ((r - ρ) / 4)
  have hd : 0 < d := lt_min zero_lt_one (div_pos (sub_pos.mpr hρr) (by norm_num))
  refine ⟨C * d⁻¹ ^ (j + 2), mul_pos hC (pow_pos (inv_pos.mpr hd) _), ?_⟩
  intro ε c Q hQ hEq hBase x hx i
  exact (hWeighted r ρ d hρ hρr hd (min_le_left _ _) (min_le_right _ _)
    ε c Q hQ hEq hBase x hx i).trans_eq (by ring)

/-- The full residual is smooth wherever the original field is smooth. -/
theorem contDiffOn_harmonicRemainder (a : BulkCoefficients) (ε : ElasticScale)
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q U) :
    ContDiffOn ℝ ∞ (harmonicRemainder a ε Q) U := by
  rw [harmonicRemainder_eq_scaleSq_mul_polynomial]
  exact ((contDiff_harmonicRemainderPolynomial a).comp_contDiffOn
    ((contDiffOn_interiorBiaxialState a ε hU hQ).prodMk
      (contDiffOn_normalizedAdjustedDefectPair a ε hU hQ))).const_smul _

/-- The projected residual has the same quadratic scale in every
classical derivative on a compact subset of the regular set. -/
theorem exists_compact_projectedHarmonicRemainder_bound (a : BulkCoefficients)
    (hEst : InteriorPoissonGradientEstimate) (hMean : External.ClassicalScalarSubsolutionMeanValue)
    {Ω : Set Point} (hΩ : IsOpen Ω) (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (q : Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    (hEuler : ∀ n x, x ∈ Ω → (ε n : ℝ) ^ 2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x))
    (hRange : BddAbove ((fun p : ℕ × Point => ‖Q p.1 p.2‖) '' (univ ×ˢ Ω)))
    (hStrong : StrongH1Loc Ω Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q))
    (hBulk : ConvergesScaledPotentialLoc a Ω ε Q)
    (K : Set Point) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (projectedHarmonicRemainder a (ε n) (Q n)) x‖ ≤ C * (ε n : ℝ) ^ 2 := by
  classical
  obtain ⟨r, hr, hR⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let t := 3 * r / 4
  have ht : 0 < t := by dsimp only [t]; positivity
  have htr : t < r := by dsimp only [t]; linarith
  have hrt : r / 2 < t := by dsimp only [t]; linarith
  have hLoc (c : K) : ∃ C > (0 : ℝ), ∀ᶠ n in atTop, ∀ x ∈ ball c.val (r / 2),
      ‖iteratedFDeriv ℝ j (projectedHarmonicRemainder a (ε n) (Q n)) x‖ ≤ C * (ε n : ℝ) ^ 2 := by
    have hClosed : closedBall c.val r ⊆ Ω := (closedBall_subset_cthickening c.property r).trans hR
    have hB : ball c.val r ⊆ Ω := ball_subset_closedBall.trans hClosed
    have hBt := (ball_subset_ball htr.le).trans hB
    let L := (eLpNorm (fun y => Real.sqrt (gradientNormSq (ClassicalGradient q y))) ⊤
      (volume.restrict (ball c.val r))).toReal
    have hL : 0 ≤ L := ENNReal.toReal_nonneg
    obtain ⟨B, hBpos, hBase⟩ :=
      exists_eventual_interior_biaxial_orderZero_bound a hEst hMean r t L ht htr hL
    obtain ⟨C, hC, hCj⟩ := exists_interior_harmonicRemainder_coordinate_bound a hEst j B hBpos.le
      t (r / 2) (half_pos hr) hrt
    have hBase' := hBase c.val ε Q q hε (fun n => (hQ n).mono hB) (((contDiffOn_infty.mp hq) 2).mono hB)
      (fun n y hy => hEuler n y (hB hy)) (hRange.mono (image_mono (prod_mono subset_rfl hB)))
      (classicalGradient_le_eLpNorm_top_on_regular_ball hΩ hq hClosed)
      (fun W hW hWC => hStrong W hW ⟨hWC.1, hWC.2.trans hB⟩)
      (fun W hW hWC => hBulk W hW ⟨hWC.1, hWC.2.trans hB⟩)
    refine ⟨(3 : ℝ) ^ j * C, by positivity, ?_⟩
    filter_upwards [hBase'] with n hn x hx
    let Z := harmonicRemainder a (ε n) (Q n)
    let P := projectedHarmonicRemainder a (ε n) (Q n)
    have hEq : P = traceFreeSymmetricPartCLM ∘ Z :=
      funext fun x => (traceFreeSymmetricPart_harmonicRemainder a (ε n) (Q n) x).symm
    have hZ : ContDiffOn ℝ ∞ Z Ω := contDiffOn_harmonicRemainder a (ε n) hΩ (hQ n)
    have hxΩ : x ∈ Ω := hBt (ball_subset_ball hrt.le hx)
    have hCoord (i : Fin j → Fin 3) : ‖iteratedCoordinateDerivative j i P x‖ ≤ C * (ε n : ℝ) ^ 2 := by
      have he : iteratedCoordinateDerivative j i P x =
          traceFreeSymmetricPart (iteratedCoordinateDerivative j i Z x) :=
        (congrArg (fun F => iteratedCoordinateDerivative j i F x) hEq).trans
          (iteratedCoordinateDerivative_compCLM hΩ hZ traceFreeSymmetricPartCLM j i hxΩ)
      exact (congrArg (fun z : S0 => ‖z‖) he).le.trans ((norm_traceFreeSymmetricPart_le _).trans
        (hCj (ε n) c.val (Q n) ((hQ n).mono hBt) (fun y hy => hEuler n y (hBt hy)) hn x hx i))
    have hP : ContDiffOn ℝ ∞ P Ω := hEq ▸ traceFreeSymmetricPartCLM.contDiff.comp_contDiffOn hZ
    exact (norm_iteratedFDeriv_le_of_coordinateBounds hΩ hP j hxΩ (by positivity) hCoord).trans_eq
      (by ring)
  choose C hC hBounds using hLoc
  let V (c : K) := ball c.val (r / 2)
  have hCov : K ⊆ ⋃ c : K, V c :=
    fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (half_pos hr)⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V (fun _ => isOpen_ball) hCov
  refine ⟨∑ c ∈ I, C c, Finset.sum_nonneg fun c _ => (hC c).le, ?_⟩
  filter_upwards [(eventually_all_finset I).2 (fun c _ => hBounds c)] with n hn x hx
  obtain ⟨c, hc, hx⟩ := mem_iUnion₂.mp (hI hx)
  exact (hn c hc x hx).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun c _ => (hC c).le) hc) (sq_nonneg _))

private def listCoordinateDerivative : List (Fin 3) → (Point → Tensor) → Point → Tensor
  | [], f => f
  | i :: l, f => coordDeriv i (listCoordinateDerivative l f)

private theorem listCoordinateDerivative_append (l m : List (Fin 3)) (f : Point → Tensor) :
    listCoordinateDerivative (l ++ m) f = listCoordinateDerivative l (listCoordinateDerivative m f) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, listCoordinateDerivative, ih]

private theorem listCoordinateDerivative_replicate (n : ℕ) (i : Fin 3) (f : Point → Tensor) :
    listCoordinateDerivative (List.replicate n i) f = (coordDeriv i)^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, listCoordinateDerivative, ih, Function.iterate_succ_apply']

private theorem listCoordinateDerivative_eq_iteratedCoordinateDerivative
    (l : List (Fin 3)) (f : Point → Tensor) :
    listCoordinateDerivative l f = iteratedCoordinateDerivative l.length l.get f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      have h : Fin.tail (i :: l).get = l.get := by funext j; simp [Fin.tail]
      change coordDeriv i (listCoordinateDerivative l f) =
        coordDeriv ((i :: l).get 0) (iteratedCoordinateDerivative l.length (Fin.tail (i :: l).get) f)
      rw [h, ih]
      rfl

private theorem exists_coordinate_word_for_multiIndexDerivative (m : Fin 3 → ℕ) :
    ∃ i : Fin (∑ k, m k) → Fin 3, ∀ f : Point → Tensor,
      multiIndexDerivative m f = iteratedCoordinateDerivative (∑ k, m k) i f := by
  let l := List.replicate (m 0) (0 : Fin 3) ++ List.replicate (m 1) (1 : Fin 3) ++ List.replicate (m 2) (2 : Fin 3)
  have hLen : l.length = ∑ k, m k := by simp [l, Fin.sum_univ_three, add_assoc]
  have h : ∃ i : Fin l.length → Fin 3, ∀ f : Point → Tensor,
      multiIndexDerivative m f = iteratedCoordinateDerivative l.length i f := by
    refine ⟨l.get, fun f => ?_⟩
    rw [← listCoordinateDerivative_eq_iteratedCoordinateDerivative l f]
    simp only [l, listCoordinateDerivative_append, listCoordinateDerivative_replicate, multiIndexDerivative]
  exact hLen ▸ h

private theorem multiIndexNorm_le_of_coordinateDerivative_bound (j : ℕ) (f : Point → Tensor) (x : Point)
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ i : Fin j → Fin 3, ‖iteratedCoordinateDerivative j i f x‖ ≤ B) :
    multiIndexNorm j f x ≤ Real.sqrt (Fintype.card (Fin 3 → Fin (j + 1)) : ℝ) * B := by
  classical
  let A := Finset.univ.filter (fun m : Fin 3 → Fin (j + 1) => (∑ k, (m k).val) = j)
  have hBound (m : Fin 3 → Fin (j + 1)) (hm : m ∈ A) :
      ‖multiIndexDerivative (fun k => (m k).val) f x‖ ≤ B := by
    have hOrder := (Finset.mem_filter.mp hm).2
    have hM := exists_coordinate_word_for_multiIndexDerivative (fun k => (m k).val)
    change (∑ k, (m k).val) = j at hOrder
    rw [hOrder] at hM
    obtain ⟨i, hi⟩ := hM
    rw [hi f]
    exact h i
  have hCard : (A.card : ℝ) ≤ Fintype.card (Fin 3 → Fin (j + 1)) := by
    exact_mod_cast Finset.card_le_univ A
  have hS : (∑ m ∈ A, ‖multiIndexDerivative (fun k => (m k).val) f x‖ ^ 2) ≤
      (Fintype.card (Fin 3 → Fin (j + 1)) : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _m ∈ A, B ^ 2 :=
        Finset.sum_le_sum fun m hm => pow_le_pow_left₀ (norm_nonneg _) (hBound m hm) 2
      _ = A.card * B ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hCard (sq_nonneg _)
  exact (Real.sqrt_le_sqrt hS).trans_eq (by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hB])

/-- The essential supremum estimate for the actual multi-index remainder
norm used in the bounded-energy limit theorem. -/
theorem exists_interior_harmonicRemainder_eLpNorm_bound (a : BulkCoefficients)
    (hEstimate : InteriorPoissonGradientEstimate) (j : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (r ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) :
    ∃ C > (0 : ℝ), ∀ (ε : ElasticScale) (c : Point) (Q : Point → S0),
      ContDiffOn ℝ ∞ Q (ball c r) →
      (∀ x ∈ ball c r, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x)) →
      (∀ x ∈ ball c r, |scaledNormDefect a ε (Q x)| ≤ C₀ ∧ |scaledCubicTrace a ε (Q x)| ≤ C₀ ∧
        Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ C₀) →
      eLpNorm (multiIndexNorm j (harmonicRemainder a ε Q)) ⊤ (volume.restrict (ball c ρ)) ≤
        ENNReal.ofReal (C * (ε : ℝ) ^ 2) := by
  obtain ⟨A, hA, hEst⟩ := exists_interior_harmonicRemainder_coordinate_bound a hEstimate j C₀ hC₀ r ρ hρ hρr
  let N := Real.sqrt (Fintype.card (Fin 3 → Fin (j + 1)) : ℝ)
  refine ⟨(N + 1) * A, mul_pos (by dsimp only [N]; positivity) hA, ?_⟩
  intro ε c Q hQ hEuler hBase
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
  have h := multiIndexNorm_le_of_coordinateDerivative_bound j (harmonicRemainder a ε Q) x (by positivity)
    (hEst ε c Q hQ hEuler hBase x hx)
  rw [Real.norm_of_nonneg (show 0 ≤ multiIndexNorm j (harmonicRemainder a ε Q) x from Real.sqrt_nonneg _)]
  exact h.trans (by
    change N * (A * (ε : ℝ) ^ 2) ≤ _
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hA.le)
      (sq_nonneg _))

private theorem exists_eventual_regularBall_harmonicRemainder_bound (a : BulkCoefficients)
    (hEstimate : InteriorPoissonGradientEstimate) (hMean : External.ClassicalScalarSubsolutionMeanValue)
    (j : ℕ) (r L : ℝ) (hr : 0 < r) (hL : 0 ≤ L) :
    ∃ C > (0 : ℝ), ∀ (c : Point) (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (q : Point → S0),
      Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
      (∀ n, ContDiffOn ℝ ∞ (Q n) (ball c r)) → ContDiffOn ℝ 2 q (ball c r) →
      (∀ n x, x ∈ ball c r → (ε n : ℝ) ^ 2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x)) →
      BddAbove ((fun p : ℕ × Point => ‖Q p.1 p.2‖) '' (univ ×ˢ ball c r)) →
      (∀ x ∈ ball c r, Real.sqrt (gradientNormSq (ClassicalGradient q x)) ≤ L) →
      StrongH1Loc (ball c r) Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q) →
      ConvergesScaledPotentialLoc a (ball c r) ε Q →
      ∀ᶠ n in atTop, eLpNorm (multiIndexNorm j (harmonicRemainder a (ε n) (Q n))) ⊤
        (volume.restrict (ball c (r / 2))) ≤ ENNReal.ofReal (C * (ε n : ℝ) ^ 2) := by
  let t := 3 * r / 4
  have ht : 0 < t := by dsimp only [t]; positivity
  have htr : t < r := by dsimp only [t]; linarith
  have hS : r / 2 < t := by dsimp only [t]; linarith
  obtain ⟨C₀, hC₀, hBase⟩ := exists_eventual_interior_biaxial_orderZero_bound a hEstimate hMean r t L ht htr hL
  obtain ⟨C, hC, hE⟩ := exists_interior_harmonicRemainder_eLpNorm_bound a hEstimate j C₀ hC₀.le t (r / 2)
    (half_pos hr) hS
  refine ⟨C, hC, ?_⟩
  intro c ε Q q hε hQ hq hEuler hRange hLimit hStrong hBulk
  have hB := hBase c ε Q q hε hQ hq hEuler hRange hLimit hStrong hBulk
  filter_upwards [hB] with n hn
  exact hE (ε n) c (Q n) ((hQ n).mono (ball_subset_ball htr.le))
    (fun x hx => hEuler n x (ball_subset_ball htr.le hx)) hn

/-- The complete local remainder clause on the regular set, with a
single material family of constants indexed by derivative order, radius
and the limiting gradient's essential supremum on the original ball. -/
theorem exists_regular_interior_harmonicRemainder_constants (a : BulkCoefficients)
    (hEstimate : InteriorPoissonGradientEstimate) (hMean : External.ClassicalScalarSubsolutionMeanValue) :
    ∃ C : ℕ → ℝ → ℝ → ℝ, (∀ j r L, 0 < r → 0 ≤ L → 0 < C j r L) ∧
      ∀ {Ω : Set Point}, IsOpen Ω → ∀ (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (q : Point → S0),
        Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        (∀ n, ContDiffOn ℝ ∞ (Q n) Ω) → ContDiffOn ℝ ∞ q Ω →
        (∀ n x, x ∈ Ω → (ε n : ℝ) ^ 2 • (laplacian (Q n) x : S0).val = bulkGradient a (Q n x)) →
        BddAbove ((fun p : ℕ × Point => ‖Q p.1 p.2‖) '' (univ ×ˢ Ω)) →
        StrongH1Loc Ω Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q) →
        ConvergesScaledPotentialLoc a Ω ε Q →
        ∀ (c : Point) (r : ℝ), 0 < r → closedBall c r ⊆ Ω →
          (∀ n, ContDiffOn ℝ ∞ (Q n) (ball c (r / 2)) ∧
            ∀ y ∈ ball c (r / 2), (laplacian (Q n) y : S0).val =
              harmonicRhs a (Q n) (ClassicalGradient (Q n)) y + harmonicRemainder a (ε n) (Q n) y) ∧
          ∀ j : ℕ, ∀ᶠ n in atTop,
            let L := (eLpNorm (fun y => Real.sqrt (gradientNormSq (ClassicalGradient q y))) ⊤
              (volume.restrict (ball c r))).toReal
            eLpNorm (multiIndexNorm j (harmonicRemainder a (ε n) (Q n))) ⊤ (volume.restrict (ball c (r / 2))) ≤
              ENNReal.ofReal (C j r L * (ε n : ℝ) ^ 2) := by
  classical
  let C (j : ℕ) (r L : ℝ) := if h : 0 < r ∧ 0 ≤ L then
    (exists_eventual_regularBall_harmonicRemainder_bound a hEstimate hMean j r L h.1 h.2).choose else 1
  refine ⟨C, ?_, ?_⟩
  · intro j r L hr hL
    have h : 0 < r ∧ 0 ≤ L := ⟨hr, hL⟩
    simpa only [C, dif_pos h] using
      (exists_eventual_regularBall_harmonicRemainder_bound a hEstimate hMean j r L hr hL).choose_spec.1
  intro Ω hΩ ε Q q hε hQ hq hEuler hRange hStrong hBulk c r hr hClosed
  have hB : ball c r ⊆ Ω := ball_subset_closedBall.trans hClosed
  have hHalf : ball c (r / 2) ⊆ Ω := (ball_subset_ball (half_le_self hr.le)).trans hB
  refine ⟨fun n => ⟨(hQ n).mono hHalf, fun y hy => laplacian_eq_harmonicRhs_add_remainder
    a (ε n) (Q n) y (hEuler n y (hHalf hy))⟩, ?_⟩
  intro j
  let L := (eLpNorm (fun y => Real.sqrt (gradientNormSq (ClassicalGradient q y))) ⊤
    (volume.restrict (ball c r))).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hG := classicalGradient_le_eLpNorm_top_on_regular_ball hΩ hq hClosed
  have hNC : 0 < r ∧ 0 ≤ L := ⟨hr, hL⟩
  have hRange' : BddAbove ((fun p : ℕ × Point => ‖Q p.1 p.2‖) '' (univ ×ˢ ball c r)) :=
    hRange.mono (image_mono (prod_mono subset_rfl hB))
  have hStrong' : StrongH1Loc (ball c r) Q (fun n => ClassicalGradient (Q n)) q (ClassicalGradient q) :=
    fun W hW hWC => hStrong W hW ⟨hWC.1, hWC.2.trans hB⟩
  have hBulk' : ConvergesScaledPotentialLoc a (ball c r) ε Q :=
    fun W hW hWC => hBulk W hW ⟨hWC.1, hWC.2.trans hB⟩
  have hResult := (exists_eventual_regularBall_harmonicRemainder_bound a hEstimate hMean j r L hr hL).choose_spec.2
    c ε Q q hε (fun n => (hQ n).mono hB) (((contDiffOn_infty.mp hq) 2).mono hB)
    (fun n y hy => hEuler n y (hB hy)) hRange' hG hStrong' hBulk'
  change ∀ᶠ n in atTop, eLpNorm (multiIndexNorm j (harmonicRemainder a (ε n) (Q n))) ⊤
    (volume.restrict (ball c (r / 2))) ≤ ENNReal.ofReal (C j r L * (ε n : ℝ) ^ 2)
  simpa only [C, dif_pos hNC] using hResult

end Thesis

end
