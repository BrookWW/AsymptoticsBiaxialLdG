module

public import Thesis.Variational.InteriorDerivativeAlgebra

/-! Interior first-derivative estimates for the coupled Poisson and screened
equations satisfied by differentiated penalized solutions. -/

public section

open Filter Metric Set Topology
open scoped ContDiff Matrix.Norms.Frobenius

noncomputable section

namespace Thesis

@[expose] def tensorFamilyGradientSum {ι : Type*} [Fintype ι] (V : ι → Point → S0) (x : Point) : ℝ :=
  ∑ j, ∑ i : Fin 3, ‖coordDeriv i (V j) x‖

@[expose] def scalarFamilyGradientSum {ι : Type*} [Fintype ι] (V : ι → Point → ℝ) (x : Point) : ℝ :=
  ∑ j, ∑ i : Fin 3, |coordDeriv i (V j) x|

theorem tensorFamilyGradientSum_nonneg {ι : Type*} [Fintype ι] (V : ι → Point → S0) (x : Point) :
    0 ≤ tensorFamilyGradientSum V x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem scalarFamilyGradientSum_nonneg {ι : Type*} [Fintype ι] (V : ι → Point → ℝ) (x : Point) :
    0 ≤ scalarFamilyGradientSum V x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem tensor_coordDeriv_le_full_gradient (f : Point → S0) (x : Point) (i : Fin 3) :
    ‖coordDeriv i f x‖ ≤ Real.sqrt (gradientNormSq (ClassicalGradient f x)) := by
  rw [gradientNormSq_eq_sum_norm_sq]
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖ClassicalGradient f x j‖) (Finset.mem_univ i)

private theorem scalar_coordDeriv_le_full_gradient (f : Point → ℝ) (x : Point) (i : Fin 3) :
    |coordDeriv i f x| ≤ Real.sqrt (∑ j : Fin 3, |coordDeriv j f x| ^ 2) :=
  Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun j _ => sq_nonneg |coordDeriv j f x|) (Finset.mem_univ i))

private theorem tensorFamilyGradientSum_le {ι : Type*} [Fintype ι] (V : ι → Point → S0)
    (x : Point) {B : ℝ} (h : ∀ j (i : Fin 3), ‖coordDeriv i (V j) x‖ ≤ B) :
    tensorFamilyGradientSum V x ≤ (3 * Fintype.card ι : ℝ) * B := by
  calc
    _ ≤ ∑ _j : ι, ∑ _i : Fin 3, B := Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => h j i
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

private theorem scalarFamilyGradientSum_le {ι : Type*} [Fintype ι] (V : ι → Point → ℝ)
    (x : Point) {B : ℝ} (h : ∀ j (i : Fin 3), |coordDeriv i (V j) x| ≤ B) :
    scalarFamilyGradientSum V x ≤ (3 * Fintype.card ι : ℝ) * B := by
  calc
    _ ≤ ∑ _j : ι, ∑ _i : Fin 3, B := Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => h j i
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

private theorem ball_with_margin_subset {c x : Point} {s t : ℝ} (hx : x ∈ ball c s) :
    closedBall x (t - s) ⊆ ball c t := fun y hy => mem_ball.mpr (by
      linarith only [dist_triangle y x c, mem_closedBall.mp hy, mem_ball.mp hx])

private theorem screened_boundary_coefficient_inv_le {ell R m μ : ℝ}
    (hell : 0 < ell) (hR : 0 < R) (hμ : 0 < μ) (hm : μ ≤ m) :
    min 1 (6 * ell ^ 2 / (m * R ^ 2)) * ell⁻¹ ≤ max 1 (6 / μ) * R⁻¹ := by
  have hm₀ := hμ.trans_le hm
  rcases le_total ell R with h | h
  · have hCoeff : (6 : ℝ) / m ≤ 6 / μ := div_le_div_of_nonneg_left (by norm_num) hμ hm
    calc
      _ ≤ (6 * ell ^ 2 / (m * R ^ 2)) * ell⁻¹ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (inv_nonneg.mpr hell.le)
      _ = (6 / m) * (ell / R ^ 2) := by field_simp [hell.ne', hR.ne', hm₀.ne']
      _ ≤ (6 / μ) * R⁻¹ := by
        apply mul_le_mul hCoeff _ (div_nonneg hell.le (sq_nonneg _)) (by positivity)
        apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
        rwa [show R⁻¹ * R ^ 2 = R by field_simp]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (inv_nonneg.mpr hR.le)
  · calc
      _ ≤ 1 * ell⁻¹ := mul_le_mul_of_nonneg_right (min_le_left _ _) (inv_nonneg.mpr hell.le)
      _ ≤ 1 * R⁻¹ := mul_le_mul_of_nonneg_left (inv_le_inv₀ hell hR |>.mpr h) zero_le_one
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr hR.le)

private theorem sqrt_weighted_absorption {D X : ℝ} (hX : 0 ≤ X) :
    D * Real.sqrt (1 + X) ≤ X / 4 + D ^ 2 + 1 / 4 := by
  have hSq := Real.sq_sqrt (by linarith : 0 ≤ 1 + X)
  nlinarith only [hSq, sq_nonneg (2 * D - Real.sqrt (1 + X))]

/-- The differentiated Poisson equations may depend linearly on the scalar
gradients. Positive mass in the scalar equations absorbs the reverse
dependence, uniformly in the two scale parameters. -/
theorem exists_interior_gradient_bound_for_screened_families
    {ι κ : Type*} [Fintype ι] [Fintype κ] (hEstimate : InteriorPoissonGradientEstimate)
    (F μ : ℝ) (hF : 1 ≤ F) (hμ : 0 < μ) :
    ∃ C > (0 : ℝ), ∀ {Ω : Set Point}, IsOpen Ω → ∀ {c : Point} {s t : ℝ},
      0 < s → s < t → closedBall c t ⊆ Ω →
      ∀ (ell β : ℝ), 0 < ell → 0 ≤ β → β ≤ 1 → β ≤ ell →
      ∀ (m : κ → ℝ), (∀ j, μ ≤ m j) →
      ∀ (V : ι → Point → S0) (W : κ → Point → ℝ),
        (∀ j, ContDiffOn ℝ ∞ (V j) Ω) → (∀ j, ContDiffOn ℝ ∞ (W j) Ω) →
        (∀ x ∈ Ω, ∀ j, ‖V j x‖ ≤ F ∧ ‖laplacian (V j) x‖ ≤ F * (1 + scalarFamilyGradientSum W x)) →
        (∀ x ∈ Ω, ∀ j, |W j x| ≤ F ∧ |laplacian (W j) x| ≤ F / ell ^ 2) →
        (∀ x ∈ Ω, ∀ j i, |-ell ^ 2 * laplacian (coordDeriv i (W j)) x + m j * coordDeriv i (W j) x| ≤
          F * (1 + tensorFamilyGradientSum V x + β * scalarFamilyGradientSum W x)) →
        ∀ x ∈ ball c s, tensorFamilyGradientSum V x + scalarFamilyGradientSum W x ≤ C * (1 + (t - s)⁻¹) := by
  obtain ⟨Cv, hCv, hIV⟩ := exists_interior_tensor_gradient_interpolation hEstimate
  obtain ⟨Cw, hCw, hIW⟩ := exists_interior_scalar_gradient_interpolation hEstimate
  have hF₀ : 0 ≤ F := zero_le_one.trans hF
  let A := max Cv Cw * F
  let Nv := (3 * Fintype.card ι : ℝ)
  let Nw := (3 * Fintype.card κ : ℝ)
  let K := max 1 (6 / μ)
  let D := F / μ * (1 + 2 * A * (Nv + Nw)) + 2 * A * (1 + K)
  let B := Nv * A + Nw * D
  let C := B + B ^ 2 + 1
  have hA : 0 ≤ A := mul_nonneg (hCv.le.trans (le_max_left _ _)) hF₀
  have hNv : 0 ≤ Nv := by dsimp only [Nv]; positivity
  have hNw : 0 ≤ Nw := by dsimp only [Nw]; positivity
  have hK : 0 ≤ K := zero_le_one.trans (le_max_left _ _)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨4 * C, by positivity, ?_⟩
  intro Ω hΩ c s t hs hst hClosed ell β hell hβ hβ₁ hβell m hm V W hV hW hVe hWe hWp
  let P := tensorFamilyGradientSum V
  let Q := scalarFamilyGradientSum W
  let H (x : Point) := P x + Q x
  let Φ (r : ℝ) := sSup (H '' ball c r)
  have hP (x : Point) : 0 ≤ P x := tensorFamilyGradientSum_nonneg V x
  have hQ (x : Point) : 0 ≤ Q x := scalarFamilyGradientSum_nonneg W x
  have hH (x : Point) : 0 ≤ H x := add_nonneg (hP x) (hQ x)
  have hOp (r : ℝ) (hr : r ≤ t) : ball c r ⊆ Ω :=
    (ball_subset_ball hr).trans (ball_subset_closedBall.trans hClosed)
  have hHC : ContinuousOn H Ω := by
    have hPC : ContinuousOn P Ω := continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun i _ =>
      (contDiffOn_coordDeriv_infty hΩ (hV j) i).continuousOn.norm
    have hQC : ContinuousOn Q Ω := continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun i _ => by
      simpa only [Real.norm_eq_abs] using (contDiffOn_coordDeriv_infty hΩ (hW j) i).continuousOn.norm
    exact hPC.add hQC
  obtain ⟨M, hM⟩ := (isCompact_closedBall c t).exists_bound_of_continuousOn (hHC.mono hClosed)
  have hM' (r : ℝ) (hr : r ≤ t) (x : Point) (hx : x ∈ ball c r) : H x ≤ M :=
    (le_abs_self (H x)).trans (by simpa only [Real.norm_eq_abs] using
      (hM x (ball_subset_closedBall ((ball_subset_ball hr) hx))))
  have hΦB (r : ℝ) (hr : r ≤ t) : BddAbove (H '' ball c r) :=
    ⟨M, fun _ ⟨x, hx, hEq⟩ => hEq ▸ hM' r hr x hx⟩
  have hΦx {r : ℝ} (hr : r ≤ t) {x : Point} (hx : x ∈ ball c r) : H x ≤ Φ r :=
    le_csSup (hΦB r hr) ⟨x, hx, rfl⟩
  have hΦpos (r : ℝ) (hr : 0 < r) (hrt : r ≤ t) : 0 ≤ Φ r :=
    (hH c).trans (hΦx hrt (mem_ball_self hr))
  have hΦle {r L : ℝ} (hr : 0 < r) (h : ∀ x ∈ ball c r, H x ≤ L) : Φ r ≤ L :=
    csSup_le ⟨_, c, mem_ball_self hr, rfl⟩ (fun _ ⟨x, hx, hEq⟩ => hEq ▸ h x hx)
  have hIV' {r r' : ℝ} (hr : 0 < r) (hrr' : r < r') (hrt : r' ≤ t) {x : Point}
      (hx : x ∈ ball c r) (j : ι) (i : Fin 3) :
      ‖coordDeriv i (V j) x‖ ≤ A * ((r' - r)⁻¹ + Real.sqrt (1 + Φ r')) := by
    have hd : 0 < r' - r := sub_pos.mpr hrr'
    have hb : ball x (r' - r) ⊆ ball c r' := ball_subset_closedBall.trans (ball_with_margin_subset hx)
    have hbΩ := hb.trans (hOp r' hrt)
    have hΦ₀ := hΦpos r' (hr.trans hrr') hrt
    have hSq : Real.sqrt (F * (F * (1 + Φ r'))) = F * Real.sqrt (1 + Φ r') := by
      rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg F), Real.sqrt_sq hF₀]
    have hE := hIV x (r' - r) hd (V j) (((contDiffOn_infty.mp (hV j)) 2).mono hbΩ)
      F (F * (1 + Φ r')) hF₀ (by positivity) (fun y hy => (hVe y (hbΩ hy) j).1)
      (fun y hy => (hVe y (hbΩ hy) j).2.trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl
          ((le_add_of_nonneg_left (hP y)).trans (hΦx hrt (hb hy)))) hF₀))
    rw [hSq] at hE
    refine (tensor_coordDeriv_le_full_gradient (V j) x i).trans (hE.trans ?_)
    have hB := mul_le_mul_of_nonneg_right (le_max_left Cv Cw)
      (by positivity : 0 ≤ F / (r' - r) + F * Real.sqrt (1 + Φ r'))
    refine hB.trans_eq ?_
    dsimp only [A]
    ring
  have hIW' {r r' : ℝ} (hrr' : r < r') (hrt : r' ≤ t) {x : Point} (hx : x ∈ ball c r)
      (j : κ) (i : Fin 3) :
      |coordDeriv i (W j) x| ≤ A * ((r' - r)⁻¹ + ell⁻¹) := by
    have hd : 0 < r' - r := sub_pos.mpr hrr'
    have hb : ball x (r' - r) ⊆ ball c r' := ball_subset_closedBall.trans (ball_with_margin_subset hx)
    have hbΩ := hb.trans (hOp r' hrt)
    have hS : Real.sqrt (F * (F / ell ^ 2)) = F * ell⁻¹ := by
      rw [show F * (F / ell ^ 2) = (F * ell⁻¹) ^ 2 by field_simp, Real.sqrt_sq (by positivity)]
    have hE := hIW x (r' - r) hd (W j) (((contDiffOn_infty.mp (hW j)) 2).mono hbΩ)
      F (F / ell ^ 2) hF₀ (by positivity) (fun y hy => (hWe y (hbΩ hy) j).1)
        (fun y hy => (hWe y (hbΩ hy) j).2)
    rw [hS] at hE
    refine (scalar_coordDeriv_le_full_gradient (W j) x i).trans (hE.trans ?_)
    have hB := mul_le_mul_of_nonneg_right (le_max_right Cv Cw)
      (by positivity : 0 ≤ F / (r' - r) + F * ell⁻¹)
    refine hB.trans_eq ?_
    dsimp only [A]
    ring
  have step (r : ℝ) (hr : r ∈ Icc s t) (r' : ℝ) (hr' : r' ∈ Icc s t) (hrr' : r < r') :
      Φ r ≤ (1 / 4 : ℝ) * Φ r' + C * (1 + (r' - r)⁻¹) := by
    let d := r' - r
    let R := d / 2
    let u := r + R
    let Z := 1 + d⁻¹ + Real.sqrt (1 + Φ r')
    have hd : 0 < d := sub_pos.mpr hrr'
    have hR : 0 < R := half_pos hd
    have hr₀ : 0 < r := hs.trans_le hr.1
    have hu₀ : 0 < u := add_pos hr₀ hR
    have hur : u < r' := by dsimp only [u, R, d]; linarith
    have hRinv : (r' - u)⁻¹ = 2 * d⁻¹ := by
      have he : r' - u = d / 2 := by dsimp only [u, R, d]; ring
      rw [he]
      field_simp
    have hRinv' : R⁻¹ = 2 * d⁻¹ := by dsimp only [R]; field_simp
    have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
    have hd₁ : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
    have hS₀ : 0 ≤ Real.sqrt (1 + Φ r') := Real.sqrt_nonneg _
    have hΦ₀ := hΦpos r' (hr₀.trans hrr') hr'.2
    have hp (y : Point) (hy : y ∈ ball c u) : P y ≤ Nv * (2 * A * Z) := by
      apply tensorFamilyGradientSum_le
      intro j i
      refine (hIV' hu₀ hur hr'.2 hy j i).trans ?_
      rw [hRinv]
      nlinarith only [mul_nonneg hA hS₀, hA]
    let M₀ := A * (2 * d⁻¹ + ell⁻¹)
    have hM₀ : 0 ≤ M₀ := by dsimp only [M₀]; positivity
    have hW₀ (y : Point) (hy : y ∈ ball c u) (j : κ) (i : Fin 3) :
        |coordDeriv i (W j) y| ≤ M₀ := by
      simpa only [M₀, hRinv] using hIW' hur hr'.2 hy j i
    have hβM : β * M₀ ≤ 2 * A * Z := by
      have h1 : β * (2 * d⁻¹) ≤ 2 * d⁻¹ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hβ₁
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd₁)
      have h2 : β * ell⁻¹ ≤ 1 := (mul_le_mul_of_nonneg_right hβell (inv_nonneg.mpr hell.le)).trans_eq
        (mul_inv_cancel₀ hell.ne')
      calc
        _ ≤ A * (2 * d⁻¹ + 1) := by
          dsimp only [M₀]
          rw [mul_left_comm β, mul_add]
          exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) hA
        _ ≤ _ := by dsimp only [Z]; nlinarith only [mul_nonneg hA hS₀, hA]
    have hq (y : Point) (hy : y ∈ ball c u) : β * Q y ≤ Nw * (2 * A * Z) := by
      have h := scalarFamilyGradientSum_le W y (hW₀ y hy)
      calc
        _ ≤ β * (Nw * M₀) := mul_le_mul_of_nonneg_left h hβ
        _ = Nw * (β * M₀) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hβM hNw
    let F₀ := F * (1 + 2 * A * (Nv + Nw)) * Z
    have hF₁ : 0 ≤ F₀ := by dsimp only [F₀]; positivity
    have hforce (y : Point) (hy : y ∈ ball c u) :
        F * (1 + P y + β * Q y) ≤ F₀ := by
      rw [show F₀ = F * ((1 + 2 * A * (Nv + Nw)) * Z) by dsimp only [F₀]; ring]
      apply mul_le_mul_of_nonneg_left _ hF₀
      exact (add_le_add (add_le_add le_rfl (hp y hy)) (hq y hy)).trans (by
        dsimp only [Z] at *
        nlinarith only [hd₁, hS₀])
    apply hΦle hr₀
    intro x hx
    have hcap : closedBall x R ⊆ ball c u := by
      have he : u - r = R := by dsimp only [u]; ring
      rw [← he]
      exact ball_with_margin_subset hx
    have huΩ := hOp u (hur.le.trans hr'.2)
    have hscalar (j : κ) (i : Fin 3) : |coordDeriv i (W j) x| ≤ D * Z := by
      have hMass := hμ.trans_le (hm j)
      let σ := min (1 : ℝ) (6 * ell ^ 2 / (m j * R ^ 2))
      have hσ : σ ≤ 1 := min_le_left _ _
      have hσell : σ * ell⁻¹ ≤ K * R⁻¹ := screened_boundary_coefficient_inv_le hell hR hμ (hm j)
      have hX := screened_solution_abs_le_at_ball_center hΩ hR (sq_pos_of_pos hell) hMass hF₁ hM₀
        (hcap.trans huΩ) ((contDiffOn_infty.mp (contDiffOn_coordDeriv_infty hΩ (hW j) i)) 2)
        (fun y hy => hW₀ y (hcap (sphere_subset_closedBall hy)) j i)
        (fun y hy => (hWp y (huΩ (hcap (ball_subset_closedBall hy))) j i).trans
          (hforce y (hcap (ball_subset_closedBall hy))))
      have hFle : F₀ / m j ≤ F₀ / μ := div_le_div_of_nonneg_left hF₁ hμ (hm j)
      have hBdry : M₀ * σ ≤ (2 * A * (1 + K)) * Z := by
        calc
          _ = A * (σ * (2 * d⁻¹) + σ * ell⁻¹) := by dsimp only [M₀]; ring
          _ ≤ A * (1 * (2 * d⁻¹) + K * R⁻¹) :=
            mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hσ (by positivity)) hσell) hA
          _ = 2 * A * (1 + K) * d⁻¹ := by rw [hRinv']; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp only [Z]; linarith) (by positivity)
      exact hX.trans ((add_le_add hFle hBdry).trans_eq (by dsimp only [F₀, D]; ring))
    have hv (j : ι) (i : Fin 3) : ‖coordDeriv i (V j) x‖ ≤ A * Z :=
      (hIV' hr₀ hrr' hr'.2 hx j i).trans
        (mul_le_mul_of_nonneg_left (by dsimp only [Z]; linarith) hA)
    have hSum : H x ≤ B * Z :=
      (add_le_add (tensorFamilyGradientSum_le V x hv) (scalarFamilyGradientSum_le W x hscalar)).trans_eq
        (by dsimp only [B]; ring)
    refine hSum.trans ?_
    have hAbs := sqrt_weighted_absorption (D := B) hΦ₀
    dsimp only [C, Z]
    nlinarith only [hAbs, hd₁, mul_nonneg (sq_nonneg B) hd₁]
  have hBound := absorb_interior_radius_bounds hst hC.le Φ (fun r hr => hΦle (hs.trans_le hr.1)
    (hM' r hr.2)) step
  intro x hx
  refine (hΦx hst.le hx).trans (hBound.trans ?_)
  dsimp only [C]
  have hInv : 0 ≤ (t - s)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hst.le)
  rw [div_eq_mul_inv]
  nlinarith only [hC]

end Thesis

end
