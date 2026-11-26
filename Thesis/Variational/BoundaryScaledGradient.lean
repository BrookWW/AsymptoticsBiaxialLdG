module

public import Thesis.Variational.BoundaryCaccioppoli
public import Thesis.Variational.BoundaryPoissonEstimate
public import Thesis.Variational.BoundaryMorreyNorms
public import Thesis.Variational.EulerLagrange
import Thesis.Variational.BoundaryDefect
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Uniform scaled gradients for classical solutions of the global Dirichlet problem. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem frontier_meets_ball_of_not_subset
    {U : Set Point} (hU : IsOpen U) {x : Point} (hx : x ∈ U) {r : ℝ} (hr : 0 < r)
    (h : ¬ Metric.ball x r ⊆ U) : ∃ c ∈ frontier U, dist x c < r := by
  by_contra hn
  have hOutside : Metric.ball x r ⊆ U ∪ (closure U)ᶜ := by
    intro y hy
    by_cases hyU : y ∈ U
    · exact Or.inl hyU
    · refine Or.inr fun hyC => ?_
      have hF : y ∈ frontier U := by rw [frontier, hU.interior_eq]; exact ⟨hyC, hyU⟩
      exact hn ⟨y, hF, by rwa [dist_comm]⟩
  have hDis : Disjoint U (closure U)ᶜ := Set.disjoint_left.mpr fun _ hy hz => hz (subset_closure hy)
  rcases IsPreconnected.subset_or_subset hU isClosed_closure.isOpen_compl hDis hOutside
    (convex_ball x r).isPreconnected with hL | hR
  · exact h hL
  · exact hR (Metric.mem_ball_self hr) (subset_closure hx)

/-- The global scaled gradient is bounded by one constant for every
classical solution with the fixed trace and uniform amplitude bound.
Interior balls use the generic Poisson estimate, and the wall caps use
the zero-trace integral identity and the (p=4) Poisson estimate. -/
theorem exists_uniform_scaledGradient_bound_on_smoothDomain
    (hGG : External.LipschitzGaussGreen) (hPoisson : External.ZeroTraceBoundaryPoissonL4GradientEstimate)
    (hInterior : InteriorPoissonGradientEstimate)
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    {b : Point → S0} (hb : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) b) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ElasticScale) (Q : Point → S0),
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U → ContDiffOn ℝ 2 Q (closure U) →
      EqOn Q b (frontier U) → (∀ x ∈ U, ‖Q x‖ ≤ M) →
      (∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) →
      ∀ x ∈ U, (ε : ℝ) * Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ C := by
  obtain ⟨Cᵢ, hCᵢ, hInt⟩ := hInterior
  obtain ⟨R, Cᵦ, hR, hCᵦ, hBdry⟩ := exists_closed_cap_poisson_gradient_bound_frobenius hPoisson hU
  obtain ⟨Ccc, hCcc, hCC⟩ := exists_boundary_caccioppoli_of_zero_trace hGG hU
  have hb₂ : ContDiff ℝ 2 b := hb.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨Mᵦ, B₁, B₂, hMᵦ, hB₁, hB₂, hbVal, hbD, hbLap⟩ := exists_compact_trace_bounds hU hb₂
  obtain ⟨F₀, hF₀, hForce⟩ := exists_bound_bulkGradient_on_norm_le a hM
  let F := F₀ + B₂
  let M₀ := M + Mᵦ
  let L := max 1 (R / 2)⁻¹
  let H := Ccc * (M₀ ^ 2 + M₀ * F)
  let κ := Real.pi * 4 / 3
  let B := Cᵦ * (L * Real.sqrt H + F * κ ^ (1 / 4 : ℝ)) + B₁
  let A := 8 * L * Cᵢ * (M + F₀)
  let C := A + 3 * B + 1
  have hF : 0 ≤ F := add_nonneg hF₀ hB₂
  have hM₀ : 0 ≤ M₀ := add_nonneg hM hMᵦ
  have hL : 0 ≤ L := zero_le_one.trans (le_max_left _ _)
  have hH : 0 ≤ H := mul_nonneg hCcc.le (add_nonneg (sq_nonneg _) (mul_nonneg hM₀ hF))
  have hκ : 0 ≤ κ := by dsimp only [κ]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 < C := add_pos_of_nonneg_of_pos (add_nonneg hA (mul_nonneg (by norm_num) hB)) zero_lt_one
  refine ⟨C, hC, ?_⟩
  intro ε Q hQ hClose hTrace hRange hEuler x hx
  have hε : 0 < (ε : ℝ) := ε.2.1
  have hε₁ : (ε : ℝ) ≤ 1 := ε.2.2.le
  let r := min (ε : ℝ) (R / 2)
  have hr : 0 < r := lt_min hε (half_pos hR)
  have hrR : r < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hrε : r ≤ (ε : ℝ) := min_le_left _ _
  have hεr : (ε : ℝ) ≤ L * r := by
    rcases le_total (ε : ℝ) (R / 2) with h | h
    · change (ε : ℝ) ≤ L * min (ε : ℝ) (R / 2)
      rw [min_eq_left h]
      exact le_mul_of_one_le_left hε.le (le_max_left _ _)
    · change (ε : ℝ) ≤ L * min (ε : ℝ) (R / 2)
      rw [min_eq_right h]
      exact hε₁.trans ((inv_mul_cancel₀ (half_pos hR).ne').symm.le.trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (half_pos hR).le))
  have hεr' : (ε : ℝ) * r⁻¹ ≤ L := by
    have h := mul_le_mul_of_nonneg_right hεr (inv_nonneg.mpr hr.le)
    rwa [mul_assoc, mul_inv_cancel₀ hr.ne', mul_one] at h
  have hrε' : r * (ε : ℝ)⁻¹ ≤ 1 :=
    (mul_le_mul_of_nonneg_right hrε (inv_nonneg.mpr hε.le)).trans_eq (mul_inv_cancel₀ hε.ne')
  have hQ₂ : ContDiffOn ℝ 2 Q U := hQ.of_le (WithTop.coe_le_coe.mpr le_top)
  let FQ (y : Point) := (ε : ℝ)⁻¹ ^ 2 • bulkGradient a (Q y)
  have hLapQ (y : Point) (hy : y ∈ U) : (↑(laplacian Q y) : Tensor) = FQ y := by
    have hScale : (ε : ℝ)⁻¹ ^ 2 * (ε : ℝ) ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hε.ne', one_pow]
    calc
      _ = (1 : ℝ) • (↑(laplacian Q y) : Tensor) := (one_smul ℝ _).symm
      _ = ((ε : ℝ)⁻¹ ^ 2 * (ε : ℝ) ^ 2) • (↑(laplacian Q y) : Tensor) :=
        congrArg (· • (↑(laplacian Q y) : Tensor)) hScale.symm
      _ = (ε : ℝ)⁻¹ ^ 2 • ((ε : ℝ) ^ 2 • (↑(laplacian Q y) : Tensor)) := mul_smul _ _ _
      _ = _ := congrArg ((ε : ℝ)⁻¹ ^ 2 • ·) (hEuler y hy)
  have hFQ (y : Point) (hy : y ∈ U) : ‖FQ y‖ ≤ (ε : ℝ)⁻¹ ^ 2 * F₀ := by
    change ‖(ε : ℝ)⁻¹ ^ 2 • bulkGradient a (Q y)‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hForce (Q y) (hRange y hy)) (sq_nonneg _)
  by_cases hBall : Metric.ball x (r / 8) ⊆ U
  · let s := r / 8
    have hs : 0 < s := by dsimp only [s]; positivity
    have hsε : s ≤ (ε : ℝ) := (show s ≤ r by dsimp only [s]; linarith only [hr]).trans hrε
    have hFin := hInt x s hs Q FQ M ((ε : ℝ)⁻¹ ^ 2 * F₀) (hQ₂.mono hBall)
      (fun y hy => hLapQ y (hBall hy)) (fun y hy => hRange y (hBall hy)) (fun y hy => hFQ y (hBall hy))
    have hSmall : s ^ 2 * ((ε : ℝ)⁻¹ ^ 2 * F₀) ≤ F₀ := by
      have hf : 0 ≤ s * (ε : ℝ)⁻¹ := mul_nonneg hs.le (inv_nonneg.mpr hε.le)
      have hq : s * (ε : ℝ)⁻¹ ≤ 1 :=
        (mul_le_mul_of_nonneg_right hsε (inv_nonneg.mpr hε.le)).trans_eq (mul_inv_cancel₀ hε.ne')
      calc
        _ = (s * (ε : ℝ)⁻¹) ^ 2 * F₀ := by ring
        _ ≤ 1 ^ 2 * F₀ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hf hq 2) hF₀
        _ = _ := by simp only [one_pow, one_mul]
    have hεs : (ε : ℝ) ≤ 8 * L * s := by dsimp only [s]; nlinarith only [hεr]
    have hBound : (ε : ℝ) * Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ A := by
      calc
        _ ≤ (8 * L * s) * Real.sqrt (gradientNormSq (ClassicalGradient Q x)) :=
          mul_le_mul_of_nonneg_right hεs (Real.sqrt_nonneg _)
        _ = (8 * L) * (s * Real.sqrt (gradientNormSq (ClassicalGradient Q x))) := by ring
        _ ≤ (8 * L) * (Cᵢ * (M + s ^ 2 * ((ε : ℝ)⁻¹ ^ 2 * F₀))) :=
          mul_le_mul_of_nonneg_left hFin (mul_nonneg (by norm_num) hL)
        _ ≤ (8 * L) * (Cᵢ * (M + F₀)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hSmall) hCᵢ.le) (mul_nonneg (by norm_num) hL)
        _ = A := by dsimp only [A]; ring
    exact hBound.trans (by dsimp only [C]; linarith only [hB])
  obtain ⟨c, hc, hDist⟩ := frontier_meets_ball_of_not_subset hU.1.1 hx (by positivity : 0 < r / 8) hBall
  let v (y : Point) := Q y - b y
  let G (y : Point) := gradientNormSq (ClassicalGradient v y)
  let Fε := F * (ε : ℝ)⁻¹ ^ 2
  have hFε : 0 ≤ Fε := mul_nonneg hF (sq_nonneg _)
  have hv : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) v U := hQ.sub hb.contDiffOn
  have hv₂ : ContDiffOn ℝ 2 v (closure U) := hClose.sub hb₂.contDiffOn
  have hv0 : EqOn v (fun _ => 0) (frontier U) := fun y hy => sub_eq_zero.mpr (hTrace hy)
  have hvRange (y : Point) (hy : y ∈ U) : ‖v y‖ ≤ M₀ :=
    (norm_sub_le _ _).trans (add_le_add (hRange y hy) (hbVal y (subset_closure hy)))
  have hvForce (y : Point) (hy : y ∈ U) : ‖laplacian v y‖ ≤ Fε := by
    have hvL : laplacian v y = laplacian Q y - laplacian b y :=
      laplacian_sub_of_contDiffOn hU.1.1 hQ₂ hb₂.contDiffOn hy
    rw [hvL]
    have hQF : ‖laplacian Q y‖ ≤ (ε : ℝ)⁻¹ ^ 2 * F₀ := by
      change ‖(↑(laplacian Q y) : Tensor)‖ ≤ _
      rw [hLapQ y hy]
      exact hFQ y hy
    have hε₂ : 1 ≤ (ε : ℝ)⁻¹ ^ 2 := by
      have hεinv := (one_le_inv₀ hε).mpr hε₁
      simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hεinv 2
    have hbF := hbLap y (subset_closure hy)
    calc
      _ ≤ ‖laplacian Q y‖ + ‖laplacian b y‖ := norm_sub_le _ _
      _ ≤ (ε : ℝ)⁻¹ ^ 2 * F₀ + B₂ * (ε : ℝ)⁻¹ ^ 2 :=
        add_le_add hQF (hbF.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hε₂ hB₂))
      _ = _ := by dsimp only [Fε, F]; ring
  let D := U ∩ Metric.ball c r
  let μ := volume.restrict D
  have hD : IsOpen D := hU.1.1.inter Metric.isOpen_ball
  have hG₀ (y : Point) : 0 ≤ G y := by
    change 0 ≤ gradientNormSq (ClassicalGradient v y)
    rw [gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hMass : (∫⁻ y, ENNReal.ofReal (G y) ∂μ) ≤ ENNReal.ofReal (H * r) := by
    have hCC' := hCC v hv hv₂ hv0 M₀ Fε hM₀ hFε hvRange hvForce c r hr
    refine hCC'.trans (ENNReal.ofReal_le_ofReal ?_)
    have hScale : r ^ 2 * (ε : ℝ)⁻¹ ^ 2 ≤ 1 := by
      rw [← mul_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (mul_nonneg hr.le (inv_nonneg.mpr hε.le)) hrε' 2
    have hF₁ := mul_le_mul_of_nonneg_left hScale (mul_nonneg (mul_nonneg hr.le hM₀) hF)
    dsimp only [Fε, H]
    rw [mul_assoc Ccc (M₀ ^ 2 + M₀ * F) r]
    apply mul_le_mul_of_nonneg_left _ hCcc.le
    linarith only [hF₁]
  have hVol : μ univ ≤ ENNReal.ofReal (κ * r ^ 3) := by
    change (volume.restrict D) univ ≤ _
    rw [Measure.restrict_apply_univ]
    calc
      _ ≤ volume (Metric.ball c r) := measure_mono inter_subset_right
      _ = _ := by rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hr.le,
        ← ENNReal.ofReal_mul (pow_nonneg hr.le 3), mul_comm (r ^ 3)]
  haveI : IsFiniteMeasure μ := ⟨hVol.trans_lt ENNReal.ofReal_lt_top⟩
  have hVSub : D ⊆ closure U := fun y hy => subset_closure hy.1
  have hGm : AEStronglyMeasurable G μ :=
    (continuousOn_classicalGradientNormSq hD (hv₂.mono hVSub)).aestronglyMeasurable hD.measurableSet
  obtain ⟨hGL, hGbound⟩ := memLp_sqrt_two_of_lintegral_bound hGm (Eventually.of_forall hG₀)
    (mul_nonneg hH hr.le) hMass
  have hFa : ∀ᵐ y ∂μ, ‖laplacian v y‖ ≤ (fun _ : Point => Fε) y :=
    (ae_restrict_mem hD.measurableSet).mono fun y hy => hvForce y hy.1
  have hFM : MemLp (laplacian v) 4 μ := (memLp_const Fε).mono'
    ((continuousOn_laplacian_of_contDiffOn_two hD (hv₂.mono hVSub)).aestronglyMeasurable hD.measurableSet) hFa
  have hFbound : (eLpNorm (fun _ : Point => Fε) 4 μ).toReal ≤ Fε * (κ * r ^ 3) ^ (1 / 4 : ℝ) := by
    simpa only [ENNReal.toReal_ofNat] using toReal_eLpNorm_const_le_of_measure_le
      (p := (4 : ℝ≥0∞)) (by norm_num) (by norm_num) hFε hVol (mul_nonneg hκ (pow_nonneg hr.le 3))
  have hGrad (y : Point) (hy : y ∈ D) :
      0 ≤ Real.sqrt (G y) ∧ ∀ u : Point, ‖(fderiv ℝ v y) u‖ ≤ Real.sqrt (G y) * ‖u‖ := by
    refine ⟨Real.sqrt_nonneg _, fun u => ?_⟩
    rw [← gradientFromColumns_classicalGradient, mul_comm]
    exact norm_gradientFromColumns_le _ _
  have hxB : x ∈ Metric.ball c (r / 2) := hDist.trans (by linarith only [hr])
  have hP (u : Point) := hBdry c hc r ⟨hr, hrR⟩ v (laplacian v) (fun y => Real.sqrt (G y)) (fun _ => Fε)
    (hv₂.mono inter_subset_left) (hv0.mono inter_subset_left) (fun _ _ => rfl) hFM hGL (memLp_const Fε)
    hGrad (fun y hy => hvForce y hy.1) x ⟨subset_closure hx, hxB⟩ u
  have hR₂ : r ^ (-3 / 2 : ℝ) * (eLpNorm (fun y => Real.sqrt (G y)) 2 μ).toReal ≤ r⁻¹ * Real.sqrt H := by
    refine (mul_le_mul_of_nonneg_left hGbound (Real.rpow_nonneg hr.le _)).trans_eq ?_
    rw [Real.sqrt_mul hH, Real.sqrt_eq_rpow r]
    calc
      _ = (r ^ (-3 / 2 : ℝ) * r ^ (1 / 2 : ℝ)) * Real.sqrt H := by ring
      _ = _ := by rw [← Real.rpow_add hr, show (-3 / 2 : ℝ) + 1 / 2 = -1 by norm_num, Real.rpow_neg_one]
  have hR₄ : r ^ (1 / 4 : ℝ) * (eLpNorm (fun _ : Point => Fε) 4 μ).toReal ≤ r * Fε * κ ^ (1 / 4 : ℝ) := by
    refine (mul_le_mul_of_nonneg_left hFbound (Real.rpow_nonneg hr.le _)).trans_eq ?_
    rw [Real.mul_rpow hκ (pow_nonneg hr.le _), ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    have hr₄ : r ^ (1 / 4 : ℝ) * r ^ ((3 : ℕ) * (1 / 4 : ℝ)) = r := by
      rw [← Real.rpow_add hr, show (1 / 4 : ℝ) + (3 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one]
    calc
      _ = (r ^ (1 / 4 : ℝ) * r ^ ((3 : ℕ) * (1 / 4 : ℝ))) * Fε * κ ^ (1 / 4 : ℝ) := by ring
      _ = _ := by rw [hr₄]
  have hFF : (ε : ℝ) * (r * Fε * κ ^ (1 / 4 : ℝ)) ≤ F * κ ^ (1 / 4 : ℝ) := by
    have hEq : (ε : ℝ) * (r * Fε * κ ^ (1 / 4 : ℝ)) = (r * (ε : ℝ)⁻¹) * (F * κ ^ (1 / 4 : ℝ)) := by
      dsimp only [Fε]
      field_simp [hε.ne']
    rw [hEq]
    exact (mul_le_mul_of_nonneg_right hrε' (mul_nonneg hF (Real.rpow_nonneg hκ _))).trans_eq (one_mul _)
  have hG' : (ε : ℝ) * (r⁻¹ * Real.sqrt H) ≤ L * Real.sqrt H := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hεr' (Real.sqrt_nonneg _)
  have hxCl : closure U ∈ 𝓝 x := mem_of_superset (hU.1.1.mem_nhds hx) subset_closure
  have hVgrad (u : Point) : (ε : ℝ) * ‖(fderiv ℝ v x) u‖ ≤
      (Cᵦ * (L * Real.sqrt H + F * κ ^ (1 / 4 : ℝ))) * ‖u‖ := by
    have h := hP u
    rw [fderivWithin_of_mem_nhds hxCl] at h
    refine (mul_le_mul_of_nonneg_left h hε.le).trans ?_
    have ht : (ε : ℝ) *
        (r ^ (-3 / 2 : ℝ) * (eLpNorm (fun y => Real.sqrt (G y)) 2 μ).toReal +
          r ^ (1 / 4 : ℝ) * (eLpNorm (fun _ : Point => Fε) 4 μ).toReal) ≤
        L * Real.sqrt H + F * κ ^ (1 / 4 : ℝ) := by
      rw [mul_add]
      exact add_le_add
        ((mul_le_mul_of_nonneg_left hR₂ hε.le).trans hG')
        ((mul_le_mul_of_nonneg_left hR₄ hε.le).trans hFF)
    convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hCᵦ.le) (norm_nonneg u) using 1
    ring
  have hbAt (u : Point) : (ε : ℝ) * ‖(fderiv ℝ b x) u‖ ≤ B₁ * ‖u‖ := by
    have h := hbD x (subset_closure hx) u
    rw [fderivWithin_of_mem_nhds hxCl] at h
    exact (mul_le_mul_of_nonneg_right hε₁ (norm_nonneg _)).trans (by simpa only [one_mul] using h)
  have hDx (u : Point) : (ε : ℝ) * ‖(fderiv ℝ Q x) u‖ ≤ B * ‖u‖ := by
    have hvD := (hv.differentiableOn (by simp) x hx).differentiableAt (hU.1.1.mem_nhds hx)
    have h := (hvD.hasFDerivAt.add (hb.differentiable (by simp) x).hasFDerivAt).fderiv
    have hEq : v + b = Q := funext fun y => sub_add_cancel _ _
    rw [hEq] at h
    have hEq' : (fderiv ℝ Q x) u = (fderiv ℝ v x) u + (fderiv ℝ b x) u :=
      DFunLike.congr_fun h u
    rw [hEq']
    calc
      _ ≤ (ε : ℝ) * (‖(fderiv ℝ v x) u‖ + ‖(fderiv ℝ b x) u‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hε.le
      _ ≤ _ := by rw [mul_add]; exact (add_le_add (hVgrad u) (hbAt u)).trans_eq (by dsimp only [B]; ring)
  have hSq : (ε : ℝ) ^ 2 * gradientNormSq (ClassicalGradient Q x) ≤ 3 * B ^ 2 := by
    rw [gradientNormSq_eq_sum_norm_sq, Finset.mul_sum]
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3))) (f := fun i =>
      (ε : ℝ) ^ 2 * ‖ClassicalGradient Q x i‖ ^ 2) (g := fun _ => B ^ 2) (fun i _ => by
        have h := hDx (axis i)
        have hi : ‖axis i‖ = 1 := by simp [axis]
        rw [hi, mul_one] at h
        change (ε : ℝ) * ‖ClassicalGradient Q x i‖ ≤ B at h
        simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg hε.le (norm_nonneg _)) h 2)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using h
  have hGQ : 0 ≤ gradientNormSq (ClassicalGradient Q x) := by
    rw [gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hFin : (ε : ℝ) * Real.sqrt (gradientNormSq (ClassicalGradient Q x)) ≤ 3 * B := by
    apply (sq_le_sq₀ (mul_nonneg hε.le (Real.sqrt_nonneg _)) (mul_nonneg (by norm_num) hB)).mp
    rw [mul_pow, Real.sq_sqrt hGQ]
    nlinarith only [hSq, sq_nonneg B]
  exact hFin.trans (by dsimp only [C]; linarith only [hA])

end Thesis

end
