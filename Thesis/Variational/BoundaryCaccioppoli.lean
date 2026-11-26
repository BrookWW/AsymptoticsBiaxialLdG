module

public import Thesis.Variational.WholeWallEnergy
import Thesis.Variational.BoundarySmallEnergy
import Thesis.Variational.BoundarySubsolution
import Thesis.Variational.BoundaryPoissonEstimate
import Thesis.Variational.EnergyEstimate
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Whole-wall Green comparison with compactly supported cutoffs. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius RealInnerProductSpace

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem coordDeriv_mul_real {f g : Point → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (j : Fin 3) :
    coordDeriv j (fun y => f y * g y) x = f x * coordDeriv j g x + g x * coordDeriv j f x := by
  have h := DFunLike.congr_fun (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv (axis j)
  simpa only [coordDeriv, Pi.mul_def, add_apply, smul_apply, smul_eq_mul] using h

private theorem coordDeriv_sub_real {f g : Point → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (j : Fin 3) :
    coordDeriv j (fun y => f y - g y) x = coordDeriv j f x - coordDeriv j g x := by
  have h := DFunLike.congr_fun (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv (axis j)
  simpa only [coordDeriv, Pi.sub_def, sub_apply] using h

private theorem laplacian_const_real (a : ℝ) (x : Point) :
    laplacian (fun _ : Point => a) x = 0 := by
  have h (j : Fin 3) (c : ℝ) : coordDeriv j (fun _ : Point => c) = fun _ => 0 := by
    funext y
    exact DFunLike.congr_fun (hasFDerivAt_const c y).fderiv (axis j)
  simp only [laplacian, h, Finset.sum_const_zero]

/-- The scalar Green expression has zero integral when the function and
its within-closure derivative vanish on the physical wall. -/
theorem integral_cutoff_laplacian_difference_eq_zero
    (hGG : External.LipschitzGaussGreen) {U : Set Point} (hU : IsSmoothDomain U)
    {g χ : Point → ℝ} (hg : ContDiffOn ℝ 2 g (closure U)) (hχ : ContDiff ℝ 2 χ)
    (h0 : EqOn g (fun _ => 0) (frontier U))
    (hD0 : EqOn (fderivWithin ℝ g (closure U)) (fun _ => 0) (frontier U)) :
    IntegrableOn (fun x => χ x * laplacian g x - g x * laplacian χ x) U volume ∧
      (∫ x in U, χ x * laplacian g x - g x * laplacian χ x) = 0 := by
  obtain ⟨ν, _, hGeo, _⟩ := hU.exists_piecewiseRegularBoundary
  let Dg (j : Fin 3) (x : Point) := (fderivWithin ℝ g (closure U) x) (axis j)
  let Dχ (j : Fin 3) := coordDeriv j χ
  let X (j : Fin 3) (x : Point) := χ x * Dg j x - g x * Dχ j x
  have hDg (j : Fin 3) : ContDiffOn ℝ 1 (Dg j) (closure U) :=
    (ContinuousLinearMap.apply ℝ ℝ (axis j)).contDiff.comp_contDiffOn
      (hg.fderivWithin hU.uniqueDiffOn_closure (by norm_num))
  have hDχ (j : Fin 3) : ContDiff ℝ 1 (Dχ j) :=
    (ContinuousLinearMap.apply ℝ ℝ (axis j)).contDiff.comp (hχ.fderiv_right (by norm_num))
  have hχ₁ : ContDiffOn ℝ 1 χ (closure U) := (hχ.of_le (by norm_num)).contDiffOn
  have hg₁ : ContDiffOn ℝ 1 g (closure U) := hg.of_le (by norm_num)
  have hX (j : Fin 3) : ContDiffOn ℝ 1 (X j) (closure U) :=
    (hχ₁.mul (hDg j)).sub (hg₁.mul (hDχ j).contDiffOn)
  have hX0 (j : Fin 3) (x : Point) (hx : x ∈ frontier U) : X j x = 0 := by
    change χ x * (fderivWithin ℝ g (closure U) x) (axis j) - g x * _ = 0
    rw [hD0 hx, h0 hx, zero_apply, mul_zero, zero_mul, sub_self]
  have hFlux (j : Fin 3) := hGG U ν hGeo (X j) (hX j) j
  have hIj (j : Fin 3) : (∫ x in U, coordDeriv j (X j) x) = 0 := by
    rw [(hFlux j).2.2]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [hX0 j x hx, zero_mul]
  have hDs (j : Fin 3) {x : Point} (hx : x ∈ U) : Dg j =ᶠ[𝓝 x] coordDeriv j g := by
    filter_upwards [hU.1.1.mem_nhds hx] with y hy
    have hCl : closure U ∈ 𝓝 y := mem_of_superset (hU.1.1.mem_nhds hy) subset_closure
    change (fderivWithin ℝ g (closure U) y) (axis j) = (fderiv ℝ g y) (axis j)
    rw [fderivWithin_of_mem_nhds hCl]
  have hId (j : Fin 3) (x : Point) (hx : x ∈ U) :
      coordDeriv j (X j) x =
        χ x * coordDeriv j (coordDeriv j g) x - g x * coordDeriv j (coordDeriv j χ) x := by
    have hCl : closure U ∈ 𝓝 x := mem_of_superset (hU.1.1.mem_nhds hx) subset_closure
    have hχa := hχ.differentiable (by norm_num) x
    have hga := (hg₁.differentiableOn one_ne_zero x (subset_closure hx)).differentiableAt hCl
    have hDga := ((hDg j).differentiableOn one_ne_zero x (subset_closure hx)).differentiableAt hCl
    have hDχa := (hDχ j).differentiable one_ne_zero x
    have hv := (hDs j hx).eq_of_nhds
    have hd := DFunLike.congr_fun ((hDs j hx).fderiv_eq (𝕜 := ℝ)) (axis j)
    change coordDeriv j (Dg j) x = coordDeriv j (coordDeriv j g) x at hd
    have hA : DifferentiableAt ℝ (fun y => χ y * Dg j y) x := by
      simpa only [Pi.mul_def] using hχa.mul hDga
    have hB : DifferentiableAt ℝ (fun y => g y * Dχ j y) x := by
      simpa only [Pi.mul_def] using hga.mul hDχa
    change coordDeriv j (fun y => χ y * Dg j y - g y * Dχ j y) x = _
    rw [coordDeriv_sub_real hA hB, coordDeriv_mul_real hχa hDga,
      coordDeriv_mul_real hga hDχa, hv, hd]
    dsimp only [Dχ]
    ring
  have hEq : (fun x => ∑ j : Fin 3, coordDeriv j (X j) x) =ᵐ[volume.restrict U]
      (fun x => χ x * laplacian g x - g x * laplacian χ x) := by
    filter_upwards [ae_restrict_mem hU.1.1.measurableSet] with x hx
    simp_rw [hId _ _ hx]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  have hI : IntegrableOn (fun x => ∑ j : Fin 3, coordDeriv j (X j) x) U volume :=
    integrable_finsetSum Finset.univ (fun j _ => (hFlux j).1)
  refine ⟨hI.congr hEq, ?_⟩
  rw [← integral_congr_ae hEq, integral_finsetSum _ (fun j _ => (hFlux j).1)]
  simp only [hIj, Finset.sum_const_zero]

/-- A single fixed radial cutoff gives smooth cutoffs with exact
quadratic Laplacian scale and support in the doubled ball. -/
theorem exists_scaled_laplacian_ball_cutoffs :
    ∃ C : ℝ, 0 < C ∧ ∀ c : Point, ∀ r : ℝ, 0 < r → ∃ χ : Point → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x ∈ Metric.ball c r, χ x = 1) ∧
      (∀ x ∉ Metric.closedBall c (2 * r), χ x = 0 ∧ laplacian χ x = 0) ∧
      ∀ x, |laplacian χ x| ≤ C * r⁻¹ ^ 2 := by
  let ψ : ContDiffBump (0 : Point) := ⟨1, 2, by norm_num, by norm_num⟩
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (ψ : Point → ℝ) := ψ.contDiff
  have hLapC := continuousOn_laplacian_of_contDiffOn_two isOpen_univ
    (hψ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Point) 2).exists_bound_of_continuousOn
    (hLapC.mono (subset_univ _))
  let C := max B 1
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  have hψZero (x : Point) (hx : x ∉ Metric.closedBall 0 2) : ψ x = 0 := by
    have h : x ∉ Function.support (ψ : Point → ℝ) := by
      rw [ψ.support_eq]
      exact fun h => hx (Metric.ball_subset_closedBall h)
    exact Function.notMem_support.mp h
  have hψLap (x : Point) : |laplacian (ψ : Point → ℝ) x| ≤ C := by
    by_cases hx : x ∈ Metric.closedBall 0 2
    · have h : |laplacian (ψ : Point → ℝ) x| ≤ B := by
        simpa only [Real.norm_eq_abs] using hB x hx
      exact h.trans (le_max_left _ _)
    · have hEq : (ψ : Point → ℝ) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
        exact hψZero y hy
      rw [laplacian_eq_of_eventuallyEq hEq, laplacian_const_real, abs_zero]
      exact hC.le
  refine ⟨C, hC, fun c r hr => ?_⟩
  let A (x : Point) := r⁻¹ • (x - c)
  let χ := (ψ : Point → ℝ) ∘ A
  have hA : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) A := (contDiff_id.sub contDiff_const).const_smul _
  have hRadius (x : Point) : ‖A x‖ = r⁻¹ * ‖x - c‖ := by
    change ‖r⁻¹ • (x - c)‖ = _
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hEq : A = fun x => -(r⁻¹ • c) + r⁻¹ • x := by
    funext x
    change r⁻¹ • (x - c) = _
    rw [smul_sub]
    abel
  have hχLap (x : Point) : laplacian χ x = r⁻¹ ^ 2 * laplacian (ψ : Point → ℝ) (A x) := by
    change laplacian ((ψ : Point → ℝ) ∘ A) x = _
    rw [hEq]
    exact laplacian_affine_dilation isOpen_univ (hψ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
      (-(r⁻¹ • c)) r⁻¹ (mem_univ _)
  refine ⟨χ, hψ.comp hA, fun x => ⟨ψ.nonneg, ψ.le_one⟩, ?_, ?_, ?_⟩
  · intro x hx
    apply ψ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, hRadius]
    have h : ‖x - c‖ ≤ r := (show ‖x - c‖ < r from by simpa only [Metric.mem_ball, dist_eq_norm] using hx).le
    exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hr.le)).trans_eq (inv_mul_cancel₀ hr.ne')
  · intro x hx
    have hNear : ∀ᶠ y in 𝓝 x, y ∉ Metric.closedBall c (2 * r) :=
      Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx
    have hχ0 : χ =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hNear] with y hy
      apply hψZero
      intro hyA
      have hNorm : ‖A y‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hyA
      rw [hRadius, ← div_eq_inv_mul] at hNorm
      have hB := (div_le_iff₀ hr).mp hNorm
      exact hy (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hB)
    exact ⟨hχ0.eq_of_nhds, (laplacian_eq_of_eventuallyEq hχ0).trans (laplacian_const_real 0 x)⟩
  · intro x
    rw [hχLap, abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm C]
    exact mul_le_mul_of_nonneg_left (hψLap _) (sq_nonneg _)

/-- The whole-wall cutoff identity gives the local Dirichlet-energy
bound for a zero-trace tensor. The amplitude and forcing bounds are
pointwise, and the cutoff has scale-independent constants. -/
theorem exists_boundary_caccioppoli_of_zero_trace
    (hGG : External.LipschitzGaussGreen) {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Point → S0),
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) v U → ContDiffOn ℝ 2 v (closure U) →
      EqOn v (fun _ => 0) (frontier U) →
      ∀ M F : ℝ, 0 ≤ M → 0 ≤ F →
        (∀ x ∈ U, ‖v x‖ ≤ M) → (∀ x ∈ U, ‖laplacian v x‖ ≤ F) →
        ∀ (c : Point) (r : ℝ), 0 < r →
          (∫⁻ x in U ∩ Metric.ball c r, ENNReal.ofReal (gradientNormSq (ClassicalGradient v x))) ≤
            ENNReal.ofReal (C * (r * M ^ 2 + r ^ 3 * M * F)) := by
  obtain ⟨K, hK, hCut⟩ := exists_scaled_laplacian_ball_cutoffs
  let κ := Real.pi * 4 / 3
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  let C := 4 * κ * K + 8 * κ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro v hv hvC hv0 M F hM hF hRange hForce c r hr
  obtain ⟨χ, hχ, hχ01, hχ1, hχOut, hχLap⟩ := hCut c r hr
  let g (y : Point) := (1 / 2 : ℝ) * ‖v y‖ ^ 2
  let G (y : Point) := gradientNormSq (ClassicalGradient v y)
  let q (y : Point) := χ y * G y
  let j (y : Point) := χ y * laplacian g y - g y * laplacian χ y
  let e := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hE : ContDiffOn ℝ 2 (e ∘ v) (closure U) := e.contDiff.comp_contDiffOn hvC
  have hg : ContDiffOn ℝ 2 g (closure U) := by
    simpa only [g, Function.comp_def, e, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map, smul_eq_mul] using
      ((hE.norm_sq ℝ).const_smul (1 / 2 : ℝ))
  have h0 : EqOn g (fun _ => 0) (frontier U) := by
    intro y hy
    change (1 / 2 : ℝ) * ‖v y‖ ^ 2 = _
    rw [hv0 hy, norm_zero, zero_pow two_ne_zero, mul_zero]
  have hD0 : EqOn (fderivWithin ℝ g (closure U)) (fun _ => 0) (frontier U) := by
    intro y hy
    have hy' := frontier_subset_closure hy
    have hd := (((hE y hy').differentiableWithinAt (by norm_num)).hasFDerivWithinAt.norm_sq).const_smul (1 / 2 : ℝ)
    have hu : (e ∘ v) y = 0 := by change e (v y) = 0; rw [hv0 hy, map_zero]
    rw [hu, map_zero, ContinuousLinearMap.zero_comp, nsmul_zero, smul_zero] at hd
    have hd' : HasFDerivWithinAt g (0 : Point →L[ℝ] ℝ) (closure U) y := by
      simpa only [g, Function.comp_def, e, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map, smul_eq_mul] using! hd
    exact hd'.fderivWithin (hU.uniqueDiffOn_closure y hy')
  obtain ⟨hJI, hJZero⟩ := integral_cutoff_laplacian_difference_eq_zero hGG hU hg
    (hχ.of_le (WithTop.coe_le_coe.mpr le_top)) h0 hD0
  have hId (y : Point) (hy : y ∈ U) :
      laplacian g y = G y + frobeniusS0 (laplacian v y) (v y) := by
    have hFrobC : ContDiffOn ℝ 2 (fun y => frobeniusS0 (v y) (v y)) U := by
      have he : ContDiffOn ℝ 2 (e ∘ v) U :=
        e.contDiff.comp_contDiffOn (hv.of_le (WithTop.coe_le_coe.mpr le_top))
      simpa only [Function.comp_def, e, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv, frobeniusCoordinateEquiv_inner] using he.inner ℝ he
    have heq : g = fun y => (1 / 2 : ℝ) • frobeniusS0 (v y) (v y) := by
      funext y
      change (1 / 2 : ℝ) * ‖v y‖ ^ 2 = (1 / 2 : ℝ) * frobeniusS0 (v y) (v y)
      rw [norm_sq_eq_frobeniusS0]
    rw [heq, laplacian_const_smul hU.1.1 hFrobC hy, laplacian_frobeniusS0_self hU.1.1 hv hy]
    change (1 / 2 : ℝ) * _ = gradientNormSq (ClassicalGradient v y) + _
    rw [gradientNormSq_eq_sum_norm_sq]
    change _ = (∑ j, ‖coordDeriv j v y‖ ^ 2) + _
    ring
  let K₁ := (1 / 2 : ℝ) * M ^ 2 * K * r⁻¹ ^ 2 + F * M
  have hK₁ : 0 ≤ K₁ := by dsimp only [K₁]; positivity
  let S := Metric.closedBall c (2 * r)
  let p := S.indicator (fun _ => K₁)
  have hPoint (y : Point) (hy : y ∈ U) : q y ≤ j y + p y := by
    have hj : j y = q y + χ y * frobeniusS0 (laplacian v y) (v y) - g y * laplacian χ y := by
      change χ y * laplacian g y - g y * laplacian χ y = _
      rw [hId y hy]
      change χ y * (G y + frobeniusS0 (laplacian v y) (v y)) - _ = χ y * G y + _ - _
      ring
    rw [hj]
    by_cases hS : y ∈ S
    · have hp : p y = K₁ := indicator_of_mem hS _
      rw [hp]
      have hh : g y * laplacian χ y ≤ (1 / 2 : ℝ) * M ^ 2 * K * r⁻¹ ^ 2 := by
        have hG : 0 ≤ g y := mul_nonneg (by norm_num) (sq_nonneg _)
        have hR : g y ≤ (1 / 2 : ℝ) * M ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hRange y hy) 2) (by norm_num)
        calc
          _ ≤ g y * |laplacian χ y| := mul_le_mul_of_nonneg_left (le_abs_self _) hG
          _ ≤ ((1 / 2 : ℝ) * M ^ 2) * (K * r⁻¹ ^ 2) :=
            mul_le_mul hR (hχLap y) (abs_nonneg _) (by positivity)
          _ = _ := by ring
      have hAbs := abs_real_inner_le_norm (frobeniusCoordinateEquiv (laplacian v y)) (frobeniusCoordinateEquiv (v y))
      rw [frobeniusCoordinateEquiv_inner, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at hAbs
      have hI : |frobeniusS0 (laplacian v y) (v y)| ≤ F * M :=
        hAbs.trans (mul_le_mul (hForce y hy) (hRange y hy) (norm_nonneg _) hF)
      have hI' : -(F * M) ≤ χ y * frobeniusS0 (laplacian v y) (v y) :=
        (by
          have h := mul_le_mul_of_nonpos_right (hχ01 y).2 (neg_nonpos.mpr (mul_nonneg hF hM))
          simpa only [one_mul] using h : -(F * M) ≤ χ y * (-(F * M))).trans
          (mul_le_mul_of_nonneg_left ((neg_le_neg hI).trans (neg_abs_le _)) (hχ01 y).1)
      dsimp only [K₁]
      linarith only [hh, hI']
    · obtain ⟨hχ0, hLap0⟩ := hχOut y hS
      have hp : p y = 0 := indicator_of_notMem hS _
      simp only [hχ0, hLap0, hp, zero_mul, mul_zero, add_zero, sub_zero, le_refl]
  have hv₁ : ContDiffOn ℝ 1 v (closure U) := hvC.of_le (by norm_num)
  have hG' := continuousOn_gradientNormSq (continuousOn_closureGradient_column hU.uniqueDiffOn_closure hv₁)
  have hComp : IsCompact (closure U) := hU.1.2.2.isCompact_closure
  have hGInter : IntegrableOn G U volume := ((hG'.integrableOn_compact hComp).mono_set subset_closure).congr_fun
    (fun y hy => by simp only [G, closureGradient_eq_classicalGradient hU.1.1 hvC hy]) hU.1.1.measurableSet
  have hQInter : IntegrableOn q U volume :=
    (((hχ.continuous.continuousOn.mul hG').integrableOn_compact hComp).mono_set subset_closure).congr_fun
      (fun y hy => by simp only [q, G, Pi.mul_apply, closureGradient_eq_classicalGradient hU.1.1 hvC hy])
      hU.1.1.measurableSet
  haveI : IsFiniteMeasure (volume.restrict U) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt (hComp.measure_lt_top)⟩
  have hpI : IntegrableOn p U volume :=
    (integrable_const K₁).indicator Metric.isClosed_closedBall.measurableSet
  have hB : (∫ y in U, q y) ≤ ∫ y in U, p y := by
    have h := setIntegral_mono_on hQInter (hJI.add hpI) hU.1.1.measurableSet hPoint
    change (∫ y in U, q y) ≤ ∫ y in U, j y + p y at h
    rwa [integral_add hJI hpI, hJZero, zero_add] at h
  let V := U ∩ Metric.ball c r
  have hQV : (∫ y in V, G y) ≤ ∫ y in U, q y := by
    have hInd : IntegrableOn ((Metric.ball c r).indicator G) U volume :=
      hGInter.indicator Metric.isOpen_ball.measurableSet
    have h := setIntegral_mono_on hInd hQInter hU.1.1.measurableSet (fun y hy => by
      have hG : 0 ≤ G y := by
        dsimp only [G]
        rw [gradientNormSq_eq_sum_norm_sq]
        exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      by_cases h : y ∈ Metric.ball c r
      · simp only [indicator_of_mem h, q, hχ1 y h, one_mul, le_rfl]
      · rw [indicator_of_notMem h]
        exact mul_nonneg (hχ01 y).1 hG)
    rwa [setIntegral_indicator Metric.isOpen_ball.measurableSet] at h
  have hVol : (volume S).toReal = κ * (2 * r) ^ 3 := by
    change (volume (Metric.closedBall c (2 * r))).toReal = _
    rw [EuclideanSpace.volume_closedBall_fin_three, ← ENNReal.ofReal_pow (mul_nonneg (by norm_num) hr.le),
      ← ENNReal.ofReal_mul (pow_nonneg (mul_nonneg (by norm_num) hr.le) 3),
      ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hr.le) 3) hκ.le), mul_comm]
  have hPF : (∫ y in U, p y) ≤ κ * (2 * r) ^ 3 * K₁ := by
    change (∫ y in U, S.indicator (fun _ => K₁) y) ≤ _
    rw [setIntegral_indicator Metric.isClosed_closedBall.measurableSet, setIntegral_const, smul_eq_mul]
    have hf : volume S ≠ ⊤ := (isCompact_closedBall c (2 * r)).measure_lt_top.ne
    exact mul_le_mul_of_nonneg_right ((ENNReal.toReal_mono hf (measure_mono inter_subset_right)).trans_eq hVol) hK₁
  have hEnd : κ * (2 * r) ^ 3 * K₁ ≤ C * (r * M ^ 2 + r ^ 3 * M * F) := by
    have hEq : κ * (2 * r) ^ 3 * K₁ = (4 * κ * K) * (r * M ^ 2) + (8 * κ) * (r ^ 3 * M * F) := by
      dsimp only [K₁]
      field_simp [hr.ne']
      ring
    rw [hEq, mul_add]
    have hC₁ : 4 * κ * K ≤ C := by
      dsimp only [C]
      linarith only [mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hκ.le]
    have hC₂ : 8 * κ ≤ C := by
      dsimp only [C]
      linarith only [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hκ.le) hK.le]
    exact add_le_add
      (mul_le_mul_of_nonneg_right hC₁ (mul_nonneg hr.le (sq_nonneg _)))
      (mul_le_mul_of_nonneg_right hC₂ (mul_nonneg (mul_nonneg (pow_nonneg hr.le 3) hM) hF))
  have hGPos : ∀ᵐ y ∂volume.restrict V, 0 ≤ G y := Eventually.of_forall fun y => by
    dsimp only [G]
    rw [gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  change (∫⁻ y in V, ENNReal.ofReal (G y)) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal (hGInter.mono_set inter_subset_left) hGPos]
  exact ENNReal.ofReal_le_ofReal (hQV.trans (hB.trans (hPF.trans hEnd)))

end Thesis

end
