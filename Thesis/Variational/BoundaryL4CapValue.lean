module

public import Thesis.Variational.BoundaryL4ExteriorBall
public import Thesis.Variational.BoundaryL4Poincare
public import Thesis.Variational.BoundaryL4Cutoff
import Thesis.Variational.ExteriorBallGreenPotential
import Thesis.Variational.BoundaryPoissonEstimate

/-! The linear vanishing bound of the true zero-wall solution in a physical cap. -/

public section

noncomputable section

open Filter HolderToCK MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology

namespace Thesis

private theorem exists_cap_norm_integral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Point) {s : ℝ}, 0 < s →
      ∀ {V : Set Point}, V ⊆ ball p s →
      ∀ {E : Type} [NormedAddCommGroup E] {f : Point → E},
        MemLp f 2 (volume.restrict V) →
        (∫ y in V, ‖f y‖) ≤ C * s ^ (3/2 : ℝ) *
          (eLpNorm f 2 (volume.restrict V)).toReal := by
  let C₀ := (eLpNorm (fun _ : Point => (1 : ℝ)) 2 (volume.restrict (ball (0 : Point) 1))).toReal
  let C := C₀ + 1
  have hC₀ : 0 ≤ C₀ := ENNReal.toReal_nonneg
  refine ⟨C, by dsimp only [C]; linarith only [hC₀], ?_⟩
  intro p s hs V hV E _ f hf
  let μ := volume.restrict V
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono hV))
  letI : IsFiniteMeasure (volume.restrict (ball p s)) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hMass : (eLpNorm (fun _ : Point => (1 : ℝ)) 2 (volume.restrict (ball p s))).toReal =
      s ^ (3/2 : ℝ) * C₀ := by
    have hScale := eLpNorm_smul_affine_unitBall_toReal p hs 0 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (fun _ : Point => (1:ℝ))
    have hExp : (0-3*(1/(2:ℝ≥0∞)).toReal : ℝ) = - (3/2) := by norm_num [ENNReal.toReal_div]
    simp only [Real.rpow_zero, one_smul, Function.comp_def, hExp] at hScale
    change C₀ = _ at hScale
    have ht := congrArg (fun x : ℝ => s^(3/2:ℝ) * x) hScale
    rw [← mul_assoc, ← Real.rpow_add hs, add_neg_cancel, Real.rpow_zero, one_mul] at ht
    exact ht.symm
  have hMon := ENNReal.toReal_mono (memLp_const (μ := volume.restrict (ball p s)) (p := 2) (1:ℝ)).eLpNorm_ne_top
    (eLpNorm_mono_measure (fun _ : Point => (1:ℝ)) (Measure.restrict_mono_set volume hV) (p := 2))
  have hConj : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.2 (by norm_num)
  have h := integral_norm_mul_le_realLp_mul hConj
    (show MemLp (fun _ : Point => (1:ℝ)) (ENNReal.ofReal 2) μ from memLp_const _)
    (by simpa only [ENNReal.ofReal_ofNat] using hf)
  simp only [norm_one, one_mul, ENNReal.ofReal_ofNat] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  rw [hMass] at hMon
  refine hMon.trans ((mul_comm _ _).le.trans ?_)
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.rpow_nonneg hs.le _)

/-- The cutoff product rule bounds the Laplacian by the forcing and the two cutoff errors. -/
theorem abs_laplacian_cutoff_mul_le {V : Set Point} (hV : IsOpen V)
    {χ u : Point → ℝ} (hχ : ContDiffOn ℝ 2 χ V) (hu : ContDiffOn ℝ 2 u V)
    {x : Point} (hx : x ∈ V) (hχ₁ : |χ x| ≤ 1) :
    |laplacian (χ*u) x| ≤ |laplacian u x|+
      6*‖fderiv ℝ χ x‖ * ‖fderiv ℝ u x‖ + |laplacian χ x| * |u x| := by
  have hTerm (i : Fin 3) : |coordDeriv i χ x * coordDeriv i u x| ≤
      ‖fderiv ℝ χ x‖ * ‖fderiv ℝ u x‖ := by
    rw [abs_mul]
    apply mul_le_mul _ _ (abs_nonneg _) (norm_nonneg _)
    · rw [← Real.norm_eq_abs, coordDeriv]
      exact ((fderiv ℝ χ x).le_opNorm _).trans_eq (by rw [show ‖axis i‖ = 1 by simp [axis], mul_one])
    · rw [← Real.norm_eq_abs, coordDeriv]
      exact ((fderiv ℝ u x).le_opNorm _).trans_eq (by rw [show ‖axis i‖ = 1 by simp [axis], mul_one])
  have hSum : |∑ i, coordDeriv i χ x * coordDeriv i u x| ≤
      3 * (‖fderiv ℝ χ x‖ * ‖fderiv ℝ u x‖) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => hTerm i).trans_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  rw [laplacian_mul_scalar hV hχ hu hx]
  refine ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have h₁ := mul_le_mul_of_nonneg_right hχ₁ (abs_nonneg (laplacian u x))
  have h₂ := mul_le_mul_of_nonneg_left hSum (by norm_num : (0:ℝ) ≤ 2)
  nlinarith only [h₁,h₂]

private theorem cutoffForce_integral_bound
    {V E : Set Point} (hV : IsOpen V) {p : Point} {s : ℝ} (hs : 0 < s)
    (hVs : V ⊆ ball p s) (hVE : V ⊆ E) {x : Point} (hx : x ∈ closedBall p (s/4))
    {u f χ : Point → ℝ} (hu : ContDiffOn ℝ 2 u V)
    (hEq : ∀ y ∈ V, laplacian u y = f y)
    (hf : MemLp f 4 (volume.restrict E)) (hDu : MemLp (fderiv ℝ u) 2 (volume.restrict E))
    (huV : MemLp u 2 (volume.restrict V))
    {C₀ : ℝ}
    (hP : (eLpNorm u 2 (volume.restrict V)).toReal ≤
      C₀*s*(eLpNorm (fderiv ℝ u) 2 (volume.restrict E)).toReal)
    (hχ : ContDiff ℝ ∞ χ) (hχPos : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχInner : EqOn χ (fun _ => 1) (closedBall p (s/2)))
    {A : ℝ} (hA : 0 ≤ A) (hχDer : ∀ y, ‖fderiv ℝ χ y‖ ≤ A/s ∧ |laplacian χ y| ≤ A / s^2)
    (hForceLp : MemLp (fun y => |laplacian (χ*u) y|) 4 (volume.restrict V))
    {L : ℝ} (hL : 0 ≤ L)
    (hKernel : ∀ x ∈ closedBall p s,
      MemLp (fun y => poissonInversePower 2 (x-y)) poissonL4Conjugate (volume.restrict (ball p s)) ∧
      (eLpNorm (fun y => poissonInversePower 2 (x-y)) poissonL4Conjugate (volume.restrict (ball p s))).toReal ≤
        L * s ^ (1/4 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hL1 : ∀ {E : Type} [NormedAddCommGroup E] {g : Point → E}, MemLp g 2 (volume.restrict V) →
      (∫ y in V, ‖g y‖) ≤ C*s^(3/2:ℝ)*(eLpNorm g 2 (volume.restrict V)).toReal) :
    let F := (eLpNorm f 4 (volume.restrict E)).toReal
    let G := (eLpNorm (fderiv ℝ u) 2 (volume.restrict E)).toReal
    (∫ y in V, poissonInversePower 2 (x-y) * |laplacian (χ*u) y|) ≤
      L*s^(1/4:ℝ)*F + (16*A*C*(6+C₀))*s^(-3/2:ℝ)*G := by
  intro F G
  let g (y : Point) := |laplacian (χ*u) y|
  let k (y : Point) := poissonInversePower 2 (x-y)
  let μ := (volume : Measure Point).restrict V
  let B := ((s/4)⁻¹)^2
  have hB : 0 ≤ B := sq_nonneg _
  have hKx := hKernel x (closedBall_subset_closedBall (by linarith only [hs]) hx)
  have hk : MemLp k poissonL4Conjugate μ := hKx.1.mono_measure (Measure.restrict_mono_set volume hVs)
  have hFv : MemLp f 4 μ := hf.mono_measure (Measure.restrict_mono_set volume hVE)
  have hDv : MemLp (fderiv ℝ u) 2 μ := hDu.mono_measure (Measure.restrict_mono_set volume hVE)
  have hDuL : (eLpNorm (fderiv ℝ u) 2 μ).toReal ≤ G :=
    ENNReal.toReal_mono hDu.eLpNorm_ne_top (eLpNorm_mono_measure _
      (Measure.restrict_mono_set volume hVE))
  have hFvL : (eLpNorm f 4 μ).toReal ≤ F :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _
      (Measure.restrict_mono_set volume hVE))
  have hKL : (eLpNorm k poissonL4Conjugate μ).toReal ≤ L * s^(1/4:ℝ) :=
    (ENNReal.toReal_mono hKx.1.eLpNorm_ne_top (eLpNorm_mono_measure _
      (Measure.restrict_mono_set volume hVs))).trans hKx.2
  have hForceI : Integrable (fun y => k y*g y) μ := integrable_poissonL4_smul hForceLp hk
  have hfI : Integrable (fun y => k y*‖f y‖) μ := integrable_poissonL4_smul hFv.norm hk
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono hVs))
  have hDuI : Integrable (fun y => ‖fderiv ℝ u y‖) μ := hDv.norm.integrable (by norm_num)
  have huI : Integrable (fun y => ‖u y‖) μ := huV.norm.integrable (by norm_num)
  let d := 6*A/s
  let b := A/s^2
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have h₁ : ∫ y, k y*‖f y‖ ∂μ ≤ L*s^(1/4:ℝ)*F := by
    have h := integral_poissonL4_product_le hFv hk
      (Eventually.of_forall fun _ => poissonInversePower_nonneg _ _)
    exact h.trans (mul_le_mul hKL hFvL ENNReal.toReal_nonneg
      (mul_nonneg hL (Real.rpow_nonneg hs.le _)))
  have h₂ : ∫ y, ‖fderiv ℝ u y‖ ∂μ ≤ C*s^(3/2:ℝ)*G :=
    (hL1 hDv).trans (mul_le_mul_of_nonneg_left hDuL (by positivity))
  have h₃ : ∫ y, ‖u y‖ ∂μ ≤ C*s^(3/2:ℝ)*(C₀*s*G) :=
    (hL1 huV).trans (mul_le_mul_of_nonneg_left hP (by positivity))
  have hDom (y : Point) (hy : y ∈ V) :
      k y*g y ≤ k y*‖f y‖ + B * (d*‖fderiv ℝ u y‖+ b*‖u y‖) := by
    by_cases hyI : y ∈ ball p (s/2)
    · obtain ⟨hD,hL⟩ := boundaryL4_cutoff_derivatives_zero hχInner hyI
      have he : laplacian (χ*u) y = f y := by
        rw [laplacian_mul_scalar hV (hχ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn hu hy,
          hχInner (ball_subset_closedBall hyI), hL, hEq y hy]
        have hχd (j : Fin 3) : coordDeriv j χ y = 0 := by
          unfold coordDeriv
          rw [hD, zero_apply]
        simp only [hχd, one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      change k y*|laplacian (χ*u) y| ≤ _
      rw [he, Real.norm_eq_abs]
      exact le_add_of_nonneg_right (by positivity)
    · have hyD : s/2 ≤ dist y p := le_of_not_gt (fun h => hyI (mem_ball.2 h))
      have hxD : dist x p ≤ s/4 := mem_closedBall.1 hx
      have hXY : s/4 ≤ ‖x-y‖ := by
        rw [← dist_eq_norm]
        linarith only [dist_triangle y x p, dist_comm y x, hyD,hxD]
      have hkB : k y ≤ B := by
        change poissonInversePower 2 (x-y) ≤ ((s/4)⁻¹)^2
        rw [poissonInversePower_two]
        exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
          ((inv_le_inv₀ ((by positivity : 0 < s/4).trans_le hXY) (by positivity)).2 hXY) 2
      have hχB : |χ y| ≤ 1 := by rw [abs_of_nonneg (hχPos y).1]; exact (hχPos y).2
      have hh := abs_laplacian_cutoff_mul_le hV
        (hχ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn hu hy hχB
      rw [hEq y hy, ← Real.norm_eq_abs (f y), ← Real.norm_eq_abs (u y)] at hh
      have hGrad := mul_le_mul_of_nonneg_right ((hχDer y).1) (norm_nonneg (fderiv ℝ u y))
      have hVal := mul_le_mul_of_nonneg_right ((hχDer y).2) (norm_nonneg (u y))
      have hgD : g y ≤ ‖f y‖+(d*‖fderiv ℝ u y‖+b*‖u y‖) := by
        dsimp only [g,d,b]
        simp only [div_eq_mul_inv] at hGrad hVal ⊢
        nlinarith only [hh,hGrad,hVal]
      have hk₀ : 0 ≤ k y := poissonInversePower_nonneg 2 (x-y)
      have h0 := mul_le_mul_of_nonneg_left hgD hk₀
      rw [mul_add] at h0
      exact h0.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hkB (by positivity)))
  have hQ : (∫ y, k y*g y ∂μ) ≤ ∫ y, k y*‖f y‖ + B*(d*‖fderiv ℝ u y‖ + b*‖u y‖) ∂μ :=
    integral_mono_ae hForceI (hfI.add (((hDuI.const_mul d).add (huI.const_mul b)).const_mul B))
      ((ae_restrict_mem hV.measurableSet).mono (fun y hy => hDom y hy))
  have hRemI : Integrable (fun y => B*(d*‖fderiv ℝ u y‖+b*‖u y‖)) μ :=
    ((hDuI.const_mul d).add (huI.const_mul b)).const_mul B
  rw [integral_add hfI hRemI, integral_const_mul,
    integral_add (hDuI.const_mul d) (huI.const_mul b), integral_const_mul, integral_const_mul] at hQ
  have hBound := hQ.trans (add_le_add h₁ (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left h₂ hd) (mul_le_mul_of_nonneg_left h₃ hb)) hB))
  have hPow : B*((s⁻¹)*(s^(3/2:ℝ))) = 16*s^(-3/2:ℝ) := by
    have he : B = 16*s^(-2:ℝ) := by
      unfold B
      rw [Real.rpow_neg hs.le,Real.rpow_two]
      field_simp
      ring
    have hi : s⁻¹*s^(3/2:ℝ) = s^(1/2:ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hs]
      congr 1
      norm_num
    rw [he,hi,mul_assoc,← Real.rpow_add hs]
    congr 2
    norm_num
  refine hBound.trans_eq ?_
  have hd' : d=6*A*s⁻¹ := by unfold d; ring
  have hb' : b*C₀*s=A*C₀*s⁻¹ := by unfold b; field_simp
  rw [hd']
  calc
    _ = L*s^(1/4:ℝ)*F + (B*(s⁻¹*s^(3/2:ℝ))) * (A*C*(6+C₀))*G := by
      have he : b*(C*s^(3/2:ℝ)*(C₀*s*G)) = (b*C₀*s)*C*s^(3/2:ℝ)*G := by ring
      rw [he,hb']
      ring
    _ = _ := by rw [hPow]; ring

private theorem cutoffForce_memLp_four
    {U : Set Point} (hU : IsSmoothDomain U) {p : Point} {s A : ℝ} (hs : 0 < s) (hA : 1 < A)
    {u f χ : Point → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ₁ : ∀ x, |χ x| ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) (hχDer : ∀ x, ‖fderiv ℝ χ x‖ ≤ C/s ∧ |laplacian χ x| ≤ C/s^2)
    (hu : ContDiffOn ℝ 2 u (closure U ∩ ball p (A*s)))
    (hEq : ∀ x ∈ U ∩ ball p (A*s), laplacian u x = f x)
    (hf : MemLp f 4 (volume.restrict (U ∩ ball p (A*s)))) :
    MemLp (fun x => |laplacian (χ*u) x|) 4 (volume.restrict (U∩ball p s)) := by
  let V := U∩ball p s
  let E := U∩ball p (A*s)
  let K := closure U ∩ ball p (A*s)
  let B := closure U ∩ closedBall p s
  have hV : IsOpen V := hU.1.1.inter isOpen_ball
  have hVE : V ⊆ E := inter_subset_inter_right _ (ball_subset_ball (le_mul_of_one_le_left hs.le hA.le))
  have hVB : V ⊆ B := inter_subset_inter subset_closure ball_subset_closedBall
  have hBK : B ⊆ K := inter_subset_inter_right _ (closedBall_subset_ball (lt_mul_of_one_lt_left hs hA))
  have hK : UniqueDiffOn ℝ K := by
    intro x hx
    exact (uniqueDiffWithinAt_inter (isOpen_ball.mem_nhds hx.2)).2 (hU.uniqueDiffOn_closure x hx.1)
  have hB : IsCompact B := (isCompact_closedBall p s).inter_left isClosed_closure
  obtain ⟨M,hM⟩ := hB.exists_bound_of_continuousOn (hu.continuousOn.mono hBK)
  have hDerC : ContinuousOn (fderivWithin ℝ u K) B := (hu.continuousOn_fderivWithin hK (by norm_num)).mono hBK
  obtain ⟨L,hL⟩ := hB.exists_bound_of_continuousOn hDerC
  let D := 6*C/s*max L 0 + C/s^2*max M 0
  have hDv (x : Point) (hx : x ∈ V) : ‖fderiv ℝ u x‖ ≤ max L 0 := by
    have hN : K ∈ 𝓝 x := mem_of_superset (hV.mem_nhds hx) (hVB.trans hBK)
    have h := hL x (hVB hx)
    rw [fderivWithin_of_mem_nhds hN] at h
    exact h.trans (le_max_left _ _)
  have hU₀ : ContDiffOn ℝ 2 u V := hu.mono (hVB.trans hBK)
  let μ := volume.restrict V
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono (show V⊆ball p s from inter_subset_right)))
  have hFv := hf.mono_measure (Measure.restrict_mono_set volume hVE)
  have hBnd : MemLp (fun x => ‖f x‖ + D) 4 μ := hFv.norm.add (memLp_const _)
  have hLC : ContinuousOn (fun x => |laplacian (χ*u) x|) V :=
    (Thesis.continuousOn_laplacian_of_contDiffOn_two hV
      ((hχ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn.mul hU₀)).abs
  apply hBnd.mono' (hLC.aestronglyMeasurable hV.measurableSet)
  filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
  rw [Real.norm_of_nonneg (abs_nonneg _)]
  have h := abs_laplacian_cutoff_mul_le hV (hχ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn hU₀ hx (hχ₁ x)
  rw [hEq x (hVE hx), ← Real.norm_eq_abs (f x), ← Real.norm_eq_abs (u x)] at h
  have hL' := mul_le_mul ((hχDer x).1) (hDv x hx) (norm_nonneg _) (by positivity : 0 ≤ C/s)
  have hM' := mul_le_mul ((hχDer x).2) ((hM x (hVB hx)).trans (le_max_left M 0))
    (norm_nonneg _) (by positivity : 0 ≤ C/s^2)
  dsimp only [D]
  simp only [div_eq_mul_inv] at hL' hM' ⊢
  nlinarith only [h,hL',hM']

/-- The zero wall forces the actual classical value to vanish linearly on
the inner cap, with the same scaled (L^2) gradient and (L^4) force norms. -/
theorem IsSmoothDomain.exists_localBoundaryL4_value_bound {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ R A C : ℝ, 0 < R ∧ 1 < A ∧ 0 < C ∧
      ∀ p ∈ frontier U, ∀ s ∈ Ioo 0 R, ∀ (u f : Point → ℝ),
        let E := U∩ball p (A*s)
        let K := closure U∩ball p (A*s)
        ContDiffOn ℝ 2 u K →
        EqOn u (fun _ => 0) (frontier U∩ball p (A*s)) →
        (∀ x ∈ E, laplacian u x = f x) →
        MemLp (fderiv ℝ u) 2 (volume.restrict E) →
        MemLp f 4 (volume.restrict E) →
        ∀ x ∈ closure U∩ball p (s/4), |u x| ≤ C*dist x p*
          (s ^ (-3/2 : ℝ)*(eLpNorm (fderiv ℝ u) 2 (volume.restrict E)).toReal +
            s ^ (1/4 : ℝ)*(eLpNorm f 4 (volume.restrict E)).toReal) := by
  obtain ⟨R₁,A,C₀,hR₁,hA,hC₀,hP⟩ := hU.exists_local_zero_wall_poincare
  obtain ⟨R₂,hR₂,hExtBall⟩ := hU.exists_uniform_exterior_tangent_balls
  obtain ⟨M,hM,hCut⟩ := exists_boundaryL4_cutoff
  obtain ⟨L,hL,hKernel⟩ := exists_poissonInversePower_conjugate_bound 2 (by norm_num)
  obtain ⟨J,hJ,hMass⟩ := exists_cap_norm_integral_bound
  let R := min R₁ R₂
  let B := 16*M*J*(6+C₀)
  let κ := (euclideanSphereArea 3)⁻¹
  let C := 1+10*κ*(L+B)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hκ : 0 ≤ κ := inv_nonneg.mpr (euclideanSphereArea_pos (by decide)).le
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨R,A,C,lt_min hR₁ hR₂,hA,hC,?_⟩
  intro p hp s hs u f E K hu hTrace hEq hDu hf
  have hs₀ : 0 < s := hs.1
  let V := U∩ball p s
  have hV : IsOpen V := hU.1.1.inter isOpen_ball
  have hVs : V ⊆ ball p s := inter_subset_right
  have hVE : V ⊆ E := inter_subset_inter_right _ (ball_subset_ball (le_mul_of_one_le_left hs.1.le hA.le))
  have hVK : V ⊆ K := fun _ hy => ⟨subset_closure (hVE hy).1,(hVE hy).2⟩
  have hVCK : closure V ⊆ K := fun x hx => ⟨closure_mono inter_subset_left hx,
    closedBall_subset_ball (lt_mul_of_one_lt_left hs.1 hA)
      (closure_minimal (hVs.trans ball_subset_closedBall) isClosed_closedBall hx)⟩
  obtain ⟨huLp,hPoin⟩ := hP p hp s ⟨hs.1,hs.2.trans_le (min_le_left _ _)⟩ u
    (hu.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) hTrace hDu
  obtain ⟨χ,hχ,hχPos,hχInner,hχSupp,hχDer⟩ := hCut p hs.1
  have hχA (x : Point) : |χ x| ≤ 1 := by rw [abs_of_nonneg (hχPos x).1]; exact (hχPos x).2
  let w := χ*u
  let g (x : Point) := |laplacian w x|
  have hw : ContDiffOn ℝ 2 w V :=
    (hχ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn.mul (hu.mono hVK)
  have hwC : ContinuousOn w (closure V) := hχ.continuous.continuousOn.mul (hu.continuousOn.mono hVCK)
  have hwZero (x : Point) (hx : x ∈ frontier V) : w x = 0 := by
    have hxC := frontier_subset_closure hx
    by_cases hxU : x ∈ U
    · have hxN : x ∉ ball p s := fun h =>
        (disjoint_left.1 ((disjoint_frontier_iff_isOpen).2 hV)) hx ⟨hxU,h⟩
      have hxTS : x ∉ tsupport χ := fun h =>
        hxN ((closedBall_subset_ball (by linarith only [hs.1])) (hχSupp h))
      change χ x*u x = 0
      rw [image_eq_zero_of_notMem_tsupport hxTS,zero_mul]
    · have hxU' : x ∈ frontier U := by
        rw [frontier,hU.1.1.interior_eq]
        exact ⟨(hVCK hxC).1,hxU⟩
      have h0 := hTrace ⟨hxU',(hVCK hxC).2⟩
      change χ x * u x = 0
      rw [h0,mul_zero]
  have hgLp : MemLp g 4 (volume.restrict V) :=
    cutoffForce_memLp_four hU hs.1 hA hχ hχA hM.le hχDer hu hEq hf
  obtain ⟨ν,hν,hνBall⟩ := hExtBall p hp
  let ρ := s/8
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  let a := p+ρ • ν
  have hBall := hνBall ρ ⟨hρ,(by dsimp only [ρ]; linarith only [hs.1,hs.2.trans_le (min_le_right R₁ R₂)] : ρ < R₂)⟩
  have hExt (y : Point) (hy : y ∈ V) : ρ < ‖y-a‖ := hBall.2 y hy.1
  have hPa : ‖p-a‖ = ρ := by
    have hE : p-a = -(ρ • ν) := by dsimp only [a]; abel
    rw [hE,norm_neg,norm_smul,Real.norm_of_nonneg hρ.le,hν,mul_one]
  have hRatio (y : Point) (hy : y ∈ V) : ‖y-a‖/ρ ≤ 9 := by
    rw [← dist_eq_norm]
    apply (div_le_iff₀ hρ).2
    have hD := dist_triangle y p a
    rw [dist_eq_norm p a,hPa] at hD
    dsimp only [ρ] at *
    linarith only [hD,mem_ball.1 hy.2]
  let P := exteriorBallGreenPotential a ρ V g
  have hBound := abs_le_exteriorBallGreenPotential_of_zero_wall hρ hs.1 hV hVs hExt
    hgLp (fun y _ => abs_nonneg (laplacian w y)) hwC hw hwZero (fun _ _ => le_rfl)
  have hP0 : P p = 0 := exteriorBallGreenPotential_eq_zero_on_sphere hρ hPa hV.measurableSet hExt g
  let Φ := (eLpNorm f 4 (volume.restrict E)).toReal
  let G := (eLpNorm (fderiv ℝ u) 2 (volume.restrict E)).toReal
  let D := s^(-3/2:ℝ)*G+s^(1/4:ℝ)*Φ
  have hD : 0 ≤ D := by dsimp only [D,Φ,G]; positivity
  have hI (x : Point) (hx : x ∈ closedBall p (s/4)) :
      (∫ y in V, poissonInversePower 2 (x-y)*g y) ≤ (L+B)*D := by
    have h' : ∀ x ∈ closedBall p s,
        MemLp (fun y => poissonInversePower 2 (x-y)) poissonL4Conjugate (volume.restrict (ball p s)) ∧
         (eLpNorm (fun y => poissonInversePower 2 (x-y)) poissonL4Conjugate (volume.restrict (ball p s))).toReal ≤
          L*s^(1/4:ℝ) := by
      intro z hz
      simpa only [show (9/4-2:ℝ)=1/4 by norm_num] using hKernel p z s hs.1 hz
    have h := cutoffForce_integral_bound hV hs.1 hVs hVE hx (hu.mono hVK) (fun x hx => hEq x (hVE hx))
      hf hDu huLp hPoin hχ hχPos hχInner hM.le hχDer hgLp hL h' hJ.le
      (fun {_} _ {_} h => hMass p hs.1 hVs h)
    refine h.trans ?_
    dsimp only [D,B]
    have h1 : 0 ≤ L * s^(-3/2:ℝ)*G := by dsimp only [G]; positivity
    have h2 : 0 ≤ (16*M*J*(6+C₀))*s^(1/4:ℝ)*Φ := by dsimp only [Φ]; positivity
    nlinarith only [h1,h2]
  intro x hx
  have hxV : x ∈ closure V := isOpen_ball.closure_inter ⟨hx.1,
    ball_subset_ball (by linarith only [hs.1]) hx.2⟩
  have hxB := ball_subset_closedBall hx.2
  have hpB : p ∈ closedBall p (s/4) := mem_closedBall_self (by positivity)
  have hχx : χ x = 1 := hχInner (closedBall_subset_closedBall (by linarith only [hs.1]) hxB)
  have hDif := exteriorBallGreenPotential_abs_sub_le hρ hs.1 (hBall.1 x hx.1) hPa.ge
    (closedBall_subset_closedBall (by linarith only [hs.1]) hxB) (mem_closedBall_self hs.1.le)
    hV.measurableSet hVs hExt hgLp (fun y _ => abs_nonneg _) hRatio
  change |P x - P p| ≤ _ at hDif
  rw [hP0,sub_zero] at hDif
  have hLHS : |u x| ≤ P x := by
    have h := hBound x hxV
    change |χ x * u x| ≤ P x at h
    rwa [hχx,one_mul] at h
  have hRhs := hDif.trans (mul_le_mul_of_nonneg_left (add_le_add (hI x hxB) (hI p hpB))
    (by positivity : 0 ≤ κ*((1+9)*dist x p/2)))
  refine (hLHS.trans ((le_abs_self _).trans hRhs)).trans ?_
  change κ * ((1+9) * dist x p / 2) * ((L+B)*D+(L+B)*D) ≤ C * dist x p * D
  calc
    _ = (10*κ*(L+B)) * (dist x p * D) := by ring
    _ ≤ C * (dist x p * D) := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left zero_le_one) (mul_nonneg dist_nonneg hD)
    _ = _ := by ring

end Thesis

end
