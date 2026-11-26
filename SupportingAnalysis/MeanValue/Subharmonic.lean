module

public import SupportingAnalysis.Calculus.ChainRule
public import SupportingAnalysis.Euclidean
public import HolderToCK.Analysis.Harmonic.SphereMean

/-! The classical subharmonic comparison and mean-value inequality on Euclidean balls. -/

@[expose] public section

open Filter HarmonicMaps InnerProductSpace MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology

set_option autoImplicit false

namespace SupportingAnalysis

private theorem deriv_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f t) (hmax : IsLocalMax f t) :
    deriv (deriv f) t ≤ 0 := by
  by_contra! hpos
  have hcont : ContinuousAt (deriv (deriv f)) t :=
    ((hf.derivWithin (m := 1) (by norm_num)).derivWithin (m := 0) (by norm_num)).continuousAt
  have hStrict : ∀ᶠ s in 𝓝 t, 0 < deriv (deriv f) s := hcont (Ioi_mem_nhds hpos)
  obtain ⟨a, ha, hA⟩ := Metric.mem_nhds_iff.mp
    (show {s : ℝ | 0 < deriv (deriv f) s ∧ f s ≤ f t ∧ ContDiffAt ℝ 2 f s} ∈ 𝓝 t from
      hStrict.and (Eventually.and hmax (hf.eventually (by simp))))
  have hI : Ioo (t - a) (t + a) ⊆ ball t a := by
    intro s hs
    rw [mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hcv : StrictConvexOn ℝ (Ioo (t - a) (t + a)) f := by
    apply strictConvexOn_of_deriv2_pos' (convex_Ioo _ _)
    · exact fun s hs => ((hA (hI hs)).2.2.continuousAt).continuousWithinAt
    · exact fun s hs => (hA (hI hs)).1
  let l := t - a / 2
  let r := t + a / 2
  have hl : l ∈ Ioo (t - a) (t + a) := ⟨by dsimp [l]; linarith, by dsimp [l]; linarith⟩
  have hr : r ∈ Ioo (t - a) (t + a) := ⟨by dsimp [r]; linarith, by dsimp [r]; linarith⟩
  have hlr : l ≠ r := by dsimp [l, r]; linarith
  have hmid := hcv.2 hl hr hlr (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  simp only [smul_eq_mul] at hmid
  rw [show 1 / 2 * l + 1 / 2 * r = t by dsimp [l, r]; ring] at hmid
  linarith only [hmid, (hA (hI hl)).2.1, (hA (hI hr)).2.1]

private theorem laplacian_eq_sum_axis {m : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : E m → V) (x : E m) :
    Laplacian.laplacian f x = ∑ i : Fin m, fderiv ℝ (fderiv ℝ f) x (axis i) (axis i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun _ ℝ)]
  simp only [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, axis]

private theorem laplacian_nonpos_of_isLocalMax {m : ℕ} {f : E m → ℝ} {x : E m}
    (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x) : Laplacian.laplacian f x ≤ 0 := by
  rw [laplacian_eq_sum_axis]
  apply Finset.sum_nonpos
  intro i _
  let bi := axis i
  let v : ℝ →L[ℝ] E m := (ContinuousLinearMap.id ℝ ℝ).smulRight bi
  let A : ℝ → E m := fun t => x + v t
  have hA : ContDiff ℝ ∞ A := contDiff_const.add v.contDiff
  have hA₀ : A 0 = x := by simp [A]
  have hcomp : ContDiffAt ℝ 2 (f ∘ A) 0 := by
    apply ContDiffAt.comp
    · rwa [hA₀]
    · exact (hA.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hMax : IsLocalMax (f ∘ A) 0 := by
    rw [← hA₀] at hmax
    exact hmax.comp_continuous hA.continuous.continuousAt
  have hh := deriv_deriv_nonpos_of_isLocalMax hcomp hMax
  have hv₂ : deriv (deriv A) 0 = 0 := by
    have hFirst : deriv A = fun _ => bi := by
      funext t
      have hd := (v.hasFDerivAt (x := t)).const_add x
      simpa [A, v] using hd.hasDerivAt.deriv
    rw [hFirst, deriv_const]
  have hv₁ : deriv A 0 = bi := by
    simpa [A, v] using ((v.hasFDerivAt (x := (0 : ℝ))).const_add x).hasDerivAt.deriv
  have hf' : ContDiffAt ℝ 2 f (A 0) := by rwa [hA₀]
  rw [deriv_deriv_comp_curve_of_contDiffAt hf'
      ((hA.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt),
    hA₀, hv₁, hv₂, map_zero, add_zero] at hh
  exact hh

private theorem laplacian_norm_sq {m : ℕ} (x : E m) :
    Laplacian.laplacian (fun y : E m => ‖y‖ ^ 2) x = 2 * (m : ℝ) := by
  rw [laplacian_eq_sum_axis, fderiv_norm_sq]
  let L : E m →L[ℝ] E m →L[ℝ] ℝ := innerSL ℝ
  have he : ((2 : ℕ) • (⇑L : E m → E m →L[ℝ] ℝ)) = ⇑((2 : ℝ) • L) := by
    funext y
    apply ContinuousLinearMap.ext
    intro v
    simp [two_nsmul, smul_apply, two_mul]
  change (∑ i : Fin m, fderiv ℝ ((2 : ℕ) • (⇑L : E m → E m →L[ℝ] ℝ))
    x (axis i) (axis i)) = 2 * (m : ℝ)
  rw [he, ContinuousLinearMap.fderiv]
  have hInner (i : Fin m) : L (axis i) (axis i) = 1 := by
    change inner ℝ (axis i) (axis i) = 1
    rw [real_inner_self_eq_norm_sq]
    simp [axis]
  simp [smul_apply, hInner, mul_comm]

/-- Comparison with zero boundary data on a closed ball. -/
theorem le_zero_on_closedBall_of_laplacian_nonneg {m : ℕ} (hm : 0 < m) {R : ℝ} (hR : 0 < R)
    {f : E m → ℝ} (hfc : ContinuousOn f (closedBall 0 R))
    (hfs : ContDiffOn ℝ 2 f (ball 0 R))
    (hBoundary : ∀ x ∈ sphere 0 R, f x ≤ 0)
    (hLap : ∀ x ∈ ball 0 R, 0 ≤ Laplacian.laplacian f x) :
    ∀ x ∈ closedBall 0 R, f x ≤ 0 := by
  intro x hx
  by_contra! hfPos
  let ε := f x / (2 * R ^ 2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  let w : E m → ℝ := fun y => f y + ε * (‖y‖ ^ 2 - R ^ 2)
  have hwC : ContinuousOn w (closedBall 0 R) := by
    refine hfc.add (Continuous.continuousOn ?_)
    fun_prop
  obtain ⟨z, hz, hzMax⟩ := (isCompact_closedBall (0 : E m) R).exists_isMaxOn
    ⟨0, mem_closedBall_self hR.le⟩ hwC
  have hwx : 0 < w x := by
    have he : ε * R ^ 2 = f x / 2 := by dsimp [ε]; field_simp
    dsimp only [w]
    nlinarith only [he, hfPos, mul_nonneg hε.le (sq_nonneg (‖x‖))]
  have hwz : 0 < w z := hwx.trans_le (hzMax hx)
  have hzi : z ∈ ball (0 : E m) R := by
    have hle := mem_closedBall.mp hz
    by_contra h
    have heDist := le_antisymm hle (le_of_not_gt (fun a => h (mem_ball.mpr a)))
    have he : ‖z‖ = R := by simpa only [dist_zero_right] using heDist
    have hzSphere : z ∈ sphere (0 : E m) R := by simpa only [mem_sphere, dist_zero_right] using he
    have hwEq : w z = f z := by simp [w, he]
    exact (not_lt.mpr (hwEq ▸ hBoundary z hzSphere)) hwz
  have hzMax' : IsLocalMax w z :=
    hzMax.isLocalMax (mem_of_superset (isOpen_ball.mem_nhds hzi) ball_subset_closedBall)
  have hfw : ContDiffAt ℝ 2 f z := hfs.contDiffAt (isOpen_ball.mem_nhds hzi)
  have hW : ContDiffAt ℝ 2 w z := hfw.add (ContDiff.contDiffAt (by
    exact contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const)))
  have hNonpos := laplacian_nonpos_of_isLocalMax hW hzMax'
  have hL : Laplacian.laplacian w z = Laplacian.laplacian f z + ε * (2 * (m : ℝ)) := by
    let g : E m → ℝ := fun y => ‖y‖ ^ 2
    let k : E m → ℝ := fun _ => R ^ 2
    have hg : ContDiffAt ℝ 2 g z := (contDiff_norm_sq ℝ).contDiffAt
    have hk : ContDiffAt ℝ 2 k z := contDiffAt_const
    have hCoeff : ContDiffAt ℝ 2 (ε • (g - k)) z := (hg.sub hk).const_smul ε
    have hScale : Laplacian.laplacian (ε • (g - k)) z = ε * Laplacian.laplacian (g - k) z :=
      laplacian_smul (f := g - k) ε (hg.sub hk)
    have hSub : Laplacian.laplacian (g - k) z = Laplacian.laplacian g z - Laplacian.laplacian k z :=
      hg.laplacian_sub hk
    change Laplacian.laplacian (f + ε • (g - k)) z = _
    rw [hfw.laplacian_add hCoeff, hScale, hSub]
    simp only [k, laplacian_const, Pi.zero_apply, sub_zero]
    exact congrArg (fun q => Laplacian.laplacian f z + ε * q) (laplacian_norm_sq z)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  linarith only [hL, hNonpos, hLap z hzi, mul_pos hε (mul_pos (by norm_num : (0 : ℝ) < 2) hmR)]

private theorem laplacian_addCenter {m : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : E m → Y) (a x : E m) :
    Laplacian.laplacian (fun y => f (a + y)) x = Laplacian.laplacian f (a + x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin m) ℝ),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin m) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_comp_add_left]

private theorem subharmonic_sphere_integral_ge {m : ℕ} (hm : 2 ≤ m)
    {f : E m → ℝ} {U : Set (E m)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {a : E m} {r : ℝ} (hr : 0 < r) (hBall : closedBall a r ⊆ U)
    (hLap : ∀ x ∈ ball a r, 0 ≤ Laplacian.laplacian f x) :
    (volume : Measure (E m)).toSphere.real univ * f a ≤
      ∫ θ : sphere (0 : E m) 1, f (a + r • θ.val) ∂(volume : Measure (E m)).toSphere := by
  let V := (fun x : E m => a + x) ⁻¹' U
  let F : E m → ℝ := fun x => f (a + x)
  let ι : ℝ →L[ℝ] E 1 := (ContinuousLinearMap.id ℝ ℝ).smulRight (axis 0)
  let π : E 1 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0
  let g : E m → E 1 := ι ∘ F
  let μ := (volume : Measure (E m)).toSphere
  have hι (x : ℝ) : π (ι x) = x := by simp [π, ι, axis]
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have hVF : closedBall (0 : E m) r ⊆ V := by
    intro x hx
    apply hBall
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hx
  have hF : ContDiffOn ℝ ∞ F V :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hx => hx)
  have hg : ContDiffOn ℝ ∞ g V := ι.contDiff.comp_contDiffOn hF
  let R : PositiveRadius := ⟨r, hr⟩
  obtain ⟨v, _, hvb, w, hwv, hws, hwh, hwf⟩ :=
    poisson_scaledPolar_closedBall_smooth hm R V hV hVF g hg
  let W := π ∘ w
  have hWs : ContDiffOn ℝ ∞ W (closedBall (0 : E m) r) := π.contDiff.comp_contDiffOn hws
  have hwBoundary (x : E m) (hx : x ∈ sphere 0 r) : W x = F x := by
    have hval : w x = g x :=
      (hwv ⟨x, sphere_subset_closedBall hx⟩).trans (hvb ⟨x, hx⟩)
    exact (congrArg π hval).trans (hι _)
  have hDiff : ∀ x ∈ ball (0 : E m) r, 0 ≤ Laplacian.laplacian (F - W) x := by
    intro x hx
    have h₂F : ContDiffAt ℝ 2 F x :=
      (hF.contDiffAt (hV.mem_nhds (hVF (ball_subset_closedBall hx)))).of_le
        (WithTop.coe_le_coe.mpr le_top)
    have h₂w : ContDiffAt ℝ 2 w x :=
      ((hws.mono ball_subset_closedBall).contDiffAt (isOpen_ball.mem_nhds hx)).of_le
        (WithTop.coe_le_coe.mpr le_top)
    have hZero : Laplacian.laplacian W x = 0 := by
      change Laplacian.laplacian (π ∘ w) x = _
      rw [h₂w.laplacian_CLM_comp_left, Function.comp_apply, hwh x hx, map_zero]
    have hAdd : a + x ∈ ball a r := by
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hx
    rw [h₂F.laplacian_sub (π.contDiff.contDiffAt.comp x h₂w), hZero, sub_zero]
    exact (laplacian_addCenter f a x).symm ▸ hLap (a + x) hAdd
  have hLe := le_zero_on_closedBall_of_laplacian_nonneg (by omega : 0 < m) hr
    ((hF.mono hVF).continuousOn.sub hWs.continuousOn)
    (((hF.mono (ball_subset_closedBall.trans hVF)).sub (hWs.mono ball_subset_closedBall)).of_le
      (WithTop.coe_le_coe.mpr le_top))
    (fun x hx => by change F x - W x ≤ 0; rw [hwBoundary x hx, sub_self]) hDiff 0
    (mem_closedBall_self hr.le)
  have hCenter : f a ≤ W 0 := by
    simpa [F, sub_nonpos] using hLe
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hvol : 0 < (volume : Measure (E m)).real (ball 0 1) := by
    apply ENNReal.toReal_pos
    · exact (measure_ball_pos volume (0 : E m) one_pos).ne'
    · exact measure_ball_ne_top
  have hMass : μ.real univ = (m : ℝ) * (volume : Measure (E m)).real (ball 0 1) := by
    rw [show μ = (volume : Measure (E m)).toSphere from rfl, Measure.toSphere_real_apply_univ]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
  have hMassPos : 0 < μ.real univ := hMass.symm ▸ mul_pos (by exact_mod_cast (show 0 < m by omega)) hvol
  have hSNorm (θ : sphere (0 : E m) 1) : ‖(0 : E m) - r • θ.val‖ = r := by
    have hθ : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
    rw [zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg hr.le, hθ, mul_one]
  have hwCenter := (hwf 0 (mem_ball_self hr)).trans
    (poisson_scaledPolar_formula_eq_angular hm R V hV hVF g hg 0 (mem_ball_self hr))
  change w 0 = (((r ^ 2 - ‖(0 : E m)‖ ^ 2) * r ^ (m - 2)) /
    ((m : ℝ) * (volume : Measure (E m)).real (ball 0 1))) •
      (∫ θ : sphere (0 : E m) 1, (‖(0 : E m) - r • θ.val‖ ^ m)⁻¹ • g (r • θ.val) ∂μ)
    at hwCenter
  simp_rw [hSNorm] at hwCenter
  rw [integral_smul, smul_smul] at hwCenter
  have hCoeff : (((r ^ 2 - ‖(0 : E m)‖ ^ 2) * r ^ (m - 2)) /
      ((m : ℝ) * (volume : Measure (E m)).real (ball 0 1))) * (r ^ m)⁻¹ = (μ.real univ)⁻¹ := by
    rw [hMass]
    have hp : r ^ m = r ^ (m - 2) * r ^ 2 := by
      conv_lhs => rw [show m = (m - 2) + 2 by omega, pow_add]
    rw [hp]
    simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
    field_simp [hr.ne', hn, hvol.ne']
  rw [hCoeff] at hwCenter
  have hTraceCont : Continuous (fun θ : sphere (0 : E m) 1 => g (r • θ.val)) := by
    have hφ : Continuous (fun θ : sphere (0 : E m) 1 => r • θ.val) :=
      (continuous_const : Continuous (fun _ : sphere (0 : E m) 1 => r)).smul continuous_subtype_val
    apply continuous_iff_continuousAt.mpr
    intro θ
    have ht : r • θ.val ∈ closedBall (0 : E m) r := by
      have he := hSNorm θ
      rw [zero_sub, norm_neg] at he
      rw [mem_closedBall, dist_zero_right, he]
    exact (hg.contDiffAt (hV.mem_nhds (hVF ht))).continuousAt.comp
      (f := fun θ : sphere (0 : E m) 1 => r • θ.val) hφ.continuousAt
  have hTraceInt := hTraceCont.integrable_of_hasCompactSupport (μ := μ)
    (HasCompactSupport.of_compactSpace _)
  have hScalar : W 0 = (μ.real univ)⁻¹ *
      ∫ θ : sphere (0 : E m) 1, f (a + r • θ.val) ∂μ := by
    change π (w 0) = _
    rw [hwCenter, map_smul, smul_eq_mul, ← π.integral_comp_comm hTraceInt]
    simp only [g, Function.comp_apply, hι, F]
  rw [hScalar] at hCenter
  have hh := mul_le_mul_of_nonneg_left hCenter hMassPos.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hMassPos.ne', one_mul] using hh

/-- A smooth function with nonnegative Laplacian is bounded by its ball average. -/
theorem le_average_ball_of_laplacian_nonneg {m : ℕ} (hm : 2 ≤ m)
    {f : E m → ℝ} {U : Set (E m)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {a : E m} {r : ℝ} (hBall : closedBall a r ⊆ U)
    (hLap : ∀ x ∈ ball a r, 0 ≤ Laplacian.laplacian f x) :
    (volume : Measure (E m)).real (ball a r) * f a ≤ ∫ x in ball a r, f x := by
  have hm₀ : 0 < m := by omega
  have hInt : IntegrableOn f (ball a r) volume :=
    (((hf.mono hBall).continuousOn).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  letI : IsFiniteMeasure ((volume : Measure (E m)).restrict (ball a r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hConst : IntegrableOn (fun _ : E m => f a) (ball a r) volume := integrable_const _
  rw [← show ∫ x in ball a r, f a = (volume : Measure (E m)).real (ball a r) * f a by
    rw [setIntegral_const, smul_eq_mul], integral_ball_eq_polar hm₀ hInt, integral_ball_eq_polar hm₀ hConst]
  apply setIntegral_mono_on (integrableOn_polar_boundary_density hm₀ hConst)
    (integrableOn_polar_boundary_density hm₀ hInt) measurableSet_Ioo
  intro q hq
  rw [integral_const, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (subharmonic_sphere_integral_ge hm hU hf hq.1
    ((closedBall_subset_ball hq.2).trans (ball_subset_closedBall.trans hBall))
    (fun x hx => hLap x (ball_subset_ball hq.2.le hx))) (pow_nonneg hq.1.le _)

/-- The smooth mean-value inequality transported by a linear isometric equivalence. -/
theorem le_average_ball_of_laplacian_nonneg_isometry {m : ℕ} (hm : 2 ≤ m)
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (e : E m ≃ₗᵢ[ℝ] X) {f : X → ℝ} {U : Set X} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : X} {r : ℝ} (hBall : closedBall x r ⊆ U)
    (hΔ : ∀ y ∈ ball x r, 0 ≤ Laplacian.laplacian f y) :
    (volume : Measure X).real (ball x r) * f x ≤ ∫ y in ball x r, f y := by
  let a := e.symm x
  let T := e.toContinuousLinearEquiv.toContinuousLinearMap
  have hT (z : E m) : T z = e z := rfl
  let W := e ⁻¹' U
  let g := f ∘ e
  have ha : e a = x := e.apply_symm_apply x
  have heB : e ⁻¹' ball x r = ball a r := by
    ext y
    rw [mem_preimage, mem_ball, mem_ball, ← ha, e.dist_map]
  have heC : e ⁻¹' closedBall x r = closedBall a r := by
    ext y
    rw [mem_preimage, mem_closedBall, mem_closedBall, ← ha, e.dist_map]
  have hW : IsOpen W := hU.preimage e.continuous
  have hg : ContDiffOn ℝ ∞ g W := hf.comp e.toContinuousLinearMap.contDiff.contDiffOn (fun _ hy => hy)
  have hB : closedBall a r ⊆ W := by
    rw [← heC]
    exact preimage_mono hBall
  have hΔg (y : E m) (hy : y ∈ ball a r) : 0 ≤ Laplacian.laplacian g y := by
    have hy' : e y ∈ ball x r := by
      have h : y ∈ e ⁻¹' ball x r := by rwa [heB]
      exact h
    have hf₂ : ContDiffAt ℝ 2 f (e y) :=
      (hf.contDiffAt (hU.mem_nhds (hBall (ball_subset_closedBall hy')))).of_le
        (WithTop.coe_le_coe.mpr le_top)
    have heq : Laplacian.laplacian g y = Laplacian.laplacian f (e y) := by
      let b := EuclideanSpace.basisFun (Fin m) ℝ
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g b,
        InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (b.map e)]
      apply Finset.sum_congr rfl
      intro i _
      simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        OrthonormalBasis.map_apply]
      have hTf : ContDiffAt ℝ 2 f ((0 : X) + T (y - 0)) := by
        simpa only [zero_add, sub_zero, hT] using hf₂
      simpa only [zero_add, sub_zero, hT, g, Function.comp_def] using
        fderiv_fderiv_comp_affine_of_contDiffAt T (0 : X) (0 : E m) y (b i) (b i) hTf
    rw [heq]
    exact hΔ _ hy'
  have hh := le_average_ball_of_laplacian_nonneg hm hW hg hB hΔg
  have hVol : (volume : Measure (E m)).real (ball a r) = volume.real (ball x r) := by
    rw [← heB, measureReal_def,
      e.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet, measureReal_def]
  have hInt : (∫ y in ball a r, g y) = ∫ y in ball x r, f y := by
    rw [← heB]
    exact e.measurePreserving.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding f _
  rwa [hVol, hInt, show g a = f x from congrArg f ha] at hh

end SupportingAnalysis
