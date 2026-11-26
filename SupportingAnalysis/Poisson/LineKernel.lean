module

public import SupportingAnalysis.Calculus.RealLine
public import SupportingAnalysis.Basics
public import HolderToCK.Analysis.Poisson.FundamentalWeakGradient

/-! The one-dimensional Newtonian kernel and its signed distributional identities. -/

@[expose] public section

open MeasureTheory Set Metric Filter InnerProductSpace
open scoped BigOperators ContDiff Topology

set_option autoImplicit false

namespace SupportingAnalysis

/-- The signed one-half jump representing the derivative of the absolute-value kernel. -/
noncomputable def lineNewtonianDerivative (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 / 2 else -(1 / 2)

private theorem lineNewtonianDerivative_measurable : Measurable lineNewtonianDerivative := by
  change Measurable ((Ici (0 : ℝ)).piecewise (fun _ : ℝ => (1 / 2 : ℝ)) (fun _ => -(1 / 2)))
  exact measurable_const.piecewise measurableSet_Ici measurable_const

private theorem integrable_lineNewtonianDerivative_mul {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (fun x => lineNewtonianDerivative x * f x) := by
  refine hf.norm.mono' (lineNewtonianDerivative_measurable.aestronglyMeasurable.mul
    hf.aestronglyMeasurable) ?_
  filter_upwards [] with x
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  by_cases hx : 0 ≤ x <;> norm_num [lineNewtonianDerivative, hx]

private theorem compactTest_openInterval {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ tsupport f ⊆ Ioo (-R) R := by
  obtain ⟨R, hR, hsub⟩ := hf.isCompact.isBounded.subset_ball_lt 0 0
  refine ⟨R, hR, fun x hx => ?_⟩
  change -R < x ∧ x < R
  simpa only [mem_ball, Real.dist_eq, sub_zero, abs_lt] using hsub hx

private theorem integral_split_compact_at_zero (f : ℝ → ℝ) (hf : Integrable f)
    {R : ℝ} (_hR : 0 < R) (hsub : Function.support f ⊆ Ioc (-R) R) :
    (∫ x, f x) = (∫ x in -R..0, f x) + ∫ x in 0..R, f x := by
  calc
    _ = ∫ x in -R..R, f x := (intervalIntegral.integral_eq_integral_of_support_subset hsub).symm
    _ = _ := (intervalIntegral.integral_add_adjacent_intervals
      (a := -R) (b := 0) (c := R) hf.intervalIntegrable hf.intervalIntegrable).symm

private theorem support_product_in_interval (f : ℝ → ℝ) {g : ℝ → ℝ} {R : ℝ}
    (hg : tsupport g ⊆ Ioo (-R) R) : Function.support (fun x => f x * g x) ⊆ Ioc (-R) R :=
  (Function.support_mul_subset_right _ _).trans ((subset_tsupport _).trans
    (hg.trans Ioo_subset_Ioc_self))

private theorem lineNewtonianDerivative_integral_negative (f : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x in -R..0, lineNewtonianDerivative x * f x) =
      -(1 / 2 : ℝ) * ∫ x in -R..0, f x := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le (neg_nonpos.mpr hR.le)
  intro x hx
  change lineNewtonianDerivative x * f x = -(1 / 2) * f x
  rw [lineNewtonianDerivative, if_neg hx.2.not_ge]

private theorem lineNewtonianDerivative_integral_positive (f : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x in 0..R, lineNewtonianDerivative x * f x) =
      (1 / 2 : ℝ) * ∫ x in 0..R, f x := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le hR.le
  intro x hx
  change lineNewtonianDerivative x * f x = (1 / 2) * f x
  rw [lineNewtonianDerivative, if_pos hx.1.le]

private theorem realNewtonian_testDerivative (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) :
    (∫ x, |x| / 2 * deriv φ x) = -∫ x, lineNewtonianDerivative x * φ x := by
  obtain ⟨R, hR, hsub⟩ := compactTest_openInterval hφc
  have hDeriv := hφ.continuous_deriv_one
  have h₁ : Integrable (fun x => |x| / 2 * deriv φ x) :=
    ((continuous_abs.div_const (2 : ℝ)).mul hDeriv).integrable_of_hasCompactSupport hφc.deriv.mul_left
  have h₂ := integrable_lineNewtonianDerivative_mul
    (hφ.continuous.integrable_of_hasCompactSupport hφc)
  have hsubD : tsupport (deriv φ) ⊆ Ioo (-R) R := tsupport_deriv_subset.trans hsub
  have hneg : φ (-R) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (hsub h).1.false)
  have hpos : φ R = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (hsub h).2.false)
  have hLeft : (∫ x in -R..0, x * deriv φ x) = -∫ x in -R..0, φ x := by
    simpa only [id, hneg, mul_zero, zero_mul, sub_zero, zero_sub, one_mul] using
      (intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -R) (b := 0)
        (u := id) (u' := fun _ => 1) (v := φ) (v' := deriv φ)
        (fun x _ => hasDerivAt_id x) (fun x _ => (hφ.differentiable one_ne_zero x).hasDerivAt)
        (continuous_const.intervalIntegrable (-R) 0) (hDeriv.intervalIntegrable (-R) 0))
  have hRight : (∫ x in 0..R, x * deriv φ x) = -∫ x in 0..R, φ x := by
    simpa only [id, hpos, mul_zero, zero_mul, sub_zero, zero_sub, one_mul] using
      (intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := R)
        (u := id) (u' := fun _ => 1) (v := φ) (v' := deriv φ)
        (fun x _ => hasDerivAt_id x) (fun x _ => (hφ.differentiable one_ne_zero x).hasDerivAt)
        (continuous_const.intervalIntegrable 0 R) (hDeriv.intervalIntegrable 0 R))
  have hAbsLeft : (∫ x in -R..0, |x| / 2 * deriv φ x) =
      -(1 / 2 : ℝ) * ∫ x in -R..0, x * deriv φ x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (neg_nonpos.mpr hR.le)
    intro x hx
    change |x| / 2 * deriv φ x = -(1 / 2) * (x * deriv φ x)
    rw [abs_of_neg hx.2]
    ring
  have hAbsRight : (∫ x in 0..R, |x| / 2 * deriv φ x) =
      (1 / 2 : ℝ) * ∫ x in 0..R, x * deriv φ x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hR.le
    intro x hx
    change |x| / 2 * deriv φ x = (1 / 2) * (x * deriv φ x)
    rw [abs_of_pos hx.1]
    ring
  rw [integral_split_compact_at_zero _ h₁ hR (support_product_in_interval _ hsubD),
    integral_split_compact_at_zero _ h₂ hR (support_product_in_interval _ hsub),
    hAbsLeft, hAbsRight, hLeft, hRight, lineNewtonianDerivative_integral_negative _ hR,
    lineNewtonianDerivative_integral_positive _ hR]
  ring

private theorem realNewtonian_distributionPairing (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    (∫ x, |x| / 2 * deriv (deriv φ) x) = φ 0 := by
  have hφOne : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hD : ContDiff ℝ 1 (deriv φ) := (contDiff_succ_iff_deriv.mp hφ).2.2
  rw [realNewtonian_testDerivative (deriv φ) hD hφc.deriv]
  obtain ⟨R, hR, hsub⟩ := compactTest_openInterval hφc
  have hsubD : tsupport (deriv φ) ⊆ Ioo (-R) R := tsupport_deriv_subset.trans hsub
  have hneg : φ (-R) = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hsub h).1.false)
  have hpos : φ R = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hsub h).2.false)
  have hd := integrable_lineNewtonianDerivative_mul
    (hφOne.continuous_deriv_one.integrable_of_hasCompactSupport hφc.deriv)
  have hFTC (a b : ℝ) : (∫ x in a..b, deriv φ x) = φ b - φ a :=
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hφOne.differentiable one_ne_zero x)
      (hφOne.continuous_deriv_one.intervalIntegrable a b)
  rw [integral_split_compact_at_zero _ hd hR (support_product_in_interval _ hsubD),
    lineNewtonianDerivative_integral_negative _ hR, lineNewtonianDerivative_integral_positive _ hR,
    hFTC, hFTC, hneg, hpos]
  ring


/-- The canonical positively normalized fundamental kernel in one dimension. -/
noncomputable def newtonianOne (x : E 1) : ℝ := |realLineEuclideanIso x| / 2

/-- A representative of the Euclidean weak gradient of the one-dimensional kernel. -/
noncomputable def newtonianOneGradient (x : E 1) : E 1 :=
  realLineEuclideanIso.symm (lineNewtonianDerivative (realLineEuclideanIso x))

theorem newtonianOne_eq_norm (x : E 1) : newtonianOne x = ‖x‖ / 2 := by
  rw [newtonianOne, realLineEuclideanIso_norm]

private theorem newtonianOneGradient_component (x : E 1) (i : Fin 1) :
    newtonianOneGradient x i = lineNewtonianDerivative (realLineEuclideanIso x) := by
  rw [Fin.fin_one_eq_zero i]
  change realLineEuclideanIso (realLineEuclideanIso.symm _) = _
  exact realLineEuclideanIso.apply_symm_apply _

theorem newtonianOne_locallyIntegrable : LocallyIntegrable newtonianOne volume := by
  exact ((continuous_abs.comp realLineEuclideanIso.continuous).div_const _).locallyIntegrable

theorem newtonianOneGradient_locallyIntegrable : LocallyIntegrable newtonianOneGradient volume := by
  have hM : Measurable newtonianOneGradient :=
    realLineEuclideanIso.symm.continuous.measurable.comp
      (lineNewtonianDerivative_measurable.comp realLineEuclideanIso.continuous.measurable)
  rw [locallyIntegrable_iff]
  intro K hK
  letI : IsFiniteMeasure ((volume : Measure (E 1)).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  apply (integrable_const (1 / 2 : ℝ)).mono' hM.aestronglyMeasurable
  filter_upwards [] with x
  change ‖realLineEuclideanIso.symm (lineNewtonianDerivative (realLineEuclideanIso x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  by_cases hx : 0 ≤ realLineEuclideanIso x <;> norm_num [lineNewtonianDerivative, hx]

theorem newtonianOne_classicalGradient {x : E 1} (hx : x ≠ 0) (i : Fin 1) :
    fderiv ℝ newtonianOne x (axis i) = newtonianOneGradient x i := by
  have hx' : realLineEuclideanIso x ≠ 0 := by
    intro h
    apply hx
    exact realLineEuclideanIso.injective (h.trans realLineEuclideanIso.map_zero.symm)
  have hd : HasDerivAt (fun y : ℝ => |y| / 2) (lineNewtonianDerivative (realLineEuclideanIso x))
      (realLineEuclideanIso x) := by
    rcases lt_or_gt_of_ne hx' with hn | hp
    · simpa only [lineNewtonianDerivative, if_neg hn.not_ge, neg_div] using
        (hasDerivAt_abs_neg hn).div_const 2
    · simpa only [lineNewtonianDerivative, if_pos hp.le] using
        (hasDerivAt_abs_pos hp).div_const 2
  let L := realLineEuclideanIso.toContinuousLinearEquiv.toContinuousLinearMap
  have hdComp : HasFDerivAt newtonianOne
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (lineNewtonianDerivative (realLineEuclideanIso x))) ∘L L) x :=
    hd.hasFDerivAt.comp x L.hasFDerivAt
  rw [hdComp.fderiv, newtonianOneGradient_component]
  change realLineEuclideanIso (axis i) • lineNewtonianDerivative (realLineEuclideanIso x) = _
  rw [realLineEuclideanIso_axis, one_smul]

private theorem realLine_symm_deriv_apply {f : E 1 → ℝ} (t : ℝ) (i : Fin 1)
    (hf : DifferentiableAt ℝ f (realLineEuclideanIso.symm t)) :
    deriv (f ∘ realLineEuclideanIso.symm) t =
      fderiv ℝ f (realLineEuclideanIso.symm t) (axis i) := by
  let L := realLineEuclideanIso.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have h := (hf.hasFDerivAt.comp t L.hasFDerivAt).hasDerivAt
  change HasDerivAt (f ∘ realLineEuclideanIso.symm)
    (fderiv ℝ f (realLineEuclideanIso.symm t) (realLineEuclideanIso.symm 1)) t at h
  rw [h.deriv, Fin.fin_one_eq_zero i, axis, realLineEuclideanIso_symm_apply 1]

theorem newtonianOne_testDerivative (i : Fin 1) (φ : E 1 → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ y, newtonianOne y * fderiv ℝ φ y (axis i)) =
      -∫ y, newtonianOneGradient y i * φ y := by
  let e := realLineEuclideanIso.symm
  let ψ : ℝ → ℝ := φ ∘ e
  let L := e.toContinuousLinearEquiv.toContinuousLinearMap
  have hψ : ContDiff ℝ 1 ψ := hφ.comp L.contDiff
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph e.toHomeomorph
  have hM := e.measurePreserving
  have hEmb := e.toHomeomorph.measurableEmbedding
  have hLeft := hM.integral_comp hEmb (fun y => newtonianOne y * fderiv ℝ φ y (axis i))
  have hRight := hM.integral_comp hEmb (fun y => newtonianOneGradient y i * φ y)
  have hDeriv (t : ℝ) : fderiv ℝ φ (e t) (axis i) = deriv ψ t :=
    (realLine_symm_deriv_apply t i (hφ.differentiable one_ne_zero _)).symm
  rw [← hLeft, ← hRight]
  simp only [newtonianOne, newtonianOneGradient_component, e, LinearIsometryEquiv.apply_symm_apply]
  change (∫ x, |x| / 2 * fderiv ℝ φ (e x) (axis i)) =
    -∫ x, lineNewtonianDerivative x * ψ x
  simp_rw [hDeriv]
  exact realNewtonian_testDerivative ψ hψ hψc

theorem newtonianOne_distributionPairing (φ : E 1 → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ y, newtonianOne y * laplacian φ y) = φ 0 := by
  let e := realLineEuclideanIso.symm
  let ψ : ℝ → ℝ := φ ∘ e
  let D : E 1 → ℝ := fun x => fderiv ℝ φ x (axis 0)
  let L := e.toContinuousLinearEquiv.toContinuousLinearMap
  have hψ : ContDiff ℝ 2 ψ := hφ.comp L.contDiff
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph e.toHomeomorph
  have hD : ContDiff ℝ 1 D :=
    (ContinuousLinearMap.apply ℝ ℝ (axis 0)).contDiff.comp (hφ.fderiv_right (by norm_num))
  have hDeriv : deriv ψ = D ∘ e := by
    funext t
    exact realLine_symm_deriv_apply t 0 (hφ.differentiable (by norm_num) _)
  have hLap (t : ℝ) : laplacian φ (e t) = deriv (deriv ψ) t := by
    rw [hDeriv, realLine_symm_deriv_apply t 0 (hD.differentiable one_ne_zero _)]
    unfold laplacian
    rw [Fin.sum_univ_one]
  have hChange := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun y => newtonianOne y * laplacian φ y)
  rw [← hChange]
  simp only [newtonianOne, e, LinearIsometryEquiv.apply_symm_apply]
  change (∫ t, |t| / 2 * laplacian φ (e t)) = φ 0
  simp_rw [hLap]
  rw [realNewtonian_distributionPairing ψ hψ hψc]
  change φ (e 0) = φ 0
  rw [map_zero]

theorem newtonianOne_dilate {r : ℝ} (hr : 0 < r) (x : E 1) :
    newtonianOne (r • x) = r ^ (2 - (1 : ℤ)) * newtonianOne x := by
  rw [newtonianOne, newtonianOne, map_smul, smul_eq_mul, abs_mul, abs_of_pos hr]
  norm_num
  ring

private theorem oneDimensionalCLM_harmonicAt (L : E 1 →L[ℝ] ℝ) (x : E 1) : HarmonicAt L x := by
  refine ⟨L.contDiff.contDiffAt, Filter.Eventually.of_forall fun z => ?_⟩
  change Laplacian.laplacian (L : E 1 → ℝ) z = 0
  rw [HolderToCK.scalarLaplacian_eq_coordinateSum _ z L.contDiff.contDiffAt]
  simp only [ContinuousLinearMap.fderiv]
  apply Finset.sum_eq_zero
  intro i _
  rw [fderiv_const_apply, zero_apply]

theorem newtonianOne_harmonicOffZero :
    HarmonicOnNhd newtonianOne ({0}ᶜ : Set (E 1)) := by
  intro x hx
  have hx' : realLineEuclideanIso x ≠ 0 := by
    intro h
    exact hx (realLineEuclideanIso.injective (h.trans realLineEuclideanIso.map_zero.symm))
  let L := realLineEuclideanIso.toContinuousLinearEquiv.toContinuousLinearMap
  rcases lt_or_gt_of_ne hx' with hn | hp
  · have hLoc : newtonianOne =ᶠ[𝓝 x] ((-(1 / 2 : ℝ)) • L) := by
      filter_upwards [realLineEuclideanIso.continuous.continuousAt.eventually_lt continuousAt_const hn] with y hy
      change |realLineEuclideanIso y| / 2 = -(1 / 2) * realLineEuclideanIso y
      rw [abs_of_neg hy]
      ring
    exact (harmonicAt_congr_nhds hLoc).mpr (oneDimensionalCLM_harmonicAt ((-(1 / 2 : ℝ)) • L) x)
  · have hLoc : newtonianOne =ᶠ[𝓝 x] ((1 / 2 : ℝ) • L) := by
      filter_upwards [continuousAt_const.eventually_lt realLineEuclideanIso.continuous.continuousAt hp] with y hy
      change |realLineEuclideanIso y| / 2 = (1 / 2) * realLineEuclideanIso y
      rw [abs_of_pos hy]
      ring
    exact (harmonicAt_congr_nhds hLoc).mpr (oneDimensionalCLM_harmonicAt ((1 / 2 : ℝ) • L) x)


private theorem oneDimensional_affineOn_ball_of_harmonic {u : E 1 → ℝ}
    (a : E 1) {r : ℝ} (hr : 0 < r) (hu : HarmonicOnNhd u (closedBall a r)) :
    ∃ C : ℝ, ∀ x ∈ ball a r,
      u x = u a + C * (realLineEuclideanIso x - realLineEuclideanIso a) := by
  let e := realLineEuclideanIso
  let a' := e a
  let U := ball a' r
  let φ : ℝ → ℝ := u ∘ e.symm
  let D : E 1 → ℝ := fun x => fderiv ℝ u x (axis 0)
  have hBack (t : ℝ) (ht : t ∈ U) : e.symm t ∈ ball a r := by
    rw [mem_ball, ← e.isometry.dist_eq, LinearIsometryEquiv.apply_symm_apply]
    exact ht
  have hTo (x : E 1) (hx : x ∈ ball a r) : e x ∈ U := by
    change dist (e x) (e a) < r
    rw [e.isometry.dist_eq]
    exact hx
  have huBall : ContDiffOn ℝ 2 u (ball a r) := hu.contDiffOn.mono ball_subset_closedBall
  have hφ : ContDiffOn ℝ 2 φ U := by
    have hE := e.symm.toContinuousLinearEquiv.contDiff (n := 2)
    exact huBall.comp hE.contDiffOn (fun t ht => hBack t ht)
  have hD : ContDiffOn ℝ 1 D (ball a r) :=
    (huBall.fderiv_of_isOpen isOpen_ball (by norm_num)).clm_apply contDiffOn_const
  have hφFirst (t : ℝ) (ht : t ∈ U) : deriv φ t = D (e.symm t) :=
    realLine_symm_deriv_apply t 0
      ((huBall.contDiffAt (isOpen_ball.mem_nhds (hBack t ht))).differentiableAt (by norm_num))
  have hφSecond (t : ℝ) (ht : t ∈ U) : deriv (deriv φ) t = 0 := by
    have hNear : deriv φ =ᶠ[𝓝 t] D ∘ e.symm := by
      filter_upwards [isOpen_ball.mem_nhds ht] with y hy
      exact hφFirst y hy
    have hU2 := hu (e.symm t) (ball_subset_closedBall (hBack t ht))
    rw [hNear.deriv_eq, realLine_symm_deriv_apply t 0
      ((hD.contDiffAt (isOpen_ball.mem_nhds (hBack t ht))).differentiableAt one_ne_zero)]
    have hLap := HolderToCK.scalarLaplacian_eq_coordinateSum u (e.symm t) hU2.1
    rw [Fin.sum_univ_one] at hLap
    change fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single (0 : Fin 1) 1))
      (e.symm t) (EuclideanSpace.single (0 : Fin 1) 1) = 0
    rw [← hLap]
    exact hU2.2.eq_of_nhds
  have hCenter : a' ∈ U := mem_ball_self hr
  have hConnected : IsPreconnected U := (convex_ball a' r).isPreconnected
  have hDerivativeC : ContDiffOn ℝ 1 (deriv φ) U :=
    hφ.deriv_of_isOpen isOpen_ball (by norm_num)
  let C := deriv φ a'
  have hConst (t : ℝ) (ht : t ∈ U) : deriv φ t = C :=
    isOpen_ball.is_const_of_deriv_eq_zero hConnected
      (hDerivativeC.differentiableOn one_ne_zero) (fun t ht => hφSecond t ht) ht hCenter
  let F := fun t : ℝ => φ a' + C * (t - a')
  have hFDeriv (t : ℝ) : HasDerivAt F C t := by
    change HasDerivAt (fun x => φ a' + C * (id x - a')) C t
    simpa only [mul_one] using (((hasDerivAt_id t).sub_const a').const_mul C).const_add (φ a')
  have hEq : Set.EqOn φ F U := by
    apply isOpen_ball.eqOn_of_deriv_eq hConnected
      (hφ.differentiableOn (by norm_num)) (fun t _ => (hFDeriv t).differentiableAt.differentiableWithinAt)
    · intro t ht
      rw [(hFDeriv t).deriv, hConst t ht]
    · exact hCenter
    · simp only [F, sub_self, mul_zero, add_zero]
  refine ⟨C, fun x hx => ?_⟩
  have h_x := hEq (hTo x hx)
  change u (e.symm (e x)) = u (e.symm (e a)) + C * (e x - e a) at h_x
  simpa only [LinearIsometryEquiv.symm_apply_apply] using h_x

/-- In dimension one a harmonic function is affine on the integration interval,
so every even probability density gives its value at the center. -/
theorem oneDimensional_harmonic_radial_probability_mean
    (u : E 1 → ℝ) (a : E 1) (r : ℝ) (ρ : E 1 → ℝ)
    (hr : 0 < r) (hu : HarmonicOnNhd u (closedBall a r)) (hρ : Continuous ρ)
    (hRad : ∃ profile : ℝ → ℝ, ∀ y, ρ y = profile ‖y‖)
    (_hNonneg : ∀ y, 0 ≤ ρ y) (hSupp : Function.support ρ ⊆ ball 0 r)
    (hMass : (∫ y, ρ y) = 1) : (∫ y, ρ y * u (a - y)) = u a := by
  obtain ⟨C, hC⟩ := oneDimensional_affineOn_ball_of_harmonic a hr hu
  obtain ⟨profile, hProfile⟩ := hRad
  let e := realLineEuclideanIso
  let f := fun y : E 1 => ρ y * e y
  have hKernelSupport : HasCompactSupport ρ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E 1) r)
      (hSupp.trans ball_subset_closedBall)
  have hKernelI : Integrable ρ := hρ.integrable_of_hasCompactSupport hKernelSupport
  have hfI : Integrable f :=
    (hρ.mul e.continuous).integrable_of_hasCompactSupport hKernelSupport.mul_right
  have hMoment : (∫ y, f y) = 0 := by
    have hNeg := integral_neg_eq_self (f := f) (μ := (volume : Measure (E 1)))
    have hOdd (y : E 1) : f (-y) = -f y := by
      change ρ (-y) * e (-y) = -(ρ y * e y)
      rw [hProfile (-y), norm_neg, ← hProfile y, map_neg, mul_neg]
    simp_rw [hOdd, integral_neg] at hNeg
    exact (neg_eq_self.mp hNeg)
  have hPair (y : E 1) : ρ y * u (a - y) = ρ y * u a - C * f y := by
    by_cases hy : ρ y = 0
    · simp only [hy, f, zero_mul, mul_zero, sub_self]
    · have hy' : y ∈ ball (0 : E 1) r := hSupp (Function.mem_support.mpr hy)
      have hAY : a - y ∈ ball a r := by
        have hSub : a - y - a = -y := by abel
        rw [mem_ball, dist_eq_norm, hSub, norm_neg]
        simpa only [mem_ball, dist_zero_right] using hy'
      rw [hC _ hAY, map_sub]
      change ρ y * (u a + C * (e a - e y - e a)) = ρ y * u a - C * f y
      dsimp [f]
      ring
  simp_rw [hPair]
  rw [integral_sub (hKernelI.mul_const (u a)) (hfI.const_mul C), integral_mul_const,
    integral_const_mul, hMass, hMoment, mul_zero, one_mul, sub_zero]

end SupportingAnalysis
