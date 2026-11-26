module

public import Thesis.Foundation.QuaternionSplittingEnergy
public import Thesis.Foundation.VacuumFreeHomotopy
public import Thesis.MeasureGeometry.PlanarDiskGrowth
import HarmonicMaps.Analysis.AnnularPolarIntegral
import StratificationTheory.Foundation.AngularL2Membership

/-! Quaternion charge and angular Dirichlet energy on a planar annulus. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory Topology
open scoped ContDiff Matrix.Norms.Frobenius

namespace Thesis

/-- The singular cost of an actual Sobolev circle loop is bounded by its angular energy. -/
theorem nativeVacuumLoop_splittingCost_le_energy (a : BulkCoefficients)
    (f : C(NativeCircle, vacuum a)) (v : Sphere3)
    (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase)
    (h : VacuumLoopH1 (nativeVacuumLoopPath a f v hv)) :
    vacuumSplittingCost a v (nativeVacuumLoopWord a f v hv) ≤
      vacuumLoopEnergy (nativeVacuumLoopPath a f v hv) := by
  rw [vacuumSplittingCost_eq]
  apply (vacuumClassCost_ge_splittingWeight a v _).trans
  have hb : BddBelow (vacuumClassEnergies a v (nativeVacuumLoopWord a f v hv)) := by
    refine ⟨0, ?_⟩
    rintro E ⟨γ, _, _, rfl⟩
    exact vacuumLoopEnergy_nonneg γ
  exact csInf_le hb ⟨nativeVacuumLoopPath a f v hv, rfl, h, rfl⟩

theorem nativeVacuumLoop_splittingCost_homotopic (a : BulkCoefficients)
    {f g : C(NativeCircle, vacuum a)} (h : f.Homotopic g) (v w : Sphere3)
    (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase)
    (hw : vacuumQuaternionProjection a w = g nativeCircleLoopBase) :
    vacuumSplittingCost a v (nativeVacuumLoopWord a f v hv) =
      vacuumSplittingCost a w (nativeVacuumLoopWord a g w hw) := by
  rw [vacuumSplittingCost_eq, vacuumSplittingCost_eq,
    quaternionSplittingWeight_conj ((nativeVacuum_homotopic_iff_isConj a f g v w hv hw).1 h)]

theorem existsUnique_nativeVacuumCircleCost (a : BulkCoefficients) (f : C(NativeCircle, vacuum a)) :
    ∃! E : ℝ, ∀ (v : Sphere3) (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase),
      E = vacuumSplittingCost a v (nativeVacuumLoopWord a f v hv) := by
  obtain ⟨w, hw⟩ := vacuumQuaternionProjection_surjective a (f nativeCircleLoopBase)
  refine ⟨vacuumSplittingCost a w (nativeVacuumLoopWord a f w hw), ?_, ?_⟩
  · intro v hv
    exact nativeVacuumLoop_splittingCost_homotopic a (ContinuousMap.Homotopic.refl f) w v hw hv
  · exact fun _ h => h w hw

/-- The singular energy of a continuous native vacuum circle, independent of the chosen lift. -/
def nativeVacuumCircleCost (a : BulkCoefficients) (f : C(NativeCircle, vacuum a)) : ℝ :=
  Classical.choose (existsUnique_nativeVacuumCircleCost a f)

theorem nativeVacuumCircleCost_eq (a : BulkCoefficients) (f : C(NativeCircle, vacuum a))
    (v : Sphere3) (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase) :
    nativeVacuumCircleCost a f = vacuumSplittingCost a v (nativeVacuumLoopWord a f v hv) :=
  (Classical.choose_spec (existsUnique_nativeVacuumCircleCost a f)).1 v hv

theorem nativeVacuumCircleCost_homotopic (a : BulkCoefficients) {f g : C(NativeCircle, vacuum a)}
    (h : f.Homotopic g) :
    nativeVacuumCircleCost a f = nativeVacuumCircleCost a g := by
  obtain ⟨v, hv⟩ := vacuumQuaternionProjection_surjective a (f nativeCircleLoopBase)
  obtain ⟨w, hw⟩ := vacuumQuaternionProjection_surjective a (g nativeCircleLoopBase)
  rw [nativeVacuumCircleCost_eq a f v hv, nativeVacuumCircleCost_eq a g w hw]
  exact nativeVacuumLoop_splittingCost_homotopic a h v w hv hw

theorem nativeVacuumCircleCost_nonneg (a : BulkCoefficients) (f : C(NativeCircle, vacuum a)) :
    0 ≤ nativeVacuumCircleCost a f := by
  obtain ⟨v, hv⟩ := vacuumQuaternionProjection_surjective a (f nativeCircleLoopBase)
  rw [nativeVacuumCircleCost_eq a f v hv, vacuumSplittingCost_eq]
  exact mul_nonneg (kappaStar_pos a).le (Nat.cast_nonneg _)

theorem nativeVacuumCircleCost_const (a : BulkCoefficients) (A : vacuum a) :
    nativeVacuumCircleCost a (ContinuousMap.const NativeCircle A) = 0 := by
  obtain ⟨v, hv⟩ := vacuumQuaternionProjection_surjective a A
  rw [nativeVacuumCircleCost_eq a (ContinuousMap.const NativeCircle A) v hv,
    nativeVacuumLoopWord_const a v A hv, vacuumSplittingCost_one]

private def circleBasis (i : Fin 2) : Plane := EuclideanSpace.single i (1 : ℝ)

private theorem circleNativeParam_val_expansion (t : ℝ) :
    (circleNativeParam t).val = Real.cos t • circleBasis 0 + Real.sin t • circleBasis 1 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [circleNativeParam_coe, circleBasis]

theorem contDiff_circleNativeParam_val_infty :
    ContDiff ℝ ∞ (fun t => (circleNativeParam t).val) := by
  simp_rw [circleNativeParam_val_expansion]
  exact (Real.contDiff_cos.smul contDiff_const).add (Real.contDiff_sin.smul contDiff_const)

theorem contDiff_circleNativeParam_val :
    ContDiff ℝ 1 (fun t => (circleNativeParam t).val) :=
  contDiff_circleNativeParam_val_infty.of_le (by decide)

private theorem hasDerivAt_circleNativeParam_val (t : ℝ) :
    HasDerivAt (fun s => (circleNativeParam s).val)
      (-Real.sin t • circleBasis 0 + Real.cos t • circleBasis 1) t := by
  have h := ((Real.hasDerivAt_cos t).smul_const (circleBasis 0)).add
    ((Real.hasDerivAt_sin t).smul_const (circleBasis 1))
  exact h.congr_of_eventuallyEq (Eventually.of_forall circleNativeParam_val_expansion)

theorem norm_deriv_circleNativeParam_val (t : ℝ) :
    ‖deriv (fun s => (circleNativeParam s).val) t‖ = 1 := by
  rw [(hasDerivAt_circleNativeParam_val t).deriv]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [PiLp.add_apply, PiLp.smul_apply, circleBasis, PiLp.single_apply,
    if_true, h01, h10, if_false, smul_eq_mul, mul_zero, mul_one, add_zero,
    zero_add, neg_sq, one_pow]
  exact Real.sin_sq_add_cos_sq t

private theorem normSq_CLM_circle_velocity_le (D : Plane →L[ℝ] Tensor) (t : ℝ) :
    ‖D (-Real.sin t • circleBasis 0 + Real.cos t • circleBasis 1)‖ ^ 2 ≤
      ∑ j : Fin 2, ‖D (circleBasis j)‖ ^ 2 := by
  let a := ‖D (circleBasis 0)‖
  let b := ‖D (circleBasis 1)‖
  let α := |Real.sin t|
  let β := |Real.cos t|
  have hα : 0 ≤ α := abs_nonneg _
  have hβ : 0 ≤ β := abs_nonneg _
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hnorm : ‖D (-Real.sin t • circleBasis 0 + Real.cos t • circleBasis 1)‖ ≤ α * a + β * b := by
    rw [map_add, map_smul, map_smul]
    exact (norm_add_le _ _).trans_eq (by
      simp only [norm_smul, Real.norm_eq_abs, abs_neg, α, β, a, b])
  have hs : α ^ 2 + β ^ 2 = 1 := by
    simpa only [α, β, sq_abs] using Real.sin_sq_add_cos_sq t
  rw [Fin.sum_univ_two]
  change _ ≤ a ^ 2 + b ^ 2
  calc
    _ ≤ (α * a + β * b) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (mul_nonneg hα ha) (mul_nonneg hβ hb))).2 hnorm
    _ ≤ (α ^ 2 + β ^ 2) * (a ^ 2 + b ^ 2) := by
      nlinarith only [sq_nonneg (α * b - β * a)]
    _ = _ := by rw [hs, one_mul]

/-- A circular restriction of an ambient tensor map with vacuum-valued traces. -/
def planarVacuumCircleTrace (a : BulkCoefficients) (Q : Plane → S0) (hQ : Continuous Q)
    (c : Plane) (r : ℝ) (hN : ∀ z : NativeCircle, Q (c + r • z.val) ∈ vacuum a) :
    C(NativeCircle, vacuum a) := by
  have hcircle : Continuous (fun z : NativeCircle => c + r • z.val) := by fun_prop
  have hcts : Continuous (fun z : NativeCircle => Q (c + r • z.val)) := hQ.comp hcircle
  exact ⟨fun z => ⟨Q (c + r • z.val), hN z⟩, hcts.subtype_mk hN⟩

/-- The smooth planar Dirichlet density computed from its two Euclidean derivative columns. -/
def planarSmoothDirichletDensity (Q : Plane → S0) (x : Plane) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin 2, ‖fderiv ℝ (fun y => (Q y : Tensor)) x (EuclideanSpace.single j 1)‖ ^ 2

theorem planarSmoothDirichletDensity_nonneg (Q : Plane → S0) (x : Plane) :
    0 ≤ planarSmoothDirichletDensity Q x := by
  unfold planarSmoothDirichletDensity
  positivity

theorem continuous_planarSmoothDirichletDensity {Q : Plane → S0} (hQ : ContDiff ℝ 1 Q) :
    Continuous (planarSmoothDirichletDensity Q) := by
  have hQT : ContDiff ℝ 1 (fun y => (Q y : Tensor)) :=
    symmetricTraceless.subtypeL.contDiff.comp hQ
  unfold planarSmoothDirichletDensity
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (((hQT.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm.pow 2))

private theorem vacuumLoopParameter_val {T x : ℝ} (hT : 0 < T) (hx : x ∈ Icc 0 T) :
    (vacuumLoopParameter T x).val = x / T :=
  congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨div_nonneg hx.1 hT.le, (div_le_one hT).2 hx.2⟩)

private theorem angular_tensor_curve_smooth {Q : Plane → S0} (hQ : ContDiff ℝ 1 Q)
    (c : Plane) (r : ℝ) :
    ContDiff ℝ 1 (fun t => (Q (c + r • (circleNativeParam (t - Real.pi)).val) : Tensor)) := by
  have harg : ContDiff ℝ 1 (fun t : ℝ => t - Real.pi) := contDiff_id.sub contDiff_const
  have hcircle : ContDiff ℝ 1 (fun t => (circleNativeParam (t - Real.pi)).val) :=
    contDiff_circleNativeParam_val.comp harg
  have hpath : ContDiff ℝ 1 (fun t => c + r • (circleNativeParam (t - Real.pi)).val) :=
    contDiff_const.add (hcircle.const_smul r)
  exact (symmetricTraceless.subtypeL.contDiff.comp hQ).comp hpath

private theorem angular_tensor_curve_density_le {Q : Plane → S0} (hQ : ContDiff ℝ 1 Q)
    (c : Plane) (r θ : ℝ) :
    (1 / 2 : ℝ) * ‖deriv (fun t => (Q (c + r • (circleNativeParam (t - Real.pi)).val) : Tensor)) θ‖ ^ 2 ≤
      r ^ 2 * planarSmoothDirichletDensity Q (c + r • (circleNativeParam (θ - Real.pi)).val) := by
  let x := c + r • (circleNativeParam (θ - Real.pi)).val
  let f (z : Plane) := (Q z : Tensor)
  let D := fderiv ℝ f x
  let velocity := -Real.sin (θ - Real.pi) • circleBasis 0 + Real.cos (θ - Real.pi) • circleBasis 1
  have hf : ContDiff ℝ 1 f := symmetricTraceless.subtypeL.contDiff.comp hQ
  have harg : HasDerivAt (fun t : ℝ => t - Real.pi) 1 θ := (hasDerivAt_id θ).sub_const Real.pi
  have hangular : HasDerivAt (fun t => (circleNativeParam (t - Real.pi)).val) velocity θ := by
    have h := (hasDerivAt_circleNativeParam_val (θ - Real.pi)).scomp θ harg
    change HasDerivAt (fun t => (circleNativeParam (t - Real.pi)).val) ((1 : ℝ) • velocity) θ at h
    simpa only [one_smul] using h
  have hpath : HasDerivAt (fun t => c + r • (circleNativeParam (t - Real.pi)).val) (r • velocity) θ :=
    (hangular.const_smul r).const_add c
  have hF : HasFDerivAt f D x := (hf.differentiable one_ne_zero x).hasFDerivAt
  have hderiv : HasDerivAt (fun t => (Q (c + r • (circleNativeParam (t - Real.pi)).val) : Tensor))
      (D (r • velocity)) θ :=
    hF.comp_hasDerivAt (f := fun t => c + r • (circleNativeParam (t - Real.pi)).val)
      (f' := r • velocity) (l := f) (l' := D) θ hpath
  have heq : (1 / 2 : ℝ) * ‖deriv (fun t => (Q (c + r • (circleNativeParam (t - Real.pi)).val) : Tensor)) θ‖ ^ 2 =
      (1 / 2 : ℝ) * ‖D (r • velocity)‖ ^ 2 := congrArg (fun M : Tensor => (1 / 2 : ℝ) * ‖M‖ ^ 2) hderiv.deriv
  rw [heq, map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  change (1 / 2 : ℝ) * (r ^ 2 * ‖D velocity‖ ^ 2) ≤
    r ^ 2 * ((1 / 2 : ℝ) * ∑ i : Fin 2, ‖D (circleBasis i)‖ ^ 2)
  calc
    _ = (r ^ 2 * (1 / 2 : ℝ)) * ‖D velocity‖ ^ 2 := by ring
    _ ≤ (r ^ 2 * (1 / 2 : ℝ)) * ∑ i : Fin 2, ‖D (circleBasis i)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (normSq_CLM_circle_velocity_le D (θ - Real.pi)) (by positivity)
    _ = _ := by ring

/-- On a vacuum-valued circle the actual quaternion cost is bounded by the
ambient angular energy, with the Euclidean radius factor. -/
theorem planarVacuumCircleTrace_splittingCost_le (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) (c : Plane) (r : ℝ)
    (hN : ∀ z : NativeCircle, Q (c + r • z.val) ∈ vacuum a)
    (v : Sphere3)
    (hv : vacuumQuaternionProjection a v =
      planarVacuumCircleTrace a Q hQ.continuous c r hN nativeCircleLoopBase) :
    let f := planarVacuumCircleTrace a Q hQ.continuous c r hN
    vacuumSplittingCost a v (nativeVacuumLoopWord a f v hv) ≤
      r ^ 2 * ∫ θ in Ioo (-Real.pi) Real.pi,
        planarSmoothDirichletDensity Q (c + r • (circleNativeParam θ).val) := by
  intro f
  let T := 2 * Real.pi
  have hT : 0 < T := Real.two_pi_pos
  let γ := nativeVacuumLoopPath a f v hv
  let F (x : ℝ) := (Q (c + r • (circleNativeParam (x - Real.pi)).val) : Tensor)
  let G (x : ℝ) := planarSmoothDirichletDensity Q (c + r • (circleNativeParam x).val)
  have hF : ContDiff ℝ 1 F := angular_tensor_curve_smooth hQ c r
  have hval : Continuous (fun t => (circleNativeParam t).val) :=
    continuous_subtype_val.comp continuous_circleNativeParam
  have hcircle : Continuous (fun t => c + r • (circleNativeParam t).val) :=
    continuous_const.add (hval.const_smul r)
  have hG : Continuous G := (continuous_planarSmoothDirichletDensity hQ).comp hcircle
  have hEq : EqOn (vacuumLoopTensor γ T) F (Icc 0 T) := by
    intro t ht
    have he : T * (vacuumLoopParameter T t).val = t := by
      rw [vacuumLoopParameter_val hT ht]
      field_simp
    change (Q (c + r • (circleNativeParam (T * (vacuumLoopParameter T t).val - Real.pi)).val) : Tensor) =
      F t
    rw [he]
  have hEqDeriv : EqOn (deriv (vacuumLoopTensor γ T)) (deriv F) (Ioo 0 T) := by
    intro t ht
    have ht' : ∀ᶠ s in 𝓝 t, s ∈ Icc 0 T := Icc_mem_nhds ht.1 ht.2
    have hNear : vacuumLoopTensor γ T =ᶠ[𝓝 t] F := ht'.mono fun _ hs => hEq hs
    exact hNear.deriv_eq
  have hSob : VacuumLoopH1 γ := by
    constructor
    · apply ContDiffOn.absolutelyContinuousOnInterval
      rw [uIcc_of_le hT.le]
      exact hF.contDiffOn.congr hEq
    · have hL : MemLp (deriv F) 2 (volume.restrict (Ioo 0 T)) := by
        obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hF.continuous_deriv_one.continuousOn
        refine (memLp_const (μ := volume.restrict (Ioo 0 T)) B).mono'
          (aestronglyMeasurable_deriv _ _) ?_
        apply (ae_restrict_iff' measurableSet_Ioo).2
        exact Eventually.of_forall fun t ht => hB t (Ioo_subset_Icc_self ht)
      exact (memLp_congr_ae ((ae_restrict_iff' measurableSet_Ioo).2
        (Eventually.of_forall fun _ ht => hEqDeriv ht))).2 hL
  have hAng : vacuumLoopEnergy γ =
      ∫ x in 0..T, (1 / 2 : ℝ) * ‖deriv F x‖ ^ 2 := by
    apply intervalIntegral.integral_congr_Ioo_of_le hT.le
    intro t ht
    exact congrArg (fun M : Tensor => (1 / 2 : ℝ) * ‖M‖ ^ 2) (hEqDeriv ht)
  have hθ : (∫ x in 0..T, G (x - Real.pi)) = ∫ θ in Ioo (-Real.pi) Real.pi, G θ := by
    have hEnd : T + -Real.pi = Real.pi := by dsimp only [T]; ring
    calc
      _ = ∫ x in 0..T, G (x + -Real.pi) := by simp only [sub_eq_add_neg]
      _ = ∫ x in (0 + -Real.pi)..(T + -Real.pi), G x :=
        intervalIntegral.integral_comp_add_right G (-Real.pi)
      _ = _ := by
        rw [zero_add, hEnd, intervalIntegral.integral_of_le
          (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]), ← restrict_Ioo_eq_restrict_Ioc]
  calc
    _ ≤ vacuumLoopEnergy γ := nativeVacuumLoop_splittingCost_le_energy a f v hv hSob
    _ = _ := hAng
    _ ≤ ∫ x in 0..T, r ^ 2 * G (x - Real.pi) := by
      apply intervalIntegral.integral_mono_on hT.le
      · exact (continuous_const.mul (hF.continuous_deriv_one.norm.pow 2)).intervalIntegrable _ _
      · exact (continuous_const.mul (hG.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _
      · exact fun x _ => angular_tensor_curve_density_le hQ c r x
    _ = _ := by rw [intervalIntegral.integral_const_mul, hθ]

theorem dist_planarCircle (c : Plane) {r : ℝ} (hr : 0 ≤ r) (z : NativeCircle) :
    dist (c + r • z.val) c = r := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr,
    mem_sphere_zero_iff_norm.mp z.property, mul_one]

/-- The vacuum restriction at a radius in the closed annulus. -/
def planarVacuumAnnulusTrace (a : BulkCoefficients) (Q : Plane → S0) (hQ : Continuous Q)
    (c : Plane) {s R : ℝ} (hs : 0 ≤ s)
    (hN : ∀ x, dist x c ∈ Icc s R → Q x ∈ vacuum a) (r : ℝ) (hr : r ∈ Icc s R) :
    C(NativeCircle, vacuum a) :=
  planarVacuumCircleTrace a Q hQ c r fun z =>
    hN _ (by rw [dist_planarCircle c (hs.trans hr.1) z]; exact hr)

theorem planarVacuumAnnulusTrace_homotopic (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : Continuous Q) (c : Plane) {s R : ℝ} (hs : 0 ≤ s)
    (hN : ∀ x, dist x c ∈ Icc s R → Q x ∈ vacuum a) {r₀ r₁ : ℝ}
    (h₀ : r₀ ∈ Icc s R) (h₁ : r₁ ∈ Icc s R) :
    (planarVacuumAnnulusTrace a Q hQ c hs hN r₀ h₀).Homotopic
      (planarVacuumAnnulusTrace a Q hQ c hs hN r₁ h₁) := by
  let σ (t : unitInterval) := (1 - t.val) * r₀ + t.val * r₁
  have hσ (t : unitInterval) : σ t ∈ Icc s R :=
    convex_iff_add_mem.mp (convex_Icc _ _) h₀ h₁ (sub_nonneg.mpr t.property.2) t.property.1
      (sub_add_cancel 1 t.val)
  let H (p : unitInterval × NativeCircle) := c + σ p.1 • p.2.val
  have hH : Continuous H := by dsimp only [H, σ]; fun_prop
  have hVac (p : unitInterval × NativeCircle) : Q (H p) ∈ vacuum a :=
    hN _ (by change dist (c + σ p.1 • p.2.val) c ∈ Icc s R
             rw [dist_planarCircle c (hs.trans (hσ p.1).1) p.2]
             exact hσ p.1)
  have hcts : Continuous (fun p => Q (H p)) := hQ.comp hH
  refine ⟨⟨⟨fun p => ⟨Q (H p), hVac p⟩, hcts.subtype_mk hVac⟩, ?_, ?_⟩⟩
  · intro z
    apply Subtype.ext
    change Q (c + σ (0 : unitInterval) • z.val) = Q (c + r₀ • z.val)
    have hσ₀ : σ 0 = r₀ := by change (1 - 0) * r₀ + 0 * r₁ = r₀; ring
    rw [hσ₀]
  · intro z
    apply Subtype.ext
    change Q (c + σ (1 : unitInterval) • z.val) = Q (c + r₁ • z.val)
    have hσ₁ : σ 1 = r₁ := by change (1 - 1) * r₀ + 1 * r₁ = r₁; ring
    rw [hσ₁]

private theorem smooth_circle_integral_eq_angular {Q : Plane → S0} (hQ : ContDiff ℝ 1 Q)
    (c : Plane) (r : ℝ) :
    (∫ z : NativeCircle, planarSmoothDirichletDensity Q (c + r • z.val)
      ∂(volume : Measure Plane).toSphere) =
      ∫ θ in Ioo (-Real.pi) Real.pi, planarSmoothDirichletDensity Q (c + r • (circleNativeParam θ).val) := by
  let f (z : NativeCircle) := planarSmoothDirichletDensity Q (c + r • z.val)
  let σ : Measure NativeCircle := Measure.euclideanHausdorffMeasure 1
  have hσ : (volume : Measure Plane).toSphere = σ :=
    (euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)).symm
  letI : IsFiniteMeasure σ := ⟨by
    change Measure.euclideanHausdorffMeasure 1 (Set.univ : Set NativeCircle) < ⊤
    rw [native_circle_measure_univ]
    exact ENNReal.ofReal_lt_top⟩
  have hf : Continuous f :=
    (continuous_planarSmoothDirichletDensity hQ).comp (by fun_prop : Continuous (fun z : NativeCircle => c + r • z.val))
  letI : CompactSpace NativeCircle := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hil : Integrable f σ :=
    (integrableOn_univ.mp (ContinuousOn.integrableOn_compact isCompact_univ hf.continuousOn))
  have he := (integrable_circleNativeParam_Ioc_and_integral f hil).2
  rw [← restrict_Ioo_eq_restrict_Ioc] at he
  simpa only [hσ, f] using he.symm

/-- The Dirichlet energy on a smooth vacuum annulus controls the outer
quaternion charge times the literal logarithmic radius ratio. -/
theorem planarVacuumAnnulus_energy_ge_splittingCost (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) (c : Plane) {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hN : ∀ x, dist x c ∈ Icc s R → Q x ∈ vacuum a) :
    let f := planarVacuumAnnulusTrace a Q hQ.continuous c hs.le hN R ⟨hsR, le_rfl⟩
    ∀ (v : Sphere3) (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase),
      vacuumSplittingCost a v (nativeVacuumLoopWord a f v hv) * Real.log (R / s) ≤
        ∫ x in ball c R \ ball c s, planarSmoothDirichletDensity Q x := by
  intro f v hv
  let E := vacuumSplittingCost a v (nativeVacuumLoopWord a f v hv)
  let G (r : ℝ) := ∫ θ in Ioo (-Real.pi) Real.pi,
    planarSmoothDirichletDensity Q (c + r • (circleNativeParam θ).val)
  have hRad (r : ℝ) (hr : r ∈ Icc s R) : E / r ≤ r * G r := by
    let g := planarVacuumAnnulusTrace a Q hQ.continuous c hs.le hN r hr
    have hH : g.Homotopic f := planarVacuumAnnulusTrace_homotopic a Q hQ.continuous c hs.le hN hr ⟨hsR, le_rfl⟩
    obtain ⟨w, hw⟩ := vacuumQuaternionProjection_surjective a (g nativeCircleLoopBase)
    have hE : vacuumSplittingCost a w (nativeVacuumLoopWord a g w hw) = E :=
      nativeVacuumLoop_splittingCost_homotopic a hH w v hw hv
    have hBound := planarVacuumCircleTrace_splittingCost_le a Q hQ c r
      (fun z => hN _ (by rw [dist_planarCircle c (hs.le.trans hr.1) z]; exact hr)) w hw
    change vacuumSplittingCost a w (nativeVacuumLoopWord a g w hw) ≤ r ^ 2 * G r at hBound
    rw [hE] at hBound
    apply (div_le_iff₀ (hs.trans_le hr.1)).2
    exact hBound.trans_eq (by ring)
  have hDensityInt : IntegrableOn (planarSmoothDirichletDensity Q) (ball c R \ ball c s) :=
    ((continuous_planarSmoothDirichletDensity hQ).continuousOn.integrableOn_compact (isCompact_closedBall c R)).mono_set
      (sdiff_subset.trans ball_subset_closedBall)
  have hPolar := HarmonicMaps.integral_annulus_eq_polar (by decide : 0 < 2) hs hsR hDensityInt
  have hPolar' : (∫ x in ball c R \ ball c s, planarSmoothDirichletDensity Q x) =
      ∫ t in s..R, t * G t := by
    rw [hPolar]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Nat.reduceSub, pow_one, smooth_circle_integral_eq_angular hQ, G]
  have hprod : Continuous (fun p : ℝ × ℝ =>
      planarSmoothDirichletDensity Q (c + p.1 • (circleNativeParam p.2).val)) :=
    (continuous_planarSmoothDirichletDensity hQ).comp
      (continuous_const.add (continuous_fst.smul (continuous_subtype_val.comp
        (continuous_circleNativeParam.comp continuous_snd))))
  have hGcts : Continuous G := by
    have h := continuous_parametric_integral_of_continuous (μ := volume)
      (f := fun r t : ℝ => planarSmoothDirichletDensity Q (c + r • (circleNativeParam t).val)) hprod
      (isCompact_Icc (a := -Real.pi) (b := Real.pi))
    have he : (fun r => ∫ θ in Icc (-Real.pi) Real.pi,
        planarSmoothDirichletDensity Q (c + r • (circleNativeParam θ).val)) = G := by
      funext r
      rw [← restrict_Ioo_eq_restrict_Icc]
    rwa [he] at h
  have hLeft : IntervalIntegrable (fun t => E / t) volume s R := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hsR]
    exact continuousOn_const.div continuousOn_id fun _ ht => (hs.trans_le ht.1).ne'
  have hCmp := intervalIntegral.integral_mono_on hsR hLeft
    ((continuous_id.mul hGcts).intervalIntegrable _ _) hRad
  have hLog : (∫ t in s..R, E / t) = E * Real.log (R / s) := by
    simp only [show (fun t => E / t) = fun t => E * (1 / t) from funext fun _ => by ring,
      intervalIntegral.integral_const_mul, integral_one_div_of_pos hs (hs.trans_le hsR)]
  exact hLog.symm.le.trans (hCmp.trans_eq hPolar'.symm)

/-- A disk growing through a smooth vacuum region sweeps at least its
unchanged quaternion charge times the elapsed logarithmic time. -/
theorem planarVacuumDiskGrowth_energy_ge_splittingCost (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) (B : PlanarDisk) {t : ℝ} (ht : 0 ≤ t)
    (hN : ∀ x, dist x B.center ∈ Icc B.radius (B.grow t).radius → Q x ∈ vacuum a) :
    let f := planarVacuumAnnulusTrace a Q hQ.continuous B.center B.radius_pos.le hN (B.grow t).radius
      ⟨by simpa only [PlanarDisk.grow, Real.exp_zero, one_mul] using B.grow_radius_mono ht, le_rfl⟩
    ∀ (v : Sphere3) (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase),
      t * vacuumSplittingCost a v (nativeVacuumLoopWord a f v hv) ≤
        ∫ x in (B.grow t).interior \ B.interior, planarSmoothDirichletDensity Q x := by
  intro f v hv
  have hmono : B.radius ≤ (B.grow t).radius := by
    simpa only [PlanarDisk.grow, Real.exp_zero, one_mul] using B.grow_radius_mono ht
  have hLog : Real.log ((B.grow t).radius / B.radius) = t := by
    change Real.log (Real.exp t * B.radius / B.radius) = t
    rw [mul_div_cancel_right₀ _ B.radius_pos.ne', Real.log_exp]
  have h := planarVacuumAnnulus_energy_ge_splittingCost a Q hQ B.center B.radius_pos hmono hN v hv
  change vacuumSplittingCost a v (nativeVacuumLoopWord a f v hv) * Real.log ((B.grow t).radius / B.radius) ≤
    ∫ x in (B.grow t).interior \ B.interior, planarSmoothDirichletDensity Q x at h
  rwa [hLog, mul_comm] at h

/-- A finite family of disjoint growing disks accumulates the sum of their charges
over the disjoint swept annuli. -/
theorem planarVacuumDiskGrowth_totalEnergy_ge (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) {ι : Type*} [Fintype ι] (B : ι → PlanarDisk) {t : ℝ} (ht : 0 ≤ t)
    (hdisj : Pairwise (fun i j => Disjoint ((B i).grow t).interior ((B j).grow t).interior))
    (hN : ∀ i x, dist x (B i).center ∈ Icc (B i).radius ((B i).grow t).radius → Q x ∈ vacuum a) :
    let f (i : ι) := planarVacuumAnnulusTrace a Q hQ.continuous (B i).center (B i).radius_pos.le
      (hN i) ((B i).grow t).radius
        ⟨by simpa only [PlanarDisk.grow, Real.exp_zero, one_mul] using (B i).grow_radius_mono ht, le_rfl⟩
    ∀ (v : ι → Sphere3) (hv : ∀ i, vacuumQuaternionProjection a (v i) = f i nativeCircleLoopBase),
      t * (∑ i, vacuumSplittingCost a (v i) (nativeVacuumLoopWord a (f i) (v i) (hv i))) ≤
        ∫ x in ⋃ i, ((B i).grow t).interior \ (B i).interior, planarSmoothDirichletDensity Q x := by
  intro f v hv
  let S (i : ι) := ((B i).grow t).interior \ (B i).interior
  have hSmeas (i : ι) : MeasurableSet (S i) := measurableSet_ball.diff measurableSet_ball
  have hSdisj : Pairwise (fun i j => Disjoint (S i) (S j)) :=
    fun _ _ hij => (hdisj hij).mono sdiff_subset sdiff_subset
  have hSInt (i : ι) : IntegrableOn (planarSmoothDirichletDensity Q) (S i) :=
    ((continuous_planarSmoothDirichletDensity hQ).continuousOn.integrableOn_compact
      (isCompact_closedBall (B i).center ((B i).grow t).radius)).mono_set
        (sdiff_subset.trans ball_subset_closedBall)
  change _ ≤ ∫ x in ⋃ i, S i, planarSmoothDirichletDensity Q x
  rw [integral_iUnion_fintype hSmeas hSdisj hSInt, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    planarVacuumDiskGrowth_energy_ge_splittingCost a Q hQ (B i) ht (hN i) (v i) (hv i)

end Thesis
