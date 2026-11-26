module

public import Thesis.Interpolation.CylinderTraceBoundaryCollars
import HarmonicMaps.Analysis.RadialCutoffDerivative
import HarmonicMaps.Analysis.SobolevCutoff
import StratificationTheory.Foundation.CylinderSurfaceProductMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Native weak zero extension across the lateral boundary of a cylinder. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal NNReal Topology

namespace Thesis.MeasureGeometry

theorem contDiff_cylinderKernelCoordinates
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) :
    ContDiff ℝ ∞ (cylinderRecoveryCoordinates B c) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let F (x : Point) := B.repr (x - c)
  have hF : ContDiff ℝ ∞ F := B.repr.toContinuousLinearEquiv.contDiff.comp (contDiff_id.sub contDiff_const)
  have hE := e.contDiff.comp hF
  have hZ : ContDiff ℝ ∞ (fun x => (e (F x)).2 0) := by
    change ContDiff ℝ ∞ ((EuclideanSpace.proj (0 : Fin 1) : Domain 1 →L[ℝ] ℝ) ∘ fun x => (e (F x)).2)
    exact (EuclideanSpace.proj (0 : Fin 1)).contDiff.comp hE.snd
  change ContDiff ℝ ∞ (fun x => ((e (F x)).1, (e (F x)).2 0))
  exact hE.fst.prodMk hZ

private abbrev cylinderKernelRadius (B : OrthonormalBasis (Fin 3) ℝ Point) (c x : Point) : ℝ :=
  ‖(cylinderRecoveryCoordinates B c x).1‖

private theorem lipschitz_cylinderKernelRadius (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) :
    LipschitzWith 1 (cylinderKernelRadius B c) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let F (x : Point) := e (B.repr x)
  have hF (x : Point) : ‖(F x).1‖ ≤ ‖x‖ := by
    have h := norm_sq_finAddEquivProd_symm (F x)
    change ‖e.symm (e (B.repr x))‖ ^ 2 = _ at h
    rw [e.symm_apply_apply, B.repr.norm_map] at h
    nlinarith only [h, sq_nonneg ‖(F x).2‖, norm_nonneg (F x).1, norm_nonneg x]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  change |‖(F (x - c)).1‖ - ‖(F (y - c)).1‖| ≤ ‖x - y‖
  refine (abs_norm_sub_norm_le _ _).trans ?_
  have hD : (F (x - c)).1 - (F (y - c)).1 = (F (x - y)).1 := by
    dsimp only [F]
    rw [← Prod.fst_sub, ← map_sub, ← map_sub, sub_sub_sub_cancel_right]
  rw [hD]
  exact hF (x - y)

private def cylinderWallCutoff (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (a δ : PositiveRadius) (x : Point) : ℝ := radialCutoffProfile a δ (cylinderKernelRadius B c x)

private theorem cylinderWallCutoff_contDiff (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (a δ : PositiveRadius) : ContDiff ℝ ∞ (cylinderWallCutoff B c a δ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hB := (contDiff_cylinderKernelCoordinates B c).fst
  by_cases hx : (cylinderRecoveryCoordinates B c x).1 = 0
  · have hConst : ContinuousAt (fun _ : Point => a.val) x := continuousAt_const
    have hSmall : ∀ᶠ y in 𝓝 x, cylinderKernelRadius B c y < a.val :=
      (hB.continuous.norm.continuousAt.eventually_lt hConst)
        (by change ‖(cylinderRecoveryCoordinates B c x).1‖ < a.val; rw [hx, norm_zero]; exact a.property)
    have hEq : (fun _ : Point => (1 : ℝ)) =ᶠ[𝓝 x] cylinderWallCutoff B c a δ :=
      hSmall.mono fun _ hy => (radialCutoffProfile_eq_one a δ hy.le).symm
    exact contDiffAt_const.congr_of_eventuallyEq hEq.symm
  · exact (radialCutoffProfile_contDiff a δ).contDiffAt.comp x (hB.contDiffAt.norm ℝ hx)

private theorem coordinateDerivative_cylinderWallCutoff_le
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (a δ : PositiveRadius)
    {C : ℝ} (hC : 0 ≤ C) (hBound : ∀ r : ℝ, |deriv (radialCutoffProfile a δ) r| ≤ C / δ.val)
    (x : Point) (i : Fin 3) :
    |coordinateDerivative (cylinderWallCutoff B c a δ) (cylinderWallCutoff_contDiff B c a δ) i x| ≤ C / δ.val := by
  let K : ℝ≥0 := ⟨C / δ.val, div_nonneg hC δ.property.le⟩
  have hP : LipschitzWith K (radialCutoffProfile a δ) := by
    apply lipschitzWith_of_nnnorm_deriv_le ((radialCutoffProfile_contDiff a δ).differentiable (by simp))
    intro r
    exact hBound r
  have hLip : LipschitzWith K (cylinderWallCutoff B c a δ) := by
    change LipschitzWith K (radialCutoffProfile a δ ∘ cylinderKernelRadius B c)
    simpa only [mul_one] using hP.comp (lipschitz_cylinderKernelRadius B c)
  unfold coordinateDerivative
  rw [← Real.norm_eq_abs]
  apply ((fderiv ℝ (cylinderWallCutoff B c a δ) x).le_opNorm _).trans
  have hE : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
  rw [hE, mul_one]
  exact norm_fderiv_le_of_lipschitz ℝ hLip

private theorem coordinateDerivative_cylinderWallCutoff_eq_zero
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (a δ : PositiveRadius) {x : Point}
    (hx : cylinderKernelRadius B c x < a.val) (i : Fin 3) :
    coordinateDerivative (cylinderWallCutoff B c a δ) (cylinderWallCutoff_contDiff B c a δ) i x = 0 := by
  have hSmall := (lipschitz_cylinderKernelRadius B c).continuous.continuousAt.eventually_lt continuousAt_const hx
  have hEq : cylinderWallCutoff B c a δ =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) :=
    hSmall.mono fun _ hy => radialCutoffProfile_eq_one a δ hy.le
  simp only [coordinateDerivative, hEq.fderiv_eq, fderiv_fun_const, Pi.zero_apply, zero_apply]

private theorem tendsto_integral_boundedCutoff {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} {f : X → E} (hf : Integrable f μ)
    (χ : ℕ → X → ℝ) (hMeas : ∀ n, Measurable (χ n)) (hB : ∀ n x, χ n x ∈ Icc (0 : ℝ) 1)
    (hEventually : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, χ n x = 1) :
    Tendsto (fun n => ∫ x, χ n x • f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
  · exact Eventually.of_forall fun n => (hMeas n).aestronglyMeasurable.smul hf.aestronglyMeasurable
  · exact Eventually.of_forall fun n => ae_of_all _ fun x => by
      rw [norm_smul, Real.norm_of_nonneg (hB n x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hB n x).2
  · exact hf.norm
  · filter_upwards [hEventually] with x hx
    exact tendsto_const_nhds.congr' (hx.mono fun n hn => by
      change f x = χ n x • f x
      rw [hn, one_smul])

private theorem integral_smul_axial_zeroExtension {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R lo hi : ℝ)
    (φ : Point → ℝ) (w : Point → E) :
    let A := {x : Point | (cylinderRecoveryCoordinates B c x).2 ∈ Ioo lo hi}
    (∫ x in translatedAxisCylinder c (B 2) R (lo - 1) (hi + 1), φ x • A.indicator w x) =
      ∫ x in translatedAxisCylinder c (B 2) R lo hi, φ x • w x := by
  intro A
  have hA : MeasurableSet A := measurableSet_Ioo.preimage (contDiff_cylinderKernelCoordinates B c).continuous.snd.measurable
  have hEq : (fun x => φ x • A.indicator w x) = A.indicator (fun x => φ x • w x) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hSet : A ∩ translatedAxisCylinder c (B 2) R (lo - 1) (hi + 1) = translatedAxisCylinder c (B 2) R lo hi := by
    ext x
    simp only [A, mem_inter_iff, mem_setOf_eq, mem_translatedAxisCylinder_iff_recoveryCoordinates]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · intro h
      exact ⟨h.2, h.1, ⟨by linarith only [h.2.1], by linarith only [h.2.2]⟩⟩
  rw [hEq, integral_indicator hA, Measure.restrict_restrict hA, hSet]

private def axialTestPlateau (lo hi : ℝ) (t : ℝ) :=
  Real.smoothTransition (2 * (t - (lo - 1 / 2))) * Real.smoothTransition (2 * ((hi + 1 / 2) - t))

private theorem axialTestPlateau_contDiff (lo hi : ℝ) : ContDiff ℝ ∞ (axialTestPlateau lo hi) := by
  unfold axialTestPlateau
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

private theorem axialTestPlateau_eq_one {lo hi t : ℝ} (ht : t ∈ Icc lo hi) : axialTestPlateau lo hi t = 1 := by
  unfold axialTestPlateau
  rw [Real.smoothTransition.one_of_one_le (by linarith only [ht.1]),
    Real.smoothTransition.one_of_one_le (by linarith only [ht.2]), mul_one]

private theorem axialTestPlateau_eq_zero {lo hi t : ℝ} (ht : t ∉ Icc (lo - 1 / 2) (hi + 1 / 2)) :
    axialTestPlateau lo hi t = 0 := by
  change ¬(lo - 1 / 2 ≤ t ∧ t ≤ hi + 1 / 2) at ht
  unfold axialTestPlateau
  rcases not_and_or.mp ht with h | h
  · have hL : 2 * (t - (lo - 1 / 2)) ≤ 0 := by linarith only [lt_of_not_ge h]
    rw [Real.smoothTransition.zero_of_nonpos hL, zero_mul]
  · have hR : 2 * ((hi + 1 / 2) - t) ≤ 0 := by linarith only [lt_of_not_ge h]
    rw [Real.smoothTransition.zero_of_nonpos hR, mul_zero]

private theorem cylinderWallCutoff_test_admissible
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R lo hi : ℝ)
    (a δ : PositiveRadius) (hInside : a.val + δ.val < R) {φ : Point → ℝ}
    (hComp : HasCompactSupport φ) :
    let ψ (x : Point) := (φ x * cylinderWallCutoff B c a δ x) *
      axialTestPlateau lo hi (cylinderRecoveryCoordinates B c x).2
    HasCompactSupport ψ ∧ tsupport ψ ⊆ translatedAxisCylinder c (B 2) R (lo - 1) (hi + 1) := by
  intro ψ
  refine ⟨(hComp.mul_right).mul_right, ?_⟩
  let K := {x : Point | (cylinderRecoveryCoordinates B c x).2 ∈ Icc (lo - 1 / 2) (hi + 1 / 2) ∧
    cylinderKernelRadius B c x ≤ a.val + δ.val}
  have hC := (contDiff_cylinderKernelCoordinates B c).continuous
  have hK : IsClosed K := (isClosed_Icc.preimage hC.snd).inter (isClosed_le hC.fst.norm continuous_const)
  have hSupport : Function.support ψ ⊆ K := by
    intro x hx
    by_contra hn
    apply hx
    change ¬((cylinderRecoveryCoordinates B c x).2 ∈ Icc (lo - 1 / 2) (hi + 1 / 2) ∧
      cylinderKernelRadius B c x ≤ a.val + δ.val) at hn
    dsimp only [ψ]
    rcases not_and_or.mp hn with h | h
    · rw [axialTestPlateau_eq_zero h, mul_zero]
    · rw [cylinderWallCutoff, radialCutoffProfile_eq_zero a δ (le_of_lt (lt_of_not_ge h)), mul_zero, zero_mul]
  apply (closure_minimal hSupport hK).trans
  intro x hx
  refine (mem_translatedAxisCylinder_iff_recoveryCoordinates B c R (lo - 1) (hi + 1) x).2 ⟨?_, ?_⟩
  · exact mem_ball_zero_iff.2 (hx.2.trans_lt hInside)
  · exact ⟨by linarith only [hx.1.1], by linarith only [hx.1.2]⟩

private theorem cylinder_weak_identity_with_wallCutoff {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R lo hi : ℝ)
    (w : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q)
    (hw : let A := {x : Point | (cylinderRecoveryCoordinates B c x).2 ∈ Ioo lo hi}
      MemW12 (translatedAxisCylinderDomain B c R (lo - 1) (hi + 1)) (A.indicator w) (A.indicator D))
    (a δ : PositiveRadius) (hInside : a.val + δ.val < R) {φ : Point → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hComp : HasCompactSupport φ) (i : Fin 3) :
    let U := translatedAxisCylinder c (B 2) R lo hi
    let χ := cylinderWallCutoff B c a δ
    let hχ := cylinderWallCutoff_contDiff B c a δ
    (∫ x in U, (coordinateDerivative φ hφ i x * χ x + φ x * coordinateDerivative χ hχ i x) • w x) =
      -(∫ x in U, (φ x * χ x) • D x i) := by
  intro U χ hχ
  let A := {x : Point | (cylinderRecoveryCoordinates B c x).2 ∈ Ioo lo hi}
  let ψ₀ (x : Point) := φ x * χ x
  let ψ (x : Point) := ψ₀ x * axialTestPlateau lo hi (cylinderRecoveryCoordinates B c x).2
  have hψ₀ : ContDiff ℝ ∞ ψ₀ := hφ.mul hχ
  have hψ : ContDiff ℝ ∞ ψ := hψ₀.mul ((axialTestPlateau_contDiff lo hi).comp
    (contDiff_cylinderKernelCoordinates B c).snd)
  obtain ⟨hψC, hψS⟩ := cylinderWallCutoff_test_admissible B c R lo hi a δ hInside hComp
  have hEq : EqOn ψ ψ₀ U := by
    intro x hx
    have hx' := (mem_translatedAxisCylinder_iff_recoveryCoordinates B c R lo hi x).1 hx
    change ψ₀ x * axialTestPlateau lo hi (cylinderRecoveryCoordinates B c x).2 = ψ₀ x
    rw [axialTestPlateau_eq_one (Ioo_subset_Icc_self hx'.2), mul_one]
  have hTest := hw.1.2.2 i ψ hψ hψC hψS
  change (∫ x in translatedAxisCylinder c (B 2) R (lo - 1) (hi + 1),
      coordinateDerivative ψ hψ i x • A.indicator w x) =
    -(∫ x in translatedAxisCylinder c (B 2) R (lo - 1) (hi + 1), ψ x • (A.indicator D x) i) at hTest
  have hCols (x : Point) : A.indicator D x i = A.indicator (fun y => D y i) x := by
    by_cases hx : x ∈ A <;> simp [hx]
  have hL : (∫ x in translatedAxisCylinder c (B 2) R (lo - 1) (hi + 1),
      coordinateDerivative ψ hψ i x • A.indicator w x) = ∫ x in U, coordinateDerivative ψ hψ i x • w x :=
    integral_smul_axial_zeroExtension B c R lo hi (coordinateDerivative ψ hψ i) w
  have hR : (∫ x in translatedAxisCylinder c (B 2) R (lo - 1) (hi + 1), ψ x • (A.indicator D x) i) =
      ∫ x in U, ψ x • D x i := by
    calc
      _ = ∫ x in translatedAxisCylinder c (B 2) R (lo - 1) (hi + 1),
          ψ x • A.indicator (fun y => D y i) x := integral_congr_ae
        (Eventually.of_forall fun x => congrArg (fun y : Ambient q => ψ x • y) (hCols x))
      _ = _ := integral_smul_axial_zeroExtension B c R lo hi ψ (fun x => D x i)
  rw [hL, hR] at hTest
  have hDeriv : ∀ x ∈ U, coordinateDerivative ψ hψ i x = coordinateDerivative ψ₀ hψ₀ i x := by
    intro x hx
    have hEqNear : ψ =ᶠ[𝓝 x] ψ₀ := Filter.mem_of_superset
      ((isOpen_translatedAxisCylinder _ _ _ _ _).mem_nhds hx) hEq
    change fderiv ℝ ψ x (EuclideanSpace.single i 1) = fderiv ℝ ψ₀ x (EuclideanSpace.single i 1)
    rw [hEqNear.fderiv_eq]
  have hU : MeasurableSet U := (isOpen_translatedAxisCylinder _ _ _ _ _).measurableSet
  calc
    _ = ∫ x in U, coordinateDerivative ψ hψ i x • w x := by
      apply setIntegral_congr_fun hU
      intro x hx
      change (coordinateDerivative φ hφ i x * χ x + φ x * coordinateDerivative χ hχ i x) • w x =
        coordinateDerivative ψ hψ i x • w x
      rw [hDeriv x hx]
      exact congrArg (fun r : ℝ => r • w x) (coordinateDerivative_mul hφ hχ i x).symm
    _ = -(∫ x in U, ψ x • D x i) := hTest
    _ = _ := by
      congr 1
      exact setIntegral_congr_fun hU (fun x hx => congrArg (fun r : ℝ => r • D x i) (hEq hx))

private theorem norm_wallCutoff_commutator_le {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R lo hi : ℝ)
    (w : Point → Ambient q) (a δ : PositiveRadius) (r : ℝ) (hr : r < a.val)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hBound : ∀ s : ℝ, |deriv (radialCutoffProfile a δ) s| ≤ C / δ.val)
    {φ : Point → ℝ} (hφ : Continuous φ) (hφM : ∀ x, |φ x| ≤ M) (i : Fin 3) :
    let U := translatedAxisCylinder c (B 2) R lo hi
    let χ := cylinderWallCutoff B c a δ
    let hχ := cylinderWallCutoff_contDiff B c a δ
    IntegrableOn w U →
    ‖∫ x in U, φ x • (coordinateDerivative χ hχ i x • w x)‖ ≤
      (M * (C / δ.val)) * ∫ x in translatedAxisCylinderWallCollar B c r R lo hi, ‖w x‖ := by
  intro U χ hχ hw
  let C₀ := translatedAxisCylinderWallCollar B c r R lo hi
  let f (x : Point) := φ x • (coordinateDerivative χ hχ i x • w x)
  let g (x : Point) := M * (C / δ.val) * C₀.indicator (fun y => ‖w y‖) x
  let μ := (volume : Measure Point).restrict U
  have hU : MeasurableSet U := (isOpen_translatedAxisCylinder _ _ _ _ _).measurableSet
  have hC₀ : MeasurableSet C₀ := hU.inter (measurableSet_Ioi.preimage
    (lipschitz_cylinderKernelRadius B c).continuous.measurable)
  have hg : Integrable g μ := (hw.norm.indicator hC₀).const_mul _
  have hMeas : AEStronglyMeasurable f μ := hφ.aestronglyMeasurable.smul
    (((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.smul hw.aestronglyMeasurable)
  have hB : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x := by
    filter_upwards [ae_restrict_mem hU] with x hx
    by_cases hxC : x ∈ C₀
    · dsimp only [f, g]
      rw [indicator_of_mem hxC, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hφM x)
        (coordinateDerivative_cylinderWallCutoff_le B c a δ hC hBound x i) (abs_nonneg _) hM) (norm_nonneg _)
    · have hxR : cylinderKernelRadius B c x ≤ r := le_of_not_gt (fun h => hxC ⟨hx, h⟩)
      have hZ : coordinateDerivative χ hχ i x = 0 :=
        coordinateDerivative_cylinderWallCutoff_eq_zero B c a δ (hxR.trans_lt hr) i
      dsimp only [f, g]
      rw [hZ, zero_smul, smul_zero, norm_zero, indicator_of_notMem hxC, mul_zero]
  have hf : Integrable f μ := hg.mono' hMeas hB
  refine (norm_integral_le_integral_norm f).trans ((integral_mono_ae hf.norm hg hB).trans_eq ?_)
  change (∫ x, M * (C / δ.val) * C₀.indicator (fun y => ‖w y‖) x ∂μ) = _
  rw [integral_const_mul, integral_indicator hC₀, Measure.restrict_restrict hC₀,
    inter_eq_left.mpr (show C₀ ⊆ U from inter_subset_left)]

private def cylinderBoundaryWidth (R : PositiveRadius) (n : ℕ) : PositiveRadius :=
  ⟨R.val / ((n : ℝ) + 4), div_pos R.property (by positivity)⟩

private theorem cylinderBoundaryWidth_le (R : PositiveRadius) (n : ℕ) :
    (cylinderBoundaryWidth R n).val ≤ R.val / 4 := by
  change R.val / ((n : ℝ) + 4) ≤ R.val / 4
  have hNat : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  exact div_le_div_of_nonneg_left R.property.le (by norm_num : (0 : ℝ) < 4) (by linarith only [hNat])

private theorem tendsto_cylinderBoundaryWidth (R : PositiveRadius) :
    Tendsto (fun n : ℕ => (cylinderBoundaryWidth R n).val) atTop (𝓝 0) := by
  have h := (tendsto_add_atTop_iff_nat 3).2 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h' := h.const_mul R.val
  simpa [cylinderBoundaryWidth, Nat.cast_add, add_assoc, div_eq_mul_inv,
    show (3 : ℝ) + 1 = 4 by norm_num] using h'

private def cylinderBoundaryInnerLevel (R : PositiveRadius) (n : ℕ) : PositiveRadius :=
  ⟨R.val - 2 * (cylinderBoundaryWidth R n).val,
    by linarith only [cylinderBoundaryWidth_le R n, R.property]⟩

private theorem cylinderBoundaryInnerLevel_mem (R : PositiveRadius) (n : ℕ) :
    (cylinderBoundaryInnerLevel R n).val + (cylinderBoundaryWidth R n).val < R.val := by
  change R.val - 2 * (cylinderBoundaryWidth R n).val + (cylinderBoundaryWidth R n).val < R.val
  linarith only [(cylinderBoundaryWidth R n).property]

private theorem tendsto_wallCutoff_commutator {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R : PositiveRadius) (lo hi : ℝ)
    (w : Point → Ambient q) (hw : IntegrableOn w (translatedAxisCylinder c (B 2) R.val lo hi))
    (hLayer : ∀ ε > (0 : ℝ), ∃ a ∈ Ico (R.val / 2) R.val, ∀ r ∈ Ico a R.val,
      (∫ x in translatedAxisCylinderWallCollar B c r R.val lo hi, ‖w x‖) ≤ ε * (R.val - r))
    {φ : Point → ℝ} (hφ : Continuous φ) (hComp : HasCompactSupport φ) (i : Fin 3) :
    let χ (n : ℕ) := cylinderWallCutoff B c (cylinderBoundaryInnerLevel R n) (cylinderBoundaryWidth R n)
    let hχ (n : ℕ) := cylinderWallCutoff_contDiff B c (cylinderBoundaryInnerLevel R n) (cylinderBoundaryWidth R n)
    Tendsto (fun n => ∫ x in translatedAxisCylinder c (B 2) R.val lo hi,
      φ x • (coordinateDerivative (χ n) (hχ n) i x • w x)) atTop (𝓝 0) := by
  intro χ hχ
  obtain ⟨M', hM'⟩ := hComp.exists_bound_of_continuousOn hφ.continuousOn
  let M := max M' 0
  have hM : 0 ≤ M := le_max_right _ _
  have hBound (x : Point) : |φ x| ≤ M := by
    by_cases hx : x ∈ tsupport φ
    · exact ((Real.norm_eq_abs (φ x)).symm ▸ hM' x hx).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
      exact hM
  obtain ⟨C, hC, hC'⟩ := radialCutoffProfile_deriv_bound
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (3 * M * C + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨a, ha, haBound⟩ := hLayer η hη
  have hδ := (tendsto_cylinderBoundaryWidth R).eventually_lt_const
    (by linarith only [ha.2] : 0 < (R.val - a) / 3)
  filter_upwards [hδ] with n hn
  let δ := cylinderBoundaryWidth R n
  let r := R.val - 3 * δ.val
  have hr : r ∈ Ico a R.val := by
    change a ≤ R.val - 3 * δ.val ∧ R.val - 3 * δ.val < R.val
    have hD : δ.val < (R.val - a) / 3 := hn
    exact ⟨by linarith only [hD], by linarith only [δ.property]⟩
  have hInner : r < (cylinderBoundaryInnerLevel R n).val := by
    change R.val - 3 * δ.val < R.val - 2 * δ.val
    linarith only [δ.property]
  have h := norm_wallCutoff_commutator_le B c R.val lo hi w (cylinderBoundaryInnerLevel R n) δ r hInner
    hC hM (hC' _ _) hφ hBound i hw
  have h₀ : 0 ≤ M * (C / δ.val) := mul_nonneg hM (div_nonneg hC δ.property.le)
  rw [dist_zero_right]
  refine h.trans_lt ((mul_le_mul_of_nonneg_left (haBound r hr) h₀).trans_lt ?_)
  have hR : R.val - r = 3 * δ.val := by dsimp only [r]; ring
  rw [hR]
  have hScale : M * (C / δ.val) * (η * (3 * δ.val)) = (3 * M * C) * η := by
    field_simp [δ.property.ne']
  rw [hScale]
  dsimp only [η]
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 3 * M * C + 1)]
  nlinarith only [hε]

private theorem integral_smul_zeroExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {U : Set Point} (hU : MeasurableSet U) (φ : Point → ℝ) (w : Point → E) :
    (∫ x, φ x • U.indicator w x) = ∫ x in U, φ x • w x := by
  have hEq : (fun x => φ x • U.indicator w x) = U.indicator (fun x => φ x • w x) := by
    funext x
    by_cases hx : x ∈ U <;> simp [hx]
  rw [hEq, integral_indicator hU]

/-- Zero horizontal and lateral classes give the literal global weak
Sobolev graph obtained by extending the map and every column by zero. -/
theorem memW12_cylinder_zeroExtend {n q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hR : 0 < R) (hI : lo < hi)
    (w : Point → Ambient q) (D : Point → HarmonicMaps.Gradient 3 q)
    (hw : MemW12 (translatedAxisCylinderDomain B c R lo hi) w D)
    (P : CylinderHeightL2Trace q R lo hi) (hP : RepresentsCylinderHeightL2Trace B c w P)
    (hLo : P ⟨lo, le_rfl, hI.le⟩ = 0) (hHi : P ⟨hi, hI.le, le_rfl⟩ = 0)
    (l h : Fin n → ℝ) (hSub : ∀ i, Ioo (l i) (h i) ⊆ Ioo lo hi)
    (hCover : ∀ᵐ z : ℝ ∂volume.restrict (Ioo lo hi), ∃ i, z ∈ Ioo (l i) (h i))
    (T : ∀ i : Fin n, CylinderSideL2Trace q R (l i) (h i))
    (hT : ∀ i, RepresentsCylinderSideL2Trace B c w (T i))
    (hZero : ∀ i, T i ⟨R, half_le_self hR.le, le_rfl⟩ = 0) :
    let U := translatedAxisCylinder c (B 2) R lo hi
    MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain 3) (U.indicator w) (U.indicator D) := by
  intro U
  have hU : IsOpen U := isOpen_translatedAxisCylinder _ _ _ _ _
  let μ := (volume : Measure Point).restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top (isCompact_translatedClosedAxisCylinder (B.orthonormal.norm_eq_one 2) R lo hi).measure_lt_top.ne
      (measure_mono (translatedAxisCylinder_subset_closed _ _ _ _ _)))
  let Z := U.indicator w
  let E := U.indicator D
  have hZE (i : Fin 3) : (fun x => E x i) = U.indicator (fun x => D x i) := by
    funext x
    by_cases hx : x ∈ U <;> simp [E, hx]
  have hZ : MemLp Z 2 volume := memLp_zeroExtension hU.measurableSet hw.2.1
  have hE (i : Fin 3) : MemLp (fun x => E x i) 2 volume := by
    rw [hZE]
    exact memLp_zeroExtension hU.measurableSet (hw.2.2 i)
  have hAxial := memW12_cylinder_axial_zeroExtend B c R hI w D hw P hP hLo hHi
  have hLayer := fun ε hε => integral_norm_wallCollar_le_of_zeroTrace_cover B c hR w hw.2.1
    l h hSub hCover T hT hZero (ε := ε) hε
  have hWLp : MemLp w 2 μ := hw.2.1
  have hDLp (i : Fin 3) : MemLp (fun x => D x i) 2 μ := hw.2.2 i
  have hWI : Integrable w μ := hWLp.integrable (by norm_num)
  have hDI (i : Fin 3) : Integrable (fun x => D x i) μ := (hDLp i).integrable (by norm_num)
  refine ⟨⟨(hZ.locallyIntegrable (by norm_num)).locallyIntegrableOn univ,
    fun i => ((hE i).locallyIntegrable (by norm_num)).locallyIntegrableOn univ, ?_⟩,
    by simpa only [Measure.restrict_univ] using hZ,
    fun i => by simpa only [Measure.restrict_univ] using hE i⟩
  intro i φ hφ hComp _
  let r : PositiveRadius := ⟨R, hR⟩
  let χ (n : ℕ) := cylinderWallCutoff B c (cylinderBoundaryInnerLevel r n) (cylinderBoundaryWidth r n)
  let hχ (n : ℕ) := cylinderWallCutoff_contDiff B c (cylinderBoundaryInnerLevel r n) (cylinderBoundaryWidth r n)
  let f (x : Point) := coordinateDerivative φ hφ i x • w x
  let g (x : Point) := φ x • D x i
  let b (n : ℕ) (x : Point) := φ x • (coordinateDerivative (χ n) (hχ n) i x • w x)
  have hφL : MemLp φ ⊤ μ := hφ.continuous.memLp_top_of_hasCompactSupport hComp _
  have hdf : MemLp (coordinateDerivative φ hφ i) ⊤ μ :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hComp.fderiv_apply ℝ (EuclideanSpace.single i 1)) _
  have hf : Integrable f μ := hWI.smul_of_top_right hdf
  have hg : Integrable g μ := (hDI i).smul_of_top_right hφL
  have hχB (n : ℕ) (x : Point) : χ n x ∈ Icc (0 : ℝ) 1 := radialCutoffProfile_mem_Icc _ _ _
  have hNear : ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, χ n x = 1 := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    have hxR : cylinderKernelRadius B c x < R := mem_ball_zero_iff.mp
      ((mem_translatedAxisCylinder_iff_recoveryCoordinates B c R lo hi x).1 hx).1
    have hδ := (tendsto_cylinderBoundaryWidth r).eventually_lt_const (half_pos (sub_pos.mpr hxR))
    filter_upwards [hδ] with n hn
    apply radialCutoffProfile_eq_one
    change cylinderKernelRadius B c x ≤ R - 2 * (cylinderBoundaryWidth r n).val
    linarith only [hn]
  have hχL (n : ℕ) : MemLp (χ n) ⊤ μ := memLp_top_of_bound (hχ n).continuous.aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (hχB n x).1]; exact (hχB n x).2)
  obtain ⟨C, hC, hCD⟩ := radialCutoffProfile_deriv_bound
  have hb (n : ℕ) : Integrable (b n) μ := by
    have hDer : MemLp (coordinateDerivative (χ n) (hχ n) i) ⊤ μ := by
      apply memLp_top_of_bound (((hχ n).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
        (C / (cylinderBoundaryWidth r n).val)
      refine ae_of_all _ fun x => ?_
      rw [Real.norm_eq_abs]
      exact coordinateDerivative_cylinderWallCutoff_le B c (cylinderBoundaryInnerLevel r n)
        (cylinderBoundaryWidth r n) hC (hCD _ _) x i
    exact (hWI.smul_of_top_right hDer).smul_of_top_right hφL
  have hIdentity (n : ℕ) : (∫ x, χ n x • f x ∂μ) + (∫ x, b n x ∂μ) = -(∫ x, χ n x • g x ∂μ) := by
    have h := cylinder_weak_identity_with_wallCutoff B c R lo hi w D hAxial (cylinderBoundaryInnerLevel r n)
      (cylinderBoundaryWidth r n) (cylinderBoundaryInnerLevel_mem r n) hφ hComp i
    have hL (x : Point) :
        (coordinateDerivative φ hφ i x * χ n x + φ x * coordinateDerivative (χ n) (hχ n) i x) • w x =
          χ n x • f x + b n x := by
      dsimp only [f, b]
      rw [add_smul, mul_smul, mul_smul, smul_comm (coordinateDerivative φ hφ i x) (χ n x)]
    have hR' (x : Point) : (φ x * χ n x) • D x i = χ n x • g x := by
      dsimp only [g]
      rw [mul_smul, smul_comm (φ x) (χ n x)]
    change (∫ x, (coordinateDerivative φ hφ i x * χ n x + φ x * coordinateDerivative (χ n) (hχ n) i x) • w x ∂μ) =
      -(∫ x, (φ x * χ n x) • D x i ∂μ) at h
    have hSum : (∫ x, χ n x • f x + b n x ∂μ) = (∫ x, χ n x • f x ∂μ) + ∫ x, b n x ∂μ :=
      integral_add (hf.smul_of_top_right (hχL n)) (hb n)
    simp_rw [hL, hR'] at h
    rw [hSum] at h
    exact h
  have hLeft := tendsto_integral_boundedCutoff hf χ (fun n => (hχ n).continuous.measurable) hχB hNear
  have hRight := (tendsto_integral_boundedCutoff hg χ (fun n => (hχ n).continuous.measurable) hχB hNear).neg
  have hComm := tendsto_wallCutoff_commutator B c r lo hi w hWI hLayer hφ.continuous hComp i
  have hLimit := hLeft.add hComm
  rw [add_zero] at hLimit
  have hTest := tendsto_nhds_unique hLimit (hRight.congr' (Eventually.of_forall fun n => (hIdentity n).symm))
  simp only [Measure.restrict_univ]
  change (∫ x, coordinateDerivative φ hφ i x • U.indicator w x) = -(∫ x, φ x • E x i)
  have hEnd : (∫ x, φ x • E x i) = ∫ x in U, φ x • D x i := by
    calc
      _ = ∫ x, φ x • U.indicator (fun y => D y i) x := integral_congr_ae
        (Eventually.of_forall fun x => congrArg (fun z : Ambient q => φ x • z) (congrFun (hZE i) x))
      _ = _ := integral_smul_zeroExtension hU.measurableSet φ (fun x => D x i)
  rw [integral_smul_zeroExtension hU.measurableSet, hEnd]
  exact hTest

end Thesis.MeasureGeometry

end
