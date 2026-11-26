module

public import Thesis.Variational.FlatWallLpTransport
public import Thesis.Variational.OddWallHessianEstimate

/-! Absorption of the Hessian error in small-slope boundary coordinates. -/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace Thesis

private theorem eLpNorm_le_of_const_add_mul {μ : Measure Point} {p : ℝ}
    (hp : 1 ≤ p) {f g : Point → ℝ} (hg : AEStronglyMeasurable g μ)
    {A d : ℝ} (hA : 0 ≤ A) (hd : 0 ≤ d)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ A + d * g x) :
    eLpNorm f (ENNReal.ofReal p) μ ≤
      μ univ ^ p⁻¹ * ENNReal.ofReal A + ENNReal.ofReal d * eLpNorm g (ENNReal.ofReal p) μ := by
  let q := ENNReal.ofReal p
  have hq : 1 ≤ q := by simpa only [q,ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  calc
    _ ≤ eLpNorm ((fun _ => A) + d • g) q μ := eLpNorm_mono_ae_real h
    _ ≤ eLpNorm (fun _ => A) q μ + eLpNorm (d • g) q μ :=
      eLpNorm_add_le aestronglyMeasurable_const (hg.const_smul d) hq
    _ ≤ _ := by
      rw [eLpNorm_const_smul]
      simp only [← ofReal_norm,Real.norm_of_nonneg hd]
      refine add_le_add ?_ le_rfl
      simpa only [q,ENNReal.toReal_ofReal (zero_le_one.trans hp),Real.norm_of_nonneg hA] using
        (eLpNorm_le_of_ae_bound (p := q) (μ := μ) (f := fun _ : Point => A)
          (Eventually.of_forall fun _ => (Real.norm_of_nonneg hA).le))

private theorem ennreal_absorb_linear {A : ℝ≥0∞} (hA : A ≠ ⊤)
    {W d B : ℝ} (hW : 0 ≤ W) (hd : 0 ≤ d) (hB : 0 ≤ B) (hsmall : W*d ≤ 1/2)
    (h : A ≤ ENNReal.ofReal W * (ENNReal.ofReal B + ENNReal.ofReal d * A)) :
    A ≤ ENNReal.ofReal (2*W*B) := by
  have hFinMul : ENNReal.ofReal d * A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA
  have hFin : ENNReal.ofReal W * (ENNReal.ofReal B + ENNReal.ofReal d * A) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,hFinMul⟩)
  have hR := ENNReal.toReal_mono hFin h
  rw [ENNReal.toReal_mul,ENNReal.toReal_add ENNReal.ofReal_ne_top hFinMul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hW,ENNReal.toReal_ofReal hB,ENNReal.toReal_ofReal hd] at hR
  apply (ENNReal.toReal_le_toReal hA ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*W*B)]
  have hR' := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ A.toReal from ENNReal.toReal_nonneg)
  nlinarith only [hR,hR']

private theorem laplacian_support_subset (f : Point → ℝ) :
    Function.support (laplacian f) ⊆ tsupport f := by
  intro x hx
  by_contra h
  apply hx
  rw [laplacian_eventuallyEq_eq (notMem_tsupport_iff_eventuallyEq.1 h)]
  have hZero (i : Fin 3) : coordDeriv i (0 : Point → ℝ) = 0 := by
    funext y
    simp [coordDeriv,fderiv_zero]
  simp only [laplacian,hZero,Pi.zero_apply,Finset.sum_const_zero]

private theorem contDiffAt_two_of_in_open_closure {U : Set Point} (hU : IsOpen U)
    {f : Point → ℝ} (hf : ContDiffOn ℝ 2 f (closure U)) {x : Point} (hx : x ∈ U) :
    ContDiffAt ℝ 2 f x :=
  (hf x (subset_closure hx)).contDiffAt (mem_of_superset (hU.mem_nhds hx) subset_closure)

/-- The Hessian of a classical zero-wall field supported in a small-slope
patch is bounded on the physical neighborhood in terms of its force and first
derivative bounds. -/
theorem RegularWallGraphPatch.exists_localHessian_bound_of_small_slope
    {U : Set Point} (hU : IsSmoothDomain U) (P : RegularWallGraphPatch U)
    (hP : ContDiff ℝ 2 P.height) {p W η : ℝ} (hp : 1 < p) (hW : 0 < W)
    (hHalf : ∀ (f : Point → ℝ), ContDiffOn ℝ 2 f closedWallHalf → EqOn f 0 flatWall →
      HasCompactSupport f →
      eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 f x‖) (ENNReal.ofReal p) (volume.restrict positiveWallHalf) ≤
        ENNReal.ofReal W * eLpNorm (laplacian f) (ENNReal.ofReal p) (volume.restrict positiveWallHalf))
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hSmall : W*(9*η) ≤ 1/2)
    (hSlope : ∀ y ∈ P.base, ‖fderiv ℝ P.height y‖ ≤ η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : Point → ℝ}, ContDiffOn ℝ 2 f (closure U) →
      EqOn f 0 (frontier U) → HasCompactSupport f → tsupport f ⊆ P.neighborhood →
      ∀ {F G : ℝ}, 0 ≤ F → 0 ≤ G →
      (∀ x ∈ U, ‖laplacian f x‖ ≤ F) → (∀ x ∈ U, ‖fderiv ℝ f x‖ ≤ G) →
      eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 f x‖) (ENNReal.ofReal p)
        (volume.restrict (U ∩ P.neighborhood)) ≤ ENNReal.ofReal (C*(F+G)) := by
  let S := P.flatPositiveBox
  let μ := (volume : Measure Point).restrict S
  let q := ENNReal.ofReal p
  have hS : IsOpen S := P.flatPositiveBox_isOpen
  have hμ : μ univ ≠ ⊤ := by
    rw [show μ univ = volume S by simp [μ]]
    exact ((measure_mono (show S ⊆ closure P.flatBox from
      fun _ hx => subset_closure hx.1)).trans_lt P.isCompact_closure_flatBox.measure_lt_top).ne
  let Q := (μ univ ^ p⁻¹).toReal
  have hQ : 0 ≤ Q := ENNReal.toReal_nonneg
  have hQeq : ENNReal.ofReal Q = μ univ ^ p⁻¹ :=
    ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg (by positivity) hμ)
  obtain ⟨H,hH,hCompare⟩ := P.exists_flatWall_poisson_comparison hP hη hη₁ hSlope
  obtain ⟨D,hD,hDer⟩ := P.exists_forward_derivative_bound hP
  let C := Q * (8*W*(1+3*H*D)+H*D)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro f hf h0 hc hs F G hF hG hLap hGrad
  let v := f ∘ P.flatChart
  let g (x : Point) := ‖iteratedFDeriv ℝ 2 v x‖
  let A := eLpNorm g q μ
  let B := eLpNorm (laplacian v) q μ
  have hv : ContDiffOn ℝ 2 v closedWallHalf := P.contDiffOn_two_flat_pullback hU.1.1 hP hf hs
  have hv0 : EqOn v 0 flatWall := P.flat_pullback_wall_zero hU.1.1 h0 hs
  have hvC : HasCompactSupport v := P.flat_pullback_hasCompactSupport hc
  have hvs : tsupport v ⊆ P.flatBox := P.flat_pullback_tsupport_subset hs
  have hvS : ContDiffOn ℝ 2 v S := hv.mono fun z hz => (show 0 < z 2 from hz.2).le
  have hgm : AEStronglyMeasurable g μ := by
    have hC : ContinuousOn (iteratedFDeriv ℝ 2 v) S :=
      (hvS.continuousOn_iteratedFDerivWithin (m := 2) le_rfl hS.uniqueDiffOn).congr
        fun _ hx => (iteratedFDerivWithin_of_isOpen (f := v) 2 hS hx).symm
    exact hC.norm.aestronglyMeasurable hS.measurableSet
  have hA : A ≠ ⊤ := by
    obtain ⟨K,hK,hBound⟩ := P.iteratedFDeriv_two_flat_pullback_bounded hv
    have he : ∀ᵐ x ∂μ, ‖g x‖ ≤ K := by
      filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
      exact (Real.norm_of_nonneg (norm_nonneg _)).trans_le (hBound x hx)
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top)
      (eLpNorm_le_of_ae_bound he)
    rw [ENNReal.toReal_ofReal (zero_lt_one.trans hp).le]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hμ
  have hgSupport : Function.support g ⊆ P.flatBox :=
    fun x hx => hvs (support_iteratedFDeriv_subset 2 (show iteratedFDeriv ℝ 2 v x ≠ 0 from
      fun h => hx (by simp [g,h])))
  have hRest (k : Point → ℝ) (hk : Function.support k ⊆ P.flatBox) :
      eLpNorm k q μ = eLpNorm k q (volume.restrict positiveWallHalf) := by
    rw [show μ = (volume.restrict positiveWallHalf).restrict P.flatBox by
      rw [Measure.restrict_restrict P.flatBox_isOpen.measurableSet]
      rfl]
    exact eLpNorm_restrict_eq_of_support_subset hk
  have hMain : A ≤ ENNReal.ofReal W * B := by
    change eLpNorm g q μ ≤ ENNReal.ofReal W * eLpNorm (laplacian v) q μ
    rw [hRest g hgSupport,hRest (laplacian v) ((laplacian_support_subset v).trans hvs)]
    exact hHalf v hv hv0 hvC
  have hPoint (z : Point) (hz : z ∈ S) :
      ‖laplacian v z‖ ≤ (F+3*H*D*G) + (9*η)*g z ∧
      ‖iteratedFDeriv ℝ 2 f (P.flatChart z)‖ ≤ H*D*G + 4*g z := by
    have hx : P.flatChart z ∈ U := (P.flatChart_mem_domain hz.1).2 hz.2
    have hfx := contDiffAt_two_of_in_open_closure hU.1.1 hf hx
    have hComp := hCompare f z hz.1 hfx
    have hVg : ‖fderiv ℝ v z‖ ≤ D*G := by
      rw [show fderiv ℝ v z = (fderiv ℝ f (P.flatChart z)).comp (fderiv ℝ P.flatChart z) from
        fderiv_comp z (hfx.differentiableAt two_ne_zero)
          ((P.flatChart_contDiff_two hP).differentiable two_ne_zero z)]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul (hGrad _ hx) (hDer _ hz.1) (norm_nonneg _) hG).trans_eq (mul_comm _ _))
    constructor
    · have hT := (norm_add_le (laplacian v z - laplacian f (P.flatChart z)) (laplacian f (P.flatChart z)))
      rw [sub_add_cancel] at hT
      refine hT.trans ((add_le_add hComp.1 (hLap _ hx)).trans ?_)
      have hD' := mul_le_mul_of_nonneg_left hVg (by positivity : 0 ≤ 3*H)
      dsimp only [g]
      nlinarith only [hD']
    · refine hComp.2.1.trans ?_
      have hD' := mul_le_mul_of_nonneg_left hVg hH
      dsimp only [g]
      nlinarith only [hD']
  have hSource : B ≤ ENNReal.ofReal (Q*(F+3*H*D*G)) + ENNReal.ofReal (9*η)*A := by
    have hL := eLpNorm_le_of_const_add_mul hp.le hgm (by positivity : 0 ≤ F+3*H*D*G)
      (by positivity : 0 ≤ 9*η)
      ((ae_restrict_mem hS.measurableSet).mono fun z hz => (hPoint z hz).1)
    rw [← hQeq, ← ENNReal.ofReal_mul hQ] at hL
    exact hL
  have hAbs := ennreal_absorb_linear hA hW.le (by positivity : 0 ≤ 9*η)
    (by positivity : 0 ≤ Q*(F+3*H*D*G)) hSmall (hMain.trans (mul_le_mul_right hSource _))
  let fb (x : Point) := ‖iteratedFDeriv ℝ 2 f x‖
  have hUO := hU.1.1.inter P.isOpen_neighborhood
  have hfb : AEStronglyMeasurable fb (volume.restrict (U ∩ P.neighborhood)) := by
    have hfO : ContDiffOn ℝ 2 f (U ∩ P.neighborhood) := hf.mono (inter_subset_left.trans subset_closure)
    have hC := hfO.continuousOn_iteratedFDerivWithin (m := 2) le_rfl hUO.uniqueDiffOn
    have hNormC : ContinuousOn fb (U ∩ P.neighborhood) :=
      (hC.congr fun _ hx => (iteratedFDerivWithin_of_isOpen (f := f) 2 hUO hx).symm).norm
    exact hNormC.aestronglyMeasurable hUO.measurableSet
  change eLpNorm fb q (volume.restrict (U ∩ P.neighborhood)) ≤ _
  rw [← eLpNorm_comp_measurePreserving hfb (P.flatPositiveBox_volume hU.1.1)]
  have hL := eLpNorm_le_of_const_add_mul (f := fb ∘ P.flatChart) hp.le hgm (by positivity : 0 ≤ H*D*G)
    (by norm_num : (0 : ℝ) ≤ 4)
    ((ae_restrict_mem hS.measurableSet).mono fun z hz => by
      simpa only [Function.comp_apply,fb,Real.norm_of_nonneg (norm_nonneg _)] using (hPoint z hz).2)
  rw [← hQeq, ← ENNReal.ofReal_mul hQ] at hL
  refine hL.trans ((add_le_add le_rfl (mul_le_mul_right hAbs (ENNReal.ofReal 4))).trans ?_)
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  dsimp only [C]
  have hL1 : 0 ≤ 8*W*Q*(F*(3*H*D)) := by positivity
  have hL2 : 0 ≤ 8*W*Q*G := by positivity
  have hL3 : 0 ≤ Q*H*D*F := by positivity
  nlinarith only [hL1,hL2,hL3]

end Thesis
