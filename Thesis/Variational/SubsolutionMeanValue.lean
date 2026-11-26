module

public import Thesis.External.SubsolutionMeanValue
import Thesis.Variational.BoundarySubsolution
import SupportingAnalysis.MeanValue.Estimate

/-! The native C² scalar mean estimate by an exponential subharmonic lift. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff Convolution ENNReal Laplacian Topology

namespace Thesis

private theorem coordDeriv_contDiff_one {f : Point → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin 3) :
    ContDiff ℝ 1 (coordDeriv i f) :=
  (ContinuousLinearMap.apply ℝ ℝ (axis i)).contDiff.comp (hf.fderiv_right (by decide))

private theorem convolution_coordDeriv {k f : Point → ℝ}
    (hk : LocallyIntegrable k volume) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x : Point) (i : Fin 3) :
    coordDeriv i (k ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x =
      (k ⋆[ContinuousLinearMap.mul ℝ ℝ] coordDeriv i f) x := by
  let L := ContinuousLinearMap.mul ℝ ℝ
  unfold coordDeriv
  rw [(hfc.hasFDerivAt_convolution_right L hk hf x).fderiv]
  exact convolution_precompR_apply L hk (hfc.fderiv ℝ)
    (hf.continuous_fderiv one_ne_zero) x (axis i)

private theorem laplacian_convolution_contDiff_two {k f : Point → ℝ} (hk : Continuous k)
    (hkc : HasCompactSupport k) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (x : Point) :
    laplacian (k ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x = ∫ y, k y * laplacian f (x-y) := by
  classical
  let L := ContinuousLinearMap.mul ℝ ℝ
  unfold laplacian
  have hD (i : Fin 3) : Continuous (coordDeriv i (coordDeriv i f)) :=
    (ContinuousLinearMap.apply ℝ ℝ (axis i)).continuous.comp
      ((coordDeriv_contDiff_one hf i).continuous_fderiv one_ne_zero)
  have hInt (i : Fin 3) : Integrable (fun y => k y * coordDeriv i (coordDeriv i f) (x-y)) :=
    (hk.mul ((hD i).comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport hkc.mul_right
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hInt i)]
  apply Finset.sum_congr rfl
  intro i _
  have hFirst : coordDeriv i (k ⋆[L] f) = (k ⋆[L] coordDeriv i f) :=
    funext (fun y => convolution_coordDeriv hk.locallyIntegrable (hf.of_le (by decide)) hfc y i)
  rw [hFirst, convolution_coordDeriv hk.locallyIntegrable (coordDeriv_contDiff_one hf i)
    (hfc.fderiv_apply ℝ (axis i)), convolution_mul]

private theorem laplacian_eq_mathlib {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 2 f x) :
    laplacian f x = Laplacian.laplacian f x := by
  rw [laplacian,InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [EuclideanSpace.basisFun_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  let L := ContinuousLinearMap.apply ℝ ℝ (axis i)
  change fderiv ℝ (L ∘ fderiv ℝ f) x (axis i) = fderiv ℝ (fderiv ℝ f) x (axis i) (axis i)
  rw [fderiv_comp x L.differentiableAt ((hf.fderiv_right (by decide : (1 : WithTop ℕ∞)+1 ≤ 2)).differentiableAt one_ne_zero),
    L.fderiv]
  rfl

private theorem exists_subsolution_cutoff {c : Point} {r : ℝ} (hr : 0 < r)
    {f : Point → ℝ} (hf : ContDiffOn ℝ 2 f (ball c r))
    (hNonneg : ∀ x ∈ ball c r, 0 ≤ f x) :
    ∃ g : Point → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∀ x, 0 ≤ g x) ∧ EqOn g f (closedBall c (3*r/4)) := by
  let χ : ContDiffBump c := ⟨3*r/4,7*r/8,by positivity,by linarith only [hr]⟩
  let g (x : Point) := χ x * f x
  have hχ : tsupport (χ : Point → ℝ) ⊆ ball c r := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by dsimp only [χ]; linarith only [hr])
  have hχdom : Function.support (χ : Point → ℝ) ⊆ ball c r := subset_tsupport _ |>.trans hχ
  have hg : ContDiff ℝ 2 g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ ball c r
    · exact (χ.contDiff (n := 2)).contDiffAt.mul (hf.contDiffAt (isOpen_ball.mem_nhds hx))
    · have h0 : ContDiffAt ℝ 2 (fun _ : Point => (0 : ℝ)) x := contDiffAt_const
      apply h0.congr_of_eventuallyEq
      have hx' : x ∈ (tsupport (χ : Point → ℝ))ᶜ := fun h => hx (hχ h)
      filter_upwards [(isClosed_tsupport (χ : Point → ℝ)).isOpen_compl.mem_nhds hx'] with y hy
      change χ y * f y = 0
      rw [image_eq_zero_of_notMem_tsupport (f := (χ : Point → ℝ)) hy,zero_mul]
  refine ⟨g,hg,χ.hasCompactSupport.mul_right,?_,?_⟩
  · intro x
    by_cases hx : x ∈ ball c r
    · exact mul_nonneg χ.nonneg (hNonneg x hx)
    · change 0 ≤ χ x * f x
      rw [Function.notMem_support.mp (fun hy => hx (hχdom hy)),zero_mul]
  · intro x hx
    change χ x * f x = f x
    rw [χ.one_of_mem_closedBall hx,one_mul]

/-- Positive local convolution approximates the C² field on a compact
interior ball while preserving the required subsolution inequality. -/
private theorem exists_smooth_subsolution_approx
    {c : Point} {r A δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    {f : Point → ℝ} (hf : ContDiffOn ℝ 2 f (ball c r))
    (hNonneg : ∀ x ∈ ball c r, 0 ≤ f x)
    (hSub : ∀ x ∈ ball c r, 0 ≤ laplacian f x + A*f x) :
    ∃ u : Point → ℝ, ContDiff ℝ ∞ u ∧
      (∀ x, 0 ≤ u x) ∧
      (∀ x ∈ ball c (r/2), 0 ≤ laplacian u x + A*u x) ∧
      ∀ x ∈ closedBall c (r/2), |u x-f x| ≤ δ := by
  obtain ⟨g,hg,hgc,hg₀,hgF⟩ := exists_subsolution_cutoff hr hf hNonneg
  have hUniform := hgc.uniformContinuous_of_continuous hg.continuous
  obtain ⟨a,ha,hNear⟩ := Metric.uniformContinuous_iff.mp hUniform δ hδ
  let t := min a (r/8)
  have ht : 0 < t := lt_min ha (by positivity)
  let χ : ContDiffBump (0 : Point) := ⟨t/2,t,half_pos ht,half_lt_self ht⟩
  let k := χ.normed volume
  let L := ContinuousLinearMap.mul ℝ ℝ
  let u := k ⋆[L] g
  have hk : Continuous k := χ.continuous_normed
  have hkc : HasCompactSupport k := χ.hasCompactSupport_normed
  have hu : ContDiff ℝ ∞ u :=
    hkc.contDiff_convolution_left L (χ.contDiff_normed (n := ⊤)) hg.continuous.locallyIntegrable
  have hk₀ (x : Point) : 0 ≤ k x := χ.nonneg_normed x
  have hkFree {x : Point} (hx : x ∉ ball (0 : Point) t) : k x = 0 :=
    Function.notMem_support.mp (χ.support_normed_eq (μ := volume) ▸ hx)
  have hBall (x y : Point) (hx : x ∈ ball c (r/2)) (hy : y ∈ ball (0 : Point) t) :
      x-y ∈ ball c (3*r/4) := by
    have hX := mem_ball.mp hx
    have hY := (mem_ball_zero_iff.mp hy).trans_le (min_le_right a (r/8))
    rw [mem_ball,dist_eq_norm]
    rw [dist_eq_norm] at hX
    have hT := norm_sub_le (x-c) y
    have he : x-y-c = x-c-y := by abel
    rw [he]
    exact hT.trans_lt (by linarith only [hX,hY,hr])
  refine ⟨u,hu,?_,?_,?_⟩
  · intro x
    change 0 ≤ (k ⋆[L] g) x
    rw [convolution_mul]
    exact integral_nonneg (fun y => mul_nonneg (hk₀ y) (hg₀ (x-y)))
  · intro x hx
    have hGD : Continuous (laplacian g) := by
      unfold laplacian
      apply continuous_finsetSum
      intro i _
      exact (ContinuousLinearMap.apply ℝ ℝ (axis i)).continuous.comp
        ((coordDeriv_contDiff_one hg i).continuous_fderiv one_ne_zero)
    have hIntD : Integrable (fun y => k y * laplacian g (x-y)) :=
      (hk.mul (hGD.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport hkc.mul_right
    have hIntG : Integrable (fun y => k y * g (x-y)) :=
      (hk.mul (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport hkc.mul_right
    change 0 ≤ laplacian (k ⋆[L] g) x + A*((k ⋆[L] g) x)
    rw [laplacian_convolution_contDiff_two hk hkc hg hgc,convolution_mul,
      ← integral_const_mul,← integral_add hIntD (hIntG.const_mul A)]
    apply integral_nonneg
    intro y
    change 0 ≤ k y * laplacian g (x-y) + A * (k y * g (x-y))
    by_cases hy : y ∈ ball (0 : Point) t
    · have hxy := hBall x y hx hy
      have hxy' : x-y ∈ ball c r := ball_subset_ball (by linarith only [hr]) hxy
      have heq : g =ᶠ[𝓝 (x-y)] f := by
        filter_upwards [isOpen_ball.mem_nhds hxy] with z hz
        exact hgF (ball_subset_closedBall hz)
      have hLap := laplacian_eq_of_eventuallyEq heq
      calc
        0 ≤ k y * (laplacian f (x-y)+A*f (x-y)) := mul_nonneg (hk₀ y) (hSub _ hxy')
        _ = _ := by rw [hLap,heq.eq_of_nhds]; ring
    · rw [hkFree hy,zero_mul,zero_mul,mul_zero,add_zero]
  · intro x hx
    have hxF : g x = f x := hgF (closedBall_subset_closedBall (by linarith only [hr]) hx)
    rw [← hxF,← Real.dist_eq]
    apply ContDiffBump.dist_normed_convolution_le hg.continuous.aestronglyMeasurable
    intro y hy
    exact (hNear ((mem_ball.mp hy).trans_le (min_le_left a (r/8)))).le

/-- The nonnegative scalar C² subsolution estimate with the thesis
normalization, obtained from the smooth mean-value estimate by positive interior convolution. -/
theorem classicalScalarSubsolutionMeanValue : External.ClassicalScalarSubsolutionMeanValue := by
  intro A hA
  let k := Real.sqrt A
  let F := SupportingAnalysis.subsolutionMeanVolumeFactor 3
  let V := volume.real (ball (0 : Point) 1)
  let C := 8 * (F+1) * Real.exp k / V
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hF : 0 ≤ F := SupportingAnalysis.subsolutionMeanVolumeFactor_nonneg 3
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume (0 : Point) zero_lt_one).ne'
    measure_ball_lt_top.ne
  have hC : 0 < C := div_pos
    (mul_pos (mul_pos (by norm_num) (by linarith only [hF])) (Real.exp_pos _)) hV
  refine ⟨C,hC,?_⟩
  intro c r hr f hf hInt hNonneg hΔ
  let S := ball c (r/2)
  let W := volume.real S
  let K := C * r⁻¹ ^ 3
  let a := r/4
  have ha : 0 < a := div_pos hr.1 (by norm_num)
  have ha₂ : 2*a = r/2 := by dsimp only [a]; ring
  have hW : 0 < W := ENNReal.toReal_pos (measure_ball_pos volume c (half_pos hr.1)).ne'
    measure_ball_lt_top.ne
  have hK : 0 ≤ K := mul_nonneg hC.le (pow_nonneg (inv_nonneg.mpr hr.1.le) _)
  have hS : S ⊆ ball c r := ball_subset_ball (half_lt_self hr.1).le
  have hWscale : W = (r/2)^3 * V := by
    dsimp only [W,S,V]
    rw [measureReal_def,Measure.addHaar_ball_of_pos volume c (half_pos hr.1),
      finrank_euclideanSpace_fin,ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg (half_pos hr.1).le _)]
    rfl
  have hCoeff : F*Real.exp (k*a)/W ≤ K := by
    have ha₁ : a ≤ 1 := by dsimp only [a]; linarith only [hr.2]
    have hExp : Real.exp (k*a) ≤ Real.exp k := Real.exp_le_exp.mpr
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ha₁ hk)
    calc
      _ ≤ ((F+1)*Real.exp k)/W :=
        div_le_div_of_nonneg_right
          (mul_le_mul (by linarith only [hF]) hExp (Real.exp_nonneg _) (by linarith only [hF])) hW.le
      _ = _ := by
        rw [hWscale]
        dsimp only [K,C]
        field_simp [hr.1.ne',hV.ne']
        ring
  have hSub (x : Point) (hx : x ∈ ball c r) : 0 ≤ laplacian f x + A*f x := by
    linarith only [hΔ x hx]
  change f c ≤ K * ∫ x in ball c r, f x
  apply le_of_forall_pos_le_add
  intro η hη
  have hDen : 0 < K*W+1 := add_pos_of_nonneg_of_pos (mul_nonneg hK hW.le) one_pos
  let δ := η/(K*W+1)
  have hδ : 0 < δ := div_pos hη hDen
  obtain ⟨u,hu,hu₀,huSub,huClose⟩ := exists_smooth_subsolution_approx hr.1 hδ hf hNonneg hSub
  have hUI : IntegrableOn u S :=
    (hu.continuous.continuousOn.integrableOn_compact (isCompact_closedBall c (r/2))).mono_set
      ball_subset_closedBall
  have hUSub (y : Point) (hy : y ∈ ball c (2*a)) :
      0 ≤ Laplacian.laplacian u y + k^2*u y := by
    rw [ha₂] at hy
    rw [← laplacian_eq_mathlib ((hu.of_le (by decide)).contDiffAt),Real.sq_sqrt hA]
    exact huSub y hy
  have hI₂ : IntegrableOn u (ball c (2*a)) := by rw [ha₂]; exact hUI
  have hMean := SupportingAnalysis.subsolutionMean_of_laplacian_lower (m := 3) (by decide)
    (c := c) (x := c) ha hk (mem_ball_self ha) hu.contDiffOn hI₂
    (fun x _ => hu₀ x) hUSub
  rw [ha₂] at hMean
  change u c ≤ F*Real.exp (k*a) * ((∫ y in S, u y)/W) at hMean
  have hMean' : u c ≤ K * ∫ y in S, u y := by
    have hEq : F*Real.exp (k*a) * ((∫ y in S, u y)/W) =
        (F*Real.exp (k*a)/W) * (∫ y in S, u y) := by ring
    rw [hEq] at hMean
    exact hMean.trans (mul_le_mul_of_nonneg_right hCoeff (integral_nonneg fun x => hu₀ x))
  have hApproxU : (∫ y in S, u y) ≤ (∫ y in S, f y)+ W*δ := by
    have hFS : IntegrableOn f S := hInt.mono_set hS
    have hδS : IntegrableOn (fun _ : Point => δ) S := integrableOn_const measure_ball_lt_top.ne
    have h := setIntegral_mono_on hUI (hFS.add hδS) measurableSet_ball (fun x hx => by
      have hb := (abs_le.mp (huClose x (ball_subset_closedBall hx))).2
      change u x ≤ f x+δ
      linarith only [hb])
    rw [integral_add' hFS hδS,setIntegral_const,smul_eq_mul] at h
    exact h
  have hMass : (∫ y in S, f y) ≤ ∫ y in ball c r, f y :=
    setIntegral_mono_set hInt
      ((ae_restrict_mem measurableSet_ball).mono (fun x hx => hNonneg x hx))
      (Eventually.of_forall hS)
  have hCenter := (abs_le.mp (huClose c (mem_closedBall_self (half_pos hr.1).le))).1
  have hSmall : δ * (K*W+1) = η := div_mul_cancel₀ _ hDen.ne'
  have hBound := mul_le_mul_of_nonneg_left (hApproxU.trans (add_le_add_left hMass (W*δ))) hK
  nlinarith only [hMean',hCenter,hSmall,hBound]

end Thesis
