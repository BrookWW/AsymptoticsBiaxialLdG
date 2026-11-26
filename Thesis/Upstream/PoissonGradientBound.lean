module

public import Thesis.Variational.EulerLagrange
public import HolderToCK.Analysis.Poisson.PotentialRegularity
public import HolderToCK.Foundation.WeakPoisson
import HolderToCK.Analysis.Poisson.PotentialTrace
import HolderToCK.Analysis.Poisson.InteriorPoissonRegularity
import HolderToCK.Analysis.Harmonic.UnitC2Bounds
import Thesis.Variational.BoundaryPoissonEstimate
import Thesis.Variational.BoundarySmallEnergy
import Thesis.Variational.ScaledDefects
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! The local linear gradient bound with continuous bounded forcing. -/

public section

noncomputable section

open Filter HarmonicMaps HolderToCK MeasureTheory Metric Set
open scoped ContDiff Convolution ENNReal Matrix.Norms.Frobenius RealInnerProductSpace Topology

namespace Thesis

private theorem compactDataMollification_tendstoUniformly_of_continuous {n q : ℕ}
    {g : Domain n → Ambient q} (hg : Continuous g) (hc : HasCompactSupport g)
    (h : ℕ → PositiveRadius) (hh : Tendsto (fun k => (h k).val) atTop (𝓝 0)) :
    TendstoUniformly (fun k => compactDataMollification g (h k)) g atTop := by
  apply Metric.tendstoUniformly_iff.2
  intro η hη
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuous_iff.1 (hc.uniformContinuous_of_continuous hg)
    (η / 2) (half_pos hη)
  filter_upwards [hh.eventually (gt_mem_nhds hδ)] with k hk x
  have hsupport : Function.support (scaledMollifierKernel n (h k)) ⊆
      ball (0 : Domain n) (h k).val :=
    (subset_tsupport _).trans ((scaledMollifierKernel_tsupport_subset_halfBall n (h k)).trans
      (closedBall_subset_ball (half_lt_self (h k).property)))
  have hB : dist (compactDataMollification g (h k) x) (g x) ≤ η / 2 := by
    apply dist_convolution_le (half_pos hη).le hsupport (scaledMollifierKernel_nonneg n (h k))
      (scaledMollifierKernel_integral_one n (h k)) hg.aestronglyMeasurable
    intro y hy
    exact (hgδ (hy.trans hk)).le
  rw [dist_comm]
  exact hB.trans_lt (half_lt_self hη)

theorem smooth_compactly_supported_holder_one {n q : ℕ} {f : Domain n → Ambient q}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    ∃ L : ℝ, 0 ≤ L ∧ HolderBoundOn univ f 1 L := by
  obtain ⟨L, hL⟩ := hf.lipschitzWith_of_hasCompactSupport hcf (by simp)
  refine ⟨L, L.coe_nonneg, ?_⟩
  intro x _ y _
  change ‖f x - f y‖ ≤ (L : ℝ) * Real.rpow (dist x y) 1
  rw [← dist_eq_norm, Real.rpow_eq_pow, Real.rpow_one]
  exact hL.dist_le_mul x y

private theorem tendsto_setIntegral_of_uniformlyOn_compact_real {E : Type*}
    [TopologicalSpace E] [T2Space E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {K : Set E} {μ : Measure E} [IsLocallyFiniteMeasure μ] (hK : IsCompact K) (hKMeas : MeasurableSet K)
    {F : ℕ → E → ℝ} {f : E → ℝ} (hF : ∀ n, ContinuousOn (F n) K)
    (hf : ContinuousOn f K) (h : TendstoUniformlyOn F f atTop K) :
    Tendsto (fun n => ∫ x in K, F n x ∂μ) atTop (𝓝 (∫ x in K, f x ∂μ)) := by
  have hFin := hK.measure_lt_top (μ := μ)
  let C := μ.real K
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hC₁ : 0 < C + 1 := by linarith only [hC]
  apply Metric.tendsto_nhds.2
  intro η hη
  let δ := η / (C + 1)
  have hδ : 0 < δ := div_pos hη hC₁
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 h) δ hδ] with n hn
  rw [dist_eq_norm, ← integral_sub ((hF n).integrableOn_compact hK) (hf.integrableOn_compact hK)]
  have hB : ‖∫ x in K, F n x - f x ∂μ‖ ≤ δ * C := by
    calc
      _ ≤ ∫ x in K, δ ∂μ := by
        apply norm_integral_le_of_norm_le (integrableOn_const hFin.ne)
        filter_upwards [ae_restrict_mem hKMeas] with x hx
        exact (by simpa only [dist_eq_norm, norm_sub_rev] using (hn x hx).le :
          ‖F n x - f x‖ ≤ δ)
      _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  exact hB.trans_lt ((mul_lt_mul_of_pos_left (lt_add_one C) hδ).trans_eq
    (div_mul_cancel₀ _ hC₁.ne'))

private theorem tendstoUniformlyOn_inner_left_of_bound {E : Type*} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u : ℕ → E → F} {v w : E → F} {K : Set E}
    (h : TendstoUniformlyOn u v atTop K) {L : ℝ}
    (hL : 0 ≤ L) (hW : ∀ x ∈ K, ‖w x‖ ≤ L) :
    TendstoUniformlyOn (fun n x => inner ℝ (u n x) (w x)) (fun x => inner ℝ (v x) (w x)) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro η hη
  have hL₁ : 0 < L + 1 := by linarith only [hL]
  let δ := η / (L + 1)
  have hδ : 0 < δ := div_pos hη hL₁
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 h) δ hδ] with n hn x hx
  rw [dist_eq_norm, ← inner_sub_left]
  refine (norm_inner_le_norm _ _).trans_lt ?_
  have hNear := hn x hx
  rw [dist_eq_norm] at hNear
  calc
    _ ≤ δ * L := mul_le_mul hNear.le (hW x hx) (norm_nonneg _) hδ.le
    _ < δ * (L + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hδ
    _ = _ := div_mul_cancel₀ _ hL₁.ne'


private theorem tendsto_setIntegral_on_ball_of_uniformOn_closedBall {n : ℕ} (R : ℝ)
    {F : ℕ → Domain n → ℝ} {f : Domain n → ℝ} (hF : ∀ m, ContinuousOn (F m) (closedBall 0 R))
    (hf : ContinuousOn f (closedBall 0 R)) (h : TendstoUniformlyOn F f atTop (closedBall 0 R)) :
    Tendsto (fun m => ∫ x in ball (0 : Domain n) R, F m x) atTop (𝓝 (∫ x in ball (0 : Domain n) R, f x)) := by
  let μ := (volume : Measure (Domain n)).restrict (ball 0 R)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_ball_ne_top
  have hμ : μ.restrict (closedBall 0 R) = μ := by
    rw [show μ = volume.restrict (ball 0 R) from rfl,
      Measure.restrict_restrict measurableSet_closedBall, inter_eq_right.2 ball_subset_closedBall]
  have hT := tendsto_setIntegral_of_uniformlyOn_compact_real (μ := μ) (isCompact_closedBall 0 R)
    measurableSet_closedBall hF hf h
  rwa [hμ] at hT

/- The (C^1) potential and its distributional equation use the same
gradient columns. Only continuity of the compactly supported datum is needed. -/
theorem compact_continuous_newtonian_regular {n q : ℕ}
    (hn : 2 ≤ n) {g : Domain n → Ambient q} (hg : Continuous g) (hcg : HasCompactSupport g) :
    let P := newtonianPotential hn g
    let D := fun x i => potentialGradientColumn i g x
    ContDiff ℝ 1 P ∧ (∀ x i, fderiv ℝ P x (EuclideanSpace.single i 1) = D x i) ∧
      ∀ R : ℝ, WeakPoissonOn (ballDomain (0 : Domain n) R) D g := by
  let P := newtonianPotential hn g
  let G (k : ℕ) := compactDataMollification g (compactDataApproximationScale k)
  let Pk (k : ℕ) := newtonianPotential hn (G k)
  let A := potentialGradientLinearMap g
  let D (x : Domain n) (i : Fin n) := potentialGradientColumn i g x
  have hn' : 0 < n := by omega
  have hG (k : ℕ) : ContDiff ℝ ∞ (G k) := compactDataMollification_contDiff hg _
  have hGc (k : ℕ) : HasCompactSupport (G k) := compactDataMollification_hasCompactSupport hcg _
  have hPk (k : ℕ) : ContDiff ℝ ∞ (Pk k) := newtonianPotential_contDiff hn (hG k) (hGc k)
  have hLim := compactDataMollification_tendstoUniformly_of_continuous hg hcg _
    compactDataApproximationScale_tendsto
  obtain ⟨S, hS, hGS⟩ := compactDataMollification_fixedSupport hcg
  have hD (i : Fin n) : Continuous (fun x => D x i) := potentialGradientColumn_continuous hn' i hg hcg
  have hA : Continuous A := by
    unfold A potentialGradientLinearMap
    exact continuous_finsetSum _ fun i _ =>
      ((ContinuousLinearMap.smulRightL ℝ (Domain n) (Ambient q))
        (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i)).continuous.comp (hD i)
  have hP (R : ℝ) : TendstoUniformlyOn Pk P atTop (closedBall 0 R) :=
    newtonianPotential_tendstoUniformlyOn hn (fun k => (hG k).continuous) hg hGS hS hLim
  have hCol (R : ℝ) (i : Fin n) : TendstoUniformlyOn
      (fun k => potentialGradientColumn i (G k)) (potentialGradientColumn i g) atTop (closedBall 0 R) :=
    potentialGradientColumn_tendstoUniformlyOn hn' i (fun k => (hG k).continuous) hg hGS hS hLim
  have hDk (k : ℕ) : fderiv ℝ (Pk k) = potentialGradientLinearMap (G k) := by
    funext x
    exact newtonianPotential_fderiv_eq_gradientLinearMap_smooth hn
      ((hG k).of_le (WithTop.coe_le_coe.mpr le_top)) (hGc k) x
  have hAx (R : ℝ) :
      TendstoUniformlyOn (fun k => fderiv ℝ (Pk k)) A atTop (closedBall 0 R) := by
    simp only [hDk, A]
    apply tendstoUniformlyOn_finiteSum Finset.univ
    intro i _
    exact (((ContinuousLinearMap.smulRightL ℝ (Domain n) (Ambient q))
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i)).uniformContinuous.comp_tendstoUniformlyOn (hCol R i))
  have hAloc : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (Pk k)) A atTop univ := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).2
    intro K _ hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Domain n)
    exact (hAx R).mono hR
  have hDeriv (x : Domain n) : HasFDerivAt P (A x) x := by
    apply hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hAloc
      (fun k y _ => ((hPk k).differentiable (by simp) y).hasFDerivAt) _ (mem_univ x)
    intro y _
    exact (hP (‖y‖ + 1)).tendsto_at
      (mem_closedBall_zero_iff.2 (le_add_of_nonneg_right zero_le_one))
  have hP1 : ContDiff ℝ 1 P := by
    rw [← contDiffOn_univ, show (1 : ℕ∞ω) = 0 + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen isOpen_univ]
    refine ⟨fun x _ => (hDeriv x).differentiableAt.differentiableWithinAt,
      fun h => by simp at h, contDiffOn_zero.2 ?_⟩
    exact hA.continuousOn.congr (fun x _ => (hDeriv x).fderiv)
  have hPD (x : Domain n) (i : Fin n) : fderiv ℝ P x (EuclideanSpace.single i 1) = D x i := by
    rw [(hDeriv x).fderiv]
    change (potentialGradientLinearMap g x) (EuclideanSpace.single i 1) = _
    rw [potentialGradientLinearMap, columnLinearMap_single]
  refine ⟨hP1, hPD, fun R => ?_⟩
  let Ω := ballDomain (0 : Domain n) R
  have hLap (k : ℕ) (x : Domain n) : Laplacian.laplacian (Pk k) x = G k x := by
    obtain ⟨L, hL, hHolder⟩ := smooth_compactly_supported_holder_one (hG k) (hGc k)
    exact newtonianPotential_laplacian hn (hG k) (hGc k) zero_lt_one hL hHolder x
  have hWeak (k : ℕ) : WeakPoissonOn Ω
      (fun x i => potentialGradientColumn i (G k) x) (G k) := by
    have hEq := weakPoissonOn_of_contDiffOn_two_of_laplacian_eq Ω
      (((hPk k).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn) (fun x _ => hLap k x)
    have he : (fun x i => fderiv ℝ (Pk k) x (EuclideanSpace.single i 1)) =
        fun x i => potentialGradientColumn i (G k) x := by
      funext x i
      rw [hDk, potentialGradientLinearMap, columnLinearMap_single]
    exact he ▸ hEq
  refine ⟨hg.continuousOn.locallyIntegrableOn Ω.property.measurableSet, fun ψ hψ hψc hψΩ => ?_⟩
  let K := closedBall (0 : Domain n) R
  let Ψ (i : Fin n) (x : Domain n) := fderiv ℝ ψ x (EuclideanSpace.single i 1)
  have hΨ (i : Fin n) : Continuous (Ψ i) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  let I (k : ℕ) (x : Domain n) := ∑ i : Fin n,
    inner ℝ (potentialGradientColumn i (G k) x) (Ψ i x)
  let I₀ (x : Domain n) := ∑ i : Fin n, inner ℝ (D x i) (Ψ i x)
  let J (k : ℕ) (x : Domain n) := inner ℝ (G k x) (ψ x)
  let J₀ (x : Domain n) := inner ℝ (g x) (ψ x)
  have hI (k : ℕ) : Continuous (I k) := continuous_finsetSum _ fun i _ =>
    (potentialGradientColumn_continuous hn' i (hG k).continuous (hGc k)).inner (hΨ i)
  have hI₀ : Continuous I₀ := continuous_finsetSum _ fun i _ => (hD i).inner (hΨ i)
  have hJ (k : ℕ) : Continuous (J k) := (hG k).continuous.inner hψ.continuous
  have hJ₀ : Continuous J₀ := hg.inner hψ.continuous
  have hUniI : TendstoUniformlyOn I I₀ atTop K := by
    apply tendstoUniformlyOn_finiteSum Finset.univ
    intro i _
    obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : Domain n) R).exists_bound_of_continuousOn (hΨ i).continuousOn
    exact tendstoUniformlyOn_inner_left_of_bound (hCol R i) (le_max_right L 0)
      (fun x hx => (hL x hx).trans (le_max_left _ _))
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : Domain n) R).exists_bound_of_continuousOn hψ.continuous.continuousOn
  have hUniJ : TendstoUniformlyOn J J₀ atTop K := tendstoUniformlyOn_inner_left_of_bound
    hLim.tendstoUniformlyOn (le_max_right L 0) (fun x hx => (hL x hx).trans (le_max_left _ _))
  have hLimitI := tendsto_setIntegral_on_ball_of_uniformOn_closedBall R
    (fun k => (hI k).continuousOn) hI₀.continuousOn hUniI
  have hLimitJ := tendsto_setIntegral_on_ball_of_uniformOn_closedBall R
    (fun k => (hJ k).continuousOn) hJ₀.continuousOn hUniJ
  have hEq (k : ℕ) : (∫ x in Ω.val, I k x) = -(∫ x in Ω.val, J k x) := (hWeak k).2 ψ hψ hψc hψΩ |>.2.2
  have hIntI : IntegrableOn I₀ Ω.val volume :=
    (hI₀.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Domain n) R)).mono_set
    (ball_subset_closedBall : Ω.val ⊆ K)
  have hIntJ : IntegrableOn J₀ Ω.val volume :=
    (hJ₀.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Domain n) R)).mono_set
    (ball_subset_closedBall : Ω.val ⊆ K)
  exact ⟨hIntI, hIntJ, tendsto_nhds_unique hLimitI (hLimitJ.neg.congr fun k => (hEq k).symm)⟩


private theorem continuous_schauderForcing_of_continuousOn {n q : ℕ}
    {F : Domain n → Ambient q} (hF : ContinuousOn F (ball 0 1)) :
    Continuous (schauderForcing F) := by
  obtain ⟨_, hχ⟩ := schauderCutoff_lipschitz n
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x ∈ ball (0 : Domain n) 1
  · change ContinuousAt (fun y => schauderCutoff y • F y) x
    exact hχ.continuous.continuousAt.smul ((hF x hx).continuousAt (isOpen_ball.mem_nhds hx))
  · apply continuousAt_const.congr
    have hN : (3 / 4 : ℝ) < ‖x‖ := (by norm_num : (3 / 4 : ℝ) < 1).trans_le
      (le_of_not_gt fun ht => hx (mem_ball_zero_iff.2 ht))
    have hNear : ∀ᶠ y in 𝓝 x, 3 / 4 < ‖y‖ :=
      continuous_norm.continuousAt.tendsto (Ioi_mem_nhds hN)
    filter_upwards [hNear] with y hy
    exact (schauderForcing_eq_zero F hy.le).symm

private theorem exists_unit_linearPoisson_gradient_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} (v : Domain 3 → Ambient q) (M K : ℝ),
      0 ≤ M → 0 ≤ K → ContDiffOn ℝ 2 v (ball 0 1) →
      (∀ x ∈ ball (0 : Point) 1, ‖v x‖ ≤ M) →
      (∀ x ∈ ball (0 : Point) 1, ‖laplacian v x‖ ≤ K) →
      ‖fderiv ℝ v 0‖ ≤ C * (M + K) := by
  obtain ⟨C_H, hC_H, hH⟩ := harmonic_unit_c2_bounds 3 (by decide) 1 zero_le_one le_rfl
  let V := potentialValueConstant 3
  have hV : 0 ≤ V := potentialValueConstant_nonneg 3
  let C := 1 + C_H * (1 + V) + Real.sqrt 3 * 3
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro q v M K hM hK hv hvB hFBound
  let F := laplacian v
  let g := schauderForcing F
  let P := newtonianPotential (n := 3) (by decide : 2 ≤ 3) g
  let H := v - P
  have hF := continuousOn_laplacian_of_contDiffOn_two isOpen_ball hv
  have hg := continuous_schauderForcing_of_continuousOn hF
  have hcg := schauderForcing_hasCompactSupport F
  obtain ⟨hP, hPD, hPweak⟩ := compact_continuous_newtonian_regular (by decide : 2 ≤ 3) hg hcg
  let U := ballDomain (0 : Domain 3) (5 / 8)
  have hU : U.val ⊆ ball (0 : Point) 1 := ball_subset_ball (by norm_num)
  have hv₂ : ContDiffOn ℝ 2 v U.val := hv.mono hU
  let Dv (x : Domain 3) (i : Fin 3) := fderiv ℝ v x (EuclideanSpace.single i 1)
  let Dp (x : Domain 3) (i : Fin 3) := potentialGradientColumn i g x
  have hvH : MemW12Loc U v Dv :=
    memW12Loc_of_contDiffOn_one U (hv₂.of_le (by norm_num))
  have hPH : MemW12Loc U P Dp := by
    have he : (fun x i => fderiv ℝ P x (EuclideanSpace.single i 1)) = Dp :=
      funext fun x => funext (hPD x)
    exact he ▸ memW12Loc_of_contDiffOn_one U hP.contDiffOn
  have hvWeak : WeakPoissonOn U Dv F := weakPoissonOn_of_contDiffOn_two_of_laplacian_eq U hv₂
    (fun x hx => laplacian_eq_coordinateSum_of_contDiffAt_two v x
      (hv₂.contDiffAt (U.property.mem_nhds hx)))
  have hHloc : MemW12Loc U H (fun x i => Dv x i - Dp x i) := by
    refine ⟨hvH.1.sub hPH.1, ?_, ?_⟩
    · intro T hT hTU
      exact (hvH.2.1 T hT hTU).sub (hPH.2.1 T hT hTU)
    · intro i T hT hTU
      exact (hvH.2.2 i T hT hTU).sub (hPH.2.2 i T hT hTU)
  have hHweak : WeakPoissonOn U (fun x i => Dv x i - Dp x i) (fun _ => 0) := by
    apply (hvWeak.sub (hPweak (5 / 8))).congr (EventuallyEq.refl _ _)
    filter_upwards [ae_restrict_mem U.property.measurableSet] with x hx
    change F x - g x = 0
    rw [show g x = F x from schauderForcing_eq F (ball_subset_closedBall hx), sub_self]
  obtain ⟨hHs, hHarm⟩ := hHweak.contDiffOn_of_continuous_weak_harmonic (by decide) U hHloc
    (hv₂.continuousOn.sub hP.continuous.continuousOn)
  have hSup : tsupport g ⊆ closedBall (0 : Domain 3) 1 :=
    (schauderForcing_tsupport_subset F).trans (closedBall_subset_closedBall (by norm_num))
  have hgB (x : Domain 3) : ‖g x‖ ≤ K := schauderForcing_norm_bound hK hFBound _
  have hHbound (x : Domain 3) (hx : x ∈ U.val) : ‖H x‖ ≤ M + V * K := by
    have hx' : ‖x‖ ≤ 1 := (mem_ball_zero_iff.1 (hU hx)).le
    exact (norm_sub_le _ _).trans (add_le_add (hvB x (hU hx))
      (newtonianPotential_unitData_norm_bound (by decide : 2 ≤ 3) hg hcg hSup hK hgB hx'))
  have hH' := (hH q H (M + V * K) (add_nonneg hM (mul_nonneg hV hK)) hHs hHarm hHbound).1
    1 (by norm_num) 0 (mem_ball_self (by norm_num))
  have hGD : ‖fderiv ℝ H 0‖ ≤ C_H * (M + V * K) := by
    simpa only [norm_iteratedFDeriv_one] using hH'
  have hPD' : ‖fderiv ℝ P (0 : Domain 3)‖ ≤ Real.sqrt 3 * (3 * K) := by
    apply norm_linearMap_le_of_columns_bound _ (by positivity : 0 ≤ 3 * K)
    intro i
    rw [hPD]
    exact potentialGradientColumn_unitData_norm_bound (by decide : 0 < 3) i hg hcg hSup hK hgB (by simp)
  have hVsum : v = H + P := by dsimp only [H]; abel
  rw [hVsum, fderiv_add ((hHs.contDiffAt (U.property.mem_nhds (mem_ball_self (by norm_num)))).differentiableAt (by simp))
    (hP.differentiable one_ne_zero _)]
  have h₁ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hK : M ≤ M + K) hC_H
  have h₂ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hM : K ≤ M + K) (mul_nonneg hC_H hV)
  have h₃ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hM : K ≤ M + K)
    (show 0 ≤ Real.sqrt 3 * 3 by positivity)
  apply (norm_add_le _ _).trans ((add_le_add hGD hPD').trans ?_)
  dsimp only [C]
  nlinarith only [h₁, h₂, h₃, add_nonneg hM hK]


private theorem norm_gradient_scaled_le_frobenius_fderiv
    (v : Point → S0) (c : Point) {r : ℝ} (hr : 0 < r)
    (hv : DifferentiableAt ℝ v c) :
    r * Real.sqrt (gradientNormSq (ClassicalGradient v c)) ≤
      Real.sqrt 3 * ‖fderiv ℝ (fun y : Point => frobeniusCoordinateEquiv (v (c + r • y))) 0‖ := by
  let Z (y : Point) := c + r • y
  let A := frobeniusCoordinateEquiv.toContinuousLinearMap
  let u (y : Point) := A (v (Z y))
  have hZ : HasFDerivAt Z (r • ContinuousLinearMap.id ℝ Point) 0 :=
    ((hasFDerivAt_id (0 : Point)).const_smul r).const_add c
  have hZ₀ : Z 0 = c := by simp [Z]
  have huv : HasFDerivAt v (fderiv ℝ v c) (Z 0) := hZ₀.symm ▸ hv.hasFDerivAt
  let Du : Point →L[ℝ] Ambient 5 := A.comp ((fderiv ℝ v c).comp (r • ContinuousLinearMap.id ℝ Point))
  have hDu : HasFDerivAt u Du 0 := A.hasFDerivAt.comp 0 (huv.comp 0 hZ)
  have hCol (i : Fin 3) : r * ‖ClassicalGradient v c i‖ ≤ ‖fderiv ℝ u 0‖ := by
    have hi : ‖axis i‖ = 1 := by simp [axis]
    have he : (fderiv ℝ u 0) (axis i) = r • A (ClassicalGradient v c i) := by
      calc
        _ = Du (axis i) := DFunLike.congr_fun hDu.fderiv (axis i)
        _ = A ((fderiv ℝ v c) (r • axis i)) := rfl
        _ = A (r • ClassicalGradient v c i) := congrArg A ((fderiv ℝ v c).map_smul r (axis i))
        _ = _ := A.map_smul r (ClassicalGradient v c i)
    have hB := (fderiv ℝ u 0).le_opNorm (axis i)
    rw [he, hi, mul_one, norm_smul, Real.norm_of_nonneg hr.le] at hB
    exact (show ‖A (ClassicalGradient v c i)‖ = ‖ClassicalGradient v c i‖ from
      frobeniusCoordinateEquiv.norm_map _) ▸ hB
  have hG : r ^ 2 * gradientNormSq (ClassicalGradient v c) ≤ 3 * ‖fderiv ℝ u 0‖ ^ 2 := by
    rw [gradientNormSq_eq_sum_norm_sq, Finset.mul_sum]
    calc
      _ = ∑ i : Fin 3, (r * ‖ClassicalGradient v c i‖) ^ 2 := by simp only [mul_pow]
      _ ≤ ∑ _i : Fin 3, ‖fderiv ℝ u 0‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (mul_nonneg hr.le (norm_nonneg _)) (hCol i) 2
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hR := Real.sqrt_le_sqrt hG
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs, abs_of_pos hr,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq (norm_nonneg _)] at hR
  exact hR

/-- The native interior Poisson gradient estimate in the thesis's
Frobenius coordinates, with one constant for all centers and radii. -/
theorem interiorPoissonGradientEstimate : InteriorPoissonGradientEstimate := by
  obtain ⟨C, hC, hUnit⟩ := exists_unit_linearPoisson_gradient_bound
  refine ⟨Real.sqrt 3 * C, mul_pos (Real.sqrt_pos.2 (by norm_num)) hC, ?_⟩
  intro c r hr v F M K hv hEq hvB hFB
  let Z (y : Point) := c + r • y
  let w := v ∘ Z
  let L := frobeniusCoordinateEquiv.toContinuousLinearMap
  let u (y : Point) := L (w y)
  have hZ : MapsTo Z (ball (0 : Point) 1) (ball c r) := by
    intro y hy
    have hyN := mem_ball_zero_iff.1 hy
    change dist (c + r • y) c < r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    exact (mul_lt_mul_of_pos_left hyN hr).trans_eq (mul_one r)
  have hZd : ContDiff ℝ 2 Z := contDiff_const.add (contDiff_id.const_smul r)
  have hw : ContDiffOn ℝ 2 w (ball (0 : Point) 1) := hv.comp hZd.contDiffOn hZ
  have hu : ContDiffOn ℝ 2 u (ball (0 : Point) 1) := L.contDiff.comp_contDiffOn hw
  have hM := (norm_nonneg (v c)).trans (hvB _ (mem_ball_self hr))
  have hK := (norm_nonneg (F c)).trans (hFB _ (mem_ball_self hr))
  have huB (y : Point) (hy : y ∈ ball (0 : Point) 1) : ‖u y‖ ≤ M :=
    (frobeniusCoordinateEquiv.norm_map (w y)).le.trans (hvB _ (hZ hy))
  have hFu (y : Point) (hy : y ∈ ball (0 : Point) 1) : ‖laplacian u y‖ ≤ r ^ 2 * K := by
    have huL : laplacian u y = L (laplacian w y) := laplacian_compCLM isOpen_ball hw hy L
    have hL : laplacian w y = r ^ 2 • laplacian v (Z y) :=
      laplacian_affine_dilation isOpen_ball hv c r (hZ hy)
    calc
      _ = ‖L (r ^ 2 • laplacian v (Z y))‖ :=
        congrArg (fun z : Ambient 5 => ‖z‖) (huL.trans (congrArg L hL))
      _ = r ^ 2 * ‖((laplacian v (Z y) : S0) : Tensor)‖ := by
        rw [map_smul, norm_smul, Real.norm_of_nonneg (sq_nonneg r)]
        exact congrArg (r ^ 2 * ·) (frobeniusCoordinateEquiv.norm_map _)
      _ ≤ _ := mul_le_mul_of_nonneg_left ((hEq (Z y) (hZ hy)).symm ▸ hFB (Z y) (hZ hy)) (sq_nonneg r)
  have hCen := (hv c (mem_ball_self hr)).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hU := hUnit u M (r ^ 2 * K) hM (mul_nonneg (sq_nonneg r) hK) hu huB hFu
  exact (norm_gradient_scaled_le_frobenius_fderiv v c hr (hCen.differentiableAt two_ne_zero)).trans
    ((mul_le_mul_of_nonneg_left hU (Real.sqrt_nonneg _)).trans_eq (by ring))

end Thesis
