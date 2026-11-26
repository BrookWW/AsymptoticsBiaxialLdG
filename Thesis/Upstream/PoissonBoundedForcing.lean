module

public import Thesis.Upstream.PoissonGradientBound
import HolderToCK.Analysis.Poisson.PotentialTrace
import HolderToCK.Analysis.ClassicalEquation
import HarmonicMaps.Analysis.InteriorSobolevApproximation
import HarmonicMaps.Analysis.SobolevPostcompositionBasic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Bounded compactly supported forcing and the local weak Poisson equation. -/

public section

noncomputable section

open Filter HarmonicMaps HolderToCK MeasureTheory Metric Set
open scoped ContDiff Convolution ENNReal RealInnerProductSpace Topology

namespace Thesis

private theorem exists_smooth_bounded_potential_data_approximation {n q : ℕ}
    {g : Domain n → Ambient q} (hg : Integrable g volume) (hg₂ : MemLp g 2 volume)
    (hcg : HasCompactSupport g) {M : ℝ} (hgM : ∀ x, ‖g x‖ ≤ M) :
    ∃ (G : ℕ → Domain n → Ambient q) (S : ℝ),
      tsupport g ⊆ closedBall 0 S ∧
      (∀ k, tsupport (G k) ⊆ closedBall 0 S) ∧ (∀ k, ContDiff ℝ ∞ (G k)) ∧
      (∀ k x, ‖G k x‖ ≤ M) ∧ ∀ᵐ x ∂volume, Tendsto (fun k => G k x) atTop (𝓝 (g x)) := by
  let σ := compactDataApproximationScale
  let G (k : ℕ) := compactDataMollification g (σ k)
  obtain ⟨S, hS, hGsupport⟩ := compactDataMollification_fixedSupport hcg
  have hG (k : ℕ) : ContDiff ℝ ∞ (G k) := by
    change ContDiff ℝ ∞ (scaledMollifierKernel n (σ k) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)
    exact (scaledMollifierKernel_hasCompactSupport n (σ k)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (scaledMollifierKernel_contDiff n (σ k)) hg.locallyIntegrable
  have hGB (k : ℕ) (x : Domain n) : ‖G k x‖ ≤ M := by
    let ρ := scaledMollifierKernel n (σ k)
    calc
      _ ≤ ∫ y, ρ y * M := by
        apply norm_integral_le_of_norm_le ((scaledMollifierKernel_integrable n (σ k)).mul_const M)
        exact Eventually.of_forall fun y => by
          rw [norm_smul, Real.norm_of_nonneg (scaledMollifierKernel_nonneg n (σ k) y)]
          exact mul_le_mul_of_nonneg_left (hgM _) (scaledMollifierKernel_nonneg n (σ k) y)
      _ = _ := by rw [integral_mul_const, scaledMollifierKernel_integral_one, one_mul]
  let U : OpenDomain n := ⟨univ, isOpen_univ⟩
  have hgU : IntegrableOn g U.val := by simpa only [U, IntegrableOn, Measure.restrict_univ] using hg
  have hgU₂ : MemLp g 2 (volume.restrict U.val) := by simpa only [U, Measure.restrict_univ] using hg₂
  have hconv := (tendsto_eLpNorm_euclideanMollification_sub U g hgU hgU₂
    MeasurableSet.univ (show (univ : Set (Domain n)) ⊆ U.val from subset_rfl)).comp
    (tendsto_comap_iff.2 compactDataApproximationScale_tendsto)
  have hnorm : Tendsto (fun k => eLpNorm (G k - g) 2 volume) atTop (𝓝 0) := by
    change Tendsto (fun k => eLpNorm (fun x => G k x - g x) 2 volume) atTop (𝓝 0)
    simpa only [G, σ, euclideanMollification, zeroExtensionOn, U, indicator_univ, Measure.restrict_univ,
      compactDataMollification, Function.comp_def, Pi.sub_apply] using hconv
  have hmeasure : TendstoInMeasure volume G atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun k => (hG k).continuous.aestronglyMeasurable) hg.aestronglyMeasurable hnorm
  obtain ⟨κ, _, hAE⟩ := hmeasure.exists_seq_tendsto_ae
  exact ⟨G ∘ κ, S, hS, fun k => hGsupport (κ k), fun k => hG (κ k), fun k x => hGB (κ k) x, hAE⟩

/-- A bounded square-integrable forcing on a bounded measurable domain has
globally smooth approximants with the original amplitude bound. -/
theorem exists_smooth_bounded_L2_approximation {n q : ℕ}
    {U : Set (Domain n)} (hU : MeasurableSet U) (hBound : Bornology.IsBounded U)
    {f : Domain n → Ambient q} (hf : MemLp f 2 (volume.restrict U)) {M : ℝ}
    (hM : 0 ≤ M) (hB : ∀ᵐ x ∂volume.restrict U, ‖f x‖ ≤ M) :
    ∃ F : ℕ → Domain n → Ambient q, (∀ k, ContDiff ℝ ∞ (F k)) ∧
      (∀ k x, ‖F k x‖ ≤ M) ∧
      Tendsto (fun k => eLpNorm (F k - f) 2 (volume.restrict U)) atTop (𝓝 0) := by
  let f₀ := U.indicator f
  have hf₀ : MemLp f₀ 2 volume := (memLp_indicator_iff_restrict hU).2 hf
  have hB₀ : ∀ᵐ x ∂volume, ‖f₀ x‖ ≤ M := by
    filter_upwards [(ae_restrict_iff' hU).mp hB] with x hx
    by_cases hIn : x ∈ U
    · rw [show f₀ x = f x from indicator_of_mem hIn f]
      exact hx hIn
    · rw [show f₀ x = 0 from indicator_of_notMem hIn f, norm_zero]
      exact hM
  let g (x : Domain n) := if ‖f₀ x‖ ≤ M then f₀ x else 0
  have hEq : g =ᵐ[volume] f₀ := hB₀.mono fun x hx => if_pos hx
  have hg₂ : MemLp g 2 volume := hf₀.ae_eq hEq.symm
  have hgM (x : Domain n) : ‖g x‖ ≤ M := by
    by_cases h : ‖f₀ x‖ ≤ M
    · rwa [show g x = f₀ x from if_pos h]
    · rwa [show g x = 0 from if_neg h, norm_zero]
  have hSupport : Function.support g ⊆ U := by
    intro x hx
    by_contra hn
    have hx₀ : f₀ x = 0 := indicator_of_notMem hn f
    exact hx (by simp [g,hx₀])
  have hgc : HasCompactSupport g := hBound.isCompact_closure.of_isClosed_subset
    (isClosed_tsupport g) (closure_mono hSupport)
  have hg : Integrable g volume := by
    apply (integrableOn_iff_integrable_of_support_subset hSupport).mp
    letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hBound.measure_lt_top.ne
    exact (hg₂.mono_measure Measure.restrict_le_self).integrable (by norm_num)
  obtain ⟨F,_,_,_,hF,hFM,hAE⟩ := exists_smooth_bounded_potential_data_approximation hg hg₂ hgc hgM
  have hEq₀ : g =ᵐ[volume.restrict U] f₀ := ae_restrict_of_ae hEq
  have hEqU : g =ᵐ[volume.restrict U] f := hEq₀.trans
    ((ae_restrict_mem hU).mono (fun x hx => indicator_of_mem hx f))
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hBound.measure_lt_top.ne
  refine ⟨F,hF,hFM,?_⟩
  apply tendsto_eLpNorm_two_zero_of_dominated (g := fun _ : Domain n => (1 : ℝ)) (C := 2*M)
    (fun k => (hF k).continuous.aestronglyMeasurable.sub hf.1) (memLp_const _)
  · intro k
    filter_upwards [hB] with x hx
    change ‖F k x - f x‖ ≤ 2*M*‖(1:ℝ)‖
    rw [norm_one,mul_one]
    exact (norm_sub_le _ _).trans ((add_le_add (hFM k x) hx).trans_eq (by ring))
  · filter_upwards [ae_restrict_of_ae hAE,hEqU] with x hx hEqx
    simpa only [Pi.sub_apply,hEqx,sub_self] using hx.sub_const (f x)

private theorem measurePreserving_subtract_from_point {n : ℕ} (x : Domain n) :
    MeasurePreserving (fun z : Domain n => x - z) volume volume := by
  exact (volume : Measure (Domain n)).measurePreserving_sub_left x

private theorem kernel_conv_pointwise_limit_of_bounded_data {n q : ℕ}
    {k : Domain n → ℝ} (hk : LocallyIntegrable k volume)
    {G : ℕ → Domain n → Ambient q} {g : Domain n → Ambient q}
    (hG : ∀ j, Continuous (G j))
    {S M : ℝ}
    (hGS : ∀ j, tsupport (G j) ⊆ closedBall 0 S)
    (hGM : ∀ j z, ‖G j z‖ ≤ M)
    (hAE : ∀ᵐ z ∂volume, Tendsto (fun j => G j z) atTop (𝓝 (g z))) (x : Domain n) :
    Tendsto (fun j => ∫ z, k z • G j (x - z)) atTop (𝓝 (∫ z, k z • g (x - z))) := by
  let T := closedBall (0 : Domain n) (‖x‖ + S)
  let B := T.indicator fun z => M * ‖k z‖
  have hMp := measurePreserving_subtract_from_point x
  have hF (j : ℕ) : AEStronglyMeasurable (fun z => k z • G j (x - z)) volume :=
    hk.aestronglyMeasurable.smul (((hG j).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have hB : Integrable B volume := (integrable_indicator_iff measurableSet_closedBall).2
    ((hk.integrableOn_isCompact (isCompact_closedBall _ _)).norm.const_mul M)
  have hDom (j : ℕ) : ∀ᵐ z ∂volume, ‖k z • G j (x - z)‖ ≤ B z :=
    Eventually.of_forall fun z => by
      change ‖k z • G j (x - z)‖ ≤ T.indicator (fun y => M * ‖k y‖) z
      by_cases hz : z ∈ T
      · rw [indicator_of_mem hz, norm_smul]
        exact (mul_le_mul_of_nonneg_left (hGM j _) (norm_nonneg _)).trans_eq (mul_comm _ _)
      · rw [compactData_translate_eq_zero (hGS j) le_rfl hz, smul_zero, norm_zero, indicator_of_notMem hz]
  have hPoint : ∀ᵐ z ∂volume, Tendsto (fun j => k z • G j (x - z)) atTop (𝓝 (k z • g (x - z))) :=
    (hMp.quasiMeasurePreserving.ae hAE).mono fun z hz => tendsto_const_nhds.smul hz
  exact tendsto_integral_filter_of_dominated_convergence B (Eventually.of_forall hF)
    (Eventually.of_forall hDom) hB hPoint


private theorem integral_smul_tendsto_of_bounded_ae {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {a : X → ℝ} {V : ℕ → X → E} {v : X → E}
    (ha : AEStronglyMeasurable a μ) (hV : ∀ k, AEStronglyMeasurable (V k) μ)
    {A B : ℝ} (haB : ∀ᵐ x ∂μ, ‖a x‖ ≤ A) (hVB : ∀ k, ∀ᵐ x ∂μ, ‖V k x‖ ≤ B)
    (hAE : ∀ᵐ x ∂μ, Tendsto (fun k => V k x) atTop (𝓝 (v x))) :
    Tendsto (fun k => ∫ x, a x • V k x ∂μ) atTop (𝓝 (∫ x, a x • v x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => max A 0 * max B 0)
    (Eventually.of_forall fun k => ha.smul (hV k)) _ (integrable_const _)
    (hAE.mono fun _ h => tendsto_const_nhds.smul h)
  refine Eventually.of_forall fun k => ?_
  filter_upwards [haB, hVB k] with x hx hxG
  change ‖a x • V k x‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul (hx.trans (le_max_left _ _)) (hxG.trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)

private theorem integral_inner_tendsto_of_bounded_ae {E X : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {a : X → E} {V : ℕ → X → E} {v : X → E}
    (ha : AEStronglyMeasurable a μ) (hV : ∀ k, AEStronglyMeasurable (V k) μ)
    {A B : ℝ} (haB : ∀ᵐ x ∂μ, ‖a x‖ ≤ A) (hVB : ∀ k, ∀ᵐ x ∂μ, ‖V k x‖ ≤ B)
    (hAE : ∀ᵐ x ∂μ, Tendsto (fun k => V k x) atTop (𝓝 (v x))) :
    Tendsto (fun k => ∫ x, inner ℝ (V k x) (a x) ∂μ)
      atTop (𝓝 (∫ x, inner ℝ (v x) (a x) ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => max B 0 * max A 0)
    (Eventually.of_forall fun k => (hV k).inner ha) _ (integrable_const _)
    (hAE.mono fun _ h => h.inner tendsto_const_nhds)
  refine Eventually.of_forall fun k => ?_
  filter_upwards [haB, hVB k] with x hx hxG
  exact (norm_inner_le_norm _ _).trans (mul_le_mul (hxG.trans (le_max_left _ _))
    (hx.trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _))

private theorem memLp_two_bounded_ae_limit {E X : Type*} [NormedAddCommGroup E]
    [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {V : ℕ → X → E} {v : X → E}
    (hV : ∀ k, AEStronglyMeasurable (V k) μ) {B : ℝ} (hVB : ∀ k, ∀ᵐ x ∂μ, ‖V k x‖ ≤ B)
    (hAE : ∀ᵐ x ∂μ, Tendsto (fun k => V k x) atTop (𝓝 (v x))) : MemLp v 2 μ := by
  apply MemLp.of_bound (aestronglyMeasurable_of_tendsto_ae atTop hV hAE) B
  filter_upwards [hAE, ae_all_iff.2 hVB] with x hx hxB
  exact le_of_tendsto hx.norm (Eventually.of_forall hxB)

private theorem derivative_norm_bounded_pointwise_limit {n q : ℕ}
    {P : Domain n → Ambient q} {Pₖ : ℕ → Domain n → Ambient q}
    (hPk : ∀ k, ContDiff ℝ ∞ (Pₖ k)) (hLim : ∀ x, Tendsto (fun k => Pₖ k x) atTop (𝓝 (P x)))
    (hGrad : ∀ R : ℝ, ∃ L ≥ (0 : ℝ), ∀ k x, x ∈ closedBall 0 R → ‖fderiv ℝ (Pₖ k) x‖ ≤ L) :
    Continuous P := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  let R := ‖x‖ + 1
  obtain ⟨L, hL, hG⟩ := hGrad R
  have hLip (k : ℕ) : LipschitzOnWith (Real.toNNReal L) (Pₖ k) (closedBall 0 R) := by
    apply (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y _ => ((hPk k).differentiable (by simp) y))
    intro y hy
    change ‖fderiv ℝ (Pₖ k) y‖ ≤ (Real.toNNReal L : ℝ)
    rw [Real.coe_toNNReal _ hL]
    exact hG k y hy
  have hLIP : LipschitzOnWith (Real.toNNReal L) P (closedBall 0 R) :=
    LipschitzOnWith.of_dist_le_mul fun y hy z hz =>
      le_of_tendsto ((hLim y).dist (hLim z)) (Eventually.of_forall fun k => (hLip k).dist_le_mul y hy z hz)
  have hx : x ∈ ball 0 R := mem_ball_zero_iff.2 (lt_add_one _)
  exact (hLIP.continuousOn x (ball_subset_closedBall hx)).continuousAt
    (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)


private theorem bounded_ambient_poisson_graph_limit {n q : ℕ} (Ω : OpenDomain n)
    (hμ : volume Ω.val ≠ ⊤) {K : Set (Domain n)} (hK : IsCompact K) (hΩK : Ω.val ⊆ K)
    {Pₖ : ℕ → Domain n → Ambient q} {Dₖ : ℕ → Domain n → HarmonicMaps.Gradient n q}
    {Fₖ : ℕ → Domain n → Ambient q} {P F : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hPcont : ∀ k, Continuous (Pₖ k)) (hDcont : ∀ k i, Continuous (fun x => Dₖ k x i))
    (hFcont : ∀ k, Continuous (Fₖ k))
    (hPweak : ∀ k, HasWeakGradient Ω (Pₖ k) (Dₖ k)) (hWeak : ∀ k, WeakPoissonOn Ω (Dₖ k) (Fₖ k))
    {B : ℝ} (hPbound : ∀ k x, x ∈ Ω.val → ‖Pₖ k x‖ ≤ B)
    (hDbound : ∀ k i x, x ∈ Ω.val → ‖Dₖ k x i‖ ≤ B) (hFbound : ∀ k x, x ∈ Ω.val → ‖Fₖ k x‖ ≤ B)
    (hPlim : ∀ x, Tendsto (fun k => Pₖ k x) atTop (𝓝 (P x)))
    (hDlim : ∀ i x, Tendsto (fun k => Dₖ k x i) atTop (𝓝 (D x i)))
    (hFlim : ∀ᵐ x ∂volume, Tendsto (fun k => Fₖ k x) atTop (𝓝 (F x))) :
    MemW12 Ω P D ∧ WeakPoissonOn Ω D F := by
  let μ := (volume : Measure (Domain n)).restrict Ω.val
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hμ
  have hIn : ∀ᵐ x ∂μ, x ∈ Ω.val := ae_restrict_mem Ω.property.measurableSet
  have hPmeas (k : ℕ) : AEStronglyMeasurable (Pₖ k) μ := (hPcont k).aestronglyMeasurable
  have hDmeas (k : ℕ) (i : Fin n) : AEStronglyMeasurable (fun x => Dₖ k x i) μ :=
    (hDcont k i).aestronglyMeasurable
  have hFmeas (k : ℕ) : AEStronglyMeasurable (Fₖ k) μ := (hFcont k).aestronglyMeasurable
  have hPB (k : ℕ) : ∀ᵐ x ∂μ, ‖Pₖ k x‖ ≤ B := hIn.mono (hPbound k)
  have hDB (k : ℕ) (i : Fin n) : ∀ᵐ x ∂μ, ‖Dₖ k x i‖ ≤ B := hIn.mono (hDbound k i)
  have hFB (k : ℕ) : ∀ᵐ x ∂μ, ‖Fₖ k x‖ ≤ B := hIn.mono (hFbound k)
  have hPAE : ∀ᵐ x ∂μ, Tendsto (fun k => Pₖ k x) atTop (𝓝 (P x)) := Eventually.of_forall hPlim
  have hDAE (i : Fin n) : ∀ᵐ x ∂μ, Tendsto (fun k => Dₖ k x i) atTop (𝓝 (D x i)) :=
    Eventually.of_forall (hDlim i)
  have hFAE : ∀ᵐ x ∂μ, Tendsto (fun k => Fₖ k x) atTop (𝓝 (F x)) := ae_restrict_of_ae hFlim
  have hPLp := memLp_two_bounded_ae_limit hPmeas hPB hPAE
  have hDLp (i : Fin n) := memLp_two_bounded_ae_limit (fun k => hDmeas k i) (fun k => hDB k i) (hDAE i)
  have hFLp := memLp_two_bounded_ae_limit hFmeas hFB hFAE
  have hPI : IntegrableOn P Ω.val volume := hPLp.integrable (by norm_num)
  have hDI (i : Fin n) : IntegrableOn (fun x => D x i) Ω.val volume := (hDLp i).integrable (by norm_num)
  have hFI : IntegrableOn F Ω.val volume := hFLp.integrable (by norm_num)
  refine ⟨⟨⟨hPI.locallyIntegrableOn, fun i => (hDI i).locallyIntegrableOn, ?_⟩, hPLp, hDLp⟩,
    ⟨hFI.locallyIntegrableOn, ?_⟩⟩
  · intro i φ hφ hcφ hsφ
    let dφ := coordinateDerivative φ hφ i
    have hdφ : Continuous dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hdφ.continuousOn
    obtain ⟨C', hC'⟩ := hK.exists_bound_of_continuousOn hφ.continuous.continuousOn
    have h := integral_smul_tendsto_of_bounded_ae (μ := μ) hdφ.aestronglyMeasurable hPmeas
      (hIn.mono fun x hx => hC _ (hΩK hx)) hPB hPAE
    have h' := integral_smul_tendsto_of_bounded_ae (μ := μ) hφ.continuous.aestronglyMeasurable
      (fun k => hDmeas k i) (hIn.mono fun x hx => hC' _ (hΩK hx)) (fun k => hDB k i) (hDAE i)
    exact tendsto_nhds_unique h (h'.neg.congr fun k => ((hPweak k).2.2 i φ hφ hcφ hsφ).symm)
  · intro ψ hψ hcψ hsψ
    let A (i : Fin n) (x : Domain n) := fderiv ℝ ψ x (EuclideanSpace.single i 1)
    have hA (i : Fin n) : Continuous (A i) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hI (i : Fin n) :
        Integrable (fun x => inner ℝ (D x i) (A i x)) μ := by
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hA i).continuousOn
      have hMeas : AEStronglyMeasurable (fun x => inner ℝ (D x i) (A i x)) μ :=
        (hDLp i).1.inner (hA i).aestronglyMeasurable
      apply (MemLp.of_bound (p := 1) hMeas (max B 0 * max C 0) ?_).integrable (by norm_num)
      filter_upwards [hIn, hDAE i, ae_all_iff.2 (fun k => hDB k i)] with x hx hdx hdxB
      have hdx' := le_of_tendsto hdx.norm (Eventually.of_forall hdxB)
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (hdx'.trans (le_max_left _ _))
        ((hC x (hΩK hx)).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _))
    have hF (i : Fin n) (k : ℕ) : Integrable (fun x => inner ℝ (Dₖ k x i) (A i x)) μ :=
      (((hDcont k i).inner (hA i)).continuousOn.integrableOn_compact hK).mono_set hΩK
    have hL (i : Fin n) : Tendsto (fun k => ∫ x, inner ℝ (Dₖ k x i) (A i x) ∂μ) atTop
        (𝓝 (∫ x, inner ℝ (D x i) (A i x) ∂μ)) := by
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hA i).continuousOn
      exact integral_inner_tendsto_of_bounded_ae (hA i).aestronglyMeasurable (fun k => hDmeas k i)
        (hIn.mono fun x hx => hC _ (hΩK hx)) (fun k => hDB k i) (hDAE i)
    have hSum : Tendsto (fun k => ∫ x, ∑ i : Fin n, inner ℝ (Dₖ k x i) (A i x) ∂μ)
        atTop (𝓝 (∫ x, ∑ i : Fin n, inner ℝ (D x i) (A i x) ∂μ)) := by
      simpa only [integral_finsetSum _ (fun i _ => hI i), integral_finsetSum _ (fun i _ => hF i _)] using
        tendsto_finsetSum Finset.univ (fun i _ => hL i)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hψ.continuous.continuousOn
    have hFright := integral_inner_tendsto_of_bounded_ae hψ.continuous.aestronglyMeasurable hFmeas
      (hIn.mono fun x hx => hC _ (hΩK hx)) hFB hFAE
    have hFint : IntegrableOn (fun x => inner ℝ (F x) (ψ x)) Ω.val volume := by
      apply (MemLp.of_bound (p := 1) (hFLp.1.inner hψ.continuous.aestronglyMeasurable)
        (max B 0 * max C 0) ?_).integrable (by norm_num)
      filter_upwards [hIn, hFAE, ae_all_iff.2 hFB] with x hx hfx hfxB
      have hfB := le_of_tendsto hfx.norm (Eventually.of_forall hfxB)
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (hfB.trans (le_max_left _ _))
        ((hC x (hΩK hx)).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _))
    exact ⟨integrable_finsetSum _ (fun i _ => hI i), hFint, tendsto_nhds_unique hSum
      (hFright.neg.congr fun k => ((hWeak k).2 ψ hψ hcψ hsψ).2.2.symm)⟩


private theorem exists_uniform_newtonian_value_column_bounds {q : ℕ}
    {G : ℕ → Domain 3 → Ambient q} {S M : ℝ} (hM : 0 ≤ M)
    (hG : ∀ k, Continuous (G k)) (hGS : ∀ k, tsupport (G k) ⊆ closedBall 0 S)
    (hGM : ∀ k x, ‖G k x‖ ≤ M) (R : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ k x, x ∈ closedBall (0 : Domain 3) R →
      ‖newtonianPotential (by decide : 2 ≤ 3) (G k) x‖ ≤ C ∧
      ∀ i : Fin 3, ‖potentialGradientColumn i (G k) x‖ ≤ C := by
  let E₀ := M * ∫ z in closedBall (0 : Domain 3) (R + S),
    ‖fundamentalPowerExpression z‖
  let E (i : Fin 3) := M * ∫ z in closedBall (0 : Domain 3) (R + S),
    ‖(euclideanSphereArea 3)⁻¹ * ‖z‖ ^ (-(3 : ℝ)) * z i‖
  have hE₀ : 0 ≤ E₀ := mul_nonneg hM (integral_nonneg fun _ => norm_nonneg _)
  have hE (i : Fin 3) : 0 ≤ E i := mul_nonneg hM (integral_nonneg fun _ => norm_nonneg _)
  let C := E₀ + ∑ i, E i
  have hC : E₀ ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hE i)
  have hCE (i : Fin 3) : E i ≤ C :=
    (Finset.single_le_sum (fun j _ => hE j) (Finset.mem_univ i)).trans (le_add_of_nonneg_left hE₀)
  refine ⟨C, hE₀.trans hC, fun k x hx => ?_⟩
  have hGc : HasCompactSupport (G k) :=
    (isCompact_closedBall (0 : Domain 3) S).of_isClosed_subset (isClosed_tsupport _) (hGS k)
  constructor
  · rw [newtonianPotential_eq_power (by decide : 3 ≤ 3)]
    exact (locallyIntegrableKernel_compactData_norm_bound (fundamentalPower_locallyIntegrable (by decide))
      (hG k) hGc (hGS k) (hGM k) (mem_closedBall_zero_iff.1 hx)).trans hC
  · intro i
    exact (locallyIntegrableKernel_compactData_norm_bound
      (normalizedRadialColumn_locallyIntegrable (by decide : 0 < 3) i)
      (hG k) hGc (hGS k) (hGM k) (mem_closedBall_zero_iff.1 hx)).trans (hCE i)

/-- A bounded compact datum has the actual Newtonian potential and weak
columns. On every bounded open set they give the weak equation. -/
theorem bounded_compact_newtonian_weakGraph {q : ℕ} {g : Domain 3 → Ambient q}
    (hg : Integrable g volume) (hg₂ : MemLp g 2 volume)
    (hcg : HasCompactSupport g) {M : ℝ} (hgM : ∀ x, ‖g x‖ ≤ M) :
    let P := newtonianPotential (by decide : 2 ≤ 3) g
    let D := fun x i => potentialGradientColumn i g x
    Continuous P ∧ ∀ Ω : OpenDomain 3, Bornology.IsBounded Ω.val →
      MemW12 Ω P D ∧ WeakPoissonOn Ω D g := by
  let hn : 2 ≤ 3 := by decide
  let P := newtonianPotential hn g
  let D (x : Domain 3) (i : Fin 3) := potentialGradientColumn i g x
  have hM : 0 ≤ M := (norm_nonneg (g 0)).trans (hgM 0)
  obtain ⟨G, S, _, hGS, hG, hGM, hAE⟩ := exists_smooth_bounded_potential_data_approximation hg hg₂ hcg hgM
  let Pk (k : ℕ) := newtonianPotential hn (G k)
  let Dk (k : ℕ) (x : Domain 3) (i : Fin 3) := potentialGradientColumn i (G k) x
  have hGc (k : ℕ) : HasCompactSupport (G k) :=
    (isCompact_closedBall (0 : Domain 3) S).of_isClosed_subset (isClosed_tsupport _) (hGS k)
  have hPk (k : ℕ) : ContDiff ℝ ∞ (Pk k) := newtonianPotential_contDiff hn (hG k) (hGc k)
  have hDk (k : ℕ) (i : Fin 3) : Continuous (fun x => Dk k x i) :=
    potentialGradientColumn_continuous (by decide : 0 < 3) i (hG k).continuous (hGc k)
  have hEqD (k : ℕ) : (fun x i => fderiv ℝ (Pk k) x (EuclideanSpace.single i 1)) = Dk k := by
    funext x i
    exact newtonianPotential_column_eq_gradient hn i
      ((hG k).of_le (WithTop.coe_le_coe.mpr le_top)) (hGc k) x
  have hPlim (x : Domain 3) : Tendsto (fun k => Pk k x) atTop (𝓝 (P x)) := by
    simp only [Pk, P, newtonianPotential_eq_power (by decide : 3 ≤ 3)]
    exact kernel_conv_pointwise_limit_of_bounded_data (fundamentalPower_locallyIntegrable (by decide))
      (fun k => (hG k).continuous) hGS hGM hAE x
  have hDlim (i : Fin 3) (x : Domain 3) : Tendsto (fun k => Dk k x i) atTop (𝓝 (D x i)) :=
    kernel_conv_pointwise_limit_of_bounded_data (normalizedRadialColumn_locallyIntegrable (by decide) i)
      (fun k => (hG k).continuous) hGS hGM hAE x
  have hBound := exists_uniform_newtonian_value_column_bounds hM (fun k => (hG k).continuous) hGS hGM
  have hGrad (R : ℝ) : ∃ L ≥ (0 : ℝ), ∀ k x, x ∈ closedBall (0 : Domain 3) R → ‖fderiv ℝ (Pk k) x‖ ≤ L := by
    obtain ⟨C, hC, hCk⟩ := hBound R
    refine ⟨Real.sqrt 3 * C, mul_nonneg (Real.sqrt_nonneg _) hC, fun k x hx => ?_⟩
    apply norm_linearMap_le_of_columns_bound _ hC
    intro i
    exact (congrArg (fun z : Ambient q => ‖z‖) (congrFun (congrFun (hEqD k) x) i)).le.trans
      ((hCk k x hx).2 i)
  refine ⟨derivative_norm_bounded_pointwise_limit hPk hPlim hGrad, fun Ω hΩB => ?_⟩
  obtain ⟨R, hR⟩ := hΩB.subset_closedBall (0 : Domain 3)
  have hμ : volume Ω.val ≠ ⊤ := ((measure_mono hR).trans_lt measure_closedBall_lt_top).ne
  obtain ⟨C, _, hCk⟩ := hBound R
  have hPweak (k : ℕ) : HasWeakGradient Ω (Pk k) (Dk k) :=
    hEqD k ▸ hasWeakGradient_of_contDiffOn_one Ω
      (((hPk k).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn)
  have hEq (k : ℕ) : WeakPoissonOn Ω (Dk k) (G k) := by
    rw [← hEqD]
    apply weakPoissonOn_of_contDiffOn_two_of_laplacian_eq Ω
      (((hPk k).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn)
    intro x _
    obtain ⟨L, hL, hHolder⟩ := smooth_compactly_supported_holder_one (hG k) (hGc k)
    exact newtonianPotential_laplacian hn (hG k) (hGc k) zero_lt_one hL hHolder x
  exact bounded_ambient_poisson_graph_limit Ω hμ (isCompact_closedBall _ _) hR
    (fun k => (hPk k).continuous) hDk (fun k => (hG k).continuous) hPweak hEq
    (fun k x hx => ((hCk k x (hR hx)).1.trans (le_max_left C M)))
    (fun k i x hx => ((hCk k x (hR hx)).2 i).trans (le_max_left C M))
    (fun k x _ => (hGM k x).trans (le_max_right C M)) hPlim hDlim hAE

end Thesis
