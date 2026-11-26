module

public import Thesis.External.DirichletPoissonRegularity
public import Thesis.External.DirichletPoissonHolder
import Thesis.Variational.ClassicalDirichletSobolev
import Thesis.Variational.ClosedDirichletC1Compactness
import Thesis.Variational.DirichletPoissonStability
import Thesis.Variational.WeakPoissonH10
import Thesis.Variational.GlobalDirichletSup
import Thesis.Upstream.PoissonBoundedForcing
import Thesis.Variational.BoundaryPoissonEstimate
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Bounded-force weak representatives from the pure classical Dirichlet
theory, with the original smooth lift. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

local instance globalApproxTensorENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

local instance globalApproxPointTensorENorm : ContinuousENorm Tensor :=
  @SeminormedAddGroup.toContinuousENorm Tensor inferInstance

local instance globalApproxPseudoMetrizable : TopologicalSpace.PseudoMetrizableSpace S0 := by
  let metric := (inferInstance : NormedAddCommGroup S0).toMetricSpace
  letI : TopologicalSpace S0 := metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace S0)

local instance globalApproxTensorPseudoMetrizable : TopologicalSpace.PseudoMetrizableSpace Tensor :=
  (inferInstance : TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))

theorem exists_bounded_projected_lift_forcing {U : Set Point} (hU : IsSmoothDomain U)
    {B : Point → S0} (hB : ContDiff ℝ ∞ B) {D : Point → Gradient} {F : Point → Tensor}
    (hP : IsWeakPoisson U D F)
    (hSup : ∃ M : ℝ, ∀ᵐ x ∂volume.restrict U, ‖F x‖ ≤ M) :
    ∃ M : ℝ, 0 ≤ M ∧ MemLp (fun x => traceFreeSymmetricPart (F x) - laplacian B x)
      2 (volume.restrict U) ∧ ∀ᵐ x ∂volume.restrict U, ‖traceFreeSymmetricPart (F x) - laplacian B x‖ ≤ M := by
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  obtain ⟨M,hM⟩ := hSup
  have hB₂ : ContDiffOn ℝ 2 B univ := hB.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top)
  have hC : Continuous (laplacian B) :=
    continuousOn_univ.1 (continuousOn_laplacian_of_contDiffOn_two isOpen_univ hB₂)
  obtain ⟨K,hK⟩ := hU.1.2.2.isCompact_closure.exists_bound_of_continuousOn hC.continuousOn
  let N := max M 0 + max K 0
  have hN : 0 ≤ N := add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hBd : ∀ᵐ x ∂μ, ‖traceFreeSymmetricPart (F x) - laplacian B x‖ ≤ N := by
    filter_upwards [hM,ae_restrict_mem hU.1.1.measurableSet] with x hM' hx
    exact (norm_sub_le _ _).trans (add_le_add ((norm_traceFreeSymmetricPart_le _).trans (hM'.trans (le_max_left _ _)))
      ((hK x (subset_closure hx)).trans (le_max_left _ _)))
  have hMeas : AEStronglyMeasurable F μ := hP.locallyIntegrable.aestronglyMeasurable
  have hMeas' : AEStronglyMeasurable (fun x => traceFreeSymmetricPart (F x) - laplacian B x) μ :=
    (traceFreeSymmetricPartCLM.continuous.comp_aestronglyMeasurable hMeas).sub hC.aestronglyMeasurable
  exact ⟨N,hN,MemLp.of_bound hMeas' N hBd,hBd⟩

private theorem exists_smooth_tensor_bounded_approximation {U : Set Point} (hU : IsBoundedDomain U)
    {f : Point → S0} (hf : MemLp f 2 (volume.restrict U))
    {M : ℝ} (hM : 0 ≤ M) (hBd : ∀ᵐ x ∂volume.restrict U, ‖f x‖ ≤ M) :
    ∃ F : ℕ → Point → S0, (∀ n, ContDiff ℝ ∞ (F n)) ∧ (∀ n x, ‖F n x‖ ≤ M) ∧
      Tendsto (fun n => eLpNorm (F n-f) 2 (volume.restrict U)) atTop (𝓝 0) := by
  let e := frobeniusCoordinateEquiv
  have hf' : MemLp (frobeniusField f) 2 (volume.restrict U) :=
    (frobeniusCoordinateEquiv_memLp_iff _ _ _).2 hf
  have hBd' : ∀ᵐ x ∂volume.restrict U, ‖frobeniusField f x‖ ≤ M :=
    hBd.mono fun x hx => (e.norm_map (f x)).le.trans hx
  obtain ⟨g,hg,hgBd,hconv⟩ := exists_smooth_bounded_L2_approximation
    hU.1.measurableSet hU.2.2 hf' hM hBd'
  let F (n : ℕ) := e.symm ∘ g n
  refine ⟨F,fun n => e.symm.contDiff.comp (hg n),fun n x => (e.symm.norm_map (g n x)).le.trans (hgBd n x),?_⟩
  apply hconv.congr
  intro n
  apply eLpNorm_congr_norm_ae
  exact Eventually.of_forall fun x => by
    change ‖g n x - e (f x)‖ = ‖e.symm (g n x) - f x‖
    calc
      ‖g n x - e (f x)‖ = ‖e.symm (g n x - e (f x))‖ := (e.symm.norm_map _).symm
      _ = _ := by rw [e.symm.map_sub, e.symm_apply_apply]

private theorem dirichlet_representative_of_bounded_L2
    (hClassical : External.ClassicalDirichletPoissonRegularity)
    (hHolder : External.GlobalDirichletPoissonGradientHolder)
    {U : Set Point} (hU : IsSmoothDomain U)
    {f : Point → S0} (hf : MemLp f 2 (volume.restrict U)) {M : ℝ} (hM : 0 ≤ M)
    (hBound : ∀ᵐ x ∂volume.restrict U, ‖f x‖ ≤ M)
    (w : H10 U)
    (hPair : ∀ z : H10 U, h10PrincipalPart U w z = ∫ x in U, frobeniusS0 (f x) (h10Value z x)) :
    ∃ v : Point → S0, h10Value w =ᵐ[volume.restrict U] v ∧
      ContDiffOn ℝ 1 v (closure U) ∧ EqOn v (fun _ => 0) (frontier U) := by
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  obtain ⟨F,hF,hFB,hFconv⟩ := exists_smooth_tensor_bounded_approximation hU.1 hf hM hBound
  choose v hReg hWall hEq using fun n => hClassical.smoothZeroTraceSolution hU (hF n)
  have hFmem (n : ℕ) : MemLp (F n) 2 μ :=
    MemLp.of_bound (hF n).continuous.aestronglyMeasurable M (Eventually.of_forall (hFB n))
  choose z hVal hGrad hWeak using fun n => exists_H10_of_classical_zeroTrace_Poisson hU
    (hReg n) (hWall n) (hFmem n) (hEq n)
  have hZ : Tendsto z atTop (𝓝 w) :=
    tendsto_h10_of_dirichletPoisson_L2 hU.1 hFmem hf hWeak hPair hFconv
  obtain ⟨A,hA,hAmp⟩ := exists_global_zeroTrace_laplacian_sup_bound hU.1
  have hLap (n : ℕ) (x : Point) (hx : x ∈ U) : ‖laplacian (v n) x‖ ≤ M := (congrArg Norm.norm (hEq n x hx)).le.trans (hFB n x)
  have hVnorm (n : ℕ) (x : Point) (hx : x ∈ closure U) : ‖v n x‖ ≤ A*M :=
    hAmp (hReg n) (hWall n) hM (hLap n) x hx
  obtain ⟨C,hC,hC1Estimate⟩ := hHolder U hU (1/2) (by norm_num) (by norm_num)
  have hC1 (n : ℕ) :
      (∀ x ∈ closure U, ‖closureGradient U (v n) x‖ ≤ C*(A*M+M)) ∧
      ∀ x ∈ closure U, ∀ y ∈ closure U,
        ‖v n x-v n y‖ + ‖closureGradient U (v n) x-closureGradient U (v n) y‖ ≤
          C*(A*M+M) * dist x y ^ (1/2 : ℝ) :=
    hC1Estimate (v n) (hReg n) (hWall n) (A*M) M (mul_nonneg hA.le hM) hM
      (fun x hx => hVnorm n x (subset_closure hx)) (hLap n)
  let L := C*(A*M+M)
  have hL : 0 ≤ L := mul_nonneg hC.le (add_nonneg (mul_nonneg hA.le hM) hM)
  let N := max (A*M) L
  have hN : 0 ≤ N := (mul_nonneg hA.le hM).trans (le_max_left _ _)
  have hNorm (n : ℕ) (x : Point) (hx : x ∈ closure U) :
      ‖((v n x,closureGradient U (v n) x) : S0 × Gradient)‖ ≤ N :=
    max_le ((hVnorm n x hx).trans (le_max_left _ _)) (((hC1 n).1 x hx).trans (le_max_right _ _))
  have hMod (n : ℕ) (x : Point) (hx : x ∈ closure U) (y : Point) (hy : y ∈ closure U) :
      dist ((v n x,closureGradient U (v n) x) : S0 × Gradient) (v n y,closureGradient U (v n) y) ≤
        L * dist x y ^ (1/2 : ℝ) := by
    rw [Prod.dist_eq,dist_eq_norm,dist_eq_norm]
    exact (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)).trans ((hC1 n).2 x hx y hy)
  obtain ⟨κ,u,_,hκ,hu,hConv,_,_⟩ := hU.exists_closedC1_subsequence hReg hN hL
    (show (0 : ℝ) < 1/2 by norm_num) hNorm hMod
  have hValLim : Tendsto (fun n => (z (κ n)).val.1) atTop (𝓝 w.val.1) :=
    (continuous_fst.comp continuous_subtype_val).continuousAt.tendsto.comp (hZ.comp hκ.tendsto_atTop)
  obtain ⟨ι,hι,hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hValLim).exists_seq_tendsto_ae
  have hUeq : h10Value w =ᵐ[μ] u := by
    filter_upwards [hAE,ae_all_iff.2 hVal,ae_restrict_mem hU.1.1.measurableSet] with x hx hxV hIn
    have hL := hx.congr (fun n => hxV (κ (ι n)))
    have hR := (hConv.tendsto_at (subset_closure hIn)).comp hι.tendsto_atTop
    exact tendsto_nhds_unique hL hR
  refine ⟨u,hUeq,hu,?_⟩
  intro x hx
  have h := hConv.tendsto_at (frontier_subset_closure hx)
  have hZ : Tendsto (fun n => v (κ n) x) atTop (𝓝 0) :=
    tendsto_const_nhds.congr (fun n => (hWall (κ n) hx).symm)
  exact tendsto_nhds_unique h hZ

/-- Bounded-force weak representatives follow from the classical smooth
Dirichlet theory and the quantitative estimate for classical gradients. -/
theorem globalDirichletPoissonRegularity_of_classical
    (hClassical : External.ClassicalDirichletPoissonRegularity)
    (hHolder : External.GlobalDirichletPoissonGradientHolder) :
    External.GlobalDirichletPoissonRegularity := by
  refine ⟨?_, hClassical.contDiffOn_succ⟩
  intro U u b D F hU hb hu hTr hW hBound
  obtain ⟨M,hM,hFmem,hFBd⟩ := exists_bounded_projected_lift_forcing hU hb hW hBound
  obtain ⟨w,hVal,hGrad⟩ := hTr.exists_H10_with_ae_data hU.1.1
  have hPair := h10PrincipalPart_eq_forcing_of_weakPoisson_lift hU.1.1 hu hW hb hFmem w hGrad
  obtain ⟨v,hvAE,hv,hvB⟩ := dirichlet_representative_of_bounded_L2 hClassical hHolder hU hFmem hM hFBd w hPair
  refine ⟨v+b,?_,hv.add (hb.contDiffOn.of_le (by simp)),?_⟩
  · filter_upwards [hVal,hvAE] with x hx hy
    have h := hx.symm.trans hy
    exact sub_eq_iff_eq_add.1 h
  · intro x hx
    change v x + b x = b x
    rw [hvB hx,zero_add]

end Thesis
