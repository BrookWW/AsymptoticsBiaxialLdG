module

public import Thesis.Definitions

/-! Locality, uniqueness, and classical representatives of the actual weak gradient. -/

public section

open Set Filter MeasureTheory Topology
open scoped ContDiff Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

-- Explicit routes through the Frobenius normed structure for the inherited product topology.
local instance : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

local instance : IsUniformAddGroup S0 := by
  letI : UniformSpace S0 :=
    (inferInstance : NormedAddCommGroup S0).toMetricSpace.toPseudoMetricSpace.toUniformSpace
  exact inferInstanceAs (IsUniformAddGroup S0)

local instance : CompleteSpace S0 := FiniteDimensional.complete ℝ S0

local instance : TopologicalSpace.PseudoMetrizableSpace S0 := by
  let metric := (inferInstance : NormedAddCommGroup S0).toMetricSpace
  letI : TopologicalSpace S0 := metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace S0)

variable {Ω U : Set Point}

theorem SmoothTest.mono {φ : Point → ℝ} (hφ : SmoothTest U φ) (hU : U ⊆ Ω) :
    SmoothTest Ω φ :=
  ⟨hφ.1, hφ.2.1, hφ.2.2.trans hU⟩

theorem SmoothTest.eq_zero_of_notMem {φ : Point → ℝ} (hφ : SmoothTest Ω φ)
    {x : Point} (hx : x ∉ Ω) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hφ.2.2 h)

theorem SmoothTest.coordDeriv_eq_zero_of_notMem {φ : Point → ℝ} (hφ : SmoothTest Ω φ)
    (j : Fin 3) {x : Point} (hx : x ∉ Ω) : coordDeriv j φ x = 0 := by
  unfold coordDeriv
  rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hφ.2.2 h))]
  rfl

/-- Coordinate derivatives preserve smooth test functions and their support constraint. -/
theorem SmoothTest.coordDeriv {φ : Point → ℝ} (hφ : SmoothTest Ω φ) (j : Fin 3) :
    SmoothTest Ω (Thesis.coordDeriv j φ) := by
  refine ⟨?_, hφ.2.1.fderiv_apply ℝ (axis j), ?_⟩
  · exact (hφ.1.fderiv_right (by simp)).clm_apply contDiff_const
  · exact (tsupport_fderiv_apply_subset ℝ (axis j)).trans hφ.2.2

theorem SmoothTest.setIntegral_smul_eq_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {φ : Point → ℝ} (hφ : SmoothTest Ω φ) (v : Point → E) :
    (∫ x in Ω, φ x • v x) = ∫ x, φ x • v x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [hφ.eq_zero_of_notMem hx, zero_smul]

theorem SmoothTest.integrable_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : Point → ℝ} (hφ : SmoothTest Ω φ) {v : Point → E}
    (hv : LocallyIntegrableOn v Ω volume) :
    Integrable (fun x => φ x • v x) volume := by
  have hvSupport := hv.integrableOn_compact_subset hφ.2.2 hφ.2.1
  obtain ⟨C, hC⟩ := hφ.2.1.exists_bound_of_continuousOn hφ.1.continuous.continuousOn
  have hbound : ∀ᵐ x ∂volume.restrict (tsupport φ), ‖φ x‖ ≤ C :=
    (ae_restrict_mem (isClosed_tsupport φ).measurableSet).mono fun x hx => hC x hx
  have hi : IntegrableOn (fun x => φ x • v x) (tsupport φ) volume :=
    hvSupport.bdd_smul C hφ.1.continuous.aestronglyMeasurable hbound
  exact hi.integrable_of_forall_notMem_eq_zero fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

theorem IsWeakGradient.mono {u : Point → S0} {D : Point → Gradient}
    (h : IsWeakGradient Ω u D) (hU : U ⊆ Ω) : IsWeakGradient U u D := by
  intro j φ hφ
  have hφΩ := hφ.mono hU
  rw [(hφ.coordDeriv j).setIntegral_smul_eq_integral, hφ.setIntegral_smul_eq_integral,
    ← (hφΩ.coordDeriv j).setIntegral_smul_eq_integral, ← hφΩ.setIntegral_smul_eq_integral]
  exact h j φ hφΩ

theorem IsWeakGradient.congr_ae {u v : Point → S0} {D G : Point → Gradient}
    (h : IsWeakGradient Ω u D) (huv : u =ᵐ[volume.restrict Ω] v)
    (hDG : D =ᵐ[volume.restrict Ω] G) : IsWeakGradient Ω v G := by
  intro j φ hφ
  calc
    (∫ x in Ω, Thesis.coordDeriv j φ x • v x) = ∫ x in Ω, Thesis.coordDeriv j φ x • u x :=
      integral_congr_ae (huv.symm.mono fun x hx => congrArg (fun y => Thesis.coordDeriv j φ x • y) hx)
    _ = -(∫ x in Ω, φ x • D x j) := h j φ hφ
    _ = -(∫ x in Ω, φ x • G x j) :=
      congrArg Neg.neg (integral_congr_ae (hDG.mono fun x hx => congrArg (fun y => φ x • y j) hx))

/-- Locally integrable weak gradients of the same map coincide almost everywhere. -/
theorem IsWeakGradient.ae_eq {u : Point → S0} {D G : Point → Gradient}
    (hD : IsWeakGradient Ω u D) (hG : IsWeakGradient Ω u G) (hΩ : IsOpen Ω)
    (hDint : ∀ j, LocallyIntegrableOn (fun x => D x j) Ω volume)
    (hGint : ∀ j, LocallyIntegrableOn (fun x => G x j) Ω volume) :
    D =ᵐ[volume.restrict Ω] G := by
  have hcoord (j : Fin 3) : ∀ᵐ x ∂volume.restrict Ω, D x j = G x j := by
    have hzero := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hDint j).sub (hGint j)) (fun φ hφdiff hφcomp hφsub => by
        have hφ : SmoothTest Ω φ := ⟨hφdiff, hφcomp, hφsub⟩
        have heq : (∫ x in Ω, φ x • D x j) = ∫ x in Ω, φ x • G x j :=
          neg_injective ((hD j φ hφ).symm.trans (hG j φ hφ))
        simp only [Pi.sub_apply, smul_sub]
        rw [integral_sub (hφ.integrable_smul (hDint j)) (hφ.integrable_smul (hGint j)),
          ← hφ.setIntegral_smul_eq_integral, ← hφ.setIntegral_smul_eq_integral, heq, sub_self])
    filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
    exact sub_eq_zero.mp (hx hxΩ)
  exact (ae_all_iff.mpr hcoord).mono fun _ hx => funext hx

theorem continuousOn_coordDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : Point → E} (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω) (j : Fin 3) :
    ContinuousOn (coordDeriv j u) Ω :=
  (hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const

/-- The classical coordinate derivatives of a continuously differentiable map are its weak
derivatives on the open domain. -/
theorem isWeakGradient_of_contDiffOn {u : Point → S0} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 1 u Ω) : IsWeakGradient Ω u (ClassicalGradient u) := by
  intro j φ hφ
  have huInt := hu.continuousOn.locallyIntegrableOn (μ := volume) hΩ.measurableSet
  have hDuInt := (continuousOn_coordDeriv hΩ hu j).locallyIntegrableOn (μ := volume) hΩ.measurableSet
  have hipb := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (v := axis j)
    ((hφ.coordDeriv j).integrable_smul huInt) (hφ.integrable_smul hDuInt)
    (hφ.integrable_smul huInt)
    (fun x _ => hφ.1.differentiable (by simp) x)
    (fun x hx => (hu.differentiableOn one_ne_zero x (hφ.2.2 hx)).differentiableAt
      (hΩ.mem_nhds (hφ.2.2 hx)))
  rw [(hφ.coordDeriv j).setIntegral_smul_eq_integral, hφ.setIntegral_smul_eq_integral]
  exact neg_eq_iff_eq_neg.mp hipb.symm

theorem IsWeakGradient.ae_eq_classicalGradient {u v : Point → S0} {D : Point → Gradient}
    (hD : IsWeakGradient Ω u D) (hΩ : IsOpen Ω)
    (hDint : ∀ j, LocallyIntegrableOn (fun x => D x j) Ω volume)
    (hv : ContDiffOn ℝ 1 v Ω) (huv : u =ᵐ[volume.restrict Ω] v) :
    D =ᵐ[volume.restrict Ω] ClassicalGradient v :=
  (hD.congr_ae huv Filter.EventuallyEq.rfl).ae_eq (isWeakGradient_of_contDiffOn hΩ hv)
    hΩ hDint fun j => (continuousOn_coordDeriv hΩ hv j).locallyIntegrableOn hΩ.measurableSet

theorem MemH1.mono {u : Point → S0} {D : Point → Gradient}
    (h : MemH1 Ω u D) (hU : U ⊆ Ω) : MemH1 U u D := by
  have hm := Measure.restrict_mono_set (volume : Measure Point) hU
  exact ⟨h.1.mono_measure hm, fun j => (h.2.1 j).mono_measure hm, h.2.2.mono hU⟩

theorem MemH1.congr_ae {u v : Point → S0} {D G : Point → Gradient}
    (h : MemH1 Ω u D) (huv : u =ᵐ[volume.restrict Ω] v)
    (hDG : D =ᵐ[volume.restrict Ω] G) : MemH1 Ω v G :=
  ⟨(memLp_congr_ae huv).mp h.1,
    fun j => (memLp_congr_ae (hDG.mono fun _ hx => congrFun hx j)).mp (h.2.1 j),
    h.2.2.congr_ae huv hDG⟩

theorem MemH1.locallyIntegrableOn_map {u : Point → S0} {D : Point → Gradient}
    (h : MemH1 Ω u D) : LocallyIntegrableOn u Ω volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (h.1.locallyIntegrable (by norm_num))

theorem MemH1.locallyIntegrableOn_gradient {u : Point → S0} {D : Point → Gradient}
    (h : MemH1 Ω u D) (j : Fin 3) : LocallyIntegrableOn (fun x => D x j) Ω volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict ((h.2.1 j).locallyIntegrable (by norm_num))

theorem MemH1Loc.mono {u : Point → S0} {D : Point → Gradient}
    (h : MemH1Loc Ω u D) (hU : U ⊆ Ω) : MemH1Loc U u D :=
  fun W hW hWc => h W hW ⟨hWc.1, hWc.2.trans hU⟩

theorem MemH1.memH1Loc {u : Point → S0} {D : Point → Gradient}
    (h : MemH1 Ω u D) : MemH1Loc Ω u D :=
  fun _ _ hWc => h.mono (subset_closure.trans hWc.2)

theorem MemH1Loc.congr_ae {u v : Point → S0} {D G : Point → Gradient}
    (h : MemH1Loc Ω u D) (huv : u =ᵐ[volume.restrict Ω] v)
    (hDG : D =ᵐ[volume.restrict Ω] G) : MemH1Loc Ω v G := by
  intro W hW hWc
  have hWsub := subset_closure.trans hWc.2
  exact (h W hW hWc).congr_ae (ae_restrict_of_ae_restrict_of_subset hWsub huv)
    (ae_restrict_of_ae_restrict_of_subset hWsub hDG)

/-- The local formulation yields one weak gradient on the whole open domain because every
test support is contained in a relatively compact open set. -/
theorem MemH1Loc.isWeakGradient {u : Point → S0} {D : Point → Gradient}
    (h : MemH1Loc Ω u D) (hΩ : IsOpen Ω) : IsWeakGradient Ω u D := by
  intro j φ hφ
  obtain ⟨W, hW, hφW, hWΩ, hWcomp⟩ :=
    exists_open_between_and_isCompact_closure hφ.2.1 hΩ hφ.2.2
  have hφ' : SmoothTest W φ := ⟨hφ.1, hφ.2.1, hφW⟩
  rw [(hφ.coordDeriv j).setIntegral_smul_eq_integral, hφ.setIntegral_smul_eq_integral,
    ← (hφ'.coordDeriv j).setIntegral_smul_eq_integral, ← hφ'.setIntegral_smul_eq_integral]
  exact (h W hW ⟨hWcomp, hWΩ⟩).2.2 j φ hφ'

theorem MemH1Loc.locallyIntegrableOn_map {u : Point → S0} {D : Point → Gradient}
    (h : MemH1Loc Ω u D) (hΩ : IsOpen Ω) : LocallyIntegrableOn u Ω volume := by
  intro x hx
  obtain ⟨W, hW, hxW, hWΩ, hWcomp⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hΩ (singleton_subset_iff.mpr hx)
  have hxW' := hxW (mem_singleton x)
  have hloc := (h W hW ⟨hWcomp, hWΩ⟩).locallyIntegrableOn_map x hxW'
  rw [nhdsWithin_eq_nhds.mpr (hW.mem_nhds hxW')] at hloc
  exact hloc.filter_mono nhdsWithin_le_nhds

theorem MemH1Loc.locallyIntegrableOn_gradient {u : Point → S0} {D : Point → Gradient}
    (h : MemH1Loc Ω u D) (hΩ : IsOpen Ω) (j : Fin 3) :
    LocallyIntegrableOn (fun x => D x j) Ω volume := by
  intro x hx
  obtain ⟨W, hW, hxW, hWΩ, hWcomp⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hΩ (singleton_subset_iff.mpr hx)
  have hxW' := hxW (mem_singleton x)
  have hloc := (h W hW ⟨hWcomp, hWΩ⟩).locallyIntegrableOn_gradient j x hxW'
  rw [nhdsWithin_eq_nhds.mpr (hW.mem_nhds hxW')] at hloc
  exact hloc.filter_mono nhdsWithin_le_nhds

theorem MemH1Loc.ae_eq_gradient {u : Point → S0} {D G : Point → Gradient}
    (hD : MemH1Loc Ω u D) (hG : MemH1Loc Ω u G) (hΩ : IsOpen Ω) :
    D =ᵐ[volume.restrict Ω] G :=
  (hD.isWeakGradient hΩ).ae_eq (hG.isWeakGradient hΩ) hΩ
    (hD.locallyIntegrableOn_gradient hΩ) (hG.locallyIntegrableOn_gradient hΩ)

theorem MemH1Loc.ae_eq_classicalGradient {u v : Point → S0} {D : Point → Gradient}
    (hD : MemH1Loc Ω u D) (hΩ : IsOpen Ω)
    (hv : ContDiffOn ℝ 1 v Ω) (huv : u =ᵐ[volume.restrict Ω] v) :
    D =ᵐ[volume.restrict Ω] ClassicalGradient v :=
  (hD.isWeakGradient hΩ).ae_eq_classicalGradient hΩ (hD.locallyIntegrableOn_gradient hΩ) hv huv

private theorem memLp_restrict_of_continuousOn_compact_closure {f : Point → S0}
    (hU : MeasurableSet U) (hc : IsCompact (closure U)) (hf : ContinuousOn f (closure U)) :
    MemLp f 2 (volume.restrict U) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hf
  have hfinite : (volume : Measure Point) U ≠ ⊤ :=
    ne_of_lt ((measure_mono subset_closure).trans_lt hc.measure_lt_top)
  letI := isFiniteMeasure_restrict.mpr hfinite
  have hCae : ∀ᵐ x ∂volume.restrict U, ‖f x‖ ≤ C :=
    (ae_restrict_mem hU).mono fun x hx => hC x (subset_closure hx)
  exact (memLp_top_of_bound ((hf.mono subset_closure).aestronglyMeasurable hU) C hCae).mono_exponent
    le_top

/-- A classical map and its actual gradient belong to the local Sobolev space. -/
theorem memH1Loc_of_contDiffOn {u : Point → S0} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 1 u Ω) : MemH1Loc Ω u (ClassicalGradient u) := by
  intro W hW hWc
  have hsub : W ⊆ Ω := subset_closure.trans hWc.2
  exact ⟨memLp_restrict_of_continuousOn_compact_closure hW.measurableSet hWc.1
      (hu.continuousOn.mono hWc.2),
    fun j => memLp_restrict_of_continuousOn_compact_closure hW.measurableSet hWc.1
      ((continuousOn_coordDeriv hΩ hu j).mono hWc.2),
    (isWeakGradient_of_contDiffOn hΩ hu).mono hsub⟩

/-- Smooth compactly supported variations are admissible zero-trace Sobolev fields. -/
theorem hasZeroTrace_of_contDiff_hasCompactSupport {u : Point → S0} (hΩ : IsOpen Ω)
    (hu : ContDiff ℝ ∞ u) (huComp : HasCompactSupport u) (huSupp : tsupport u ⊆ Ω) :
    HasZeroTrace Ω u (ClassicalGradient u) := by
  have hμ : (volume : Measure Point).restrict Ω ≤ volume := Measure.restrict_le_self
  have huLp : MemLp u 2 volume := hu.continuous.memLp_of_hasCompactSupport huComp
  have hDLp (j : Fin 3) : MemLp (coordDeriv j u) 2 volume :=
    ((hu.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (huComp.fderiv_apply ℝ (axis j))
  refine ⟨⟨huLp.mono_measure hμ, fun j => (hDLp j).mono_measure hμ,
    isWeakGradient_of_contDiffOn hΩ (hu.of_le (by simp)).contDiffOn⟩, ?_⟩
  intro δ hδ
  refine ⟨u, hu, huComp, huSupp, ?_⟩
  simpa only [h1Deviation, ClassicalGradient, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, add_zero, ENNReal.ofReal_zero, lintegral_zero] using hδ

theorem MemH1.sub {u v : Point → S0} {D G : Point → Gradient}
    (hu : MemH1 Ω u D) (hv : MemH1 Ω v G) : MemH1 Ω (u - v) (D - G) := by
  refine ⟨hu.1.sub hv.1, fun j => (hu.2.1 j).sub (hv.2.1 j), ?_⟩
  intro j φ hφ
  have hφj := hφ.coordDeriv j
  simp only [Pi.sub_apply, smul_sub]
  rw [integral_sub (hφj.integrable_smul hu.locallyIntegrableOn_map).integrableOn
      (hφj.integrable_smul hv.locallyIntegrableOn_map).integrableOn,
    integral_sub (hφ.integrable_smul (hu.locallyIntegrableOn_gradient j)).integrableOn
      (hφ.integrable_smul (hv.locallyIntegrableOn_gradient j)).integrableOn,
    hu.2.2 j φ hφ, hv.2.2 j φ hφ]
  abel

theorem MemH1.const_smul {u : Point → S0} {D : Point → Gradient}
    (hu : MemH1 Ω u D) (c : ℝ) : MemH1 Ω (c • u) (c • D) := by
  refine ⟨hu.1.const_smul c, fun j => (hu.2.1 j).const_smul c, ?_⟩
  intro j φ hφ
  simp only [Pi.smul_apply, smul_comm _ c, integral_smul, hu.2.2 j φ hφ, smul_neg]

theorem MemH1.add {u v : Point → S0} {D G : Point → Gradient}
    (hu : MemH1 Ω u D) (hv : MemH1 Ω v G) : MemH1 Ω (u + v) (D + G) := by
  have hvNeg : (-1 : ℝ) • v = -v := by
    funext x
    exact neg_one_smul ℝ (v x)
  have hGNeg : (-1 : ℝ) • G = -G := by
    funext x j
    exact neg_one_smul ℝ (G x j)
  have h := hu.sub (hv.const_smul (-1 : ℝ))
  rwa [hvNeg, hGNeg, sub_neg_eq_add, sub_neg_eq_add] at h

theorem h1Deviation_congr_ae {u v u' v' : Point → S0} {D G D' G' : Point → Gradient}
    (hu : u =ᵐ[volume.restrict Ω] u') (hv : v =ᵐ[volume.restrict Ω] v')
    (hD : D =ᵐ[volume.restrict Ω] D') (hG : G =ᵐ[volume.restrict Ω] G') :
    h1Deviation Ω u v D G = h1Deviation Ω u' v' D' G' := by
  unfold h1Deviation
  refine lintegral_congr_ae ?_
  filter_upwards [hu, hv, hD, hG] with x hxU hxV hxD hxG
  rw [hxU, hxV, hxD, hxG]

theorem h1Deviation_mono {u v : Point → S0} {D G : Point → Gradient} (hU : U ⊆ Ω) :
    h1Deviation U u v D G ≤ h1Deviation Ω u v D G :=
  lintegral_mono' (Measure.restrict_mono_set volume hU) le_rfl

theorem StrongH1.mono {u : ℕ → Point → S0} {D : ℕ → Point → Gradient}
    {v : Point → S0} {G : Point → Gradient} (h : StrongH1 Ω u D v G) (hU : U ⊆ Ω) :
    StrongH1 U u D v G := by
  refine ⟨fun n => (h.1 n).mono hU, h.2.1.mono hU, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h.2.2
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun _ => h1Deviation_mono hU)

theorem mem_diff_singularSet_iff {u : Point → S0} {x : Point} :
    x ∈ Ω \ singularSet Ω u ↔
      ∃ (W : Set Point) (v : Point → S0), IsOpen W ∧ x ∈ W ∧ W ⊆ Ω ∧
        ContDiffOn ℝ ∞ v W ∧ u =ᵐ[volume.restrict W] v := by
  constructor
  · rintro ⟨hxΩ, hxS⟩
    by_contra h
    exact hxS ⟨hxΩ, h⟩
  · rintro ⟨W, v, hW, hxW, hWΩ, hv, hu⟩
    refine ⟨hWΩ hxW, ?_⟩
    rintro ⟨_, hno⟩
    exact hno ⟨W, v, hW, hxW, hWΩ, hv, hu⟩

theorem isOpen_diff_singularSet (u : Point → S0) : IsOpen (Ω \ singularSet Ω u) := by
  refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
  obtain ⟨W, v, hW, hxW, hWΩ, hv, hu⟩ := mem_diff_singularSet_iff.mp hx
  exact mem_of_superset (hW.mem_nhds hxW) fun y hy =>
    mem_diff_singularSet_iff.mpr ⟨W, v, hW, hy, hWΩ, hv, hu⟩

/-- The open regular part has one smooth representative of the given a.e. map. -/
theorem exists_regularRepresentative (u : Point → S0) (hΩ : IsOpen Ω) :
    ∃ v : Point → S0, v =ᵐ[volume.restrict Ω] u ∧ ContDiffOn ℝ ∞ v (Ω \ singularSet Ω u) := by
  classical
  let R := Ω \ singularSet Ω u
  have hloc (a : R) := mem_diff_singularSet_iff.mp a.2
  choose W f hW hxW hWΩ hf hu using hloc
  have hWR (a : R) : W a ⊆ R := fun _ hy =>
    mem_diff_singularSet_iff.mpr ⟨W a, f a, hW a, hy, hWΩ a, hf a, hu a⟩
  let v : Point → S0 := fun x => if h : x ∈ R then f ⟨x, h⟩ x else u x
  have hAgree (a : R) : EqOn v (f a) (W a) := by
    intro x hx
    let b : R := ⟨x, hWR a hx⟩
    have hbAE : u =ᵐ[volume.restrict (W b ∩ W a)] f b :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hu b)
    have haAE : u =ᵐ[volume.restrict (W b ∩ W a)] f a :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hu a)
    have hAE := hbAE.symm.trans haAE
    have hAgreeOverlap := Measure.eqOn_open_of_ae_eq hAE ((hW b).inter (hW a))
      ((hf b).continuousOn.mono inter_subset_left) ((hf a).continuousOn.mono inter_subset_right)
    change (if h : x ∈ R then f ⟨x, h⟩ x else u x) = _
    rw [dif_pos b.2]
    exact hAgreeOverlap ⟨hxW b, hx⟩
  have hv : ContDiffOn ℝ ∞ v R := by
    intro x hx
    let a : R := ⟨x, hx⟩
    have hn : W a ∈ 𝓝 x := (hW a).mem_nhds (hxW a)
    have heq : v =ᶠ[𝓝 x] f a := Eventually.mono hn fun _ hy => hAgree a hy
    exact (((hf a).contDiffAt hn).congr_of_eventuallyEq heq).contDiffWithinAt
  have hR : R = ⋃ a : R, W a := by
    apply Subset.antisymm
    · intro x hx
      exact mem_iUnion_of_mem ⟨x, hx⟩ (hxW ⟨x, hx⟩)
    · exact iUnion_subset hWR
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  letI := hTc.to_subtype
  have hR' : R = ⋃ a : T, W a := by
    calc
      R = ⋃ a : R, W a := hR
      _ = ⋃ a ∈ T, W a := hT.symm
      _ = ⋃ a : T, W a := by
        conv_rhs => rw [iUnion_subtype]
  have hvR : v =ᵐ[volume.restrict R] u := by
    unfold Filter.EventuallyEq
    rw [hR']
    apply (ae_restrict_iUnion_iff _ _).mpr
    intro a
    filter_upwards [(hu a.1).symm, ae_restrict_mem (hW a.1).measurableSet] with x hxu hxW
    exact (hAgree a.1 hxW).trans hxu
  refine ⟨v, (ae_restrict_iff' hΩ.measurableSet).mpr ?_, hv⟩
  have hs : MeasurableSet R := (isOpen_diff_singularSet (Ω := Ω) u).measurableSet
  filter_upwards [(ae_restrict_iff' hs).mp hvR] with x hx _
  by_cases hxR : x ∈ R
  · exact hx hxR
  · exact dif_neg hxR

theorem singularSet_congr_ae {u v : Point → S0} (h : u =ᵐ[volume.restrict Ω] v) :
    singularSet Ω u = singularSet Ω v := by
  have inclusion {f g : Point → S0} (hfg : f =ᵐ[volume.restrict Ω] g) :
      singularSet Ω f ⊆ singularSet Ω g := by
    rintro x ⟨hx, hno⟩
    refine ⟨hx, ?_⟩
    rintro ⟨W, w, hW, hxW, hWΩ, hw, hgw⟩
    have hfgW : f =ᵐ[volume.restrict W] g := ae_restrict_of_ae_restrict_of_subset hWΩ hfg
    exact hno ⟨W, w, hW, hxW, hWΩ, hw, hfgW.trans hgw⟩
  exact Subset.antisymm (inclusion h) (inclusion h.symm)

theorem MemH1Loc.exists_regularRepresentative {u : Point → S0} {D : Point → Gradient}
    (h : MemH1Loc Ω u D) (hΩ : IsOpen Ω) :
    ∃ v : Point → S0, v =ᵐ[volume.restrict Ω] u ∧ MemH1Loc Ω v D ∧
      ContDiffOn ℝ ∞ v (Ω \ singularSet Ω u) ∧
      D =ᵐ[volume.restrict (Ω \ singularSet Ω u)] ClassicalGradient v := by
  obtain ⟨v, hAE, hv⟩ := Thesis.exists_regularRepresentative u hΩ
  refine ⟨v, hAE, h.congr_ae hAE.symm EventuallyEq.rfl, hv, ?_⟩
  exact (h.mono sdiff_subset).ae_eq_classicalGradient (isOpen_diff_singularSet u)
    (.of_le hv (by simp)) (ae_restrict_of_ae_restrict_of_subset sdiff_subset hAE.symm)

end Thesis

end
