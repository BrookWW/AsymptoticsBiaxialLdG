module

public import Thesis.Foundation.FrobeniusInnerProduct

public import Thesis.Variational.H10FractionalEmbedding
public import Thesis.Variational.HilbertRangeDuality
public import Thesis.Variational.FractionalTransposition
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences

/-! The intrinsic fractional norm is the Hilbert norm of the closed
graph of the Gagliardo difference in two L² spaces. -/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Frobenius RealInnerProductSpace

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance fractionalFrobeniusInnerProduct : InnerProductSpace ℝ S0 := frobeniusInnerProductSpace

private theorem fractionalFrobenius_inner_eq (x y : S0) :
    inner ℝ x y = frobeniusS0 x y :=
  frobenius_inner_eq x y

private abbrev TensorL2 (μ : Measure Point) := Lp S0 2 μ
private abbrev TensorPairL2 (μ : Measure Point) := Lp S0 2 (μ.prod μ)
private abbrev FractionalGraphAmbient (μ : Measure Point) := WithLp 2 (TensorL2 μ × TensorPairL2 μ)

private def fractionalDifference (s : ℝ) (u : Point → S0) (z : Point × Point) : S0 :=
  (dist z.1 z.2 ^ ((3 + 2 * s) / 2))⁻¹ • (u z.1 - u z.2)

private theorem fractionalDifference_congr_ae
    {μ : Measure Point} (s : ℝ) {u v : Point → S0} (h : u =ᵐ[μ] v) :
    fractionalDifference s u =ᵐ[μ.prod μ] fractionalDifference s v := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h, Measure.quasiMeasurePreserving_snd.ae h]
    with z h₁ h₂
  simp only [fractionalDifference, h₁, h₂]

private theorem aestronglyMeasurable_fractionalDifference
    {μ : Measure Point} (s : ℝ) {u : Point → S0} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fractionalDifference s u) (μ.prod μ) := by
  have h₁ : AEStronglyMeasurable (u ∘ Prod.fst) (μ.prod μ) :=
    hu.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have h₂ : AEStronglyMeasurable (u ∘ Prod.snd) (μ.prod μ) :=
    hu.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hd : Measurable (fun z : Point × Point => (dist z.1 z.2 ^ ((3 + 2 * s) / 2))⁻¹) := by fun_prop
  exact hd.aestronglyMeasurable.smul (h₁.sub h₂)

private theorem fractionalDifference_tendsto_ae
    {μ : Measure Point} (s : ℝ) {u : ℕ → Point → S0} {v : Point → S0}
    (h : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
    ∀ᵐ z ∂μ.prod μ, Tendsto (fun n => fractionalDifference s (u n) z) atTop
      (𝓝 (fractionalDifference s v z)) := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h, Measure.quasiMeasurePreserving_snd.ae h]
    with z h₁ h₂
  exact (h₁.sub h₂).const_smul _

private def fractionalGraphSubmodule (s : ℝ) (μ : Measure Point) :
    Submodule ℝ (FractionalGraphAmbient μ) where
  carrier := {p | (p.snd : Point × Point → S0) =ᵐ[μ.prod μ] fractionalDifference s p.fst}
  zero_mem' := by
    change ((0 : TensorPairL2 μ) : Point × Point → S0) =ᵐ[μ.prod μ] fractionalDifference s (0 : TensorL2 μ)
    have h₀ := Lp.coeFn_zero S0 2 μ
    refine (Lp.coeFn_zero S0 2 (μ.prod μ)).trans ?_
    have hDiff : (0 : Point × Point → S0) =ᵐ[μ.prod μ] fractionalDifference s (0 : Point → S0) :=
      .of_forall fun z => by simp [fractionalDifference]
    exact hDiff.trans (fractionalDifference_congr_ae s h₀).symm
  add_mem' := by
    intro p q hp hq
    change (p.snd : Point × Point → S0) =ᵐ[μ.prod μ] fractionalDifference s p.fst at hp
    change (q.snd : Point × Point → S0) =ᵐ[μ.prod μ] fractionalDifference s q.fst at hq
    change ((p.snd + q.snd : TensorPairL2 μ) : Point × Point → S0) =ᵐ[μ.prod μ]
      fractionalDifference s (p.fst + q.fst : TensorL2 μ)
    have hAdd := fractionalDifference_congr_ae s (Lp.coeFn_add p.fst q.fst)
    filter_upwards [Lp.coeFn_add p.snd q.snd, hp, hq, hAdd] with z h₀ h₁ h₂ h₃
    rw [h₀, h₃]
    change p.snd z + q.snd z = fractionalDifference s ((p.fst : Point → S0) + (q.fst : Point → S0)) z
    rw [h₁, h₂]
    simp only [fractionalDifference, Pi.add_apply, smul_sub, smul_add]
    abel
  smul_mem' := by
    intro c p hp
    change (p.snd : Point × Point → S0) =ᵐ[μ.prod μ] fractionalDifference s p.fst at hp
    change ((c • p.snd : TensorPairL2 μ) : Point × Point → S0) =ᵐ[μ.prod μ]
      fractionalDifference s (c • p.fst : TensorL2 μ)
    have hScale := fractionalDifference_congr_ae s (Lp.coeFn_smul c p.fst)
    filter_upwards [Lp.coeFn_smul c p.snd, hp, hScale] with z h₀ h₁ h₂
    rw [h₀, h₂]
    change c • p.snd z = fractionalDifference s (c • (p.fst : Point → S0)) z
    rw [h₁]
    let d := (dist z.1 z.2 ^ ((3 + 2 * s) / 2))⁻¹
    let a := p.fst z.1
    let b := p.fst z.2
    change c • (d • (a - b)) = d • (c • a - c • b)
    exact (smul_comm c d (a - b)).trans (congrArg (d • ·) (smul_sub c a b))

private theorem isClosed_fractionalGraphSubmodule (s : ℝ) (μ : Measure Point) :
    IsClosed (fractionalGraphSubmodule s μ : Set (FractionalGraphAmbient μ)) := by
  apply IsSeqClosed.isClosed
  intro p v hp hLim
  have hFst : Tendsto (fun n => (p n).fst) atTop (𝓝 v.fst) :=
    (WithLp.fstL 2 ℝ (TensorL2 μ) (TensorPairL2 μ)).continuous.continuousAt.tendsto.comp hLim
  have hSnd : Tendsto (fun n => (p n).snd) atTop (𝓝 v.snd) :=
    (WithLp.sndL 2 ℝ (TensorL2 μ) (TensorPairL2 μ)).continuous.continuousAt.tendsto.comp hLim
  obtain ⟨κ,hκ,hκAe⟩ := (tendstoInMeasure_of_tendsto_Lp hFst).exists_seq_tendsto_ae
  obtain ⟨η,hη,hηAe⟩ := (tendstoInMeasure_of_tendsto_Lp (hSnd.comp hκ.tendsto_atTop)).exists_seq_tendsto_ae
  have hValue : ∀ᵐ x ∂μ, Tendsto (fun n => (p (κ (η n))).fst x) atTop (𝓝 (v.fst x)) :=
    hκAe.mono fun x hx => hx.comp hη.tendsto_atTop
  have hDiff : ∀ᵐ z ∂μ.prod μ,
      Tendsto (fun n => fractionalDifference s (p (κ (η n))).fst z) atTop
        (𝓝 (fractionalDifference s v.fst z)) := fractionalDifference_tendsto_ae s hValue
  have hGraph (n : ℕ) : (p (κ (η n))).snd =ᵐ[μ.prod μ] fractionalDifference s (p (κ (η n))).fst :=
    hp _
  change (v.snd : Point × Point → S0) =ᵐ[μ.prod μ] fractionalDifference s v.fst
  filter_upwards [hηAe,hDiff,ae_all_iff.mpr hGraph] with z h₁ h₂ h₃
  exact tendsto_nhds_unique (h₁.congr' (.of_forall h₃)) h₂

private instance fractionalGraphComplete (s : ℝ) (μ : Measure Point) :
    CompleteSpace (fractionalGraphSubmodule s μ) :=
  completeSpace_coe_iff_isComplete.2 (isClosed_fractionalGraphSubmodule s μ).isComplete


private theorem fractionalDifference_norm_sq (s : ℝ) (u : Point → S0) (z : Point × Point) :
    ‖fractionalDifference s u z‖ ^ 2 = ‖u z.1 - u z.2‖ ^ 2 / dist z.1 z.2 ^ (3 + 2 * s) := by
  let d := dist z.1 z.2
  have hd : 0 ≤ d := dist_nonneg
  have hPow : (d ^ ((3 + 2 * s) / 2)) ^ (2 : ℕ) = d ^ (3 + 2 * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd]
    congr 1
    push_cast
    ring
  have hNonneg : 0 ≤ (d ^ ((3 + 2 * s) / 2))⁻¹ :=
    inv_nonneg.mpr (Real.rpow_nonneg hd _)
  change ‖(d ^ ((3 + 2 * s) / 2))⁻¹ • (u z.1 - u z.2)‖ ^ 2 = _
  rw [norm_smul, Real.norm_of_nonneg hNonneg, mul_pow, inv_pow, hPow, div_eq_mul_inv]
  exact mul_comm _ _

private theorem fractionalEnergy_eq_lintegral_squares
    (s : ℝ) (U : Set Point) (u : Point → S0) (hu : AEStronglyMeasurable u (volume.restrict U)) :
    fractionalEnergy s U u =
      (∫⁻ x in U, ENNReal.ofReal (‖u x‖ ^ 2)) +
      (∫⁻ z, ENNReal.ofReal (‖fractionalDifference s u z‖ ^ 2)
        ∂(volume.restrict U).prod (volume.restrict U)) := by
  let μ := volume.restrict U
  let G (z : Point × Point) := ENNReal.ofReal (‖fractionalDifference s u z‖ ^ 2)
  have hG : AEMeasurable G (μ.prod μ) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((aestronglyMeasurable_fractionalDifference s hu).norm.aemeasurable.pow_const _)
  change _ = _ + (∫⁻ z, G z ∂μ.prod μ)
  rw [lintegral_prod _ hG]
  unfold fractionalEnergy
  congr 1
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  exact (congrArg ENNReal.ofReal (fractionalDifference_norm_sq s u (x,y))).symm

private theorem fractional_graph_memHs_and_norm
    (s : ℝ) (U : Set Point) (v : fractionalGraphSubmodule s (volume.restrict U)) :
    MemHs s U v.val.fst ∧ ‖v‖ = Real.sqrt ((fractionalEnergy s U v.val.fst).toReal) := by
  let μ := volume.restrict U
  let p := v.val
  have hV : AEStronglyMeasurable (p.fst : Point → S0) μ := Lp.aestronglyMeasurable _
  have hAe : (p.snd : Point × Point → S0) =ᵐ[μ.prod μ] fractionalDifference s p.fst := v.property
  have hInt :
      (∫⁻ z, ENNReal.ofReal (‖fractionalDifference s p.fst z‖ ^ 2) ∂μ.prod μ) =
        ENNReal.ofReal (‖p.snd‖ ^ 2) := by
    rw [← lintegral_sq_norm_lp (μ.prod μ) p.snd]
    apply lintegral_congr_ae
    filter_upwards [hAe] with z hz
    rw [hz]
  have hE : fractionalEnergy s U p.fst = ENNReal.ofReal (‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2) := by
    rw [fractionalEnergy_eq_lintegral_squares s U p.fst hV, lintegral_sq_norm_lp μ p.fst,
      hInt, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  change (AEStronglyMeasurable p.fst μ ∧ fractionalEnergy s U p.fst < ⊤) ∧
    ‖p‖ = Real.sqrt ((fractionalEnergy s U p.fst).toReal)
  rw [hE, ENNReal.toReal_ofReal (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact ⟨⟨hV, ENNReal.ofReal_lt_top⟩, WithLp.prod_norm_eq_of_L2 p⟩

private theorem exists_fractional_graph_of_memHs
    (s : ℝ) (U : Set Point) (u : Point → S0) (hu : MemHs s U u) :
    ∃ v : fractionalGraphSubmodule s (volume.restrict U), v.val.fst =ᵐ[volume.restrict U] u := by
  let μ := volume.restrict U
  let g := fractionalDifference s u
  have hEnergy := hu.2
  rw [fractionalEnergy_eq_lintegral_squares s U u hu.1, ENNReal.add_lt_top] at hEnergy
  have hU : MemLp u 2 μ := memLp_two_of_finite_tensor_square hu.1 hEnergy.1
  have hG : MemLp g 2 (μ.prod μ) :=
    memLp_two_of_finite_tensor_square (aestronglyMeasurable_fractionalDifference s hu.1) hEnergy.2
  let p : FractionalGraphAmbient μ := WithLp.toLp 2 (hU.toLp u, hG.toLp g)
  have hValue : (p.fst : Point → S0) =ᵐ[μ] u := hU.coeFn_toLp
  have hGraph : p ∈ fractionalGraphSubmodule s μ :=
    (hG.coeFn_toLp).trans (fractionalDifference_congr_ae s hValue).symm
  exact ⟨⟨p,hGraph⟩,hValue⟩

private def fractionalInclusion (s : ℝ) (μ : Measure Point) :
    fractionalGraphSubmodule s μ →L[ℝ] TensorL2 μ :=
  (WithLp.fstL 2 ℝ (TensorL2 μ) (TensorPairL2 μ)).comp (fractionalGraphSubmodule s μ).subtypeL

private theorem inner_tensorL2_eq_frobenius {μ : Measure Point} (u v : TensorL2 μ) :
    inner ℝ u v = ∫ x, frobeniusS0 (u x) (v x) ∂μ := by
  rw [L2.inner_def]
  exact integral_congr_ae (.of_forall fun x => fractionalFrobenius_inner_eq (u x) (v x))

private def fractionalAdjoint (s : ℝ) (μ : Measure Point) :
    TensorL2 μ →L[ℝ] fractionalGraphSubmodule s μ := ContinuousLinearMap.adjoint (𝕜 := ℝ) (fractionalInclusion s μ)

private theorem fractionalL2DualBound_of_adjoint
    (s : ℝ) (U : Set Point) (f : TensorL2 (volume.restrict U)) :
    FractionalL2DualBound s U f ‖fractionalAdjoint s (volume.restrict U) f‖ := by
  let μ := volume.restrict U
  let i := fractionalInclusion s μ
  let adj := fractionalAdjoint s μ
  change FractionalL2DualBound s U f ‖adj f‖
  refine ⟨norm_nonneg _,?_⟩
  intro u hu
  obtain ⟨v,hAe⟩ := exists_fractional_graph_of_memHs s U u hu
  have hi : (i v : Point → S0) =ᵐ[μ] u := hAe
  have hFrob : (∫ x in U, frobeniusS0 (u x) (f x)) = inner ℝ (i v) f := by
    rw [inner_tensorL2_eq_frobenius]
    exact integral_congr_ae (hi.mono fun x hx => congrArg (fun w => frobeniusS0 w (f x)) hx.symm)
  have hN := (fractional_graph_memHs_and_norm s U v).2
  rw [fractionalEnergy_congr_ae hAe] at hN
  rw [hFrob, ← hN, mul_comm]
  have hP : inner ℝ (i v) f = inner ℝ v (adj f) := (i.adjoint_inner_right v f).symm
  rw [hP]
  exact abs_real_inner_le_norm _ _

/-- The intrinsic fractional norm is recovered from its tests against
the ambient L² space. -/
theorem fractionalL2NormDuality : External.FractionalL2NormDuality := by
  intro U _ s _ _ u C hC h
  let μ := volume.restrict U
  let i := fractionalInclusion s μ
  let adj := fractionalAdjoint s μ
  have hAdj (f : TensorL2 μ) : |inner ℝ u f| ≤ C * ‖adj f‖ := by
    rw [inner_tensorL2_eq_frobenius]
    have hBound := fractionalL2DualBound_of_adjoint s U f
    exact h f ‖adj f‖ hBound
  have hLift := @exists_norm_le_of_adjoint_pairing (fractionalGraphSubmodule s μ) (TensorL2 μ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance i u C hC hAdj
  obtain ⟨v,hv,hNorm⟩ := hLift
  obtain ⟨hM,hN⟩ := fractional_graph_memHs_and_norm s U v
  change v.val.fst = u at hv
  rw [hv] at hM hN
  exact ⟨hM,hN.symm.trans_le hNorm⟩

/-- The intrinsic energy of a difference is controlled by the two
individual fractional energies. -/
theorem memHs_and_fractionalEnergy_sub_le {s : ℝ} {U : Set Point} {u v : Point → S0}
    (hu : MemHs s U u) (hv : MemHs s U v) :
    MemHs s U (u-v) ∧ fractionalEnergy s U (u-v) ≤ 2 * fractionalEnergy s U u + 2 * fractionalEnergy s U v := by
  let μ := volume.restrict U
  obtain ⟨p,hP⟩ := exists_fractional_graph_of_memHs s U u hu
  obtain ⟨q,hQ⟩ := exists_fractional_graph_of_memHs s U v hv
  let w := p - q
  have hW : (w.val.fst : Point → S0) =ᵐ[μ] u-v := by
    have h := Lp.coeFn_sub p.val.fst q.val.fst
    filter_upwards [h,hP,hQ] with x h₀ h₁ h₂
    exact h₀.trans (congrArg₂ (· - ·) h₁ h₂)
  have hf (z : fractionalGraphSubmodule s μ) :
      fractionalEnergy s U z.val.fst = ENNReal.ofReal (‖z‖ ^ 2) := by
    obtain ⟨hM,hN⟩ := fractional_graph_memHs_and_norm s U z
    rw [hN, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hM.2.ne]
  have hSq : ‖w‖ ^ 2 ≤ 2 * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
    calc
      _ ≤ (‖p‖ + ‖q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le p q) 2
      _ ≤ _ := by nlinarith only [sq_nonneg (‖p‖ - ‖q‖)]
  refine ⟨(fractional_graph_memHs_and_norm s U w).1.congr_ae hW,?_⟩
  calc
    fractionalEnergy s U (u-v) = ENNReal.ofReal (‖w‖ ^ 2) :=
      (fractionalEnergy_congr_ae hW).symm.trans (hf w)
    _ ≤ ENNReal.ofReal (2 * (‖p‖ ^ 2 + ‖q‖ ^ 2)) := ENNReal.ofReal_le_ofReal hSq
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← hf p, ← hf q,
        fractionalEnergy_congr_ae hP, fractionalEnergy_congr_ae hQ, mul_add]
      norm_num

end Thesis

end
