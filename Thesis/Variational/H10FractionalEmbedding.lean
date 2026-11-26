module

public import Thesis.Variational.FractionalSmoothEmbedding
public import Thesis.External.FractionalDirichlet
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences

/-! The frozen zero-trace graph embeds in the intrinsic fractional space. -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped BigOperators ContDiff ENNReal NNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private def smoothGraphSubmodule (U : Set Point) : Submodule ℝ (H1Graph U) where
  carrier := {p | ∃ φ : Point → S0, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
    (p.1 : Point → S0) =ᵐ[volume.restrict U] φ ∧
    ∀ j, (p.2 j : Point → S0) =ᵐ[volume.restrict U] coordDeriv j φ}
  zero_mem' := by
    have hZero := Lp.coeFn_zero S0 2 (volume.restrict U)
    refine ⟨0, contDiff_const, HasCompactSupport.zero, by simp, hZero, ?_⟩
    intro j
    have hD : coordDeriv j (0 : Point → S0) = 0 := by
      funext x
      change fderiv ℝ (fun _ : Point => (0 : S0)) x (axis j) = 0
      simp
    rw [hD]
    exact hZero
  add_mem' := by
    rintro p q ⟨φ,hφ,hφc,hφU,hφV,hφD⟩ ⟨ψ,hψ,hψc,hψU,hψV,hψD⟩
    refine ⟨φ + ψ, hφ.add hψ, hφc.add hψc, (tsupport_add _ _).trans (union_subset hφU hψU), ?_, ?_⟩
    · change ((p.1 + q.1 : Lp S0 2 (volume.restrict U)) : Point → S0) =ᵐ[volume.restrict U] φ + ψ
      filter_upwards [Lp.coeFn_add p.1 q.1, hφV, hψV] with x hP h₁ h₂
      exact hP.trans (congrArg₂ (· + ·) h₁ h₂)
    · intro j
      change ((p.2 j + q.2 j : Lp S0 2 (volume.restrict U)) : Point → S0) =ᵐ[volume.restrict U] coordDeriv j (φ + ψ)
      filter_upwards [Lp.coeFn_add (p.2 j) (q.2 j), hφD j, hψD j] with x hP h₁ h₂
      have hD : coordDeriv j (φ + ψ) x = coordDeriv j φ x + coordDeriv j ψ x :=
        DFunLike.congr_fun (fderiv_add (hφ.differentiable (by simp) x)
          (hψ.differentiable (by simp) x)) (axis j)
      exact hP.trans ((congrArg₂ (· + ·) h₁ h₂).trans hD.symm)
  smul_mem' := by
    rintro c p ⟨φ,hφ,hφc,hφU,hφV,hφD⟩
    have hC : HasCompactSupport (c • φ) := HasCompactSupport.smul_left (f := fun _ : Point => c) hφc
    have hT : tsupport (c • φ) ⊆ tsupport φ := tsupport_smul_subset_right (fun _ : Point => c) φ
    refine ⟨c • φ, hφ.const_smul c, hC, hT.trans hφU, ?_, ?_⟩
    · change ((c • p.1 : Lp S0 2 (volume.restrict U)) : Point → S0) =ᵐ[volume.restrict U] c • φ
      filter_upwards [Lp.coeFn_smul c p.1, hφV] with x hP hx
      exact hP.trans (congrArg (c • ·) hx)
    · intro j
      change ((c • p.2 j : Lp S0 2 (volume.restrict U)) : Point → S0) =ᵐ[volume.restrict U] coordDeriv j (c • φ)
      filter_upwards [Lp.coeFn_smul c (p.2 j), hφD j] with x hP hx
      have hD : coordDeriv j (c • φ) x = c • coordDeriv j φ x :=
        DFunLike.congr_fun (fderiv_const_smul (hφ.differentiable (by simp) x) c) (axis j)
      exact hP.trans ((congrArg (c • ·) hx).trans hD.symm)

/-- The approximants carry the simultaneous values and all three first
derivative columns of the frozen graph. -/
theorem H10.exists_smooth_graph_approximation {U : Set Point} (v : H10 U) :
    ∃ (p : ℕ → H1Graph U) (f : ℕ → Point → S0), Tendsto p atTop (𝓝 v.val) ∧
      ∀ n, ContDiff ℝ ∞ (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ U ∧
        (p n).1 =ᵐ[volume.restrict U] f n ∧
        ∀ j, (p n).2 j =ᵐ[volume.restrict U] coordDeriv j (f n) := by
  classical
  have hv := v.property
  change v.val ∈ closure ((Submodule.span ℝ (smoothGraphSubmodule U : Set (H1Graph U))) : Set (H1Graph U)) at hv
  rw [Submodule.span_eq] at hv
  obtain ⟨p,hp,hpLim⟩ := mem_closure_iff_seq_limit.mp hv
  choose f hf using hp
  exact ⟨p,f,hpLim,hf⟩

theorem eLpNorm_two_sq_eq_tensor_lintegral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (v : X → S0) :
    eLpNorm v 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (‖v x‖ ^ 2) ∂μ := by
  calc
    _ = ∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ := by
      simpa only [ENNReal.rpow_two, NNReal.coe_two, ENNReal.coe_two] using
        (eLpNorm_nnreal_pow_eq_lintegral (f := v) (μ := μ) (p := (2 : ℝ≥0)) (by norm_num))
    _ = _ := lintegral_congr fun x => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem lintegral_sq_norm_lp {X : Type*} [MeasurableSpace X] (μ : Measure X) (v : Lp S0 2 μ) :
    (∫⁻ x, ENNReal.ofReal (‖v x‖ ^ 2) ∂μ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← eLpNorm_two_sq_eq_tensor_lintegral μ, ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.memLp v).2.ne]

theorem memLp_two_of_finite_tensor_square {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u : X → S0} (hMeas : AEStronglyMeasurable u μ)
    (hFin : (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ) < ⊤) : MemLp u 2 μ := by
  refine ⟨hMeas, lt_top_iff_ne_top.2 ?_⟩
  intro hTop
  rw [← eLpNorm_two_sq_eq_tensor_lintegral μ, hTop, ENNReal.top_pow (by norm_num)] at hFin
  exact (lt_irrefl _ hFin)

/-- The compactly supported smooth field's global Dirichlet integral equals
the sum of the squares of its displayed (L^2(U)) columns. -/
theorem lintegral_smooth_gradient_eq_columns_norm_sq
    {U : Set Point} (hU : MeasurableSet U)
    (p : H1Graph U) (φ : Point → S0) (hφ : ContDiff ℝ ∞ φ) (hSupp : tsupport φ ⊆ U)
    (hGraph : ∀ j, (p.2 j : Point → S0) =ᵐ[volume.restrict U] coordDeriv j φ) :
    (∫⁻ x : Point, ENNReal.ofReal (∑ j : Fin 3, ‖coordDeriv j φ x‖ ^ 2)) =
      ENNReal.ofReal (∑ j : Fin 3, ‖p.2 j‖ ^ 2) := by
  let g (j : Fin 3) (x : Point) := ENNReal.ofReal (‖coordDeriv j φ x‖ ^ 2)
  have hMeas (j : Fin 3) : Measurable (g j) := by
    have hD : Continuous (coordDeriv j φ) :=
      (ContinuousLinearMap.apply ℝ S0 (axis j)).continuous.comp (hφ.continuous_fderiv (by simp))
    exact ENNReal.measurable_ofReal.comp (hD.norm.pow 2).measurable
  have hInt (j : Fin 3) : (∫⁻ x, g j x) = ∫⁻ x in U, g j x := by
    rw [← lintegral_indicator hU]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ U
    · exact (indicator_of_mem hx _).symm
    · rw [indicator_of_notMem hx]
      have hX : x ∉ tsupport (coordDeriv j φ) :=
        fun hy => hx (hSupp ((tsupport_fderiv_apply_subset ℝ (axis j)) hy))
      have h0 : coordDeriv j φ x = 0 := Function.notMem_support.mp
        (fun h => hX (subset_closure h))
      simp only [g, h0, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero]
  calc
    _ = ∑ j : Fin 3, ∫⁻ x, g j x := by
      simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      exact lintegral_finsetSum _ (fun j _ => hMeas j)
    _ = ∑ j : Fin 3, ENNReal.ofReal (‖p.2 j‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hInt j, ← lintegral_sq_norm_lp (volume.restrict U) (p.2 j)]
      apply lintegral_congr_ae
      filter_upwards [hGraph j] with x hx
      simp only [g, hx]
    _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)).symm

/-- The full gradient square integral of a compact smooth representative is
controlled by the norm of its original Sobolev graph. -/
theorem lintegral_smooth_gradient_le_norm_graph
    {U : Set Point} (hU : MeasurableSet U)
    (p : H1Graph U) (φ : Point → S0) (hφ : ContDiff ℝ ∞ φ) (hSupp : tsupport φ ⊆ U)
    (hGraph : ∀ j, (p.2 j : Point → S0) =ᵐ[volume.restrict U] coordDeriv j φ) :
    (∫⁻ x : Point, ENNReal.ofReal (∑ j : Fin 3, ‖coordDeriv j φ x‖ ^ 2)) ≤
      3 * ENNReal.ofReal (‖p‖ ^ 2) := by
  rw [lintegral_smooth_gradient_eq_columns_norm_sq hU p φ hφ hSupp hGraph,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  calc
    _ = ∑ j : Fin 3, ENNReal.ofReal (‖p.2 j‖ ^ 2) := rfl
    _ ≤ ∑ _ : Fin 3, ENNReal.ofReal (‖p‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      have hj : ‖p.2 j‖ ≤ ‖p‖ :=
        (norm_le_pi_norm p.2 j).trans (le_max_right ‖p.1‖ ‖p.2‖)
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hj 2)
    _ = _ := by simp [nsmul_eq_mul]

private theorem fractionalEnergy_le_of_smooth_graph
    {U : Set Point} (hU : IsBoundedDomain U) (s : ℝ) (hs : 0 < s) (hs₁ : s < 1) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (p : H1Graph U) (φ : Point → S0),
      ContDiff ℝ ∞ φ → tsupport φ ⊆ U →
      (p.1 : Point → S0) =ᵐ[volume.restrict U] φ →
      (∀ j, (p.2 j : Point → S0) =ᵐ[volume.restrict U] coordDeriv j φ) →
      fractionalEnergy s U φ ≤ C * ENNReal.ofReal (‖p‖ ^ 2) := by
  obtain ⟨K,hK,hBound⟩ := exists_fractionalEnergy_le_of_smooth hU s hs hs₁
  refine ⟨1 + K * 3, ENNReal.add_lt_top.2 ⟨by simp, ENNReal.mul_lt_top hK (by simp)⟩, ?_⟩
  intro p φ hφ hSupp hVal hGrad
  have hValLp : (∫⁻ x in U, ENNReal.ofReal (‖φ x‖ ^ 2)) = ENNReal.ofReal (‖p.1‖ ^ 2) := by
    rw [← lintegral_sq_norm_lp (volume.restrict U) p.1]
    apply lintegral_congr_ae
    filter_upwards [hVal] with x hx
    rw [hx]
  have hValLe : ENNReal.ofReal (‖p.1‖ ^ 2) ≤ ENNReal.ofReal (‖p‖ ^ 2) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (le_max_left ‖p.1‖ ‖p.2‖) 2)
  have hD := lintegral_smooth_gradient_le_norm_graph hU.1.measurableSet p φ hφ hSupp hGrad
  refine (hBound φ hφ).trans ?_
  rw [hValLp, add_mul, one_mul, mul_assoc]
  exact add_le_add hValLe (mul_le_mul' le_rfl hD)

@[expose] def fractionalPairEnergy (s : ℝ) (u : Point → S0) (z : Point × Point) : ℝ≥0∞ :=
  ENNReal.ofReal (‖u z.1 - u z.2‖ ^ 2 / dist z.1 z.2 ^ (3 + 2 * s))

theorem fractionalPairEnergy_aemeasurable {μ : Measure Point} (s : ℝ)
    {u : Point → S0} (hu : AEStronglyMeasurable u μ) :
    AEMeasurable (fractionalPairEnergy s u) (μ.prod μ) := by
  have h₁ : AEStronglyMeasurable (u ∘ Prod.fst) (μ.prod μ) := hu.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have h₂ : AEStronglyMeasurable (u ∘ Prod.snd) (μ.prod μ) := hu.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hD : Measurable (fun z : Point × Point => dist z.1 z.2 ^ (3 + 2 * s)) := by fun_prop
  exact ENNReal.measurable_ofReal.comp_aemeasurable (((h₁.sub h₂).norm.aemeasurable.pow_const _).div hD.aemeasurable)

private theorem nonlocal_energy_le_limit_bound_of_tendsto_ae
    {U : Set Point} (s : ℝ) {f : ℕ → Point → S0} {u : Point → S0} {C : ℝ≥0∞}
    {Cₙ : ℕ → ℝ≥0∞} (hLim : Tendsto Cₙ atTop (𝓝 C))
    (hF : ∀ n, AEStronglyMeasurable (f n) (volume.restrict U)) (hU : AEStronglyMeasurable u (volume.restrict U))
    (hAe : ∀ᵐ x ∂volume.restrict U, Tendsto (fun n => f n x) atTop (𝓝 (u x)))
    (hB : ∀ᶠ n in atTop, fractionalEnergy s U (f n) ≤ Cₙ n) :
    (∫⁻ x in U, ∫⁻ y in U, ENNReal.ofReal (‖u x - u y‖ ^ 2 / dist x y ^ (3 + 2 * s))) ≤ C := by
  let μ := volume.restrict U
  let E (n : ℕ) := fractionalPairEnergy s (f n)
  have hFE (n : ℕ) : AEMeasurable (E n) (μ.prod μ) := fractionalPairEnergy_aemeasurable s (hF n)
  have hUE := fractionalPairEnergy_aemeasurable s hU
  have hEq : (fun z => fractionalPairEnergy s u z) =ᵐ[μ.prod μ]
      fun z => liminf (fun n => E n z) atTop := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hAe, Measure.quasiMeasurePreserving_snd.ae hAe] with z h₁ h₂
    have h := ENNReal.tendsto_ofReal (((h₁.sub h₂).norm.pow 2).div_const (dist z.1 z.2 ^ (3 + 2 * s)))
    exact h.liminf_eq.symm
  have hProd (n : ℕ) :
      (∫⁻ z, E n z ∂μ.prod μ) ≤ fractionalEnergy s U (f n) := by
    rw [lintegral_prod _ (hFE n)]
    exact self_le_add_left _ _
  have hBoundProd := hB.mono fun n hn => (hProd n).trans hn
  change (∫⁻ x, ∫⁻ y, fractionalPairEnergy s u (x,y) ∂μ ∂μ) ≤ C
  have hCurry : AEMeasurable (Function.uncurry (fun x y : Point => fractionalPairEnergy s u (x,y))) (μ.prod μ) := hUE
  rw [lintegral_lintegral hCurry, lintegral_congr_ae hEq]
  exact (lintegral_liminf_le' hFE).trans ((liminf_le_liminf hBoundProd).trans_eq hLim.liminf_eq)

theorem nonlocal_energy_bounded_of_tendsto_ae
    {U : Set Point} (s : ℝ) {f : ℕ → Point → S0} {u : Point → S0} {C : ℝ≥0∞}
    (hF : ∀ n, AEStronglyMeasurable (f n) (volume.restrict U)) (hU : AEStronglyMeasurable u (volume.restrict U))
    (hAe : ∀ᵐ x ∂volume.restrict U, Tendsto (fun n => f n x) atTop (𝓝 (u x)))
    (hB : ∀ᶠ n in atTop, fractionalEnergy s U (f n) ≤ C) :
    (∫⁻ x in U, ∫⁻ y in U, ENNReal.ofReal (‖u x - u y‖ ^ 2 / dist x y ^ (3 + 2 * s))) ≤ C :=
  nonlocal_energy_le_limit_bound_of_tendsto_ae s (tendsto_const_nhds (x := C)) hF hU hAe hB

/-- The zero-trace graph embeds continuously in the original fractional
norm for every exponent strictly between zero and one. -/
theorem exists_h10FractionalEmbedding_bound {U : Set Point} (hU : IsBoundedDomain U)
    (s : ℝ) (hs : 0 < s) (hs₁ : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : H10 U, MemHs s U (h10Value v) ∧
      Real.sqrt ((fractionalEnergy s U (h10Value v)).toReal) ≤ C * ‖v‖ := by
  obtain ⟨K,hK,hBound⟩ := fractionalEnergy_le_of_smooth_graph hU s hs hs₁
  let C := Real.sqrt (1 + K).toReal
  refine ⟨C,Real.sqrt_nonneg _,?_⟩
  intro v
  obtain ⟨p,f,hLim,hData⟩ := v.exists_smooth_graph_approximation
  let μ := volume.restrict U
  let u : Lp S0 2 μ := v.val.1
  have hProj : Tendsto (fun n => (p n).1) atTop (𝓝 u) := continuous_fst.continuousAt.tendsto.comp hLim
  obtain ⟨κ,hκ,hAe⟩ := (tendstoInMeasure_of_tendsto_Lp hProj).exists_seq_tendsto_ae
  have hV (n : ℕ) : ((p (κ n)).1 : Point → S0) =ᵐ[μ] f (κ n) := (hData (κ n)).2.2.2.1
  have hF : ∀ᵐ x ∂μ, Tendsto (fun n => f (κ n) x) atTop (𝓝 (u x)) := by
    filter_upwards [hAe, ae_all_iff.mpr hV] with x hx hfx
    exact hx.congr' (.of_forall hfx)
  have hEnergy (n : ℕ) : fractionalEnergy s U (f (κ n)) ≤ K * ENNReal.ofReal (‖p (κ n)‖ ^ 2) := by
    obtain ⟨hC,hSupp,hU,hVal,hD⟩ := hData (κ n)
    exact hBound (p (κ n)) (f (κ n)) hC hU hVal hD
  have hELim : Tendsto (fun n => K * ENNReal.ofReal (‖p (κ n)‖ ^ 2)) atTop
      (𝓝 (K * ENNReal.ofReal (‖v‖ ^ 2))) :=
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal ((hLim.comp hκ.tendsto_atTop).norm.pow 2)) (Or.inr hK.ne)
  have hN := nonlocal_energy_le_limit_bound_of_tendsto_ae s hELim
    (fun n => (hData (κ n)).1.continuous.aestronglyMeasurable) (Lp.aestronglyMeasurable u) hF
    (Eventually.of_forall hEnergy)
  have hL2 : (∫⁻ x in U, ENNReal.ofReal (‖u x‖ ^ 2)) ≤ ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [lintegral_sq_norm_lp μ u]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (le_max_left ‖v.val.1‖ ‖v.val.2‖) 2)
  have h : fractionalEnergy s U (h10Value v) ≤ (1+K) * ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [add_mul,one_mul]
    exact add_le_add hL2 hN
  have hFin : (1+K) * ENNReal.ofReal (‖v‖ ^ 2) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.add_lt_top.2 ⟨by simp,hK⟩) ENNReal.ofReal_lt_top
  refine ⟨⟨Lp.aestronglyMeasurable u,h.trans_lt hFin⟩,?_⟩
  have hReal := ENNReal.toReal_mono hFin.ne h
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg _)] at hReal
  exact (Real.sqrt_le_sqrt hReal).trans_eq (by
    rw [Real.sqrt_mul ENNReal.toReal_nonneg,Real.sqrt_sq (norm_nonneg _)])

/-- The zero-trace Sobolev graph defines a fractional Sobolev map for
every exponent strictly between zero and one. -/
theorem H10.memHs_of_zero_trace {U : Set Point} (hU : IsBoundedDomain U)
    (s : ℝ) (hs : 0 < s) (hs₁ : s < 1) (v : H10 U) : MemHs s U (h10Value v) :=
  ((exists_h10FractionalEmbedding_bound hU s hs hs₁).choose_spec.2 v).1

/-- Native realization of the zero-trace fractional embedding. -/
theorem h10FractionalEmbedding : External.H10FractionalEmbedding := by
  intro U hU s hs hs₁ v
  exact v.memHs_of_zero_trace hU.1 s hs hs₁

end Thesis

end
