module

public import Thesis.MeasureGeometry.StressLimit
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! The distributional stress limit for the sextic energy. -/

public section

open Filter Matrix MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction Classical ContDiff ENNReal NNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

noncomputable local instance penalizedStressLimitContinuousENorm : ContinuousENorm Tensor :=
  @SeminormedAddGroup.toContinuousENorm Tensor inferInstance

private noncomputable def stressDensityOn (a : BulkCoefficients) (ε : ElasticScale)
    (Ω : Set Point) (v : Point → S0) (x : Point) : Tensor :=
  if x ∈ Ω then elasticStressDensity a ε (v x) (ClassicalGradient v x) else 1

private theorem stressDensityOn_bounds (a : BulkCoefficients) (ε : ElasticScale)
    (Ω : Set Point) (v : Point → S0) (x : Point) :
    let T := stressDensityOn a ε Ω v x
    Tᵀ = T ∧ 1 ≤ T.trace ∧ ‖T‖ ≤ 2 ∧
      ∀ w : Point, tensorQuadratic T w ≤ ‖w‖ ^ 2 := by
  by_cases hx : x ∈ Ω
  · simpa only [stressDensityOn, if_pos hx] using elasticStressDensity_bounds a ε (v x)
      (ClassicalGradient v x)
  · simp only [stressDensityOn, if_neg hx, Matrix.transpose_one, true_and,
      tensorQuadratic_one, le_refl, forall_const, and_true, frobenius_norm_one]
    exact ⟨by simp, (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩⟩

private theorem stressDensityOn_measurable_entry (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {v : Point → S0} (hv : ContDiffOn ℝ ∞ v Ω)
    (i j : Fin 3) : Measurable (fun x => stressDensityOn a ε Ω v x i j) := by
  let e : Point → ℝ := Ω.piecewise
    (fun x => energyDensity a ε (v x) (ClassicalGradient v x)) 0
  let T : Point → ℝ := Ω.piecewise (fun x => stressTensor a ε v x i j) 0
  have he : Measurable e :=
    (contDiffOn_classicalEnergyDensity a ε hΩ hv).continuousOn.measurable_piecewise
      continuousOn_const hΩ.measurableSet
  have hT : Measurable T :=
    (contDiffOn_stressTensor_entry a ε hΩ hv i j).continuousOn.measurable_piecewise
      continuousOn_const hΩ.measurableSet
  have he0 : MeasurableSet {x | e x = 0} := he (measurableSet_singleton 0)
  have hE : (fun x => stressDensityOn a ε Ω v x i j) =
      {x | e x = 0}.piecewise (fun _ => (1 : Tensor) i j) (fun x => (e x)⁻¹ * T x) := by
    funext x
    by_cases hx : x ∈ Ω
    · by_cases hz : energyDensity a ε (v x) (ClassicalGradient v x) = 0
      · simp [stressDensityOn, elasticStressDensity, e, hx, hz]
      · simp [stressDensityOn, elasticStressDensity, e, T, hx, hz, elasticStress_classicalGradient]
    · simp [stressDensityOn, e, hx]
  rw [hE]
  exact measurable_const.piecewise he0 (he.inv.mul hT)

private noncomputable def stressDomainTest (X : Point → Point) {Ω : Set Point}
    (hX : IsSmoothTest Ω X) (i j : Fin 3) : Point →ᵇ ℝ :=
  ofCompactSupport (fun x => coordDeriv j X x i)
    ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp
      ((hX.1.continuous_fderiv (by simp)).clm_apply continuous_const)) (by
    apply hX.2.1.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra h
    apply hx
    simp [coordDeriv, fderiv_of_notMem_tsupport ℝ h])

private theorem stressDomainTest_eq_zero_of_notMem {X : Point → Point} {Ω : Set Point}
    (hX : IsSmoothTest Ω X) (i j : Fin 3) {x : Point} (hx : x ∉ Ω) :
    stressDomainTest X hX i j x = 0 := by
  have h : x ∉ tsupport X := fun hx' => hx (hX.2.2 hx')
  change coordDeriv j X x i = 0
  simp [coordDeriv, fderiv_of_notMem_tsupport ℝ h]

private theorem stressDensityOn_pairing (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {u v : Point → S0} {D : Point → Gradient}
    (huv : u =ᵐ[volume.restrict Ω] v) (hD : D =ᵐ[volume.restrict Ω] ClassicalGradient v)
    (hv : ContDiffOn ℝ ∞ v Ω) {μ : FiniteMeasure Point}
    (hμ : (μ : Measure Point) = normalizedEnergyMeasure a ε Ω u D)
    (i j : Fin 3) (φ : Point →ᵇ ℝ) :
    (∫ x, stressDensityOn a ε Ω v x i j * φ x ∂(μ : Measure Point)) =
      (Real.log (1 / (ε : ℝ)))⁻¹ * ∫ x in Ω, stressTensor a ε v x i j * φ x := by
  let m := (volume : Measure Point).restrict Ω
  let e (x : Point) := energyDensity a ε (v x) (ClassicalGradient v x)
  let L := Real.log (1 / (ε : ℝ))
  let w (x : Point) := ENNReal.ofReal (e x / L)
  have hμ' : (μ : Measure Point) = m.withDensity w := by
    rw [hμ, normalizedEnergyMeasure]
    apply withDensity_congr_ae
    filter_upwards [huv, hD] with x h₁ h₂
    simp only [h₁, h₂, w, e, L]
  have hwae : AEMeasurable w m := by
    let e' := Ω.piecewise e (0 : Point → ℝ)
    have hm : Measurable e' :=
      (contDiffOn_classicalEnergyDensity a ε hΩ hv).continuousOn.measurable_piecewise
        continuousOn_const hΩ.measurableSet
    refine ((hm.div_const L).ennreal_ofReal.aemeasurable (μ := m)).congr ?_
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    simp [e', w, hx]
  rw [hμ', integral_withDensity_eq_integral_toReal_smul₀ hwae
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hEq : (∫ x, (w x).toReal • (stressDensityOn a ε Ω v x i j * φ x) ∂m) =
      ∫ x, L⁻¹ * (stressTensor a ε v x i j * φ x) ∂m := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    have hnonneg : 0 ≤ e x := by
      have hn := (elasticStress_bounds a ε (v x) (ClassicalGradient v x)).2.2.1
      exact (mul_nonneg_iff_of_pos_left (by norm_num : 0 < (2 : ℝ))).1 ((norm_nonneg _).trans hn)
    rw [smul_eq_mul, show (w x).toReal = e x / L from
      ENNReal.toReal_ofReal (div_nonneg hnonneg (log_inv_scale_pos ε).le)]
    have hmul : e x * stressDensityOn a ε Ω v x i j = stressTensor a ε v x i j := by
      rw [stressDensityOn, if_pos hx, ← elasticStress_classicalGradient a ε v x]
      exact congrFun (congrFun (energyDensity_smul_elasticStressDensity a ε (v x)
        (ClassicalGradient v x)) i) j
    rw [div_eq_inv_mul, mul_assoc, ← mul_assoc (e x), hmul]
  exact hEq.trans (integral_const_mul _ _)

/-- Along a subsequence of the chosen normalized energy measures, the stress
has one bounded matrix density, with divergence zero on the same open set. -/
theorem exists_penalizedStress_limit (a : BulkCoefficients) {Ω : Set Point}
    (hΩ : IsBoundedDomain Ω) {ε : ℕ → ElasticScale} {u v : ℕ → Point → S0}
    {D : ℕ → Point → Gradient} (huv : ∀ n, u n =ᵐ[volume.restrict Ω] v n)
    (hD : ∀ n, D n =ᵐ[volume.restrict Ω] ClassicalGradient (v n))
    (hv : ∀ n, ContDiffOn ℝ ∞ (v n) Ω)
    (hEuler : ∀ n, ∀ x ∈ Ω, (ε n : ℝ) ^ 2 • (laplacian (v n) x : S0).val = bulkGradient a (v n x))
    {μ : ℕ → FiniteMeasure Point} {ν : FiniteMeasure Point} (hlim : Tendsto μ atTop (𝓝 ν))
    (hμ : ∀ n, (μ n : Measure Point) = normalizedEnergyMeasure a (ε n) Ω (u n) (D n))
    (B : ℝ≥0) (hB : ∀ n, (μ n).mass ≤ B) :
    ∃ (s : ℕ → ℕ) (F : Point → Tensor), StrictMono s ∧
      Integrable F ((ν : Measure Point).restrict Ω) ∧ External.RowDivergenceFree Ω ν F ∧
      (∀ᵐ x ∂((ν : Measure Point).restrict Ω), (F x)ᵀ = F x ∧ 1 ≤ (F x).trace ∧ ‖F x‖ ≤ 2 ∧
        ∀ z : Point, tensorQuadratic (F x) z ≤ ‖z‖ ^ 2) ∧
      ∀ (i j : Fin 3) (φ : Point →ᵇ ℝ), Tendsto
        (fun n => (Real.log (1 / (ε (s n) : ℝ)))⁻¹ *
          ∫ x in Ω, stressTensor a (ε (s n)) (v (s n)) x i j * φ x) atTop
        (𝓝 (∫ x, F x i j * φ x ∂(ν : Measure Point))) := by
  let T (n : ℕ) := stressDensityOn a (ε n) Ω (v n)
  have hK : IsCompact (closure Ω) := hΩ.2.2.isCompact_closure
  have hsupp (n : ℕ) : (μ n : Measure Point) (closure Ω)ᶜ = 0 := by
    rw [hμ n]
    exact normalizedEnergyMeasure_compl_closure a (ε n) Ω (u n) (D n)
  have hm n := stressDensityOn_measurable_entry a (ε n) hΩ.1 (hv n)
  have ht n := stressDensityOn_bounds a (ε n) Ω (v n)
  obtain ⟨s, F, hs, hFm, hFi, hFb, hweak⟩ := exists_matrixStressDensity_subsequence hK
    hΩ.2.1.nonempty.closure hlim B hB hsupp T hm ht
  refine ⟨s, F, hs, hFi.integrableOn, ?_, ae_restrict_of_ae hFb, ?_⟩
  · intro X hXs hXc hXsub
    have hX : IsSmoothTest Ω X := ⟨hXs, hXc, hXsub⟩
    let φ := stressDomainTest X hX
    have hweakSum := tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_finsetSum Finset.univ (fun j _ => hweak i j (φ i j)))
    have hsum (n : ℕ) : (∑ i, ∑ j, ∫ x, T n x i j * φ i j x ∂(μ n : Measure Point)) = 0 := by
      let f (x : Point) := ∑ i, ∑ j, (fderiv ℝ X x (axis j)) i * stressTensor a (ε n) (v n) x i j
      have hPure : (∫ x in Ω, f x) = 0 := by
        have hAll := integral_stressTensor_contract_eq_zero a (ε n) hΩ.1 (hv n) (hEuler n) hX
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)]
        · exact hAll
        · simp only [f, show fderiv ℝ X x = 0 from fderiv_of_notMem_tsupport ℝ
            (fun hx' => hx (hXsub hx')), _root_.zero_apply, PiLp.zero_apply, zero_mul,
            Finset.sum_const_zero]
      have hp (i j : Fin 3) : (∫ x, T n x i j * φ i j x ∂(μ n : Measure Point)) =
          (Real.log (1 / (ε n : ℝ)))⁻¹ * ∫ x in Ω, stressTensor a (ε n) (v n) x i j * φ i j x :=
        stressDensityOn_pairing a (ε n) hΩ.1 (huv n) (hD n) (hv n) (hμ n) i j (φ i j)
      simp_rw [hp, ← Finset.mul_sum]
      have hInt (i j : Fin 3) : IntegrableOn (fun x => stressTensor a (ε n) (v n) x i j * φ i j x)
          Ω volume := by
        have hc := (contDiffOn_stressTensor_entry a (ε n) hΩ.1 (hv n) i j).continuousOn
        have hComp := hXc
        have hOn := (hc.mono hXsub).mul (φ i j).continuous.continuousOn
        exact ((hOn.integrableOn_compact hComp).integrable_of_forall_notMem_eq_zero
          (fun x hx => by
            have hd := fderiv_of_notMem_tsupport ℝ hx
            change _ * coordDeriv j X x i = 0
            simp [coordDeriv, hd])).integrableOn
      have hInner (i : Fin 3) : (∑ j, ∫ x in Ω, stressTensor a (ε n) (v n) x i j * φ i j x) =
          ∫ x in Ω, ∑ j, stressTensor a (ε n) (v n) x i j * φ i j x :=
        (integral_finsetSum _ (fun j _ => hInt i j)).symm
      simp_rw [hInner]
      rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hInt i j))]
      change (Real.log (1 / (ε n : ℝ)))⁻¹ *
        (∫ x in Ω, ∑ i, ∑ j, stressTensor a (ε n) (v n) x i j * coordDeriv j X x i) = 0
      simp_rw [mul_comm (stressTensor _ _ _ _ _ _)]
      change (Real.log (1 / (ε n : ℝ)))⁻¹ * (∫ x in Ω, f x) = 0
      rw [hPure, mul_zero]
    have hzero := tendsto_nhds_unique_of_eventuallyEq hweakSum tendsto_const_nhds
      (Filter.Eventually.of_forall (fun n => hsum (s n)))
    have hIF (i j : Fin 3) : Integrable (fun x => F x i j * φ i j x) (ν : Measure Point) := by
      have I : Integrable (fun x => F x i j) (ν : Measure Point) :=
        hFi.norm.mono' (hFm i j).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => by
            simpa only [Real.norm_eq_abs] using abs_tensor_entry_le_frobenius_norm (F x) i j)
      exact I.mul_bdd (φ i j).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall (φ i j).norm_coe_le_norm)
    change (∫ x in Ω, ∑ i, ∑ j, F x i j * φ i j x ∂(ν : Measure Point)) = 0
    have hcomp (x : Point) (hx : x ∉ Ω) : (∑ i, ∑ j, F x i j * φ i j x) = 0 := by
      have hφz (i j : Fin 3) : φ i j x = 0 := stressDomainTest_eq_zero_of_notMem hX i j hx
      simp only [hφz, mul_zero, Finset.sum_const_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hcomp,
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hIF i j))]
    have hInner (i : Fin 3) : (∫ x, ∑ j, F x i j * φ i j x ∂(ν : Measure Point)) =
        ∑ j, ∫ x, F x i j * φ i j x ∂(ν : Measure Point) :=
      integral_finsetSum _ (fun j _ => hIF i j)
    simp_rw [hInner]
    exact hzero
  · intro i j φ
    apply (hweak i j φ).congr
    intro n
    exact stressDensityOn_pairing a (ε (s n)) hΩ.1 (huv (s n)) (hD (s n))
      (hv (s n)) (hμ (s n)) i j φ

end Thesis.MeasureGeometry

end
