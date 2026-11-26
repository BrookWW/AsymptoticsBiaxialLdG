module

public import Thesis.Variational.BoundaryLimit

/-! Global convergence of the actual energy densities and uniform estimates
at a base radius in the regular boundary collar. -/

public section

open Set Filter MeasureTheory Topology
open scoped BigOperators ENNReal NNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance boundaryEnergyContinuousENormS0 : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

variable {Ω U : Set Point}

private theorem eLpNorm_two_sq_le_h1Deviation
    {u v : Point → S0} {D G : Point → Gradient} (hu : MemH1 Ω u D) (hv : MemH1 Ω v G)
    (j : Fin 3) :
    eLpNorm (fun x => D x j - G x j) 2 (volume.restrict Ω) ^ 2 ≤ h1Deviation Ω u v D G := by
  have hMap (w : Point → S0) (hw : MemLp w 2 (volume.restrict Ω)) :
      MemLp (frobeniusField w) 2 (volume.restrict Ω) :=
    (frobeniusCoordinateEquiv_memLp_iff _ _ _).mpr hw
  have hD (k : Fin 3) := hMap (fun x => D x k) (hu.2.1 k)
  have hG (k : Fin 3) := hMap (fun x => G x k) (hv.2.1 k)
  have hEq := h1Deviation_eq_sq_eLpNorm Ω u v D G
    ((hMap v hv.1).aestronglyMeasurable.sub (hMap u hu.1).aestronglyMeasurable)
    (fun k => (hG k).aestronglyMeasurable.sub (hD k).aestronglyMeasurable)
  have hNorm : eLpNorm (fun x => D x j - G x j) 2 (volume.restrict Ω) =
      eLpNorm (fun x => frobeniusGradient G x j - frobeniusGradient D x j)
        2 (volume.restrict Ω) := by
    apply eLpNorm_congr_norm_ae
    exact Eventually.of_forall fun x => by
      change ‖D x j - G x j‖ = ‖frobeniusCoordinateEquiv (G x j) - frobeniusCoordinateEquiv (D x j)‖
      rw [← map_sub, LinearIsometryEquiv.norm_map, norm_sub_rev]
  rw [hNorm, hEq]
  refine (Finset.single_le_sum (f := fun k : Fin 3 =>
    eLpNorm (fun x => frobeniusGradient G x k - frobeniusGradient D x k)
      2 (volume.restrict Ω) ^ 2) (fun _ _ => zero_le) (Finset.mem_univ j)).trans ?_
  exact le_add_of_nonneg_left zero_le

theorem StrongH1.tendsto_eLpNorm_gradient_column
    {u : ℕ → Point → S0} {D : ℕ → Point → Gradient}
    {v : Point → S0} {G : Point → Gradient} (h : StrongH1 Ω u D v G) (j : Fin 3) :
    Tendsto (fun n => eLpNorm (fun x => D n x j - G x j) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun _ hc => (not_lt_of_ge zero_le hc).elim, fun c hc => ?_⟩
  have hε : ∀ᶠ n in atTop, h1Deviation Ω (u n) v (D n) G < c ^ 2 :=
    (tendsto_order.1 h.2.2).2 _ (ENNReal.pow_pos hc _)
  refine hε.mono fun n hn => lt_of_not_ge fun hge => ?_
  exact (not_lt_of_ge (pow_le_pow_left' hge 2))
    ((eLpNorm_two_sq_le_h1Deviation (h.1 n) h.2.1 j).trans_lt hn)

private theorem eLpNorm_diff_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    {μ : Measure Point} {f g : Point → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    eLpNorm (fun x => ‖f x‖ ^ 2 - ‖g x‖ ^ 2) 1 μ ≤ eLpNorm (f - g) 2 μ *
      (eLpNorm (f - g) 2 μ + eLpNorm (fun x => 2 * ‖g x‖) 2 μ) := by
  let A (x : Point) := ‖f x - g x‖
  let B (x : Point) := 2 * ‖g x‖
  have hA : AEStronglyMeasurable A μ := (hf.sub hg).1.norm
  have hB : AEStronglyMeasurable B μ := hg.1.norm.const_mul _
  have hAB : AEStronglyMeasurable (A + B) μ := hA.add hB
  have hPoint (x : Point) : ‖‖f x‖ ^ 2 - ‖g x‖ ^ 2‖ ≤ A x * (A + B) x := by
    have h₁ : ‖f x‖ ≤ A x + ‖g x‖ := by
      have hn := norm_add_le (f x - g x) (g x)
      rw [sub_add_cancel] at hn
      exact hn
    have h₂ : ‖f x‖ + ‖g x‖ ≤ (A + B) x := by
      change ‖f x‖ + ‖g x‖ ≤ A x + 2 * ‖g x‖
      linarith only [h₁]
    rw [Real.norm_eq_abs, show ‖f x‖ ^ 2 - ‖g x‖ ^ 2 =
      (‖f x‖ - ‖g x‖) * (‖f x‖ + ‖g x‖) by ring, abs_mul,
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul (abs_norm_sub_norm_le _ _) h₂
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  haveI : ENNReal.HolderTriple 2 2 1 := by
    constructor
    norm_num [← two_mul, ENNReal.mul_inv_cancel]
  have hAeq : eLpNorm A 2 μ = eLpNorm (f - g) 2 μ := eLpNorm_norm _
  calc
    _ ≤ eLpNorm (A • (A + B)) 1 μ := eLpNorm_mono_ae_real (Eventually.of_forall hPoint)
    _ ≤ eLpNorm A 2 μ * eLpNorm (A + B) 2 μ := eLpNorm_smul_le_mul_eLpNorm hAB hA
    _ ≤ eLpNorm A 2 μ * (eLpNorm A 2 μ + eLpNorm B 2 μ) :=
      mul_le_mul_right (eLpNorm_add_le hA hB (by norm_num : (1 : ℝ≥0∞) ≤ 2)) _
    _ = _ := by rw [hAeq]

/-- Strong L² convergence implies L¹ convergence of the squared norms. -/
theorem tendsto_eLpNorm_diff_norm_sq_zero {E : Type*} [NormedAddCommGroup E]
    {μ : Measure Point} {f : ℕ → Point → E} {g : Point → E}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => ‖f n x‖ ^ 2 - ‖g x‖ ^ 2) 1 μ) atTop (𝓝 0) := by
  let C := eLpNorm (fun x => 2 * ‖g x‖) 2 μ
  have hC : C ≠ ⊤ :=
    (show MemLp (fun x => (2 : ℝ) * ‖g x‖) 2 μ from hg.norm.const_mul 2).eLpNorm_lt_top.ne
  have hsum : Tendsto (fun n => eLpNorm (f n - g) 2 μ + C) atTop (𝓝 C) := by
    simpa only [zero_add] using h.add tendsto_const_nhds
  have hProd : Tendsto (fun n => eLpNorm (f n - g) 2 μ * (eLpNorm (f n - g) 2 μ + C))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul h (Or.inr hC) hsum (Or.inr ENNReal.zero_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hProd
    (fun _ => zero_le) (fun n => eLpNorm_diff_norm_sq_le (hf n) hg)

/-- The (L^1) defect of the actual penalized energy density from the limiting
half-normalized Dirichlet density. -/
@[expose] def energyDensityDefect (a : BulkCoefficients) (ε : ElasticScale) (Ω : Set Point)
    (u : Point → S0) (D G : Point → Gradient) : ℝ≥0∞ :=
  eLpNorm (fun x => energyDensity a ε (u x) (D x) - (1 / 2 : ℝ) * gradientNormSq (G x))
    1 (volume.restrict Ω)

/-- Global strong (H^1) convergence and vanishing scaled bulk potential give
(L^1) convergence of the actual energy densities. -/
theorem tendsto_energyDensityDefect_zero_of_strongH1
    (a : BulkCoefficients) (ε : ℕ → ElasticScale)
    {u : ℕ → Point → S0} {D : ℕ → Point → Gradient} {v : Point → S0} {G : Point → Gradient}
    (h : StrongH1 Ω u D v G)
    (hBulkLp : ∀ n, MemLp (fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (u n x))
      1 (volume.restrict Ω))
    (hBulk : Tendsto (fun n => eLpNorm (fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (u n x))
      1 (volume.restrict Ω)) atTop (𝓝 0)) :
    Tendsto (fun n => energyDensityDefect a (ε n) Ω (u n) (D n) G) atTop (𝓝 0) := by
  let μ := volume.restrict Ω
  let K (n : ℕ) (j : Fin 3) (x : Point) := ‖D n x j‖ ^ 2 - ‖G x j‖ ^ 2
  let S (n : ℕ) := ∑ j, K n j
  let B (n : ℕ) (x : Point) := (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (u n x)
  have hK (n : ℕ) (j : Fin 3) : AEStronglyMeasurable (K n j) μ :=
    (((h.1 n).2.1 j).1.norm.pow 2).sub (((h.2.1).2.1 j).1.norm.pow 2)
  have hKconv (j : Fin 3) : Tendsto (fun n => eLpNorm (K n j) 1 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_diff_norm_sq_zero (fun n => (h.1 n).2.1 j) (h.2.1.2.1 j)
      (h.tendsto_eLpNorm_gradient_column j)
  have hSconv : Tendsto (fun n => eLpNorm (S n) 1 μ) atTop (𝓝 0) := by
    have hT : Tendsto (fun n => ∑ j, eLpNorm (K n j) 1 μ) atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero] using tendsto_finsetSum (s := Finset.univ) (fun j _ => hKconv j)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT
      (fun _ => zero_le) (fun n => eLpNorm_sum_le (fun j _ => hK n j) le_rfl)
  have hS (n : ℕ) : AEStronglyMeasurable (S n) μ :=
    Finset.aestronglyMeasurable_sum _ (fun j _ => hK n j)
  have hSscale : Tendsto (fun n => eLpNorm ((1 / 2 : ℝ) • S n) 1 μ) atTop (𝓝 0) := by
    simp_rw [eLpNorm_const_smul]
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hSconv
      (Or.inr (enorm_ne_top (x := (1 / 2 : ℝ))))
  have hSum : Tendsto (fun n => eLpNorm ((1 / 2 : ℝ) • S n) 1 μ + eLpNorm (B n) 1 μ)
      atTop (𝓝 0) := by
    simpa only [add_zero] using hSscale.add hBulk
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSum
    (fun _ => zero_le) (fun n => ?_)
  have hF : (fun x => energyDensity a (ε n) (u n x) (D n x) - (1 / 2 : ℝ) * gradientNormSq (G x)) =
      (1 / 2 : ℝ) • S n + B n := by
    funext x
    simp only [energyDensity, gradientNormSq_eq_sum_norm_sq, Pi.add_apply, Pi.smul_apply, S,
      Finset.sum_apply, K, Finset.sum_sub_distrib, smul_eq_mul, B]
    ring
  rw [energyDensityDefect, hF]
  exact eLpNorm_add_le ((hS n).const_smul _) (hBulkLp n).1 le_rfl

/-- The global energy-density defect bounds the local energy excess
above the limiting Dirichlet energy. -/
theorem energy_le_dirichletEnergy_add_energyDensityDefect
    (a : BulkCoefficients) (ε : ElasticScale) (u : Point → S0) (D G : Point → Gradient)
    (hU : U ⊆ Ω) (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict Ω)) :
    energy a ε U u D ≤ dirichletEnergy U G + energyDensityDefect a ε Ω u D G := by
  let e (x : Point) := energyDensity a ε (u x) (D x)
  let d (x : Point) := (1 / 2 : ℝ) * gradientNormSq (G x)
  have hRestrict := Measure.restrict_mono_set (volume : Measure Point) hU
  have hd : AEMeasurable (fun x => ENNReal.ofReal (d x)) (volume.restrict U) := by
    apply AEMeasurable.ennreal_ofReal
    simp only [d, gradientNormSq_eq_sum_norm_sq]
    exact aemeasurable_const.mul (Finset.aemeasurable_fun_sum Finset.univ fun j _ =>
      ((hG j).mono_measure hRestrict).aestronglyMeasurable.norm.aemeasurable.pow_const (2 : ℕ))
  have hNonneg (x : Point) : 0 ≤ d x := by
    simp only [d, gradientNormSq_eq_sum_norm_sq]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hPoint (x : Point) : ENNReal.ofReal (e x) ≤ ENNReal.ofReal (d x) + ‖e x - d x‖ₑ := by
    rw [← ofReal_norm, ← ENNReal.ofReal_add (hNonneg x) (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hAbs := le_abs_self (e x - d x)
    rw [← Real.norm_eq_abs] at hAbs
    linarith only [hAbs]
  change (∫⁻ x in U, ENNReal.ofReal (e x)) ≤
    (∫⁻ x in U, ENNReal.ofReal (d x)) + eLpNorm (fun x => e x - d x) 1 (volume.restrict Ω)
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc
    _ ≤ ∫⁻ x in U, (ENNReal.ofReal (d x) + ‖e x - d x‖ₑ) := lintegral_mono hPoint
    _ = (∫⁻ x in U, ENNReal.ofReal (d x)) + (∫⁻ x in U, ‖e x - d x‖ₑ) :=
      lintegral_add_left' hd _
    _ ≤ _ := add_le_add le_rfl (lintegral_mono' hRestrict le_rfl)

/-- At a fixed radius in the regular collar, the normalized energy is
bounded by the global defect divided by the radius plus a quadratic term.
The collar and compact set determine the constants uniformly in the center. -/
theorem exists_boundary_collar_base_radius_bound
    {V K : Set Point} (hΩ : IsOpen Ω) (hV : IsOpen V) {q : Point → S0} {G : Point → Gradient}
    (hq : ContDiffOn ℝ 2 q (closure Ω ∩ V))
    (hK : IsCompact K) (hKsub : K ⊆ closure Ω ∩ V)
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict Ω))
    (hGrad : G =ᵐ[volume.restrict Ω] ClassicalGradient q) :
    ∃ (R₀ M : ℝ), 0 < R₀ ∧ 0 ≤ M ∧
      ∀ x ∈ K, ∀ R ∈ Ioo 0 R₀, ∀ (a : BulkCoefficients) (ε : ElasticScale)
        (u : Point → S0) (D : Point → Gradient),
        ENNReal.ofReal (R⁻¹) * energy a ε (Ω ∩ Metric.ball x R) u D ≤
          ENNReal.ofReal (R⁻¹) * energyDensityDefect a ε Ω u D G +
            ENNReal.ofReal ((M / 2) * (Real.pi * 4 / 3) * R ^ 2) := by
  obtain ⟨O, M, hO, hKO, _, hM, hBound⟩ :=
    exists_gradientNormSq_bound_on_compact_collar hΩ hV hq hK hKsub
  obtain ⟨R₀, hR₀, hSep⟩ := hK.exists_thickening_subset_open hO hKO
  refine ⟨R₀, M, hR₀, hM, ?_⟩
  intro x hx R hR a ε u D
  let W := Ω ∩ Metric.ball x R
  have hW : MeasurableSet W := hΩ.measurableSet.inter Metric.isOpen_ball.measurableSet
  have hBall : Metric.ball x R ⊆ O := (Metric.ball_subset_ball hR.2.le).trans
    ((Metric.ball_subset_thickening hx R₀).trans hSep)
  have hWGrad : ∀ᵐ y ∂volume.restrict W, gradientNormSq (G y) ≤ M := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hGrad,
      ae_restrict_mem hW] with y hy hyW
    rw [hy]
    exact hBound y ⟨hyW.1, hBall hyW.2⟩
  have hM₂ : 0 ≤ M / 2 := div_nonneg hM (by norm_num)
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.1.le
  have hED : dirichletEnergy W G ≤ ENNReal.ofReal (M / 2) * volume (Metric.ball x R) := by
    calc
      _ ≤ ∫⁻ _ in W, ENNReal.ofReal (M / 2) := lintegral_mono_ae (hWGrad.mono fun y hy => by
        apply ENNReal.ofReal_le_ofReal
        linarith only [hy])
      _ = ENNReal.ofReal (M / 2) * volume W := by
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ _ := mul_le_mul_right (measure_mono inter_subset_right) _
  calc
    _ ≤ ENNReal.ofReal (R⁻¹) * (dirichletEnergy W G + energyDensityDefect a ε Ω u D G) :=
      mul_le_mul_right (energy_le_dirichletEnergy_add_energyDensityDefect a ε u D G
        inter_subset_left hG) _
    _ ≤ ENNReal.ofReal (R⁻¹) * (ENNReal.ofReal (M / 2) * volume (Metric.ball x R) +
        energyDensityDefect a ε Ω u D G) := by gcongr
    _ = _ := by
      rw [mul_add, add_comm, EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hR.1.le,
        ← ENNReal.ofReal_mul (pow_nonneg hR.1.le 3), ← ENNReal.ofReal_mul hM₂,
        ← ENNReal.ofReal_mul hRinv]
      congr 2
      field_simp [hR.1.ne']

end Thesis

end
