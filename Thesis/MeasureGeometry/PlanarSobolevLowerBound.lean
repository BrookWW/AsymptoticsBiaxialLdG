module

public import Thesis.MeasureGeometry.PlanarSmoothLowerBound
public import Thesis.MeasureGeometry.PlanarSobolevApproximation
import Thesis.StressEnergy
import HarmonicMaps.Analysis.VariableMollificationL2

/-! Strong approximation and the planar logarithmic estimate for a
continuous positive-gap collar of a Sobolev disk. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Matrix.Norms.Frobenius Topology

namespace Thesis

/-- The bulk potential in the same Frobenius coordinates used by the
native Sobolev derivatives. -/
def planarCoordinateBulkPotential (a : BulkCoefficients) (A : Ambient 5) : ℝ :=
  bulkPotential a (frobeniusCoordinateEquiv.symm A)

/-- The planar energy computed from the displayed weak gradient columns. -/
def planarWeakEnergy (a : BulkCoefficients) (ε : ℝ) (u : Plane → Ambient 5)
    (Du : Plane → HarmonicMaps.Gradient 2 5) (R : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∫ x in ball (0 : Plane) R, hsNormSq (Du x)) +
    ε⁻¹ ^ 2 * ∫ x in ball (0 : Plane) R, planarCoordinateBulkPotential a (u x)

theorem finite_planarVolume_restrict_ball (r : ℝ) :
    IsFiniteMeasure ((volume : Measure Plane).restrict (ball (0 : Plane) r)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact (measure_mono ball_subset_closedBall).trans_lt ((isCompact_closedBall (0 : Plane) r).measure_lt_top)

theorem continuous_planarCoordinateBulkPotential (a : BulkCoefficients) :
    Continuous (planarCoordinateBulkPotential a) :=
  (contDiff_bulkPotential a).continuous.comp frobeniusCoordinateEquiv.symm.continuous

theorem integrable_planarCoordinateBulkPotential_of_bound (a : BulkCoefficients)
    {μ : Measure Plane} [IsFiniteMeasure μ] {u : Plane → Ambient 5} {C : ℝ}
    (hu : AEStronglyMeasurable u μ) (hBound : ∀ᵐ x ∂μ, ‖u x‖ ≤ C) :
    Integrable (fun x => planarCoordinateBulkPotential a (u x)) μ := by
  have hP := continuous_planarCoordinateBulkPotential a
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Ambient 5) C).exists_bound_of_continuousOn hP.continuousOn
  apply (integrable_const M).mono' (hP.comp_aestronglyMeasurable hu)
  filter_upwards [hBound] with x hx
  exact hM _ (mem_closedBall_zero_iff.mpr hx)

private theorem integral_norm_sq_eq_toLp_sq {u : Plane → Ambient 5} {μ : Measure Plane}
    (hu : MemLp u 2 μ) : (∫ x, ‖u x‖ ^ 2 ∂μ) = ‖hu.toLp u‖ ^ 2 := by
  calc
    _ = ∫ x, inner ℝ ((hu.toLp u) x) ((hu.toLp u) x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
    _ = inner ℝ (hu.toLp u) (hu.toLp u) := (L2.inner_def _ _).symm
    _ = _ := real_inner_self_eq_norm_sq _

private theorem tendsto_integral_norm_sq_of_L2 {μ : Measure Plane} {f : ℕ → Plane → Ambient 5}
    {u : Plane → Ambient 5} (hf : ∀ n, MemLp (f n) 2 μ) (hu : MemLp u 2 μ)
    (h : Tendsto (fun n => eLpNorm (f n - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖f n x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖u x‖ ^ 2 ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr h
  simpa only [← integral_norm_sq_eq_toLp_sq] using hLp.norm.pow 2

theorem tendsto_integral_planarCoordinateBulkPotential_of_L2 (a : BulkCoefficients)
    {μ : Measure Plane} [IsFiniteMeasure μ] {f : ℕ → Plane → Ambient 5} {u : Plane → Ambient 5}
    {C : ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hu : MemLp u 2 μ)
    (hfB : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C) (huB : ∀ᵐ x ∂μ, ‖u x‖ ≤ C)
    (h : Tendsto (fun n => eLpNorm (f n - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, planarCoordinateBulkPotential a (f n x) ∂μ) atTop
      (𝓝 (∫ x, planarCoordinateBulkPotential a (u x) ∂μ)) := by
  let P := planarCoordinateBulkPotential a
  have hP : ContDiff ℝ ∞ P :=
    (contDiff_bulkPotential a).comp frobeniusCoordinateEquiv.symm.toContinuousLinearMap.contDiff
  obtain ⟨L, hL⟩ := hP.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : Ambient 5) C) (isCompact_closedBall _ _)
  have hL1 : Tendsto (fun n => eLpNorm (f n - u) 1 μ) atTop (𝓝 0) := by
    have hM : Tendsto (fun n => eLpNorm (f n - u) 2 μ *
        μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)) atTop (𝓝 0) := by
      simpa only [zero_mul] using ENNReal.Tendsto.mul_const h (Or.inr (by norm_num))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hM (fun _ => zero_le)
    intro n
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((hf n).sub hu).aestronglyMeasurable
  have hL1P : Tendsto (fun n => eLpNorm ((fun x => P (f n x)) - (fun x => P (u x))) 1 μ) atTop (𝓝 0) := by
    have hM : Tendsto (fun n => (L : ℝ≥0∞) * eLpNorm (f n - u) 1 μ) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hL1 (Or.inr (by simp))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hM (fun _ => zero_le)
    intro n
    have hB : eLpNorm ((fun x => P (f n x)) - (fun x => P (u x))) 1 μ ≤
        eLpNorm ((L : ℝ) • (f n - u)) 1 μ := by
      apply eLpNorm_mono_ae
      filter_upwards [hfB n, huB] with x hx hy
      have hh := hL.dist_le_mul (f n x) (mem_closedBall_zero_iff.mpr hx) (u x) (mem_closedBall_zero_iff.mpr hy)
      simpa only [Pi.sub_apply, Pi.smul_apply, norm_smul, Real.norm_of_nonneg L.coe_nonneg, dist_eq_norm] using hh
    simpa only [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg L.coe_nonneg, ENNReal.ofReal_coe_nnreal] using hB
  exact tendsto_integral_of_L1' (fun x => P (u x))
    ((continuous_planarCoordinateBulkPotential a).comp_aestronglyMeasurable hu.aestronglyMeasurable)
    (Eventually.of_forall fun n => integrable_planarCoordinateBulkPotential_of_bound a
      (hf n).aestronglyMeasurable (hfB n)) hL1P

theorem planarSmoothEnergy_eq_weak (a : BulkCoefficients) (ε : ℝ)
    (m : Plane → Ambient 5) (hm : ContDiff ℝ ∞ m) (r : ℝ) :
    planarSmoothEnergy a ε (fun x => frobeniusCoordinateEquiv.symm (m x)) r =
      planarWeakEnergy a ε m (fun x i => coordinateDerivative m hm i x) r := by
  let Q (x : Plane) := frobeniusCoordinateEquiv.symm (m x)
  let D (x : Plane) (i : Fin 2) := coordinateDerivative m hm i x
  let L : Ambient 5 →L[ℝ] Tensor := symmetricTraceless.subtypeL.comp frobeniusCoordinateEquiv.symm.toContinuousLinearMap
  have hn (v : Ambient 5) : ‖L v‖ = ‖v‖ := frobeniusCoordinateEquiv.symm.norm_map v
  have hQ : ContDiff ℝ 1 Q := frobeniusCoordinateEquiv.symm.toContinuousLinearMap.contDiff.comp (hm.of_le (by decide))
  have hEq (x : Plane) : planarSmoothDirichletDensity Q x = (1 / 2 : ℝ) * hsNormSq (D x) := by
    have hFd : fderiv ℝ (fun y => (Q y : Tensor)) x = L.comp (fderiv ℝ m x) :=
      (L.hasFDerivAt.comp x (hm.differentiable (by simp) x).hasFDerivAt).fderiv
    simp only [planarSmoothDirichletDensity, hFd, ContinuousLinearMap.comp_apply, hn, hsNormSq, D, coordinateDerivative]
  unfold planarSmoothEnergy planarWeakEnergy planarSmoothEnergyDensity
  change (∫ x in ball (0 : Plane) r, planarSmoothDirichletDensity Q x + planarCoordinateBulkPotential a (m x) / ε ^ 2) = _
  have hIntD : IntegrableOn (planarSmoothDirichletDensity Q) (ball (0 : Plane) r) :=
    ((continuous_planarSmoothDirichletDensity hQ).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hP : Continuous (fun x => planarCoordinateBulkPotential a (m x)) :=
    (continuous_planarCoordinateBulkPotential a).comp hm.continuous
  have hIntP : IntegrableOn (fun x => planarCoordinateBulkPotential a (m x)) (ball (0 : Plane) r) :=
    (hP.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Plane) r)).mono_set ball_subset_closedBall
  rw [integral_add hIntD (hIntP.div_const _)]
  simp_rw [hEq, div_eq_mul_inv, ← inv_pow]
  rw [integral_const_mul, integral_mul_const, mul_comm _ (ε⁻¹ ^ 2)]

/-- A single sequence of native mollifications preserves the essential
norm bound, converges in the weak-gradient energy on inner disks, and is
uniform on compact subsets of the actual continuity region. -/
theorem exists_planarSmoothEnergy_approximation (a : BulkCoefficients) (ε : ℝ)
    {u : Plane → Ambient 5} {Du : Plane → HarmonicMaps.Gradient 2 5}
    (hu : MemW12 (ballDomain (0 : Plane) 1) u Du) {C r : ℝ} (hC : 0 ≤ C) (hr : r < 1)
    (huC : ∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖u x‖ ≤ C) :
    ∃ (m : ℕ → Plane → Ambient 5), (∀ n, ContDiff ℝ ∞ (m n)) ∧
      (∀ n x, ‖m n x‖ ≤ C) ∧
      Tendsto (fun n => planarSmoothEnergy a ε (fun x => frobeniusCoordinateEquiv.symm (m n x)) r)
        atTop (𝓝 (planarWeakEnergy a ε u Du r)) ∧
      ∀ (V : OpenDomain 2), V.val ⊆ ball (0 : Plane) 1 → ContinuousOn u V.val →
        ∀ (K : Set Plane), IsCompact K → K ⊆ V.val → ∀ η > 0,
          ∀ᶠ n in atTop, ∀ x ∈ K, ‖m n x - u x‖ < η := by
  let B := ball (0 : Plane) r
  let μ := (volume : Measure Plane).restrict B
  have hμ : μ ≤ volume.restrict (ball (0 : Plane) 1) := Measure.restrict_mono (ball_subset_ball hr.le) le_rfl
  let Ω := ballDomain (0 : Plane) 1
  have hrPos : 0 < 1 - r := sub_pos.mpr hr
  let h (n : ℕ) : PositiveRadius := ⟨(1 - r) * (1 / ((n : ℝ) + 1)), mul_pos hrPos (one_div_pos.mpr (by positivity))⟩
  have hLim : Tendsto (fun n => (h n).val) atTop (𝓝 0) := by
    simpa only [h, mul_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 - r))
  have hScale : Tendsto h atTop (comap (fun t : PositiveRadius => t.val) (𝓝 (0 : ℝ))) :=
    tendsto_comap_iff.mpr hLim
  let m := fun n => euclideanMollification Ω u hu.integrable_ball (h n)
  have hm (n : ℕ) : ContDiff ℝ ∞ (m n) := euclideanMollification_contDiff Ω u hu.integrable_ball (h n)
  have hmB (n : ℕ) (x : Plane) : ‖m n x‖ ≤ C :=
    euclideanMollification_norm_le_essential_bound Ω u hu.integrable_ball hC huC (h n) x
  have hMargin (n : ℕ) : (h n).val / 2 ≤ 1 - r := by
    have hk : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).2 (le_add_of_nonneg_left (Nat.cast_nonneg n))
    have hK := mul_le_mul_of_nonneg_left hk (sub_nonneg.mpr hr.le)
    dsimp only [h]
    nlinarith only [hK, hr]
  let D (n : ℕ) (i : Fin 2) (x : Plane) := coordinateDerivative (m n) (hm n) i x
  have hmL (n : ℕ) : MemLp (m n) 2 μ := hu.euclideanMollification_memLp_inner_ball (h n)
  have hmConv : Tendsto (fun n => eLpNorm (m n - u) 2 μ) atTop (𝓝 0) :=
    (hu.tendsto_eLpNorm_mollification_inner_ball hr).comp hScale
  have hD (n : ℕ) (i : Fin 2) : MemLp (D n i) 2 μ := hu.euclideanMollification_column_memLp_inner_ball (h n) (hMargin n) i
  have hConv (i : Fin 2) : Tendsto (fun n => eLpNorm (D n i - (fun x => Du x i)) 2 μ) atTop (𝓝 0) :=
    (hu.tendsto_eLpNorm_mollification_column_inner_ball hr i).comp hScale
  have hSq (i : Fin 2) := tendsto_integral_norm_sq_of_L2 (fun n => hD n i)
    ((hu.2.2 i).mono_measure hμ) (hConv i)
  have hHS : Tendsto (fun n => ∫ x, hsNormSq (fun i => D n i x) ∂μ) atTop
      (𝓝 (∫ x, hsNormSq (Du x) ∂μ)) := by
    have hE (n : ℕ) : (∫ x, hsNormSq (fun i => D n i x) ∂μ) =
        (∫ x, ‖D n 0 x‖ ^ 2 ∂μ) + ∫ x, ‖D n 1 x‖ ^ 2 ∂μ := by
      simp only [hsNormSq, Fin.sum_univ_two]
      exact integral_add ((hD n 0).integrable_norm_pow (by norm_num)) ((hD n 1).integrable_norm_pow (by norm_num))
    have hU : (∫ x, hsNormSq (Du x) ∂μ) = (∫ x, ‖Du x 0‖ ^ 2 ∂μ) + ∫ x, ‖Du x 1‖ ^ 2 ∂μ := by
      simp only [hsNormSq, Fin.sum_univ_two]
      exact integral_add (((hu.2.2 0).mono_measure hμ).integrable_norm_pow (by norm_num))
        (((hu.2.2 1).mono_measure hμ).integrable_norm_pow (by norm_num))
    simpa only [hE, hU] using (hSq 0).add (hSq 1)
  letI : IsFiniteMeasure μ := finite_planarVolume_restrict_ball r
  have hP := tendsto_integral_planarCoordinateBulkPotential_of_L2 a hmL (hu.2.1.mono_measure hμ)
    (fun n => Eventually.of_forall (hmB n)) (ae_mono hμ huC) hmConv
  refine ⟨m, hm, hmB, ?_, ?_⟩
  · simp_rw [planarSmoothEnergy_eq_weak a ε _ (hm _) r, planarWeakEnergy]
    exact (hHS.const_mul (1 / 2)).add (hP.const_mul (ε⁻¹ ^ 2))
  · intro V hV hVC K hK hKV η hη
    obtain ⟨δ, hδ, hBound⟩ := exists_euclideanMollification_uniform_radius Ω u hu.integrable_ball
      V hV hVC K hK hKV hη
    exact (hLim.eventually_lt_const hδ).mono fun n hn => hBound (h n) hn.le

private theorem planarWeakEnergy_mono (a : BulkCoefficients) (ε : ℝ)
    {u : Plane → Ambient 5} {Du : Plane → HarmonicMaps.Gradient 2 5}
    (hu : MemW12 (ballDomain (0 : Plane) 1) u Du) {C r : ℝ} (hr : r ≤ 1)
    (huC : ∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖u x‖ ≤ C) :
    planarWeakEnergy a ε u Du r ≤ planarWeakEnergy a ε u Du 1 := by
  have hSub : ball (0 : Plane) r ⊆ ball 0 1 := ball_subset_ball hr
  letI := finite_planarVolume_restrict_ball 1
  have hP : IntegrableOn (fun x => planarCoordinateBulkPotential a (u x)) (ball (0 : Plane) 1) :=
    integrable_planarCoordinateBulkPotential_of_bound a hu.2.1.aestronglyMeasurable huC
  unfold planarWeakEnergy
  exact add_le_add
    (mul_le_mul_of_nonneg_left (setIntegral_mono_set hu.integrable_hsNormSq
      (Eventually.of_forall fun _ => hsNormSq_nonneg _) (Eventually.of_forall hSub)) (by norm_num))
    (mul_le_mul_of_nonneg_left (setIntegral_mono_set hP
      (Eventually.of_forall fun _ => bulkPotential_nonneg a _) (Eventually.of_forall hSub)) (sq_nonneg _))

/-- The logarithmic lower bound for an actual Sobolev disk whose tensor
representative is continuous on the positive-gap collar used in the proof. -/
theorem exists_planarWeakEnergy_continuous_collar_lower (hcoarea : External.PlanarScalarCoarea)
    (a : BulkCoefficients) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε g : ℝ}, 0 < ε → 0 < g →
    ∀ (u : Plane → Ambient 5) (Du : Plane → HarmonicMaps.Gradient 2 5),
      MemW12 (ballDomain (0 : Plane) 1) u Du →
      (∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖u x‖ ≤ C₀) →
      (∀ x : Plane, (1 / 40 : ℝ) ≤ ‖x‖ → ‖x‖ ≤ 39 / 40 →
        g ≤ normalizedSpectralGap a (frobeniusCoordinateEquiv.symm (u x))) →
      ∀ (V : OpenDomain 2), V.val ⊆ ball (0 : Plane) 1 → ContinuousOn u V.val →
        (∀ x : Plane, (1 / 40 : ℝ) ≤ ‖x‖ → ‖x‖ ≤ 39 / 40 → x ∈ V.val) →
      ∀ p : C(NativeCircle, vacuum a),
        (∀ z, p z = spectralVacuumPoint a (frobeniusCoordinateEquiv.symm (u ((39 / 40 : ℝ) • z.val)))) →
        nativeVacuumCircleCost a p * g ^ 2 * Real.log (1 / ε) - C ≤ planarWeakEnergy a ε u Du 1 := by
  obtain ⟨C, hC, hSmooth⟩ := exists_planarSmooth_annular_gap_lower hcoarea a C₀
  refine ⟨C, hC, ?_⟩
  intro ε g hε hg u Du hu huC huGap V hV hVC hIn p hp
  let R : ℝ := 39 / 40
  let K : Set Plane := closedBall (0 : Plane) R \ ball 0 (1 / 40)
  have hK : IsCompact K := (isCompact_closedBall _ _).diff isOpen_ball
  have hKR (x : Plane) : x ∈ K ↔ (1 / 40 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ R := by
    simp only [K, Set.mem_sdiff, mem_ball, mem_closedBall, dist_zero_right, not_lt, and_comm]
  have hKV : K ⊆ V.val := fun x hx => hIn x ((hKR x).1 hx).1 ((hKR x).1 hx).2
  let Q (x : Plane) := frobeniusCoordinateEquiv.symm (u x)
  have hQ : ContinuousOn Q V.val := frobeniusCoordinateEquiv.symm.continuous.comp_continuousOn hVC
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hQ.mono hKV)
  obtain ⟨m, hm, hmNorm, hEnergy, hUniform⟩ :=
    exists_planarSmoothEnergy_approximation a ε hu hC₀ (show R < 1 by norm_num [R]) huC
  let Qm (n : ℕ) (x : Plane) := frobeniusCoordinateEquiv.symm (m n x)
  have hQm (n : ℕ) : ContDiff ℝ 1 (Qm n) :=
    frobeniusCoordinateEquiv.symm.toContinuousLinearMap.contDiff.comp ((hm n).of_le (by decide))
  let e := nativeVacuumCircleCost a p
  let F (s : ℝ) := e * s ^ 2 * Real.log (1 / ε) - C
  have hClosed : IsClosed {s : ℝ | F s ≤ planarWeakEnergy a ε u Du R} :=
    isClosed_le (by dsimp only [F]; fun_prop) continuous_const
  suffices hAt : g ∈ {s : ℝ | F s ≤ planarWeakEnergy a ε u Du R} by
    exact (show F g ≤ planarWeakEnergy a ε u Du R from hAt).trans
      (planarWeakEnergy_mono a ε hu (show R ≤ 1 by norm_num [R]) huC)
  apply closure_minimal ?_ hClosed (show g ∈ closure (Ioo (0 : ℝ) g) by
    rw [closure_Ioo hg.ne]
    exact right_mem_Icc.mpr hg.le)
  intro s hs
  have hδGap : 0 < g - s := sub_pos.mpr hs.2
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (IsCompact.uniformContinuousOn_of_continuous (isCompact_closedBall (0 : S0) (M + 1))
      (continuous_normalizedSpectralGap a).continuousOn) (g - s) hδGap
  have hClose : ∀ᶠ n in atTop, ∀ x ∈ K, ‖Qm n x - Q x‖ < min δ 1 := by
    filter_upwards [hUniform V hV hVC K hK hKV (min δ 1) (lt_min hδ zero_lt_one)] with n hn x hx
    rw [show Qm n x - Q x = frobeniusCoordinateEquiv.symm (m n x - u x) from (map_sub _ _ _).symm,
      frobeniusCoordinateEquiv.symm.norm_map]
    exact hn x hx
  have hBound : ∀ᶠ n in atTop, F s ≤ planarSmoothEnergy a ε (Qm n) R := by
    filter_upwards [hClose] with n hn
    let Qτ (t : unitInterval) (x : Plane) := Q x + t.val • (Qm n x - Q x)
    have hSegGap (t : unitInterval) (x : Plane) (hx : x ∈ K) :
        s ≤ normalizedSpectralGap a (Qτ t x) := by
      have hDiff : dist (Qτ t x) (Q x) < min δ 1 := by
        rw [dist_eq_norm, show Qτ t x - Q x = t.val • (Qm n x - Q x) by dsimp only [Qτ]; abel,
          norm_smul, Real.norm_of_nonneg t.property.1]
        exact ((mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)).trans_eq (one_mul _)).trans_lt (hn x hx)
      have hBoundQ : Q x ∈ closedBall (0 : S0) (M + 1) :=
        mem_closedBall_zero_iff.mpr ((hM x hx).trans (by linarith))
      have hBoundQt : Qτ t x ∈ closedBall (0 : S0) (M + 1) := by
        apply mem_closedBall_zero_iff.mpr
        have hBt := dist_triangle (Qτ t x) (Q x) 0
        simp only [dist_zero_right] at hBt
        exact hBt.trans (by linarith only [hDiff.trans_le (min_le_right _ _), hM x hx])
      have hG := hU (Qτ t x) hBoundQt (Q x) hBoundQ (hDiff.trans_le (min_le_left _ _))
      have hGineq := (abs_lt.mp (by simpa only [Real.dist_eq] using hG)).1
      have hOrig := huGap x ((hKR x).1 hx).1 ((hKR x).1 hx).2
      linarith only [hOrig, hGineq]
    have hAnn (x : Plane) (hx : (1 / 40 : ℝ) ≤ ‖x‖) (hxR : ‖x‖ ≤ R) :
        s ≤ normalizedSpectralGap a (Qm n x) := by
      simpa [Qτ] using hSegGap 1 x ((hKR x).2 ⟨hx, hxR⟩)
    have hRC (z : NativeCircle) : R • z.val ∈ K := (hKR _).2 (by
      rw [planar_norm_on_circle (show 0 ≤ R by norm_num [R])]
      norm_num [R])
    have hSimple (z : NativeCircle) : Qm n (R • z.val) ∈ simpleSpectrumLocus :=
      simpleSpectrum_of_normalizedSpectralGap_pos a (hs.1.trans_le (hAnn _
        ((hKR _).1 (hRC z)).1 ((hKR _).1 (hRC z)).2))
    let q_m := planarSpectralCircleTrace a (Qm n) (show 0 ≤ R by norm_num [R])
      (hQm n).continuous.continuousOn hSimple
    have hRay : Continuous (fun z : NativeCircle => R • z.val) := by fun_prop
    have hQRay : Continuous (fun z : NativeCircle => Q (R • z.val)) :=
      hQ.comp_continuous hRay (fun z => hKV (hRC z))
    have hQmRay : Continuous (fun z : NativeCircle => Qm n (R • z.val)) := (hQm n).continuous.comp hRay
    let H (v : unitInterval × NativeCircle) := Qτ v.1 (R • v.2.val)
    have hH : Continuous H := (hQRay.comp continuous_snd).add (continuous_subtype_val.comp continuous_fst |>.smul
      ((hQmRay.sub hQRay).comp continuous_snd))
    have hHS (v : unitInterval × NativeCircle) : H v ∈ simpleSpectrumLocus :=
      simpleSpectrum_of_normalizedSpectralGap_pos a (hs.1.trans_le (hSegGap v.1 _ (hRC v.2)))
    have hP : Continuous (fun v => (spectralVacuumPoint a (H v)).val) :=
      (contDiffOn_spectralVacuumPoint a).continuousOn.comp_continuous hH hHS
    have hHom : p.Homotopic q_m := by
      refine ⟨⟨⟨fun v => spectralVacuumPoint a (H v), hP.subtype_mk _⟩, ?_, ?_⟩⟩
      · intro z
        change spectralVacuumPoint a (Qτ 0 (R • z.val)) = p z
        simpa [Qτ, Q] using (hp z).symm
      · intro z
        change spectralVacuumPoint a (Qτ 1 (R • z.val)) = spectralVacuumPoint a (Qm n (R • z.val))
        simp [Qτ]
    have hCost := nativeVacuumCircleCost_homotopic a hHom
    have hMain := hSmooth hε hs.1 (Qm n) (hQm n).contDiffOn (hQm n).continuous.continuousOn
      (fun x _ => by simpa only [Qm, frobeniusCoordinateEquiv.symm.norm_map] using hmNorm n x) hAnn
    change ENNReal.ofReal (nativeVacuumCircleCost a q_m * s ^ 2 * Real.log (1 / ε) - C) ≤ _ at hMain
    rw [← hCost] at hMain
    have hInt : IntegrableOn (planarSmoothEnergyDensity a ε (Qm n)) (ball (0 : Plane) R) :=
      ((continuous_planarSmoothEnergyDensity a ε (hQm n)).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : Plane) R)).mono_set ball_subset_closedBall
    rw [← ofReal_integral_eq_lintegral_ofReal hInt
      (Eventually.of_forall (planarSmoothEnergyDensity_nonneg a ε (Qm n)))] at hMain
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (planarSmoothEnergyDensity_nonneg a ε (Qm n)))).mp hMain
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hEnergy hBound

end Thesis
