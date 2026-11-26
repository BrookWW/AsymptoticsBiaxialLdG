module

public import Thesis.Upstream.MinimizingSobolev
public import Thesis.Variational.EulerLagrange
public import HarmonicMaps.Analysis.SmoothWeakGradient
public import HarmonicMaps.Analysis.SobolevL2Closure

/-! Zero extension in the Sobolev trace class, global-to-local minimality, and
the radial comparison for global penalized minimizers. -/

public section

open Set Filter MeasureTheory Topology
open scoped BigOperators ContDiff ENNReal NNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance globalComparisonContinuousENormS0 : ContinuousENorm S0 := @SeminormedAddGroup.toContinuousENorm S0 inferInstance

variable {Ω U : Set Point}

private theorem eLpNorm_sub_indicator {E : Type*} [NormedAddCommGroup E]
    {f g : Point → E} (hU : MeasurableSet U) (hf : ∀ x ∉ U, f x = 0) (p : ℝ≥0∞) :
    eLpNorm (f - U.indicator g) p volume = eLpNorm (f - g) p (volume.restrict U) := by
  have h : f - U.indicator g = U.indicator (f - g) := by
    funext x
    by_cases hx : x ∈ U
    · simp only [Pi.sub_apply, indicator_of_mem hx]
    · simp only [Pi.sub_apply, indicator_of_notMem hx, hf x hx, sub_zero]
  rw [h, eLpNorm_indicator_eq_eLpNorm_restrict hU]

private theorem tendsto_eLpNorm_restrict {E : Type*} [NormedAddCommGroup E]
    {f : ℕ → Point → E} {p : ℝ≥0∞}
    (h : Tendsto (fun k => eLpNorm (f k) p volume) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k) p (volume.restrict Ω)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)

private theorem frobeniusField_indicator (U : Set Point) (u : Point → S0) :
    frobeniusField (U.indicator u) = U.indicator (frobeniusField u) := by
  classical
  funext x
  by_cases hx : x ∈ U
  · simp only [frobeniusField, indicator_of_mem hx]
  · simp only [frobeniusField, indicator_of_notMem hx, map_zero]

private theorem frobeniusGradient_indicator (U : Set Point) (D : Point → Gradient)
    (j : Fin 3) :
    (fun x => frobeniusGradient (U.indicator D) x j) =
      U.indicator (fun x => frobeniusGradient D x j) := by
  classical
  funext x
  by_cases hx : x ∈ U
  · simp only [frobeniusGradient, indicator_of_mem hx]
  · simp only [frobeniusGradient, indicator_of_notMem hx, Pi.zero_apply, map_zero]

private theorem memW12_of_smooth_compactSupport (W : HarmonicMaps.OpenDomain 3)
    {f : Point → HarmonicMaps.Ambient 5} (hf : ContDiff ℝ ∞ f) (hK : HasCompactSupport f) :
    HarmonicMaps.MemW12 W f (fun x j => coordDeriv j f x) := by
  have hμ : (volume : Measure Point).restrict W.val ≤ volume := Measure.restrict_le_self
  apply HarmonicMaps.memW12_of_contDiff W hf
  · exact (hf.continuous.memLp_of_hasCompactSupport hK).mono_measure hμ
  · intro j
    exact (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hK.fderiv_apply ℝ (axis j))).mono_measure hμ

/-- Extending a zero-trace field and its weak-gradient columns by zero preserves
the intrinsic zero trace in any larger open set. -/
theorem HasZeroTrace.zeroExtend {u : Point → S0} {D : Point → Gradient}
    (h : HasZeroTrace U u D) (hU : IsOpen U) (hΩ : IsOpen Ω) (hSub : U ⊆ Ω) :
    HasZeroTrace Ω (U.indicator u) (U.indicator D) := by
  classical
  let U' : HarmonicMaps.OpenDomain 3 := ⟨U, hU⟩
  let Ω' : HarmonicMaps.OpenDomain 3 := ⟨Ω, hΩ⟩
  let z := U.indicator u
  let Z := U.indicator D
  obtain ⟨hu, f, hf, hSupp, hMap, hGrad⟩ :=
    (hasZeroTrace_iff_hasZeroBoundaryValues U' u D).mp h
  have hz : MemLp (frobeniusField z) 2 volume := by
    change MemLp (frobeniusField (U.indicator u)) 2 volume
    rw [frobeniusField_indicator]
    exact (memLp_indicator_iff_restrict hU.measurableSet).mpr hu.2.1
  have hZ (j : Fin 3) : MemLp (fun x => frobeniusGradient Z x j) 2 volume := by
    change MemLp (fun x => frobeniusGradient (U.indicator D) x j) 2 volume
    rw [frobeniusGradient_indicator]
    exact (memLp_indicator_iff_restrict hU.measurableSet).mpr (hu.2.2 j)
  have hNz (k : ℕ) :
      eLpNorm (f k - frobeniusField z) 2 volume =
        eLpNorm (f k - frobeniusField u) 2 (volume.restrict U) := by
    change eLpNorm (f k - frobeniusField (U.indicator u)) 2 volume = _
    rw [frobeniusField_indicator]
    exact eLpNorm_sub_indicator hU.measurableSet
      (fun x hx => image_eq_zero_of_notMem_tsupport (fun hs => hx ((hSupp k).2 hs))) 2
  have hNZ (k : ℕ) (j : Fin 3) :
      eLpNorm (fun x => coordDeriv j (f k) x - frobeniusGradient Z x j) 2 volume =
        eLpNorm (fun x => coordDeriv j (f k) x - frobeniusGradient D x j)
          2 (volume.restrict U) := by
    change eLpNorm (coordDeriv j (f k) - (fun x => frobeniusGradient (U.indicator D) x j))
      2 volume = _
    rw [frobeniusGradient_indicator]
    apply eLpNorm_sub_indicator hU.measurableSet _ 2
    intro x hx
    have hx' : x ∉ tsupport (f k) := fun hs => hx ((hSupp k).2 hs)
    simp only [coordDeriv, fderiv_of_notMem_tsupport ℝ hx', zero_apply]
  have hCz : Tendsto (fun k => eLpNorm (f k - frobeniusField z) 2 volume) atTop (𝓝 0) := by
    simp_rw [hNz]
    exact hMap
  have hCZ (j : Fin 3) : Tendsto
      (fun k => eLpNorm (fun x => coordDeriv j (f k) x - frobeniusGradient Z x j) 2 volume)
      atTop (𝓝 0) := by
    simp_rw [hNZ]
    exact hGrad j
  have hLoc : MemH1Loc Ω z Z := by
    intro W hW hWc
    let W' : HarmonicMaps.OpenDomain 3 := ⟨W, hW⟩
    letI : IsFiniteMeasure (volume.restrict W'.val) :=
      isFiniteMeasure_restrict.mpr ((measure_mono subset_closure).trans_lt hWc.1.measure_lt_top).ne
    apply (memH1_iff_memW12 W' z Z).mpr
    exact HarmonicMaps.MemW12.of_L2_limit
      (fun k => memW12_of_smooth_compactSupport W' (hf k) (hSupp k).1)
      (hz.mono_measure Measure.restrict_le_self)
      (fun j => (hZ j).mono_measure Measure.restrict_le_self)
      (tendsto_eLpNorm_restrict hCz) (fun j => tendsto_eLpNorm_restrict (hCZ j))
  apply (hasZeroTrace_iff_hasZeroBoundaryValues Ω' z Z).mpr
  refine ⟨?_, f, hf, fun k => ⟨(hSupp k).1, (hSupp k).2.trans hSub⟩,
    tendsto_eLpNorm_restrict hCz, fun j => tendsto_eLpNorm_restrict (hCZ j)⟩
  apply (memH1_iff_memW12 Ω' z Z).mp
  exact ⟨(frobeniusCoordinateEquiv_memLp_iff (volume.restrict Ω) 2 z).1
      (hz.mono_measure Measure.restrict_le_self),
    fun j => (frobeniusCoordinateEquiv_memLp_iff (volume.restrict Ω) 2 (fun x => Z x j)).1
      ((hZ j).mono_measure Measure.restrict_le_self),
    hLoc.isWeakGradient hΩ⟩

private theorem tendsto_eLpNorm_add_two {μ : Measure Point}
    {f g : ℕ → Point → HarmonicMaps.Ambient 5}
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) (hg : ∀ k, AEStronglyMeasurable (g k) μ)
    (hF : Tendsto (fun k => eLpNorm (f k) 2 μ) atTop (𝓝 0))
    (hG : Tendsto (fun k => eLpNorm (g k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k + g k) 2 μ) atTop (𝓝 0) := by
  have hadd : Tendsto (fun k => eLpNorm (f k) 2 μ + eLpNorm (g k) 2 μ) atTop (𝓝 0) := by
    simpa only [add_zero] using hF.add hG
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hadd
    (fun _ => zero_le) (fun k => eLpNorm_add_le (hf k) (hg k) (by norm_num))

/-- The difference of two successive trace comparisons can be assembled from
the two zero-trace fields in the intrinsic Sobolev closure. -/
theorem HasZeroTrace.add {u v : Point → S0} {D G : Point → Gradient}
    (hΩ : IsOpen Ω) (hu : HasZeroTrace Ω u D) (hv : HasZeroTrace Ω v G) :
    HasZeroTrace Ω (u + v) (D + G) := by
  let W : HarmonicMaps.OpenDomain 3 := ⟨Ω, hΩ⟩
  let μ := volume.restrict Ω
  obtain ⟨huW, f, hf, hfSupp, hfMap, hfGrad⟩ := (hasZeroTrace_iff_hasZeroBoundaryValues W u D).mp hu
  obtain ⟨hvW, g, hg, hgSupp, hgMap, hgGrad⟩ := (hasZeroTrace_iff_hasZeroBoundaryValues W v G).mp hv
  apply (hasZeroTrace_iff_hasZeroBoundaryValues W (u + v) (D + G)).mpr
  refine ⟨(memH1_iff_memW12 W _ _).mp (MemH1.add hu.1 hv.1), fun k => f k + g k,
    fun k => (hf k).add (hg k), ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hfSupp k).1.add (hgSupp k).1,
      (tsupport_add (f k) (g k)).trans (union_subset (hfSupp k).2 (hgSupp k).2)⟩
  · have hF : frobeniusField (u + v) = frobeniusField u + frobeniusField v := by
      funext x
      exact map_add frobeniusCoordinateEquiv (u x) (v x)
    have hErr (k : ℕ) : f k + g k - frobeniusField (u + v) =
        (f k - frobeniusField u) + (g k - frobeniusField v) := by rw [hF]; abel
    change Tendsto (fun k => eLpNorm (f k + g k - frobeniusField (u + v)) 2 μ) atTop (𝓝 0)
    simp_rw [hErr]
    exact tendsto_eLpNorm_add_two
      (fun k => (hf k).continuous.aestronglyMeasurable.sub huW.2.1.1)
      (fun k => (hg k).continuous.aestronglyMeasurable.sub hvW.2.1.1) hfMap hgMap
  · intro j
    have hErr (k : ℕ) :
        (fun x => coordDeriv j (f k + g k) x - frobeniusGradient (D + G) x j) =
          (fun x => coordDeriv j (f k) x - frobeniusGradient D x j) +
            (fun x => coordDeriv j (g k) x - frobeniusGradient G x j) := by
      funext x
      have hS : coordDeriv j (f k + g k) x =
          coordDeriv j (f k) x + coordDeriv j (g k) x :=
        DFunLike.congr_fun (fderiv_add ((hf k).differentiable (by simp) x)
          ((hg k).differentiable (by simp) x)) (axis j)
      have hD : frobeniusGradient (D + G) x j =
          frobeniusGradient D x j + frobeniusGradient G x j :=
        map_add frobeniusCoordinateEquiv (D x j) (G x j)
      rw [hS, hD]
      change _ = (coordDeriv j (f k) x - frobeniusGradient D x j) +
        (coordDeriv j (g k) x - frobeniusGradient G x j)
      abel
    change Tendsto (fun k => eLpNorm
      (fun x => coordDeriv j (f k + g k) x - frobeniusGradient (D + G) x j) 2 μ) atTop (𝓝 0)
    simp_rw [hErr]
    exact tendsto_eLpNorm_add_two
      (fun k => ((hf k).continuous_fderiv (by simp) |>.clm_apply continuous_const).aestronglyMeasurable.sub
        (huW.2.2 j).1)
      (fun k => ((hg k).continuous_fderiv (by simp) |>.clm_apply continuous_const).aestronglyMeasurable.sub
        (hvW.2.2 j).1) (hfGrad j) (hgGrad j)

theorem SameTrace.trans {u v w : Point → S0} {D G H : Point → Gradient}
    (hΩ : IsOpen Ω) (huv : SameTrace Ω u v D G) (hvw : SameTrace Ω v w G H) :
    SameTrace Ω u w D H := by
  change HasZeroTrace Ω (u - w) (D - H)
  simpa only [sub_add_sub_cancel] using HasZeroTrace.add hΩ huv hvw

theorem HasZeroTrace.zero (hΩ : IsOpen Ω) : HasZeroTrace Ω (0 : Point → S0) (0 : Point → Gradient) := by
  have hc : HasCompactSupport (0 : Point → S0) := by
    change IsCompact (tsupport (0 : Point → S0))
    rw [tsupport_zero]
    exact isCompact_empty
  have h := hasZeroTrace_of_contDiff_hasCompactSupport (u := (0 : Point → S0))
    hΩ contDiff_const hc (by rw [tsupport_zero]; exact empty_subset Ω)
  have hD : ClassicalGradient (0 : Point → S0) = 0 := by
    funext x j
    simp only [ClassicalGradient, coordDeriv, fderiv_zero, zero_apply, Pi.zero_apply]
  exact hD ▸ h

theorem SameTrace.refl (hΩ : IsOpen Ω) (u : Point → S0) (D : Point → Gradient) :
    SameTrace Ω u u D D := by
  simpa only [SameTrace, sub_self] using HasZeroTrace.zero hΩ

theorem HasSmoothTrace.add_zeroTrace {u z : Point → S0} {D Z : Point → Gradient}
    {b : frontier Ω → S0} (h : HasSmoothTrace Ω u D b) (hz : HasZeroTrace Ω z Z)
    (hΩ : IsOpen Ω) : HasSmoothTrace Ω (u + z) (D + Z) b := by
  obtain ⟨B, hB, hboundary, htrace⟩ := h
  refine ⟨B, hB, hboundary, ?_⟩
  change HasZeroTrace Ω ((u + z) - B) ((D + Z) - ClassicalGradient B)
  have hU : (u + z) - B = (u - B) + z := by abel
  have hD : (D + Z) - ClassicalGradient B = (D - ClassicalGradient B) + Z := by abel
  rw [hU, hD]
  exact HasZeroTrace.add hΩ htrace hz

/-- Replace the original field on a set by the comparison field. -/
noncomputable def replaceOn {E : Type*} [AddCommGroup E]
    (U : Set Point) (u v : Point → E) : Point → E :=
  u + U.indicator (v - u)

theorem replaceOn_of_mem {E : Type*} [AddCommGroup E] {u v : Point → E}
    {x : Point} (hx : x ∈ U) : replaceOn U u v x = v x := by
  simp only [replaceOn, Pi.add_apply, indicator_of_mem hx, Pi.sub_apply]
  abel

theorem replaceOn_of_notMem {E : Type*} [AddCommGroup E] {u v : Point → E}
    {x : Point} (hx : x ∉ U) : replaceOn U u v x = u x := by
  simp only [replaceOn, Pi.add_apply, indicator_of_notMem hx, add_zero]

/-- The piecewise comparison has the prescribed outer trace and the displayed
actual gradient assembled from both pieces. -/
theorem HasSmoothTrace.replaceOn {u v : Point → S0} {D G : Point → Gradient}
    {b : frontier Ω → S0} (hTrace : HasSmoothTrace Ω u D b) (hu : MemH1 Ω u D)
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hSub : U ⊆ Ω) (hv : SameTrace U v u G D) :
    MemH1 Ω (replaceOn U u v) (replaceOn U D G) ∧
      HasSmoothTrace Ω (replaceOn U u v) (replaceOn U D G) b := by
  have hZ := HasZeroTrace.zeroExtend hv hU hΩ hSub
  exact ⟨MemH1.add hu hZ.1, hTrace.add_zeroTrace hZ hΩ⟩

theorem TakesVacuumValues.replaceOn {a : BulkCoefficients} {u v : Point → S0}
    (hu : TakesVacuumValues a Ω u) (hv : TakesVacuumValues a U v)
    (hΩ : MeasurableSet Ω) (hU : MeasurableSet U) :
    TakesVacuumValues a Ω (Thesis.replaceOn U u v) := by
  change ∀ᵐ x ∂volume.restrict Ω, Thesis.replaceOn U u v x ∈ vacuum a
  rw [ae_restrict_iff' hΩ]
  filter_upwards [(ae_restrict_iff' hΩ).mp hu, (ae_restrict_iff' hU).mp hv] with x h₁ h₂ hx
  by_cases hxU : x ∈ U
  · rw [replaceOn_of_mem hxU]
    exact h₂ hxU
  · rw [replaceOn_of_notMem hxU]
    exact h₁ hx

private theorem lintegral_partition (hU : MeasurableSet U) (hSub : U ⊆ Ω)
    (f : Point → ℝ≥0∞) :
    (∫⁻ x in Ω, f x) = (∫⁻ x in U, f x) + ∫⁻ x in Ω \ U, f x := by
  have hD : Disjoint (Ω \ U) U := disjoint_left.mpr fun _ hx hy => hx.2 hy
  calc
    _ = ∫⁻ x in (Ω \ U) ∪ U, f x := by rw [sdiff_union_of_subset hSub]
    _ = (∫⁻ x in Ω \ U, f x) + ∫⁻ x in U, f x := lintegral_union hU hD
    _ = _ := add_comm _ _

private theorem lintegral_eqOn_partition (hΩ : MeasurableSet Ω) (hU : MeasurableSet U)
    (hSub : U ⊆ Ω) {f g k : Point → ℝ≥0∞} (hIn : EqOn f g U) (hOut : EqOn f k (Ω \ U)) :
    (∫⁻ x in Ω, f x) = (∫⁻ x in U, g x) + ∫⁻ x in Ω \ U, k x := by
  rw [lintegral_partition hU hSub f,
    lintegral_congr_ae ((ae_restrict_mem hU).mono fun _ hx => hIn hx),
    lintegral_congr_ae ((ae_restrict_mem (hΩ.diff hU)).mono fun _ hx => hOut hx)]

theorem energy_replaceOn (a : BulkCoefficients) (ε : ElasticScale)
    {u v : Point → S0} {D G : Point → Gradient}
    (hΩ : MeasurableSet Ω) (hU : MeasurableSet U) (hSub : U ⊆ Ω) :
    energy a ε Ω (replaceOn U u v) (replaceOn U D G) =
      energy a ε U v G + energy a ε (Ω \ U) u D := by
  apply lintegral_eqOn_partition hΩ hU hSub
  · intro x hx
    simp only [replaceOn_of_mem hx]
  · intro x hx
    simp only [replaceOn_of_notMem hx.2]

theorem dirichletEnergy_replaceOn {D G : Point → Gradient}
    (hΩ : MeasurableSet Ω) (hU : MeasurableSet U) (hSub : U ⊆ Ω) :
    dirichletEnergy Ω (replaceOn U D G) =
      dirichletEnergy U G + dirichletEnergy (Ω \ U) D := by
  apply lintegral_eqOn_partition hΩ hU hSub
  · intro x hx
    simp only [replaceOn_of_mem hx]
  · intro x hx
    simp only [replaceOn_of_notMem hx.2]

/-- A zero-trace competitor on any open subregion of an admissible
comparison ball is tested by the original ball minimality. -/
theorem IsLocalEnergyMinimizer.energy_le_on_open_subregion
    {a : BulkCoefficients} {ε : ElasticScale} {u v : Point → S0} {D G : Point → Gradient}
    (h : IsLocalEnergyMinimizer a ε Ω u D) (hFinite : energy a ε Ω u D < ⊤)
    {c : Point} {r : ℝ} (hr : 0 < r) (hBall : Metric.closedBall c r ⊆ Ω)
    (hU : IsOpen U) (hSub : U ⊆ Metric.ball c r)
    (hTrace : SameTrace U v u G D) :
    energy a ε U u D ≤ energy a ε U v G := by
  let B := Metric.ball c r
  have hB : IsOpen B := Metric.isOpen_ball
  have hC : CompactlyContained B Ω := by
    unfold CompactlyContained
    rw [closure_ball c hr.ne']
    exact ⟨isCompact_closedBall _ _, hBall⟩
  have hZ := hTrace.zeroExtend hU hB hSub
  have hW : MemH1 B (replaceOn U u v) (replaceOn U D G) :=
    MemH1.add (h.1 B hB hC) hZ.1
  have hT : SameTrace B (replaceOn U u v) u (replaceOn U D G) D := by
    change HasZeroTrace B (replaceOn U u v - u) (replaceOn U D G - D)
    simpa only [replaceOn, add_sub_cancel_left] using hZ
  have hMin := h.2 c r hr hBall (replaceOn U u v) (replaceOn U D G) hW hT
  rw [energy_replaceOn a ε hB.measurableSet hU.measurableSet hSub,
    show energy a ε B u D = energy a ε U u D + energy a ε (B \ U) u D from
      lintegral_partition hU.measurableSet hSub _] at hMin
  have hOutside : energy a ε (B \ U) u D ≠ ⊤ :=
    ne_top_of_le_ne_top hFinite.ne (lintegral_mono_set (sdiff_subset.trans
      (Metric.ball_subset_closedBall.trans hBall)))
  exact (ENNReal.add_le_add_iff_right hOutside).1 hMin

theorem dirichletEnergy_eq_ofReal_integral {D : Point → Gradient}
    (hD : ∀ j, MemLp (fun x => D x j) 2 (volume.restrict U)) :
    dirichletEnergy U D = ENNReal.ofReal (∫ x in U, (1 / 2 : ℝ) * gradientNormSq (D x)) := by
  have hD₂ (j : Fin 3) : Integrable (fun x => ‖D x j‖ ^ 2) (volume.restrict U) :=
    (hD j).integrable_norm_pow (p := 2) (by decide)
  have hI : Integrable (fun x => (1 / 2 : ℝ) * gradientNormSq (D x)) (volume.restrict U) := by
    simp only [gradientNormSq_eq_sum_norm_sq]
    exact (integrable_finsetSum Finset.univ (fun j _ => hD₂ j)).const_mul _
  exact (ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun x => by
    change (0 : ℝ) ≤ (1 / 2 : ℝ) * gradientNormSq (D x)
    rw [gradientNormSq_eq_sum_norm_sq]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _))).symm

theorem dirichletEnergy_lt_top_of_memLp {D : Point → Gradient}
    (hD : ∀ j, MemLp (fun x => D x j) 2 (volume.restrict U)) : dirichletEnergy U D < ⊤ := by
  rw [dirichletEnergy_eq_ofReal_integral hD]
  exact ENNReal.ofReal_lt_top

/-- Finite penalized energy of a global minimizer on a bounded open set
follows by comparison with its smooth trace lift. -/
theorem IsGlobalEnergyMinimizer.energy_lt_top {a : BulkCoefficients} {ε : ElasticScale}
    {b : frontier Ω → S0} {u : Point → S0} {D : Point → Gradient}
    (h : IsGlobalEnergyMinimizer a ε Ω b u D) (hΩ : IsOpen Ω)
    (hBound : Bornology.IsBounded Ω) : energy a ε Ω u D < ⊤ := by
  obtain ⟨B, hB, hBoundary, _⟩ := h.2.1
  have hBΩ : MemH1 Ω B (ClassicalGradient B) :=
    memH1Loc_of_contDiffOn isOpen_univ (hB.of_le (by simp)).contDiffOn
      Ω hΩ ⟨hBound.isCompact_closure, subset_univ _⟩
  have hVol : (volume : Measure Point) Ω ≠ ⊤ := hBound.measure_lt_top.ne
  letI := isFiniteMeasure_restrict.mpr hVol
  obtain ⟨K, hK⟩ := hBound.isCompact_closure.exists_bound_of_continuousOn hB.continuous.continuousOn
  have hB6 : MemLp B 6 (volume.restrict Ω) := MemLp.of_bound hBΩ.1.1 K
    ((ae_restrict_mem hΩ.measurableSet).mono fun x hx => hK x (subset_closure hx))
  have hTrace : HasSmoothTrace Ω B (ClassicalGradient B) b :=
    ⟨B, hB, hBoundary, SameTrace.refl hΩ B _⟩
  exact (h.2.2 B (ClassicalGradient B) hBΩ hTrace).trans_lt
    (energy_lt_top_of_memLp_six a ε hVol hB6 hBΩ.2.1)

theorem IsGlobalEnergyMinimizer.isLocalEnergyMinimizer_of_energy_lt_top
    {a : BulkCoefficients} {ε : ElasticScale} {b : frontier Ω → S0}
    {u : Point → S0} {D : Point → Gradient} (h : IsGlobalEnergyMinimizer a ε Ω b u D)
    (hΩ : IsOpen Ω) (hFin : energy a ε Ω u D < ⊤) :
    IsLocalEnergyMinimizer a ε Ω u D := by
  refine ⟨h.1.memH1Loc, fun x r _ hBall v G _ hv => ?_⟩
  let B := Metric.ball x r
  have hB : IsOpen B := Metric.isOpen_ball
  have hSub : B ⊆ Ω := Metric.ball_subset_closedBall.trans hBall
  have hAdm := h.2.1.replaceOn h.1 hΩ hB hSub hv
  have hmin := h.2.2 (replaceOn B u v) (replaceOn B D G) hAdm.1 hAdm.2
  rw [energy_replaceOn a ε hΩ.measurableSet hB.measurableSet hSub] at hmin
  have hOriginal : energy a ε Ω u D = energy a ε B u D + energy a ε (Ω \ B) u D :=
    lintegral_partition hB.measurableSet hSub _
  rw [hOriginal] at hmin
  have hOutside : energy a ε (Ω \ B) u D ≠ ⊤ := by
    unfold energy at hFin ⊢
    exact ne_of_lt ((lintegral_mono' (Measure.restrict_mono_set volume sdiff_subset) le_rfl).trans_lt hFin)
  exact (ENNReal.add_le_add_iff_right hOutside).mp hmin

theorem IsGlobalEnergyMinimizer.isLocalEnergyMinimizer
    {a : BulkCoefficients} {ε : ElasticScale} {b : frontier Ω → S0}
    {u : Point → S0} {D : Point → Gradient} (h : IsGlobalEnergyMinimizer a ε Ω b u D)
    (hΩ : IsOpen Ω) (hBound : Bornology.IsBounded Ω) :
    IsLocalEnergyMinimizer a ε Ω u D :=
  h.isLocalEnergyMinimizer_of_energy_lt_top hΩ (h.energy_lt_top hΩ hBound)

theorem IsGlobalDirichletMinimizer.isLocalDirichletMinimizer
    {a : BulkCoefficients} {b : frontier Ω → S0} {u : Point → S0} {D : Point → Gradient}
    (h : IsGlobalDirichletMinimizer a Ω b u D) (hΩ : IsOpen Ω) :
    IsLocalDirichletMinimizer a Ω u D := by
  refine ⟨h.1.memH1Loc, h.2.2.1, fun x r _ hBall v G _ hvVac hv => ?_⟩
  let B := Metric.ball x r
  have hB : IsOpen B := Metric.isOpen_ball
  have hSub : B ⊆ Ω := Metric.ball_subset_closedBall.trans hBall
  have hAdm := h.2.1.replaceOn h.1 hΩ hB hSub hv
  have hVac := h.2.2.1.replaceOn hvVac hΩ.measurableSet hB.measurableSet
  have hmin := h.2.2.2 (replaceOn B u v) (replaceOn B D G) hAdm.1 hAdm.2 hVac
  rw [dirichletEnergy_replaceOn hΩ.measurableSet hB.measurableSet hSub] at hmin
  have hOriginal : dirichletEnergy Ω D = dirichletEnergy B D + dirichletEnergy (Ω \ B) D :=
    lintegral_partition hB.measurableSet hSub _
  rw [hOriginal] at hmin
  have hSub' : Ω \ B ⊆ Ω := sdiff_subset
  have hOutside := dirichletEnergy_lt_top_of_memLp (D := D) (h.1.mono hSub').2.1
  exact (ENNReal.add_le_add_iff_right hOutside.ne).mp hmin

/-- Radial projection onto the closed norm ball of nonnegative radius. -/
noncomputable def radialProjection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (A : E) : E :=
  if ‖A‖ ≤ R then A else (R / ‖A‖) • A

theorem radialProjection_eq_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} {A : E} (hA : ‖A‖ ≤ R) : radialProjection R A = A :=
  if_pos hA

theorem norm_radialProjection_of_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 ≤ R) {A : E} (hA : R < ‖A‖) : ‖radialProjection R A‖ = R := by
  rw [radialProjection, if_neg hA.not_ge, norm_smul,
    Real.norm_of_nonneg (div_nonneg hR (norm_nonneg _)), div_mul_cancel₀ _ (hR.trans_lt hA).ne']

theorem norm_radialProjection_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 ≤ R) (A : E) : ‖radialProjection R A‖ ≤ R := by
  rcases le_or_gt ‖A‖ R with hA | hA
  · rw [radialProjection_eq_self hA]
    exact hA
  · exact (norm_radialProjection_of_lt hR hA).le

private theorem inner_radialProjection_le_zero {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 ≤ R) (A Z : E) (hZ : ‖Z‖ ≤ R) :
    inner ℝ (A - radialProjection R A) (Z - radialProjection R A) ≤ 0 := by
  rcases le_or_gt ‖A‖ R with hA | hA
  · rw [radialProjection_eq_self hA, sub_self, inner_zero_left]
  · let t := R / ‖A‖
    have hAn : 0 < ‖A‖ := hR.trans_lt hA
    have ht₀ : 0 ≤ t := div_nonneg hR hAn.le
    have ht : t ≤ 1 := (div_le_one hAn).2 hA.le
    have htMul : t * ‖A‖ = R := div_mul_cancel₀ R hAn.ne'
    have hI : inner ℝ A Z - t * ‖A‖ ^ 2 ≤ 0 := by
      rw [show t * ‖A‖ ^ 2 = ‖A‖ * R by rw [pow_two, ← mul_assoc, htMul, mul_comm]]
      exact sub_nonpos.mpr ((real_inner_le_norm A Z).trans
        (mul_le_mul_of_nonneg_left hZ hAn.le))
    rw [radialProjection, if_neg hA.not_ge]
    change inner ℝ (A - t • A) (Z - t • A) ≤ 0
    have hmul : inner ℝ (A - t • A) (Z - t • A) =
        (1 - t) * (inner ℝ A Z - t * ‖A‖ ^ 2) := by
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, norm_smul, Real.norm_of_nonneg ht₀, mul_pow]
      ring
    rw [hmul]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht) hI

private theorem lipschitzWith_radialProjection_innerProductSpace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 1 (radialProjection R : E → E) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  let P := radialProjection R A
  let Q := radialProjection R B
  have hP := inner_radialProjection_le_zero hR A Q (norm_radialProjection_le hR B)
  have hQ := inner_radialProjection_le_zero hR B P (norm_radialProjection_le hR A)
  have hPQ : ‖P - Q‖ ^ 2 ≤ inner ℝ (A - B) (P - Q) := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (A - P) (Q - P) ≤ 0 at hP
    change inner ℝ (B - Q) (P - Q) ≤ 0 at hQ
    simp only [inner_sub_left, inner_sub_right] at hP hQ ⊢
    linarith only [hP, hQ]
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  change ‖P - Q‖ ≤ ‖A - B‖
  rcases (norm_nonneg (P - Q)).eq_or_lt with h | h
  · rw [← h]
    exact norm_nonneg _
  · have hle := hPQ.trans (real_inner_le_norm (A - B) (P - Q))
    rw [pow_two] at hle
    exact le_of_mul_le_mul_right hle h

theorem lipschitzWith_radialProjection {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 1 (radialProjection R : S0 → S0) := by
  let e := frobeniusCoordinateEquiv
  have hE : LipschitzWith 1 (radialProjection R : EuclideanSpace ℝ (Fin 5) → _) :=
    lipschitzWith_radialProjection_innerProductSpace hR
  have hEq (A : S0) : e (radialProjection R A) = radialProjection R (e A) := by
    by_cases hA : ‖A‖ ≤ R
    · have hEA : ‖e A‖ ≤ R := (e.norm_map A).trans_le hA
      rw [radialProjection_eq_self hA, radialProjection_eq_self hEA]
    · simp only [radialProjection, if_neg hA, e.norm_map, map_smul]
  apply LipschitzWith.of_dist_le_mul
  intro A B
  calc
    _ = dist (e (radialProjection R A)) (e (radialProjection R B)) :=
      (e.isometry.dist_eq _ _).symm
    _ = dist (radialProjection R (e A)) (radialProjection R (e B)) := by rw [hEq, hEq]
    _ ≤ (1 : ℝ≥0) * dist (e A) (e B) := hE.dist_le_mul _ _
    _ = _ := by rw [e.isometry.dist_eq]

private theorem trace_sq_eq_norm_sq (A : S0) : ((A : Tensor) ^ 2).trace = ‖A‖ ^ 2 := by
  rw [norm_sq_eq_frobeniusS0, frobeniusS0, frobenius, A.transpose_eq, pow_two]

private theorem sq_vacuumNorm (a : BulkCoefficients) :
    (Real.sqrt 2 * vacuumRadius a) ^ 2 = preferredTraceSq a := by
  rw [mul_pow, Real.sq_sqrt (by norm_num), two_mul_vacuumRadius_sq]

/-- Outside the comparison ball the bulk potential strictly decreases along the
radial projection, provided the radius is at least the vacuum norm. -/
theorem bulkPotential_radialProjection_lt (a : BulkCoefficients) {R : ℝ}
    (hR : Real.sqrt 2 * vacuumRadius a ≤ R) {A : S0} (hA : R < ‖A‖) :
    bulkPotential a (radialProjection R A) < bulkPotential a A := by
  have hVac : 0 ≤ Real.sqrt 2 * vacuumRadius a :=
    mul_nonneg (Real.sqrt_nonneg _) (vacuumRadius_pos a).le
  have hRn := hVac.trans hR
  have hNorm := norm_radialProjection_of_lt hRn hA
  let t := preferredTraceSq a
  let U := ((radialProjection R A : S0) : Tensor) ^ 2 |>.trace
  let V := ((A : Tensor) ^ 2).trace
  let C (s : ℝ) := a.a4 / 4 + a.a6 / 6 * (s + 2 * t)
  have htU : t ≤ U := by
    change preferredTraceSq a ≤ (((radialProjection R A : S0) : Tensor) ^ 2).trace
    rw [trace_sq_eq_norm_sq, hNorm, ← sq_vacuumNorm a]
    exact pow_le_pow_left₀ hVac hR 2
  have hUV : U < V := by
    change (((radialProjection R A : S0) : Tensor) ^ 2).trace < ((A : Tensor) ^ 2).trace
    rw [trace_sq_eq_norm_sq, trace_sq_eq_norm_sq, hNorm]
    exact pow_lt_pow_left₀ hA hRn (by decide : (2 : ℕ) ≠ 0)
  have ht : 0 < t := preferredTraceSq_pos a
  have hCU : 0 < C U := by
    have hU : 0 ≤ U := ht.le.trans htU
    have h4 := a.a4_pos
    have h6 := a.a6_pos
    change 0 < a.a4 / 4 + a.a6 / 6 * (U + 2 * t)
    positivity
  have hCV : C U ≤ C V := by
    have h6 := a.a6_pos
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hUV.le le_rfl) (by positivity))
  have hStrict : (U - t) ^ 2 * C U < (V - t) ^ 2 * C V :=
    (mul_lt_mul_of_pos_right (pow_lt_pow_left₀ (sub_lt_sub_right hUV t)
      (sub_nonneg.mpr htU) (by decide : (2 : ℕ) ≠ 0)) hCU).trans_le
        (mul_le_mul_of_nonneg_left hCV (sq_nonneg _))
  let c := R / ‖A‖
  have hc0 : 0 ≤ c := div_nonneg hRn (norm_nonneg _)
  have hc1 : c ≤ 1 := (div_le_one (hRn.trans_lt hA)).2 hA.le
  have hCube :
      (((radialProjection R A : S0) : Tensor) ^ 3).trace ^ 2 ≤ (((A : Tensor) ^ 3).trace) ^ 2 := by
    have hPr : ((radialProjection R A : S0) : Tensor) = c • (A : Tensor) :=
      congrArg (fun A : S0 => (A : Tensor)) (if_neg hA.not_ge)
    rw [hPr, smul_pow, Matrix.trace_smul, smul_eq_mul, mul_pow, ← pow_mul]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hc0 hc1) (sq_nonneg _)).trans_eq (one_mul _)
  have h6' := a.a6'_pos
  rw [bulkPotential_factorization, bulkPotential_factorization]
  exact add_lt_add_of_lt_of_le hStrict (mul_le_mul_of_nonneg_left hCube (by positivity))

theorem bulkPotential_radialProjection_le (a : BulkCoefficients) {R : ℝ}
    (hR : Real.sqrt 2 * vacuumRadius a ≤ R) (A : S0) :
    bulkPotential a (radialProjection R A) ≤ bulkPotential a A := by
  rcases le_or_gt ‖A‖ R with hA | hA
  · rw [radialProjection_eq_self hA]
  · exact (bulkPotential_radialProjection_lt a hR hA).le

private theorem continuous_bulkPotential (a : BulkCoefficients) : Continuous (bulkPotential a) := by
  let tr : Tensor →L[ℝ] ℝ := (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap
  change Continuous (fun A : S0 =>
    let t := tr ((symmetricTraceless.subtypeL A) ^ 2)
    let s := tr ((symmetricTraceless.subtypeL A) ^ 3)
    let t₀ := preferredTraceSq a
    a.a2 / 2 * t₀ - a.a4 / 4 * t₀ ^ 2 - a.a6 / 6 * t₀ ^ 3
      - a.a2 / 2 * t + a.a4 / 4 * t ^ 2 + a.a6 / 6 * t ^ 3 + a.a6' / 6 * s ^ 2)
  fun_prop

private theorem aemeasurable_ofReal_energyDensity (a : BulkCoefficients) (ε : ElasticScale)
    {u : Point → S0} {D : Point → Gradient} (h : MemH1 Ω u D) :
    AEMeasurable (fun x => ENNReal.ofReal (energyDensity a ε (u x) (D x))) (volume.restrict Ω) := by
  have hPot : AEStronglyMeasurable (fun x => bulkPotential a (u x)) (volume.restrict Ω) :=
    Continuous.comp_aestronglyMeasurable (β := S0) (f := u) (g := bulkPotential a)
      (continuous_bulkPotential a) h.1.1
  let K (j : Fin 3) (x : Point) := ‖D x j‖ ^ 2
  have hK (j : Fin 3) : AEStronglyMeasurable (K j) (volume.restrict Ω) :=
    (continuous_pow 2).comp_aestronglyMeasurable (h.2.1 j).1.norm
  have hDsum : AEStronglyMeasurable (fun x => ∑ j, K j x) (volume.restrict Ω) :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ (fun j _ => hK j)
  apply ENNReal.continuous_ofReal.measurable.comp_aemeasurable
  have hE := (hDsum.const_mul (1 / 2 : ℝ)).add (hPot.const_mul ((ε : ℝ)⁻¹ ^ 2))
  have hEq : (fun x => energyDensity a ε (u x) (D x)) =
      fun x => (1 / 2 : ℝ) * (∑ k, K k x) + (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (u x) := by
    funext x
    rw [energyDensity, gradientNormSq_eq_sum_norm_sq]
  rw [hEq]
  exact hE.aemeasurable

private theorem energyDensity_nonneg (a : BulkCoefficients) (ε : ElasticScale)
    (A : S0) (D : Gradient) : 0 ≤ energyDensity a ε A D := by
  rw [energyDensity, gradientNormSq_eq_sum_norm_sq]
  exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a A))

/-- A projection comparison with nonincreasing gradient columns has no greater
energy. The energy is strictly smaller when the projected region has positive volume. -/
theorem energy_radialProjection_comparison
    (a : BulkCoefficients) (ε : ElasticScale) {u : Point → S0} {D G : Point → Gradient}
    (hu : MemH1 Ω u D) (hE : energy a ε Ω u D < ⊤)
    {R : ℝ} (hR : Real.sqrt 2 * vacuumRadius a ≤ R)
    (hG : ∀ᵐ x ∂volume.restrict Ω, ∀ j, ‖G x j‖ ≤ ‖D x j‖) :
    energy a ε Ω (radialProjection R ∘ u) G ≤ energy a ε Ω u D ∧
      ((volume.restrict Ω) {x | R < ‖u x‖} ≠ 0 →
        energy a ε Ω (radialProjection R ∘ u) G < energy a ε Ω u D) := by
  let μ := volume.restrict Ω
  let f (x : Point) := ENNReal.ofReal (energyDensity a ε (radialProjection R (u x)) (G x))
  let g (x : Point) := ENNReal.ofReal (energyDensity a ε (u x) (D x))
  let q : ℝ := (ε : ℝ)⁻¹ ^ 2
  have hq : 0 < q := pow_pos (inv_pos.mpr ε.2.1) 2
  have hK : ∀ᵐ x ∂μ, (1 / 2 : ℝ) * gradientNormSq (G x) ≤ (1 / 2 : ℝ) * gradientNormSq (D x) := by
    refine hG.mono fun x hx => mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [gradientNormSq_eq_sum_norm_sq, gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hx j) 2
  have hfg : f ≤ᵐ[μ] g := hK.mono fun x hx => ENNReal.ofReal_le_ofReal
    (add_le_add hx (mul_le_mul_of_nonneg_left (bulkPotential_radialProjection_le a hR (u x)) hq.le))
  have hLE : (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ := lintegral_mono_ae hfg
  refine ⟨hLE, fun hBig => ?_⟩
  exact lintegral_strict_mono_of_ae_le_of_ae_lt_on (aemeasurable_ofReal_energyDensity a ε hu)
    (hLE.trans_lt hE).ne hfg hBig (hK.mono fun x hx hBigx => by
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (energyDensity_nonneg a ε _ _)).mpr
      exact add_lt_add_of_le_of_lt hx
        (mul_lt_mul_of_pos_left (bulkPotential_radialProjection_lt a hR hBigx) hq))

/-- The normalized surface measure for the Dirichlet trace on a three-dimensional
Lipschitz domain. -/
noncomputable abbrev frontierSurfaceMeasure (Ω : Set Point) : Measure (frontier Ω) :=
  Measure.euclideanHausdorffMeasure 2

/-- The Lipschitz Sobolev chain rule and the trace composition law on a fixed
domain, in the nonexpansive case. The projection comparison uses pointwise
control of each displayed weak-gradient column. -/
@[expose] def NonexpansiveSobolevTraceComposition (Ω : Set Point) : Prop :=
  ∀ (F : S0 → S0), LipschitzWith 1 F →
    ∀ (b : frontier Ω → S0) (u : Point → S0) (D : Point → Gradient),
      MemH1 Ω u D → HasSmoothTrace Ω u D b →
      (∀ᵐ x ∂frontierSurfaceMeasure Ω, F (b x) = b x) →
      ∃ G : Point → Gradient, MemH1 Ω (F ∘ u) G ∧ HasSmoothTrace Ω (F ∘ u) G b ∧
        ∀ᵐ x ∂volume.restrict Ω, ∀ j, ‖G x j‖ ≤ ‖D x j‖

theorem HasSmoothTrace.eLpNorm_boundary_lt_top {b : frontier Ω → S0} {u : Point → S0}
    {D : Point → Gradient} (h : HasSmoothTrace Ω u D b) (hBound : Bornology.IsBounded Ω) :
    eLpNorm b ⊤ (frontierSurfaceMeasure Ω) < ⊤ := by
  obtain ⟨B, hB, hb, _⟩ := h
  obtain ⟨M, hM⟩ := hBound.isCompact_closure.exists_bound_of_continuousOn hB.continuous.continuousOn
  rw [eLpNorm_exponent_top]
  have hBound' : ∀ᵐ x ∂frontierSurfaceMeasure Ω, ‖b x‖ ≤ M :=
    Eventually.of_forall fun x => (by rw [← hb x]; exact hM x (frontier_subset_closure x.2))
  exact (eLpNormEssSup_le_of_ae_bound hBound').trans_lt ENNReal.ofReal_lt_top

private theorem ae_norm_le_eLpNorm_top_toReal {α : Type*} [MeasurableSpace α]
    {b : α → S0} {μ : Measure α} (hB : eLpNorm b ⊤ μ < ⊤) :
    ∀ᵐ x ∂μ, ‖b x‖ ≤ (eLpNorm b ⊤ μ).toReal := by
  filter_upwards [enorm_ae_le_eLpNormEssSup b μ] with x hx
  rw [← eLpNorm_exponent_top] at hx
  calc
    ‖b x‖ = ‖b x‖ₑ.toReal := (toReal_enorm (b x)).symm
    _ ≤ _ := ENNReal.toReal_mono hB.ne hx

/-- Exact radial (L∞) bound for the global minimizer with its prescribed
frozen Dirichlet trace. -/
theorem IsGlobalEnergyMinimizer.eLpNorm_top_le_vacuumOrTrace
    {a : BulkCoefficients} {ε : ElasticScale} {b : frontier Ω → S0}
    {u : Point → S0} {D : Point → Gradient} (h : IsGlobalEnergyMinimizer a ε Ω b u D)
    (hΩ : IsOpen Ω) (hBound : Bornology.IsBounded Ω)
    (hComp : NonexpansiveSobolevTraceComposition Ω) :
    eLpNorm u ⊤ (volume.restrict Ω) ≤ ENNReal.ofReal
      (max (Real.sqrt 2 * vacuumRadius a) (eLpNorm b ⊤ (frontierSurfaceMeasure Ω)).toReal) := by
  let σ := frontierSurfaceMeasure Ω
  let R := max (Real.sqrt 2 * vacuumRadius a) (eLpNorm b ⊤ σ).toReal
  have hRL : Real.sqrt 2 * vacuumRadius a ≤ R := le_max_left _ _
  have hRR : (eLpNorm b ⊤ σ).toReal ≤ R := le_max_right _ _
  have hR : 0 ≤ R := (mul_nonneg (Real.sqrt_nonneg _) (vacuumRadius_pos a).le).trans hRL
  have hb : ∀ᵐ x ∂σ, radialProjection R (b x) = b x :=
    (ae_norm_le_eLpNorm_top_toReal (h.2.1.eLpNorm_boundary_lt_top hBound)).mono
      fun _ hx => radialProjection_eq_self (hx.trans hRR)
  obtain ⟨G, hG, hT, hCol⟩ := hComp (radialProjection R) (lipschitzWith_radialProjection hR)
    b u D h.1 h.2.1 hb
  have hMin := h.2.2 (radialProjection R ∘ u) G hG hT
  have hCmp := energy_radialProjection_comparison a ε h.1 (h.energy_lt_top hΩ hBound) hRL hCol
  have hAlmost : ∀ᵐ x ∂volume.restrict Ω, ‖u x‖ ≤ R := by
    rw [ae_iff]
    by_contra hNonzero
    have hBig : (volume.restrict Ω) {x | R < ‖u x‖} ≠ 0 := by
      simpa only [not_le] using hNonzero
    exact (not_lt_of_ge hMin) (hCmp.2 hBig)
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound hAlmost

end Thesis

end
