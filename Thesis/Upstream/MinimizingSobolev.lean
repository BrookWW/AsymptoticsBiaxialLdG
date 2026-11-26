module

public import Thesis.Foundation.Frobenius
public import Thesis.Foundation.WeakGradient
public import HarmonicMaps.Minimizer

/-! Sobolev maps and Dirichlet comparisons in the Frobenius coordinates. -/

@[expose] public section

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal ContDiff BigOperators Matrix.Norms.Frobenius

namespace Thesis

/-- The Euclidean coordinates of a tensor field. -/
abbrev frobeniusField (u : Point → S0) : HarmonicMaps.Domain 3 → HarmonicMaps.Ambient 5 :=
  fun x => frobeniusCoordinateEquiv (u x)

/-- The Euclidean coordinates of the columns of a weak tensor gradient. -/
abbrev frobeniusGradient (D : Point → Gradient) :
    HarmonicMaps.Domain 3 → HarmonicMaps.Gradient 3 5 :=
  fun x j => frobeniusCoordinateEquiv (D x j)

theorem HarmonicMaps.coordinateDerivative_eq_coordDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (u : Point → E) (hu : ContDiff ℝ ∞ u) (j : Fin 3) (x : Point) :
    HarmonicMaps.coordinateDerivative u hu j x = coordDeriv j u x := rfl

private theorem locallyIntegrableOn_of_memLp_two {f : Point → HarmonicMaps.Ambient 5}
    {U : Set Point} (h : MemLp f 2 (volume.restrict U)) : LocallyIntegrableOn f U volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (h.locallyIntegrable (by norm_num))

private theorem locallyIntegrableOn_of_locallyMemL2 {Ω : HarmonicMaps.OpenDomain 3}
    {f : Point → HarmonicMaps.Ambient 5} (h : HarmonicMaps.LocallyMemL2 Ω f) :
    LocallyIntegrableOn f Ω.val volume := by
  rw [locallyIntegrableOn_iff Ω.property.isLocallyClosed]
  intro K hKΩ hK
  letI : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  exact (h K hK hKΩ).integrable (by norm_num)

/-- The displayed tensor gradient is exactly the upstream distributional gradient
when the coordinates are locally integrable. -/
theorem upstreamHasWeakGradient_iff (Ω : HarmonicMaps.OpenDomain 3) (u : Point → S0)
    (D : Point → Gradient) :
    HarmonicMaps.HasWeakGradient Ω (frobeniusField u) (frobeniusGradient D) ↔
      LocallyIntegrableOn (frobeniusField u) Ω.val volume ∧
      (∀ j : Fin 3, LocallyIntegrableOn (fun x => frobeniusGradient D x j) Ω.val volume) ∧
      IsWeakGradient Ω.val u D := by
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  rw [isWeakGradient_iff_frobeniusCoordinates]
  constructor
  · intro h j φ hφ
    exact h j φ hφ.1 hφ.2.1 hφ.2.2
  · intro h j φ hφ hcomp hsub
    exact h j φ ⟨hφ, hcomp, hsub⟩

theorem memH1_iff_memW12 (Ω : HarmonicMaps.OpenDomain 3) (u : Point → S0)
    (D : Point → Gradient) :
    MemH1 Ω.val u D ↔ HarmonicMaps.MemW12 Ω (frobeniusField u) (frobeniusGradient D) := by
  constructor
  · rintro ⟨hu, hD, hweak⟩
    have hu' := (frobeniusCoordinateEquiv_memLp_iff (volume.restrict Ω.val) 2 u).2 hu
    have hD' : ∀ j : Fin 3, MemLp (fun x => frobeniusGradient D x j) 2
        (volume.restrict Ω.val) :=
      fun j => (frobeniusCoordinateEquiv_memLp_iff (volume.restrict Ω.val) 2
        (fun x => D x j)).2 (hD j)
    refine ⟨(upstreamHasWeakGradient_iff Ω u D).2 ?_, hu', hD'⟩
    exact ⟨locallyIntegrableOn_of_memLp_two hu',
      fun j => locallyIntegrableOn_of_memLp_two (hD' j), hweak⟩
  · rintro ⟨hweak, hu, hD⟩
    exact ⟨(frobeniusCoordinateEquiv_memLp_iff (volume.restrict Ω.val) 2 u).1 hu,
      fun j => (frobeniusCoordinateEquiv_memLp_iff (volume.restrict Ω.val) 2
        (fun x => D x j)).1 (hD j), ((upstreamHasWeakGradient_iff Ω u D).1 hweak).2.2⟩

theorem memH1Loc_iff_memW12Loc (Ω : HarmonicMaps.OpenDomain 3) (u : Point → S0)
    (D : Point → Gradient) :
    MemH1Loc Ω.val u D ↔ HarmonicMaps.MemW12Loc Ω (frobeniusField u) (frobeniusGradient D) := by
  constructor
  · intro h
    have hcompact (K : Set Point) (hK : IsCompact K) (hKΩ : K ⊆ Ω.val) :
        MemH1 K u D := by
      obtain ⟨W, hW, hKW, hWΩ, hWcomp⟩ :=
        exists_open_between_and_isCompact_closure hK Ω.property hKΩ
      exact (h W hW ⟨hWcomp, hWΩ⟩).mono hKW
    have hu' : HarmonicMaps.LocallyMemL2 Ω (frobeniusField u) :=
      fun K hK hKΩ =>
        (frobeniusCoordinateEquiv_memLp_iff (volume.restrict K) 2 u).2 (hcompact K hK hKΩ).1
    have hD' (j : Fin 3) : HarmonicMaps.LocallyMemL2 Ω (fun x => frobeniusGradient D x j) :=
      fun K hK hKΩ =>
        (frobeniusCoordinateEquiv_memLp_iff (volume.restrict K) 2 (fun x => D x j)).2
          ((hcompact K hK hKΩ).2.1 j)
    refine ⟨(upstreamHasWeakGradient_iff Ω u D).2 ?_, hu', hD'⟩
    exact ⟨locallyIntegrableOn_of_locallyMemL2 hu',
      fun j => locallyIntegrableOn_of_locallyMemL2 (hD' j), h.isWeakGradient Ω.property⟩
  · rintro ⟨hweak, hu, hD⟩ W _ ⟨hWcomp, hWΩ⟩
    have hmono := Measure.restrict_mono_set (volume : Measure Point)
      (subset_closure : W ⊆ closure W)
    refine ⟨?_, ?_, (((upstreamHasWeakGradient_iff Ω u D).1 hweak).2.2).mono
      (subset_closure.trans hWΩ)⟩
    · exact (frobeniusCoordinateEquiv_memLp_iff (volume.restrict W) 2 u).1
        ((hu (closure W) hWcomp hWΩ).mono_measure hmono)
    · intro j
      exact (frobeniusCoordinateEquiv_memLp_iff (volume.restrict W) 2 (fun x => D x j)).1
        ((hD j (closure W) hWcomp hWΩ).mono_measure hmono)

private theorem eLpNorm_two_sq_eq_lintegral {E : Type*} [NormedAddCommGroup E]
    (μ : Measure Point) (f : Point → E) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
  simpa [ENNReal.rpow_two, ENNReal.ofReal_pow, ofReal_norm] using
    (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := (2 : ℝ≥0)) (by norm_num))

theorem h1Deviation_eq_sq_eLpNorm (U : Set Point) (u v : Point → S0)
    (D G : Point → Gradient)
    (hmap : AEStronglyMeasurable (frobeniusField v - frobeniusField u) (volume.restrict U))
    (hgradient : ∀ j : Fin 3, AEStronglyMeasurable
      (fun x => frobeniusGradient G x j - frobeniusGradient D x j) (volume.restrict U)) :
    h1Deviation U u v D G =
      eLpNorm (frobeniusField v - frobeniusField u) 2 (volume.restrict U) ^ 2 +
      ∑ j : Fin 3,
        eLpNorm (fun x => frobeniusGradient G x j - frobeniusGradient D x j)
          2 (volume.restrict U) ^ 2 := by
  rw [h1Deviation_frobeniusCoordinates]
  let F := frobeniusField v - frobeniusField u
  let J (j : Fin 3) (x : Point) := frobeniusGradient G x j - frobeniusGradient D x j
  calc
    _ = ∫⁻ x in U, ENNReal.ofReal (‖F x‖ ^ 2) +
        ∑ j : Fin 3, ENNReal.ofReal (‖J j x‖ ^ 2) := by
      apply lintegral_congr
      intro x
      have hF : ‖frobeniusCoordinateEquiv (u x) - frobeniusCoordinateEquiv (v x)‖ = ‖F x‖ :=
        norm_sub_rev _ _
      have hJ (j : Fin 3) : ‖frobeniusCoordinateEquiv (D x j) -
          frobeniusCoordinateEquiv (G x j)‖ = ‖J j x‖ := norm_sub_rev _ _
      simp only [hF, hJ]
      rw [ENNReal.ofReal_add (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _),
        ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
    _ = _ := by
      have hF : AEMeasurable (fun x => ENNReal.ofReal (‖F x‖ ^ 2)) (volume.restrict U) :=
        (hmap.norm.aemeasurable.pow_const _).ennreal_ofReal
      have hJ (j : Fin 3) : AEMeasurable (fun x => ENNReal.ofReal (‖J j x‖ ^ 2))
          (volume.restrict U) :=
        ((hgradient j).norm.aemeasurable.pow_const _).ennreal_ofReal
      rw [lintegral_add_left' hF, lintegral_finsetSum' _ (fun j _ => hJ j)]
      simp only [eLpNorm_two_sq_eq_lintegral, F, J]

private theorem coordDeriv_comp_clm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {u : Point → E} (hu : ContDiff ℝ ∞ u) (j : Fin 3) (x : Point) :
    coordDeriv j (L ∘ u) x = L (coordDeriv j u x) := by
  unfold coordDeriv
  rw [fderiv_comp x L.differentiableAt (hu.differentiable (by simp) x),
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]

private theorem contDiff_frobeniusField {φ : Point → S0} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (frobeniusField φ) :=
  frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hφ

private theorem h1Deviation_eq_smooth_approximation (U : Set Point) (u : Point → S0)
    (D : Point → Gradient) (hu : MemH1 U u D) (φ : Point → S0) (hφ : ContDiff ℝ ∞ φ) :
    h1Deviation U u φ D (ClassicalGradient φ) =
      eLpNorm (frobeniusField φ - frobeniusField u) 2 (volume.restrict U) ^ 2 +
      ∑ j : Fin 3, eLpNorm (fun x => coordDeriv j (frobeniusField φ) x - frobeniusGradient D x j)
        2 (volume.restrict U) ^ 2 := by
  have hF := contDiff_frobeniusField hφ
  have hderiv (j : Fin 3) (x : Point) : frobeniusGradient (ClassicalGradient φ) x j =
      coordDeriv j (frobeniusField φ) x :=
    (coordDeriv_comp_clm frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
      hφ j x).symm
  have hmap := ((frobeniusCoordinateEquiv_memLp_iff (volume.restrict U) 2 u).2 hu.1).1
  have hgradient (j : Fin 3) : AEStronglyMeasurable
      (fun x => frobeniusGradient (ClassicalGradient φ) x j - frobeniusGradient D x j)
        (volume.restrict U) := by
    have hcont : Continuous (coordDeriv j (frobeniusField φ)) := continuousOn_univ.mp
      (continuousOn_coordDeriv isOpen_univ (hF.of_le (by simp)).contDiffOn j)
    have hj := ((frobeniusCoordinateEquiv_memLp_iff (volume.restrict U) 2
      (fun x => D x j)).2 (hu.2.1 j)).1
    simp only [hderiv]
    exact hcont.aestronglyMeasurable.sub hj
  simpa only [hderiv] using h1Deviation_eq_sq_eLpNorm U u φ D (ClassicalGradient φ)
    (hF.continuous.aestronglyMeasurable.sub hmap) hgradient

private theorem tendsto_zero_of_sq_le {s a : ℕ → ENNReal}
    (hle : ∀ k, s k ^ 2 ≤ a k ^ 2) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto s atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ha
    (fun _ => zero_le) (fun k => (ENNReal.pow_le_pow_left_iff two_ne_zero).mp (hle k))

private theorem tendsto_sq_zero {s : ℕ → ENNReal} (h : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun k => s k ^ 2) atTop (𝓝 0) := by
  have hc : Continuous (fun x : ENNReal => x ^ (2 : ℝ)) := ENNReal.continuous_rpow_const
  have h' : Tendsto (fun k => s k ^ (2 : ℝ)) atTop (𝓝 ((0 : ENNReal) ^ (2 : ℝ))) :=
    (hc.tendsto 0).comp h
  simpa only [ENNReal.rpow_two, zero_pow (by decide : 2 ≠ 0)] using h'

/-- The intrinsic trace closure and the upstream sequential closure use the same Sobolev norm. -/
theorem hasZeroTrace_iff_hasZeroBoundaryValues (Ω : HarmonicMaps.OpenDomain 3)
    (u : Point → S0) (D : Point → Gradient) :
    HasZeroTrace Ω.val u D ↔
      HarmonicMaps.HasZeroBoundaryValues Ω (frobeniusField u) (frobeniusGradient D) := by
  classical
  constructor
  · rintro ⟨hu, happ⟩
    let a (k : ℕ) := ENNReal.ofReal (1 / ((k : ℝ) + 1))
    have ha (k : ℕ) : 0 < a k := ENNReal.ofReal_pos.mpr (by positivity)
    have haLim : Tendsto a atTop (𝓝 0) := by
      have h : Tendsto a atTop (𝓝 (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal.tendsto 0).comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa only [ENNReal.ofReal_zero] using h
    choose φ hSmooth hCompact hSupport herr using fun k : ℕ =>
      happ (a k ^ 2) (ENNReal.pow_pos (ha k) _)
    refine ⟨(memH1_iff_memW12 Ω u D).1 hu, fun k => frobeniusField (φ k),
      fun k => contDiff_frobeniusField (hSmooth k), ?_, ?_, ?_⟩
    · intro k
      have h0 : frobeniusCoordinateEquiv (0 : S0) = 0 := map_zero _
      exact ⟨(hCompact k).comp_left h0,
        (tsupport_comp_subset h0 (φ k)).trans (hSupport k)⟩
    · apply tendsto_zero_of_sq_le _ haLim
      intro k
      have h : h1Deviation Ω.val u (φ k) D (ClassicalGradient (φ k)) ≤ a k ^ 2 :=
        (herr k).le
      rw [h1Deviation_eq_smooth_approximation _ u D hu (φ k) (hSmooth k)] at h
      exact (le_self_add).trans h
    · intro j
      apply tendsto_zero_of_sq_le _ haLim
      intro k
      have h : h1Deviation Ω.val u (φ k) D (ClassicalGradient (φ k)) ≤ a k ^ 2 :=
        (herr k).le
      rw [h1Deviation_eq_smooth_approximation _ u D hu (φ k) (hSmooth k)] at h
      exact (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)).trans
        (le_add_self.trans h)
  · rintro ⟨hu, f, hfSmooth, hfSupport, hfMap, hfGradient⟩
    have hu' := (memH1_iff_memW12 Ω u D).2 hu
    refine ⟨hu', ?_⟩
    let φ (k : ℕ) (x : Point) : S0 := frobeniusCoordinateEquiv.symm (f k x)
    have hφ (k : ℕ) : ContDiff ℝ ∞ (φ k) :=
      frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
        (hfSmooth k)
    have hF (k : ℕ) : frobeniusField (φ k) = f k :=
      funext fun x => frobeniusCoordinateEquiv.apply_symm_apply (f k x)
    have hFgrad (j : Fin 3) : Tendsto (fun k => eLpNorm
        (fun x => coordDeriv j (f k) x - frobeniusGradient D x j) 2 (volume.restrict Ω.val))
        atTop (𝓝 0) := hfGradient j
    have htotal : Tendsto (fun k => h1Deviation Ω.val u (φ k) D (ClassicalGradient (φ k))) atTop
        (𝓝 0) := by
      simp_rw [h1Deviation_eq_smooth_approximation _ u D hu' _ (hφ _), hF]
      have hSum := tendsto_finsetSum (s := Finset.univ) fun j _ => tendsto_sq_zero (hFgrad j)
      simpa using (tendsto_sq_zero hfMap).add hSum
    intro δ hδ
    obtain ⟨k, hk⟩ := (htotal.eventually (gt_mem_nhds hδ)).exists
    have h0 : frobeniusCoordinateEquiv.symm (0 : HarmonicMaps.Ambient 5) = 0 := map_zero _
    exact ⟨φ k, hφ k, (hfSupport k).1.comp_left h0,
      (tsupport_comp_subset h0 (f k)).trans (hfSupport k).2, hk⟩

theorem sameTrace_iff_hasZeroBoundaryDifference (Ω : HarmonicMaps.OpenDomain 3)
    (v u : Point → S0) (G D : Point → Gradient) :
    SameTrace Ω.val v u G D ↔
      HarmonicMaps.HasZeroBoundaryDifference Ω (frobeniusField u) (frobeniusGradient D)
        (frobeniusField v) (frobeniusGradient G) := by
  rw [SameTrace, hasZeroTrace_iff_hasZeroBoundaryValues, HarmonicMaps.HasZeroBoundaryDifference]
  have hmap : frobeniusField (v - u) = frobeniusField v - frobeniusField u :=
    funext fun x => map_sub frobeniusCoordinateEquiv (v x) (u x)
  have hgrad : frobeniusGradient (G - D) = fun x i =>
      frobeniusGradient G x i - frobeniusGradient D x i :=
    funext fun x => funext fun i => map_sub frobeniusCoordinateEquiv (G x i) (D x i)
  rw [hmap, hgrad]

/-- The paper's Dirichlet energy includes a factor of one half. -/
theorem dirichletEnergy_eq_half_upstream (U : Set Point) (D : Point → Gradient) :
    dirichletEnergy U D = ENNReal.ofReal (1 / 2 : ℝ) *
      HarmonicMaps.dirichletEnergy (frobeniusGradient D) U := by
  simp_rw [dirichletEnergy, HarmonicMaps.dirichletEnergy, HarmonicMaps.hsNormSq,
    gradientNormSq_eq_sum_norm_sq, frobeniusGradient, LinearIsometryEquiv.norm_map,
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem dirichletEnergy_le_iff_upstream (U : Set Point) (D G : Point → Gradient) :
    dirichletEnergy U D ≤ dirichletEnergy U G ↔
      HarmonicMaps.dirichletEnergy (frobeniusGradient D) U ≤
        HarmonicMaps.dirichletEnergy (frobeniusGradient G) U := by
  rw [dirichletEnergy_eq_half_upstream U D, dirichletEnergy_eq_half_upstream U G]
  exact ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr (by norm_num)).ne' ENNReal.ofReal_ne_top

theorem takesVacuumValues_iff_upstream (a : BulkCoefficients) (Ω : HarmonicMaps.OpenDomain 3)
    (N : HarmonicMaps.CompactSmoothEmbeddedTarget 5)
    (hN : N.carrierSet = (frobeniusCoordinateEquiv : S0 → HarmonicMaps.Ambient 5) '' vacuum a)
    (u : Point → S0) :
    TakesVacuumValues a Ω.val u ↔ HarmonicMaps.TakesValuesIn N Ω (frobeniusField u) := by
  rw [TakesVacuumValues, HarmonicMaps.TakesValuesIn, hN]
  constructor
  · intro h
    exact h.mono fun x hx => ⟨u x, hx, rfl⟩
  · intro h
    apply h.mono
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact (frobeniusCoordinateEquiv.injective hxy) ▸ hy

/-- Local Dirichlet comparisons transfer to the native Euclidean minimizer interface.
The target carrier is matched by the tensor isometry. -/
theorem isLocalDirichletMinimizer_iff_upstream (a : BulkCoefficients)
    (Ω : HarmonicMaps.OpenDomain 3) (N : HarmonicMaps.CompactSmoothEmbeddedTarget 5)
    (hN : N.carrierSet = (frobeniusCoordinateEquiv : S0 → HarmonicMaps.Ambient 5) '' vacuum a)
    (u : Point → S0) (D : Point → Gradient) :
    IsLocalDirichletMinimizer a Ω.val u D ↔
      HarmonicMaps.MemW12Loc Ω (frobeniusField u) (frobeniusGradient D) ∧
      HarmonicMaps.TakesValuesIn N Ω (frobeniusField u) ∧
      HarmonicMaps.IsLocallyEnergyMinimizing N Ω (frobeniusField u) (frobeniusGradient D) := by
  unfold IsLocalDirichletMinimizer
  rw [memH1Loc_iff_memW12Loc Ω, takesVacuumValues_iff_upstream a Ω N hN]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h x r hr hsub v Dv hv hvN hdiff
    let w (y : Point) := frobeniusCoordinateEquiv.symm (v y)
    let G (y : Point) (j : Fin 3) := frobeniusCoordinateEquiv.symm (Dv y j)
    have hw : frobeniusField w = v := funext fun y =>
      frobeniusCoordinateEquiv.apply_symm_apply (v y)
    have hG : frobeniusGradient G = Dv := funext fun y => funext fun j =>
      frobeniusCoordinateEquiv.apply_symm_apply (Dv y j)
    let B := HarmonicMaps.ballDomain x r
    have hwSob : MemH1 B.val w G := (memH1_iff_memW12 B w G).2 (by simpa only [hw, hG] using hv)
    have hwN : TakesVacuumValues a B.val w :=
      (takesVacuumValues_iff_upstream a B N hN w).2 (by simpa only [hw] using hvN)
    have hwTrace : SameTrace B.val w u G D :=
      (sameTrace_iff_hasZeroBoundaryDifference B w u G D).2 (by simpa only [hw, hG] using hdiff)
    have hle := (dirichletEnergy_le_iff_upstream (Metric.ball x r) D G).1
      (h x r hr hsub w G hwSob hwN hwTrace)
    simpa only [hG] using hle
  · intro h x r hr hsub v G hv hvN htrace
    let B := HarmonicMaps.ballDomain x r
    apply (dirichletEnergy_le_iff_upstream (Metric.ball x r) D G).2
    exact h x r hr hsub (frobeniusField v) (frobeniusGradient G)
      ((memH1_iff_memW12 B v G).1 hv) ((takesVacuumValues_iff_upstream a B N hN v).1 hvN)
      ((sameTrace_iff_hasZeroBoundaryDifference B v u G D).1 htrace)

end Thesis
end
end
