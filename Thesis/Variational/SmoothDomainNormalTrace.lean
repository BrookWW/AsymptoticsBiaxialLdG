module

public import Thesis.Variational.SmoothDomainTraceChart
import Thesis.Interpolation.FiniteL2TraceEstimate
import StratificationTheory.Foundation.CylinderRawTime
import StratificationTheory.Foundation.BoundedFiberL2Trace
import HarmonicMaps.Analysis.RadialIntegrability
import HarmonicMaps.Analysis.VariableMollificationL2

/-! The original normal Sobolev trace and its bounded endpoint on a smooth wall. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace Thesis.SmoothDomainEpigraphBox

variable {Ω : Set Point} (B : SmoothDomainEpigraphBox Ω)

abbrev NormalTraceL2 (q : ℕ) := Lp (Ambient q) 2 (volume.restrict B.planeDomain.val)

abbrev NormalTrace (q : ℕ) (t : ℝ) := C(Icc (0 : ℝ) t, B.NormalTraceL2 q)

@[expose] def RepresentsNormalTrace {q : ℕ} {t : ℝ} (u : Point → Ambient q) (H : B.NormalTrace q t) : Prop :=
  ∀ᵐ s : ℝ ∂volume, ∀ hs : s ∈ Ioo (0 : ℝ) t,
    ∃ hslice : MemLp (fun y => u (B.normalParameter (y,s))) 2 (volume.restrict B.planeDomain.val),
      H ⟨s,hs.1.le,hs.2.le⟩ = hslice.toLp _

private theorem normalProduct_measurePreserving (t : ℝ) :
    MeasurePreserving B.normalParameter
      ((volume.restrict B.planeDomain.val).prod (volume.restrict (Ioo 0 t)))
      (volume.restrict (B.physicalRectangle 0 t).val) := by
  let Y (p : Plane × ℝ) := normalCoordinateEquiv.symm (p.1, EuclideanSpace.single 0 p.2)
  have hRaw : MeasurePreserving Y ((volume : Measure Plane).prod (volume : Measure ℝ)) volume :=
    measurePreserving_cylinder_coordinates_inverse 2
  have hRestricted := hRaw.restrict_preimage (B.flatSlab t).property.measurableSet
  have hPre : Y ⁻¹' (B.flatSlab t).val = B.planeDomain.val ×ˢ Ioo 0 t := by
    ext p
    simp only [Y, flatSlab, flatRectangle, mem_preimage, mem_setOf_eq, ContinuousLinearEquiv.apply_symm_apply,
      PiLp.single_apply, if_true, mem_prod]
  rw [hPre, ← Measure.prod_restrict] at hRestricted
  have h := (B.flatSlab_measurePreserving t).comp hRestricted
  have hE : B.normalEuclideanChart ∘ Y = B.normalParameter := funext B.normalEuclideanChart_apply
  change MeasurePreserving (B.normalEuclideanChart ∘ Y) _ (volume.restrict (B.physicalRectangle 0 t).val) at h
  rwa [hE] at h

/-- The normal trace of a finite weak graph is bounded by its full weak graph
norm, using the original plane measure and only the geometry of this chart. -/
theorem exists_normalTrace_bound {q : ℕ} (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t) (htR : t ≤ B.radius) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q},
      MemW12 ⟨Ω,hΩ⟩ u D →
      ∃ H : B.NormalTrace q t, B.RepresentsNormalTrace u H ∧
        ∀ s : Icc (0 : ℝ) t, ‖H s‖ ^ 2 ≤
          C * ((∫ x in Ω, ‖u x‖ ^ 2) + (∫ x in Ω, hsNormSq (D x))) := by
  let V := B.flatSlab t
  let P := B.physicalRectangle 0 t
  let E := B.normalEuclideanChart
  let σ := (volume : Measure Plane).restrict B.planeDomain.val
  let ν := (volume : Measure ℝ).restrict (Ioo 0 t)
  let νC := (volume : Measure ℝ).restrict (Icc 0 t)
  letI : IsFiniteMeasure σ := B.isFiniteMeasure_planeDomain
  have hν : νC = ν := Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  have hPΩ : P.val ⊆ Ω := by
    rintro _ ⟨x,hx,rfl⟩
    exact B.flatSlab_mapsTo_domain htR hx
  have hMap := B.normalProduct_measurePreserving t
  obtain ⟨L,hL⟩ := (B.isBounded_flatSlab htR).isCompact_closure.exists_bound_of_continuousOn
    (B.normalEuclideanChart_smooth.continuous_fderiv (by simp)).continuousOn
  let L₀ := max L 0
  have hL₀ : 0 ≤ L₀ := le_max_right _ _
  let C := max (2/t) (2*t*L₀^2)
  have hC : 0 ≤ C := (by positivity : 0 ≤ 2/t).trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro u D hu
  let J (x : Point) (i : Fin 3) := ∑ j : Fin 3, (fderiv ℝ E x (EuclideanSpace.single i 1)) j • D (E x) j
  have hChart := B.memW12_normalChart hΩ htR hu
  let Y (p : Plane × ℝ) := normalCoordinateEquiv.symm (p.1, EuclideanSpace.single 0 p.2)
  let F (p : Plane × ℝ) := u (B.normalParameter p)
  let k := Fin.natAdd 2 (0 : Fin 1)
  let G (p : Plane × ℝ) := J (Y p) k
  have hEY (p : Plane × ℝ) : E (Y p) = B.normalParameter p := B.normalEuclideanChart_apply p
  have hY : MeasurePreserving Y (σ.prod ν) (volume.restrict V.val) := by
    have h := (measurePreserving_cylinder_coordinates_inverse 2).restrict_preimage V.property.measurableSet
    have hp : Y ⁻¹' V.val = B.planeDomain.val ×ˢ Ioo 0 t := by
      ext p
      simp only [Y, V, flatRectangle, mem_preimage, mem_setOf_eq,
        ContinuousLinearEquiv.apply_symm_apply, PiLp.single_apply, if_true, mem_prod]
    rw [hp, ← Measure.prod_restrict] at h
    exact h
  have hSub := Measure.restrict_mono_set volume hPΩ
  have hF : MemLp F 2 (σ.prod νC) := by
    rw [hν]
    exact (hu.2.1.mono_measure hSub).comp_measurePreserving hMap
  have hG : MemLp G 2 (σ.prod νC) := by
    rw [hν]
    exact (hChart.2.2 k).comp_measurePreserving hY
  have hWeak (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioo 0 t) :
      ∀ᵐ y ∂σ, (∫ r in Icc 0 t, deriv φ r • F (y,r)) = -(∫ r in Icc 0 t, φ r • G (y,r)) := by
    have h := MemW12.cylinder_time_test_ae B.planeDomain (isFiniteMeasure_restrict.mp (B.isFiniteMeasure_planeDomain))
      hChart hφ hc hs
    have hφL : MemLp φ ⊤ ν := hφ.continuous.memLp_top_of_hasCompactSupport hc _
    have hDer : MemLp (deriv φ) ⊤ ν := (hφ.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport hc.deriv _
    filter_upwards [h] with y hy
    have hFI : Integrable (fun r => deriv φ r • F (y,r)) ν := by
      have h := hy.1.smul_of_top_right hDer
      change Integrable (fun r => deriv φ r • u (E (Y (y,r)))) ν at h
      simpa only [hEY] using h
    have hGI : Integrable (fun r => φ r • G (y,r)) ν := hy.2.1.smul_of_top_right hφL
    have hEq := hy.2.2.2
    change (∫ r, deriv φ r • (u ∘ E) (Y (y,r)) + φ r • G (y,r) ∂ν) = 0 at hEq
    simp_rw [Function.comp_apply, hEY] at hEq
    change (∫ r, deriv φ r • F (y,r) + φ r • G (y,r) ∂ν) = 0 at hEq
    rw [integral_add hFI hGI] at hEq
    change (∫ r, deriv φ r • F (y,r) ∂νC) = -(∫ r, φ r • G (y,r) ∂νC)
    rw [hν]
    exact eq_neg_of_add_eq_zero_left hEq
  obtain ⟨H,hH,hNorm⟩ := exists_finite_L2_trace_with_endpoint_estimate σ ht hF hG hWeak
  refine ⟨H,hH,?_⟩
  intro s
  have hU2 := memLp_two_iff_integrable_sq_norm hu.2.1.aestronglyMeasurable |>.mp hu.2.1
  have hD2 := integrable_hsNormSq_of_memLp_columns hu.2.2
  have hMapEnergy : (∫ p, ‖F p‖ ^ 2 ∂σ.prod νC) ≤ ∫ x in Ω, ‖u x‖ ^ 2 := by
    rw [hν]
    calc
      _ = ∫ x in P.val, ‖u x‖ ^ 2 := by
        rw [← hMap.map_eq]
        exact (integral_map hMap.aemeasurable
          (hMap.map_eq.symm ▸ (hU2.mono_measure hSub).aestronglyMeasurable)).symm
      _ ≤ _ := integral_mono_measure hSub (Eventually.of_forall fun _ => sq_nonneg _) hU2
  have hColumnEnergy : (∫ p, ‖G p‖ ^ 2 ∂σ.prod νC) ≤ L₀^2 * ∫ x in Ω, hsNormSq (D x) := by
    have hT : Integrable (fun p => hsNormSq (D (B.normalParameter p))) (σ.prod ν) :=
      hMap.integrable_comp_of_integrable (hD2.mono_measure hSub)
    have hNormJ : ∀ᵐ p ∂σ.prod ν, ‖G p‖ ^ 2 ≤ L₀^2 * hsNormSq (D (B.normalParameter p)) := by
      have hIn : ∀ᵐ p ∂σ.prod ν, Y p ∈ V.val :=
        hY.quasiMeasurePreserving.ae (ae_restrict_mem V.property.measurableSet)
      filter_upwards [hIn] with p hp
      let v := fderiv ℝ E (Y p) (EuclideanSpace.single k 1)
      have hN : ‖v‖ ≤ L₀ := by
        apply (ContinuousLinearMap.le_opNorm _ _).trans
        rw [show ‖EuclideanSpace.single k (1 : ℝ)‖ = 1 by simp, mul_one]
        exact (hL _ (subset_closure hp)).trans (le_max_left _ _)
      rw [show G p = ∑ j : Fin 3, v j • D (B.normalParameter p) j by simp only [G,J,v,hEY]]
      exact (norm_sq_sum_gradient_le _ _).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hN 2) (hsNormSq_nonneg _))
    rw [hν]
    have hGi : Integrable (fun p => ‖G p‖ ^ 2) (σ.prod ν) :=
      memLp_two_iff_integrable_sq_norm (hν ▸ hG.aestronglyMeasurable) |>.mp (hν ▸ hG)
    calc
      _ ≤ ∫ p, L₀ ^ 2 * hsNormSq (D (B.normalParameter p)) ∂σ.prod ν :=
        integral_mono_ae hGi (hT.const_mul _) hNormJ
      _ = L₀ ^ 2 * (∫ x in P.val, hsNormSq (D x)) := by
        rw [integral_const_mul]
        congr 1
        rw [← hMap.map_eq]
        exact (integral_map hMap.aemeasurable (hMap.map_eq.symm ▸ (hD2.mono_measure hSub).aestronglyMeasurable)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (integral_mono_measure hSub (Eventually.of_forall fun _ => hsNormSq_nonneg _) hD2) (sq_nonneg _)
  have hA : 0 ≤ ∫ x in Ω, ‖u x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ ∫ x in Ω, hsNormSq (D x) := integral_nonneg fun _ => hsNormSq_nonneg _
  refine (hNorm s).trans ?_
  rw [sub_zero]
  calc
    _ ≤ (2/t) * (∫ x in Ω, ‖u x‖ ^ 2) +
        (2*t) * (L₀^2 * ∫ x in Ω, hsNormSq (D x)) :=
      add_le_add (mul_le_mul_of_nonneg_left hMapEnergy (by positivity))
        (mul_le_mul_of_nonneg_left hColumnEnergy (by positivity))
    _ = (2/t) * (∫ x in Ω, ‖u x‖ ^ 2) +
        (2*t*L₀^2) * ∫ x in Ω, hsNormSq (D x) := by ring
    _ ≤ C * ((∫ x in Ω, ‖u x‖ ^ 2) + ∫ x in Ω, hsNormSq (D x)) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hA)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hB)

theorem normalParameter_continuous : Continuous B.normalParameter := by
  have h (j : Fin 2) : Continuous fun p : Plane × ℝ => p.1 j :=
    (PiLp.continuous_apply 2 _ j).comp continuous_fst
  exact B.chart.continuous.comp (((h 0).prodMk (h 1)).prodMk continuous_snd)

private theorem normalParameter_mem_closure {t : ℝ} (htR : t ≤ B.radius)
    {y : Plane} (hy : y ∈ B.planeDomain.val) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) t) :
    B.normalParameter (y,r) ∈ closure Ω := by
  have hBox : (((y 0,y 1),r) : EpigraphCoordinates) ∈ closedBall 0 B.radius :=
    epigraphCoordinates_mem_closedBall_iff.2
      ⟨⟨⟨hy.1.1.le,hy.1.2.le⟩,⟨hy.2.1.le,hy.2.2.le⟩⟩,
        ⟨(neg_nonpos.mpr B.radius_pos.le).trans hr.1, hr.2.trans htR⟩⟩
  rcases hr.1.eq_or_lt with h | h
  · exact frontier_subset_closure ((B.frontier_iff _ hBox).2 h.symm)
  · exact subset_closure ((B.mem_domain _ hBox).2 h)

/-- A field continuous on the original closed domain has its actual
closed normal-rectangle endpoint values in each continuous L² trace. -/
theorem RepresentsNormalTrace.eq_raw_of_continuousOn_closure {q : ℕ} {t : ℝ}
    (ht : 0 < t) (htR : t ≤ B.radius)
    {u : Point → Ambient q} (hu : ContinuousOn u (closure Ω)) {H : B.NormalTrace q t}
    (hH : B.RepresentsNormalTrace u H) (s : Icc (0 : ℝ) t) :
    ∃ hs : MemLp (fun y => u (B.normalParameter (y,s.val))) 2 (volume.restrict B.planeDomain.val),
      H s = hs.toLp _ := by
  let σ := (volume : Measure Plane).restrict B.planeDomain.val
  letI : IsFiniteMeasure σ := B.isFiniteMeasure_planeDomain
  let F (p : Plane × ℝ) := u (B.normalParameter p)
  let K := (B.chart '' closedBall (0 : EpigraphCoordinates) B.radius) ∩ closure Ω
  have hK : IsCompact K := ((isCompact_closedBall _ _).image B.chart.continuous).inter_right isClosed_closure
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn (hu.mono inter_subset_right)
  have hB : ∀ᵐ y ∂σ, ∀ r ∈ Icc (0 : ℝ) t, ‖F (y,r)‖ ≤ M := by
    filter_upwards [ae_restrict_mem B.planeDomain.property.measurableSet] with y hy r hr
    apply hM
    refine ⟨⟨((y 0,y 1),r), epigraphCoordinates_mem_closedBall_iff.2 ?_, rfl⟩,
      B.normalParameter_mem_closure htR hy hr⟩
    exact ⟨⟨⟨hy.1.1.le,hy.1.2.le⟩,⟨hy.2.1.le,hy.2.2.le⟩⟩,
      ⟨(neg_nonpos.mpr B.radius_pos.le).trans hr.1, hr.2.trans htR⟩⟩
  have hFmeas : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (0 : ℝ) t,
      AEStronglyMeasurable (fun y => F (y,r)) σ := by
    apply Eventually.of_forall
    intro r hr
    have hC : ContinuousOn (fun y : Plane => F (y,r)) B.planeDomain.val :=
      hu.comp (B.normalParameter_continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
        (fun _ hy => B.normalParameter_mem_closure htR hy ⟨hr.1.le,hr.2.le⟩)
    exact hC.aestronglyMeasurable B.planeDomain.property.measurableSet
  have hc : ∀ᵐ y ∂σ, ContinuousOn (fun r => F (y,r)) (Icc (0 : ℝ) t) := by
    filter_upwards [ae_restrict_mem B.planeDomain.property.measurableSet] with y hy
    exact hu.comp (B.normalParameter_continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
      (fun _ hr => B.normalParameter_mem_closure htR hy hr)
  obtain ⟨H₀,hRaw,hUniq⟩ :=
    exists_continuous_L2_trace_of_bounded_fiber_continuity σ ht hFmeas hc hB
  rw [hUniq H hH]
  exact hRaw s

theorem RepresentsNormalTrace.eq_raw_of_continuous {q : ℕ} {t : ℝ}
    (ht : 0 < t) (htR : t ≤ B.radius)
    {u : Point → Ambient q} (hu : Continuous u) {H : B.NormalTrace q t}
    (hH : B.RepresentsNormalTrace u H) (s : Icc (0 : ℝ) t) :
    ∃ hs : MemLp (fun y => u (B.normalParameter (y,s.val))) 2 (volume.restrict B.planeDomain.val),
      H s = hs.toLp _ :=
  hH.eq_raw_of_continuousOn_closure (B := B) ht htR hu.continuousOn s

theorem RepresentsNormalTrace.sub {q : ℕ} {t : ℝ} {u v : Point → Ambient q}
    {H K : B.NormalTrace q t} (hH : B.RepresentsNormalTrace u H) (hK : B.RepresentsNormalTrace v K) :
    B.RepresentsNormalTrace (u - v) (H - K) := by
  unfold RepresentsNormalTrace at hH hK ⊢
  filter_upwards [hH,hK] with s hu hv hs
  obtain ⟨hU,hHU⟩ := hu hs
  obtain ⟨hV,hKV⟩ := hv hs
  refine ⟨hU.sub hV,?_⟩
  change H _ - K _ = _
  rw [hHU,hKV,← hU.toLp_sub hV]
  rfl

theorem RepresentsNormalTrace.unique {q : ℕ} {t : ℝ} (ht : 0 < t) {u : Point → Ambient q}
    {H K : B.NormalTrace q t} (hH : B.RepresentsNormalTrace u H) (hK : B.RepresentsNormalTrace u K) : H = K :=
  continuous_Lp_representatives_eq_of_ae_slices (f := fun p : Plane × ℝ => u (B.normalParameter p))
    (g := fun p : Plane × ℝ => u (B.normalParameter p)) ht H K hH hK
    (Eventually.of_forall fun _ _ => EventuallyEq.rfl)

end Thesis.SmoothDomainEpigraphBox
