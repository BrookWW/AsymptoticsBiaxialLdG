module

public import Thesis.MeasureGeometry.PlanarBoundaryLowerBound
import HarmonicMaps.Analysis.SmoothWeakGradient
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import StratificationTheory.Foundation.AngularL2Membership

/-! Applying the boundary logarithmic estimate on physical planar slices. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

private theorem continuous_memLp_restrict_compact {X E : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup E] [SecondCountableTopology E] {μ : Measure X} [IsFiniteMeasure μ] {f : X → E}
    (hf : Continuous f) {K : Set X} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K) :
    MemLp f 2 μ := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable M (hμ.mono hM)

private theorem exists_nativeBallTrace_of_continuous (u : Plane → Ambient 5) (hu : Continuous u) :
    ∃ H : VacuumBallTrace 2 (1 / 2), RepresentsVacuumBallTrace u H ∧
      ∃ hb : MemLp (fun z : NativeCircle => u z.val) 2 (unitBoundarySurface 2),
        H ⟨1, by norm_num, le_rfl⟩ = hb.toLp _ := by
  letI : IsFiniteMeasure (unitBoundarySurface 2) := by
    change IsFiniteMeasure (Measure.euclideanHausdorffMeasure (2 - 1) : Measure NativeCircle)
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)]
    infer_instance
  letI : CompactSpace NativeCircle := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let F : C(Icc (1 / 2 : ℝ) 1 × NativeCircle, Ambient 5) :=
    ⟨fun p => u (p.1.val • p.2.val), hu.comp (by fun_prop)⟩
  let L := (ContinuousMap.toLp 2 (unitBoundarySurface 2) ℝ :
    C(NativeCircle, Ambient 5) →L[ℝ] Lp (Ambient 5) 2 (unitBoundarySurface 2))
  let H : VacuumBallTrace 2 (1 / 2) := ⟨fun t => L (F.curry t), L.continuous.comp F.curry.continuous⟩
  have hSlice (t : Icc (1 / 2 : ℝ) 1) :
      ∃ ht : MemLp (fun z : NativeCircle => u (t.val • z.val)) 2 (unitBoundarySurface 2),
        H t = ht.toLp _ := by
    have ht : MemLp (fun z : NativeCircle => u (t.val • z.val)) 2 (unitBoundarySurface 2) :=
      (F.curry t).memLp (unitBoundarySurface 2) ℝ
    refine ⟨ht, Lp.ext ?_⟩
    exact ((F.curry t).coeFn_toLp (p := 2) (𝕜 := ℝ) (unitBoundarySurface 2)).trans ht.coeFn_toLp.symm
  refine ⟨H, ae_of_all _ (fun t ht => hSlice ⟨t, ht.1.le, ht.2.le⟩), ?_⟩
  simpa only [one_smul] using hSlice ⟨1, by norm_num, le_rfl⟩

/-- The exact dimension-two energy scaling on physical disks. -/
theorem planarSmoothEnergy_scale_unit (a : BulkCoefficients) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (Q : Plane → S0) (hQ : ContDiff ℝ 1 Q) :
    planarSmoothEnergy a (ε / r) (fun x => Q (r • x)) 1 = planarSmoothEnergy a ε Q r := by
  classical
  let S := ball (0 : Plane) 1
  let T := ball (0 : Plane) r
  let f := planarSmoothEnergyDensity a ε Q
  have hEq (x : Plane) : planarSmoothEnergyDensity a (ε / r) (fun y => Q (r • y)) x =
      r ^ 2 * f (r • x) := by
    dsimp only [f, planarSmoothEnergyDensity]
    rw [scaled_planarSmoothDirichletDensity Q hQ r hr]
    field_simp [hr.ne', hε.ne']
  have hP (x : Plane) : x ∈ S ↔ r • x ∈ T := by
    simp only [S, T, mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le]
    constructor
    · intro h
      simpa only [mul_one] using mul_lt_mul_of_pos_left h hr
    · intro h
      exact lt_of_not_ge (fun h' => h.not_ge (by simpa only [mul_one] using mul_le_mul_of_nonneg_left h' hr.le))
  have hInd : S.indicator (fun y => f (r • y)) = fun x => T.indicator f (r • x) := by
    funext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, indicator_of_mem ((hP x).mp hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hP x).mpr h))]
  have hDim : Module.finrank ℝ Plane = 2 := by simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  change (∫ x in S, planarSmoothEnergyDensity a (ε / r) (fun y => Q (r • y)) x) = ∫ x in T, f x
  simp_rw [hEq]
  rw [integral_const_mul, ← integral_indicator (show MeasurableSet S from measurableSet_ball),
    hInd, Measure.integral_comp_smul_of_nonneg volume _ r (hR := hr.le), hDim, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul, integral_indicator measurableSet_ball]

private theorem exists_planarSmooth_boundary_gap_lower_radius_global
    (hcoarea : External.PlanarScalarCoarea) (hAngular : External.PeriodicAngularSobolev)
    (a : BulkCoefficients) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r ε g : ℝ}, 0 < r → 0 < ε → ε < r / 80 → 0 < g →
      ∀ (Q : Plane → S0), ContDiff ℝ ∞ Q →
        (∀ x ∈ ball (0 : Plane) r, ‖Q x‖ ≤ C₀) →
        (∀ z : NativeCircle, g ≤ normalizedSpectralGap a (Q (r • z.val))) →
        ∀ q : C(NativeCircle, vacuum a),
          (∀ z, q z = spectralVacuumPoint a (Q (r • z.val))) →
          let β (t : ℝ) := Q (r • (circleNativeParam (t - Real.pi)).val)
          nativeVacuumCircleCost a q * g ^ 2 * Real.log (r / ε) - C ≤
            planarSmoothEnergy a ε Q r +
              Real.log 80 * ((1 / 2 : ℝ) * (∫ t in Ioo 0 (2 * Real.pi), ‖deriv β t‖ ^ 2) +
                (r / ε) ^ 2 * ∫ t in Ioo 0 (2 * Real.pi), bulkPotential a (β t)) := by
  obtain ⟨C, hC, hUnit⟩ := exists_planarWeakEnergy_boundary_gap_lower_unit hcoarea hAngular a C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro r ε g hr hε hεr hg Q hQ hNorm hGap q hq β
  let A : Plane →L[ℝ] Plane := r • ContinuousLinearMap.id ℝ Plane
  let P (x : Plane) := Q (r • x)
  have hP : ContDiff ℝ ∞ P := hQ.comp A.contDiff
  let v (x : Plane) := frobeniusCoordinateEquiv (P x)
  have hv : ContDiff ℝ ∞ v := frobeniusCoordinateEquiv.toContinuousLinearMap.contDiff.comp hP
  letI := finite_planarVolume_restrict_ball 1
  have hBound : ∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖v x‖ ≤ C₀ := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [show ‖v x‖ = ‖Q (r • x)‖ from frobeniusCoordinateEquiv.norm_map _]
    apply hNorm
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_lt_of_lt_one_right hr (mem_ball_zero_iff.mp hx)
  have hvMem : MemLp v 2 (volume.restrict (ball (0 : Plane) 1)) :=
    MemLp.of_bound hv.continuous.aestronglyMeasurable C₀ hBound
  have hDv (i : Fin 2) : MemLp (coordinateDerivative v hv i) 2 (volume.restrict (ball (0 : Plane) 1)) := by
    have hCT : Continuous (coordinateDerivative v hv i) :=
      (hv.continuous_fderiv (by simp)).clm_apply continuous_const
    exact continuous_memLp_restrict_compact hCT (isCompact_closedBall (0 : Plane) 1)
      ((ae_restrict_mem measurableSet_ball).mono fun _ hx => ball_subset_closedBall hx)
  have hW := memW12_of_contDiff (ballDomain (0 : Plane) 1) hv hvMem hDv
  let b : C(NativeCircle, S0) := ⟨fun z => P z.val, hP.continuous.comp continuous_subtype_val⟩
  obtain ⟨H, hH, hEnd⟩ := exists_nativeBallTrace_of_continuous v hv.continuous
  have hβ : ContDiff ℝ 1 β := by
    change ContDiff ℝ 1 (fun t => P ((circleNativeParam (t - Real.pi)).val))
    exact (hP.of_le (by decide)).comp (contDiff_circleNativeParam_val.comp (contDiff_id.sub contDiff_const))
  have hBD : MemLp (deriv β) 2 (volume.restrict (Ioo 0 (2 * Real.pi))) := by
    letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi))) := by infer_instance
    exact continuous_memLp_restrict_compact hβ.continuous_deriv_one isCompact_Icc
      ((ae_restrict_mem measurableSet_Ioo).mono fun _ hx => Ioo_subset_Icc_self hx)
  have hE := hUnit (div_pos hε hr) ((div_lt_iff₀ hr).mpr (by linarith only [hεr])) hg
    v (fun x i => coordinateDerivative v hv i x) hW hBound b (by norm_num) H hH hEnd
    hβ.contDiffOn.absolutelyContinuousOnInterval hBD hGap q hq
  have hNormEnergy : planarWeakEnergy a (ε / r) v (fun x i => coordinateDerivative v hv i x) 1 =
      planarSmoothEnergy a ε Q r := by
    refine (planarSmoothEnergy_eq_weak a (ε / r) v hv 1).symm.trans ?_
    have hEq : (fun x => frobeniusCoordinateEquiv.symm (v x)) = P := by
      funext x
      exact frobeniusCoordinateEquiv.symm_apply_apply _
    rw [hEq]
    exact planarSmoothEnergy_scale_unit a hr hε Q (hQ.of_le (by decide))
  have hξ : (ε / r)⁻¹ = r / ε := inv_div _ _
  have hξ' : 1 / (ε / r) = r / ε := by rw [one_div, hξ]
  rw [hNormEnergy, hξ, hξ'] at hE
  exact hE

/-- The actual smooth planar boundary estimate at any positive physical
radius. The boundary term is `r log 80` times the physical circle energy. -/
theorem exists_planarSmooth_boundary_gap_lower_radius
    (hcoarea : External.PlanarScalarCoarea) (hAngular : External.PeriodicAngularSobolev)
    (a : BulkCoefficients) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r ε g : ℝ}, 0 < r → 0 < ε → ε < r / 80 → 0 < g →
      ∀ (Q : Plane → S0) (U : Set Plane), IsOpen U → closedBall (0 : Plane) r ⊆ U → ContDiffOn ℝ ∞ Q U →
        (∀ x ∈ ball (0 : Plane) r, ‖Q x‖ ≤ C₀) →
        (∀ z : NativeCircle, g ≤ normalizedSpectralGap a (Q (r • z.val))) →
        ∀ q : C(NativeCircle, vacuum a),
          (∀ z, q z = spectralVacuumPoint a (Q (r • z.val))) →
          let β (t : ℝ) := Q (r • (circleNativeParam (t - Real.pi)).val)
          nativeVacuumCircleCost a q * g ^ 2 * Real.log (r / ε) - C ≤
            planarSmoothEnergy a ε Q r +
              Real.log 80 * ((1 / 2 : ℝ) * (∫ t in Ioo 0 (2 * Real.pi), ‖deriv β t‖ ^ 2) +
                (r / ε) ^ 2 * ∫ t in Ioo 0 (2 * Real.pi), bulkPotential a (β t)) := by
  obtain ⟨C, hC, hGlobal⟩ := exists_planarSmooth_boundary_gap_lower_radius_global hcoarea hAngular a C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro r ε g hr hε hεr hg Q U hU hBall hQ hNorm hGap q hq β
  obtain ⟨P, hP, hEq⟩ := exists_contDiff_eq_near_compact_of_order (n := ⊤)
    hU (isCompact_closedBall (0 : Plane) r) hBall hQ
  have hPoint (z : NativeCircle) : P (r • z.val) = Q (r • z.val) :=
    (hEq _ (by rw [mem_closedBall_zero_iff, planar_norm_on_circle hr.le])).eq_of_nhds
  have hLower := hGlobal hr hε hεr hg P hP
    (fun x hx => ((hEq x (ball_subset_closedBall hx)).eq_of_nhds).symm ▸ hNorm x hx)
    (fun z => (hPoint z).symm ▸ hGap z) q (fun z => (hPoint z).symm ▸ hq z)
  have hβ : (fun t : ℝ => P (r • (circleNativeParam (t - Real.pi)).val)) = β := funext fun t => hPoint _
  have hE : planarSmoothEnergy a ε P r = planarSmoothEnergy a ε Q r := by
    unfold planarSmoothEnergy
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    have hN := hEq x (ball_subset_closedBall hx)
    have hD : fderiv ℝ (fun y => (P y : Tensor)) x = fderiv ℝ (fun y => (Q y : Tensor)) x :=
      (hN.fun_comp (fun A : S0 => (A : Tensor))).fderiv_eq
    unfold planarSmoothEnergyDensity planarSmoothDirichletDensity
    rw [hN.eq_of_nhds, hD]
  dsimp only at hLower
  have hPt (t : ℝ) : P (r • (circleNativeParam (t - Real.pi)).val) = β t := congrFun hβ t
  exact hLower.trans_eq (by rw [hE, hβ]; simp_rw [hPt])

end Thesis
