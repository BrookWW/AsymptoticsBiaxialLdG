module

public import Thesis.Interpolation.OriginalMeshSquareBoundary
import HarmonicMaps.Analysis.EuclideanHausdorffLipschitz
import StratificationTheory.Foundation.UnitCubeAffineCoordinates
import Thesis.Interpolation.PenalizedRadialFill
import Thesis.Foundation.SpectralProjection
import Thesis.StressEnergy

/-! The actual outer face, its boundary and both energy channels on a unit disk. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

/-- The inverse radial square chart transports the native Sobolev graph
and the same original boundary trace to the disk. -/
@[expose] def External.UnitSquareDiskSobolevPushforward : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (u : Plane → Ambient 5) (Du : Plane → HarmonicMaps.Gradient 2 5),
    MemW12 (unitCellCube 2) u Du → ∀ b : C(UnitSquareBoundary, Ambient 5),
      CenteredSquareTraceData u b →
      let w := u ∘ planarSquareBallHomeomorph.symm
      ∃ (Dw : Plane → HarmonicMaps.Gradient 2 5) (s : ℝ) (hs : s < 1) (H : VacuumBallTrace 2 s),
        0 < s ∧ MemW12 (ballDomain (0 : Plane) 1) w Dw ∧ RepresentsVacuumBallTrace w H ∧
        (∃ hb : MemLp (fun θ => b (unitSquareCircleHomeomorph.symm θ)) 2 (unitBoundarySurface 2),
          H ⟨1, hs.le, le_rfl⟩ = hb.toLp _) ∧
        (∫ x in ball (0 : Plane) 1, hsNormSq (Dw x)) ≤ C * (∫ x in (unitCellCube 2).val, hsNormSq (Du x))

private theorem inverse_squareDisk_preimage_unit :
    planarSquareBallHomeomorph.symm ⁻¹' (unitCellCube 2).val = ball (0 : Plane) 1 := by
  rw [← planarSquare_one_eq_unitCellCube, planarSquare_eq_preimage_ball]
  ext x
  change (planarSquareBallHomeomorph (planarSquareBallHomeomorph.symm x) ∈ ball (0 : Plane) 1) ↔ _
  rw [Homeomorph.apply_symm_apply]

private theorem map_inverse_squareDisk_volume_le :
    Measure.map planarSquareBallHomeomorph.symm (volume.restrict (ball (0 : Plane) 1)) ≤
      (9 : ℝ≥0∞) • volume.restrict (unitCellCube 2).val := by
  let e := planarSquareBallHomeomorph.symm
  have he : MeasurableEmbedding e := e.isClosedEmbedding.measurableEmbedding
  have hFull : Measure.map e (volume : Measure Plane) ≤ (9 : ℝ≥0∞) • volume := by
    apply Measure.le_iff.2
    intro U hU
    rw [Measure.map_apply he.measurable hU, ← e.image_symm]
    have h := HarmonicMaps.euclideanHausdorff_lipschitzOn_image_le_volume
      (lipschitz_coordinateCubeToBall_plane.lipschitzOnWith (s := Set.univ)) (subset_univ U)
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
    have hDim : Module.finrank ℝ Plane = 2 := by simp [Plane]
    rw [hDim] at h
    change volume (coordinateCubeToBall '' U) ≤ (3 : ℝ≥0∞) ^ 2 * volume U at h
    simpa [e, planarSquareBallHomeomorph, pow_two, show (3 : ℝ≥0∞) * 3 = 9 by norm_num] using h
  rw [← inverse_squareDisk_preimage_unit, ← he.restrict_map, ← Measure.restrict_smul]
  exact Measure.restrict_mono_measure hFull _

private theorem lintegral_inverse_squareDisk_le (p : Plane → ℝ≥0∞)
    (hp : AEMeasurable p (volume.restrict (unitCellCube 2).val)) :
    (∫⁻ x in ball (0 : Plane) 1, p (planarSquareBallHomeomorph.symm x)) ≤
      9 * ∫⁻ x in (unitCellCube 2).val, p x := by
  let e := planarSquareBallHomeomorph.symm
  let μ := volume.restrict (ball (0 : Plane) 1)
  let ν := volume.restrict (unitCellCube 2).val
  have hDom : Measure.map e μ ≤ (9 : ℝ≥0∞) • ν := map_inverse_squareDisk_volume_le
  have hp' : AEMeasurable p (Measure.map e μ) :=
    (hp.smul_measure (c := (9 : ℝ≥0∞))).mono_measure hDom
  change (∫⁻ x, p (e x) ∂μ) ≤ 9 * ∫⁻ x, p x ∂ν
  rw [← lintegral_map' hp' e.continuous.measurable.aemeasurable]
  exact (lintegral_mono' hDom le_rfl).trans_eq (lintegral_smul_measure _ _)

variable {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}
  {G : PenalizedSphereFaces a B h v hv} {f : ↥(cubeBoundarySquares G.grid.level)}

/-- Original continuous circle datum of the physical face. -/
@[expose] def OriginalMeshSquareBoundary.circle (P : OriginalMeshSquareBoundary G f) : C(NativeCircle, S0) :=
  P.boundary.comp ⟨unitSquareCircleHomeomorph.symm, unitSquareCircleHomeomorph.symm.continuous⟩

theorem OriginalMeshSquareBoundary.forall_circle (P : OriginalMeshSquareBoundary G f) {p : S0 → Prop}
    (hEdges : ∀ i j t, t ∈ Icc 0 h → p (G.grid.trace (tensorSquareCoordinateEdge f i j) t)) :
    ∀ θ, p (P.circle θ) :=
  fun θ => P.forall_boundary hEdges (unitSquareCircleHomeomorph.symm θ)

theorem OriginalMeshSquareBoundary.circle_projection (P : OriginalMeshSquareBoundary G f) {C δ : ℝ}
    (J : ProjectedMeshSquareBoundary G f C) (hδ : δ ≤ (vacuumTubularProjection a).radius)
    (hTube : ∀ e t, t ∈ Icc (0 : ℝ) h → G.grid.trace e t ∈ vacuumTube a δ)
    (θ : NativeCircle) :
    spectralVacuumPoint a (P.circle θ) = squareVacuumBoundaryLoop a J.boundary θ := by
  let x := unitSquareCircleHomeomorph.symm θ
  change spectralVacuumPoint a (P.boundary x) = J.boundary x
  obtain ⟨i, p, t, ht⟩ := exists_unitSquareSideParameter x
  rw [← ht]
  apply Subtype.ext
  rw [P.edge i p t.val t.property, J.edge i p t.val t.property]
  let A := G.grid.trace (tensorSquareCoordinateEdge f i p) (normalizedEdgeParameter h t.val)
  let S := vacuumTubularProjection a
  have hA₀ : infDist A (vacuum a) < δ :=
    hTube _ _ (normalizedEdgeParameter_mem_closed G.ht_pos t.property)
  have hA : A ∈ vacuumTube a S.radius := hA₀.trans_le hδ
  change (spectralVacuumPoint a A).val = S.extend A
  exact (congrArg Subtype.val (spectralVacuumPoint_eq_tubeProjection S ⟨A, hA⟩)).trans (S.extend_eq ⟨A, hA⟩).symm

theorem OriginalMeshSquareBoundary.circle_angular_estimates
    (hAngular : External.SquareBoundaryAngularSobolev) (hMeasure : External.SquareBoundaryAngularMeasure) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}
      {G : PenalizedSphereFaces a B h v hv} {f : ↥(cubeBoundarySquares G.grid.level)}
      (P : OriginalMeshSquareBoundary G f),
      let b (t : ℝ) := P.circle (circleNativeParam (t - Real.pi))
      AbsolutelyContinuousOnInterval b 0 (2 * Real.pi) ∧
      MemLp (deriv b) 2 (volume.restrict (Ioo 0 (2 * Real.pi))) ∧
      (∫ t in Ioo 0 (2 * Real.pi), ‖deriv b t‖ ^ 2) ≤ C * (h / 2) * meshSquareEdgeDerivativeEnergy G f ∧
      (∫ t in Ioo 0 (2 * Real.pi), bulkPotential a (b t)) ≤ C * (h / 2)⁻¹ * meshSquareEdgeBulkEnergy G f := by
  obtain ⟨K, hK, hAngle⟩ := hAngular
  obtain ⟨L, hL, hMeasure⟩ := hMeasure
  let C := max K L
  refine ⟨C, hK.trans_le (le_max_left _ _), ?_⟩
  intro B h v hv G f P b
  have hEq : EqOn (squareBoundaryAngular P.boundary) b (Icc 0 (2 * Real.pi)) := by
    intro t ht
    let T := 2 * Real.pi
    have hT : 0 < T := Real.two_pi_pos
    have hDiv : t / T ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hT.le, (div_le_one hT).2 ht.2⟩
    have hP : (vacuumLoopParameter T t).val = t / T :=
      congrArg Subtype.val (projIcc_of_mem zero_le_one hDiv)
    have hAngle : nativeCircleLoopParam (vacuumLoopParameter T t) = circleNativeParam (t - Real.pi) := by
      change circleNativeParam (T * (vacuumLoopParameter T t).val - Real.pi) = _
      rw [hP, mul_comm T, div_mul_cancel₀ _ hT.ne']
    exact congrArg (fun θ => P.boundary (unitSquareCircleHomeomorph.symm θ)) hAngle
  obtain ⟨hAC, hD, hEn⟩ := hAngle P.boundary P.edge_sobolev
  have hDer : deriv (squareBoundaryAngular P.boundary) =ᵐ[volume.restrict (Ioo 0 (2 * Real.pi))] deriv b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have h : squareBoundaryAngular P.boundary =ᶠ[𝓝 t] b :=
      Filter.Eventually.mono (Icc_mem_nhds ht.1 ht.2) hEq
    exact h.deriv_eq
  refine ⟨?_, hD.ae_eq hDer, ?_, ?_⟩
  · rw [absolutelyContinuousOnInterval_iff] at hAC ⊢
    intro ε hε
    obtain ⟨δ, hδ, hCrit⟩ := hAC ε hε
    refine ⟨δ, hδ, fun I hI hSmall => ?_⟩
    refine lt_of_eq_of_lt (Finset.sum_congr rfl fun i hi => ?_) (hCrit I hI hSmall)
    have hPair := hI.1 i hi
    rw [uIcc_of_le Real.two_pi_pos.le] at hPair
    exact congrArg₂ dist (hEq hPair.1).symm (hEq hPair.2).symm
  · have hEnergyEq := integral_congr_ae (hDer.symm.mono fun _ h => congrArg (fun z : S0 => ‖z‖ ^ 2) h)
    have hBudget : 0 ≤ meshSquareEdgeDerivativeEnergy G f :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
    calc
      _ = ∫ t in Ioo 0 (2 * Real.pi), ‖deriv (squareBoundaryAngular P.boundary) t‖ ^ 2 := hEnergyEq
      _ ≤ K * (∑ i : Fin 2, ∑ p : Bool,
          ∫ t in Ioo (-1 : ℝ) 1, ‖deriv (P.boundary ∘ unitSquareSideParameter i p) t‖ ^ 2) := hEn
      _ = K * ((h / 2) * meshSquareEdgeDerivativeEnergy G f) := congrArg (K * ·) P.derivative_energy
      _ ≤ C * (h / 2) * meshSquareEdgeDerivativeEnergy G f := by
        rw [mul_assoc C]
        exact mul_le_mul_of_nonneg_right (le_max_left K L) (mul_nonneg (half_pos G.ht_pos).le hBudget)
  · let Φ : C(UnitSquareBoundary, ℝ) := ⟨fun x => bulkPotential a (P.boundary x),
      (contDiff_bulkPotential a).continuous.comp P.boundary.continuous⟩
    have hMeasureBound := hMeasure Φ (fun _ => bulkPotential_nonneg a _)
    have hEnergyEq : (∫ t in Ioo 0 (2 * Real.pi), bulkPotential a (b t)) =
        ∫ t in Ioo 0 (2 * Real.pi), squareBoundaryAngular Φ t := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      exact congrArg (bulkPotential a) (hEq (Ioo_subset_Icc_self ht)).symm
    have hBudget : 0 ≤ meshSquareEdgeBulkEnergy G f := Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => bulkPotential_nonneg a _
    calc
      _ = ∫ t in Ioo 0 (2 * Real.pi), squareBoundaryAngular Φ t := hEnergyEq
      _ ≤ L * (∑ i : Fin 2, ∑ p : Bool,
          ∫ t in Ioo (-1 : ℝ) 1, bulkPotential a (P.boundary (unitSquareSideParameter i p t))) := hMeasureBound
      _ = L * ((h / 2)⁻¹ * meshSquareEdgeBulkEnergy G f) := congrArg (L * ·) P.bulk_energy
      _ ≤ C * (h / 2)⁻¹ * meshSquareEdgeBulkEnergy G f := by
        rw [mul_assoc C]
        exact mul_le_mul_of_nonneg_right (le_max_right K L) (mul_nonneg (inv_nonneg.2 (half_pos G.ht_pos).le) hBudget)

private def OriginalMeshSquareBoundary.centeredTraces (P : OriginalMeshSquareBoundary G f)
    (T : NormalizedSquareTraces h (fun x => frobeniusCoordinateEquiv (G.face f x))
      (fun i p t => frobeniusCoordinateEquiv (G.grid.trace (tensorSquareCoordinateEdge f i p) t))) :
    CenteredSquareTraceData
      (fun x => frobeniusCoordinateEquiv (G.face f (unitToPhysicalCellFace h x)))
      (fun x => frobeniusCoordinateEquiv (P.boundary x)) where
  curve := T.curve
  slice := T.slice
  edge i p := by
    filter_upwards [T.edge i p, ae_restrict_mem (unitCellCube 1).property.measurableSet] with x hx hxU
    have hX : x 0 ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self (mem_iInter.1 hxU 0)
    rw [hx, P.edge i p (x 0) hX]
    exact congrArg (fun t => frobeniusCoordinateEquiv (G.grid.trace (tensorSquareCoordinateEdge f i p) t))
      (add_comm (h / 2) ((h / 2) * x 0))

/-- One original bounded physical face transported to the unit disk. The
gradient and bulk channels have the two distinct similarity scalings. -/
theorem exists_meshFaceDisk (hTransport : External.UnitSquareDiskSobolevPushforward) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}
      {G : PenalizedSphereFaces a B h v hv} {f : ↥(cubeBoundarySquares G.grid.level)}
      (_ : ∀ θ, ‖v θ‖ ≤ B) (P : OriginalMeshSquareBoundary G f),
      ∃ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5) (s : ℝ) (hs : s < 1)
        (H : VacuumBallTrace 2 s),
        0 < s ∧
        w = (fun x => frobeniusCoordinateEquiv (G.face f (unitToPhysicalCellFace h (planarSquareBallHomeomorph.symm x)))) ∧
        MemW12 (ballDomain (0 : Plane) 1) w Dw ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖frobeniusCoordinateEquiv.symm (w x)‖ ≤ B) ∧
        RepresentsVacuumBallTrace w H ∧
        (∃ hb : MemLp (fun θ => frobeniusCoordinateEquiv (P.circle θ)) 2 (unitBoundarySurface 2),
          H ⟨1, hs.le, le_rfl⟩ = hb.toLp _) ∧
        (∫ x in ball (0 : Plane) 1, hsNormSq (Dw x)) ≤
          C * (∫ x in (tensorGridOpenParameterBox 2 h).val, ∑ i, ‖G.derivative f x i‖ ^ 2) ∧
        (∫⁻ x in ball (0 : Plane) 1, ENNReal.ofReal (bulkPotential a (frobeniusCoordinateEquiv.symm (w x)))) ≤
          ENNReal.ofReal (9 * (h / 2)⁻¹ ^ 2) *
            ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (bulkPotential a (G.face f x)) := by
  obtain ⟨C, hC, hTransport⟩ := hTransport
  refine ⟨C, hC, ?_⟩
  intro B h v hv G f hBound P
  let u (x : Plane) := frobeniusCoordinateEquiv (G.face f x)
  let D (x : Plane) (i : Fin 2) := frobeniusCoordinateEquiv (G.derivative f x i)
  let F := unitToPhysicalCellFace h
  let z := u ∘ F
  let Dz (x : Plane) (i : Fin 2) := (h / 2) • D (F x) i
  let b : C(UnitSquareBoundary, Ambient 5) := ⟨fun x => frobeniusCoordinateEquiv (P.boundary x),
    frobeniusCoordinateEquiv.continuous.comp P.boundary.continuous⟩
  have hh := G.ht_pos
  have hu : MemW12 (tensorGridOpenParameterBox 2 h) u D := G.face_memW12 f
  obtain ⟨hz, hGrad, _, hValues⟩ := memW12_unit_cube_normalization_energy hh hu
  change MemW12 (unitCellCube 2) z Dz at hz
  have hGrad' : (∫ x in (unitCellCube 2).val, hsNormSq (Dz x)) =
      ∫ x in (tensorGridOpenParameterBox 2 h).val, ∑ i, ‖G.derivative f x i‖ ^ 2 := by
    change (∫ x in (unitCellCube 2).val, hsNormSq (Dz x)) =
      (h / 2) ^ (2 - ((2 : ℕ) : ℤ)) * (∫ x in (tensorGridOpenParameterBox 2 h).val, hsNormSq (D x)) at hGrad
    have hPow : (2 : ℤ) - ((2 : ℕ) : ℤ) = 0 := by norm_num
    simpa only [hPow, zpow_zero, one_mul, hsNormSq, D, frobeniusCoordinateEquiv.norm_map] using hGrad
  obtain ⟨T⟩ := G.exists_normalized_traces f
  obtain ⟨Dw, s, hs, H, hs₀, hw, hRep, hTrace, hCost⟩ := hTransport z Dz hz b (P.centeredTraces T)
  let e := planarSquareBallHomeomorph.symm
  let w := z ∘ e
  have huB : ∀ᵐ x ∂volume.restrict (tensorGridOpenParameterBox 2 h).val,
      ‖frobeniusCoordinateEquiv.symm (u x)‖ ≤ B := by
    filter_upwards [ae_restrict_mem (tensorGridOpenParameterBox 2 h).property.measurableSet] with x hx
    obtain ⟨θ, _, hθ⟩ := G.face_eq f x (Ioo_subset_Icc_self (mem_iInter.1 hx 0))
      (Ioo_subset_Icc_self (mem_iInter.1 hx 1))
    rw [show frobeniusCoordinateEquiv.symm (u x) = G.face f x from frobeniusCoordinateEquiv.symm_apply_apply _,
      hθ]
    exact hBound θ
  have hzB : ∀ᵐ x ∂volume.restrict (unitCellCube 2).val, ‖frobeniusCoordinateEquiv.symm (z x)‖ ≤ B :=
    hValues (fun y => ‖frobeniusCoordinateEquiv.symm y‖ ≤ B) huB
  have hwB : ∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖frobeniusCoordinateEquiv.symm (w x)‖ ≤ B := by
    rw [← inverse_squareDisk_preimage_unit]
    apply (ae_restrict_iff' (e.continuous.measurable (unitCellCube 2).property.measurableSet)).2
    exact planarSquareBallHomeomorph_symm_quasiMeasurePreserving.ae
      ((ae_restrict_iff' (unitCellCube 2).property.measurableSet).1 hzB)
  refine ⟨w, Dw, s, hs, H, hs₀, rfl, hw, hwB, hRep, hTrace, hCost.trans_eq (congrArg (C * ·) hGrad'), ?_⟩
  let p (x : Plane) := ENNReal.ofReal (bulkPotential a (frobeniusCoordinateEquiv.symm (u x)))
  let μ := volume.restrict (unitCellCube 2).val
  let ν := volume.restrict (tensorGridOpenParameterBox 2 h).val
  have hP : AEMeasurable p ν :=
    ((ENNReal.continuous_ofReal.comp (contDiff_bulkPotential a).continuous).comp
      frobeniusCoordinateEquiv.symm.continuous).measurable.comp_aemeasurable hu.2.1.aemeasurable
  have hzP : AEMeasurable (p ∘ F) μ :=
    ((ENNReal.continuous_ofReal.comp (contDiff_bulkPotential a).continuous).comp
      frobeniusCoordinateEquiv.symm.continuous).measurable.comp_aemeasurable hz.2.1.aemeasurable
  have hMap : Measure.map F μ = ENNReal.ofReal (((h / 2) ^ 2)⁻¹) • ν :=
    map_affine_unit_cube_volume 2 hh
  have hAff : MeasurableEmbedding F := by
    change MeasurableEmbedding (fun x : Plane => WithLp.toLp 2 (fun _ => h / 2) + (h / 2) • x)
    simpa only [sub_zero] using
      affineBall_measurableEmbedding (WithLp.toLp 2 (fun _ => h / 2) : Plane) 0 (half_pos hh).ne'
  have hNormBulk : (∫⁻ x, p (F x) ∂μ) =
      ENNReal.ofReal (((h / 2) ^ 2)⁻¹) * ∫⁻ x, p x ∂ν := by
    have hP' : AEMeasurable p (Measure.map F μ) := by
      rw [hMap]
      exact hP.smul_measure _
    exact (lintegral_map' hP' hAff.measurable.aemeasurable).symm.trans
      ((congrArg (fun m : Measure Plane => ∫⁻ x, p x ∂m) hMap).trans (lintegral_smul_measure _ _))
  have hpEq : (fun x => p x) = fun x => ENNReal.ofReal (bulkPotential a (G.face f x)) :=
    funext fun x => congrArg (fun y => ENNReal.ofReal (bulkPotential a y)) (frobeniusCoordinateEquiv.symm_apply_apply _)
  have hNine : (9 : ℝ≥0∞) = ENNReal.ofReal (9 : ℝ) := (by norm_num)
  change (∫⁻ x in ball (0 : Plane) 1, (p ∘ F) (e x)) ≤ _
  refine (lintegral_inverse_squareDisk_le _ hzP).trans_eq ?_
  change (9 : ℝ≥0∞) * (∫⁻ x, p (F x) ∂μ) = _
  rw [hNormBulk, hNine, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (9 : ℝ)), inv_pow]
  exact congrArg _ (congrArg (fun g : Plane → ℝ≥0∞ => ∫⁻ x, g x ∂ν) hpEq)

end Thesis
