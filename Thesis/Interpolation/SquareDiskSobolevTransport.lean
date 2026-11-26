module

public import Thesis.Interpolation.SquareDiskFill
public import Thesis.Interpolation.LipschitzSobolevPullback
import Thesis.Interpolation.InverseDilationTrace
import HarmonicMaps.Analysis.EuclideanHausdorffLipschitz
import HarmonicMaps.EnergyLemmas
import StratificationTheory.Foundation.CubicalConeGeometry
import StratificationTheory.Foundation.CoordinateRectangleTrace
import StratificationTheory.Foundation.IsometricDomainSobolevPullback
import StratificationTheory.Foundation.FlatRadialEndpoint
import StratificationTheory.Foundation.LpTwoMeasureRestriction

/-! The native centered square and disk weak graph and boundary trace transport. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal NNReal Topology

namespace Thesis

theorem squareDisk_preimage_unit :
    planarSquareBallHomeomorph ⁻¹' ball (0 : Plane) 1 = (unitCellCube 2).val := by
  rw [← planarSquare_eq_preimage_ball, planarSquare_one_eq_unitCellCube]

private theorem map_squareDisk_volume_le :
    Measure.map planarSquareBallHomeomorph (volume.restrict (unitCellCube 2).val) ≤
      (64 : ℝ≥0∞) • volume.restrict (ball (0 : Plane) 1) := by
  let e := planarSquareBallHomeomorph
  have he : MeasurableEmbedding e := e.isClosedEmbedding.measurableEmbedding
  have hVol : Measure.map e (volume : Measure Plane) ≤ (64 : ℝ≥0∞) • volume := by
    apply Measure.le_iff.2
    intro U hU
    rw [Measure.map_apply he.measurable hU, ← e.image_symm]
    have h := HarmonicMaps.euclideanHausdorff_lipschitzOn_image_le_volume
      (lipschitz_ballToCoordinateCube_plane.lipschitzOnWith (s := Set.univ)) (subset_univ U)
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
    have hDim : Module.finrank ℝ Plane = 2 := by simp [Plane]
    rw [hDim] at h
    change volume (ballToCoordinateCube '' U) ≤ (8 : ℝ≥0∞) ^ 2 * volume U at h
    simpa [e, planarSquareBallHomeomorph, pow_two, show (8 : ℝ≥0∞) * 8 = 64 by norm_num] using h
  rw [← squareDisk_preimage_unit, ← he.restrict_map, ← Measure.restrict_smul]
  exact Measure.restrict_mono_measure hVol _

/-- The literal square pullback of a disk graph has its actual weak columns
and unhalved Dirichlet energy bounded by `1152` times the disk energy. -/
theorem exists_unitSquare_memW12_disk_pullback (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5)
    (hw : MemW12 (ballDomain (0 : Plane) 1) w Dw) :
    ∃ G : Plane → HarmonicMaps.Gradient 2 5,
      MemW12 (unitCellCube 2) (w ∘ planarSquareBallHomeomorph) G ∧
      (∫ x in (unitCellCube 2).val, hsNormSq (G x)) ≤ 1152 * (∫ x in ball (0 : Plane) 1, hsNormSq (Dw x)) := by
  let e := planarSquareBallHomeomorph
  let G (x : Plane) (i : Fin 2) := ∑ j : Fin 2, (fderiv ℝ e x (EuclideanSpace.single i 1)) j • Dw (e x) j
  have hInto : MapsTo e (unitCellCube 2).val (ball (0 : Plane) 1) := by
    intro x hx
    change x ∈ planarSquareBallHomeomorph ⁻¹' (ball (0 : Plane) 1)
    rw [squareDisk_preimage_unit]
    exact hx
  have hSquareVol : (volume : Measure Plane) (unitCellCube 2).val ≠ ⊤ := volume_unit_coordinate_face_ne_top 2
  have hG : MemW12 (unitCellCube 2) (w ∘ e) G := memW12_lipschitz_domain_pullback_ball zero_lt_one hw
    (unitCellCube 2) hSquareVol e lipschitz_coordinateCubeToBall_plane hInto (by norm_num) map_squareDisk_volume_le
  refine ⟨G, hG, ?_⟩
  have hE := dirichletEnergy_lipschitz_pullback_le (unitCellCube 2).val (ball (0 : Plane) 1)
    e lipschitz_coordinateCubeToBall_plane map_squareDisk_volume_le Dw hw.2.2
  change HarmonicMaps.dirichletEnergy G (unitCellCube 2).val ≤
    ENNReal.ofReal ((2 : ℝ) * ((3 : ℝ≥0) : ℝ) ^ 2) * (64 * HarmonicMaps.dirichletEnergy Dw (ball (0 : Plane) 1)) at hE
  have hDw : IntegrableOn (fun x => hsNormSq (Dw x)) (ball (0 : Plane) 1) := hw.integrable_hsNormSq
  rw [HarmonicMaps.dirichletEnergy_eq_ofReal_integral hG.integrable_hsNormSq,
    HarmonicMaps.dirichletEnergy_eq_ofReal_integral hDw] at hE
  have hE' := ENNReal.toReal_mono (by finiteness) hE
  have hG₀ : 0 ≤ ∫ x in (unitCellCube 2).val, hsNormSq (G x) := integral_nonneg fun _ => hsNormSq_nonneg _
  have hDw₀ : 0 ≤ ∫ x in ball (0 : Plane) 1, hsNormSq (Dw x) := integral_nonneg fun _ => hsNormSq_nonneg _
  have hL₀ : 0 ≤ (2 : ℝ) * ((3 : ℝ≥0) : ℝ) ^ 2 := by norm_num
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hG₀, ENNReal.toReal_ofReal hDw₀,
    ENNReal.toReal_ofReal hL₀] at hE'
  norm_num at hE'
  linarith only [hE']

private theorem squareSideSingle_isometry : Isometry
    (fun t : ℝ => (EuclideanSpace.single (0 : Fin 1) t : Domain 1)) :=
  Isometry.of_dist_eq fun x y => PiLp.dist_single_same 2 (fun _ : Fin 1 => ℝ) 0 x y

@[expose] def squareDiskSideAngle (i : Fin 2) (p : Bool) (x : Domain 1) : NativeCircle :=
  unitSquareCircleHomeomorph (unitSquareSideParameter i p (x 0))

private theorem continuous_squareDiskSideAngle (i : Fin 2) (p : Bool) :
    Continuous (squareDiskSideAngle i p) := by
  have hProj : Continuous (fun x : Domain 1 => x 0) := (EuclideanSpace.proj 0).continuous
  have hClamped : Continuous (fun x : Domain 1 => (projIcc (-1 : ℝ) 1 (by norm_num) (x 0)).val) :=
    continuous_subtype_val.comp (continuous_projIcc.comp hProj)
  have hSide : Continuous (fun x : Domain 1 => (unitSquareSideParameter i p (x 0)).val) := by
    change Continuous (fun x : Domain 1 => unitCellFaceSlice i
      (EuclideanSpace.single 0 (projIcc (-1 : ℝ) 1 (by norm_num) (x 0)).val) (if p then 1 else -1))
    unfold unitCellFaceSlice
    have hPair : Continuous (fun x : Domain 1 =>
      (EuclideanSpace.single (0 : Fin 1) (projIcc (-1 : ℝ) 1 (by norm_num) (x 0)).val,
        EuclideanSpace.single (0 : Fin 1) (if p then (1 : ℝ) else -1))) :=
      (squareSideSingle_isometry.continuous.comp hClamped).prodMk continuous_const
    exact (cubicalSignedFaceIsometry 1 i true).continuous.comp
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).symm.continuous.comp hPair)
  exact unitSquareCircleHomeomorph.continuous.comp (hSide.subtype_mk fun x =>
    (unitSquareSideParameter i p (x 0)).property)

private def squareDiskSideInverse (i : Fin 2) (θ : NativeCircle) : Domain 1 :=
  EuclideanSpace.single 0 ((ballToCoordinateCube θ.val) (if i = 0 then 1 else 0))

private theorem lipschitz_squareDiskSideInverse (i : Fin 2) : LipschitzWith 8 (squareDiskSideInverse i) := by
  let j : Fin 2 := if i = 0 then 1 else 0
  have hCoord : LipschitzWith 1 (fun x : Plane => x j) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact PiLp.norm_apply_le (x - y) j
  have hCircle : Isometry (fun θ : NativeCircle => θ.val) := Isometry.of_dist_eq fun _ _ => rfl
  have hL := squareSideSingle_isometry.lipschitz.comp
    (hCoord.comp (lipschitz_ballToCoordinateCube_plane.comp hCircle.lipschitz))
  norm_num at hL
  exact hL

private theorem squareDiskSideInverse_angle (i : Fin 2) (p : Bool) {x : Domain 1}
    (hx : x ∈ (unitCellCube 1).val) : squareDiskSideInverse i (squareDiskSideAngle i p x) = x := by
  have hxI : x 0 ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self (mem_iInter.mp hx 0)
  have hS : ballToCoordinateCube (squareDiskSideAngle i p x).val = unitCellFaceSlice i x (if p then 1 else -1) := by
    change ballToCoordinateCube (coordinateCubeToBall (unitSquareSideParameter i p (x 0)).val) = _
    rw [ballToCoordinateCube_coordinateCubeToBall, unitSquareSideParameter_eq i p x hxI]
  unfold squareDiskSideInverse
  rw [hS, unitCellFaceSlice_coordinates]
  apply PiLp.ext
  intro j
  fin_cases i <;> fin_cases j <;> simp

private theorem map_squareDiskSideAngle_le (i : Fin 2) (p : Bool) :
    Measure.map (squareDiskSideAngle i p) (volume.restrict (unitCellCube 1).val) ≤
      (8 : ℝ≥0∞) • unitBoundarySurface 2 := by
  apply Measure.le_iff.2
  intro U hU
  rw [Measure.map_apply (continuous_squareDiskSideAngle i p).measurable hU,
    Measure.restrict_apply (hU.preimage (continuous_squareDiskSideAngle i p).measurable)]
  have hContain : squareDiskSideAngle i p ⁻¹' U ∩ (unitCellCube 1).val ⊆ squareDiskSideInverse i '' U :=
    fun x hx => ⟨squareDiskSideAngle i p x, hx.1, squareDiskSideInverse_angle i p hx.2⟩
  apply (measure_mono hContain).trans
  have hArea := (lipschitz_squareDiskSideInverse i).hausdorffMeasure_image_le (d := 1) (by norm_num) U
  have hDim : Module.finrank ℝ (Domain 1) = 1 := by simp [Domain]
  have hVol : (Measure.euclideanHausdorffMeasure 1 : Measure (Domain 1)) = volume := by
    simpa only [hDim] using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Domain 1))
  rw [← hVol]
  change Measure.euclideanHausdorffMeasure 1 (squareDiskSideInverse i '' U) ≤
    ((8 : ℝ≥0∞) • (Measure.euclideanHausdorffMeasure 1 : Measure NativeCircle)) U
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [mul_left_comm (8 : ℝ≥0∞)]
  apply mul_le_mul_right
  norm_num at hArea ⊢
  exact hArea

private theorem coordinateCubeToBall_pos_smul {r : ℝ} (hr : 0 < r) (x : Plane) :
    coordinateCubeToBall (r • x) = r • coordinateCubeToBall x := by
  unfold coordinateCubeToBall
  rw [coordinateNorm_smul, norm_smul, Real.norm_of_nonneg hr.le, mul_div_mul_left _ _ hr.ne', smul_comm]

private theorem squareDiskSide_raw_radius (i : Fin 2) (p : Bool) {r : ℝ} (hr : 0 < r)
    {x : Domain 1} (hx : |x 0| < r) :
    planarSquareBallHomeomorph (unitCellFaceSlice i x (if p then r else -r)) =
      r • (squareDiskSideAngle i p (r⁻¹ • x)).val := by
  have hxI : (r⁻¹ • x) 0 ∈ Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hr]
    apply ((inv_mul_lt_iff₀ hr).mpr ?_).le
    simpa only [mul_one] using hx
  have hRay : unitCellFaceSlice i x (if p then r else -r) =
      r • unitCellFaceSlice i (r⁻¹ • x) (if p then 1 else -1) := by
    apply PiLp.ext
    intro j
    fin_cases i <;> fin_cases j <;> cases p <;>
      simp [unitCellFaceSlice_coordinates, PiLp.smul_apply, smul_eq_mul, hr.ne']
  change coordinateCubeToBall (unitCellFaceSlice i x (if p then r else -r)) =
    r • coordinateCubeToBall (unitSquareSideParameter i p ((r⁻¹ • x) 0)).val
  rw [hRay, coordinateCubeToBall_pos_smul hr, unitSquareSideParameter_eq i p (r⁻¹ • x) hxI]

private abbrev squareSideVolume : Measure (Domain 1) := volume.restrict (unitCellCube 1).val

private abbrev squareSideL2 := Lp (Ambient 5) 2 squareSideVolume

private theorem exists_centeredSquare_normal_L2_trace {u : Plane → Ambient 5}
    {D : Plane → HarmonicMaps.Gradient 2 5} (hu : MemW12 (unitCellCube 2) u D) (i : Fin 2) :
    ∃ K : C(Icc (-1 : ℝ) 1, squareSideL2), ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ htLp : MemLp (fun x => u (unitCellFaceSlice i x t)) 2 squareSideVolume,
        K ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp _ := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
  let A := cubicalSignedFaceIsometry 1 i true
  let Ω := unitCellCube 2
  have hPre : A ⁻¹' Ω.val = Ω.val := by
    ext x
    have hNorm : ∀ y : Plane, y ∈ Ω.val ↔ ‖WithLp.ofLp y‖ < 1 := by
      intro y
      change y ∈ (unitCellCube 2).val ↔ _
      rw [← planarSquare_one_eq_unitCellCube]
      rfl
    change A x ∈ Ω.val ↔ x ∈ Ω.val
    rw [hNorm, hNorm, cubicalSignedFaceIsometry_coordinate_norm]
  let ΩA : OpenDomain 2 := ⟨A ⁻¹' Ω.val, Ω.property.preimage A.continuous⟩
  have hΩA : ΩA = Ω := Subtype.ext hPre
  let DA (x : Plane) (j : Fin 2) := ∑ k : Fin 2, (A (EuclideanSpace.single j 1)) k • D (A x) k
  have hUA : MemW12 Ω (u ∘ A) DA := by
    rw [← hΩA]
    exact memW12_isometric_preimage (volume_unit_coordinate_face_ne_top 2) hu A
  let R : OpenDomain 2 :=
    ⟨{y | (e y).1 ∈ (unitCellCube 1).val ∧ (e y).2 0 ∈ Ioo (-1 : ℝ) 1},
      ((unitCellCube 1).property.preimage (continuous_fst.comp e.continuous)).inter
        (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          (continuous_snd.comp e.continuous)))⟩
  have hR : R = Ω := by
    apply Subtype.ext
    ext x
    change (e x).1 ∈ (unitCellCube 1).val ∧ (e x).2 0 ∈ Ioo (-1 : ℝ) 1 ↔ x ∈ (unitCellCube 2).val
    constructor
    · rintro ⟨h₀, h₁⟩
      apply mem_iInter.mpr
      intro j
      fin_cases j
      · exact mem_iInter.mp h₀ 0
      · exact h₁
    · intro h
      refine ⟨mem_iInter.mpr (fun j => ?_), mem_iInter.mp h 1⟩
      fin_cases j
      exact mem_iInter.mp h 0
  letI : IsFiniteMeasure squareSideVolume := isFiniteMeasure_restrict.mpr (volume_unit_coordinate_face_ne_top 1)
  have hUR : MemW12 R (u ∘ A) DA := by rwa [hR]
  obtain ⟨K, hK, _⟩ := exists_unique_L2_trace_of_memW12_rectangle (unitCellCube 1)
    (by norm_num : (-1 : ℝ) < 1) hUR
  exact ⟨K, hK⟩

private theorem exists_squareDiskSide_radial_L2_trace (i : Fin 2) (p : Bool)
    {w : Plane → Ambient 5} {s : ℝ} (hs : s < 1) (H : VacuumBallTrace 2 s)
    (hH : RepresentsVacuumBallTrace w H) (b : UnitSquareBoundary → Ambient 5)
    (hEnd : ∃ hb : MemLp (fun θ => b (unitSquareCircleHomeomorph.symm θ)) 2 (unitBoundarySurface 2),
      H ⟨1, hs.le, le_rfl⟩ = hb.toLp _) :
    ∃ P : C(Icc s 1, squareSideL2),
      (∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo s 1,
        ∃ hrLp : MemLp (fun x => w (r • (squareDiskSideAngle i p x).val)) 2 squareSideVolume,
          P ⟨r, hr.1.le, hr.2.le⟩ = hrLp.toLp _) ∧
      ∃ hb : MemLp (fun x => b (unitSquareSideParameter i p (x 0))) 2 squareSideVolume,
        P ⟨1, hs.le, le_rfl⟩ = hb.toLp _ := by
  let ξ := squareDiskSideAngle i p
  let ν := Measure.map ξ squareSideVolume
  let σ := unitBoundarySurface 2
  have hC : (8 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hMap : ν ≤ (8 : ℝ≥0∞) • σ := map_squareDiskSideAngle_le i p
  let L : Lp (Ambient 5) 2 σ →L[ℝ] Lp (Ambient 5) 2 ν := Lp.LpToLpOfMeasureLeSMul hC hMap
  have hMP : MeasurePreserving ξ squareSideVolume ν := ⟨(continuous_squareDiskSideAngle i p).measurable, rfl⟩
  let J : Lp (Ambient 5) 2 ν → squareSideL2 := Lp.compMeasurePreserving ξ hMP
  have hJ : Continuous J := (Lp.isometry_compMeasurePreserving hMP).continuous
  let P : C(Icc s 1, squareSideL2) := ⟨J ∘ L ∘ H, hJ.comp (L.continuous.comp H.continuous)⟩
  have hValue (r : Icc s 1) (g : NativeCircle → Ambient 5) (hg : MemLp g 2 σ)
      (hr : H r = hg.toLp g) : ∃ hq : MemLp (g ∘ ξ) 2 squareSideVolume, P r = hq.toLp _ := by
    have hgν := hg.of_measure_le_smul hC hMap
    have hq := hgν.comp_measurePreserving hMP
    have hG : L (H r) = hgν.toLp g := by
      apply Lp.ext
      have hL := Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) hC hMap (H r)
      have hGr : (H r : NativeCircle → Ambient 5) =ᵐ[σ] g := by rw [hr]; exact hg.coeFn_toLp
      exact hL.trans (((Measure.absolutelyContinuous_of_le_smul hMap).ae_eq hGr).trans hgν.coeFn_toLp.symm)
    refine ⟨hq, ?_⟩
    change J (L (H r)) = _
    rw [hG]
    exact Lp.toLp_compMeasurePreserving hgν hMP
  refine ⟨P, ?_, ?_⟩
  · filter_upwards [hH] with r hr hrI
    obtain ⟨hrLp, hClass⟩ := hr hrI
    exact hValue ⟨r, hrI.1.le, hrI.2.le⟩ _ hrLp hClass
  · obtain ⟨hb, hB⟩ := hEnd
    obtain ⟨hLp, hClass⟩ := hValue ⟨1, hs.le, le_rfl⟩ _ hb hB
    have hEq : (fun θ => b (unitSquareCircleHomeomorph.symm θ)) ∘ ξ =
        fun x => b (unitSquareSideParameter i p (x 0)) := by
      funext x
      simp [ξ, squareDiskSideAngle]
    have hAE := Eventually.of_forall (congrFun hEq) (f := ae squareSideVolume)
    let hLp' := hLp.ae_eq hAE
    exact ⟨hLp', hClass.trans (MemLp.toLp_congr hLp hLp' hAE)⟩

private def signedSquareHeight (p : Bool) (t : Icc (-1 : ℝ) 1) : Icc (-1 : ℝ) 1 :=
  ⟨if p then t.val else -t.val, by
    cases p
    · change (-1 : ℝ) ≤ -t.val ∧ -t.val ≤ 1
      exact ⟨by linarith only [t.property.2], by linarith only [t.property.1]⟩
    · exact t.property⟩

private theorem continuous_signedSquareHeight (p : Bool) : Continuous (signedSquareHeight p) := by
  cases p
  · exact continuous_subtype_val.neg.subtype_mk _
  · exact continuous_id

private theorem signed_squareSide_raw_trace {u : Plane → Ambient 5} (i : Fin 2) (p : Bool)
    (K : C(Icc (-1 : ℝ) 1, squareSideL2))
    (hK : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ htLp : MemLp (fun x => u (unitCellFaceSlice i x t)) 2 squareSideVolume,
        K ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp _) :
    ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ htLp : MemLp (fun x => u (unitCellFaceSlice i x (if p then t else -t))) 2 squareSideVolume,
        K (signedSquareHeight p ⟨t, ht.1.le, ht.2.le⟩) = htLp.toLp _ := by
  cases p
  · have hNeg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hK
    filter_upwards [hNeg] with t ht htI
    exact ht ⟨by linarith only [htI.2], by linarith only [htI.1]⟩
  · exact hK

private theorem squareDiskSide_endpoint_eq_on_subface (i : Fin 2) (p : Bool) (w : Plane → Ambient 5)
    (K : C(Icc (-1 : ℝ) 1, squareSideL2))
    (hK : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ htLp : MemLp (fun x => w (planarSquareBallHomeomorph (unitCellFaceSlice i x t))) 2 squareSideVolume,
        K ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp _)
    {s : ℝ} (hs : s < 1) (P : C(Icc s 1, squareSideL2))
    (hP : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo s 1,
      ∃ hLp : MemLp (fun x => w (r • (squareDiskSideAngle i p x).val)) 2 squareSideVolume,
        P ⟨r, hr.1.le, hr.2.le⟩ = hLp.toLp _)
    {g : Domain 1 → Ambient 5} (hg : MemLp g 2 squareSideVolume)
    (hEnd : P ⟨1, hs.le, le_rfl⟩ = hg.toLp g) {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ < 1) :
    (K (signedSquareHeight p ⟨1, by norm_num, le_rfl⟩) : Domain 1 → Ambient 5) =ᵐ[
      volume.restrict {x : Domain 1 | ‖WithLp.ofLp x‖ < ρ}] g := by
  let S := (unitCellCube 1).val
  let A := {x : Domain 1 | ‖WithLp.ofLp x‖ < ρ}
  let μ := (volume : Measure (Domain 1)).restrict A
  let a := max s ρ
  have ha₀ : 0 < a := hρ.trans_le (le_max_right _ _)
  have ha₁ : a < 1 := max_lt hs hρ₁
  have hsa : s ≤ a := le_max_left _ _
  have hab : (-1 : ℝ) ≤ a := (by norm_num : (-1 : ℝ) < 0).le.trans ha₀.le
  have hS : MeasurableSet S := (unitCellCube 1).property.measurableSet
  have hA : MeasurableSet A := (isOpen_lt ((PiLp.continuous_ofLp 2 (fun _ : Fin 1 => ℝ)).norm)
    continuous_const).measurableSet
  have hSmall (x : Domain 1) (hx : x ∈ A) : |x 0| < ρ :=
    (show |x 0| ≤ ‖WithLp.ofLp x‖ from norm_le_pi_norm (WithLp.ofLp x) 0).trans_lt hx
  have hInto : ∀ (r : Icc a 1), ∀ x ∈ A, r.val⁻¹ • x ∈ S := by
    intro r x hx
    have hr₀ : 0 < r.val := ha₀.trans_le r.property.1
    apply mem_iInter.mpr
    intro j
    fin_cases j
    change -1 < (r.val⁻¹ • x) 0 ∧ (r.val⁻¹ • x) 0 < 1
    apply abs_lt.mp
    rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hr₀]
    apply (inv_mul_lt_iff₀ hr₀).2
    simpa only [mul_one] using (hSmall x hx).trans_le ((le_max_right s ρ).trans r.property.1)
  have hAS : A ⊆ S := by
    intro x hx
    simpa only [inv_one, one_smul] using hInto ⟨1, ha₁.le, le_rfl⟩ x hx
  have hμ : μ ≤ squareSideVolume := Measure.restrict_mono_set volume hAS
  let L : squareSideL2 →L[ℝ] Lp (Ambient 5) 2 μ :=
    Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by norm_num) (by simpa only [one_smul] using hμ)
  let τ (r : Icc a 1) : Icc s 1 := ⟨r.val, hsa.trans r.property.1, r.property.2⟩
  let j (r : Icc a 1) : Icc (-1 : ℝ) 1 := ⟨r.val, hab.trans r.property.1, r.property.2⟩
  let Q : C(Icc a 1, squareSideL2) := ⟨P ∘ τ, P.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  let B : C(Icc a 1, Lp (Ambient 5) 2 μ) :=
    ⟨fun r => L (K (signedSquareHeight p (j r))), L.continuous.comp (K.continuous.comp
      ((continuous_signedSquareHeight p).comp (continuous_subtype_val.subtype_mk _)))⟩
  obtain ⟨J, hJ⟩ := exists_continuous_varying_inverseDilation_L2 hS hA ha₀ Q hInto
  let f (z : Domain 1 × ℝ) := w (planarSquareBallHomeomorph (unitCellFaceSlice i z.1 (if p then z.2 else -z.2)))
  let q (z : Domain 1 × ℝ) := if hz : z.2 ∈ Icc a 1 then Q ⟨z.2, hz⟩ (z.2⁻¹ • z.1) else 0
  have hK' := signed_squareSide_raw_trace (u := w ∘ planarSquareBallHomeomorph) i p K hK
  have hB : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo a 1,
      ∃ hLp : MemLp (fun x => f (x, r)) 2 μ, B ⟨r, hr.1.le, hr.2.le⟩ = hLp.toLp _ := by
    filter_upwards [hK'] with r hr hrA
    obtain ⟨hLp, hRaw⟩ := hr ⟨hab.trans_lt hrA.1, hrA.2⟩
    let hSmall := hLp.mono_measure hμ
    refine ⟨hSmall, ?_⟩
    change L (K (signedSquareHeight p ⟨r, (hab.trans_lt hrA.1).le, hrA.2.le⟩)) = hSmall.toLp _
    rw [hRaw]
    exact lp_two_measure_restriction_toLp hμ _ hLp hSmall
  have hJ' : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo a 1,
      ∃ hLp : MemLp (fun x => q (x, r)) 2 μ, J ⟨r, hr.1.le, hr.2.le⟩ = hLp.toLp _ := by
    refine Eventually.of_forall fun r hr => ?_
    have hEq : (fun x => q (x, r)) = fun x => Q ⟨r, hr.1.le, hr.2.le⟩ (r⁻¹ • x) := by
      funext x
      simp only [q, dif_pos (Ioo_subset_Icc_self hr)]
    rw [hEq]
    exact hJ ⟨r, hr.1.le, hr.2.le⟩
  have hCoincide : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo a 1,
      (fun x => f (x, r)) =ᵐ[μ] fun x => q (x, r) := by
    filter_upwards [hP] with r hrP hr
    let r' : Icc a 1 := ⟨r, hr.1.le, hr.2.le⟩
    obtain ⟨hLp, hRaw⟩ := hrP ⟨hsa.trans_lt hr.1, hr.2⟩
    have hOriginal : ∀ᵐ x ∂squareSideVolume, Q r' x = w (r • (squareDiskSideAngle i p x).val) := by
      change (P ⟨r, (hsa.trans_lt hr.1).le, hr.2.le⟩ : Domain 1 → Ambient 5) =ᵐ[squareSideVolume] _
      rw [hRaw]
      exact hLp.coeFn_toLp
    have hDilated := ae_inverse_dilation_property_on_subset hS hA
      (fun x => (Q r' x, w (r • (squareDiskSideAngle i p x).val)))
      (fun z : Ambient 5 × Ambient 5 => z.1 = z.2) (t := r) (ha₀.trans hr.1).ne' (hInto r') hOriginal
    filter_upwards [hDilated, ae_restrict_mem hA] with x hx hxA
    have hxAbs : |x 0| < r := (hSmall x hxA).trans_le ((le_max_right s ρ).trans hr.1.le)
    change w (planarSquareBallHomeomorph (unitCellFaceSlice i x (if p then r else -r))) = q (x, r)
    rw [squareDiskSide_raw_radius i p (ha₀.trans hr.1) hxAbs]
    simpa only [q, dif_pos (Ioo_subset_Icc_self hr)] using hx.symm
  have hBJ : B = J := continuous_Lp_representatives_eq_of_ae_slices ha₁ B J hB hJ' hCoincide
  let t₁ : Icc a 1 := ⟨1, ha₁.le, le_rfl⟩
  let k := K (signedSquareHeight p ⟨1, by norm_num, le_rfl⟩)
  have hBoundary : L k = J t₁ := congrArg (fun C : C(Icc a 1, Lp (Ambient 5) 2 μ) => C t₁) hBJ
  obtain ⟨hLp, hJL⟩ := hJ t₁
  have hL := Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) (c := (1 : ℝ≥0∞))
    (by norm_num) (by simpa only [one_smul] using hμ) k
  change L k =ᵐ[μ] k at hL
  rw [hBoundary, hJL] at hL
  have hP₁ : (P ⟨1, hs.le, le_rfl⟩ : Domain 1 → Ambient 5) =ᵐ[μ] g := by
    rw [hEnd]
    exact hg.coeFn_toLp.filter_mono (ae_mono hμ)
  have hJ₁ : (hLp.toLp _ : Domain 1 → Ambient 5) =ᵐ[μ] P ⟨1, hs.le, le_rfl⟩ := by
    simpa only [t₁, Q, τ, Function.comp_apply, inv_one, one_smul,
      ContinuousMap.coe_mk] using hLp.coeFn_toLp
  exact hL.symm.trans (hJ₁.trans hP₁)

/-- The disk graph and its actual radial endpoint class pull back to the
same centered-square graph with all four original coordinate trace classes. -/
theorem unitSquareDiskSobolevPullback : External.UnitSquareDiskSobolevPullback := by
  refine ⟨1152, by norm_num, ?_⟩
  intro w Dw hw b s hs H hH hEnd
  obtain ⟨G, hG, hEnergy⟩ := exists_unitSquare_memW12_disk_pullback w Dw hw
  have hNormal (i : Fin 2) := exists_centeredSquare_normal_L2_trace hG i
  choose K hK using hNormal
  refine ⟨G, hG, ⟨⟨K, hK, ?_⟩⟩, hEnergy⟩
  intro i p
  obtain ⟨P, hP, hb, hP₁⟩ := exists_squareDiskSide_radial_L2_trace i p hs H hH b hEnd
  have hFull : (K i (signedSquareHeight p ⟨1, by norm_num, le_rfl⟩) : Domain 1 → Ambient 5) =ᵐ[squareSideVolume]
      fun x => b (unitSquareSideParameter i p (x 0)) := by
    apply ae_eq_unit_cube_of_smaller_cubes
    exact fun ρ hρ hρ₁ => squareDiskSide_endpoint_eq_on_subface i p w (K i) (hK i) hs P hP hb hP₁ hρ hρ₁
  exact hFull

end Thesis

end
