module

public import Thesis.Interpolation.SphericalShellCapTrace
import StratificationTheory.Foundation.SpatialConstantRectangle
import StratificationTheory.Foundation.CoordinatePiecewiseSobolevData
import StratificationTheory.Foundation.SphereAEClasses
import StratificationTheory.Foundation.AffineDomainSobolevPullback
import StratificationTheory.Foundation.PositiveCubeSobolevDenormalization
import StratificationTheory.Frozen.SphereRadialBallExtension
import HarmonicMaps.Analysis.SobolevAECongruence
import Thesis.Foundation.VacuumTarget

/-! Global surface Sobolev data from the actual projected inner face collars. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

variable {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}
variable {G : PenalizedSphereFaces a B h v hv}

/-- The physical inner face has an actual continuous collar at each open
side, taking the selected projected edge value there. -/
@[expose] def HasContinuousProjectedFaceCollar {f : ShellCellIndex G.grid.level} (I : ProjectedCellInnerFace G f) : Prop :=
  ∀ (i : Fin 2) (upper : Bool) {t : ℝ}, t ∈ Ioo (0 : ℝ) h →
    let x := shellSquareSideParameters i (if upper then h else 0) t
    let p : Domain 2 := WithLp.toLp 2 ![x.1, x.2]
    I.field p = frobeniusCoordinateEquiv (G.grid.projectedEdge (tensorSquareCoordinateEdge f i upper) t) ∧
      ∃ N : Set (Domain 2), IsOpen N ∧ p ∈ N ∧ ContinuousOn I.field (N ∩ sphericalFaceParameterBox h)

/-- A signed endpoint of the normalized square becomes the same actual
physical edge endpoint and free affine parameter. -/
theorem unitToPhysicalCellFace_signed_edge (h : ℝ) (i : Fin 2) (upper : Bool) (x : Domain 1) :
    let p := shellSquareSideParameters i (if upper then h else 0) (unitEdgeToPhysical h x)
    unitToPhysicalCellFace h (unitCellFaceSlice i x (if upper then 1 else -1)) = WithLp.toLp 2 ![p.1, p.2] := by
  intro p
  apply PiLp.ext
  intro j
  fin_cases i <;> fin_cases j <;> cases upper <;>
    simp [p, unitToPhysicalCellFace, unitCellFaceSlice_coordinates, shellSquareSideParameters,
      unitEdgeToPhysical, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- A collar supplied on a common open neighborhood of the normalized
signed edges gives the same actual local physical collar. -/
theorem HasContinuousProjectedFaceCollar.of_normalized_edges {f : ShellCellIndex G.grid.level}
    (I : ProjectedCellInnerFace G f) (N : Set (Domain 2)) (hN : IsOpen N) (hCont : ContinuousOn I.field N)
    (hMem : ∀ (i : Fin 2) (upper : Bool) (x : Domain 1), x 0 ∈ Icc (-1 : ℝ) 1 →
      unitToPhysicalCellFace h (unitCellFaceSlice i x (if upper then 1 else -1)) ∈ N)
    (hValue : ∀ (i : Fin 2) (upper : Bool) (x : Domain 1), x 0 ∈ Icc (-1 : ℝ) 1 →
      I.field (unitToPhysicalCellFace h (unitCellFaceSlice i x (if upper then 1 else -1))) =
        frobeniusCoordinateEquiv (G.grid.projectedEdge (tensorSquareCoordinateEdge f i upper) (unitEdgeToPhysical h x))) :
    HasContinuousProjectedFaceCollar I := by
  intro i upper t ht p z
  let x : Domain 1 := WithLp.toLp 2 (fun _ => (t - h / 2) / (h / 2))
  have hPos := half_pos G.ht_pos
  have hx : x 0 ∈ Icc (-1 : ℝ) 1 := by
    change (t - h / 2) / (h / 2) ∈ Icc (-1 : ℝ) 1
    exact ⟨(le_div_iff₀ hPos).mpr (by linarith only [ht.1]), (div_le_iff₀ hPos).mpr (by linarith only [ht.2])⟩
  have ht' : unitEdgeToPhysical h x = t := by
    change h / 2 + (h / 2) * ((t - h / 2) / (h / 2)) = t
    rw [mul_comm (h / 2), div_mul_cancel₀ _ hPos.ne']
    ring
  have hPoint : unitToPhysicalCellFace h (unitCellFaceSlice i x (if upper then 1 else -1)) = z := by
    rw [unitToPhysicalCellFace_signed_edge]
    change (WithLp.toLp 2 ![(shellSquareSideParameters i (if upper then h else 0) (unitEdgeToPhysical h x)).1,
      (shellSquareSideParameters i (if upper then h else 0) (unitEdgeToPhysical h x)).2] : Domain 2) = z
    rw [ht']
  have he := hValue i upper x hx
  rw [hPoint, ht'] at he
  have hZ := hMem i upper x hx
  rw [hPoint] at hZ
  exact ⟨he, N, hN, hZ, hCont.mono inter_subset_left⟩

private theorem sphericalCellNativeOpenDomain_eq_slab (h : ℝ) :
    sphericalCellNativeOpenDomain h = cellInterfaceSlab (tensorGridOpenParameterBox 2 h) (1 - h) 1 := by
  apply Subtype.ext
  rw [sphericalCellNativeOpenDomain_coord_eq]
  ext x
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  have h₀ : shellCellParameterLower h 0 = 0 := rfl
  have h₁ : shellCellParameterLower h 1 = 0 := rfl
  have h₂ : shellCellParameterLower h 2 = 1 - h := rfl
  have hTop : 1 - h + h = 1 := by ring
  constructor
  · intro hx
    change (e x).1 ∈ (tensorGridOpenParameterBox 2 h).val ∧ (e x).2 0 ∈ Ioo (1 - h) 1
    refine ⟨mem_iInter.mpr ?_, ?_⟩
    · intro i
      fin_cases i
      · have hx₀ := mem_iInter.mp hx (0 : Fin 3)
        change x 0 ∈ Ioo (shellCellParameterLower h 0) (shellCellParameterLower h 0 + h) at hx₀
        change x 0 ∈ Ioo (0 : ℝ) h
        simpa only [h₀, zero_add] using hx₀
      · have hx₁ := mem_iInter.mp hx (1 : Fin 3)
        change x 1 ∈ Ioo (shellCellParameterLower h 1) (shellCellParameterLower h 1 + h) at hx₁
        change x 1 ∈ Ioo (0 : ℝ) h
        simpa only [h₁, zero_add] using hx₁
    · have hx₂ := mem_iInter.mp hx (2 : Fin 3)
      change x 2 ∈ Ioo (shellCellParameterLower h 2) (shellCellParameterLower h 2 + h) at hx₂
      change x 2 ∈ Ioo (1 - h) 1
      simpa only [h₂, hTop] using hx₂
  · intro hx
    change (e x).1 ∈ (tensorGridOpenParameterBox 2 h).val ∧ (e x).2 0 ∈ Ioo (1 - h) 1 at hx
    apply mem_iInter.mpr
    intro i
    fin_cases i
    · change x 0 ∈ Ioo (shellCellParameterLower h 0) (shellCellParameterLower h 0 + h)
      have hx₀ : x 0 ∈ Ioo (0 : ℝ) h := mem_iInter.mp hx.1 0
      simpa only [h₀, zero_add] using hx₀
    · change x 1 ∈ Ioo (shellCellParameterLower h 1) (shellCellParameterLower h 1 + h)
      have hx₁ : x 1 ∈ Ioo (0 : ℝ) h := mem_iInter.mp hx.1 1
      simpa only [h₁, zero_add] using hx₁
    · change x 2 ∈ Ioo (shellCellParameterLower h 2) (shellCellParameterLower h 2 + h)
      have hx₂ : x 2 ∈ Ioo (1 - h) 1 := hx.2
      simpa only [h₂, hTop] using hx₂

private theorem nativeCellParameter_fst_map (h : ℝ) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    Measure.map (fun z : Point => (e z).1) (volume.restrict (sphericalCellNativeOpenDomain h).val) =
      ENNReal.ofReal h • (volume : Measure (Domain 2)).restrict (tensorGridOpenParameterBox 2 h).val := by
  intro e
  let U := tensorGridOpenParameterBox 2 h
  let Φ : Domain 2 × ℝ → Point := fun p => cellInterfacePoint p.1 p.2
  let P : Point → Domain 2 := fun x => (e x).1
  have hMP := StratificationTheory.measurePreserving_inverse_native_rectangle U.property.measurableSet
    (measurableSet_Ioo (a := 1 - h) (b := (1 : ℝ)))
  have hSlab : MeasurePreserving Φ ((volume.restrict U.val).prod (volume.restrict (Ioo (1 - h) 1)))
      (volume.restrict (cellInterfaceSlab U (1 - h) 1).val) := hMP
  have hMeas : Measurable P := (continuous_fst.comp e.continuous).measurable
  have hComp : P ∘ Φ = Prod.fst := by
    funext x
    change (e (e.symm (x.1, EuclideanSpace.single 0 x.2))).1 = x.1
    rw [e.apply_symm_apply]
  change Measure.map P (volume.restrict (sphericalCellNativeOpenDomain h).val) = _
  rw [sphericalCellNativeOpenDomain_eq_slab, ← hSlab.map_eq, Measure.map_map hMeas hSlab.measurable,
    hComp, Measure.map_fst_prod, Measure.restrict_apply_univ, Real.volume_Ioo,
    show (1 : ℝ) - (1 - h) = h by ring]

private theorem nativeCellParameter_constant_extension {q : ℕ} {h : ℝ}
    {u : Domain 2 → Ambient q} {D : Domain 2 → HarmonicMaps.Gradient 2 q}
    (hW : MemW12 (tensorGridOpenParameterBox 2 h) u D) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let P : Point → Domain 2 := fun z => (e z).1
    let W := u ∘ P
    let DW : Point → HarmonicMaps.Gradient 3 q := fun z i => Fin.lastCases (0 : Ambient q) (fun k => D (P z) k) i
    MemW12 (sphericalCellNativeOpenDomain h) W DW ∧
      HarmonicMaps.dirichletEnergy DW (sphericalCellNativeOpenDomain h).val =
        ENNReal.ofReal h * HarmonicMaps.dirichletEnergy D (tensorGridOpenParameterBox 2 h).val ∧
      ∀ Q : Ambient q → Prop, (∀ᵐ y ∂volume.restrict (tensorGridOpenParameterBox 2 h).val, Q (u y)) →
        ∀ᵐ z ∂volume.restrict (sphericalCellNativeOpenDomain h).val, Q (W z) := by
  intro e P W DW
  let U := tensorGridOpenParameterBox 2 h
  let V := sphericalCellNativeOpenDomain h
  have hw : MemW12 (cellInterfaceSlab U (1 - h) 1) W DW :=
    StratificationTheory.memW12_spatial_constant_rectangle U u D hW (1 - h) 1
  rw [← sphericalCellNativeOpenDomain_eq_slab] at hw
  have hMap : Measure.map P (volume.restrict V.val) = ENNReal.ofReal h • volume.restrict U.val :=
    nativeCellParameter_fst_map h
  have hp : Measurable P := (continuous_fst.comp e.continuous).measurable
  have hQ : Measure.QuasiMeasurePreserving P (volume.restrict V.val) (volume.restrict U.val) :=
    ⟨hp, Measure.absolutelyContinuous_of_le_smul hMap.le⟩
  refine ⟨hw, ?_, fun Q hQae => hQ.ae hQae⟩
  have hPoint (z : Point) : hsNormSq (DW z) = hsNormSq (D (P z)) := by
    simp only [hsNormSq, Fin.sum_univ_castSucc, DW, Fin.lastCases_castSucc, Fin.lastCases_last,
      norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  let E := fun x => ENNReal.ofReal (hsNormSq (D x))
  have hE : AEMeasurable E (volume.restrict U.val) := hW.integrable_hsNormSq.aemeasurable.ennreal_ofReal
  have hEP : AEMeasurable E (Measure.map P (volume.restrict V.val)) := hE.mono_ac hQ.absolutelyContinuous
  unfold HarmonicMaps.dirichletEnergy
  simp_rw [hPoint]
  change (∫⁻ z, E (P z) ∂volume.restrict V.val) = _
  rw [← lintegral_map' hEP hp.aemeasurable, hMap, lintegral_smul_measure, smul_eq_mul]

/-- The constant radial extension of one original physical inner face. -/
structure ProjectedInnerFaceExtrusion {f : ShellCellIndex G.grid.level} (I : ProjectedCellInnerFace G f) where
  parameter : Point → Domain 2
  derivative : Point → HarmonicMaps.Gradient 3 5
  parameter_continuous : ContinuousOn parameter (sphericalClosedCell G.grid.center h f.val)
  parameter_in_box : MapsTo parameter (sphericalClosedCell G.grid.center h f.val) (sphericalFaceParameterBox h)
  parameter_eq : ∀ p ∈ sphericalCellParameterBox h,
    parameter (sphericalCellPoint G.grid.center h f.val p) = WithLp.toLp 2 ![p.1.1, p.1.2]
  memW12 : MemW12 (sphericalCellOpenDomain G.grid.center h f.val) (I.field ∘ parameter) derivative
  bound : ∀ᵐ x ∂volume.restrict (sphericalCellOpenDomain G.grid.center h f.val).val,
    ‖I.field (parameter x)‖ ≤ Real.sqrt 2 * vacuumRadius a
  dirichlet_bound : HarmonicMaps.dirichletEnergy derivative (sphericalCellOpenDomain G.grid.center h f.val).val ≤
    (9 * 204 ^ 2 * 65 ^ 3 : ℝ≥0∞) * ENNReal.ofReal h * HarmonicMaps.dirichletEnergy I.derivative (tensorGridOpenParameterBox 2 h).val

/-- Constant radial extension retains the actual inner weak face graph and
has exactly one factor of the shell thickness before chart distortion. -/
theorem exists_projectedInnerFaceExtrusion {f : ShellCellIndex G.grid.level} (I : ProjectedCellInnerFace G f)
    (hSmall : h ≤ 1 / 32) : Nonempty (ProjectedInnerFaceExtrusion I) := by
  let c := G.grid.center
  let U := sphericalCellNativeOpenDomain h
  let V := sphericalCellOpenDomain c h f.val
  let C := sphericalClosedCell c h f.val
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let P : Point → Domain 2 := fun z => (e z).1
  let W := I.field ∘ P
  let DW : Point → HarmonicMaps.Gradient 3 5 := fun z i => Fin.lastCases (0 : Ambient 5) (fun k => I.derivative (P z) k) i
  have hh := G.ht_pos
  have hh' : h ≤ 1 / 2 := hSmall.trans (by norm_num)
  have hc (i : Fin 3) : c i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(G.grid.offset_mem i).1, (G.grid.offset_mem i).2.le.trans hSmall⟩
  obtain ⟨hW, hDirP, hV⟩ := nativeCellParameter_constant_extension I.memW12
  obtain ⟨g, _, hMaps, hLeft, _, hSmooth, hDF, hMap⟩ := exists_sphericalCellNativeInverse hh hh' hc G.grid.radius_mem f.property
  let Y := P ∘ g
  let D : Point → HarmonicMaps.Gradient 3 5 := fun z i =>
    ∑ j : Fin 3, (fderiv ℝ g z (EuclideanSpace.single i 1)) j • DW (g z) j
  have hG : ContDiffOn ℝ ∞ g V.val := hSmooth.mono interior_subset
  obtain ⟨hWeak, _, hEnergy, hVal⟩ := StratificationTheory.memW12_smooth_open_domain_pullback_energy
    hW V g hG hMaps 204 hDF (65 ^ 3) (by norm_num) hMap
  have hY (p : SphericalCellParameter) (hp : p ∈ sphericalCellParameterBox h) :
      Y (sphericalCellPoint c h f.val p) = WithLp.toLp 2 ![p.1.1, p.1.2] := by
    let z := sphericalCellNativeParameter.symm p
    have hz' : sphericalCellNativeParameter z = p := sphericalCellNativeParameter.apply_symm_apply _
    have hz : z ∈ sphericalCellNativeBox h := by
      change sphericalCellNativeParameter z ∈ sphericalCellParameterBox h
      rwa [hz']
    have hPoint : sphericalCellNativePoint c h f.val z = sphericalCellPoint c h f.val p := by
      change sphericalCellPoint c h f.val (sphericalCellNativeParameter z) = _
      rw [hz']
    rw [← hPoint]
    change P (g (sphericalCellNativePoint c h f.val z)) = _
    rw [hLeft hz]
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  refine ⟨{ parameter := Y
            derivative := D
            parameter_continuous := (continuous_fst.comp e.continuous).comp_continuousOn hSmooth.continuousOn
            parameter_in_box := ?_
            parameter_eq := hY
            memW12 := hWeak
            bound := ?_
            dirichlet_bound := ?_ }⟩
  · rintro z ⟨p, hp, rfl⟩
    rw [hY p hp]
    exact ⟨hp.1.1, hp.1.2⟩
  · have hInner : ∀ᵐ x ∂volume.restrict (tensorGridOpenParameterBox 2 h).val,
        ‖I.field x‖ ≤ Real.sqrt 2 * vacuumRadius a := by
      filter_upwards [I.vacuum_ae] with x hx
      rw [← frobeniusCoordinateEquiv.symm.norm_map (I.field x), vacuum_norm hx]
    exact hVal (fun y => ‖y‖ ≤ Real.sqrt 2 * vacuumRadius a) (hV (fun y => ‖y‖ ≤ Real.sqrt 2 * vacuumRadius a) hInner)
  · have hCoeff : ENNReal.ofReal ((↑(3 : ℕ) : ℝ) * ↑(3 : ℕ) * 204 ^ 2) = (9 * 204 ^ 2 : ℝ≥0∞) := by norm_num
    rw [hCoeff, hDirP] at hEnergy
    simpa only [mul_assoc] using hEnergy

/-- The extruded side values are constant in the physical radius and are
the same actual projected edge values on both incident cells. -/
theorem ProjectedInnerFaceExtrusion.open_side {f : ShellCellIndex G.grid.level} {I : ProjectedCellInnerFace G f}
    (E : ProjectedInnerFaceExtrusion I) (H : HasContinuousProjectedFaceCollar I)
    (i : Fin 2) (upper : Bool) {t r : ℝ} (ht : t ∈ Ioo (0 : ℝ) h) (hr : r ∈ Ioo (1 - h) 1) :
    let y := sphericalLateralEdge G.grid.center h (tensorSquareCoordinateEdge f i upper).val (t, r)
    I.field (E.parameter y) = frobeniusCoordinateEquiv (G.grid.projectedEdge (tensorSquareCoordinateEdge f i upper) t) ∧
      ∃ N : Set Point, IsOpen N ∧ y ∈ N ∧ ContinuousOn (I.field ∘ E.parameter) (N ∩ sphericalClosedCell G.grid.center h f.val) := by
  intro y
  let s := shellSquareSideParameters i (if upper then h else 0) t
  let p := (s, r)
  let C := sphericalClosedCell G.grid.center h f.val
  have ht' := Ioo_subset_Icc_self ht
  have hd : (if upper then h else 0) ∈ Icc (0 : ℝ) h := by cases upper <;> simp [G.ht_pos.le]
  have hs : s ∈ Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) h := by
    by_cases hi : i = 0
    · rw [show s = (if upper then h else 0, t) by simp [s, shellSquareSideParameters, hi]]
      exact ⟨hd, ht'⟩
    · rw [show s = (t, if upper then h else 0) by simp [s, shellSquareSideParameters, hi]]
      exact ⟨ht', hd⟩
  have hp : p ∈ sphericalCellParameterBox h := ⟨hs, Ioo_subset_Icc_self hr⟩
  have hPoint : sphericalCellPoint G.grid.center h f.val p = y := shellSquareSide_point_on_edge G.grid.center h f i upper t r
  have hy : y ∈ C := ⟨p, hp, hPoint⟩
  have hj : E.parameter y = (WithLp.toLp 2 ![s.1, s.2] : Domain 2) := by
    rw [← hPoint, E.parameter_eq p hp]
  obtain ⟨hv, N, hN, hMem, hCont⟩ := H i upper ht
  refine ⟨(congrArg I.field hj).trans hv, ?_⟩
  · have hP : E.parameter y ∈ N := by rwa [hj]
    have hN' : E.parameter ⁻¹' N ∈ 𝓝[C] y := (E.parameter_continuous y hy) (hN.mem_nhds hP)
    obtain ⟨M, hM, hyM, hSub⟩ := mem_nhdsWithin.mp hN'
    exact ⟨M, hM, hyM, hCont.comp (E.parameter_continuous.mono inter_subset_right)
      (fun z hz => ⟨hSub hz, E.parameter_in_box hz.2⟩)⟩

private theorem radial_mem_cell_iff_angularPatch {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32)) (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    (f : ShellCellIndex m) (θ : UnitTensorSphere) {r : ℝ} (hr : r ∈ Ioo (1 - h) 1) :
    r • θ.val ∈ (sphericalCellOpenDomain c h f.val).val ↔ θ ∈ shellAngularSpherePatch c h f.val := by
  change r • θ.val ∈ interior (sphericalClosedCell c h f.val) ↔ θ.val ∈ shellAngularPatch c h f.val
  rw [sphericalClosedCell_interior hh' hc hm f.property]
  constructor
  · rintro ⟨p, hp, hEq⟩
    let z : Domain 2 := WithLp.toLp 2 ![p.1.1, p.1.2]
    let x : Domain 2 := (h / 2)⁻¹ • (z - WithLp.toLp 2 (fun _ => h / 2))
    have hZ : z ∈ (tensorGridOpenParameterBox 2 h).val := by
      apply mem_iInter.mpr
      intro i
      fin_cases i
      · exact hp.1.1
      · exact hp.1.2
    have hx : x ∈ (unitCellCube 2).val := by
      have hPre : (fun z : Domain 2 => (h / 2)⁻¹ • (z - WithLp.toLp 2 (fun _ => h / 2))) ⁻¹'
          (unitCellCube 2).val = (tensorGridOpenParameterBox 2 h).val :=
        StratificationTheory.inverse_unit_cube_preimage_unit_cube 2 hh
      have hz' := hZ
      rwa [← hPre] at hz'
    have hRaw : unitToPhysicalCellFace h x = z := unitToPhysicalCellFace_inverse hh z
    have hp' : p.1 ∈ Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) h :=
      ⟨Ioo_subset_Icc_self hp.1.1, Ioo_subset_Icc_self hp.1.2⟩
    have hNorm : ‖sphericalFacePoint c h f.val p.1‖ = 1 :=
      mem_sphere_zero_iff_norm.mp (sphericalFacePoint_dist_bounds hh hc hm f.property hp' hp').1
    have hPos : 0 < p.2 := by linarith only [hp.2.1, hh']
    have hr₀ : 0 < r := by linarith only [hr.1, hh']
    have hTheta : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
    have hAngle := congrArg NormedSpace.normalize hEq
    change NormedSpace.normalize (p.2 • sphericalFacePoint c h f.val p.1) = NormedSpace.normalize (r • θ.val) at hAngle
    rw [NormedSpace.normalize_smul_of_pos hPos, NormedSpace.normalize_smul_of_pos hr₀,
      NormedSpace.normalize_eq_self_of_norm_eq_one hNorm, NormedSpace.normalize_eq_self_of_norm_eq_one hTheta] at hAngle
    refine ⟨x, hx, ?_⟩
    change sphericalFaceParameterPoint c h f.val (unitToPhysicalCellFace h x) = θ.val
    rw [hRaw]
    exact hAngle
  · rintro ⟨x, hx, hEq⟩
    let z := unitToPhysicalCellFace h x
    have hz := unitToPhysicalCellFace_open_box hh hx
    refine ⟨((z 0, z 1), r), ⟨⟨mem_iInter.mp hz 0, mem_iInter.mp hz 1⟩, hr⟩, ?_⟩
    change r • shellCapAngularPoint c h f.val x = _
    rw [hEq]

private theorem ProjectedInnerFaceExtrusion.parameter_on_ray {f : ShellCellIndex G.grid.level}
    {I : ProjectedCellInnerFace G f} (E : ProjectedInnerFaceExtrusion I) (A : ShellAngularInverse G.grid.center h f.val)
    {θ : UnitTensorSphere} (hθ : θ ∈ shellAngularSpherePatch G.grid.center h f.val) {r : ℝ} (hr : r ∈ Ioo (1 - h) 1) :
    E.parameter (r • θ.val) = unitToPhysicalCellFace h (A.inverse θ.val) := by
  let x := A.inverse θ.val
  let z := unitToPhysicalCellFace h x
  have hx : x ∈ (unitCellCube 2).val := A.inverse_mem θ.val hθ
  have hz : z ∈ (tensorGridOpenParameterBox 2 h).val := unitToPhysicalCellFace_open_box G.ht_pos hx
  let p : SphericalCellParameter := ((z 0, z 1), r)
  have hp : p ∈ sphericalCellParameterBox h :=
    ⟨⟨Ioo_subset_Icc_self (mem_iInter.mp hz 0), Ioo_subset_Icc_self (mem_iInter.mp hz 1)⟩, Ioo_subset_Icc_self hr⟩
  have hPoint : sphericalCellPoint G.grid.center h f.val p = r • θ.val := by
    change r • shellCapAngularPoint G.grid.center h f.val x = r • θ.val
    rw [A.right_inv θ.val hθ]
  rw [← hPoint, E.parameter_eq p hp]
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

/-- The exact angular inner cap and its constant radial weak graph on the
same finite shell partition. -/
structure ProjectedInnerRadialGraph {I : ∀ f : ShellCellIndex G.grid.level, ProjectedCellInnerFace G f}
    {W : PenalizedFilledShell G I} (A : PhysicalShellCapClasses W) where
  sphereField : UnitTensorSphere → Ambient 5
  field : Point → Ambient 5
  derivative : Point → HarmonicMaps.Gradient 3 5
  sphere_ae : sphereField =ᵐ[tensorSphereMeasure] fun θ => frobeniusCoordinateEquiv (A.innerTensor θ)
  memW12 : MemW12 (sphericalShellDomain h) field derivative
  ray : ∀ (r : PositiveRadius) (θ : UnitTensorSphere), r.val • θ.val ∈ (sphericalShellDomain h).val →
    field (r.val • θ.val) = sphereField θ
  dirichlet_bound : HarmonicMaps.dirichletEnergy derivative (sphericalShellDomain h).val ≤
    (9 * 204 ^ 2 * 65 ^ 3 : ℝ≥0∞) * ENNReal.ofReal h *
      ∑ f, HarmonicMaps.dirichletEnergy (I f).derivative (tensorGridOpenParameterBox 2 h).val

/-- The constant radial inner graphs glue through all their actual shared
projected sides and give the original lower cap class. -/
theorem exists_projectedInnerRadialGraph {I : ∀ f : ShellCellIndex G.grid.level, ProjectedCellInnerFace G f}
    {W : PenalizedFilledShell G I} (A : PhysicalShellCapClasses W) (hSmall : h ≤ 1 / 32)
    (hCollar : ∀ f, HasContinuousProjectedFaceCollar (I f)) : Nonempty (ProjectedInnerRadialGraph A) := by
  classical
  let c := G.grid.center
  let J := ShellCellIndex G.grid.level
  let F (f : J) := shellAngularSpherePatch c h f.val
  let K (f : J) := Classical.choice (exists_projectedInnerFaceExtrusion (I f) hSmall)
  let u (f : J) := (I f).field ∘ (K f).parameter
  let D (f : J) := (K f).derivative
  let w := sphericalShellPiecewiseField c h u
  let E := sphericalShellPiecewiseDerivative c h D
  have hh := G.ht_pos
  have hh' : h ≤ 1 / 2 := hSmall.trans (by norm_num)
  have hc (i : Fin 3) : c i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(G.grid.offset_mem i).1, (G.grid.offset_mem i).2.le.trans hSmall⟩
  have hm := G.grid.radius_mem
  have hGraph (f : J) := (K f).memW12
  have hSide (s : ShellSideIndex G.grid.level) {t r : ℝ} (ht : t ∈ Ioo (0 : ℝ) h) (hr : r ∈ Ioo (1 - h) 1) :
      let y := sphericalLateralEdge c h s.edge.val (t, r)
      u s.1 y = frobeniusCoordinateEquiv (G.grid.projectedEdge s.edge t) ∧
        ∃ N : Set Point, IsOpen N ∧ y ∈ N ∧ ContinuousOn (u s.1) (N ∩ sphericalClosedCell c h s.1.val) :=
    (K s.1).open_side (hCollar s.1) s.2.1 s.2.2 ht hr
  obtain ⟨hW, _⟩ := sphericalShellPiecewise_memW12_of_common_sides hh hh' hc hm u D hGraph
    (fun f => (K f).bound) (fun e q => frobeniusCoordinateEquiv (G.grid.projectedEdge e q.1)) hSide
  let S (f : J) (θ : UnitTensorSphere) := (I f).field (unitToPhysicalCellFace h ((A.normalized.chart f).inverse θ.val))
  let p (θ : UnitTensorSphere) := ∑ f : J, (F f).indicator (S f) θ
  have hDis : Pairwise fun f g : J => Disjoint (F f) (F g) := pairwiseDisjoint_shellAngularSpherePatch hh hh' hc hm
  have hPoint (f : J) {θ : UnitTensorSphere} (hθ : θ ∈ F f) : p θ = S f θ := by
    dsimp only [p]
    rw [Finset.sum_eq_single f]
    · exact indicator_of_mem hθ _
    · intro g _ hg
      exact indicator_of_notMem (fun hp => Set.disjoint_left.mp (hDis hg) hp hθ) _
    · exact fun hf => (hf (Finset.mem_univ f)).elim
  have hEach (f : J) : ∀ᵐ θ ∂tensorSphereMeasure, θ ∈ F f → frobeniusCoordinateEquiv (A.innerTensor θ) = S f θ :=
    (ae_restrict_iff' ((A.normalized.chart f).patch_measurable.preimage measurable_subtype_coe)).mp (A.innerTensor_eq_on_patch f)
  have hCover : ∀ᵐ θ ∂tensorSphereMeasure, ∃ f : J, θ ∈ F f := ae_shellAngularSpherePatch_cover hh hc hm
  have hPae : p =ᵐ[tensorSphereMeasure] fun θ => frobeniusCoordinateEquiv (A.innerTensor θ) := by
    filter_upwards [hCover, ae_all_iff.mpr hEach] with θ hθ heq
    obtain ⟨f, hf⟩ := hθ
    exact (hPoint f hf).trans (heq f hf).symm
  refine ⟨{ sphereField := p
            field := w
            derivative := E
            sphere_ae := hPae
            memW12 := hW
            ray := ?_
            dirichlet_bound := ?_ }⟩
  · intro r θ hr
    have hθNorm : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
    have hr' : r.val ∈ Ioo (1 - h) 1 := by
      change ‖r.val • θ.val - 0‖ ∈ Ioo (1 - h) 1 at hr
      simpa only [sub_zero, norm_smul, Real.norm_of_nonneg r.property.le, hθNorm, mul_one] using hr
    by_cases hF : ∃ f : J, θ ∈ F f
    · obtain ⟨f, hf⟩ := hF
      have hCell := (radial_mem_cell_iff_angularPatch hh hh' hc hm f θ hr').mpr hf
      change sphericalShellPiecewiseField c h u (r.val • θ.val) = p θ
      rw [(sphericalShellPiecewise_eq_on_cell hh hh' hc hm u D f hCell).1, hPoint f hf]
      change (I f).field ((K f).parameter (r.val • θ.val)) = _
      rw [(K f).parameter_on_ray (A.normalized.chart f) hf hr']
    · have hNone (f : J) : θ ∉ F f := fun hf => hF ⟨f, hf⟩
      have hCells (f : J) : r.val • θ.val ∉ (sphericalCellOpenDomain c h f.val).val :=
        fun h => hNone f ((radial_mem_cell_iff_angularPatch hh hh' hc hm f θ hr').mp h)
      simp only [w, sphericalShellPiecewiseField, p, indicator_of_notMem (hCells _), indicator_of_notMem (hNone _),
        Finset.sum_const_zero]
  · obtain ⟨_, _, _, hDir, _, _⟩ := sphericalShellPiecewise_data hh hh' hc hm u D hGraph
    have hSum : HarmonicMaps.dirichletEnergy E (sphericalShellDomain h).val =
        ∑ f, HarmonicMaps.dirichletEnergy (D f) (sphericalCellOpenDomain c h f.val).val := by
      rw [HarmonicMaps.dirichletEnergy_eq_ofReal_integral hW.integrable_hsNormSq, hDir,
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg fun _ => hsNormSq_nonneg _)]
      exact Finset.sum_congr rfl fun f _ => (HarmonicMaps.dirichletEnergy_eq_ofReal_integral (hGraph f).integrable_hsNormSq).symm
    rw [hSum, Finset.mul_sum]
    exact Finset.sum_le_sum fun f _ => (K f).dirichlet_bound

/-- The constant radial graph can be rescaled into a genuine open
neighborhood of the unit sphere, as required by the native definition. -/
theorem ProjectedInnerRadialGraph.memSphereW12 {I : ∀ f : ShellCellIndex G.grid.level, ProjectedCellInnerFace G f}
    {W : PenalizedFilledShell G I} {A : PhysicalShellCapClasses W} (R : ProjectedInnerRadialGraph A)
    (hSmall : h ≤ 1 / 32) : StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) R.sphereField := by
  let Ω := sphericalShellDomain h
  let α : ℝ := 1 - h / 2
  have hh := G.ht_pos
  have hα : 0 < α := by dsimp only [α]; linarith only [hSmall]
  have hMid : α ∈ Ioo (1 - h) 1 := by constructor <;> dsimp only [α] <;> linarith only [hh]
  let X : OpenDomain 3 := ⟨(fun x : Point => α • x) ⁻¹' Ω.val, Ω.property.preimage (continuous_id.const_smul α)⟩
  have hFinite : (volume : Measure Point) Ω.val ≠ ⊤ := ne_top_of_le_ne_top measure_ball_ne_top
    (measure_mono (fun x hx => mem_ball_iff_norm.mpr hx.2 : Ω.val ⊆ ball (0 : Point) 1))
  have hData := StratificationTheory.memW12_affine_preimage_energy hFinite R.memW12 (0 : Point) (0 : Point) hα
  have hWeak : MemW12 X (fun x => R.field (α • x)) (fun x i => α • R.derivative (α • x) i) := by
    simpa only [X, zero_add, sub_zero, Function.comp_def] using! hData.1
  refine ⟨A.innerTensor_memLp.ae_eq R.sphere_ae.symm, X, ?_, ?_, _, _, hWeak, ?_⟩
  · intro θ hθ
    have hN : ‖θ‖ = 1 := mem_sphere_zero_iff_norm.mp hθ
    change ‖α • θ - 0‖ ∈ Ioo (1 - h) 1
    simpa only [sub_zero, norm_smul, Real.norm_of_nonneg hα.le, hN, mul_one] using hMid
  · intro hz
    have hp : 1 - h < ‖α • (0 : Point) - 0‖ := hz.1
    simp only [smul_zero, sub_zero, norm_zero] at hp
    linarith only [hSmall, hp]
  · intro r θ hr
    let ρ : PositiveRadius := ⟨α * r.val, mul_pos hα r.property⟩
    change R.field (α • (r.val • θ.val)) = R.sphereField θ
    rw [smul_smul]
    apply R.ray ρ θ
    change α • (r.val • θ.val) ∈ Ω.val at hr
    rwa [smul_smul] at hr

private theorem ae_eq_of_same_positive_rays {q : ℕ} {U : OpenDomain 3} {u w : Point → Ambient q}
    (h : ∀ (r : PositiveRadius) (θ : UnitTensorSphere), r.val • θ.val ∈ U.val →
      u (r.val • θ.val) = w (r.val • θ.val)) : u =ᵐ[volume.restrict U.val] w := by
  have hz : ∀ᵐ x : Point ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem U.property.measurableSet] with x hx₀ hx
  let θ : UnitTensorSphere := ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hx₀)⟩
  let r : PositiveRadius := ⟨‖x‖, norm_pos_iff.mpr hx₀⟩
  have hx' : r.val • θ.val = x := NormedSpace.norm_smul_normalize x
  rw [← hx']
  exact h r θ (by rwa [hx'])

private theorem setIntegral_ball_split_shell {h : ℝ} (hh : 0 < h) {f : Point → ℝ}
    (hf : IntegrableOn f (ball (0 : Point) 1)) :
    (∫ x in ball (0 : Point) 1, f x) =
      (∫ x in ball (0 : Point) (1 - h), f x) + ∫ x in (sphericalShellDomain h).val, f x := by
  let U := ball (0 : Point) (1 - h)
  let V := (sphericalShellDomain h).val
  have hNone : ∀ᵐ x : Point ∂volume, x ∉ sphere (0 : Point) (1 - h) := by
    rw [ae_iff]
    simpa only [not_not, setOf_mem_eq] using Measure.addHaar_sphere volume (0 : Point) (1 - h)
  have hCover : (ball (0 : Point) 1 : Set Point) =ᵐ[volume] (U ∪ V : Set Point) := by
    filter_upwards [hNone] with x hx
    rw [mem_sphere, dist_zero_right] at hx
    change (dist x 0 < 1) = (dist x 0 < 1 - h ∨ (1 - h < ‖x - 0‖ ∧ ‖x - 0‖ < 1))
    rw [dist_zero_right, sub_zero]
    exact propext ⟨fun h => (lt_or_gt_of_ne hx).elim Or.inl (fun hp => Or.inr ⟨hp, h⟩),
      fun hp => hp.elim (fun h => h.trans (by linarith only [hh])) And.right⟩
  have hDisj : Disjoint U V := Set.disjoint_left.mpr fun x hx hv => not_lt_of_ge (mem_ball_iff_norm.mp hx).le hv.1
  have hIntU := hf.mono_set (ball_subset_ball (sub_le_self _ hh.le))
  have hIntV := hf.mono_set (fun x hx => mem_ball_iff_norm.mpr hx.2 : V ⊆ ball (0 : Point) 1)
  rw [show (volume : Measure Point).restrict (ball 0 1) = volume.restrict (U ∪ V) from Measure.restrict_congr_set hCover]
  exact setIntegral_union hDisj (sphericalShellDomain h).property.measurableSet hIntU hIntV

private theorem radial_nativeEnergy_on_shell {q : ℕ} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    (p : UnitTensorSphere → Ambient q) (hp : StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) p)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hU : MemW12 (sphericalShellDomain h) u D)
    (hRay : ∀ (r : PositiveRadius) (θ : UnitTensorSphere), r.val • θ.val ∈ (sphericalShellDomain h).val →
      u (r.val • θ.val) = p θ) :
    (∫ x in (sphericalShellDomain h).val, hsNormSq (D x)) = h * nativeSphereGradientEnergy p hp := by
  have hR : 0 < 1 - h := by linarith only [hh']
  obtain ⟨w, Dw, hw, hwr, _, _, hwe, _⟩ := StratificationTheory.exists_radial_ball_sobolev_extension
    (n := 3) (by decide) p hp (R := 1) (by norm_num)
  obtain ⟨z, Dz, hz, hzr, _, _, hze, _⟩ := StratificationTheory.exists_radial_ball_sobolev_extension
    (n := 3) (by decide) p hp hR
  let A := sphericalShellDomain h
  let B := ballDomain (0 : Point) (1 - h)
  have hIn : B.val ⊆ ball (0 : Point) 1 := ball_subset_ball (sub_le_self _ hh.le)
  have hOut : A.val ⊆ ball (0 : Point) 1 := fun x hx => mem_ball_iff_norm.mpr hx.2
  have hg_in : Dw =ᵐ[volume.restrict B.val] Dz := by
    apply (hw.1.mono hIn).ae_eq_of_ae_eq_map hz.1
    exact ae_eq_of_same_positive_rays fun r θ _ => (hwr r θ).trans (hzr r θ).symm
  have hg_out : Dw =ᵐ[volume.restrict A.val] D := by
    apply (hw.1.mono hOut).ae_eq_of_ae_eq_map hU.1
    exact ae_eq_of_same_positive_rays fun r θ hθ => (hwr r θ).trans (hRay r θ hθ).symm
  have hi : (∫ x in B.val, hsNormSq (Dw x)) = ∫ x in B.val, hsNormSq (Dz x) :=
    integral_congr_ae (hg_in.mono (fun _ h => congrArg hsNormSq h))
  have ho : (∫ x in A.val, hsNormSq (Dw x)) = ∫ x in A.val, hsNormSq (D x) :=
    integral_congr_ae (hg_out.mono (fun _ h => congrArg hsNormSq h))
  have hTotal := setIntegral_ball_split_shell hh hw.integrable_hsNormSq
  change (∫ x in ball (0 : Point) 1, hsNormSq (Dw x)) =
    (∫ x in B.val, hsNormSq (Dw x)) + ∫ x in A.val, hsNormSq (Dw x) at hTotal
  rw [hi, ho] at hTotal
  have hThree : (3 : ℝ) - 2 = 1 := by norm_num
  have hw' : (∫ x in ball (0 : Point) 1, hsNormSq (Dw x)) = nativeSphereGradientEnergy p hp := by
    simpa [nativeSphereGradientEnergy, hsNormSq, hThree] using! hwe
  have hz' : (∫ x in B.val, hsNormSq (Dz x)) = (1 - h) * nativeSphereGradientEnergy p hp := by
    simpa [B, nativeSphereGradientEnergy, hsNormSq, hThree] using! hze
  rw [hw', hz'] at hTotal
  change (∫ x in A.val, hsNormSq (D x)) = _
  nlinarith only [hTotal]

/-- The lower trace has the actual native sphere H¹ graph and a uniform
energy bound by the original physical inner face Dirichlet sum. -/
theorem exists_projectedInnerCap_memSphereH1 {I : ∀ f : ShellCellIndex G.grid.level, ProjectedCellInnerFace G f}
    {W : PenalizedFilledShell G I} (A : PhysicalShellCapClasses W) (hSmall : h ≤ 1 / 32)
    (hCollar : ∀ f, HasContinuousProjectedFaceCollar (I f)) :
    ∃ hp : MemSphereH1 A.innerTensor,
      ENNReal.ofReal (sphereGradientEnergy A.innerTensor hp) ≤
        (9 * 204 ^ 2 * 65 ^ 3 : ℝ≥0∞) *
          ∑ f, HarmonicMaps.dirichletEnergy (I f).derivative (tensorGridOpenParameterBox 2 h).val := by
  obtain ⟨R⟩ := exists_projectedInnerRadialGraph A hSmall hCollar
  have hp₀ := R.memSphereW12 hSmall
  have hp : MemSphereH1 A.innerTensor := StratificationTheory.memSphereW12_congr_ae (by decide : 2 ≤ 3) hp₀ R.sphere_ae
  refine ⟨hp, ?_⟩
  have hGrad := (StratificationTheory.sphereGradient_characterization (by decide : 2 ≤ 3) R.sphereField hp₀).2.2
    (fun θ => frobeniusCoordinateEquiv (A.innerTensor θ)) hp R.sphere_ae
  have hEq : sphereGradientEnergy A.innerTensor hp = nativeSphereGradientEnergy R.sphereField hp₀ := by
    unfold sphereGradientEnergy nativeSphereGradientEnergy
    rw [hGrad]
    rfl
  have hh' : h ≤ 1 / 2 := hSmall.trans (by norm_num)
  have hShell := radial_nativeEnergy_on_shell G.ht_pos hh' R.sphereField hp₀ R.memW12 R.ray
  have hBound := R.dirichlet_bound
  rw [HarmonicMaps.dirichletEnergy_eq_ofReal_integral R.memW12.integrable_hsNormSq, hShell,
    ENNReal.ofReal_mul G.ht_pos.le] at hBound
  rw [hEq]
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr G.ht_pos).ne' ENNReal.ofReal_ne_top).mp
  exact hBound.trans_eq (by ac_rfl)

end Thesis
