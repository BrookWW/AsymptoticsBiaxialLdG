module

public import Thesis.Interpolation.PenalizedShellCell
public import Thesis.Interpolation.SphericalCellHalfspaces
import StratificationTheory.Foundation.CubicalConeGeometry
import StratificationTheory.Foundation.PositiveCubeSobolevDenormalization

/-! Continuity up to the common affine side of a filled shell cell. -/

public section

open HarmonicMaps MeasureTheory Metric Set
open scoped Matrix.Norms.Frobenius Topology

namespace Thesis

/-- A continuous face datum makes its degree-zero filling continuous near
each point of that face's relative interior. -/
theorem UnitCellFilling.exists_continuous_near_face {q : ℕ} {B : ℝ} {A : CompatibleCellFaces q B}
    (W : UnitCellFilling A) (j : CellFaceIndex) (hA : ContinuousOn (A.face j) (unitCellCube 2).val)
    {x : Domain 2} (hx : x ∈ (unitCellCube 2).val) :
    ∃ N : Set Point, IsOpen N ∧ unitCellFacePoint j x 1 ∈ N ∧ ContinuousOn (cellRadialField W.boundary) N := by
  let Q := StratificationTheory.cubicalSignedFaceIsometry 2 j.1 j.2
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let b : Point → Domain 2 := fun y => (e (Q.symm y)).1
  let r : Point → ℝ := fun y => (e (Q.symm y)).2 0
  let C : Set Point := {y | 0 < r y} ∩ ⋂ i : Fin 2, {y | |b y i| < r y}
  let g : Point → Domain 2 := fun y => (r y)⁻¹ • b y
  have hb : Continuous b := continuous_fst.comp (e.continuous.comp Q.symm.continuous)
  have hr : Continuous r := (EuclideanSpace.proj (0 : Fin 1)).continuous.comp
    (continuous_snd.comp (e.continuous.comp Q.symm.continuous))
  have hC : IsOpen C := (isOpen_lt continuous_const hr).inter (isOpen_iInter_of_finite fun i =>
    isOpen_lt ((EuclideanSpace.proj i).continuous.comp hb).abs hr)
  have hMaps : MapsTo g C (unitCellCube 2).val := by
    intro y hy
    apply (StratificationTheory.inverse_smul_mem_unit_coordinate_face_iff hy.1 (b y)).mpr
    intro i
    exact mem_iInter.mp hy.2 i
  have hEq : EqOn (cellRadialField W.boundary) (A.face j ∘ g) C := by
    intro y hy
    have hRadial : r y • unitCellFacePoint j (g y) 1 = y := by
      rw [← unitCellFacePoint_smul]
      change Q (e.symm (r y • ((r y)⁻¹ • b y), EuclideanSpace.single 0 (r y))) = y
      rw [smul_smul, mul_inv_cancel₀ (show r y ≠ 0 from (show 0 < r y from hy.1).ne'), one_smul]
      have hPair : (b y, EuclideanSpace.single (0 : Fin 1) (r y)) = e (Q.symm y) := by
        apply Prod.ext
        · rfl
        · apply PiLp.ext
          intro i
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          simp only [PiLp.single_apply, ite_true, r]
      rw [hPair, e.symm_apply_apply, Q.apply_symm_apply]
    exact (congrArg (cellRadialField W.boundary) hRadial.symm).trans
      (W.ray j (g y) (hMaps hy) (r y) hy.1)
  have hCont : ContinuousOn (A.face j ∘ g) C :=
    hA.comp ((hr.continuousOn.inv₀ fun y hy => (show 0 < r y from hy.1).ne').smul hb.continuousOn) hMaps
  have hGeom : e (Q.symm (unitCellFacePoint j x 1)) = (x, EuclideanSpace.single 0 1) := by
    change e (Q.symm (Q (e.symm (x, EuclideanSpace.single 0 1)))) = _
    rw [Q.symm_apply_apply, e.apply_symm_apply]
  have hIn : unitCellFacePoint j x 1 ∈ C := by
    constructor
    · change 0 < (e (Q.symm (unitCellFacePoint j x 1))).2 0
      rw [hGeom]
      norm_num [PiLp.single_apply]
    · apply mem_iInter.mpr
      intro i
      change |(e (Q.symm (unitCellFacePoint j x 1))).1 i| < (e (Q.symm (unitCellFacePoint j x 1))).2 0
      rw [hGeom]
      simpa only [PiLp.single_apply, ite_true] using (StratificationTheory.mem_unit_coordinate_face_iff x).mp hx i
  exact ⟨C, hC, hIn, hCont.congr hEq⟩

private theorem shellCellParameterToUnit_mem_closed {h : ℝ} (hh : 0 < h) {z : Point}
    (hz : z ∈ sphericalCellNativeBox h) : ∀ i : Fin 3, shellCellParameterToUnit h z i ∈ Icc (-1 : ℝ) 1 := by
  have hPos : 0 < h / 2 := half_pos hh
  change (z 0 ∈ Icc 0 h ∧ z 1 ∈ Icc 0 h) ∧ z 2 ∈ Icc (1 - h) 1 at hz
  intro i
  fin_cases i
  · change ((h / 2)⁻¹ * (z 0 - (0 + h / 2))) ∈ Icc (-1 : ℝ) 1
    rw [mul_comm, ← div_eq_mul_inv]
    exact ⟨(le_div_iff₀ hPos).mpr (by linarith only [hz.1.1.1]),
      (div_le_iff₀ hPos).mpr (by linarith only [hz.1.1.2])⟩
  · change ((h / 2)⁻¹ * (z 1 - (0 + h / 2))) ∈ Icc (-1 : ℝ) 1
    rw [mul_comm, ← div_eq_mul_inv]
    exact ⟨(le_div_iff₀ hPos).mpr (by linarith only [hz.1.2.1]),
      (div_le_iff₀ hPos).mpr (by linarith only [hz.1.2.2])⟩
  · change ((h / 2)⁻¹ * (z 2 - (1 - h + h / 2))) ∈ Icc (-1 : ℝ) 1
    rw [mul_comm, ← div_eq_mul_inv]
    exact ⟨(le_div_iff₀ hPos).mpr (by linarith only [hz.2.1]),
      (div_le_iff₀ hPos).mpr (by linarith only [hz.2.2])⟩

private theorem unitToShellCellParameter_shellCellParameterToUnit {h : ℝ} (hh : 0 < h) (z : Point) :
    unitToShellCellParameter h (shellCellParameterToUnit h z) = z := by
  simp only [unitToShellCellParameter, shellCellParameterToUnit, smul_smul,
    mul_inv_cancel₀ (half_pos hh).ne', one_smul]
  abel

/-- Continuity of the face datum is inherited within the actual closed cell
at every relative interior point of its signed face. -/
theorem SphericalCellFilling.exists_continuous_near_face {q : ℕ} {B h : ℝ} {A : CompatibleCellFaces q B}
    {c : Point} {f : TensorGridSquare} (W : SphericalCellFilling A c h f)
    (hh : 0 < h) (hh' : h ≤ 1 / 2) {m : ℕ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32)) (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    (hf : f ∈ cubeBoundarySquares m) (j : CellFaceIndex) (hA : ContinuousOn (A.face j) (unitCellCube 2).val)
    {x : Domain 2} (hx : x ∈ (unitCellCube 2).val) :
    ∃ N : Set Point, IsOpen N ∧ normalizedShellCellPoint c h f (unitCellFacePoint j x 1) ∈ N ∧
      ContinuousOn W.field (N ∩ sphericalClosedCell c h f) := by
  obtain ⟨G, _, _, hLeft, hRight, hSmooth, _, _⟩ := exists_sphericalCellNativeInverse hh hh' hc hm hf
  let F := sphericalCellNativePoint c h f
  let V := sphericalClosedCell c h f
  let Z := shellCellParameterToUnit h ∘ G
  have hG : MapsTo G V (sphericalCellNativeBox h) := by
    rintro y ⟨p, hp, rfl⟩
    let z := sphericalCellNativeParameter.symm p
    have hP : sphericalCellNativeParameter z = p := sphericalCellNativeParameter.apply_symm_apply _
    have hz : z ∈ sphericalCellNativeBox h := by
      change sphericalCellNativeParameter z ∈ sphericalCellParameterBox h
      rwa [hP]
    have hF : F z = sphericalCellPoint c h f p := by
      change sphericalCellPoint c h f (sphericalCellNativeParameter z) = _
      rw [hP]
    rw [← hF, hLeft hz]
    exact hz
  have hCont : ContinuousOn Z V := by
    have hNorm : Continuous (shellCellParameterToUnit h) := by
      change Continuous (fun z : Point => (h / 2)⁻¹ • (z - shellCellParameterCenter h))
      fun_prop
    exact hNorm.comp_continuousOn hSmooth.continuousOn
  have hEq : EqOn W.field (cellRadialField W.unit.boundary ∘ Z) V := by
    intro y hy
    have hb := W.chart_value (Z y) (shellCellParameterToUnit_mem_closed hh (hG hy))
    change W.field (F (unitToShellCellParameter h (shellCellParameterToUnit h (G y)))) = _ at hb
    have hR : F (G y) = y := hRight hy
    rwa [unitToShellCellParameter_shellCellParameterToUnit hh, hR] at hb
  let p := unitCellFacePoint j x 1
  let z := unitToShellCellParameter h p
  have hz : z ∈ sphericalCellNativeBox h := unitToShellCellParameter_mem_box hh
    (unitCellFacePoint_mem_closed hx j (by constructor <;> norm_num))
  have hFz : F z ∈ V := ⟨sphericalCellNativeParameter z, hz, rfl⟩
  have hZ : Z (F z) = p := by
    change shellCellParameterToUnit h (G (F z)) = p
    have hL : G (F z) = z := hLeft hz
    rw [hL]
    exact shellCellParameterToUnit_unitToShellCellParameter hh p
  obtain ⟨U, hU, hUmem, hUcont⟩ := W.unit.exists_continuous_near_face j hA hx
  have hU' : Z ⁻¹' U ∈ 𝓝[V] F z :=
    (hCont (F z) hFz) (hU.mem_nhds (hZ.symm ▸ hUmem))
  obtain ⟨N, hN, hNmem, hNsub⟩ := mem_nhdsWithin.mp hU'
  have hComp : ContinuousOn (cellRadialField W.unit.boundary ∘ Z) (N ∩ V) :=
    hUcont.comp (hCont.mono inter_subset_right) hNsub
  exact ⟨N, hN, hNmem, hComp.congr (hEq.mono inter_subset_right)⟩

/-- Continuity of the given face data gives continuity within the closed
physical cell, including each point of the relative face interior. -/
theorem SphericalCellFilling.continuousWithinAt_face {q : ℕ} {B h : ℝ} {A : CompatibleCellFaces q B}
    {c : Point} {f : TensorGridSquare} (W : SphericalCellFilling A c h f)
    (hh : 0 < h) (hh' : h ≤ 1 / 2) {m : ℕ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32)) (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    (hf : f ∈ cubeBoundarySquares m) (j : CellFaceIndex) (hA : ContinuousOn (A.face j) (unitCellCube 2).val)
    {x : Domain 2} (hx : x ∈ (unitCellCube 2).val) :
    ContinuousWithinAt W.field (sphericalClosedCell c h f) (normalizedShellCellPoint c h f (unitCellFacePoint j x 1)) := by
  obtain ⟨N, hN, hPt, hW⟩ := W.exists_continuous_near_face hh hh' hc hm hf j hA hx
  let z := unitToShellCellParameter h (unitCellFacePoint j x 1)
  have hBox : z ∈ sphericalCellNativeBox h :=
    unitToShellCellParameter_mem_box hh (unitCellFacePoint_mem_closed hx j (by constructor <;> norm_num))
  have hMem : normalizedShellCellPoint c h f (unitCellFacePoint j x 1) ∈ sphericalClosedCell c h f :=
    ⟨sphericalCellNativeParameter z, hBox, rfl⟩
  have h := hW _ ⟨hPt, hMem⟩
  rw [inter_comm, continuousWithinAt_inter (hN.mem_nhds hPt)] at h
  exact h

/-- On any open lateral side the filled field has the original affine side
value and is continuous on the adjacent closed cell in a neighborhood. -/
theorem penalizedShellCell_open_side {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0}
    {hv : MemSphereH1 v} {G : PenalizedSphereFaces a B h v hv} (hSmall : h ≤ 1 / 32)
    {f : ↥(cubeBoundarySquares G.grid.level)} (I : ProjectedCellInnerFace G f)
    {A : CompatiblePhysicalCellFaces 5 (max B (Real.sqrt 2 * vacuumRadius a)) h}
    (hFace : A.face = penalizedShellCellFace I)
    (W : SphericalCellFilling (A.toUnit G.ht_pos) G.grid.center h f.val)
    (i : Fin 2) (upper : Bool) {t r : ℝ} (ht : t ∈ Ioo (0 : ℝ) h) (hr : r ∈ Ioo (1 - h) 1) :
    let e := tensorSquareCoordinateEdge f i upper
    let y := sphericalLateralEdge G.grid.center h e.val (t, r)
    y ∈ sphericalClosedCell G.grid.center h f.val ∧
      W.field y = G.grid.cellSide e (WithLp.toLp 2 ![t, r - (1 - h)]) ∧
      ∃ N : Set Point, IsOpen N ∧ y ∈ N ∧ ContinuousOn W.field (N ∩ sphericalClosedCell G.grid.center h f.val) := by
  intro e y
  let j : CellFaceIndex := (i.castSucc, upper)
  have hj : j.1 ≠ 2 := Fin.castSucc_ne_last i
  let d := r - (1 - h)
  let z : Domain 2 := if i = 0 then WithLp.toLp 2 ![d, t] else WithLp.toLp 2 ![t, d]
  let x : Domain 2 := (h / 2)⁻¹ • (z - WithLp.toLp 2 (fun _ => h / 2))
  have hh := G.ht_pos
  have hd : d ∈ Ioo (0 : ℝ) h := ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
  have hz : z ∈ (tensorGridOpenParameterBox 2 h).val := by
    apply mem_iInter.mpr
    intro k
    fin_cases i <;> fin_cases k <;> simp [z, hd, ht]
  have hx : x ∈ (unitCellCube 2).val := by
    have hPre : (fun z : Domain 2 => (h / 2)⁻¹ • (z - WithLp.toLp 2 (fun _ => h / 2))) ⁻¹'
        (unitCellCube 2).val = (tensorGridOpenParameterBox 2 h).val :=
      StratificationTheory.inverse_unit_cube_preimage_unit_cube 2 hh
    have hz' := hz
    rwa [← hPre] at hz'
  have hPhys : unitToPhysicalCellFace h x = z := unitToPhysicalCellFace_inverse hh z
  have hPoint : normalizedShellCellPoint G.grid.center h f.val (unitCellFacePoint j x 1) = y := by
    rw [shellCellSide_point f j hj x, hPhys]
    have hRadial : 1 - h + d = r := by dsimp only [d]; ring
    fin_cases i <;> simp [j, y, e, shellCellSideEdge, z, hRadial]
  have hBox : unitToShellCellParameter h (unitCellFacePoint j x 1) ∈ sphericalCellNativeBox h :=
    unitToShellCellParameter_mem_box hh (unitCellFacePoint_mem_closed hx j (by constructor <;> norm_num))
  have hy : y ∈ sphericalClosedCell G.grid.center h f.val := by
    rw [← hPoint]
    exact ⟨sphericalCellNativeParameter (unitToShellCellParameter h (unitCellFacePoint j x 1)), hBox, rfl⟩
  have hSwap : physicalSquareSwap (WithLp.toLp 2 ![d, t] : Domain 2) = WithLp.toLp 2 ![t, d] := by
    apply PiLp.ext
    intro k
    fin_cases k <;> simp [physicalSquareSwap_coordinates]
  have hVal : W.field y = G.grid.cellSide e (WithLp.toLp 2 ![t, d]) := by
    rw [← hPoint, W.face_value j hx, A.toUnit_face]
    change A.face j (unitToPhysicalCellFace h x) = _
    rw [hFace, hPhys]
    fin_cases i <;> simp [penalizedShellCellFace, j, shellCellSideEdge, e, z, hSwap, Function.comp_apply]
  have hMap : MapsTo (unitToPhysicalCellFace h) (unitCellCube 2).val (sphericalFaceParameterBox h) := by
    intro q hq
    have hPre : unitToPhysicalCellFace h ⁻¹' (tensorGridOpenParameterBox 2 h).val = (unitCellCube 2).val :=
      StratificationTheory.affine_unit_cube_preimage_positive_cube 2 hh
    have hq' : unitToPhysicalCellFace h q ∈ (tensorGridOpenParameterBox 2 h).val := by
      change q ∈ unitToPhysicalCellFace h ⁻¹' (tensorGridOpenParameterBox 2 h).val
      rwa [hPre]
    exact ⟨Ioo_subset_Icc_self (mem_iInter.mp hq' 0), Ioo_subset_Icc_self (mem_iInter.mp hq' 1)⟩
  have hAffine : Continuous (unitToPhysicalCellFace h) := by
    unfold unitToPhysicalCellFace
    fun_prop
  have hTraceCont : ContinuousOn ((A.toUnit hh).face j) (unitCellCube 2).val := by
    rw [A.toUnit_face]
    apply ContinuousOn.comp ?_ hAffine.continuousOn hMap
    rw [hFace]
    have hsw : MapsTo physicalSquareSwap (sphericalFaceParameterBox h) (sphericalFaceParameterBox h) := by
      intro q hq
      constructor
      · change physicalSquareSwap q 0 ∈ Icc (0 : ℝ) h
        rw [(physicalSquareSwap_coordinates q).1]
        exact hq.2
      · change physicalSquareSwap q 1 ∈ Icc (0 : ℝ) h
        rw [(physicalSquareSwap_coordinates q).2]
        exact hq.1
    fin_cases i
    · simpa [penalizedShellCellFace, shellCellSideEdge, j, e] using
        (G.grid.cellSide_continuousOn hh (tensorSquareCoordinateEdge f 0 upper)).comp physicalSquareSwap.continuous.continuousOn hsw
    · simpa [penalizedShellCellFace, shellCellSideEdge, j, e] using
        G.grid.cellSide_continuousOn hh (tensorSquareCoordinateEdge f 1 upper)
  have hCenter (k : Fin 3) : G.grid.center k ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(G.grid.offset_mem k).1, (G.grid.offset_mem k).2.le.trans hSmall⟩
  obtain ⟨N, hN, hNmem, hNCont⟩ := W.exists_continuous_near_face hh (hSmall.trans (by norm_num)) hCenter
    G.grid.radius_mem f.property j hTraceCont hx
  exact ⟨hy, hVal, N, hN, hPoint ▸ hNmem, hNCont⟩

end Thesis
