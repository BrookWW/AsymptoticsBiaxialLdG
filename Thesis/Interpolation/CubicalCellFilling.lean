module

public import Thesis.Interpolation.SphericalCellSobolev
public import StratificationTheory.Foundation.CubicalFaceFamilyExtension
import StratificationTheory.Foundation.CubicalRadialFaceValues
import StratificationTheory.Foundation.TranslatedCubeAffineCoordinates
import Thesis.Foundation.BulkGeometry
import Thesis.StressEnergy
import Thesis.Upstream.MinimizingSobolev

/-! Degree-zero filling of the six compatible faces of a shell cell. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal NNReal Topology Matrix.Norms.Frobenius

namespace Thesis

/-- The open centered unit cube in native Euclidean coordinates. -/
@[expose] def unitCellCube (n : ℕ) : OpenDomain n :=
  ⟨⋂ k : Fin n, (EuclideanSpace.proj k) ⁻¹' Ioo (-1 : ℝ) 1,
    isOpen_iInter_of_finite fun k => isOpen_Ioo.preimage (EuclideanSpace.proj k).continuous⟩

abbrev CellFaceIndex := Fin 3 × Bool

/-- Each face uses the original signed coordinate chart of the cube. The
Boolean records whether the normal coordinate is `1` or `-1`. -/
@[expose] noncomputable def unitCellFacePoint (j : CellFaceIndex) (x : Domain 2) (t : ℝ) : Point :=
  StratificationTheory.cubicalSignedFaceIsometry 2 j.1 j.2
    ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).symm
      (x, EuclideanSpace.single 0 t))

/-- A transverse slice of an open face in its coordinate direction `i`. -/
@[expose] noncomputable def unitCellFaceSlice (i : Fin 2) (x : Domain 1) (t : ℝ) : Domain 2 :=
  StratificationTheory.cubicalSignedFaceIsometry 1 i true
    ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).symm
      (x, EuclideanSpace.single 0 t))

/-- The common physical edge point as viewed from one of its incident faces. -/
@[expose] noncomputable def unitCellEdgePoint (j : CellFaceIndex) (i : Fin 2) (positive : Bool)
    (x : Domain 1) : Point :=
  unitCellFacePoint j
    (StratificationTheory.cubicalSignedFaceIsometry 1 i positive
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).symm
        (x, EuclideanSpace.single 0 1))) 1

/-- The six original weak face graphs share their edge trace classes via
one function of the physical edge point. -/
structure CompatibleCellFaces (q : ℕ) (B : ℝ) where
  face : CellFaceIndex → Domain 2 → Ambient q
  derivative : CellFaceIndex → Domain 2 → HarmonicMaps.Gradient 2 q
  face_memW12 : ∀ j, MemW12 (unitCellCube 2) (face j) (derivative j)
  face_bound : ∀ j, ∀ᵐ x ∂volume.restrict (unitCellCube 2).val, ‖face j x‖ ≤ B
  edge : Point → Ambient q
  trace : CellFaceIndex → Fin 2 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict (unitCellCube 1).val))
  trace_slice : ∀ j i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
    ∃ h : MemLp (fun x => face j (unitCellFaceSlice i x t)) 2 (volume.restrict (unitCellCube 1).val),
      trace j i ⟨t, ht.1.le, ht.2.le⟩ = h.toLp _
  trace_edge : ∀ j i positive,
    (trace j i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
      by cases positive <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict (unitCellCube 1).val]
      fun x => edge (unitCellEdgePoint j i positive x)

/-- The degree-zero map evaluates the same boundary datum on each ray. -/
@[expose] noncomputable def cellRadialField {q : ℕ} (G : Point → Ambient q) (y : Point) : Ambient q :=
  G (‖WithLp.ofLp y‖⁻¹ • y)

private theorem cellRadialField_pos_smul {q : ℕ} (G : Point → Ambient q) {r : ℝ} (hr : 0 < r) (y : Point) :
    cellRadialField G (r • y) = cellRadialField G y := by
  unfold cellRadialField
  rw [WithLp.ofLp_smul, norm_smul, Real.norm_of_nonneg hr.le, smul_smul]
  have h : (r * ‖WithLp.ofLp y‖)⁻¹ * r = ‖WithLp.ofLp y‖⁻¹ := by
    by_cases hn : ‖WithLp.ofLp y‖ = 0
    · simp [hn]
    · field_simp
  rw [h]

theorem unitCellFacePoint_smul (j : CellFaceIndex) (x : Domain 2) (r : ℝ) :
    unitCellFacePoint j (r • x) r = r • unitCellFacePoint j x 1 := by
  let Q := StratificationTheory.cubicalSignedFaceIsometry 2 j.1 j.2
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  change Q (e.symm (r • x, EuclideanSpace.single 0 r)) = r • Q (e.symm (x, EuclideanSpace.single 0 1))
  rw [← Q.map_smul, ← e.symm.map_smul]
  apply congrArg Q
  apply congrArg e.symm
  apply Prod.ext
  · rfl
  apply PiLp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change (EuclideanSpace.single 0 r : Domain 1) 0 = (r • (EuclideanSpace.single 0 1 : Domain 1)) 0
  simp only [PiLp.single_apply, PiLp.smul_apply, ite_true, smul_eq_mul, mul_one]

private theorem unitCell_radial_lintegral_factor :
    (∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ (2 : ℕ))) = ENNReal.ofReal (1 / 3 : ℝ) := by
  have hInt : IntegrableOn (fun r : ℝ => r ^ (2 : ℕ)) (Ioo 0 1) :=
    (continuous_id.pow 2).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hNN : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun r => r ^ (2 : ℕ) :=
    Eventually.of_forall fun _ => sq_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hNN, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_pow]
  norm_num

/-- The integral of any measurable nonnegative function of the radial values
is one third of its sum over the six original unit-face measures. -/
theorem cellRadialField_lintegral {q : ℕ} (G : Point → Ambient q)
    (Dface : CellFaceIndex → Domain 2 → HarmonicMaps.Gradient 2 q)
    (hFace : ∀ j, MemW12 (unitCellCube 2) (fun x => G (unitCellFacePoint j x 1)) (Dface j))
    (b : Ambient q → ℝ≥0∞)
    (hb : AEMeasurable (b ∘ cellRadialField G) (volume.restrict (unitCellCube 3).val)) :
    (∫⁻ y in (unitCellCube 3).val, b (cellRadialField G y)) =
      ENNReal.ofReal (1 / 3 : ℝ) * ∑ j : CellFaceIndex, ∫⁻ x in (unitCellCube 2).val, b (G (unitCellFacePoint j x 1)) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let C (j : CellFaceIndex) : Set Point := {y |
    (if j.2 then y j.1 else -y j.1) ∈ Ioo (0 : ℝ) 1 ∧
      ∀ k : Fin 3, k ≠ j.1 → |y k| < (if j.2 then y j.1 else -y j.1)}
  have hOpen (j : CellFaceIndex) : IsOpen (C j) := StratificationTheory.isOpen_cubical_signed_cone j.1 j.2
  have hSub (j : CellFaceIndex) : C j ⊆ (unitCellCube 3).val :=
    StratificationTheory.cubical_signed_cone_subset_unit_cube j.1 j.2
  have hDisj : Pairwise fun j k : CellFaceIndex => Disjoint (C j) (C k) :=
    StratificationTheory.pairwise_disjoint_cubical_signed_cones 2
  have hCover : ∀ᵐ y ∂volume.restrict (unitCellCube 3).val, ∃ j : CellFaceIndex, y ∈ C j :=
    StratificationTheory.ae_unit_cube_mem_cubical_signed_cone (by decide : 2 ≤ 2)
  have hRestrict : (volume : Measure Point).restrict (unitCellCube 3).val = volume.restrict (⋃ j, C j) := by
    apply Measure.restrict_congr_set
    have hA : ∀ᵐ y ∂volume, y ∈ (unitCellCube 3).val → ∃ j : CellFaceIndex, y ∈ C j :=
      (ae_restrict_iff' (unitCellCube 3).property.measurableSet).mp hCover
    filter_upwards [hA] with y hy
    exact propext ⟨fun h => mem_iUnion.mpr (hy h), fun h =>
      let ⟨j, hj⟩ := mem_iUnion.mp h
      hSub j hj⟩
  let ψ := b ∘ cellRadialField G
  have hCone (j : CellFaceIndex) :
      (∫⁻ y in C j, ψ y) = ENNReal.ofReal (1 / 3 : ℝ) *
          ∫⁻ x in (unitCellCube 2).val, b (G (unitCellFacePoint j x 1)) := by
    let Q := StratificationTheory.cubicalSignedFaceIsometry 2 j.1 j.2
    let T : Point → ℝ := fun y => (e y).2 0
    let C₀ := T ⁻¹' Ioo (0 : ℝ) 1 ∩ ⋂ i : Fin 2, {y : Point | |(e y).1 i| < T y}
    have hC : Q ⁻¹' C j = C₀ := by
      ext y
      have hr := StratificationTheory.cubicalSignedFaceIsometry_strict_cone_iff j.1 j.2 (Q y)
      change ((e (Q.symm (Q y))).2 0 ∈ Ioo (0 : ℝ) 1 ∧
        ∀ k : Fin 2, |(e (Q.symm (Q y))).1 k| < (e (Q.symm (Q y))).2 0) ↔ Q y ∈ C j at hr
      rw [Q.symm_apply_apply] at hr
      simpa only [C₀, T, mem_preimage, mem_setOf_eq, mem_inter_iff, mem_iInter] using hr.symm
    have hMP := Q.measurePreserving.restrict_preimage (hOpen j).measurableSet
    rw [hC] at hMP
    have hψ : AEMeasurable ψ (volume.restrict (C j)) :=
      hb.mono_measure (Measure.restrict_mono_set volume (hSub j))
    have hψQ : AEMeasurable (ψ ∘ Q) (volume.restrict C₀) := hψ.comp_quasiMeasurePreserving hMP.quasiMeasurePreserving
    obtain ⟨_, _, hJac, _, _, _, _, _, _, _⟩ :=
      StratificationTheory.cubical_face_cone_extension_joint (by decide : 2 ≤ 2) (hFace j)
    have hJac' := hJac (ψ ∘ Q) hψQ
    have hRay (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) (x : Domain 2) (hx : x ∈ (unitCellCube 2).val) :
        (ψ ∘ Q) (e.symm (r • x, EuclideanSpace.single 0 r)) = b (G (unitCellFacePoint j x 1)) := by
      change b (cellRadialField G (unitCellFacePoint j (r • x) r)) = _
      rw [unitCellFacePoint_smul, cellRadialField_pos_smul _ hr.1]
      exact congrArg b (StratificationTheory.cubical_radial_map_unit_face_value G j.1 j.2 x hx)
    calc
      _ = ∫⁻ y in C₀, (ψ ∘ Q) y := by
        have hm : AEMeasurable ψ (Measure.map Q (volume.restrict C₀)) := by rw [hMP.map_eq]; exact hψ
        exact hMP.map_eq ▸ lintegral_map' hm hMP.measurable.aemeasurable
      _ = ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ (2 : ℕ)) *
          ∫⁻ x in (unitCellCube 2).val, (ψ ∘ Q) (e.symm (r • x, EuclideanSpace.single 0 r)) := hJac'
      _ = ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ (2 : ℕ)) *
          ∫⁻ x in (unitCellCube 2).val, b (G (unitCellFacePoint j x 1)) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro r hr
        exact congrArg (fun X => ENNReal.ofReal (r ^ 2) * X)
          (setLIntegral_congr_fun (unitCellCube 2).property.measurableSet (hRay r hr))
      _ = _ := by
        rw [lintegral_mul_const _ (by fun_prop : Measurable fun r : ℝ => ENNReal.ofReal (r ^ (2 : ℕ))),
          unitCell_radial_lintegral_factor]
  rw [show (∫⁻ y in (unitCellCube 3).val, b (cellRadialField G y)) =
    ∫⁻ y in ⋃ j, C j, ψ y from congrArg (fun μ => ∫⁻ y, ψ y ∂μ) hRestrict,
    lintegral_iUnion (fun j => (hOpen j).measurableSet) hDisj, tsum_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => hCone j)

/-- The native unit-cube filling, its full face traces and its separate
Dirichlet and bulk formulas on the same degree-zero representative. -/
structure UnitCellFilling {q : ℕ} {B : ℝ} (A : CompatibleCellFaces q B) where
  boundary : Point → Ambient q
  derivative : Point → HarmonicMaps.Gradient 3 q
  memW12 : MemW12 (unitCellCube 3) (cellRadialField boundary) derivative
  ray : ∀ j x, x ∈ (unitCellCube 2).val → ∀ r : ℝ, 0 < r →
    cellRadialField boundary (r • unitCellFacePoint j x 1) = A.face j x
  dirichlet_bound : (∫ y in (unitCellCube 3).val, hsNormSq (derivative y)) ≤
    3 * ∑ j, ∫ x in (unitCellCube 2).val, hsNormSq (A.derivative j x)
  bulk_integral : ∀ b : Ambient q → ℝ≥0∞, Measurable b →
    (∫⁻ y in (unitCellCube 3).val, b (cellRadialField boundary y)) =
      ENNReal.ofReal (1 / 3 : ℝ) * ∑ j, ∫⁻ x in (unitCellCube 2).val, b (A.face j x)
  trace : Fin 3 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict (unitCellCube 2).val))
  trace_slice : ∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
    ∃ h : MemLp (fun x => cellRadialField boundary (unitCellFacePoint (i, true) x t)) 2
        (volume.restrict (unitCellCube 2).val),
      trace i ⟨t, ht.1.le, ht.2.le⟩ = h.toLp _
  trace_end : ∀ i positive,
    (trace i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
      by cases positive <;> norm_num⟩ : Domain 2 → Ambient q) =ᵐ[volume.restrict (unitCellCube 2).val]
      A.face (i, positive)
  values : ∀ P : Ambient q → Prop, (∀ j, ∀ᵐ x ∂volume.restrict (unitCellCube 2).val, P (A.face j x)) →
    ∀ᵐ y ∂volume.restrict (unitCellCube 3).val, P (cellRadialField boundary y)

/-- Six compatible original face graphs give a single Sobolev filling.
The native cone Jacobian gives the bulk factor `1/3`. -/
theorem exists_unitCellFilling {q : ℕ} {B : ℝ} (A : CompatibleCellFaces q B) : Nonempty (UnitCellFilling A) := by
  obtain ⟨G, D, hCap, hW, _, hDir, ⟨trace, hTrace, hEnd⟩, hVals⟩ :=
    StratificationTheory.exists_cubical_face_family_extension (n := 0)
      A.face A.derivative A.edge A.face_memW12 B A.face_bound A.trace A.trace_slice A.trace_edge
  have hCap' : ∀ j x, x ∈ (unitCellCube 2).val → G (unitCellFacePoint j x 1) = A.face j x := hCap
  have hWeak : MemW12 (unitCellCube 3) (cellRadialField G) D := hW
  refine ⟨{ boundary := G
            derivative := D
            memW12 := hWeak
            ray := ?_
            dirichlet_bound := ?_
            bulk_integral := ?_
            trace := trace
            trace_slice := hTrace
            trace_end := hEnd
            values := hVals }⟩
  · intro j x hx r hr
    rw [cellRadialField_pos_smul _ hr]
    exact (StratificationTheory.cubical_radial_map_unit_face_value G j.1 j.2 x hx).trans (hCap' j x hx)
  · norm_num at hDir
    exact hDir
  · intro b hb
    have hFace : ∀ j, MemW12 (unitCellCube 2) (fun x => G (unitCellFacePoint j x 1)) (A.derivative j) := by
      intro j
      refine (A.face_memW12 j).congr_ae ?_ (EventuallyEq.refl _ _)
      filter_upwards [ae_restrict_mem (unitCellCube 2).property.measurableSet] with x hx
      exact (hCap' j x hx).symm
    rw [cellRadialField_lintegral G A.derivative hFace b (hb.comp_aemeasurable hWeak.2.1.aemeasurable)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact setLIntegral_congr_fun (unitCellCube 2).property.measurableSet (fun x hx => congrArg b (hCap' j x hx))

/-- Lower vertex of the physical parameter box, in the two tangential
coordinates and the original absolute radius. -/
@[expose] noncomputable def shellCellParameterLower (h : ℝ) : Point :=
  WithLp.toLp 2 ![0, 0, 1 - h]

/-- The physical center of the parameters and the corresponding unit similarity. -/
@[expose] noncomputable def shellCellParameterCenter (h : ℝ) : Point :=
  shellCellParameterLower h + WithLp.toLp 2 (fun _ => h / 2)

@[expose] noncomputable def unitToShellCellParameter (h : ℝ) (x : Point) : Point :=
  shellCellParameterCenter h + (h / 2) • x

@[expose] noncomputable def shellCellParameterToUnit (h : ℝ) (z : Point) : Point :=
  (h / 2)⁻¹ • (z - shellCellParameterCenter h)

@[expose] noncomputable def normalizedShellCellPoint (c : Point) (h : ℝ) (f : TensorGridSquare) (x : Point) : Point :=
  sphericalCellNativePoint c h f (unitToShellCellParameter h x)

theorem shellCellParameterToUnit_unitToShellCellParameter {h : ℝ} (hh : 0 < h) (x : Point) :
    shellCellParameterToUnit h (unitToShellCellParameter h x) = x := by
  simp only [shellCellParameterToUnit, unitToShellCellParameter, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ (half_pos hh).ne', one_smul]

theorem unitToShellCellParameter_mem_box {h : ℝ} (hh : 0 < h) {x : Point}
    (hx : ∀ i : Fin 3, x i ∈ Icc (-1 : ℝ) 1) : unitToShellCellParameter h x ∈ sphericalCellNativeBox h := by
  have hPos : 0 < h / 2 := half_pos hh
  have hHalf (i : Fin 3) : -(h / 2) ≤ (h / 2) * x i ∧ (h / 2) * x i ≤ h / 2 := by
    simpa only [mul_one, mul_neg, mul_neg_one] using And.intro
      (mul_le_mul_of_nonneg_left (hx i).1 hPos.le) (mul_le_mul_of_nonneg_left (hx i).2 hPos.le)
  change (((unitToShellCellParameter h x) 0 ∈ Icc 0 h) ∧ ((unitToShellCellParameter h x) 1 ∈ Icc 0 h)) ∧
    (unitToShellCellParameter h x) 2 ∈ Icc (1 - h) 1
  change ((0 + h / 2 + (h / 2) * x 0 ∈ Icc 0 h) ∧ (0 + h / 2 + (h / 2) * x 1 ∈ Icc 0 h)) ∧
    (1 - h + h / 2 + (h / 2) * x 2 ∈ Icc (1 - h) 1)
  exact ⟨⟨⟨by linarith only [(hHalf 0).1], by linarith only [(hHalf 0).2]⟩,
    ⟨by linarith only [(hHalf 1).1], by linarith only [(hHalf 1).2]⟩⟩,
    ⟨by linarith only [(hHalf 2).1], by linarith only [(hHalf 2).2]⟩⟩

theorem sphericalCellNativeOpenDomain_coord_eq (h : ℝ) :
    (sphericalCellNativeOpenDomain h).val =
      ⋂ i : Fin 3, (EuclideanSpace.proj i) ⁻¹' Ioo (shellCellParameterLower h i) (shellCellParameterLower h i + h) := by
  change interior (sphericalCellNativeParameter ⁻¹' sphericalCellParameterBox h) = _
  rw [← sphericalCellNativeParameter.preimage_interior, sphericalCellParameterBox,
    interior_prod_eq, interior_prod_eq, interior_Icc, interior_Icc]
  ext x
  rw [mem_iInter]
  change ((x 0 ∈ Ioo 0 h ∧ x 1 ∈ Ioo 0 h) ∧ x 2 ∈ Ioo (1 - h) 1) ↔
    ∀ i : Fin 3, x i ∈ Ioo (shellCellParameterLower h i) (shellCellParameterLower h i + h)
  have h₀ : shellCellParameterLower h 0 = 0 := rfl
  have h₁ : shellCellParameterLower h 1 = 0 := rfl
  have h₂ : shellCellParameterLower h 2 = 1 - h := rfl
  have hEnd : 1 - h + h = 1 := by ring
  constructor
  · intro hx i
    fin_cases i
    · change x 0 ∈ Ioo (shellCellParameterLower h 0) (shellCellParameterLower h 0 + h)
      simpa only [h₀, zero_add] using hx.1.1
    · change x 1 ∈ Ioo (shellCellParameterLower h 1) (shellCellParameterLower h 1 + h)
      simpa only [h₁, zero_add] using hx.1.2
    · change x 2 ∈ Ioo (shellCellParameterLower h 2) (shellCellParameterLower h 2 + h)
      simpa only [h₂, hEnd] using hx.2
  · intro hx
    exact ⟨⟨by simpa only [h₀, zero_add] using hx 0, by simpa only [h₁, zero_add] using hx 1⟩,
      by simpa only [h₂, hEnd] using hx 2⟩

private theorem lintegral_comp_scaled_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {F : X → Y} {k : ℝ≥0∞} {g : Y → ℝ≥0∞}
    (hF : Measurable F) (hMap : Measure.map F μ = k • ν) (hg : AEMeasurable g ν) :
    (∫⁻ x, g (F x) ∂μ) = k * ∫⁻ y, g y ∂ν := by
  have hgm : AEMeasurable g (Measure.map F μ) :=
    hg.mono_ac (Measure.absolutelyContinuous_of_le_smul hMap.le)
  rw [← lintegral_map' hgm hF.aemeasurable, hMap, lintegral_smul_measure, smul_eq_mul]

/-- The original face field expressed in physical parameters of length `h`. -/
@[expose] noncomputable def physicalCellFace {q : ℕ} {B : ℝ} (h : ℝ) (A : CompatibleCellFaces q B)
    (j : CellFaceIndex) (x : Domain 2) : Ambient q :=
  A.face j ((h / 2)⁻¹ • (x - WithLp.toLp 2 (fun _ => h / 2)))

@[expose] noncomputable def physicalCellFaceDerivative {q : ℕ} {B : ℝ} (h : ℝ) (A : CompatibleCellFaces q B)
    (j : CellFaceIndex) (x : Domain 2) : HarmonicMaps.Gradient 2 q :=
  fun i => (h / 2)⁻¹ • A.derivative j ((h / 2)⁻¹ • (x - WithLp.toLp 2 (fun _ => h / 2))) i

/-- In the two physical face dimensions, the inverse similarity preserves
the Dirichlet integral. -/
theorem physicalCellFace_memW12_energy {q : ℕ} {B h : ℝ} (hh : 0 < h) (A : CompatibleCellFaces q B)
    (j : CellFaceIndex) :
    MemW12 (tensorGridOpenParameterBox 2 h) (physicalCellFace h A j) (physicalCellFaceDerivative h A j) ∧
      HarmonicMaps.dirichletEnergy (physicalCellFaceDerivative h A j) (tensorGridOpenParameterBox 2 h).val =
        HarmonicMaps.dirichletEnergy (A.derivative j) (unitCellCube 2).val := by
  obtain ⟨hW, hEq, _, _⟩ := StratificationTheory.memW12_positive_cube_denormalization_energy hh
    (A.face j) (A.derivative j) (A.face_memW12 j)
  have hu : MemW12 (tensorGridOpenParameterBox 2 h) (physicalCellFace h A j) (physicalCellFaceDerivative h A j) := hW
  refine ⟨hu, ?_⟩
  simp only [HarmonicMaps.dirichletEnergy]
  rw [← ofReal_integral_eq_lintegral_ofReal hu.integrable_hsNormSq (Eventually.of_forall fun _ => hsNormSq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal (A.face_memW12 j).integrable_hsNormSq (Eventually.of_forall fun _ => hsNormSq_nonneg _)]
  congr 1
  change (∫ y in (tensorGridOpenParameterBox 2 h).val, hsNormSq (physicalCellFaceDerivative h A j y)) =
    (h / 2) ^ ((2 : ℤ) - 2) * ∫ x in (unitCellCube 2).val, hsNormSq (A.derivative j x) at hEq
  rw [show (2 : ℤ) - 2 = 0 by norm_num, zpow_zero, one_mul] at hEq
  exact hEq

/-- The physical face area carries exactly the factor `(h / 2) ^ 2`. -/
theorem physicalCellFace_lintegral {q : ℕ} {B h : ℝ} (hh : 0 < h) (A : CompatibleCellFaces q B)
    (j : CellFaceIndex) {b : Ambient q → ℝ≥0∞} (hb : Measurable b) :
    (∫⁻ x in (tensorGridOpenParameterBox 2 h).val, b (physicalCellFace h A j x)) =
      ENNReal.ofReal ((h / 2) ^ 2) * ∫⁻ x in (unitCellCube 2).val, b (A.face j x) := by
  have hMap := StratificationTheory.map_inverse_affine_unit_cube_volume 2 hh
  exact lintegral_comp_scaled_map (by fun_prop) hMap (hb.comp_aemeasurable (A.face_memW12 j).2.1.aemeasurable)

/-- The same six compatible faces give one native Sobolev graph on an actual
spherical cell. Their physical face energies are measured before the uniform
radial chart distortion. -/
structure SphericalCellFilling {q : ℕ} {B : ℝ} (A : CompatibleCellFaces q B)
    (c : Point) (h : ℝ) (f : TensorGridSquare) where
  unit : UnitCellFilling A
  field : Point → Ambient q
  derivative : Point → HarmonicMaps.Gradient 3 q
  memW12 : MemW12 (sphericalCellOpenDomain c h f) field derivative
  chart_value : ∀ x : Point, (∀ i : Fin 3, x i ∈ Icc (-1 : ℝ) 1) →
    field (normalizedShellCellPoint c h f x) = cellRadialField unit.boundary x
  dirichlet_bound : HarmonicMaps.dirichletEnergy derivative (sphericalCellOpenDomain c h f).val ≤
    (9 * 204 ^ 2 * 65 ^ 3 : ℝ≥0∞) * ENNReal.ofReal (3 * h / 2) *
      ∑ j, HarmonicMaps.dirichletEnergy (physicalCellFaceDerivative h A j) (tensorGridOpenParameterBox 2 h).val
  bulk_bound : ∀ b : Ambient q → ℝ≥0∞, Measurable b →
    (∫⁻ y in (sphericalCellOpenDomain c h f).val, b (field y)) ≤
      (65 ^ 3 : ℝ≥0∞) * ENNReal.ofReal (h / 6) *
        ∑ j, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, b (physicalCellFace h A j x)
  values : ∀ P : Ambient q → Prop, (∀ j, ∀ᵐ x ∂volume.restrict (unitCellCube 2).val, P (A.face j x)) →
    ∀ᵐ y ∂volume.restrict (sphericalCellOpenDomain c h f).val, P (field y)

/-- The exact cone factors become linear mesh-size costs after physical
scaling. The transported field retains the same values on the closed chart. -/
theorem exists_sphericalCellFilling {q : ℕ} {B : ℝ} (A : CompatibleCellFaces q B)
    {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2) {m : ℕ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) : Nonempty (SphericalCellFilling A c h f) := by
  obtain ⟨K⟩ := exists_unitCellFilling A
  let τ := shellCellParameterToUnit h
  let U := sphericalCellNativeOpenDomain h
  let V := sphericalCellOpenDomain c h f
  let P := cellRadialField K.boundary ∘ τ
  let DP : Point → HarmonicMaps.Gradient 3 q := fun x i => (h / 2)⁻¹ • K.derivative (τ x) i
  let S : OpenDomain 3 :=
    ⟨⋂ i : Fin 3, (EuclideanSpace.proj i) ⁻¹' Ioo (shellCellParameterLower h i) (shellCellParameterLower h i + h),
      isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous⟩
  have hU := sphericalCellNativeOpenDomain_coord_eq h
  have hUS : U = S := Subtype.ext hU
  obtain ⟨hSob, hGradScale, hVal⟩ := StratificationTheory.memW12_translated_cube_denormalization_energy hh
    (shellCellParameterLower h) (cellRadialField K.boundary) K.derivative K.memW12
  have hSob' : MemW12 U P DP := by
    rw [hUS]
    exact hSob
  change (∫ y in S.val, hsNormSq (DP y)) =
    (h / 2) ^ ((3 : ℤ) - 2) * ∫ x in (unitCellCube 3).val, hsNormSq (K.derivative x) at hGradScale
  change ∀ R : Ambient q → Prop,
    (∀ᵐ x ∂volume.restrict (unitCellCube 3).val, R (cellRadialField K.boundary x)) →
      ∀ᵐ y ∂volume.restrict S.val, R (P y) at hVal
  rw [← hUS] at hGradScale hVal
  obtain ⟨G, hLeft, _, hTr⟩ := exists_sphericalCellNative_sobolev_transport hh hh' hc hm hf
  let W := P ∘ G
  let DW : Point → HarmonicMaps.Gradient 3 q := fun z i =>
    ∑ j : Fin 3, (fderiv ℝ G z (EuclideanSpace.single i 1)) j • DP (G z) j
  obtain ⟨hWeak, hDir, hProp, hBulk⟩ := hTr hSob'
  refine ⟨{ unit := K
            field := W
            derivative := DW
            memW12 := hWeak
            chart_value := ?_
            dirichlet_bound := ?_
            bulk_bound := ?_
            values := ?_ }⟩
  · intro x hx
    change cellRadialField K.boundary (τ (G (sphericalCellNativePoint c h f (unitToShellCellParameter h x)))) = _
    rw [hLeft (unitToShellCellParameter_mem_box hh hx), show τ (unitToShellCellParameter h x) = x from
      shellCellParameterToUnit_unitToShellCellParameter hh x]
  · have hIntScale : (∫ y in U.val, hsNormSq (DP y)) =
        h / 2 * ∫ x in (unitCellCube 3).val, hsNormSq (K.derivative x) := by
      simpa only [show (3 : ℤ) - 2 = 1 by norm_num, zpow_one] using hGradScale
    have hUnitSum : (∫ y in U.val, hsNormSq (DP y)) ≤
        (3 * h / 2) * ∑ j, ∫ x in (unitCellCube 2).val, hsNormSq (A.derivative j x) := by
      rw [hIntScale]
      calc
        _ ≤ (h / 2) * (3 * ∑ j, ∫ x in (unitCellCube 2).val, hsNormSq (A.derivative j x)) :=
          mul_le_mul_of_nonneg_left K.dirichlet_bound (half_pos hh).le
        _ = _ := by ring
    have hPhysDir : HarmonicMaps.dirichletEnergy DP U.val ≤ ENNReal.ofReal (3 * h / 2) *
        ∑ j, HarmonicMaps.dirichletEnergy (physicalCellFaceDerivative h A j) (tensorGridOpenParameterBox 2 h).val := by
      simp_rw [(physicalCellFace_memW12_energy hh A _).2]
      simp only [HarmonicMaps.dirichletEnergy]
      rw [← ofReal_integral_eq_lintegral_ofReal hSob'.integrable_hsNormSq (Eventually.of_forall fun _ => hsNormSq_nonneg _)]
      refine (ENNReal.ofReal_le_ofReal hUnitSum).trans_eq ?_
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
        integral_nonneg fun _ => hsNormSq_nonneg _)]
      congr 1
      exact Finset.sum_congr rfl fun j _ => ofReal_integral_eq_lintegral_ofReal
        (A.face_memW12 j).integrable_hsNormSq (Eventually.of_forall fun _ => hsNormSq_nonneg _)
    exact hDir.trans ((mul_le_mul_right hPhysDir _).trans_eq (by simp only [mul_assoc]))
  · intro b hb
    have hB : AEMeasurable (b ∘ P) (volume.restrict U.val) := hb.comp_aemeasurable hSob'.2.1.aemeasurable
    have hMap : Measure.map τ (volume.restrict U.val) =
        ENNReal.ofReal ((h / 2) ^ 3) • volume.restrict (unitCellCube 3).val := by
      rw [hU]
      exact StratificationTheory.map_inverse_translated_cube_volume 3 hh (shellCellParameterLower h)
    have hMeas : Measurable τ := by
      change Measurable (fun z : Point => (h / 2)⁻¹ • (z - shellCellParameterCenter h))
      exact (((continuous_id : Continuous (id : Point → Point)).sub
        (continuous_const : Continuous fun _ : Point => shellCellParameterCenter h)).const_smul (h / 2)⁻¹).measurable
    have hBulkPhys := lintegral_comp_scaled_map hMeas hMap (hb.comp_aemeasurable K.memW12.2.1.aemeasurable)
    change (∫⁻ x in U.val, b (P x)) = ENNReal.ofReal ((h / 2) ^ 3) *
      ∫⁻ y in (unitCellCube 3).val, b (cellRadialField K.boundary y) at hBulkPhys
    rw [K.bulk_integral b hb, ← mul_assoc] at hBulkPhys
    have hCoeff : ENNReal.ofReal ((h / 2) ^ 3) * ENNReal.ofReal (1 / 3) =
        ENNReal.ofReal (h / 6) * ENNReal.ofReal ((h / 2) ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (h / 2) ^ 3),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ h / 6)]
      congr 1
      ring
    rw [hCoeff, mul_assoc, Finset.mul_sum (a := ENNReal.ofReal ((h / 2) ^ 2))] at hBulkPhys
    simp_rw [← physicalCellFace_lintegral hh A _ hb] at hBulkPhys
    exact (hBulk b hB).trans_eq (by rw [hBulkPhys]; simp only [mul_assoc])
  · intro P hP
    exact hProp P (hVal P (K.values P hP))

theorem unitCellFacePoint_mem_closed {x : Domain 2} (hx : x ∈ (unitCellCube 2).val)
    (j : CellFaceIndex) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ∀ i : Fin 3, unitCellFacePoint j x t i ∈ Icc (-1 : ℝ) 1 := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let z := e.symm (x, EuclideanSpace.single (0 : Fin 1) t)
  let Q := StratificationTheory.cubicalSignedFaceIsometry 2 j.1 j.2
  have hZ : e z = (x, EuclideanSpace.single (0 : Fin 1) t) := e.apply_symm_apply _
  have hNorm : ‖WithLp.ofLp z‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · change ‖(e z).2 0‖ ≤ 1
      rw [hZ]
      simpa only [PiLp.single_apply, ite_true, Real.norm_eq_abs] using abs_le.mpr ht
    · change ‖(e z).1 k‖ ≤ 1
      rw [hZ, Real.norm_eq_abs]
      exact ((StratificationTheory.mem_unit_coordinate_face_iff x).mp hx k).le
  have hBound : ‖WithLp.ofLp (unitCellFacePoint j x t)‖ ≤ 1 := by
    change ‖WithLp.ofLp (Q z)‖ ≤ 1
    rw [StratificationTheory.cubicalSignedFaceIsometry_coordinate_norm j.1 j.2 z]
    exact hNorm
  intro i
  apply abs_le.mp
  simpa only [Real.norm_eq_abs] using
    (norm_le_pi_norm (WithLp.ofLp (unitCellFacePoint j x t)) i).trans hBound

/-- A point of the actual signed shell-cell face has the prescribed original
boundary value in its signed face coordinates. -/
theorem SphericalCellFilling.face_value {q : ℕ} {B h : ℝ} {A : CompatibleCellFaces q B}
    {c : Point} {f : TensorGridSquare} (W : SphericalCellFilling A c h f) (j : CellFaceIndex)
    {x : Domain 2} (hx : x ∈ (unitCellCube 2).val) :
    W.field (normalizedShellCellPoint c h f (unitCellFacePoint j x 1)) = A.face j x := by
  rw [W.chart_value _ (unitCellFacePoint_mem_closed hx j (by constructor <;> norm_num : (1 : ℝ) ∈ Icc (-1) 1))]
  simpa only [one_smul] using W.unit.ray j x hx 1 (by norm_num)

/-- The actual transported field has the same continuous transverse face
traces in the closed coordinates of the cell. -/
theorem SphericalCellFilling.trace_slice {q : ℕ} {B h : ℝ} {A : CompatibleCellFaces q B}
    {c : Point} {f : TensorGridSquare} (W : SphericalCellFilling A c h f) (i : Fin 3) :
    ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ htLp : MemLp (fun x => W.field (normalizedShellCellPoint c h f (unitCellFacePoint (i, true) x t))) 2
        (volume.restrict (unitCellCube 2).val),
        W.unit.trace i ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp _ := by
  filter_upwards [W.unit.trace_slice i] with t htG ht
  obtain ⟨hLp, hTrace⟩ := htG ht
  have hEq : (fun x => W.field (normalizedShellCellPoint c h f (unitCellFacePoint (i, true) x t)))
      =ᵐ[volume.restrict (unitCellCube 2).val]
        fun x => cellRadialField W.unit.boundary (unitCellFacePoint (i, true) x t) := by
    filter_upwards [ae_restrict_mem (unitCellCube 2).property.measurableSet] with x hx
    exact W.chart_value _ (unitCellFacePoint_mem_closed hx (i, true) (Ioo_subset_Icc_self ht))
  have hLp' := (memLp_congr_ae hEq).mpr hLp
  exact ⟨hLp', hTrace.trans (MemLp.toLp_congr hLp hLp' hEq.symm)⟩

/-- The physical tangential similarity from the centered unit face to the
square with coordinates between `0` and `h`. -/
@[expose] noncomputable def unitToPhysicalCellFace (h : ℝ) (x : Domain 2) : Domain 2 :=
  WithLp.toLp 2 (fun _ => h / 2) + (h / 2) • x

/-- Physical native face maps and columns, with the shared edge classes in
the normalized coordinate curves used for the cubical extension. -/
structure CompatiblePhysicalCellFaces (q : ℕ) (B h : ℝ) where
  face : CellFaceIndex → Domain 2 → Ambient q
  derivative : CellFaceIndex → Domain 2 → HarmonicMaps.Gradient 2 q
  face_memW12 : ∀ j, MemW12 (tensorGridOpenParameterBox 2 h) (face j) (derivative j)
  face_bound : ∀ j, ∀ᵐ x ∂volume.restrict (tensorGridOpenParameterBox 2 h).val, ‖face j x‖ ≤ B
  edge : Point → Ambient q
  trace : CellFaceIndex → Fin 2 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict (unitCellCube 1).val))
  trace_slice : ∀ j i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
    ∃ hLp : MemLp (fun x => face j (unitToPhysicalCellFace h (unitCellFaceSlice i x t))) 2
        (volume.restrict (unitCellCube 1).val),
      trace j i ⟨t, ht.1.le, ht.2.le⟩ = hLp.toLp _
  trace_edge : ∀ j i positive,
    (trace j i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
      by cases positive <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict (unitCellCube 1).val]
      fun x => edge (unitToShellCellParameter h (unitCellEdgePoint j i positive x))

/-- Normalize just the coordinates of the same physical face graphs and
the same shared edge data. -/
noncomputable def CompatiblePhysicalCellFaces.toUnit {q : ℕ} {B h : ℝ}
    (A : CompatiblePhysicalCellFaces q B h) (hh : 0 < h) : CompatibleCellFaces q B where
  face j := A.face j ∘ unitToPhysicalCellFace h
  derivative j x i := (h / 2) • A.derivative j (unitToPhysicalCellFace h x) i
  face_memW12 j := (StratificationTheory.memW12_unit_cube_normalization_energy hh (A.face_memW12 j)).1
  face_bound j := (StratificationTheory.memW12_unit_cube_normalization_energy hh (A.face_memW12 j)).2.2.2
    (fun y => ‖y‖ ≤ B) (A.face_bound j)
  edge := A.edge ∘ unitToShellCellParameter h
  trace := A.trace
  trace_slice := A.trace_slice
  trace_edge := A.trace_edge

theorem CompatiblePhysicalCellFaces.toUnit_face {q : ℕ} {B h : ℝ}
    (A : CompatiblePhysicalCellFaces q B h) (hh : 0 < h) (j : CellFaceIndex) :
    (A.toUnit hh).face j = A.face j ∘ unitToPhysicalCellFace h := by
  simp only [CompatiblePhysicalCellFaces.toUnit]

theorem unitToPhysicalCellFace_inverse {h : ℝ} (hh : 0 < h) (x : Domain 2) :
    unitToPhysicalCellFace h ((h / 2)⁻¹ • (x - WithLp.toLp 2 (fun _ => h / 2))) = x := by
  unfold unitToPhysicalCellFace
  rw [smul_smul, mul_inv_cancel₀ (half_pos hh).ne', one_smul]
  abel

/-- Returning to the physical face recovers exactly the original map and columns. -/
theorem CompatiblePhysicalCellFaces.physical_eq {q : ℕ} {B h : ℝ}
    (A : CompatiblePhysicalCellFaces q B h) (hh : 0 < h) (j : CellFaceIndex) :
    physicalCellFace h (A.toUnit hh) j = A.face j ∧
      physicalCellFaceDerivative h (A.toUnit hh) j = A.derivative j := by
  constructor
  · funext x
    change A.face j (unitToPhysicalCellFace h ((h / 2)⁻¹ • (x - WithLp.toLp 2 (fun _ => h / 2)))) = _
    rw [unitToPhysicalCellFace_inverse hh]
  · funext x i
    change (h / 2)⁻¹ • ((h / 2) • A.derivative j
      (unitToPhysicalCellFace h ((h / 2)⁻¹ • (x - WithLp.toLp 2 (fun _ => h / 2)))) i) = _
    rw [unitToPhysicalCellFace_inverse hh, smul_smul, inv_mul_cancel₀ (half_pos hh).ne', one_smul]

@[expose] noncomputable def SphericalCellFilling.tensorField {B h : ℝ} {A : CompatibleCellFaces 5 B}
    {c : Point} {f : TensorGridSquare} (W : SphericalCellFilling A c h f) (x : Point) : S0 :=
  frobeniusCoordinateEquiv.symm (W.field x)

@[expose] noncomputable def SphericalCellFilling.tensorDerivative {B h : ℝ} {A : CompatibleCellFaces 5 B}
    {c : Point} {f : TensorGridSquare} (W : SphericalCellFilling A c h f) : Point → Thesis.Gradient :=
  fun x i => frobeniusCoordinateEquiv.symm (W.derivative x i)

private theorem SphericalCellFilling.frobenius_tensorField {B h : ℝ} {A : CompatibleCellFaces 5 B}
    {c : Point} {f : TensorGridSquare} (W : SphericalCellFilling A c h f) :
    frobeniusField W.tensorField = W.field :=
  funext fun x => frobeniusCoordinateEquiv.apply_symm_apply (W.field x)

private theorem SphericalCellFilling.frobenius_tensorDerivative {B h : ℝ} {A : CompatibleCellFaces 5 B}
    {c : Point} {f : TensorGridSquare} (W : SphericalCellFilling A c h f) :
    frobeniusGradient W.tensorDerivative = W.derivative :=
  funext fun x => funext fun i => frobeniusCoordinateEquiv.apply_symm_apply (W.derivative x i)

/-- The same filled weak graph in Frobenius tensor coordinates. -/
theorem SphericalCellFilling.tensor_memH1 {B h : ℝ} {A : CompatibleCellFaces 5 B}
    {c : Point} {f : TensorGridSquare} (W : SphericalCellFilling A c h f) :
    MemH1 (sphericalCellOpenDomain c h f).val W.tensorField W.tensorDerivative := by
  apply (memH1_iff_memW12 (sphericalCellOpenDomain c h f) _ _).mpr
  rw [W.frobenius_tensorField, W.frobenius_tensorDerivative]
  exact W.memW12

/-- The local tensor filling has linear mesh-size bounds for both parts of
the thesis's penalized energy, using the same six physical face data. -/
theorem SphericalCellFilling.tensor_energy_bound {B h : ℝ} {A : CompatibleCellFaces 5 B}
    {c : Point} {f : TensorGridSquare} (W : SphericalCellFilling A c h f)
    (a : BulkCoefficients) (ε : ElasticScale) :
    energy a ε (sphericalCellOpenDomain c h f).val W.tensorField W.tensorDerivative ≤
      ENNReal.ofReal (1 / 2 : ℝ) *
        ((9 * 204 ^ 2 * 65 ^ 3 : ℝ≥0∞) * ENNReal.ofReal (3 * h / 2) *
          ∑ j, HarmonicMaps.dirichletEnergy (physicalCellFaceDerivative h A j) (tensorGridOpenParameterBox 2 h).val) +
      (65 ^ 3 : ℝ≥0∞) * ENNReal.ofReal (h / 6) *
        ∑ j, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val,
          ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm (physicalCellFace h A j x))) := by
  let b : Ambient 5 → ℝ≥0∞ := fun z => ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm z))
  have hCont : Continuous (fun z : Ambient 5 => (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm z)) :=
    continuous_const.mul ((contDiff_bulkPotential a).continuous.comp frobeniusCoordinateEquiv.symm.continuous)
  have hBulk := W.bulk_bound b hCont.measurable.ennreal_ofReal
  have hEnergy := W.tensor_memH1
  rw [energy_eq_dirichlet_add_scaledPotential a ε _ hEnergy.2.1, dirichletEnergy_eq_half_upstream,
    W.frobenius_tensorDerivative, eLpNorm_one_eq_lintegral_enorm]
  refine add_le_add (mul_le_mul_right W.dirichlet_bound _) ?_
  refine le_trans ?_ hBulk
  apply le_of_eq
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _))]
  rfl

end Thesis
