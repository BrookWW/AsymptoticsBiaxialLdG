module

public import Thesis.Interpolation.CubicalCellFilling
public import Thesis.Interpolation.PenalizedSphereFaces
import StratificationTheory.Foundation.UnitSquareCoordinateTraces
import StratificationTheory.Foundation.BoundedFiberL2Trace
import StratificationTheory.Foundation.UnitSquareCoordinateSwap

/-! Both coordinate curves of a physical cell face and their common edge traces. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal Topology Matrix.Norms.Frobenius

namespace Thesis

/-- The signed square coordinates agree with the two literal coordinate
slices of the physical square. -/
theorem unitCellFaceSlice_coordinates (i : Fin 2) (x : Domain 1) (t : ℝ) :
    unitCellFaceSlice i x t = if i = 0 then WithLp.toLp 2 ![t, x 0] else WithLp.toLp 2 ![x 0, t] := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
  have hPair : e.symm (x, EuclideanSpace.single 0 t) = WithLp.toLp 2 ![x 0, t] := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext <;> ext j <;> fin_cases j <;> rfl
  change StratificationTheory.cubicalSignedFaceIsometry 1 i true
    (e.symm (x, EuclideanSpace.single 0 t)) = _
  rw [hPair]
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [StratificationTheory.cubicalSignedFaceIsometry_coordinate, Fin.last]

/-- The tangential parameter of a normalized edge in the original interval. -/
@[expose] noncomputable def unitEdgeToPhysical (h : ℝ) (x : Domain 1) : ℝ := h / 2 + (h / 2) * x 0

/-- Physical face curves with actual common edge representatives on the
four sides. Each endpoint is also the restriction of the original face. -/
structure PhysicalSquareTraces {q : ℕ} (h : ℝ) (u : Domain 2 → Ambient q)
    (edge : Fin 2 → Bool → ℝ → Ambient q) where
  ht_pos : 0 < h
  curve : Fin 2 → C(Icc (0 : ℝ) h, Lp (Ambient q) 2 (volume.restrict (tensorGridOpenParameterBox 1 h).val))
  slice : ∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) h,
    ∃ htLp : MemLp (fun x => u (unitCellFaceSlice i x t)) 2 (volume.restrict (tensorGridOpenParameterBox 1 h).val),
      curve i ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp _
  curve_edge : ∀ i positive,
    (curve i ⟨if positive then h else 0, by cases positive <;> simp [ht_pos.le],
      by cases positive <;> simp [ht_pos.le]⟩ : Domain 1 → Ambient q)
      =ᵐ[volume.restrict (tensorGridOpenParameterBox 1 h).val] fun x => edge i positive (x 0)
  face_edge : ∀ i positive,
    (fun x : Domain 1 => u (unitCellFaceSlice i x (if positive then h else 0)))
      =ᵐ[volume.restrict (tensorGridOpenParameterBox 1 h).val] fun x => edge i positive (x 0)

/-- The same physical square and edge representatives in the centered unit
coordinates of the six-face filling. -/
structure NormalizedSquareTraces {q : ℕ} (h : ℝ) (u : Domain 2 → Ambient q)
    (edge : Fin 2 → Bool → ℝ → Ambient q) where
  curve : Fin 2 → C(Icc (-1 : ℝ) 1, Lp (Ambient q) 2 (volume.restrict (unitCellCube 1).val))
  slice : ∀ i, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
    ∃ htLp : MemLp (fun x => u (unitToPhysicalCellFace h (unitCellFaceSlice i x t))) 2
        (volume.restrict (unitCellCube 1).val), curve i ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp _
  edge : ∀ i positive,
    (curve i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
      by cases positive <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict (unitCellCube 1).val]
      fun x => edge i positive (unitEdgeToPhysical h x)

/-- The native affine normalization preserves both coordinate curves and
all four actual edge classes. -/
theorem PhysicalSquareTraces.exists_normalized {q : ℕ} {h : ℝ} {u : Domain 2 → Ambient q}
    {g : Fin 2 → Bool → ℝ → Ambient q} (T : PhysicalSquareTraces h u g) :
    Nonempty (NormalizedSquareTraces h u g) := by
  let μ := volume.restrict (tensorGridOpenParameterBox 1 h).val
  have hEnd (i : Fin 2) (positive : Bool) :
      ∃ hs : MemLp (fun x => u (unitCellFaceSlice i x (if positive then h else 0))) 2 μ,
        T.curve i ⟨if positive then h else 0, by cases positive <;> simp [T.ht_pos.le],
          by cases positive <;> simp [T.ht_pos.le]⟩ = hs.toLp _ := by
    let K := T.curve i ⟨if positive then h else 0, by cases positive <;> simp [T.ht_pos.le],
      by cases positive <;> simp [T.ht_pos.le]⟩
    have hEq := (T.curve_edge i positive).trans (T.face_edge i positive).symm
    have hMem := (Lp.memLp K).ae_eq hEq
    refine ⟨hMem, ?_⟩
    apply Lp.ext
    exact hEq.trans hMem.coeFn_toLp.symm
  obtain ⟨K, hK, hEndK⟩ := StratificationTheory.exists_unit_square_coordinate_traces T.ht_pos u T.curve T.slice hEnd
  refine ⟨{ curve := K, slice := hK, edge := ?_ }⟩
  intro i positive
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
  let θ : Domain 1 → Domain 1 := fun x => WithLp.toLp 2 (fun _ => h / 2) + (h / 2) • x
  have hθm : Measurable θ := by
    change Measurable (fun x : Domain 1 => WithLp.toLp 2 (fun _ => h / 2) + (h / 2) • x)
    fun_prop
  have hMap := StratificationTheory.map_affine_unit_cube_volume 1 T.ht_pos
  have hm : Measure.map θ (volume.restrict (unitCellCube 1).val) =
      ENNReal.ofReal (((h / 2) ^ (1 : ℕ))⁻¹) • μ := hMap
  have hQ : Measure.QuasiMeasurePreserving θ (volume.restrict (unitCellCube 1).val) μ :=
    ⟨hθm, Measure.absolutelyContinuous_of_le_smul hm.le⟩
  obtain ⟨hs, hEq⟩ := hEndK i positive
  have hGeom (x : Domain 1) : unitToPhysicalCellFace h
        (StratificationTheory.cubicalSignedFaceIsometry 1 i positive (e.symm (x, EuclideanSpace.single 0 1))) =
        unitCellFaceSlice i (θ x) (if positive then h else 0) :=
    StratificationTheory.affine_unit_square_axis_endpoint i positive h x
  have hEq' : (K i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
      by cases positive <;> norm_num⟩ : Domain 1 → Ambient q) =ᵐ[volume.restrict (unitCellCube 1).val]
      fun x => u (unitCellFaceSlice i (θ x) (if positive then h else 0)) := by
    rw [hEq]
    exact hs.coeFn_toLp.trans (Eventually.of_forall fun x => congrArg u (hGeom x))
  exact hEq'.trans (hQ.ae (T.face_edge i positive))

/-- The selected edge at a given signed endpoint of one square coordinate. -/
@[expose] def tensorSquareCoordinateEdge {m : ℕ} (f : ↥(cubeBoundarySquares m))
    (i : Fin 2) (positive : Bool) : ↥(cubeBoundaryEdges m) :=
  if i = 0 then (if positive then tensorSquareRightEdge f else tensorSquareLeftEdge f)
  else (if positive then tensorSquareUpperEdge f else tensorSquareLowerEdge f)

private theorem oneBox_eq (h : ℝ) :
    (tensorGridOpenParameterBox 1 h).val = (fun x : Domain 1 => x 0) ⁻¹' Ioo (0 : ℝ) h := by
  ext x
  exact ⟨fun hx => mem_iInter.mp hx 0, fun hx => mem_iInter.mpr (fun i => Subsingleton.elim (0 : Fin 1) i ▸ hx)⟩

/-- The original tensor face has the same almost-everywhere value as the
actual edge representative on each of its four sides. -/
theorem PenalizedSphereFaces.face_eq_edge {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0}
    {hv : MemSphereH1 v} (G : PenalizedSphereFaces a B h v hv) (f : ↥(cubeBoundarySquares G.grid.level))
    (i : Fin 2) (positive : Bool) :
    (fun x => G.face f (unitCellFaceSlice i x (if positive then h else 0)))
      =ᵐ[volume.restrict (tensorGridOpenParameterBox 1 h).val]
        fun x => G.grid.trace (tensorSquareCoordinateEdge f i positive) (x 0) := by
  let e := tensorSquareCoordinateEdge f i positive
  have hEdgeAE := (StratificationTheory.measurePreserving_domainOne_eval.restrict_preimage
    (measurableSet_Ioo (a := 0) (b := h))).quasiMeasurePreserving.ae (G.grid.trace_ae e)
  rw [← oneBox_eq] at hEdgeAE
  filter_upwards [hEdgeAE, ae_restrict_mem (tensorGridOpenParameterBox 1 h).property.measurableSet]
    with x hx hxBox
  have hx₀ : x 0 ∈ Icc (0 : ℝ) h := Ioo_subset_Icc_self (mem_iInter.mp hxBox 0)
  have ht : (if positive then h else 0) ∈ Icc (0 : ℝ) h := by cases positive <;> simp [G.ht_pos.le]
  let y := unitCellFaceSlice i x (if positive then h else 0)
  have hy₀ : y 0 ∈ Icc (0 : ℝ) h := by
    change unitCellFaceSlice i x (if positive then h else 0) 0 ∈ _
    fin_cases i <;> simp [unitCellFaceSlice_coordinates, hx₀, ht]
  have hy₁ : y 1 ∈ Icc (0 : ℝ) h := by
    change unitCellFaceSlice i x (if positive then h else 0) 1 ∈ _
    fin_cases i <;> simp [unitCellFaceSlice_coordinates, hx₀, ht]
  have hPoint : tensorGridSquarePoint (tensorGridVertex G.grid.center h f.val.1) f.val.2 (y 0) (y 1) =
      tensorGridEdgePoint G.grid.center h e.val (x 0) := by
    obtain ⟨hBottom, hTop, hLeft, hRight⟩ := tensorGridSquarePoint_boundary G.grid.center h f.val (x 0)
    fin_cases i <;> cases positive <;>
      simpa [y, e, unitCellFaceSlice_coordinates, tensorSquareCoordinateEdge, tensorSquareLeftEdge,
        tensorSquareRightEdge, tensorSquareLowerEdge, tensorSquareUpperEdge] using ‹_›
  obtain ⟨θ, hθ, hFace⟩ := G.face_eq f y hy₀ hy₁
  obtain ⟨η, hη, hTrace⟩ := hx
  have hEq : θ = η := Subtype.ext (hθ.trans ((congrArg NormedSpace.normalize hPoint).trans hη.symm))
  exact hFace.trans (hEq ▸ hTrace.symm)

private theorem encodeTensorLp_toLp {μ : Measure (Domain 1)} {f : Domain 1 → S0}
    (hf : MemLp f 2 μ) :
    let L := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    L.compLpL 2 μ (hf.toLp f) = (hf.continuousLinearMap_comp L).toLp (fun x => L (f x)) := by
  intro L
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (μ := μ) (hf.toLp f), hf.coeFn_toLp,
    (hf.continuousLinearMap_comp L).coeFn_toLp] with x hL hF hNew
  exact hL.trans ((congrArg L hF).trans hNew.symm)

/-- Both upper-face coordinate curves encode to the native target with the
same four selected edge representatives. -/
theorem PenalizedSphereFaces.exists_physical_traces {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0}
    {hv : MemSphereH1 v} (G : PenalizedSphereFaces a B h v hv) (f : ↥(cubeBoundarySquares G.grid.level)) :
    Nonempty (PhysicalSquareTraces h (fun x => frobeniusCoordinateEquiv (G.face f x))
      (fun i b t => frobeniusCoordinateEquiv (G.grid.trace (tensorSquareCoordinateEdge f i b) t))) := by
  obtain ⟨H₁, h₁, hBot, hTop⟩ := G.face_trace f
  obtain ⟨H₀, h₀, hLeft, hRight⟩ := G.face_trace_cross f
  let μ := volume.restrict (tensorGridOpenParameterBox 1 h).val
  let L := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let H : Fin 2 → C(Icc (0 : ℝ) h, Lp S0 2 μ) := fun i => if i = 0 then H₀ else H₁
  let K : Fin 2 → C(Icc (0 : ℝ) h, Lp (Ambient 5) 2 μ) := fun i =>
    ⟨fun t => L.compLpL 2 μ (H i t), (L.compLpL 2 μ).continuous.comp (H i).continuous⟩
  have hSlice (i : Fin 2) : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) h,
      ∃ hs : MemLp (fun x => G.face f (unitCellFaceSlice i x t)) 2 μ,
        H i ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp _ := by
    fin_cases i
    · simpa [H, unitCellFaceSlice_coordinates] using! h₀
    · simpa [H, unitCellFaceSlice_coordinates] using! h₁
  have hEnd (i : Fin 2) (b : Bool) :
      ∃ hs : MemLp (fun x : Domain 1 => G.grid.trace (tensorSquareCoordinateEdge f i b) (x 0)) 2 μ,
        H i ⟨if b then h else 0, by cases b <;> simp [G.ht_pos.le],
          by cases b <;> simp [G.ht_pos.le]⟩ = hs.toLp _ := by
    fin_cases i <;> cases b
    · simpa [H, tensorSquareCoordinateEdge] using! hLeft
    · simpa [H, tensorSquareCoordinateEdge] using! hRight
    · simpa [H, tensorSquareCoordinateEdge] using! hBot
    · simpa [H, tensorSquareCoordinateEdge] using! hTop
  refine ⟨{ ht_pos := G.ht_pos
            curve := K
            slice := ?_
            curve_edge := ?_
            face_edge := ?_ }⟩
  · intro i
    filter_upwards [hSlice i] with t ht htI
    obtain ⟨hs, hH⟩ := ht htI
    refine ⟨hs.continuousLinearMap_comp L, ?_⟩
    change L.compLpL 2 μ (H i ⟨t, htI.1.le, htI.2.le⟩) = _
    rw [hH]
    exact encodeTensorLp_toLp hs
  · intro i b
    obtain ⟨hs, hH⟩ := hEnd i b
    change ((L.compLpL 2 μ (H i ⟨if b then h else 0, by cases b <;> simp [G.ht_pos.le],
      by cases b <;> simp [G.ht_pos.le]⟩) : Lp (Ambient 5) 2 μ) : Domain 1 → Ambient 5)
      =ᵐ[μ] _
    rw [hH, encodeTensorLp_toLp hs]
    exact (hs.continuousLinearMap_comp L).coeFn_toLp
  · intro i b
    exact (G.face_eq_edge f i b).mono (fun _ hx => congrArg frobeniusCoordinateEquiv hx)

/-- The original upper face and its actual four mesh edges fit the unit
signed coordinate API of cell filling. -/
theorem PenalizedSphereFaces.exists_normalized_traces {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0}
    {hv : MemSphereH1 v} (G : PenalizedSphereFaces a B h v hv) (f : ↥(cubeBoundarySquares G.grid.level)) :
    Nonempty (NormalizedSquareTraces h (fun x => frobeniusCoordinateEquiv (G.face f x))
      (fun i b t => frobeniusCoordinateEquiv (G.grid.trace (tensorSquareCoordinateEdge f i b) t))) := by
  obtain ⟨T⟩ := G.exists_physical_traces f
  exact T.exists_normalized

private theorem continuous_unitCellFaceSlice (i : Fin 2) :
    Continuous (fun p : Domain 1 × ℝ => unitCellFaceSlice i p.1 p.2) := by
  have hSingle : Continuous (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) := by
    have heq (t : ℝ) : EuclideanSpace.single (0 : Fin 1) t = t • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
      apply PiLp.ext
      intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp only [PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one]
    rw [funext heq]
    exact continuous_id.smul continuous_const
  exact (StratificationTheory.cubicalSignedFaceIsometry 1 i true).continuous.comp
    ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).symm.continuous.comp
      (continuous_fst.prodMk (hSingle.comp continuous_snd)))

private theorem unitCellFaceSlice_mem_square {h : ℝ} (i : Fin 2) {x : Domain 1} {t : ℝ}
    (hx : x 0 ∈ Icc (0 : ℝ) h) (ht : t ∈ Icc (0 : ℝ) h) :
    unitCellFaceSlice i x t ∈ sphericalFaceParameterBox h := by
  fin_cases i
  · rw [unitCellFaceSlice_coordinates]
    exact ⟨ht, hx⟩
  · rw [unitCellFaceSlice_coordinates]
    exact ⟨hx, ht⟩

/-- A continuous bounded physical side has both native continuous L² curves
with its literal four edge data. -/
theorem exists_physicalSquareTraces_of_continuousOn {q : ℕ} {h B : ℝ} (hh : 0 < h)
    {u : Domain 2 → Ambient q} (hu : ContinuousOn u (sphericalFaceParameterBox h))
    (hB : ∀ x ∈ sphericalFaceParameterBox h, ‖u x‖ ≤ B)
    {edge : Fin 2 → Bool → ℝ → Ambient q}
    (he : ∀ i positive (x : Domain 1), x 0 ∈ Icc (0 : ℝ) h →
      u (unitCellFaceSlice i x (if positive then h else 0)) = edge i positive (x 0)) :
    Nonempty (PhysicalSquareTraces h u edge) := by
  let S := (tensorGridOpenParameterBox 1 h).val
  let μ := volume.restrict S
  have hVol : (volume : Measure (Domain 1)) S ≠ ⊤ := by
    exact (StratificationTheory.volume_native_positive_cube 1 hh).trans_ne ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hVol
  have hX (x : Domain 1) (hx : x ∈ S) : x 0 ∈ Icc (0 : ℝ) h :=
    Ioo_subset_Icc_self (mem_iInter.mp hx 0)
  let f (i : Fin 2) (p : Domain 1 × ℝ) := u (unitCellFaceSlice i p.1 p.2)
  have hOne (i : Fin 2) : ∃ H : C(Icc (0 : ℝ) h, Lp (Ambient q) 2 μ),
      ∀ t : Icc (0 : ℝ) h, ∃ htLp : MemLp (fun x => f i (x, t.val)) 2 μ, H t = htLp.toLp _ := by
    have hMeas : ∀ᵐ t : ℝ ∂volume, ∀ _ht : t ∈ Ioo (0 : ℝ) h,
        AEStronglyMeasurable (fun x => f i (x, t)) μ := by
      refine Eventually.of_forall fun t ht => ?_
      have hc : ContinuousOn (fun x : Domain 1 => u (unitCellFaceSlice i x t)) S :=
        hu.comp ((continuous_unitCellFaceSlice i).comp (continuous_id.prodMk continuous_const)).continuousOn
          (fun x hx => unitCellFaceSlice_mem_square i (hX x hx) (Ioo_subset_Icc_self ht))
      exact hc.aestronglyMeasurable (tensorGridOpenParameterBox 1 h).property.measurableSet
    have hCont : ∀ᵐ x ∂μ, ContinuousOn (fun t => f i (x, t)) (Icc (0 : ℝ) h) := by
      filter_upwards [ae_restrict_mem (tensorGridOpenParameterBox 1 h).property.measurableSet] with x hx
      exact hu.comp ((continuous_unitCellFaceSlice i).comp (continuous_const.prodMk continuous_id)).continuousOn
        (fun t ht => unitCellFaceSlice_mem_square i (hX x hx) ht)
    have hBound : ∀ᵐ x ∂μ, ∀ t ∈ Icc (0 : ℝ) h, ‖f i (x, t)‖ ≤ B := by
      filter_upwards [ae_restrict_mem (tensorGridOpenParameterBox 1 h).property.measurableSet] with x hx
      exact fun t ht => hB _ (unitCellFaceSlice_mem_square i (hX x hx) ht)
    obtain ⟨H, hH, _⟩ := StratificationTheory.exists_continuous_L2_trace_of_bounded_fiber_continuity μ hh
      hMeas hCont hBound
    exact ⟨H, hH⟩
  choose K hK using hOne
  have hEdges (i : Fin 2) (b : Bool) :
      (fun x : Domain 1 => u (unitCellFaceSlice i x (if b then h else 0))) =ᵐ[μ]
        fun x => edge i b (x 0) := by
    filter_upwards [ae_restrict_mem (tensorGridOpenParameterBox 1 h).property.measurableSet] with x hx
    exact he i b x (hX x hx)
  refine ⟨{ ht_pos := hh
            curve := K
            slice := fun i => Eventually.of_forall fun t ht => hK i ⟨t, ht.1.le, ht.2.le⟩
            face_edge := hEdges
            curve_edge := ?_ }⟩
  intro i b
  let t : Icc (0 : ℝ) h := ⟨if b then h else 0, by cases b <;> simp [hh.le], by cases b <;> simp [hh.le]⟩
  obtain ⟨hMem, hH⟩ := hK i t
  change ((K i t : Lp (Ambient q) 2 μ) : Domain 1 → Ambient q) =ᵐ[μ] _
  rw [hH]
  exact hMem.coeFn_toLp.trans (hEdges i b)

/-- The coordinate permutation needed when a side face lists the radial
coordinate before its edge coordinate. -/
@[expose] noncomputable def physicalSquareSwap : Domain 2 ≃ₗᵢ[ℝ] Domain 2 :=
  StratificationTheory.cubicalSignedFaceIsometry 1 (0 : Fin 2) true

theorem physicalSquareSwap_coordinates (x : Domain 2) :
    physicalSquareSwap x 0 = x 1 ∧ physicalSquareSwap x 1 = x 0 := by
  exact ⟨(StratificationTheory.unit_square_coordinate_swap.1 x).1,
    (StratificationTheory.unit_square_coordinate_swap.1 x).2.1⟩

private theorem physicalSquareSwap_slice (i : Fin 2) (x : Domain 1) (t : ℝ) :
    physicalSquareSwap (unitCellFaceSlice i x t) = unitCellFaceSlice (Equiv.swap 0 1 i) x t := by
  apply PiLp.ext
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [unitCellFaceSlice_coordinates, physicalSquareSwap_coordinates]

private theorem physicalSquareSwap_affine (h : ℝ) (x : Domain 2) :
    physicalSquareSwap (unitToPhysicalCellFace h x) = unitToPhysicalCellFace h (physicalSquareSwap x) := by
  unfold unitToPhysicalCellFace
  rw [map_add, map_smul]
  congr 1
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [physicalSquareSwap_coordinates]

/-- Swapping the two coordinates permutes the trace curves and changes no
edge value or endpoint class. -/
noncomputable def NormalizedSquareTraces.swap {q : ℕ} {h : ℝ} {u : Domain 2 → Ambient q}
    {edge : Fin 2 → Bool → ℝ → Ambient q} (T : NormalizedSquareTraces h u edge) :
    NormalizedSquareTraces h (u ∘ physicalSquareSwap) (fun i => edge (Equiv.swap 0 1 i)) where
  curve i := T.curve (Equiv.swap 0 1 i)
  slice i := by
    filter_upwards [T.slice (Equiv.swap 0 1 i)] with t ht htI
    simpa only [Function.comp_apply, physicalSquareSwap_affine, physicalSquareSwap_slice] using ht htI
  edge i := T.edge (Equiv.swap 0 1 i)

private theorem physicalSquareSwap_preimage (h : ℝ) : physicalSquareSwap ⁻¹' (tensorGridOpenParameterBox 2 h).val =
    (tensorGridOpenParameterBox 2 h).val := by
  ext x
  have hCoords (x : Domain 2) : x ∈ (tensorGridOpenParameterBox 2 h).val ↔
      x 0 ∈ Ioo (0 : ℝ) h ∧ x 1 ∈ Ioo (0 : ℝ) h := by
    constructor
    · intro hx
      exact ⟨mem_iInter.mp hx 0, mem_iInter.mp hx 1⟩
    · intro hx
      apply mem_iInter.mpr
      intro i
      fin_cases i
      · exact hx.1
      · exact hx.2
  change physicalSquareSwap x ∈ (tensorGridOpenParameterBox 2 h).val ↔ _
  rw [hCoords, hCoords, (physicalSquareSwap_coordinates x).1, (physicalSquareSwap_coordinates x).2, and_comm]

/-- The positive physical square measure is invariant under its coordinate swap. -/
theorem measurePreserving_physicalSquareSwap (h : ℝ) : MeasurePreserving physicalSquareSwap
    (volume.restrict (tensorGridOpenParameterBox 2 h).val) (volume.restrict (tensorGridOpenParameterBox 2 h).val) := by
  have h := physicalSquareSwap.measurePreserving.restrict_preimage (tensorGridOpenParameterBox 2 h).property.measurableSet
  rwa [physicalSquareSwap_preimage] at h

/-- The pulled-back columns and energy are the original weak face graph in
the other ordering of its physical coordinates. -/
theorem memW12_physicalSquareSwap {q : ℕ} {h : ℝ} (hh : 0 < h)
    {u : Domain 2 → Ambient q} {D : Domain 2 → HarmonicMaps.Gradient 2 q}
    (hu : MemW12 (tensorGridOpenParameterBox 2 h) u D) :
    let Δ : Domain 2 → HarmonicMaps.Gradient 2 q := fun x i =>
      ∑ j : Fin 2, (physicalSquareSwap (EuclideanSpace.single i 1)) j • D (physicalSquareSwap x) j
    MemW12 (tensorGridOpenParameterBox 2 h) (u ∘ physicalSquareSwap) Δ ∧
      HarmonicMaps.dirichletEnergy Δ (tensorGridOpenParameterBox 2 h).val =
        HarmonicMaps.dirichletEnergy D (tensorGridOpenParameterBox 2 h).val := by
  intro Δ
  let U := tensorGridOpenParameterBox 2 h
  let V : OpenDomain 2 := ⟨physicalSquareSwap ⁻¹' U.val, U.property.preimage physicalSquareSwap.continuous⟩
  have hVol : (volume : Measure (Domain 2)) U.val ≠ ⊤ :=
    (StratificationTheory.volume_native_positive_cube 2 hh).trans_ne ENNReal.ofReal_ne_top
  have hEq : V = U := Subtype.ext (physicalSquareSwap_preimage h)
  obtain ⟨hW, _, _, hEnergy, _⟩ := StratificationTheory.memW12_isometric_preimage_energy hVol hu physicalSquareSwap
  have hW' : MemW12 V (u ∘ physicalSquareSwap) Δ := hW
  have hE' : HarmonicMaps.dirichletEnergy Δ V.val = HarmonicMaps.dirichletEnergy D U.val := hEnergy
  rw [hEq] at hW' hE'
  exact ⟨hW', hE'⟩

end Thesis
