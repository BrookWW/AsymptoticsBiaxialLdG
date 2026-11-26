module

public import Thesis.Interpolation.PenalizedShellGluing
import Mathlib.Analysis.Convex.Measure
import StratificationTheory.Foundation.UnitCubeAffineCoordinates

/-! The original angular square patches and their volume-to-surface coordinates. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Thesis

/-- The parameter square including its four original edges. -/
@[expose] def unitClosedFaceSquare : Set (Domain 2) :=
  (EuclideanSpace.proj 0) ⁻¹' Icc (-1 : ℝ) 1 ∩ (EuclideanSpace.proj 1) ⁻¹' Icc (-1 : ℝ) 1

theorem unitCellCube_subset_closedFaceSquare : (unitCellCube 2).val ⊆ unitClosedFaceSquare := by
  intro x hx
  exact ⟨Ioo_subset_Icc_self (mem_iInter.mp hx 0), Ioo_subset_Icc_self (mem_iInter.mp hx 1)⟩

private theorem unitClosedFaceSquare_isClosed : IsClosed unitClosedFaceSquare :=
  (isClosed_Icc.preimage (EuclideanSpace.proj (0 : Fin 2)).continuous).inter
    (isClosed_Icc.preimage (EuclideanSpace.proj (1 : Fin 2)).continuous)

private theorem unitClosedFaceSquare_isCompact : IsCompact unitClosedFaceSquare := by
  refine (isCompact_closedBall (0 : Domain 2) 2).of_isClosed_subset unitClosedFaceSquare_isClosed ?_
  intro x hx
  rw [mem_closedBall_zero_iff]
  have hSup : ‖WithLp.ofLp x‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · change ‖x 0‖ ≤ 1
      exact abs_le.mpr hx.1
    · change ‖x 1‖ ≤ 1
      exact abs_le.mpr hx.2
  have hNorm : ‖x‖ ≤ (2 : ℝ) * ‖WithLp.ofLp x‖ := by
    simpa only [Nat.cast_ofNat] using (StratificationTheory.cube_coordinate_norm_comparison x).2
  exact hNorm.trans (by linarith only [hSup])

/-- The physical face similarity has the whole closed physical square as image. -/
theorem unitToPhysicalCellFace_preimage_box {h : ℝ} (hh : 0 < h) :
    unitToPhysicalCellFace h ⁻¹' sphericalFaceParameterBox h = unitClosedFaceSquare := by
  ext x
  have hOne (t : ℝ) : h / 2 + (h / 2) * t ∈ Icc (0 : ℝ) h ↔ t ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> intro ht <;> constructor <;> nlinarith only [half_pos hh, ht.1, ht.2]
  change ((h / 2 + (h / 2) * x 0) ∈ Icc (0 : ℝ) h ∧ (h / 2 + (h / 2) * x 1) ∈ Icc (0 : ℝ) h) ↔
    x 0 ∈ Icc (-1 : ℝ) 1 ∧ x 1 ∈ Icc (-1 : ℝ) 1
  rw [hOne, hOne]

theorem unitToPhysicalCellFace_open_box {h : ℝ} (hh : 0 < h) :
    MapsTo (unitToPhysicalCellFace h) (unitCellCube 2).val (tensorGridOpenParameterBox 2 h).val := by
  intro x hx
  have hPre : unitToPhysicalCellFace h ⁻¹' (tensorGridOpenParameterBox 2 h).val = (unitCellCube 2).val :=
    StratificationTheory.affine_unit_cube_preimage_positive_cube 2 hh
  change x ∈ unitToPhysicalCellFace h ⁻¹' (tensorGridOpenParameterBox 2 h).val
  rwa [hPre]

private theorem unitToPhysicalCellFace_dist {h : ℝ} (hh : 0 < h) (x y : Domain 2) :
    dist (unitToPhysicalCellFace h x) (unitToPhysicalCellFace h y) = h / 2 * dist x y := by
  unfold unitToPhysicalCellFace
  rw [dist_add_left, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (half_pos hh).le, ← dist_eq_norm]

/-- The original angular square with its open grid edges excluded. -/
@[expose] noncomputable def shellAngularPatch (c : Point) (h : ℝ) (f : TensorGridSquare) : Set Point :=
  shellCapAngularPoint c h f '' (unitCellCube 2).val

/-- The same angular patch as a subset of the native sphere. -/
@[expose] noncomputable def shellAngularSpherePatch (c : Point) (h : ℝ) (f : TensorGridSquare) : Set UnitTensorSphere :=
  Subtype.val ⁻¹' shellAngularPatch c h f

/-- The literal angular map of the physical square has image on the unit sphere. -/
theorem shellCapAngularPoint_mem_sphere {c : Point} {h : ℝ} (hh : 0 < h) {m : ℕ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) {x : Domain 2} (hx : x ∈ unitClosedFaceSquare) :
    shellCapAngularPoint c h f x ∈ sphere (0 : Point) 1 := by
  have hX : unitToPhysicalCellFace h x ∈ sphericalFaceParameterBox h := by
    change x ∈ unitToPhysicalCellFace h ⁻¹' sphericalFaceParameterBox h
    rwa [unitToPhysicalCellFace_preimage_box hh]
  change sphericalFacePoint c h f ((unitToPhysicalCellFace h x) 0, (unitToPhysicalCellFace h x) 1) ∈ _
  exact (sphericalFacePoint_dist_bounds hh hc hm hf (p := ((unitToPhysicalCellFace h x) 0, (unitToPhysicalCellFace h x) 1))
    (q := ((unitToPhysicalCellFace h x) 0, (unitToPhysicalCellFace h x) 1)) ⟨hX.1, hX.2⟩ ⟨hX.1, hX.2⟩).1

private theorem shellCapAngularPoint_bounds {c : Point} {h : ℝ} (hh : 0 < h) {m : ℕ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) {x y : Domain 2}
    (hx : x ∈ unitClosedFaceSquare) (hy : y ∈ unitClosedFaceSquare) :
    dist (shellCapAngularPoint c h f x) (shellCapAngularPoint c h f y) ≤ (32 * h) * dist x y ∧
      h / 2 * dist x y ≤ 34 * dist (shellCapAngularPoint c h f x) (shellCapAngularPoint c h f y) := by
  have hMap : MapsTo (unitToPhysicalCellFace h) unitClosedFaceSquare (sphericalFaceParameterBox h) := by
    intro z hz
    change z ∈ unitToPhysicalCellFace h ⁻¹' sphericalFaceParameterBox h
    rwa [unitToPhysicalCellFace_preimage_box hh]
  have hDist := sphericalFaceParameterPoint_dist_bounds hh hc hm hf (hMap hx) (hMap hy)
  rw [unitToPhysicalCellFace_dist hh] at hDist
  refine ⟨?_, hDist.2⟩
  change dist (sphericalFaceParameterPoint c h f (unitToPhysicalCellFace h x))
    (sphericalFaceParameterPoint c h f (unitToPhysicalCellFace h y)) ≤ _
  linarith only [hDist.1]

private theorem shellCapAngularPoint_area {c : Point} {h : ℝ} (hh : 0 < h) {m : ℕ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) {S : Set (Domain 2)} (hS : S ⊆ unitClosedFaceSquare) :
    (Measure.euclideanHausdorffMeasure 2 : Measure Point) (shellCapAngularPoint c h f '' S) ≤
      ENNReal.ofReal ((32 * h) ^ 2) * (volume : Measure (Domain 2)) S := by
  let K : ℝ≥0 := ⟨32 * h, by positivity⟩
  have hLip : LipschitzOnWith K (shellCapAngularPoint c h f) unitClosedFaceSquare :=
    LipschitzOnWith.of_dist_le_mul (fun _ hx _ hy => (shellCapAngularPoint_bounds hh hc hm hf hx hy).1)
  have h := euclideanHausdorff_lipschitzOn_image_le_volume hLip hS
  rw [finrank_euclideanSpace_fin, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (show (0 : ℝ) ≤ (K : ℝ) from K.2)] at h
  exact h

/-- Literal inverse of the angular chart on its actual patch, including the
native two-dimensional measure bound needed by the cap L² traces. -/
structure ShellAngularInverse (c : Point) (h : ℝ) (f : TensorGridSquare) where
  inverse : Point → Domain 2
  measurable : Measurable inverse
  patch_measurable : MeasurableSet (shellAngularPatch c h f)
  left_inv : ∀ x ∈ (unitCellCube 2).val, inverse (shellCapAngularPoint c h f x) = x
  inverse_mem : ∀ y ∈ shellAngularPatch c h f, inverse y ∈ (unitCellCube 2).val
  right_inv : ∀ y ∈ shellAngularPatch c h f, shellCapAngularPoint c h f (inverse y) = y
  map_volume : Measure.map inverse ((Measure.euclideanHausdorffMeasure 2 : Measure Point).restrict (shellAngularPatch c h f)) ≤
    ENNReal.ofReal ((32 * h) ^ 2) • (volume : Measure (Domain 2)).restrict (unitCellCube 2).val

/-- The actual angular chart has a measurable inverse and its explicit
physical area bound. -/
theorem exists_shellAngularInverse {c : Point} {h : ℝ} (hh : 0 < h) {m : ℕ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) : Nonempty (ShellAngularInverse c h f) := by
  let Q := unitClosedFaceSquare
  let F := shellCapAngularPoint c h f
  let K := shellAngularPatch c h f
  let U := (unitCellCube 2).val
  let g : Q → Point := fun x => F x.val
  letI : CompactSpace Q := isCompact_iff_compactSpace.mp unitClosedFaceSquare_isCompact
  letI : Nonempty Q := ⟨⟨0, by exact ⟨by norm_num, by norm_num⟩⟩⟩
  have hLip : LipschitzWith (Real.toNNReal (32 * h)) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.coe_toNNReal _ (by positivity)]
    exact (shellCapAngularPoint_bounds hh hc hm hf x.property y.property).1
  have hInj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply dist_eq_zero.mp
    have hLe := (shellCapAngularPoint_bounds hh hc hm hf x.property y.property).2
    change F x.val = F y.val at hxy
    change h / 2 * dist x.val y.val ≤ 34 * dist (F x.val) (F y.val) at hLe
    rw [hxy, dist_self, mul_zero] at hLe
    exact (mul_eq_zero.mp (le_antisymm hLe (mul_nonneg (half_pos hh).le dist_nonneg))).resolve_left (half_pos hh).ne'
  have hEmb := (hLip.continuous.isClosedEmbedding hInj).measurableEmbedding
  let φ : Point → Domain 2 := fun y => (hEmb.invFun y).val
  have hMeas : Measurable φ := measurable_subtype_coe.comp hEmb.measurable_invFun
  have hLeft (x : Domain 2) (hx : x ∈ U) : φ (F x) = x :=
    congrArg Subtype.val (hEmb.leftInverse_invFun ⟨x, unitCellCube_subset_closedFaceSquare hx⟩)
  have hImage : g '' (Subtype.val ⁻¹' U : Set Q) = K := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, unitCellCube_subset_closedFaceSquare hx⟩, hx, rfl⟩
  have hK : MeasurableSet K := hImage ▸ hEmb.measurableSet_image.mpr
    ((unitCellCube 2).property.measurableSet.preimage measurable_subtype_coe)
  have hRight (y : Point) (hy : y ∈ K) : φ y ∈ U ∧ F (φ y) = y := by
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hLeft x hx]
    exact ⟨hx, rfl⟩
  refine ⟨{ inverse := φ
            measurable := hMeas
            patch_measurable := hK
            left_inv := hLeft
            inverse_mem := fun y hy => (hRight y hy).1
            right_inv := fun y hy => (hRight y hy).2
            map_volume := ?_ }⟩
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hMeas hA, Measure.restrict_apply' hK, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]
  have hP : φ ⁻¹' A ∩ K = F '' (A ∩ U) := by
    ext y
    constructor
    · intro hy
      exact ⟨φ y, ⟨hy.1, (hRight y hy.2).1⟩, (hRight y hy.2).2⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by change φ (F x) ∈ A; rw [hLeft x hx.2]; exact hx.1, ⟨x, hx.2, rfl⟩⟩
  rw [hP]
  exact shellCapAngularPoint_area hh hc hm hf (inter_subset_right.trans unitCellCube_subset_closedFaceSquare)

private theorem unitClosedFaceSquare_interior : interior unitClosedFaceSquare = (unitCellCube 2).val := by
  have hO (i : Fin 2) : IsOpenMap (EuclideanSpace.proj i : Domain 2 → ℝ) :=
    PiLp.isOpenMap_apply 2 (fun _ : Fin 2 => ℝ) i
  rw [unitClosedFaceSquare, interior_inter,
    ← (hO 0).preimage_interior_eq_interior_preimage (EuclideanSpace.proj (0 : Fin 2)).continuous,
    ← (hO 1).preimage_interior_eq_interior_preimage (EuclideanSpace.proj (1 : Fin 2)).continuous, interior_Icc]
  ext x
  constructor
  · intro hx
    apply mem_iInter.mpr
    intro i
    fin_cases i
    · exact hx.1
    · exact hx.2
  · exact fun hx => ⟨mem_iInter.mp hx 0, mem_iInter.mp hx 1⟩

private theorem volume_closedFaceSquare_boundary :
    (volume : Measure (Domain 2)) (unitClosedFaceSquare \ (unitCellCube 2).val) = 0 := by
  have hC : Convex ℝ unitClosedFaceSquare :=
    ((convex_Icc (-1 : ℝ) 1).linear_preimage (EuclideanSpace.proj (0 : Fin 2)).toLinearMap).inter
      ((convex_Icc (-1 : ℝ) 1).linear_preimage (EuclideanSpace.proj (1 : Fin 2)).toLinearMap)
  have h := hC.addHaar_frontier volume
  rwa [frontier, unitClosedFaceSquare_isClosed.closure_eq, unitClosedFaceSquare_interior] at h

/-- Each angular open patch lies on the same unit sphere. -/
theorem shellAngularPatch_subset_sphere {c : Point} {h : ℝ} (hh : 0 < h) {m : ℕ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) :
    shellAngularPatch c h f ⊆ sphere (0 : Point) 1 := by
  rintro _ ⟨x, hx, rfl⟩
  exact shellCapAngularPoint_mem_sphere hh hc hm hf (unitCellCube_subset_closedFaceSquare hx)

/-- The angular closed grid squares cover the entire unit sphere. -/
theorem iUnion_shellAngular_closed_eq_sphere {c : Point} {h : ℝ} (hh : 0 < h)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4)) :
    (⋃ f : ShellCellIndex m, shellCapAngularPoint c h f.val '' unitClosedFaceSquare) = sphere (0 : Point) 1 := by
  ext y
  rw [mem_iUnion]
  constructor
  · rintro ⟨f, x, hx, rfl⟩
    exact shellCapAngularPoint_mem_sphere hh hc hm f.property hx
  · intro hy
    obtain ⟨_, _, _, F, hF, _⟩ := shiftedCoordinateCube_geometry hc hm
    let θ : sphere (0 : Point) 1 := ⟨y, hy⟩
    let x := F θ
    have hm₀ : 0 < m := by
      by_contra hn
      have h : m = 0 := by omega
      simp only [h, Nat.cast_zero, zero_mul] at hm
      exact (by norm_num : ¬ (1 / 8 : ℝ) ≤ 0) hm.1
    obtain ⟨f, hf, p, hp, hpX⟩ := exists_tensorGridSquare_of_frontier c hm₀ hh x.property
    let z : Domain 2 := WithLp.toLp 2 ![p.1, p.2]
    let w : Domain 2 := (h / 2)⁻¹ • (z - WithLp.toLp 2 (fun _ => h / 2))
    have hW : unitToPhysicalCellFace h w = z := unitToPhysicalCellFace_inverse hh z
    have hz : z ∈ sphericalFaceParameterBox h := ⟨hp.1, hp.2⟩
    have hw : w ∈ unitClosedFaceSquare := by
      rw [← unitToPhysicalCellFace_preimage_box hh]
      change unitToPhysicalCellFace h w ∈ sphericalFaceParameterBox h
      rwa [hW]
    refine ⟨⟨f, hf⟩, w, hw, ?_⟩
    change sphericalFaceParameterPoint c h f (unitToPhysicalCellFace h w) = y
    rw [hW]
    change NormedSpace.normalize (tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 p.1 p.2) = y
    rw [hpX, ← hF x, F.symm_apply_apply]

/-- The open angular squares cover the native sphere almost everywhere.
Only their actual edges are omitted. -/
theorem ae_shellAngularSpherePatch_cover {c : Point} {h : ℝ} (hh : 0 < h)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4)) :
    ∀ᵐ θ ∂tensorSphereMeasure, ∃ f : ShellCellIndex m, θ ∈ shellAngularSpherePatch c h f.val := by
  let μ : Measure Point := Measure.euclideanHausdorffMeasure 2
  let H (f : ShellCellIndex m) := shellCapAngularPoint c h f.val '' (unitClosedFaceSquare \ (unitCellCube 2).val)
  have hK (f : ShellCellIndex m) : μ (H f) = 0 := by
    have h := shellCapAngularPoint_area hh hc hm f.property (sdiff_subset :
      unitClosedFaceSquare \ (unitCellCube 2).val ⊆ unitClosedFaceSquare)
    rw [volume_closedFaceSquare_boundary, mul_zero] at h
    exact le_antisymm h bot_le
  have hNull : μ (⋃ f, H f) = 0 := measure_iUnion_null hK
  rw [ae_iff]
  let Bad : Set UnitTensorSphere := {θ | ¬∃ f : ShellCellIndex m, θ ∈ shellAngularSpherePatch c h f.val}
  change tensorSphereMeasure Bad = 0
  rw [← isometry_subtype_coe.euclideanHausdorffMeasure_image Bad]
  apply measure_mono_null ?_ hNull
  rintro _ ⟨θ, hBad, rfl⟩
  have hCover : θ.val ∈ sphere (0 : Point) 1 := θ.property
  rw [← iUnion_shellAngular_closed_eq_sphere hh hc hm] at hCover
  obtain ⟨f, x, hx, heq⟩ := mem_iUnion.mp hCover
  refine mem_iUnion.mpr ⟨f, x, ⟨hx, ?_⟩, heq⟩
  intro hU
  exact hBad ⟨f, x, hU, heq⟩

/-- Distinct open angular squares are disjoint. -/
theorem pairwiseDisjoint_shellAngularSpherePatch {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4)) :
    Pairwise (fun f g : ShellCellIndex m => Disjoint (shellAngularSpherePatch c h f.val) (shellAngularSpherePatch c h g.val)) := by
  intro f g hfg
  apply Set.disjoint_left.mpr
  rintro θ ⟨x, hx, hX⟩ ⟨y, hy, hY⟩
  let r : ℝ := 1 - h / 2
  have hr : r ∈ Ioo (1 - h) 1 := by constructor <;> dsimp only [r] <;> linarith only [hh]
  have hPoint (f : ShellCellIndex m) (x : Domain 2) (hx : x ∈ (unitCellCube 2).val) :
      r • shellCapAngularPoint c h f.val x ∈ interior (sphericalClosedCell c h f.val) := by
    let s := unitToPhysicalCellFace h x
    have hS := unitToPhysicalCellFace_open_box hh hx
    rw [sphericalClosedCell_interior hh' hc hm f.property]
    exact ⟨((s 0, s 1), r), ⟨⟨mem_iInter.mp hS 0, mem_iInter.mp hS 1⟩, hr⟩, rfl⟩
  have hA := hPoint f x hx
  have hB := hPoint g y hy
  rw [hX] at hA
  rw [hY] at hB
  exact Set.disjoint_left.mp (sphericalClosedCell_disjoint_interiors hh hh' hc hm f.property g.property
    (fun h => hfg (Subtype.ext h))) hA hB

/-- Surface measure in the native sphere subtype is the actual ambient
Hausdorff measure restricted to that sphere. -/
theorem map_unitSphere_surface_measure : Measure.map (Subtype.val : UnitTensorSphere → Point) tensorSphereMeasure =
    (Measure.euclideanHausdorffMeasure 2 : Measure Point).restrict (sphere (0 : Point) 1) := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_subtype_coe hA, Measure.restrict_apply hA,
    ← isometry_subtype_coe.euclideanHausdorffMeasure_image]
  congr 1
  ext x
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨hθ, θ.property⟩
  · rintro ⟨hx, hxs⟩
    exact ⟨⟨x, hxs⟩, hx, rfl⟩

/-- Pulling the native angular patch measure back to its unit-square
coordinates retains the verified physical area factor. -/
theorem ShellAngularInverse.map_sphere_measure {c : Point} {h : ℝ} {f : TensorGridSquare}
    (A : ShellAngularInverse c h f) (hS : shellAngularPatch c h f ⊆ sphere (0 : Point) 1) :
    Measure.map (A.inverse ∘ (Subtype.val : UnitTensorSphere → Point)) (tensorSphereMeasure.restrict (shellAngularSpherePatch c h f)) ≤
      ENNReal.ofReal ((32 * h) ^ 2) • (volume : Measure (Domain 2)).restrict (unitCellCube 2).val := by
  have hE := MeasurableEmbedding.subtype_coe (isClosed_sphere : IsClosed (sphere (0 : Point) 1)).measurableSet
  have hR : Measure.map (Subtype.val : UnitTensorSphere → Point) (tensorSphereMeasure.restrict (shellAngularSpherePatch c h f)) =
      (Measure.euclideanHausdorffMeasure 2 : Measure Point).restrict (shellAngularPatch c h f) := by
    rw [shellAngularSpherePatch, ← hE.restrict_map, map_unitSphere_surface_measure,
      Measure.restrict_restrict A.patch_measurable, inter_eq_left.mpr hS]
  rw [← Measure.map_map A.measurable measurable_subtype_coe, hR]
  exact A.map_volume

end Thesis
