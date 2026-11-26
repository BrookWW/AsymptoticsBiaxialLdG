module

public import Thesis.Interpolation.SphericalCellHalfspaces
public import Thesis.Interpolation.CellInterfaceGluing
import StratificationTheory.Foundation.FiniteDisjointSobolevData
import StratificationTheory.Foundation.SobolevLocalAssembly

/-! The literal finite shell partition, original piecewise data and radial corner lines. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped Topology ENNReal

namespace Thesis

abbrev ShellCellIndex (m : ℕ) := ↥(cubeBoundarySquares m)

/-- The open shell at the actual radial scale. -/
@[expose] noncomputable def sphericalShellDomain (h : ℝ) : OpenDomain 3 :=
  ⟨radialAnnulus 0 (1 - h) 1, isOpen_radialAnnulus 0 (1 - h) 1⟩

/-- The values on the disjoint actual open cells, with a fixed value on the
volume-null complement. -/
@[expose] noncomputable def sphericalShellPiecewiseField {q m : ℕ} (c : Point) (h : ℝ)
    (u : ShellCellIndex m → Point → Ambient q) (x : Point) : Ambient q :=
  ∑ f : ShellCellIndex m, (sphericalCellOpenDomain c h f.val).val.indicator (u f) x

/-- The corresponding literal piecewise native columns. -/
@[expose] noncomputable def sphericalShellPiecewiseDerivative {q m : ℕ} (c : Point) (h : ℝ)
    (D : ShellCellIndex m → Point → HarmonicMaps.Gradient 3 q) (x : Point) : HarmonicMaps.Gradient 3 q :=
  ∑ f : ShellCellIndex m, (sphericalCellOpenDomain c h f.val).val.indicator (D f) x

private theorem finite_indicator_at {α E J : Type*} [AddCommMonoid E] [Fintype J]
    (S : J → Set α) (hd : Pairwise fun i j => Disjoint (S i) (S j))
    (f : J → α → E) (j : J) {x : α} (hx : x ∈ S j) :
    (∑ i : J, (S i).indicator (f i) x) = f j x := by
  classical
  rw [Finset.sum_eq_single j]
  · exact indicator_of_mem hx _
  · intro k _ hk
    exact indicator_of_notMem (fun hx' => Set.disjoint_left.mp (hd hk) hx' hx) _
  · exact fun h => (h (Finset.mem_univ j)).elim

/-- An open cell lies in the same open annulus as all the other cells. -/
theorem sphericalCellOpenDomain_subset_shell {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) :
    (sphericalCellOpenDomain c h f).val ⊆ (sphericalShellDomain h).val := by
  change interior (sphericalClosedCell c h f) ⊆ _
  rw [sphericalClosedCell_interior hh' hc hm hf]
  rintro _ ⟨p, hp, rfl⟩
  have hP : p.1 ∈ Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) h :=
    ⟨Ioo_subset_Icc_self hp.1.1, Ioo_subset_Icc_self hp.1.2⟩
  have hN : ‖sphericalFacePoint c h f p.1‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (sphericalFacePoint_dist_bounds hh hc hm hf hP hP).1
  have hp' : 0 ≤ p.2 := by linarith only [hp.2.1, hh']
  change ‖sphericalCellPoint c h f p - 0‖ ∈ Ioo (1 - h) 1
  simpa only [sub_zero, sphericalCellPoint, norm_smul, Real.norm_of_nonneg hp', hN, mul_one] using hp.2

/-- The literal piecewise field and columns equal their original values on
every open cell. -/
theorem sphericalShellPiecewise_eq_on_cell {q m : ℕ} {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32)) (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    (u : ShellCellIndex m → Point → Ambient q) (D : ShellCellIndex m → Point → HarmonicMaps.Gradient 3 q)
    (f : ShellCellIndex m) {x : Point} (hx : x ∈ (sphericalCellOpenDomain c h f.val).val) :
    sphericalShellPiecewiseField c h u x = u f x ∧ sphericalShellPiecewiseDerivative c h D x = D f x := by
  have hd : Pairwise fun f g : ShellCellIndex m => Disjoint (sphericalCellOpenDomain c h f.val).val
      (sphericalCellOpenDomain c h g.val).val := by
    intro f g hfg
    exact sphericalClosedCell_disjoint_interiors hh hh' hc hm f.property g.property
      (fun h => hfg (Subtype.ext h))
  exact ⟨finite_indicator_at _ hd u f hx, finite_indicator_at _ hd D f hx⟩

/-- The original independent cell graphs have the actual piecewise L² data
and additive Dirichlet and bulk integrals on the finite shell partition. -/
theorem sphericalShellPiecewise_data {q m : ℕ} {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32)) (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    (u : ShellCellIndex m → Point → Ambient q) (D : ShellCellIndex m → Point → HarmonicMaps.Gradient 3 q)
    (hGraph : ∀ f, MemW12 (sphericalCellOpenDomain c h f.val) (u f) (D f)) :
    let Ω := sphericalShellDomain h
    let U := fun f : ShellCellIndex m => sphericalCellOpenDomain c h f.val
    let w := sphericalShellPiecewiseField c h u
    let E := sphericalShellPiecewiseDerivative c h D
    MemLp w 2 (volume.restrict Ω.val) ∧ (∀ i : Fin 3, MemLp (fun x => E x i) 2 volume) ∧
      (∀ f, MemW12 (U f) w E) ∧
      ((∫ x in Ω.val, hsNormSq (E x)) = ∑ f, ∫ x in (U f).val, hsNormSq (D f x)) ∧
      (∀ b : Ambient q → ℝ≥0∞, (∫⁻ x in Ω.val, b (w x)) = ∑ f, ∫⁻ x in (U f).val, b (u f x)) ∧
      ∀ P : Ambient q → Prop, (∀ f, ∀ᵐ x ∂volume.restrict (U f).val, P (u f x)) →
        ∀ᵐ x ∂volume.restrict Ω.val, P (w x) := by
  classical
  intro Ω U w E
  have hSub (f : ShellCellIndex m) : (U f).val ⊆ Ω.val :=
    sphericalCellOpenDomain_subset_shell hh hh' hc hm f.property
  have hd : Pairwise fun f g : ShellCellIndex m => Disjoint (U f).val (U g).val := by
    intro f g hfg
    exact sphericalClosedCell_disjoint_interiors hh hh' hc hm f.property g.property (fun h => hfg (Subtype.ext h))
  have hCover : ∀ᵐ x ∂volume.restrict Ω.val, ∃ f : ShellCellIndex m, x ∈ (U f).val := by
    have hAE := ae_restrict_of_ae (μ := (volume : Measure Point)) (s := Ω.val)
      (sphericalCell_interior_ae_partition hh hh' hc hm)
    filter_upwards [hAE, ae_restrict_mem Ω.property.measurableSet] with x hEq hx
    have hMem : x ∈ ⋃ f ∈ cubeBoundarySquares m, interior (sphericalClosedCell c h f) := by
      change (x ∈ ⋃ f ∈ cubeBoundarySquares m, interior (sphericalClosedCell c h f)) =
        (x ∈ Ω.val) at hEq
      exact hEq.mpr hx
    obtain ⟨f, hf, hx'⟩ := mem_iUnion₂.mp hMem
    exact ⟨⟨f, hf⟩, hx'⟩
  have hw (f : ShellCellIndex m) {x : Point} (hx : x ∈ (U f).val) : w x = u f x :=
    (sphericalShellPiecewise_eq_on_cell hh hh' hc hm u D f hx).1
  have hSob (f : ShellCellIndex m) : MemW12 (U f) w (D f) := by
    apply (hGraph f).congr_ae ?_ (EventuallyEq.refl _ _)
    filter_upwards [ae_restrict_mem (U f).property.measurableSet] with x hx
    exact (hw f hx).symm
  obtain ⟨hWLp, hDLp, hWeak, hE⟩ := StratificationTheory.finite_disjoint_sobolev_data Ω.val U hd hSub hCover w D hSob
  refine ⟨hWLp, hDLp, hWeak, hE, ?_, ?_⟩
  · intro b
    have hRestrict : (volume : Measure Point).restrict Ω.val = volume.restrict (⋃ f, (U f).val) := by
      apply Measure.restrict_congr_set
      have hA := (ae_restrict_iff' Ω.property.measurableSet).mp hCover
      filter_upwards [hA] with x hA
      exact propext ⟨fun hx => mem_iUnion.mpr (hA hx),
        fun hx => let ⟨f, hf⟩ := mem_iUnion.mp hx; hSub f hf⟩
    rw [hRestrict, lintegral_iUnion (fun f => (U f).property.measurableSet) hd, tsum_fintype]
    apply Finset.sum_congr rfl
    intro f _
    exact setLIntegral_congr_fun (U f).property.measurableSet (fun x hx => congrArg b (hw f hx))
  · intro P hP
    have hEach (f : ShellCellIndex m) : ∀ᵐ x : Point ∂volume, x ∈ (U f).val → P (u f x) :=
      (ae_restrict_iff' (U f).property.measurableSet).mp (hP f)
    filter_upwards [hCover, ae_restrict_of_ae (ae_all_iff.mpr hEach)] with x hx hp
    obtain ⟨f, hf⟩ := hx
    rw [hw f hf]
    exact hp f hf

/-- Each corner fixes both tangential coordinates of its original lattice square. -/
@[expose] noncomputable def shellCellRawCorner (c : Point) (h : ℝ) (f : TensorGridSquare) (b : Bool × Bool) : Point :=
  tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 (if b.1 then h else 0) (if b.2 then h else 0)

abbrev ShellCellCornerIndex (m : ℕ) := ShellCellIndex m × (Bool × Bool)

/-- The finite family of radial lines through the mesh corners. -/
@[expose] noncomputable def sphericalShellCornerLines (c : Point) (h : ℝ) (m : ℕ) : Set Point :=
  ⋃ f : ShellCellCornerIndex m, range (fun r : ℝ => r • shellCellRawCorner c h f.1.val f.2)

/-- A cell boundary point strictly between the two caps and away from the
radial corner lines is in the relative interior of a genuine lateral side. -/
theorem exists_shellCell_lateral_side_of_regular_boundary {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32)) (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    (f : ShellCellIndex m) {y : Point} (hy : y ∈ frontier (sphericalClosedCell c h f.val))
    (hY : y ∈ (sphericalShellDomain h).val) (hRegular : y ∉ sphericalShellCornerLines c h m) :
    ∃ (i : Fin 2) (b : Bool) (t r : ℝ), t ∈ Ioo (0 : ℝ) h ∧ r ∈ Ioo (1 - h) 1 ∧
      y = sphericalCellPoint c h f.val (shellSquareSideParameters i (if b then h else 0) t, r) := by
  rw [sphericalClosedCell_frontier hh hh' hc hm f.property] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  obtain ⟨hpBox, hpSide⟩ := sphericalCellParameterBox_mem_frontier.mp hp
  have hN : ‖sphericalFacePoint c h f.val p.1‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (sphericalFacePoint_dist_bounds hh hc hm f.property hpBox.1 hpBox.1).1
  have hp₀ : 0 ≤ p.2 := by linarith only [hpBox.2.1, hh']
  have hr : p.2 ∈ Ioo (1 - h) 1 := by
    change ‖sphericalCellPoint c h f.val p - 0‖ ∈ Ioo (1 - h) 1 at hY
    simpa only [sub_zero, sphericalCellPoint, norm_smul, Real.norm_of_nonneg hp₀, hN, mul_one] using hY
  have hNo₀ : p.2 ≠ 1 - h := ne_of_gt hr.1
  have hNo₁ : p.2 ≠ 1 := ne_of_lt hr.2
  have hSide : (p.1.1 = 0 ∨ p.1.1 = h) ∨ (p.1.2 = 0 ∨ p.1.2 = h) := by
    simpa only [hNo₀, hNo₁, or_false, or_assoc] using hpSide
  have hBool (s : ℝ) (hs : s = 0 ∨ s = h) : ∃ b : Bool, s = if b then h else 0 := by
    rcases hs with h₀ | h₁
    · exact ⟨false, h₀⟩
    · exact ⟨true, h₁⟩
  have hNotBoth : (p.1.1 = 0 ∨ p.1.1 = h) → (p.1.2 = 0 ∨ p.1.2 = h) → False := by
    intro h₀ h₁
    obtain ⟨b₀, hb₀⟩ := hBool _ h₀
    obtain ⟨b₁, hb₁⟩ := hBool _ h₁
    let z := shellCellRawCorner c h f.val (b₀, b₁)
    have hRaw : tensorGridSquarePoint (tensorGridVertex c h f.val.1) f.val.2 p.1.1 p.1.2 = z := by
      rw [hb₀, hb₁]
      rfl
    apply hRegular
    refine mem_iUnion.mpr ⟨(f, b₀, b₁), p.2 / ‖z‖, ?_⟩
    change (p.2 / ‖z‖) • z = p.2 • NormedSpace.normalize
      (tensorGridSquarePoint (tensorGridVertex c h f.val.1) f.val.2 p.1.1 p.1.2)
    rw [hRaw, NormedSpace.normalize, smul_smul, div_eq_mul_inv]
  rcases hSide with hs | ht
  · obtain ⟨b, hb⟩ := hBool _ hs
    have hn : ¬(p.1.2 = 0 ∨ p.1.2 = h) := hNotBoth hs
    push Not at hn
    have ht : p.1.2 ∈ Ioo (0 : ℝ) h :=
      ⟨lt_of_le_of_ne hpBox.1.2.1 hn.1.symm, lt_of_le_of_ne hpBox.1.2.2 hn.2⟩
    refine ⟨0, b, p.1.2, p.2, ht, hr, ?_⟩
    rw [← hb]
    rfl
  · obtain ⟨b, hb⟩ := hBool _ ht
    have hn : ¬(p.1.1 = 0 ∨ p.1.1 = h) := fun hs => hNotBoth hs ht
    push Not at hn
    have hs : p.1.1 ∈ Ioo (0 : ℝ) h :=
      ⟨lt_of_le_of_ne hpBox.1.1.1 hn.1.symm, lt_of_le_of_ne hpBox.1.1.2 hn.2⟩
    refine ⟨1, b, p.1.1, p.2, hs, hr, ?_⟩
    rw [← hb]
    rfl

/-- Each regular side parametrization is the same literal radial chart of
its selected oriented mesh edge. -/
theorem shellSquareSide_point_on_edge (c : Point) (h : ℝ) {m : ℕ} (f : ShellCellIndex m)
    (i : Fin 2) (upper : Bool) (t r : ℝ) :
    sphericalCellPoint c h f.val (shellSquareSideParameters i (if upper then h else 0) t, r) =
      sphericalLateralEdge c h (tensorSquareCoordinateEdge f i upper).val (t, r) := by
  obtain ⟨_, _, hB, hT, hL, hR⟩ := sphericalCellPoint_boundary c h f.val t t r
  fin_cases i <;> cases upper
  · simpa [shellSquareSideParameters, tensorSquareCoordinateEdge, tensorSquareLeftEdge] using hL
  · simpa [shellSquareSideParameters, tensorSquareCoordinateEdge, tensorSquareRightEdge] using hR
  · simpa [shellSquareSideParameters, tensorSquareCoordinateEdge, tensorSquareLowerEdge] using hB
  · simpa [shellSquareSideParameters, tensorSquareCoordinateEdge, tensorSquareUpperEdge] using hT

private theorem rawGridEdge_floor {c : Point} {h : ℝ} (hh : 0 < h) (e : TensorGridEdge)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) h) (i : Fin 3) :
    let x := tensorGridEdgePoint c h e t
    let v := (x i - c i) / h
    ⌊v⌋ = e.1 i ∧ (v ≠ (e.1 i : ℝ) ↔ i = e.2) := by
  intro x v
  have h₁ : 0 < t / h := div_pos ht.1 hh
  have h₂ : t / h < 1 := (div_lt_one hh).mpr ht.2
  have hV : v = (e.1 i : ℝ) + (if i = e.2 then t / h else 0) := by
    dsimp only [v, x]
    rw [tensorGridEdgePoint_apply]
    split_ifs <;> field_simp <;> ring
  by_cases hi : i = e.2
  · rw [hV, if_pos hi]
    exact ⟨Int.floor_eq_iff.mpr ⟨by linarith only [h₁], by linarith only [h₂]⟩,
      ⟨fun _ => hi, fun _ => ne_of_gt (by linarith only [h₁])⟩⟩
  · rw [hV, if_neg hi, add_zero]
    simp [hi]

/-- Relative interiors of the literal raw edges are disjoint, and each
edge has its original unique tangential parameter. -/
theorem rawGridEdge_eq_of_open_point {c : Point} {h : ℝ} (hh : 0 < h) {e f : TensorGridEdge}
    {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) h) (ht : t ∈ Ioo (0 : ℝ) h)
    (hEq : tensorGridEdgePoint c h e s = tensorGridEdgePoint c h f t) : e = f ∧ s = t := by
  have hIndices (i : Fin 3) : e.1 i = f.1 i ∧ (i = e.2 ↔ i = f.2) := by
    obtain ⟨he, he'⟩ := rawGridEdge_floor (c := c) hh e hs i
    obtain ⟨hf, hf'⟩ := rawGridEdge_floor (c := c) hh f ht i
    rw [hEq] at he he'
    have hI := he.symm.trans hf
    exact ⟨hI, he'.symm.trans (by rwa [hI])⟩
  have hIndex : e = f := Prod.ext (funext fun i => (hIndices i).1) ((hIndices e.2).2.mp rfl)
  refine ⟨hIndex, dist_eq_zero.mp ?_⟩
  rw [← tensorGridEdgePoint_dist c h e, hEq, hIndex, dist_self]

/-- A regular point of a projected side identifies its raw edge and both
physical parameters. -/
theorem sphericalLateralEdge_eq_of_open_point {c : Point} {h : ℝ} (hh : 0 < h) {m : ℕ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {e f : TensorGridEdge} (he : e ∈ cubeBoundaryEdges m) (hf : f ∈ cubeBoundaryEdges m)
    {s t r R : ℝ} (hs : s ∈ Ioo (0 : ℝ) h) (ht : t ∈ Ioo (0 : ℝ) h) (hr : 0 < r) (hR : 0 < R)
    (hEq : sphericalLateralEdge c h e (s, r) = sphericalLateralEdge c h f (t, R)) : e = f ∧ (s, r) = (t, R) := by
  let x := NormedSpace.normalize (tensorGridEdgePoint c h e s)
  let y := NormedSpace.normalize (tensorGridEdgePoint c h f t)
  have hx : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp
    (normalized_grid_edge_dist hh hc hm he (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self hs)).1
  have hy : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp
    (normalized_grid_edge_dist hh hc hm hf (Ioo_subset_Icc_self ht) (Ioo_subset_Icc_self ht)).1
  change r • x = R • y at hEq
  have hRad : r = R := by
    have h := congrArg norm hEq
    simpa only [norm_smul, Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hR.le, hx, hy, mul_one] using h
  have hDir : x = y := by
    have h := congrArg NormedSpace.normalize hEq
    simpa only [NormedSpace.normalize_smul_of_pos hr, NormedSpace.normalize_smul_of_pos hR,
      NormedSpace.normalize_eq_self_of_norm_eq_one hx, NormedSpace.normalize_eq_self_of_norm_eq_one hy] using h
  obtain ⟨_, _, _, F, heq, _⟩ := shiftedCoordinateCube_geometry hc hm
  let X : frontier (shiftedCoordinateCube c ((m : ℝ) * h)) :=
    ⟨_, tensorGridEdgePoint_mem_frontier hh he (Ioo_subset_Icc_self hs)⟩
  let Y : frontier (shiftedCoordinateCube c ((m : ℝ) * h)) :=
    ⟨_, tensorGridEdgePoint_mem_frontier hh hf (Ioo_subset_Icc_self ht)⟩
  have hRaw : X = Y := F.symm.injective (Subtype.ext ((heq X).trans (hDir.trans (heq Y).symm)))
  obtain ⟨hIdx, hArg⟩ := rawGridEdge_eq_of_open_point hh hs ht (congrArg Subtype.val hRaw)
  exact ⟨hIdx, Prod.ext hArg hRad⟩

/-- Local Sobolev gluing away from the actual finite radial corner lines
gives the same complete weak graph on the open shell. -/
theorem sphericalShell_memW12_of_off_cornerLines {q m : ℕ} (c : Point) (h : ℝ)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemLp u 2 (volume.restrict (sphericalShellDomain h).val))
    (hD : ∀ i, MemLp (fun x => D x i) 2 (volume.restrict (sphericalShellDomain h).val))
    {B : ℝ} (hB : ∀ᵐ x ∂volume.restrict (sphericalShellDomain h).val, ‖u x‖ ≤ B)
    (hLocal : ∀ x ∈ (sphericalShellDomain h).val, x ∉ sphericalShellCornerLines c h m →
      ∃ r : ℝ, 0 < r ∧ MemW12 (ballDomain x r) u D) :
    MemW12 (sphericalShellDomain h) u D := by
  classical
  let J := ShellCellCornerIndex m
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 2)
  have hOne (j : J) := exists_cellVertex_radialLineFrame (shellCellRawCorner c h j.1.val j.2)
  choose Q hQ using hOne
  let P : J → Point →L[ℝ] Domain 2 := fun j =>
    (ContinuousLinearMap.snd ℝ (Domain 1) (Domain 2)).comp
      (e.toContinuousLinearMap.comp (Q j).toContinuousLinearEquiv.toContinuousLinearMap)
  let Z (j : J) : Set Point := (fun x => P j (x - 0)) ⁻¹' {(0 : Domain 2)}
  let Ω := sphericalShellDomain h
  let V := Ω.val ∩ (⋃ j ∈ (Finset.univ : Finset J), Z j)ᶜ
  have hV : IsOpen V := Ω.property.inter (isClosed_biUnion_finset (fun j _ =>
    isClosed_singleton.preimage ((P j).continuous.comp (continuous_id.sub continuous_const)))).isOpen_compl
  have hLines : sphericalShellCornerLines c h m ⊆ ⋃ j ∈ (Finset.univ : Finset J), Z j := by
    intro z hz
    obtain ⟨j, t, rfl⟩ := mem_iUnion.mp hz
    apply mem_iUnion₂.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    change (e (Q j (t • shellCellRawCorner c h j.1.val j.2 - 0))).2 = 0
    simpa only [sub_zero] using hQ j t
  have hBound : Bornology.IsBounded Ω.val := isBounded_ball.subset
    (fun x hx => mem_ball_iff_norm.mpr hx.2 : Ω.val ⊆ ball (0 : Point) 1)
  apply StratificationTheory.memW12_of_bounded_local_sobolev_off_finite_affine_flats
    (Finset.univ : Finset J) Q (fun _ => 0) hBound hu hD hB
  change ∀ x ∈ V, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ V ∧ MemW12 (ballDomain x r) u D
  intro x hx
  obtain ⟨r, hr, hw⟩ := hLocal x hx.1 (fun h => hx.2 (hLines h))
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV x hx
  let t := min r δ
  have hSub : ball x t ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  exact ⟨t, lt_min hr hδ, (ball_subset_ball (min_le_right _ _)).trans hδV, hw.1.mono hSub,
    hw.2.1.mono_measure (Measure.restrict_mono_set volume hSub),
    fun i => (hw.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)⟩

end Thesis
