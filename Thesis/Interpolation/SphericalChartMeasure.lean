module

public import Thesis.Interpolation.SphericalCellGeometry
public import HarmonicMaps.Analysis.EuclideanHausdorffLipschitz
public import Thesis.Variational.StrongComparison
import Mathlib.Analysis.Convex.Measure

/-! Quantitative volume and surface measure of the actual spherical grid charts. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Thesis

/-- The closed angular chart carrier in native physical square coordinates. -/
@[expose] def sphericalFaceParameterBox (h : ℝ) : Set (Domain 2) :=
  (EuclideanSpace.proj 0) ⁻¹' Icc 0 h ∩ (EuclideanSpace.proj 1) ⁻¹' Icc 0 h

/-- Literal normalization of the original physical mesh square. -/
@[expose] noncomputable def sphericalFaceParameterPoint (c : Point) (h : ℝ) (f : TensorGridSquare)
    (p : Domain 2) : Point := sphericalFacePoint c h f (p 0, p 1)

private theorem dist_pairCoordinates_bounds (p q : Domain 2) :
    dist (p 0, p 1) (q 0, q 1) ≤ dist p q ∧ dist p q ≤ 2 * dist (p 0, p 1) (q 0, q 1) := by
  rw [Prod.dist_eq]
  constructor
  · apply max_le
    · simpa only [Real.dist_eq, dist_eq_norm p q, PiLp.sub_apply, Real.norm_eq_abs] using
        PiLp.norm_apply_le (p - q) (0 : Fin 2)
    · simpa only [Real.dist_eq, dist_eq_norm p q, PiLp.sub_apply, Real.norm_eq_abs] using
        PiLp.norm_apply_le (p - q) (1 : Fin 2)
  · rw [dist_eq_norm p q]
    have hg : ‖WithLp.ofLp (p - q)‖ ≤ max (dist (p 0) (q 0)) (dist (p 1) (q 1)) := by
      apply (pi_norm_le_iff_of_nonneg (dist_nonneg.trans (le_max_left _ _))).mpr
      intro i
      fin_cases i
      · change ‖p 0 - q 0‖ ≤ _
        rw [← dist_eq_norm]
        exact le_max_left _ _
      · change ‖p 1 - q 1‖ ≤ _
        rw [← dist_eq_norm]
        exact le_max_right _ _
    exact (StratificationTheory.cube_coordinate_norm_comparison (p - q)).2.trans
      (mul_le_mul_of_nonneg_left hg (by norm_num))

/-- Bounds for the original projected square in the native Euclidean metric. -/
theorem sphericalFaceParameterPoint_dist_bounds {c : Point} {h : ℝ} (hh : 0 < h)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) {p q : Domain 2}
    (hp : p ∈ sphericalFaceParameterBox h) (hq : q ∈ sphericalFaceParameterBox h) :
    dist (sphericalFaceParameterPoint c h f p) (sphericalFaceParameterPoint c h f q) ≤ 64 * dist p q ∧
      dist p q ≤ 34 * dist (sphericalFaceParameterPoint c h f p) (sphericalFaceParameterPoint c h f q) := by
  obtain ⟨_, _, hU, hL⟩ := sphericalFacePoint_dist_bounds hh hc hm hf
    (p := (p 0, p 1)) (q := (q 0, q 1)) hp hq
  have hCoords := dist_pairCoordinates_bounds p q
  change dist (sphericalFacePoint c h f (p 0, p 1)) (sphericalFacePoint c h f (q 0, q 1)) ≤ _ ∧
    _ ≤ 34 * dist (sphericalFacePoint c h f (p 0, p 1)) (sphericalFacePoint c h f (q 0, q 1))
  constructor
  · linarith only [hU, hCoords.1]
  · linarith only [hL, hCoords.2]

/-- Surface area of every subset of a projected square is comparable to the
Lebesgue volume in the physical chart, with mesh-independent constants. -/
theorem sphericalFaceParameterPoint_area {c : Point} {h : ℝ} (hh : 0 < h)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) {S : Set (Domain 2)}
    (hS : S ⊆ sphericalFaceParameterBox h) :
    let A := sphericalFaceParameterPoint c h f '' S
    (Measure.euclideanHausdorffMeasure 2 : Measure Point) A ≤ 64 ^ 2 * (volume : Measure (Domain 2)) S ∧
      (volume : Measure (Domain 2)) S ≤ 34 ^ 2 * (Measure.euclideanHausdorffMeasure 2 : Measure Point) A := by
  intro A
  have hLip : LipschitzOnWith 64 (sphericalFaceParameterPoint c h f) (sphericalFaceParameterBox h) :=
    LipschitzOnWith.of_dist_le_mul (fun _ hx _ hy => (sphericalFaceParameterPoint_dist_bounds hh hc hm hf hx hy).1)
  have hUpper := euclideanHausdorff_lipschitzOn_image_le_volume hLip hS
  have hLower := volume_le_euclideanHausdorff_image_of_dist_le (K := 34)
    (f := sphericalFaceParameterPoint c h f)
    (fun _ hx _ hy => (sphericalFaceParameterPoint_dist_bounds hh hc hm hf hx hy).2) hS
  simpa only [finrank_euclideanSpace_fin, ENNReal.coe_ofNat] using And.intro hUpper hLower

/-- The canonical surface measure on the angular square and the actual
pushforward from any part of its parameter box dominate one another. -/
theorem sphericalFaceParameterPoint_map_volume {c : Point} {h : ℝ} (hh : 0 < h)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) {Q : Set (Domain 2)}
    (hQ : MeasurableSet Q) (hQBox : Q ⊆ sphericalFaceParameterBox h) :
    let φ := sphericalFaceParameterPoint c h f
    let μ := Measure.map φ (volume.restrict Q)
    let ν := (Measure.euclideanHausdorffMeasure 2 : Measure Point).restrict (φ '' Q)
    ν ≤ (64 ^ 2 : ℝ≥0∞) • μ ∧ μ ≤ (34 ^ 2 : ℝ≥0∞) • ν := by
  intro φ μ ν
  have hLip : LipschitzOnWith 64 φ (sphericalFaceParameterBox h) :=
    LipschitzOnWith.of_dist_le_mul (fun _ hx _ hy => (sphericalFaceParameterPoint_dist_bounds hh hc hm hf hx hy).1)
  have hMeas : AEMeasurable φ (volume.restrict Q) := (hLip.mono hQBox).continuousOn.aemeasurable hQ
  have hSets (A : Set Point) (hA : MeasurableSet A) :
      ν A ≤ 64 ^ 2 * μ A ∧ μ A ≤ 34 ^ 2 * ν A := by
    let S := φ ⁻¹' A ∩ Q
    have hImage : φ '' S = A ∩ φ '' Q := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx.1, ⟨x, hx.2, rfl⟩⟩
      · rintro ⟨hy, x, hx, rfl⟩
        exact ⟨x, ⟨hy, hx⟩, rfl⟩
    have hμ : μ A = (volume : Measure (Domain 2)) S := by
      dsimp only [μ, S]
      rw [Measure.map_apply_of_aemeasurable hMeas hA, Measure.restrict_apply' hQ]
    have hν : ν A = (Measure.euclideanHausdorffMeasure 2 : Measure Point) (φ '' S) := by
      dsimp only [ν]
      rw [Measure.restrict_apply hA, hImage]
    rw [hμ, hν]
    exact sphericalFaceParameterPoint_area hh hc hm hf (inter_subset_right.trans hQBox)
  exact ⟨Measure.le_iff.mpr fun A hA => by simpa only [Measure.smul_apply, smul_eq_mul] using (hSets A hA).1,
    Measure.le_iff.mpr fun A hA => by simpa only [Measure.smul_apply, smul_eq_mul] using (hSets A hA).2⟩

/-- The native Euclidean chart coordinates record the two tangential
parameters and the physical radius, in that order. -/
@[expose] noncomputable def sphericalCellNativeParameter : Point ≃ₜ SphericalCellParameter where
  toFun x := ((x 0, x 1), x 2)
  invFun p := WithLp.toLp 2 ![p.1.1, p.1.2, p.2]
  left_inv x := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp
  right_inv p := by simp
  continuous_toFun := by
    have h (i : Fin 3) : Continuous (fun x : Point => x i) := (EuclideanSpace.proj i).continuous
    exact ((h 0).prodMk (h 1)).prodMk (h 2)
  continuous_invFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop

/-- The closed physical shell parameter box in the native Euclidean metric. -/
@[expose] def sphericalCellNativeBox (h : ℝ) : Set Point :=
  sphericalCellNativeParameter ⁻¹' sphericalCellParameterBox h

/-- The same actual shell chart with native three-dimensional coordinates. -/
@[expose] noncomputable def sphericalCellNativePoint (c : Point) (h : ℝ) (f : TensorGridSquare) : Point → Point :=
  sphericalCellPoint c h f ∘ sphericalCellNativeParameter

private theorem dist_cellNativeParameter_bounds (p q : Point) :
    dist (sphericalCellNativeParameter p) (sphericalCellNativeParameter q) ≤ dist p q ∧
      dist p q ≤ 3 * dist (sphericalCellNativeParameter p) (sphericalCellNativeParameter q) := by
  change dist (((p 0, p 1), p 2) : SphericalCellParameter) ((q 0, q 1), q 2) ≤ dist p q ∧
    dist p q ≤ 3 * dist (((p 0, p 1), p 2) : SphericalCellParameter) ((q 0, q 1), q 2)
  simp only [Prod.dist_eq]
  constructor
  · have h (i : Fin 3) : dist (p i) (q i) ≤ dist p q := by
      simpa only [Real.dist_eq, dist_eq_norm p q, PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (p - q) i
    exact max_le (max_le (h 0) (h 1)) (h 2)
  · let D := max (max (dist (p 0) (q 0)) (dist (p 1) (q 1))) (dist (p 2) (q 2))
    have hD : 0 ≤ D := dist_nonneg.trans (le_max_right _ _)
    have hg : ‖WithLp.ofLp (p - q)‖ ≤ D := by
      apply (pi_norm_le_iff_of_nonneg hD).mpr
      intro i
      fin_cases i
      · change ‖p 0 - q 0‖ ≤ D
        rw [← dist_eq_norm]
        exact (le_max_left _ _).trans (le_max_left _ _)
      · change ‖p 1 - q 1‖ ≤ D
        rw [← dist_eq_norm]
        exact (le_max_right _ _).trans (le_max_left _ _)
      · change ‖p 2 - q 2‖ ≤ D
        rw [← dist_eq_norm]
        exact le_max_right _ _
    rw [dist_eq_norm p q]
    exact (StratificationTheory.cube_coordinate_norm_comparison (p - q)).2.trans
      (mul_le_mul_of_nonneg_left hg (by norm_num))

/-- Two-sided chart constants in the native Euclidean coordinates, independent
of the selected cell and its scale. -/
theorem sphericalCellNativePoint_dist_bounds {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) {p q : Point}
    (hp : p ∈ sphericalCellNativeBox h) (hq : q ∈ sphericalCellNativeBox h) :
    dist (sphericalCellNativePoint c h f p) (sphericalCellNativePoint c h f q) ≤ 65 * dist p q ∧
      dist p q ≤ 204 * dist (sphericalCellNativePoint c h f p) (sphericalCellNativePoint c h f q) := by
  have hStep := sphericalCellPoint_dist_bounds hh hh' hc hm hf hp hq
  have hCoord := dist_cellNativeParameter_bounds p q
  constructor
  · exact hStep.1.trans (mul_le_mul_of_nonneg_left hCoord.1 (by norm_num))
  · have h := hCoord.2.trans (mul_le_mul_of_nonneg_left hStep.2 (by norm_num : (0 : ℝ) ≤ 3))
    simpa only [sphericalCellNativePoint, Function.comp_apply, ← mul_assoc, show (3 : ℝ) * 68 = 204 by norm_num] using h

private theorem sphericalCellNativeBox_convex (h : ℝ) : Convex ℝ (sphericalCellNativeBox h) := by
  change Convex ℝ ((((EuclideanSpace.proj 0) ⁻¹' Icc 0 h) ∩ ((EuclideanSpace.proj 1) ⁻¹' Icc 0 h)) ∩
    ((EuclideanSpace.proj 2) ⁻¹' Icc (1 - h) 1))
  exact (((convex_Icc (0 : ℝ) h).linear_preimage (EuclideanSpace.proj (0 : Fin 3)).toLinearMap).inter
    ((convex_Icc (0 : ℝ) h).linear_preimage (EuclideanSpace.proj (1 : Fin 3)).toLinearMap)).inter
      ((convex_Icc (1 - h) 1).linear_preimage (EuclideanSpace.proj (2 : Fin 3)).toLinearMap)

/-- Each actual cell frontier has zero three-dimensional volume. -/
theorem sphericalClosedCell_frontier_volume {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) :
    (volume : Measure Point) (frontier (sphericalClosedCell c h f)) = 0 := by
  let B := sphericalCellNativeBox h
  have hB : IsClosed B := by
    apply IsClosed.preimage sphericalCellNativeParameter.continuous
    exact (isClosed_Icc.prod isClosed_Icc).prod isClosed_Icc
  have hBnd : frontier B ⊆ B := frontier_subset_closure.trans_eq hB.closure_eq
  have hLip : LipschitzOnWith 65 (sphericalCellNativePoint c h f) B :=
    LipschitzOnWith.of_dist_le_mul fun _ hp _ hq => (sphericalCellNativePoint_dist_bounds hh hh' hc hm hf hp hq).1
  have hV := euclideanHausdorff_lipschitzOn_image_le_volume hLip hBnd
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume, finrank_euclideanSpace_fin] at hV
  have hBoxNull : (volume : Measure Point) (frontier B) = 0 := (sphericalCellNativeBox_convex h).addHaar_frontier volume
  rw [hBoxNull, mul_zero] at hV
  have hImg : sphericalCellNativePoint c h f '' frontier B = frontier (sphericalClosedCell c h f) := by
    rw [sphericalClosedCell_frontier hh hh' hc hm hf]
    change (sphericalCellPoint c h f ∘ sphericalCellNativeParameter) ''
      frontier (sphericalCellNativeParameter ⁻¹' sphericalCellParameterBox h) = _
    rw [← sphericalCellNativeParameter.preimage_frontier]
    let e := sphericalCellNativeParameter
    change (fun x => sphericalCellPoint c h f (e x)) '' (e ⁻¹' frontier (sphericalCellParameterBox h)) = _
    rw [← image_image (sphericalCellPoint c h f) e, image_preimage_eq _ e.surjective]
  exact le_antisymm (hImg ▸ hV) bot_le

/-- At volume-almost every point, the radial annulus is the union of the
actual disjoint cell interiors. -/
theorem sphericalCell_interior_ae_partition {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4)) :
    (⋃ f ∈ cubeBoundarySquares m, interior (sphericalClosedCell c h f))
      =ᵐ[(volume : Measure Point)] radialAnnulus 0 (1 - h) 1 := by
  classical
  have hPart :
      (⋃ f ∈ cubeBoundarySquares m, interior (sphericalClosedCell c h f))
        =ᵐ[(volume : Measure Point)] (⋃ f ∈ cubeBoundarySquares m, sphericalClosedCell c h f) :=
    ae_eq_set_biUnion (cubeBoundarySquares m).finite_toSet.countable fun f hf =>
      interior_ae_eq_of_null_frontier (sphericalClosedCell_frontier_volume hh hh' hc hm hf)
  rw [iUnion_sphericalClosedCell_eq_closedShell hh hh' hc hm] at hPart
  refine hPart.trans ?_
  have hSphere (r : ℝ) : ∀ᵐ z ∂(volume : Measure Point), z ∉ sphere (0 : Point) r := by
    rw [ae_iff]
    simpa only [not_not, setOf_mem_eq] using Measure.addHaar_sphere volume (0 : Point) r
  filter_upwards [hSphere (1 - h), hSphere 1] with z hz₀ hz₁
  rw [mem_sphere, dist_zero_right] at hz₀ hz₁
  change (‖z‖ ∈ Icc (1 - h) 1) = (1 - h < ‖z - 0‖ ∧ ‖z - 0‖ < 1)
  rw [sub_zero]
  exact propext ⟨fun hz => ⟨lt_of_le_of_ne hz.1 (fun he => hz₀ he.symm), lt_of_le_of_ne hz.2 hz₁⟩,
    fun hz => ⟨hz.1.le, hz.2.le⟩⟩

end Thesis
