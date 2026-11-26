module

public import Thesis.Interpolation.SphericalGridFaces
public import Thesis.Interpolation.SphericalSideChart
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Square and three-dimensional cell charts for the selected spherical lattice. -/

public section

open Filter Metric Set
open scoped ContDiff NNReal Topology

namespace Thesis

/-- The affine physical square has two orthogonal unit coordinate directions. -/
theorem tensorGridSquarePoint_dist_bounds (y : Point) (a : TensorGridFaceAxes) (p q : ℝ × ℝ) :
    dist p q ≤ dist (tensorGridSquarePoint y a p.1 p.2) (tensorGridSquarePoint y a q.1 q.2) ∧
      dist (tensorGridSquarePoint y a p.1 p.2) (tensorGridSquarePoint y a q.1 q.2) ≤ 2 * dist p q := by
  let u : Point := EuclideanSpace.single a.val.1 (1 : ℝ)
  let v : Point := EuclideanSpace.single a.val.2 (1 : ℝ)
  let d : Point := (p.1 - q.1) • u + (p.2 - q.2) • v
  have hSub : tensorGridSquarePoint y a p.1 p.2 - tensorGridSquarePoint y a q.1 q.2 = d := by
    unfold tensorGridSquarePoint
    change y + p.1 • u + p.2 • v - (y + q.1 • u + q.2 • v) = d
    simp only [d, sub_smul]
    abel
  have hFirst : d a.val.1 = p.1 - q.1 := by
    simp [d, u, v, PiLp.add_apply, PiLp.smul_apply, a.property]
  have hSecond : d a.val.2 = p.2 - q.2 := by
    simp [d, u, v, PiLp.add_apply, PiLp.smul_apply, Ne.symm a.property]
  rw [dist_eq_norm (tensorGridSquarePoint y a p.1 p.2), hSub, Prod.dist_eq]
  constructor
  · apply max_le
    · simpa only [Real.dist_eq, ← hFirst, Real.norm_eq_abs] using PiLp.norm_apply_le d a.val.1
    · simpa only [Real.dist_eq, ← hSecond, Real.norm_eq_abs] using PiLp.norm_apply_le d a.val.2
  · calc
      ‖d‖ ≤ ‖(p.1 - q.1) • u‖ + ‖(p.2 - q.2) • v‖ := norm_add_le _ _
      _ = dist p.1 q.1 + dist p.2 q.2 := by
        simp only [u, v, norm_smul, PiLp.norm_single, norm_one, mul_one, dist_eq_norm]
      _ ≤ _ := by
        linarith only [le_max_left (dist p.1 q.1) (dist p.2 q.2),
          le_max_right (dist p.1 q.1) (dist p.2 q.2)]

/-- The same radial normalization defines each point of the spherical square
and of its four boundary edges. -/
@[expose] noncomputable def sphericalFacePoint (c : Point) (h : ℝ) (f : TensorGridSquare)
    (p : ℝ × ℝ) : Point :=
  NormedSpace.normalize (tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 p.1 p.2)

/-- Uniform two-sided distance bounds for the projected physical square. -/
theorem sphericalFacePoint_dist_bounds {c : Point} {h : ℝ} (hh : 0 < h) {m : ℕ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) {p q : ℝ × ℝ}
    (hp : p ∈ Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) h) (hq : q ∈ Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) h) :
    sphericalFacePoint c h f p ∈ sphere (0 : Point) 1 ∧
      sphericalFacePoint c h f q ∈ sphere (0 : Point) 1 ∧
      dist (sphericalFacePoint c h f p) (sphericalFacePoint c h f q) ≤ 64 * dist p q ∧
      dist p q ≤ 17 * dist (sphericalFacePoint c h f p) (sphericalFacePoint c h f q) := by
  obtain ⟨_, _, _, e, he, hLip, hInvLip⟩ := shiftedCoordinateCube_geometry hc hm
  let x : frontier (shiftedCoordinateCube c ((m : ℝ) * h)) :=
    ⟨_, tensorGridSquarePoint_mem_frontier hh hf hp.1 hp.2⟩
  let y : frontier (shiftedCoordinateCube c ((m : ℝ) * h)) :=
    ⟨_, tensorGridSquarePoint_mem_frontier hh hf hq.1 hq.2⟩
  have hSphere (z : frontier (shiftedCoordinateCube c ((m : ℝ) * h))) :
      NormedSpace.normalize z.val ∈ sphere (0 : Point) 1 := he z ▸ (e.symm z).property
  have hUpper := hInvLip.dist_le_mul x y
  have hLower := hLip.dist_le_mul (e.symm x) (e.symm y)
  simp only [Subtype.dist_eq, he, NNReal.coe_ofNat] at hUpper hLower
  rw [e.apply_symm_apply, e.apply_symm_apply] at hLower
  obtain ⟨hAffineLow, hAffineUp⟩ := tensorGridSquarePoint_dist_bounds (tensorGridVertex c h f.1) f.2 p q
  change dist p q ≤ dist x.val y.val at hAffineLow
  change dist x.val y.val ≤ 2 * dist p q at hAffineUp
  refine ⟨hSphere x, hSphere y, ?_, ?_⟩
  · change dist (NormedSpace.normalize x.val) (NormedSpace.normalize y.val) ≤ 64 * dist p q
    linarith only [hUpper, hAffineUp]
  · exact hAffineLow.trans hLower

/-- The two physical tangential parameters and absolute radius of the shell cell. -/
abbrev SphericalCellParameter := (ℝ × ℝ) × ℝ

/-- All three side lengths of the shell cell parameter box equal `h`. -/
@[expose] def sphericalCellParameterBox (h : ℝ) : Set SphericalCellParameter :=
  (Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) h) ×ˢ Icc (1 - h) 1

/-- The parameter boundary consists of the six coordinate faces of the box. -/
theorem sphericalCellParameterBox_mem_frontier {h : ℝ} {p : SphericalCellParameter} :
    p ∈ frontier (sphericalCellParameterBox h) ↔
      p ∈ sphericalCellParameterBox h ∧ (p.1.1 = 0 ∨ p.1.1 = h ∨ p.1.2 = 0 ∨ p.1.2 = h ∨
        p.2 = 1 - h ∨ p.2 = 1) := by
  have hClosed : IsClosed (sphericalCellParameterBox h) := (isClosed_Icc.prod isClosed_Icc).prod isClosed_Icc
  rw [frontier, hClosed.closure_eq]
  change _ ∈ sphericalCellParameterBox h \ interior ((Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) h) ×ˢ Icc (1 - h) 1) ↔ _
  rw [interior_prod_eq, interior_prod_eq, interior_Icc, interior_Icc]
  constructor
  · rintro ⟨hp, hOut⟩
    refine ⟨hp, ?_⟩
    by_contra hB
    push Not at hB
    exact hOut ⟨⟨⟨lt_of_le_of_ne hp.1.1.1 hB.1.symm, lt_of_le_of_ne hp.1.1.2 hB.2.1⟩,
      ⟨lt_of_le_of_ne hp.1.2.1 hB.2.2.1.symm, lt_of_le_of_ne hp.1.2.2 hB.2.2.2.1⟩⟩,
      ⟨lt_of_le_of_ne hp.2.1 hB.2.2.2.2.1.symm, lt_of_le_of_ne hp.2.2 hB.2.2.2.2.2⟩⟩
  · rintro ⟨hp, hB⟩
    refine ⟨hp, ?_⟩
    rintro ⟨⟨⟨hs₀, hs₁⟩, ⟨ht₀, ht₁⟩⟩, ⟨hr₀, hr₁⟩⟩
    rcases hB with hs | hs | ht | ht | hr | hr
    · exact (ne_of_gt hs₀) hs
    · exact (ne_of_lt hs₁) hs
    · exact (ne_of_gt ht₀) ht
    · exact (ne_of_lt ht₁) ht
    · exact (ne_of_gt hr₀) hr
    · exact (ne_of_lt hr₁) hr

/-- The actual radial cell parameterization over a projected lattice square. -/
@[expose] noncomputable def sphericalCellPoint (c : Point) (h : ℝ) (f : TensorGridSquare)
    (p : SphericalCellParameter) : Point :=
  p.2 • sphericalFacePoint c h f p.1

/-- The closed shell cell swept out by the same projected lattice square. -/
@[expose] noncomputable def sphericalClosedCell (c : Point) (h : ℝ) (f : TensorGridSquare) : Set Point :=
  sphericalCellPoint c h f '' sphericalCellParameterBox h

/-- Uniform bounds in the product metric on the entire closed shell cell. -/
theorem sphericalCellPoint_dist_bounds {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) {p q : SphericalCellParameter}
    (hp : p ∈ sphericalCellParameterBox h) (hq : q ∈ sphericalCellParameterBox h) :
    dist (sphericalCellPoint c h f p) (sphericalCellPoint c h f q) ≤ 65 * dist p q ∧
      dist p q ≤ 68 * dist (sphericalCellPoint c h f p) (sphericalCellPoint c h f q) := by
  let x := sphericalFacePoint c h f p.1
  let y := sphericalFacePoint c h f q.1
  obtain ⟨hx, hy, hUpper, hLower⟩ := sphericalFacePoint_dist_bounds hh hc hm hf hp.1 hq.1
  have hx₁ : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
  have hy₁ : ‖y‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hy
  have ha : (1 / 2 : ℝ) ≤ 1 - h := by linarith only [hh']
  obtain ⟨hRadUpper, hRadLower, hAngLower⟩ := radial_dist_bounds (r := p.2) (s := q.2) hx₁ hy₁
    ⟨ha.trans hp.2.1, hp.2.2⟩ ⟨ha.trans hq.2.1, hq.2.2⟩
  change dist (p.2 • x) (q.2 • y) ≤ 65 * dist p q ∧ dist p q ≤ 68 * dist (p.2 • x) (q.2 • y)
  rw [Prod.dist_eq]
  constructor
  · have h := mul_le_mul_of_nonneg_left (le_max_left (dist p.1 q.1) (dist p.2 q.2))
      (by norm_num : (0 : ℝ) ≤ 64)
    change dist x y ≤ 64 * dist p.1 q.1 at hUpper
    linarith only [hRadUpper, hUpper, h, le_max_right (dist p.1 q.1) (dist p.2 q.2)]
  · apply max_le
    · change dist p.1 q.1 ≤ 17 * dist x y at hLower
      linarith only [hLower, hAngLower]
    · linarith only [hRadLower, dist_nonneg (x := p.2 • x) (y := q.2 • y)]

/-- Global bi-Lipschitz coordinates on the actual closed shell cell with the
same pointwise parameterization used for the edges. -/
theorem sphericalClosedCell_geometry {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) :
    IsCompact (sphericalClosedCell c h f) ∧
      ∃ e : sphericalCellParameterBox h ≃ₜ sphericalClosedCell c h f,
        (∀ p, (e p).val = sphericalCellPoint c h f p.val) ∧
          LipschitzWith 65 e ∧ LipschitzWith 68 e.symm := by
  let F : sphericalCellParameterBox h → sphericalClosedCell c h f :=
    fun p => ⟨sphericalCellPoint c h f p.val, ⟨p.val, p.property, rfl⟩⟩
  have hLip : LipschitzWith 65 F := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    exact (sphericalCellPoint_dist_bounds hh hh' hc hm hf p.property q.property).1
  have hAnti : AntilipschitzWith 68 F := by
    apply AntilipschitzWith.of_le_mul_dist
    intro p q
    exact (sphericalCellPoint_dist_bounds hh hh' hc hm hf p.property q.property).2
  have hSurj : Function.Surjective F := by
    intro y
    obtain ⟨p, hp, hy⟩ := y.property
    exact ⟨⟨p, hp⟩, Subtype.ext hy⟩
  let e := (hAnti.isEmbedding hLip.continuous).toHomeomorphOfSurjective hSurj
  refine ⟨?_, e, fun _ => rfl, hLip, ?_⟩
  · have hK : IsCompact (sphericalCellParameterBox h) :=
      (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
    apply hK.image_of_continuousOn
    rw [continuousOn_iff_continuous_restrict]
    exact continuous_subtype_val.comp hLip.continuous
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    have hb := hAnti.le_mul_dist (e.symm p) (e.symm q)
    change _ ≤ _ * dist (e (e.symm p)) (e (e.symm q)) at hb
    rwa [e.apply_symm_apply, e.apply_symm_apply] at hb

/-- The two spherical caps and four lateral faces use the same pointwise
charts on every common edge. -/
theorem sphericalCellPoint_boundary (c : Point) (h : ℝ) (f : TensorGridSquare) (s t r : ℝ) :
    sphericalCellPoint c h f ((s, t), 1) = sphericalFacePoint c h f (s, t) ∧
      sphericalCellPoint c h f ((s, t), 1 - h) = (1 - h) • sphericalFacePoint c h f (s, t) ∧
      sphericalCellPoint c h f ((s, 0), r) = sphericalLateralEdge c h ⟨f.1, f.2.val.1⟩ (s, r) ∧
      sphericalCellPoint c h f ((s, h), r) =
        sphericalLateralEdge c h ⟨f.1 + Pi.single f.2.val.2 (1 : ℤ), f.2.val.1⟩ (s, r) ∧
      sphericalCellPoint c h f ((0, t), r) = sphericalLateralEdge c h ⟨f.1, f.2.val.2⟩ (t, r) ∧
      sphericalCellPoint c h f ((h, t), r) =
        sphericalLateralEdge c h ⟨f.1 + Pi.single f.2.val.1 (1 : ℤ), f.2.val.2⟩ (t, r) := by
  obtain ⟨hs₀, hs₁, _, _⟩ := tensorGridSquarePoint_boundary c h f s
  obtain ⟨_, _, ht₀, ht₁⟩ := tensorGridSquarePoint_boundary c h f t
  simp only [sphericalCellPoint, sphericalFacePoint, sphericalLateralEdge, one_smul, hs₀, hs₁, ht₀, ht₁,
    and_self]

/-- The closed coordinate cube and Euclidean closed ball have the same
radius along any ray when measured in their respective norms. -/
@[expose] def centeredCoordinateCube (R : ℝ) : Set Point :=
  {x | ‖WithLp.ofLp x‖ ≤ R}

/-- Radial map sending the maximum coordinate radius to the Euclidean radius. -/
@[expose] noncomputable def coordinateCubeToBall {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (‖WithLp.ofLp x‖ / ‖x‖) • x

/-- Inverse radial map sending the Euclidean radius to the maximum coordinate radius. -/
@[expose] noncomputable def ballToCoordinateCube {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (‖x‖ / ‖WithLp.ofLp x‖) • x

theorem coordinateNorm_pos {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) : 0 < ‖WithLp.ofLp x‖ := by
  refine norm_pos_iff.mpr fun h => hx ?_
  exact (WithLp.equiv 2 (Fin n → ℝ)).injective h

theorem coordinateNorm_smul {n : ℕ} (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖WithLp.ofLp (a • x)‖ = ‖a‖ * ‖WithLp.ofLp x‖ := by
  rw [WithLp.ofLp_smul, norm_smul]

theorem norm_coordinateCubeToBall {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ‖coordinateCubeToBall x‖ = ‖WithLp.ofLp x‖ := by
  by_cases hx : x = 0
  · simp [hx, coordinateCubeToBall]
  rw [coordinateCubeToBall, norm_smul, Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

theorem coordinateNorm_ballToCoordinateCube {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖WithLp.ofLp (ballToCoordinateCube x)‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, ballToCoordinateCube]
  rw [ballToCoordinateCube, coordinateNorm_smul,
    Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)),
    div_mul_cancel₀ _ (coordinateNorm_pos hx).ne']

theorem ballToCoordinateCube_coordinateCubeToBall {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ballToCoordinateCube (coordinateCubeToBall x) = x := by
  by_cases hx : x = 0
  · simp [hx, ballToCoordinateCube, coordinateCubeToBall]
  have hg := (coordinateNorm_pos hx).ne'
  have he := norm_ne_zero_iff.mpr hx
  rw [ballToCoordinateCube, norm_coordinateCubeToBall, coordinateCubeToBall, coordinateNorm_smul,
    Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)), smul_smul]
  have h : ‖WithLp.ofLp x‖ / ((‖WithLp.ofLp x‖ / ‖x‖) * ‖WithLp.ofLp x‖) *
      (‖WithLp.ofLp x‖ / ‖x‖) = 1 := by field_simp
  rw [h, one_smul]

theorem coordinateCubeToBall_ballToCoordinateCube {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    coordinateCubeToBall (ballToCoordinateCube x) = x := by
  by_cases hx : x = 0
  · simp [hx, ballToCoordinateCube, coordinateCubeToBall]
  have hg := (coordinateNorm_pos hx).ne'
  have he := norm_ne_zero_iff.mpr hx
  rw [coordinateCubeToBall, coordinateNorm_ballToCoordinateCube, ballToCoordinateCube, norm_smul,
    Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)), smul_smul]
  have h : ‖x‖ / ((‖x‖ / ‖WithLp.ofLp x‖) * ‖x‖) * (‖x‖ / ‖WithLp.ofLp x‖) = 1 := by field_simp
  rw [h, one_smul]

theorem continuous_coordinateCubeToBall {n : ℕ} :
    Continuous (coordinateCubeToBall (n := n)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    simpa only [ContinuousAt, coordinateCubeToBall, norm_zero, div_zero, zero_smul] using
      (squeeze_zero_norm (f := coordinateCubeToBall) (a := norm)
        (fun y => (norm_coordinateCubeToBall y).le.trans (StratificationTheory.cube_coordinate_norm_comparison y).1)
        (by simpa only [norm_zero] using (continuous_norm.continuousAt (x := (0 : EuclideanSpace ℝ (Fin n)))).tendsto))
  · have hg := (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).norm.continuousAt (x := x)
    exact (hg.div continuous_norm.continuousAt (norm_ne_zero_iff.mpr hx)).smul continuousAt_id

theorem continuous_ballToCoordinateCube {n : ℕ} :
    Continuous (ballToCoordinateCube (n := n)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hB (y : EuclideanSpace ℝ (Fin n)) : ‖ballToCoordinateCube y‖ ≤ (n : ℝ) * ‖y‖ :=
      (StratificationTheory.cube_coordinate_norm_comparison (ballToCoordinateCube y)).2.trans_eq
        (by rw [coordinateNorm_ballToCoordinateCube])
    have hT : Tendsto (fun y : EuclideanSpace ℝ (Fin n) => (n : ℝ) * ‖y‖) (𝓝 0) (𝓝 0) := by
      have hCont : Continuous (fun y : EuclideanSpace ℝ (Fin n) => (n : ℝ) * ‖y‖) :=
        continuous_const.mul continuous_norm
      simpa only [norm_zero, mul_zero] using (hCont.continuousAt (x := (0 : EuclideanSpace ℝ (Fin n)))).tendsto
    simpa only [ContinuousAt, ballToCoordinateCube, norm_zero, zero_div, zero_smul] using
      (squeeze_zero_norm hB hT)
  · have hg := (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).norm.continuousAt (x := x)
    exact (continuous_norm.continuousAt.div hg (coordinateNorm_pos hx).ne').smul continuousAt_id

/-- Literal radial homeomorphism between a centered closed cube and the
closed ball of the same radius, including their centers and boundaries. -/
noncomputable def centeredCoordinateCubeHomeomorph (R : ℝ) : centeredCoordinateCube R ≃ₜ closedBall (0 : Point) R where
  toFun x := ⟨coordinateCubeToBall x.val, by simpa only [mem_closedBall_zero_iff, norm_coordinateCubeToBall,
    centeredCoordinateCube, mem_setOf_eq] using x.property⟩
  invFun x := ⟨ballToCoordinateCube x.val, by simpa only [centeredCoordinateCube, mem_setOf_eq,
    coordinateNorm_ballToCoordinateCube] using mem_closedBall_zero_iff.mp x.property⟩
  left_inv x := Subtype.ext (ballToCoordinateCube_coordinateCubeToBall x.val)
  right_inv x := Subtype.ext (coordinateCubeToBall_ballToCoordinateCube x.val)
  continuous_toFun := (continuous_coordinateCubeToBall.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_ballToCoordinateCube.comp continuous_subtype_val).subtype_mk _

private noncomputable def sphericalCellCenteredCoordinates (h : ℝ) : SphericalCellParameter ≃ₜ Point where
  toFun p := WithLp.toLp 2 ![p.1.1 - h / 2, p.1.2 - h / 2, p.2 - (1 - h / 2)]
  invFun x := ((x 0 + h / 2, x 1 + h / 2), x 2 + (1 - h / 2))
  left_inv p := by simp
  right_inv x := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    have hp (i : Fin 3) : Continuous (fun x : Point => x i) := (EuclideanSpace.proj i).continuous
    fun_prop

private theorem sphericalCellCenteredCoordinates_image {h : ℝ} (hh : 0 ≤ h) :
    sphericalCellCenteredCoordinates h '' sphericalCellParameterBox h = centeredCoordinateCube (h / 2) := by
  let e := sphericalCellCenteredCoordinates h
  have hMem (p : SphericalCellParameter) :
      e p ∈ centeredCoordinateCube (h / 2) ↔ p ∈ sphericalCellParameterBox h := by
    change ‖WithLp.ofLp (e p)‖ ≤ h / 2 ↔ _
    rw [pi_norm_le_iff_of_nonneg (div_nonneg hh (by norm_num : (0 : ℝ) ≤ 2))]
    have hFirst : WithLp.ofLp (e p) 0 = p.1.1 - h / 2 := rfl
    have hSecond : WithLp.ofLp (e p) 1 = p.1.2 - h / 2 := rfl
    have hRadius : WithLp.ofLp (e p) 2 = p.2 - (1 - h / 2) := rfl
    constructor
    · intro hp
      have hs := hp 0
      have ht := hp 1
      have hr := hp 2
      simp only [hFirst, hSecond, hRadius, Real.norm_eq_abs, abs_le] at hs ht hr
      exact ⟨⟨⟨by linarith only [hs.1], by linarith only [hs.2]⟩,
        ⟨by linarith only [ht.1], by linarith only [ht.2]⟩⟩,
        ⟨by linarith only [hr.1], by linarith only [hr.2]⟩⟩
    · intro hp i
      fin_cases i
      · change ‖p.1.1 - h / 2‖ ≤ h / 2
        exact abs_le.mpr ⟨by linarith only [hp.1.1.1], by linarith only [hp.1.1.2]⟩
      · change ‖p.1.2 - h / 2‖ ≤ h / 2
        exact abs_le.mpr ⟨by linarith only [hp.1.2.1], by linarith only [hp.1.2.2]⟩
      · change ‖p.2 - (1 - h / 2)‖ ≤ h / 2
        exact abs_le.mpr ⟨by linarith only [hp.2.1], by linarith only [hp.2.2]⟩
  change e '' _ = _
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (hMem p).2 hp
  · intro hx
    exact ⟨e.symm x, (hMem _).1 (by rwa [e.apply_symm_apply]), e.apply_symm_apply x⟩

/-- The parameter cube is homeomorphic to a closed ball at its actual scale. -/
noncomputable def sphericalCellParameterBallHomeomorph {h : ℝ} (hh : 0 ≤ h) :
    sphericalCellParameterBox h ≃ₜ closedBall (0 : Point) (h / 2) :=
  ((sphericalCellCenteredCoordinates h).image _).trans
    ((Homeomorph.setCongr (sphericalCellCenteredCoordinates_image hh)).trans
      (centeredCoordinateCubeHomeomorph (h / 2)))

private theorem centeredCoordinateCube_frontier {R : ℝ} (hR : R ≠ 0) :
    frontier (centeredCoordinateCube R) = {x | ‖WithLp.ofLp x‖ = R} := by
  let e : Point ≃ₜ (Fin 3 → ℝ) := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
  have hPre : e ⁻¹' closedBall 0 R = centeredCoordinateCube R := by
    ext x
    exact mem_closedBall_zero_iff
  rw [← hPre, ← e.preimage_frontier, frontier_closedBall _ hR]
  ext x
  rw [mem_preimage, mem_sphere, dist_zero_right, mem_setOf_eq]
  rfl

/-- The radial cube-to-ball map carries the parameter frontier to the sphere. -/
theorem sphericalCellParameterBallHomeomorph_mem_sphere {h : ℝ} (hh : 0 < h)
    (p : sphericalCellParameterBox h) :
    (sphericalCellParameterBallHomeomorph hh.le p).val ∈ sphere (0 : Point) (h / 2) ↔
      p.val ∈ frontier (sphericalCellParameterBox h) := by
  let e := sphericalCellCenteredCoordinates h
  change coordinateCubeToBall (e p.val) ∈ sphere (0 : Point) (h / 2) ↔ _
  rw [mem_sphere, dist_zero_right, norm_coordinateCubeToBall]
  change e p.val ∈ {x : Point | ‖WithLp.ofLp x‖ = h / 2} ↔ _
  have hr : h / 2 ≠ 0 := (div_pos hh (by norm_num : (0 : ℝ) < 2)).ne'
  rw [← centeredCoordinateCube_frontier hr, ← sphericalCellCenteredCoordinates_image hh.le,
    ← Homeomorph.image_frontier]
  constructor
  · rintro ⟨q, hq, heq⟩
    exact e.injective heq ▸ hq
  · intro hp
    exact ⟨p.val, hp, rfl⟩

private theorem finThree_axes {i j k l : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    l = i ∨ l = j ∨ l = k := by
  simp only [← Fin.val_inj] at *
  omega

private theorem exists_openRadialSquareChart (y : Point) (a : TensorGridFaceAxes) (j : Fin 3)
    (hj₁ : j ≠ a.val.1) (hj₂ : j ≠ a.val.2) (hy : y j ≠ 0) :
    ∃ e : OpenPartialHomeomorph SphericalCellParameter Point,
      e.source = (univ : Set (ℝ × ℝ)) ×ˢ Ioi 0 ∧ e.target = {z | 0 < y j * z j} ∧
      (∀ p, e p = p.2 • NormedSpace.normalize (tensorGridSquarePoint y a p.1.1 p.1.2)) ∧
      ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let A : SphericalCellParameter → Point := fun p => tensorGridSquarePoint y a p.1.1 p.1.2
  let F : SphericalCellParameter → Point := fun p => p.2 • NormedSpace.normalize (A p)
  let L : Point → Point := fun z => (y j / z j) • z
  let G : Point → SphericalCellParameter := fun z =>
    (((L z) a.val.1 - y a.val.1, (L z) a.val.2 - y a.val.2), ‖z‖)
  let S : Set SphericalCellParameter := (univ : Set (ℝ × ℝ)) ×ˢ Ioi 0
  let T : Set Point := {z | 0 < y j * z j}
  have hA₁ (p : SphericalCellParameter) : (A p) a.val.1 = y a.val.1 + p.1.1 := by
    simp [A, tensorGridSquarePoint, PiLp.add_apply, PiLp.smul_apply, a.property]
  have hA₂ (p : SphericalCellParameter) : (A p) a.val.2 = y a.val.2 + p.1.2 := by
    simp [A, tensorGridSquarePoint, PiLp.add_apply, PiLp.smul_apply, Ne.symm a.property]
  have hAj (p : SphericalCellParameter) : (A p) j = y j := by
    simp [A, tensorGridSquarePoint, PiLp.add_apply, PiLp.smul_apply, hj₁, hj₂]
  have hA₀ (p : SphericalCellParameter) : A p ≠ 0 := by
    intro hz
    apply hy
    rw [← hAj p, hz]
    rfl
  have hF (p : SphericalCellParameter) : F p = (p.2 / ‖A p‖) • A p := by
    simp only [F, NormedSpace.normalize, smul_smul, div_eq_mul_inv]
  have hFj (p : SphericalCellParameter) : (F p) j = (p.2 / ‖A p‖) * y j := by
    rw [hF, PiLp.smul_apply, hAj, smul_eq_mul]
  have hFr {p : SphericalCellParameter} (hp : p ∈ S) : ‖F p‖ = p.2 := by
    have hr : 0 < p.2 := hp.2
    simp only [F, norm_smul, Real.norm_of_nonneg hr.le, NormedSpace.norm_normalize (hA₀ p), mul_one]
  have hTj {z : Point} (hz : z ∈ T) : z j ≠ 0 := by
    have hp : 0 < y j * z j := hz
    exact (mul_ne_zero_iff.mp hp.ne').2
  have hL {z : Point} (hz : z ∈ T) : (L z) j = y j := by
    simp only [L, PiLp.smul_apply, smul_eq_mul, div_mul_cancel₀ _ (hTj hz)]
  have hMapS : MapsTo F S T := by
    intro p hp
    change 0 < y j * (F p) j
    have hk : 0 < p.2 / ‖A p‖ := div_pos hp.2 (norm_pos_iff.mpr (hA₀ p))
    rw [hFj, mul_left_comm]
    exact mul_pos hk (mul_self_pos.mpr hy)
  have hMapT : MapsTo G T S := by
    intro z hz
    exact ⟨mem_univ _, norm_pos_iff.mpr (fun h => hTj hz (by rw [h]; rfl))⟩
  have hLeft : LeftInvOn G F S := by
    intro p hp
    have hk : p.2 / ‖A p‖ ≠ 0 := (div_pos hp.2 (norm_pos_iff.mpr (hA₀ p))).ne'
    have hLF : L (F p) = A p := by
      change (y j / (F p) j) • F p = A p
      rw [hFj, hF, smul_smul]
      have hCoeff : y j / ((p.2 / ‖A p‖) * y j) * (p.2 / ‖A p‖) = 1 := by
        rw [div_mul_eq_mul_div, mul_comm (y j), div_self (mul_ne_zero hk hy)]
      rw [hCoeff, one_smul]
    change G (F p) = p
    rcases p with ⟨⟨s, t⟩, r⟩
    simp only [G, hLF, hA₁, hA₂, add_sub_cancel_left, hFr hp]
  have hRight : RightInvOn G F T := by
    intro z hz
    have hAG : A (G z) = L z := by
      apply PiLp.ext
      intro i
      rcases finThree_axes a.property hj₁ hj₂ (l := i) with rfl | rfl | rfl
      · rw [hA₁]
        simp [G]
      · rw [hA₂]
        simp [G]
      · rw [hAj, hL hz]
    have ht : 0 < y j * z j := hz
    have hScale : 0 < y j / z j := div_pos_iff.mpr (mul_pos_iff.mp ht)
    change ‖z‖ • NormedSpace.normalize (A (G z)) = z
    rw [hAG, show L z = (y j / z j) • z from rfl, NormedSpace.normalize_smul_of_pos hScale,
      NormedSpace.norm_smul_normalize]
  have hProj (i : Fin 3) : ContDiff ℝ ∞ (fun z : Point => z i) := by
    change ContDiff ℝ ∞ (⇑(EuclideanSpace.proj i : Point →L[ℝ] ℝ))
    exact ContinuousLinearMap.contDiff _
  have hADiff : ContDiff ℝ ∞ A := by
    unfold A tensorGridSquarePoint
    fun_prop
  have hFDiff : ContDiff ℝ ∞ F := by
    rw [show F = (fun p => (p.2 / ‖A p‖) • A p) from funext hF]
    exact (contDiff_snd.div (hADiff.norm ℝ hA₀) fun p => norm_ne_zero_iff.mpr (hA₀ p)).smul hADiff
  have hLDiff : ContDiffOn ℝ ∞ L T :=
    (contDiffOn_const.div (hProj j).contDiffOn fun _ hz => hTj hz).smul contDiffOn_id
  have hGDiff : ContDiffOn ℝ ∞ G T := by
    have hNorm : ContDiffOn ℝ ∞ (fun z : Point => ‖z‖) T :=
      contDiffOn_id.norm ℝ fun z hz h0 => hTj hz (by change z = 0 at h0; rw [h0]; rfl)
    exact (((hProj a.val.1).comp_contDiffOn hLDiff).sub contDiffOn_const).prodMk
      (((hProj a.val.2).comp_contDiffOn hLDiff).sub contDiffOn_const) |>.prodMk hNorm
  let e : OpenPartialHomeomorph SphericalCellParameter Point :=
    { toFun := F
      invFun := G
      source := S
      target := T
      map_source' := hMapS
      map_target' := hMapT
      left_inv' := hLeft
      right_inv' := hRight
      continuousOn_toFun := hFDiff.continuous.continuousOn
      continuousOn_invFun := hGDiff.continuousOn
      open_source := isOpen_univ.prod isOpen_Ioi
      open_target := isOpen_lt continuous_const (continuous_const.mul (hProj j).continuous) }
  exact ⟨e, rfl, rfl, fun _ => rfl, hFDiff, hGDiff⟩

/-- The actual radial chart extends smoothly to an open neighborhood of the
whole box and has a smooth inverse on its target half-space. -/
theorem exists_sphericalCellOpenChart {c : Point} {h : ℝ} (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) :
    ∃ e : OpenPartialHomeomorph SphericalCellParameter Point,
      (e : SphericalCellParameter → Point) = sphericalCellPoint c h f ∧
      sphericalCellParameterBox h ⊆ e.source ∧ sphericalClosedCell c h f ⊆ e.target ∧
      e.IsImage (sphericalCellParameterBox h) (sphericalClosedCell c h f) ∧
      ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨_, _, _, _, j, hj₁, hj₂, hj⟩ := mem_cubeBoundarySquares_iff.mp hf
  let y := tensorGridVertex c h f.1
  have hy : y j ≠ 0 := by
    change c j + (f.1 j : ℝ) * h ≠ 0
    rcases eq_or_eq_neg_of_abs_eq hj with hp | hn
    · have he : (f.1 j : ℝ) = m := by exact_mod_cast hp
      rw [he]
      exact ne_of_gt (by linarith only [(hc j).1, hm.1])
    · have he : (f.1 j : ℝ) = -(m : ℝ) := by exact_mod_cast hn
      rw [he]
      exact ne_of_lt (by linarith only [(hc j).2, hm.1])
  obtain ⟨e, hSrc, _, hEq, hSmooth, hInvSmooth⟩ := exists_openRadialSquareChart y f.2 j hj₁ hj₂ hy
  have hFun : (e : SphericalCellParameter → Point) = sphericalCellPoint c h f := funext hEq
  have hBox : sphericalCellParameterBox h ⊆ e.source := by
    rw [hSrc]
    intro p hp
    exact ⟨mem_univ _, show 0 < p.2 from by linarith only [hp.2.1, hh']⟩
  have hCell : sphericalClosedCell c h f ⊆ e.target := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← hFun]
    exact e.map_source (hBox hp)
  refine ⟨e, hFun, hBox, hCell, OpenPartialHomeomorph.IsImage.of_image_eq ?_, hSmooth, hInvSmooth⟩
  rw [inter_eq_right.mpr hBox, inter_eq_right.mpr hCell, hFun]
  rfl

/-- The ambient boundary of the actual three-dimensional shell cell is exactly
the image of the six faces of its parameter box. -/
theorem sphericalClosedCell_frontier {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) :
    frontier (sphericalClosedCell c h f) = sphericalCellPoint c h f '' frontier (sphericalCellParameterBox h) := by
  obtain ⟨e, hFun, hBox, hCell, hImg, _, _⟩ := exists_sphericalCellOpenChart hh' hc hm hf
  have hBndBox : frontier (sphericalCellParameterBox h) ⊆ e.source := by
    have hClosed : IsClosed (sphericalCellParameterBox h) := (isClosed_Icc.prod isClosed_Icc).prod isClosed_Icc
    exact (frontier_subset_closure.trans_eq hClosed.closure_eq).trans hBox
  have hBndCell : frontier (sphericalClosedCell c h f) ⊆ e.target := by
    have hClosed := (sphericalClosedCell_geometry hh hh' hc hm hf).1.isClosed
    exact (frontier_subset_closure.trans_eq hClosed.closure_eq).trans hCell
  have hBnd := hImg.frontier.image_eq
  rw [inter_eq_right.mpr hBndBox, inter_eq_right.mpr hBndCell, hFun] at hBnd
  exact hBnd.symm

/-- A cell interior is the actual image of the coordinatewise open box. -/
theorem sphericalClosedCell_interior {c : Point} {h : ℝ} (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) :
    interior (sphericalClosedCell c h f) = sphericalCellPoint c h f ''
      ((Ioo (0 : ℝ) h ×ˢ Ioo (0 : ℝ) h) ×ˢ Ioo (1 - h) 1) := by
  obtain ⟨e, hFun, hBox, hCell, hImg, _, _⟩ := exists_sphericalCellOpenChart hh' hc hm hf
  have hInt := hImg.interior.image_eq
  rw [inter_eq_right.mpr (interior_subset.trans hBox), inter_eq_right.mpr (interior_subset.trans hCell), hFun] at hInt
  rw [← hInt, sphericalCellParameterBox, interior_prod_eq, interior_prod_eq, interior_Icc, interior_Icc]

/-- The closed shell cell and its ambient boundary correspond to the closed
ball of radius half the mesh size and its sphere. -/
theorem sphericalClosedCell_homeomorph_ball {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) :
    ∃ e : sphericalClosedCell c h f ≃ₜ closedBall (0 : Point) (h / 2),
      ∀ x, (e x).val ∈ sphere (0 : Point) (h / 2) ↔ x.val ∈ frontier (sphericalClosedCell c h f) := by
  obtain ⟨_, e, he, _, _⟩ := sphericalClosedCell_geometry hh hh' hc hm hf
  refine ⟨e.symm.trans (sphericalCellParameterBallHomeomorph hh.le), fun x => ?_⟩
  change (sphericalCellParameterBallHomeomorph hh.le (e.symm x)).val ∈ sphere (0 : Point) (h / 2) ↔ _
  rw [sphericalCellParameterBallHomeomorph_mem_sphere hh, sphericalClosedCell_frontier hh hh' hc hm hf]
  constructor
  · intro hx
    refine ⟨(e.symm x).val, hx, ?_⟩
    rw [← he, e.apply_symm_apply]
  · rintro ⟨p, hp, hEq⟩
    let q : sphericalCellParameterBox h := ⟨p, (sphericalCellParameterBox_mem_frontier.mp hp).1⟩
    have hEx : e q = x := Subtype.ext ((he q).trans hEq)
    rwa [← hEx, e.symm_apply_apply]

private theorem exists_integerMeshInterval {m : ℕ} (hm : 0 < m) {a h x : ℝ} (hh : 0 < h)
    (hx : x ∈ Icc (a - (m : ℝ) * h) (a + (m : ℝ) * h)) :
    ∃ b : ℤ, -(m : ℤ) ≤ b ∧ b < (m : ℤ) ∧ ∃ t ∈ Icc (0 : ℝ) h, x = a + (b : ℝ) * h + t := by
  let v := (x - a) / h
  have hvl : -(m : ℝ) ≤ v := (le_div_iff₀ hh).mpr (by linarith only [hx.1])
  have hvu : v ≤ (m : ℝ) := (div_le_iff₀ hh).mpr (by linarith only [hx.2])
  have hvMul : v * h = x - a := div_mul_cancel₀ _ hh.ne'
  have hb : ∃ b : ℤ, -(m : ℤ) ≤ b ∧ b < (m : ℤ) ∧ (b : ℝ) ≤ v ∧ v ≤ (b : ℝ) + 1 := by
    rcases hvu.lt_or_eq with hlt | he
    · exact ⟨⌊v⌋, Int.le_floor.mpr (by simpa only [Int.cast_neg, Int.cast_natCast] using hvl),
        Int.floor_lt.mpr (by simpa only [Int.cast_natCast] using hlt),
        Int.floor_le _, (Int.lt_floor_add_one _).le⟩
    · refine ⟨(m : ℤ) - 1, by omega, by omega, ?_, ?_⟩ <;>
        simp only [he, Int.cast_sub, Int.cast_natCast, Int.cast_one] <;> linarith
  obtain ⟨b, hbl, hbu, h₀, h₁⟩ := hb
  refine ⟨b, hbl, hbu, (v - (b : ℝ)) * h, ⟨mul_nonneg (sub_nonneg.mpr h₀) hh.le, ?_⟩, ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right (sub_le_iff_le_add'.mpr h₁) hh.le
  · rw [sub_mul, hvMul]
    ring

private theorem exists_sortedTangentialAxes (j : Fin 3) :
    ∃ a : TensorGridFaceAxes, a.val.1 < a.val.2 ∧ j ≠ a.val.1 ∧ j ≠ a.val.2 := by
  fin_cases j
  · exact ⟨⟨(1, 2), by decide⟩, by decide⟩
  · exact ⟨⟨(0, 2), by decide⟩, by decide⟩
  · exact ⟨⟨(0, 1), by decide⟩, by decide⟩

/-- The literal integer square labels cover the boundary of the physical cube. -/
theorem exists_tensorGridSquare_of_frontier (c : Point) {m : ℕ} (hm : 0 < m) {h : ℝ} (hh : 0 < h)
    {x : Point} (hx : x ∈ frontier (shiftedCoordinateCube c ((m : ℝ) * h))) :
    ∃ f ∈ cubeBoundarySquares m, ∃ p ∈ Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) h,
      tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 p.1 p.2 = x := by
  let C := shiftedCoordinateCube c ((m : ℝ) * h)
  have hC : IsClosed C := isClosed_iInter (fun i => isClosed_Icc.preimage (EuclideanSpace.proj i).continuous)
  have hxC : x ∈ C := hC.closure_eq ▸ frontier_subset_closure hx
  have hX (i : Fin 3) : x i ∈ Icc (c i - (m : ℝ) * h) (c i + (m : ℝ) * h) := mem_iInter.mp hxC i
  have hSat : ∃ j : Fin 3, x j = c j - (m : ℝ) * h ∨ x j = c j + (m : ℝ) * h := by
    by_contra hEnd
    push Not at hEnd
    let U : Set Point := ⋂ i : Fin 3, (EuclideanSpace.proj i) ⁻¹' Ioo (c i - (m : ℝ) * h) (c i + (m : ℝ) * h)
    have hOpen : IsOpen U := isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)
    have hSub : U ⊆ C := iInter_mono (fun _ => preimage_mono Ioo_subset_Icc_self)
    have hMem : x ∈ U := mem_iInter.mpr (fun i => ⟨lt_of_le_of_ne (hX i).1 (hEnd i).1.symm,
      lt_of_le_of_ne (hX i).2 (hEnd i).2⟩)
    exact hx.2 (interior_maximal hSub hOpen hMem)
  obtain ⟨j, hj⟩ := hSat
  obtain ⟨a, ha, hj₁, hj₂⟩ := exists_sortedTangentialAxes j
  obtain ⟨b₁, hb₁l, hb₁u, s, hs, hXs⟩ := exists_integerMeshInterval hm hh (hX a.val.1)
  obtain ⟨b₂, hb₂l, hb₂u, t, ht, hXt⟩ := exists_integerMeshInterval hm hh (hX a.val.2)
  have hb₃ : ∃ b : ℤ, |b| = (m : ℤ) ∧ x j = c j + (b : ℝ) * h := by
    rcases hj with hl | hu
    · exact ⟨-(m : ℤ), by simp, by simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, sub_eq_add_neg] using hl⟩
    · exact ⟨(m : ℤ), by simp, by simpa only [Int.cast_natCast] using hu⟩
  obtain ⟨b₃, hb₃, hXj⟩ := hb₃
  let b : Fin 3 → ℤ := fun i => if i = a.val.1 then b₁ else if i = a.val.2 then b₂ else b₃
  have hB₁ : b a.val.1 = b₁ := if_pos rfl
  have hB₂ : b a.val.2 = b₂ := by simp [b, Ne.symm a.property]
  have hBj : b j = b₃ := by simp [b, hj₁, hj₂]
  let f : TensorGridSquare := (b, a)
  have hf : f ∈ cubeBoundarySquares m := by
    apply mem_cubeBoundarySquares_iff.mpr
    refine ⟨?_, ha, by rwa [show f.1 f.2.val.1 = b₁ from hB₁], by rwa [show f.1 f.2.val.2 = b₂ from hB₂],
      j, hj₁, hj₂, by rwa [show f.1 j = b₃ from hBj]⟩
    intro i
    change -(m : ℤ) ≤ b i ∧ b i ≤ (m : ℤ)
    rcases finThree_axes a.property hj₁ hj₂ (l := i) with rfl | rfl | rfl
    · exact hB₁ ▸ ⟨hb₁l, hb₁u.le⟩
    · exact hB₂ ▸ ⟨hb₂l, hb₂u.le⟩
    · exact hBj ▸ abs_le.mp hb₃.le
  refine ⟨f, hf, (s, t), ⟨hs, ht⟩, ?_⟩
  apply PiLp.ext
  intro i
  rw [tensorGridSquarePoint_apply]
  change c i + (b i : ℝ) * h + (if i = a.val.1 then s else 0) + (if i = a.val.2 then t else 0) = x i
  rcases finThree_axes a.property hj₁ hj₂ (l := i) with rfl | rfl | rfl
  · simpa [hB₁, a.property] using hXs.symm
  · simpa [hB₂, Ne.symm a.property] using hXt.symm
  · simpa only [hBj, if_neg hj₁, if_neg hj₂, add_zero] using hXj.symm

/-- The selected projected squares sweep out exactly the closed shell between
the two spherical radii. -/
theorem iUnion_sphericalClosedCell_eq_closedShell {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4)) :
    (⋃ f ∈ cubeBoundarySquares m, sphericalClosedCell c h f) = {z | ‖z‖ ∈ Icc (1 - h) 1} := by
  have ha : (0 : ℝ) < 1 - h := by linarith only [hh']
  ext z
  rw [mem_iUnion₂, mem_setOf_eq]
  constructor
  · rintro ⟨f, hf, p, hp, rfl⟩
    have hSphere := (sphericalFacePoint_dist_bounds hh hc hm hf hp.1 hp.1).1
    have hNorm : ‖sphericalFacePoint c h f p.1‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hSphere
    have hp₀ : 0 ≤ p.2 := ha.le.trans hp.2.1
    simpa only [sphericalCellPoint, norm_smul, Real.norm_of_nonneg hp₀, hNorm, mul_one] using hp.2
  · intro hz
    have hz₀ : z ≠ 0 := norm_pos_iff.mp (ha.trans_le hz.1)
    let u : sphere (0 : Point) 1 := ⟨NormedSpace.normalize z, by
      simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hz₀⟩
    obtain ⟨_, _, _, e, he, _⟩ := shiftedCoordinateCube_geometry hc hm
    let x := e u
    have hx : NormedSpace.normalize x.val = NormedSpace.normalize z :=
      (he x).symm.trans (congrArg Subtype.val (e.symm_apply_apply u))
    have hm₀ : 0 < m := by
      by_contra h
      have : m = 0 := by omega
      simp only [this, Nat.cast_zero, zero_mul] at hm
      exact (by norm_num : ¬ (1 / 8 : ℝ) ≤ 0) hm.1
    obtain ⟨f, hf, p, hp, hRaw⟩ := exists_tensorGridSquare_of_frontier c hm₀ hh x.property
    refine ⟨f, hf, (p, ‖z‖), ⟨hp, hz⟩, ?_⟩
    change ‖z‖ • NormedSpace.normalize (tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 p.1 p.2) = z
    rw [hRaw, hx, NormedSpace.norm_smul_normalize]

private theorem openGridSquare_index (c : Point) {h : ℝ} (hh : 0 < h) (f : TensorGridSquare) {p : ℝ × ℝ}
    (hp : p ∈ Ioo (0 : ℝ) h ×ˢ Ioo (0 : ℝ) h) (i : Fin 3) :
    let x := tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 p.1 p.2
    let v := (x i - c i) / h
    ⌊v⌋ = f.1 i ∧ (v ≠ (f.1 i : ℝ) ↔ i = f.2.val.1 ∨ i = f.2.val.2) := by
  intro x v
  let u := (if i = f.2.val.1 then p.1 else 0) + (if i = f.2.val.2 then p.2 else 0)
  have hV : v = (f.1 i : ℝ) + u / h := by
    dsimp only [v, x]
    rw [tensorGridSquarePoint_apply]
    change (c i + (f.1 i : ℝ) * h + (if i = f.2.val.1 then p.1 else 0) +
      (if i = f.2.val.2 then p.2 else 0) - c i) / h = _
    dsimp only [u]
    field_simp
    ring
  have hStep : 0 ≤ u ∧ u < h ∧ (u ≠ 0 ↔ i = f.2.val.1 ∨ i = f.2.val.2) := by
    by_cases h₁ : i = f.2.val.1
    · simpa [u, h₁, f.2.property] using
        And.intro hp.1.1.le (And.intro hp.1.2 hp.1.1.ne')
    · by_cases h₂ : i = f.2.val.2
      · simpa [u, h₂, Ne.symm f.2.property] using
          And.intro hp.2.1.le (And.intro hp.2.2 hp.2.1.ne')
      · simp [u, h₁, h₂, hh]
  refine ⟨Int.floor_eq_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [hV]
    exact le_add_of_nonneg_right (div_nonneg hStep.1 hh.le)
  · rw [hV]
    have hLt : u / h < 1 := (div_lt_iff₀ hh).mpr (by simpa only [one_mul] using hStep.2.1)
    linarith only [hLt]
  · have hZero : (f.1 i : ℝ) + u / h = (f.1 i : ℝ) ↔ u = 0 := by
      constructor
      · intro hz
        exact (div_eq_zero_iff.mp (by linarith only [hz])).resolve_right hh.ne'
      · intro hz
        simp [hz]
    simpa only [hV, ne_eq, hZero] using hStep.2.2

private theorem gridSquare_eq_of_openPoint {c : Point} {h : ℝ} (hh : 0 < h) {m : ℕ} {f g : TensorGridSquare}
    (hf : f ∈ cubeBoundarySquares m) (hg : g ∈ cubeBoundarySquares m) {p q : ℝ × ℝ}
    (hp : p ∈ Ioo (0 : ℝ) h ×ˢ Ioo (0 : ℝ) h) (hq : q ∈ Ioo (0 : ℝ) h ×ˢ Ioo (0 : ℝ) h)
    (he : tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 p.1 p.2 =
      tensorGridSquarePoint (tensorGridVertex c h g.1) g.2 q.1 q.2) : f = g := by
  have hIndices (i : Fin 3) : f.1 i = g.1 i ∧
      (i = f.2.val.1 ∨ i = f.2.val.2 ↔ i = g.2.val.1 ∨ i = g.2.val.2) := by
    obtain ⟨hfFloor, hfTang⟩ := openGridSquare_index c hh f hp i
    obtain ⟨hgFloor, hgTang⟩ := openGridSquare_index c hh g hq i
    rw [he] at hfFloor hfTang
    have hIdx := hfFloor.symm.trans hgFloor
    exact ⟨hIdx, hfTang.symm.trans (by rwa [hIdx])⟩
  refine Prod.ext (funext fun i => (hIndices i).1) (Subtype.ext ?_)
  have hOrderF := (mem_cubeBoundarySquares_iff.mp hf).2.1
  have hOrderG := (mem_cubeBoundarySquares_iff.mp hg).2.1
  have h₁ := (hIndices f.2.val.1).2.mp (Or.inl rfl)
  have h₂ := (hIndices f.2.val.2).2.mp (Or.inr rfl)
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact (f.2.property (h₁.trans h₂.symm)).elim
  · exact Prod.ext h₁ h₂
  · rw [h₁, h₂] at hOrderF
    exact (not_lt_of_gt hOrderG hOrderF).elim
  · exact (f.2.property (h₁.trans h₂.symm)).elim

/-- Distinct integer square labels give disjoint open three-dimensional cells. -/
theorem sphericalClosedCell_disjoint_interiors {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4)) {f g : TensorGridSquare}
    (hf : f ∈ cubeBoundarySquares m) (hg : g ∈ cubeBoundarySquares m) (hfg : f ≠ g) :
    Disjoint (interior (sphericalClosedCell c h f)) (interior (sphericalClosedCell c h g)) := by
  rw [sphericalClosedCell_interior hh' hc hm hf, sphericalClosedCell_interior hh' hc hm hg]
  refine Set.disjoint_left.mpr ?_
  rintro z ⟨p, hp, hP⟩ ⟨q, hq, hQ⟩
  have hpc : p.1 ∈ Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) h := ⟨Ioo_subset_Icc_self hp.1.1, Ioo_subset_Icc_self hp.1.2⟩
  have hqc : q.1 ∈ Icc (0 : ℝ) h ×ˢ Icc (0 : ℝ) h := ⟨Ioo_subset_Icc_self hq.1.1, Ioo_subset_Icc_self hq.1.2⟩
  have hp₀ : 0 < p.2 := by linarith only [hp.2.1, hh']
  have hq₀ : 0 < q.2 := by linarith only [hq.2.1, hh']
  have hfN : ‖sphericalFacePoint c h f p.1‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using (sphericalFacePoint_dist_bounds hh hc hm hf hpc hpc).1
  have hgN : ‖sphericalFacePoint c h g q.1‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using (sphericalFacePoint_dist_bounds hh hc hm hg hqc hqc).1
  have hAngular := congrArg NormedSpace.normalize (hP.trans hQ.symm)
  simp only [sphericalCellPoint, NormedSpace.normalize_smul_of_pos hp₀, NormedSpace.normalize_smul_of_pos hq₀,
    NormedSpace.normalize_eq_self_of_norm_eq_one hfN, NormedSpace.normalize_eq_self_of_norm_eq_one hgN] at hAngular
  obtain ⟨_, _, _, e, he, _⟩ := shiftedCoordinateCube_geometry hc hm
  let x : frontier (shiftedCoordinateCube c ((m : ℝ) * h)) :=
    ⟨_, tensorGridSquarePoint_mem_frontier hh hf hpc.1 hpc.2⟩
  let y : frontier (shiftedCoordinateCube c ((m : ℝ) * h)) :=
    ⟨_, tensorGridSquarePoint_mem_frontier hh hg hqc.1 hqc.2⟩
  have hRaw : x = y := e.symm.injective (Subtype.ext (by rw [he, he]; exact hAngular))
  exact hfg (gridSquare_eq_of_openPoint hh hf hg hp.1 hq.1 (congrArg Subtype.val hRaw))

end Thesis
