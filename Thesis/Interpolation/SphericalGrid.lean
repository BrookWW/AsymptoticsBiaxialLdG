module

public import Thesis.Interpolation.PenalizedShell
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Normed.Module.Normalize
public import StratificationTheory.Foundation.SphereOriginalFaceGrid
import StratificationTheory.Foundation.CoordinateClosedTargetCubeGeometry
import StratificationTheory.Foundation.CoordinateACLIntegralIncrements
import StratificationTheory.Foundation.CoordinateNormalLineGeometry
import StratificationTheory.Foundation.OriginalCoordinateLineChannels

/-! Radial coordinates for the translated cubical mesh of the unit sphere. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Module Set
open scoped BigOperators ENNReal NNReal Topology

namespace Thesis

private theorem norm_smul_sub_le_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (a b : ℝ) :
    ‖a • x - b • y‖ ≤ |a| * ‖x - y‖ + |a - b| * ‖y‖ := by
  have h : a • x - b • y = a • (x - y) + (a - b) • y := by
    rw [smul_sub, sub_smul]
    abel
  rw [h]
  exact (norm_add_le _ _).trans_eq (by simp only [norm_smul, Real.norm_eq_abs])

private theorem abs_inv_sub_eq_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a⁻¹ - b⁻¹| = a⁻¹ * b⁻¹ * |a - b| := by
  rw [inv_sub_inv ha.ne' hb.ne', abs_div, abs_of_pos (mul_pos ha hb), abs_sub_comm]
  field_simp

private theorem normalize_dist_le_of_le_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {r : ℝ} (hr : 0 < r) {x y : E} (hx : r ≤ ‖x‖) (hy : r ≤ ‖y‖) :
    dist (NormedSpace.normalize x) (NormedSpace.normalize y) ≤ 2 * r⁻¹ * dist x y := by
  have hx₀ := hr.trans_le hx
  have hy₀ := hr.trans_le hy
  have h := norm_smul_sub_le_split x y ‖x‖⁻¹ ‖y‖⁻¹
  rw [abs_of_pos (inv_pos.mpr hx₀), abs_inv_sub_eq_of_pos hx₀ hy₀] at h
  have hcancel : ‖x‖⁻¹ * ‖y‖⁻¹ * |‖x‖ - ‖y‖| * ‖y‖ = ‖x‖⁻¹ * |‖x‖ - ‖y‖| := by
    field_simp
  rw [hcancel] at h
  simp only [NormedSpace.normalize, dist_eq_norm]
  calc
    _ ≤ ‖x‖⁻¹ * ‖x - y‖ + ‖x‖⁻¹ * |‖x‖ - ‖y‖| := h
    _ ≤ ‖x‖⁻¹ * ‖x - y‖ + ‖x‖⁻¹ * ‖x - y‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (inv_nonneg.mpr hx₀.le))
    _ = 2 * ‖x‖⁻¹ * ‖x - y‖ := by ring
    _ ≤ _ := by gcongr

/-- The radial chart of a convex body between concentric balls, with explicit
constants independent of the particular body. -/
theorem exists_radial_bilipschitz_homeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {C : Set E} {r R : ℝ≥0} (hr : 0 < r) (hR : 0 < R)
    (hC : Convex ℝ C) (hInner : ball (0 : E) r ⊆ C)
    (hOuter : C ⊆ closedBall (0 : E) R) :
    ∃ e : sphere (0 : E) 1 ≃ₜ frontier C,
      (∀ θ, (e θ).val = (gauge C θ.val)⁻¹ • θ.val) ∧
      (∀ x, (e.symm x).val = NormedSpace.normalize x.val) ∧
      LipschitzWith (R + R ^ 2 * r⁻¹) e ∧ LipschitzWith (2 * r⁻¹) e.symm := by
  have hr₀ : 0 < (r : ℝ) := hr
  have hR₀ : 0 < (R : ℝ) := hR
  have hCn : C ∈ 𝓝 (0 : E) := mem_of_superset (ball_mem_nhds _ hr₀) hInner
  have hCore : ball (0 : E) r ⊆ interior C := interior_maximal hInner isOpen_ball
  have hθnorm (θ : sphere (0 : E) 1) : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
  have hg (θ : sphere (0 : E) 1) : (R : ℝ)⁻¹ ≤ gauge C θ.val := by
    simpa only [hθnorm θ, one_div] using
      le_gauge_of_subset_closedBall (absorbent_nhds_zero hCn) hR₀.le hOuter (x := θ.val)
  have hgpos (θ : sphere (0 : E) 1) : 0 < gauge C θ.val := (inv_pos.mpr hR₀).trans_le (hg θ)
  have hrad (θ : sphere (0 : E) 1) : (gauge C θ.val)⁻¹ • θ.val ∈ frontier C := by
    apply (gauge_eq_one_iff_mem_frontier hC hCn).mp
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr (hgpos θ).le), smul_eq_mul,
      inv_mul_cancel₀ (hgpos θ).ne']
  have hxnorm (x : frontier C) : (r : ℝ) ≤ ‖x.val‖ := by
    by_contra! hx
    exact x.property.2 (hCore (mem_ball_zero_iff.mpr hx))
  have hxpos (x : frontier C) : 0 < ‖x.val‖ := hr₀.trans_le (hxnorm x)
  let f (θ : sphere (0 : E) 1) : frontier C := ⟨_, hrad θ⟩
  let g (x : frontier C) : sphere (0 : E) 1 :=
    ⟨NormedSpace.normalize x.val, mem_sphere_zero_iff_norm.mpr
      (NormedSpace.norm_normalize (norm_pos_iff.mp (hxpos x)))⟩
  have hfg (x : frontier C) : f (g x) = x := by
    have hxGauge := (gauge_eq_one_iff_mem_frontier hC hCn).mpr x.property
    apply Subtype.ext
    change (gauge C (NormedSpace.normalize x.val))⁻¹ • NormedSpace.normalize x.val = x.val
    simp only [NormedSpace.normalize, gauge_smul_of_nonneg (inv_nonneg.mpr (hxpos x).le),
      hxGauge, smul_eq_mul, mul_one, inv_inv, smul_smul, mul_inv_cancel₀ (hxpos x).ne', one_smul]
  have hgf (θ : sphere (0 : E) 1) : g (f θ) = θ := by
    apply Subtype.ext
    change NormedSpace.normalize ((gauge C θ.val)⁻¹ • θ.val) = θ.val
    rw [NormedSpace.normalize_smul_of_pos (inv_pos.mpr (hgpos θ)),
      NormedSpace.normalize_eq_self_of_norm_eq_one (hθnorm θ)]
  have hf : LipschitzWith (R + R ^ 2 * r⁻¹) f := by
    apply LipschitzWith.of_dist_le_mul
    intro θ η
    have hG := (hC.lipschitzWith_gauge hr hInner).dist_le_mul θ.val η.val
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_inv] at hG
    have hInvBound (u : sphere (0 : E) 1) : (gauge C u.val)⁻¹ ≤ R := by
      simpa only [inv_inv] using (inv_le_inv₀ (hgpos u) (inv_pos.mpr hR₀)).2 (show
        (R : ℝ)⁻¹ ≤ gauge C u.val from hg u)
    change dist ((gauge C θ.val)⁻¹ • θ.val) ((gauge C η.val)⁻¹ • η.val) ≤
      ((R + R ^ 2 * r⁻¹ : ℝ≥0) : ℝ) * dist θ.val η.val
    simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv]
    have hh := norm_smul_sub_le_split θ.val η.val (gauge C θ.val)⁻¹ (gauge C η.val)⁻¹
    rw [abs_of_pos (inv_pos.mpr (hgpos θ)), abs_inv_sub_eq_of_pos (hgpos θ) (hgpos η), hθnorm η,
      mul_one] at hh
    calc
      _ ≤ (gauge C θ.val)⁻¹ * ‖θ.val - η.val‖ +
          (gauge C θ.val)⁻¹ * (gauge C η.val)⁻¹ * |gauge C θ.val - gauge C η.val| := hh
      _ ≤ (R : ℝ) * ‖θ.val - η.val‖ + (R : ℝ) * R * ((r : ℝ)⁻¹ * ‖θ.val - η.val‖) := by
        refine add_le_add (mul_le_mul_of_nonneg_right (hInvBound θ) (norm_nonneg _)) ?_
        refine mul_le_mul ?_ hG (abs_nonneg _) (mul_nonneg hR₀.le hR₀.le)
        exact mul_le_mul (hInvBound θ) (hInvBound η) (inv_nonneg.mpr (hgpos η).le) hR₀.le
      _ = _ := by ring
  have hgLip : LipschitzWith (2 * r⁻¹) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (NormedSpace.normalize x.val) (NormedSpace.normalize y.val) ≤
      ((2 * r⁻¹ : ℝ≥0) : ℝ) * dist x.val y.val
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_inv] using
      normalize_dist_le_of_le_norm hr₀ (hxnorm x) (hxnorm y)
  let e : sphere (0 : E) 1 ≃ₜ frontier C :=
    ⟨⟨f, g, hgf, hfg⟩, hf.continuous, hgLip.continuous⟩
  exact ⟨e, fun _ => rfl, fun _ => rfl, hf, hgLip⟩

/-- The closed coordinate cube of radius `s` about a lattice offset `c`. -/
@[expose] def shiftedCoordinateCube (c : Point) (s : ℝ) : Set Point :=
  ⋂ i : Fin 3, (EuclideanSpace.proj i) ⁻¹' Icc (c i - s) (c i + s)

private theorem mem_shiftedCoordinateCube_iff {c x : Point} {s : ℝ} :
    x ∈ shiftedCoordinateCube c s ↔ ∀ i : Fin 3, c i - s ≤ x i ∧ x i ≤ c i + s :=
  mem_iInter

/-- Shifted lattice boxes at the selected radii have a common radial chart
bound. Their points also lie in the open unit coordinate box used for ACL. -/
theorem shiftedCoordinateCube_geometry {c : Point} {s : ℝ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hs : s ∈ Icc (1 / 8 : ℝ) (1 / 4)) :
    IsClosed (shiftedCoordinateCube c s) ∧ Convex ℝ (shiftedCoordinateCube c s) ∧
    (∀ x ∈ shiftedCoordinateCube c s, ∀ i : Fin 3, x i ∈ Ioo (-1 : ℝ) 1) ∧
    ∃ e : sphere (0 : Point) 1 ≃ₜ frontier (shiftedCoordinateCube c s),
      (∀ x, (e.symm x).val = NormedSpace.normalize x.val) ∧
      LipschitzWith 17 e ∧ LipschitzWith 32 e.symm := by
  have hClosed : IsClosed (shiftedCoordinateCube c s) :=
    isClosed_iInter (fun i => isClosed_Icc.preimage (EuclideanSpace.proj i).continuous)
  have hConvex : Convex ℝ (shiftedCoordinateCube c s) :=
    convex_iInter (fun i => convex_Icc _ _ |>.linear_preimage (EuclideanSpace.proj i).toLinearMap)
  have hInner : ball (0 : Point) (1 / 16) ⊆ shiftedCoordinateCube c s := by
    intro x hx
    rw [mem_ball_zero_iff] at hx
    apply mem_shiftedCoordinateCube_iff.mpr
    intro i
    have hi := (PiLp.norm_apply_le x i).trans_lt hx
    rw [Real.norm_eq_abs] at hi
    have hi' := abs_lt.mp hi
    exact ⟨by linarith only [hi'.1, (hc i).2, hs.1], by linarith only [hi'.2, (hc i).1, hs.1]⟩
  have hCoord (x : Point) (hx : x ∈ shiftedCoordinateCube c s) (i : Fin 3) :
      |x i| ≤ 9 / 32 := by
    obtain ⟨hlo, hhi⟩ := mem_shiftedCoordinateCube_iff.mp hx i
    apply abs_le.mpr
    exact ⟨by linarith only [hlo, (hc i).1, hs.2], by linarith only [hhi, (hc i).2, hs.2]⟩
  have hOuter : shiftedCoordinateCube c s ⊆ closedBall (0 : Point) 1 := by
    intro x hx
    have hxSup : ‖WithLp.ofLp x‖ ≤ 9 / 32 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 32)).mpr
      intro i
      simpa only [Real.norm_eq_abs] using hCoord x hx i
    rw [mem_closedBall_zero_iff]
    calc
      ‖x‖ ≤ ((3 : ℕ) : ℝ) * ‖WithLp.ofLp x‖ :=
        (StratificationTheory.cube_coordinate_norm_comparison x).2
      _ ≤ (3 : ℝ) * (9 / 32) := by
        simpa only [Nat.cast_ofNat] using mul_le_mul_of_nonneg_left hxSup (Nat.cast_nonneg 3)
      _ ≤ 1 := by norm_num
  refine ⟨hClosed, hConvex, ?_, ?_⟩
  · intro x hx i
    exact abs_lt.mp ((hCoord x hx i).trans_lt (by norm_num))
  · obtain ⟨e, _, hi, he, hiLip⟩ := exists_radial_bilipschitz_homeomorph
      (r := 1 / 16) (R := 1) (by norm_num) (by norm_num) hConvex
      (by simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hInner)
      (by simpa only [NNReal.coe_one] using hOuter)
    norm_num at he hiLip
    exact ⟨e, hi, he, hiLip⟩

/-- A positive unit grid edge is recorded by its integer origin and
coordinate direction. -/
abbrev TensorGridEdge := (Fin 3 → ℤ) × Fin 3

/-- Positive grid edges in the boundary of the integer cube `[-m,m]³`.
All coordinates of the starting vertex belong to the cube, the direction
coordinate is strictly below the upper bound, and some other coordinate is
fixed at one of the two boundary levels. -/
@[expose] noncomputable def cubeBoundaryEdges (m : ℕ) : Finset TensorGridEdge := by
  classical
  exact (Finset.Icc (fun _ : Fin 3 => -(m : ℤ)) (fun _ => (m : ℤ)) ×ˢ Finset.univ).filter
    (fun e => e.1 e.2 < (m : ℤ) ∧ ∃ i : Fin 3, i ≠ e.2 ∧ |e.1 i| = (m : ℤ))

/-- The membership conditions use the same integer origin for every
appearance of a geometric edge. -/
theorem mem_cubeBoundaryEdges_iff {m : ℕ} {e : TensorGridEdge} :
    e ∈ cubeBoundaryEdges m ↔
      (∀ i : Fin 3, -(m : ℤ) ≤ e.1 i ∧ e.1 i ≤ (m : ℤ)) ∧ e.1 e.2 < (m : ℤ) ∧
      ∃ i : Fin 3, i ≠ e.2 ∧ |e.1 i| = (m : ℤ) := by
  classical
  rcases e with ⟨z, k⟩
  simp only [cubeBoundaryEdges, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
    Finset.mem_Icc, Pi.le_def, ← forall_and]

/-- Different nested cubes have disjoint boundary edge indices. -/
theorem disjoint_cubeBoundaryEdges {m n : ℕ} (h : m ≠ n) :
    Disjoint (cubeBoundaryEdges m) (cubeBoundaryEdges n) := by
  apply Finset.disjoint_left.mpr
  intro e hm hn
  obtain ⟨hmb, _, i, _, hi⟩ := mem_cubeBoundaryEdges_iff.mp hm
  obtain ⟨hnb, _, j, _, hj⟩ := mem_cubeBoundaryEdges_iff.mp hn
  have hij : (m : ℤ) ≤ n := hi ▸ abs_le.mpr (hnb i)
  have hji : (n : ℤ) ≤ m := hj ▸ abs_le.mpr (hmb j)
  exact h (by exact_mod_cast le_antisymm hij hji)

private theorem normalized_channel_sum_le_one {ι : Type*} [Fintype ι] (f : ι → ℝ≥0∞)
    {B : ℝ≥0∞} (hB : B ≠ ⊤) (hf : ∑ i, f i ≤ B) : ∑ i, f i / B ≤ 1 := by
  simp_rw [ENNReal.div_eq_inv_mul, ← Finset.mul_sum]
  by_cases h : B = 0
  · have hZero : ∑ i, f i = 0 := le_antisymm (hf.trans_eq h) zero_le
    rw [hZero, mul_zero]
    exact zero_le
  · calc
      _ ≤ B⁻¹ * B := mul_le_mul' le_rfl hf
      _ = _ := ENNReal.inv_mul_cancel h hB

/-- One level between radii `1/8` and `1/4` controls both finite channels
on any pairwise disjoint family indexed by the integer cube level. -/
theorem exists_meshBoundary_linear_gain {ι : Type*} [DecidableEq ι] {h : ℝ}
    (hh : 0 < h) (hhsmall : h ≤ 1 / 32) (boundary : ℕ → Finset ι)
    (hDisjoint : Pairwise (fun m n => Disjoint (boundary m) (boundary n)))
    (A D : ι → ℝ≥0∞) (hA : (∑' e, A e) ≠ ⊤) (hD : (∑' e, D e) ≠ ⊤) :
    ∃ m : ℕ, (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4) ∧
      (∑ e ∈ boundary m, A e) ≤ ENNReal.ofReal ((64 / 3) * h) * ∑' e, A e ∧
      (∑ e ∈ boundary m, D e) ≤ ENNReal.ofReal ((64 / 3) * h) * ∑' e, D e := by
  classical
  let M := ⌊(1 : ℝ) / (8 * h)⌋₊
  have hDen : 0 < 8 * h := mul_pos (by norm_num) hh
  have hMtop : (M : ℝ) * (8 * h) ≤ 1 :=
    (le_div_iff₀ hDen).mp (Nat.floor_le (div_nonneg zero_le_one hDen.le))
  have hMbot : 1 < ((M : ℝ) + 1) * (8 * h) :=
    (div_lt_iff₀ hDen).mp (Nat.lt_floor_add_one _)
  have hM : (1 : ℝ) ≤ (M : ℝ) * ((32 / 3) * h) := by nlinarith only [hMbot, hhsmall]
  have hMpos : 0 < M := by
    by_contra! hzero
    have hz : M = 0 := Nat.eq_zero_of_le_zero hzero
    norm_num [hz] at hM
  letI : Nonempty (Fin M) := ⟨⟨0, hMpos⟩⟩
  let level (i : Fin M) := M + 1 + i.val
  have hLevel (i : Fin M) : (level i : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4) := by
    have hlo : ((M : ℝ) + 1) ≤ level i := by
      exact_mod_cast (show M + 1 ≤ level i by exact Nat.le_add_right _ _)
    have hhi : (level i : ℝ) ≤ 2 * (M : ℝ) := by
      exact_mod_cast (show level i ≤ 2 * M by have := i.isLt; dsimp only [level]; omega)
    have hLower := mul_le_mul_of_nonneg_right hlo hh.le
    have hUpper := mul_le_mul_of_nonneg_right hhi hh.le
    exact ⟨by linarith only [hLower, hMbot], by linarith only [hUpper, hMtop]⟩
  have hDisj : (↑(Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint
      (fun i => boundary (level i)) := by
    intro i _ j _ hne
    apply hDisjoint
    intro heq
    apply hne
    apply Fin.ext
    dsimp only [level] at heq
    omega
  let a (i : Fin M) : ℝ≥0∞ := ∑ e ∈ boundary (level i), A e
  let d (i : Fin M) : ℝ≥0∞ := ∑ e ∈ boundary (level i), D e
  have ha₀ : ∑ i, a i ≤ ∑' e, A e := by
    change (∑ i : Fin M, ∑ e ∈ boundary (level i), A e) ≤ ∑' e, A e
    rw [← Finset.sum_biUnion hDisj]
    exact ENNReal.sum_le_tsum _
  have hd₀ : ∑ i, d i ≤ ∑' e, D e := by
    change (∑ i : Fin M, ∑ e ∈ boundary (level i), D e) ≤ ∑' e, D e
    rw [← Finset.sum_biUnion hDisj]
    exact ENNReal.sum_le_tsum _
  let score (i : Fin M) := a i / (∑' e, A e) + d i / (∑' e, D e)
  have hScore : (∑ i, score i) ≤ 2 := by
    simp only [score, Finset.sum_add_distrib]
    exact (add_le_add (normalized_channel_sum_le_one a hA ha₀)
      (normalized_channel_sum_le_one d hD hd₀)).trans_eq (by norm_num)
  obtain ⟨i, _, hMin⟩ := Finset.exists_min_image Finset.univ score Finset.univ_nonempty
  have hMean : (M : ℝ≥0∞) * score i ≤ 2 := by
    have hmono := (Finset.sum_le_sum (s := Finset.univ) (fun j hj => hMin j hj)).trans hScore
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hmono
  have hMcast : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos
  have hCoeff : (2 : ℝ≥0∞) / M ≤ ENNReal.ofReal ((64 / 3) * h) := by
    have hGain : 2 / (M : ℝ) ≤ (64 / 3) * h := (div_le_iff₀ hMcast).mpr (by nlinarith only [hM])
    simpa only [ENNReal.ofReal_div_of_pos hMcast, ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal hGain
  have hScorei : score i ≤ (2 : ℝ≥0∞) / M :=
    (ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr hMpos.ne'))
      (Or.inl (ENNReal.natCast_ne_top M))).mpr
      (by simpa only [mul_comm] using hMean)
  have hRecover {b B : ℝ≥0∞} (hB : B ≠ ⊤) (hb : b / B ≤ score i) :
      b ≤ ENNReal.ofReal ((64 / 3) * h) * B :=
    (ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl hB)).mp
      ((hb.trans hScorei).trans hCoeff)
  exact ⟨level i, hLevel i, hRecover hA le_self_add, hRecover hD le_add_self⟩

/-- One original nested lattice cube controls both finite edge channels with a
linear gain in the mesh size. The two channels may vanish independently. -/
theorem exists_cubeBoundaryEdges_linear_gain {h : ℝ} (hh : 0 < h) (hhsmall : h ≤ 1 / 32)
    (A D : TensorGridEdge → ℝ≥0∞) (hA : (∑' e, A e) ≠ ⊤) (hD : (∑' e, D e) ≠ ⊤) :
    ∃ m : ℕ, (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4) ∧
      (∑ e ∈ cubeBoundaryEdges m, A e) ≤ ENNReal.ofReal (32 * h) * ∑' e, A e ∧
      (∑ e ∈ cubeBoundaryEdges m, D e) ≤ ENNReal.ofReal (32 * h) * ∑' e, D e := by
  obtain ⟨m, hm, hA', hD'⟩ := exists_meshBoundary_linear_gain hh hhsmall cubeBoundaryEdges
    (fun _ _ hne => disjoint_cubeBoundaryEdges hne) A D hA hD
  have hGain : ENNReal.ofReal ((64 / 3) * h) ≤ ENNReal.ofReal (32 * h) :=
    ENNReal.ofReal_le_ofReal (by linarith only [hh])
  exact ⟨m, hm, hA'.trans (mul_le_mul_left hGain _), hD'.trans (mul_le_mul_left hGain _)⟩

/-- Physical points on a positive grid edge in the translated mesh. -/
@[expose] noncomputable def tensorGridEdgePoint (c : Point) (h : ℝ) (e : TensorGridEdge) (t : ℝ) :
    Point := WithLp.toLp 2 (fun j : Fin 3 => c j + (e.1 j : ℝ) * h) +
      t • EuclideanSpace.single e.2 (1 : ℝ)

theorem tensorGridEdgePoint_apply (c : Point) (h : ℝ) (e : TensorGridEdge)
    (t : ℝ) (i : Fin 3) :
    tensorGridEdgePoint c h e t i = c i + (e.1 i : ℝ) * h + if i = e.2 then t else 0 := by
  by_cases hi : i = e.2
  · subst i
    simp [tensorGridEdgePoint, PiLp.add_apply, PiLp.smul_apply]
  · simp [tensorGridEdgePoint, PiLp.add_apply, PiLp.smul_apply, hi]

/-- A selected edge belongs to the boundary of the actual physical cube. -/
theorem tensorGridEdgePoint_mem_frontier {c : Point} {h : ℝ} (hh : 0 < h)
    {m : ℕ} {e : TensorGridEdge} (he : e ∈ cubeBoundaryEdges m)
    {t : ℝ} (ht : t ∈ Icc 0 h) :
    tensorGridEdgePoint c h e t ∈ frontier (shiftedCoordinateCube c ((m : ℝ) * h)) := by
  obtain ⟨hb, hd, j, hj, hsat⟩ := mem_cubeBoundaryEdges_iff.mp he
  have hxMem : tensorGridEdgePoint c h e t ∈ shiftedCoordinateCube c ((m : ℝ) * h) := by
    apply mem_shiftedCoordinateCube_iff.mpr
    intro i
    obtain ⟨hlo, hhi⟩ := hb i
    have hLower : -(m : ℝ) ≤ (e.1 i : ℝ) := by exact_mod_cast hlo
    have hUpper : (e.1 i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hhi
    have hlo' := mul_le_mul_of_nonneg_right hLower hh.le
    have hhi' := mul_le_mul_of_nonneg_right hUpper hh.le
    rw [tensorGridEdgePoint_apply]
    by_cases hi : i = e.2
    · have hd' : (e.1 i : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast (show e.1 i + 1 ≤ (m : ℤ) by subst i; omega)
      have hd'' := mul_le_mul_of_nonneg_right hd' hh.le
      rw [if_pos hi]
      exact ⟨by linarith only [ht.1, hlo'], by linarith only [ht.2, hd'']⟩
    · rw [if_neg hi, add_zero]
      exact ⟨by linarith only [hlo'], by linarith only [hhi']⟩
  refine ⟨subset_closure hxMem, ?_⟩
  intro hInterior
  have hSub : shiftedCoordinateCube c ((m : ℝ) * h) ⊆
      (EuclideanSpace.proj j) ⁻¹' Icc (c j - (m : ℝ) * h) (c j + (m : ℝ) * h) :=
    iInter_subset _ j
  have hOpen : IsOpenMap (EuclideanSpace.proj j : Point → ℝ) :=
    PiLp.isOpenMap_apply 2 (fun _ : Fin 3 => ℝ) j
  have hJ := hOpen.interior_preimage_subset_preimage_interior (interior_mono hSub hInterior)
  rw [interior_Icc] at hJ
  change tensorGridEdgePoint c h e t j ∈ Ioo (c j - (m : ℝ) * h) (c j + (m : ℝ) * h) at hJ
  rw [tensorGridEdgePoint_apply, if_neg hj, add_zero] at hJ
  rcases eq_or_eq_neg_of_abs_eq hsat with hUpper | hLower
  · have hu : (e.1 j : ℝ) = m := by exact_mod_cast hUpper
    rw [hu] at hJ
    exact (lt_irrefl _) hJ.2
  · have hl : (e.1 j : ℝ) = -(m : ℝ) := by exact_mod_cast hLower
    rw [hl, neg_mul, ← sub_eq_add_neg] at hJ
    exact (lt_irrefl _) hJ.1

/-- The affine parameter of a physical grid edge is its arc-length
coordinate before radial projection. -/
theorem tensorGridEdgePoint_dist (c : Point) (h : ℝ) (e : TensorGridEdge) (s t : ℝ) :
    dist (tensorGridEdgePoint c h e s) (tensorGridEdgePoint c h e t) = dist s t := by
  unfold tensorGridEdgePoint
  rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, PiLp.norm_single, norm_one, mul_one,
    ← dist_eq_norm]

/-- The same radial projection gives a uniformly bi-Lipschitz arc-length
chart on every selected edge. -/
theorem normalized_grid_edge_dist {c : Point} {h : ℝ} (hh : 0 < h) {m : ℕ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {e : TensorGridEdge} (he : e ∈ cubeBoundaryEdges m) {s t : ℝ} (hs : s ∈ Icc 0 h) (ht : t ∈ Icc 0 h) :
    let x := NormedSpace.normalize (tensorGridEdgePoint c h e s)
    let y := NormedSpace.normalize (tensorGridEdgePoint c h e t)
    x ∈ sphere (0 : Point) 1 ∧ y ∈ sphere (0 : Point) 1 ∧
      dist x y ≤ 32 * dist s t ∧ dist s t ≤ 17 * dist x y := by
  obtain ⟨_, _, _, f, hf, hLip, hInvLip⟩ := shiftedCoordinateCube_geometry hc hm
  let x : frontier (shiftedCoordinateCube c ((m : ℝ) * h)) :=
    ⟨tensorGridEdgePoint c h e s, tensorGridEdgePoint_mem_frontier hh he hs⟩
  let y : frontier (shiftedCoordinateCube c ((m : ℝ) * h)) :=
    ⟨tensorGridEdgePoint c h e t, tensorGridEdgePoint_mem_frontier hh he ht⟩
  have hxy : dist x y = dist s t := tensorGridEdgePoint_dist c h e s t
  have hSphere (z : frontier (shiftedCoordinateCube c ((m : ℝ) * h))) :
      NormedSpace.normalize z.val ∈ sphere (0 : Point) 1 := hf z ▸ (f.symm z).property
  have hUpper := hInvLip.dist_le_mul x y
  have hLower := hLip.dist_le_mul (f.symm x) (f.symm y)
  simp only [Subtype.dist_eq, hf, NNReal.coe_ofNat] at hUpper hLower
  rw [f.apply_symm_apply, f.apply_symm_apply] at hLower
  change _ ∧ _ ∧ _ ≤ 32 * dist s t ∧ dist s t ≤ _
  rw [← hxy]
  exact ⟨hSphere x, hSphere y, hUpper, hLower⟩

theorem scaled_integer_lattice_embedding {h : ℝ} (hh : 0 < h) :
    let basis := (Pi.basisFun ℝ (Fin 3)).isUnitSMul (w := fun _ : Fin 3 => h)
      (fun _ => hh.ne'.isUnit)
    let L := Submodule.span ℤ (range basis)
    ∃ ν : (Fin 3 → ℤ) ↪ L, ∀ z i, (ν z : Fin 3 → ℝ) i = (z i : ℝ) * h := by
  intro basis L
  let step (i : Fin 3) : L := ⟨basis i, Submodule.subset_span ⟨i, rfl⟩⟩
  let ν (z : Fin 3 → ℤ) : L := ∑ i : Fin 3, z i • step i
  have hν (z : Fin 3 → ℤ) (i : Fin 3) : (ν z : Fin 3 → ℝ) i = (z i : ℝ) * h := by
    simp only [ν, step, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      basis, Basis.isUnitSMul_apply, Pi.basisFun_apply, zsmul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  have hInj : Function.Injective ν := by
    intro z z' hzz'
    funext i
    have hEq := congrArg (fun x : L => (x : Fin 3 → ℝ) i) hzz'
    rw [hν, hν] at hEq
    exact_mod_cast (mul_right_cancel₀ hh.ne' hEq)
  exact ⟨⟨ν, hInj⟩, hν⟩

private theorem sampled_edge_mass_scale {h : ℝ} (hh : 0 < h) :
    (ENNReal.ofReal (32 * h)) * (3 * (2 * (ENNReal.ofReal (h ^ 3))⁻¹ * (3 * ENNReal.ofReal h))) =
      ENNReal.ofReal (576 / h) := by
  have hh₃ := pow_pos hh 3
  rw [← ENNReal.ofReal_inv_of_pos hh₃]
  rw [← ENNReal.ofReal_ofNat (n := 3), ← ENNReal.ofReal_ofNat (n := 2)]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (h ^ 3)⁻¹),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 32 * h)]
  congr 1
  field_simp
  ring

private abbrev gridAxisPermutation (i : Fin 3) : Equiv.Perm (Fin 3) :=
  Equiv.swap (Fin.natAdd 2 (0 : Fin 1)) i

private noncomputable abbrev gridSplit := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)

private noncomputable abbrev gridAxisEquiv (i : Fin 3) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (gridAxisPermutation i)

private theorem gridSplit_in_unit_box (i : Fin 3) {x : Point}
    (hx : ∀ j : Fin 3, x j ∈ Ioo (-1 : ℝ) 1) :
    (gridSplit ((gridAxisEquiv i).symm x)).1 ∈
        ⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1 ∧
      (gridSplit ((gridAxisEquiv i).symm x)).2 0 ∈ Ioo (-1 : ℝ) 1 := by
  refine ⟨mem_iInter.mpr (fun j => ?_), ?_⟩
  · change (gridSplit ((gridAxisEquiv i).symm x)).1 j ∈ Ioo (-1 : ℝ) 1
    dsimp only [gridAxisEquiv]
    rw [LinearIsometryEquiv.piLpCongrLeft_symm]
    exact hx (gridAxisPermutation i (j.castAdd 1))
  · have heq := StratificationTheory.coordinate_split_last_eq (n := 2) (gridAxisPermutation i) x
    have hEq : (gridSplit ((gridAxisEquiv i).symm x)).2 0 = x i := by
      simpa only [gridAxisPermutation, Equiv.swap_apply_left] using heq
    exact hEq ▸ hx i

/-- A compact-range Sobolev sphere pair supplies actual edge Sobolev graphs
and two jointly controlled lower-integral channels on one physical cube.
The cube is selected from the native translated lattice before radial
projection. Both channels refer to the same radial extensions and edges. -/
theorem exists_sphere_pair_shifted_cube_edge_data {q : ℕ}
    (P : Fin 2 → UnitTensorSphere → Ambient q)
    (hP : ∀ l, StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) (P l))
    {N : Set (Ambient q)} (hN : IsCompact N)
    (hTarget : ∀ l, ∀ᵐ θ ∂tensorSphereMeasure, P l θ ∈ N)
    {h : ℝ} (hh : 0 < h) (hhsmall : h ≤ 1 / 32) :
    ∃ (w : Fin 2 → Point → Ambient q) (Dw : Fin 2 → Point → HarmonicMaps.Gradient 3 q),
      (∀ l, MemW12 (ballDomain 0 4) (w l) (Dw l)) ∧
      (∀ (l : Fin 2) (ρ : PositiveRadius) (θ : UnitTensorSphere), w l (ρ.val • θ.val) = P l θ) ∧
      ∃ (c : Point) (m : ℕ), (∀ j : Fin 3, c j ∈ Ico (0 : ℝ) h) ∧
        (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4) ∧
        (∀ e ∈ cubeBoundaryEdges m, ∀ l,
          MemW12 ⟨{t : Domain 1 | t 0 ∈ Ioo (0 : ℝ) h}, isOpen_Ioo.preimage (EuclideanSpace.proj 0).continuous⟩
            (fun t => w l (tensorGridEdgePoint c h e (t 0)))
            (fun t _ => Dw l (tensorGridEdgePoint c h e (t 0)) e.2)) ∧
        (∀ e ∈ cubeBoundaryEdges m, ∀ l, ∃ g : ℝ → Ambient q,
          ContinuousOn g (Icc 0 h) ∧
          g =ᵐ[volume.restrict (Ioo 0 h)] (fun t => w l (tensorGridEdgePoint c h e t)) ∧
          g 0 = w l (tensorGridEdgePoint c h e 0) ∧ g h = w l (tensorGridEdgePoint c h e h) ∧
          (∀ t ∈ Icc 0 h, g t ∈ N) ∧
          ∀ s ∈ Icc 0 h, ∀ t ∈ Icc 0 h,
            g t - g s = ∫ r in s..t, Dw l (tensorGridEdgePoint c h e r) e.2) ∧
        (∑ e ∈ cubeBoundaryEdges m, ∫⁻ t in Ioo (0 : ℝ) h,
          ENNReal.ofReal (hsNormSq (Dw 0 (tensorGridEdgePoint c h e t)) +
            hsNormSq (Dw 1 (tensorGridEdgePoint c h e t)))) ≤
          ENNReal.ofReal (2304 / h) * ENNReal.ofReal
            (nativeSphereGradientEnergy (P 0) (hP 0) + nativeSphereGradientEnergy (P 1) (hP 1)) ∧
        (∑ e ∈ cubeBoundaryEdges m, ∫⁻ t in Ioo (0 : ℝ) h,
          ENNReal.ofReal (‖w 0 (tensorGridEdgePoint c h e t) - w 1 (tensorGridEdgePoint c h e t)‖ ^ 2)) ≤
          ENNReal.ofReal (12288 / h) * ENNReal.ofReal
            (∫ θ : UnitTensorSphere, ‖P 0 θ - P 1 θ‖ ^ 2 ∂tensorSphereMeasure) := by
  classical
  let sampleFace (i : Fin 3) : Fin 1 ↪ Fin 3 := ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩
  obtain ⟨w, Dw, hW, _, hRad, _, _, _, offset, hOffset, hFace, hACL, _, _, hE, hD, _⟩ :=
    StratificationTheory.exists_sphere_pair_original_closed_target_face_grid
      (n := 2) (by decide : 2 ≤ 2) P hP hN hTarget (fun _ : Fin 3 => 0)
      gridAxisPermutation (fun _ => ⟨Fin.elim0, fun j => Fin.elim0 j⟩)
      (fun _ j => Fin.elim0 j) (fun _ : Fin 3 => 1) sampleFace hh
  let c : Point := WithLp.toLp 2 offset
  let R : ℝ := 4
  let B := ball (0 : Point) R
  let Eraw := B.indicator (fun x => ENNReal.ofReal (hsNormSq (Dw 0 x) + hsNormSq (Dw 1 x)))
  let Draw := B.indicator (fun x => ENNReal.ofReal (‖w 0 x - w 1 x‖ ^ 2))
  let basis := (Pi.basisFun ℝ (Fin 3)).isUnitSMul (w := fun _ : Fin 3 => h)
    (fun _ => hh.ne'.isUnit)
  let L := Submodule.span ℤ (range basis)
  obtain ⟨ν, hν⟩ := scaled_integer_lattice_embedding hh
  let origin (z : L) : Point := WithLp.toLp 2 ((z : Fin 3 → ℝ) + offset)
  have hPT (e : TensorGridEdge) (t : ℝ) :
      tensorGridEdgePoint c h e t = origin (ν e.1) + t • EuclideanSpace.single e.2 (1 : ℝ) := by
    unfold tensorGridEdgePoint
    congr 1
    ext i
    change offset i + (e.1 i : ℝ) * h = ((ν e.1 : L) : Fin 3 → ℝ) i + offset i
    rw [hν, add_comm]
  let C := ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ico (0 : ℝ) h
  let F (g : Point → ℝ≥0∞) (i : Fin 3) (z : L) :=
    ∫⁻ t : Domain 1 in C, g (origin z + t 0 • EuclideanSpace.single i (1 : ℝ))
  let E (e : TensorGridEdge) := F Eraw e.2 (ν e.1)
  let D (e : TensorGridEdge) := F Draw e.2 (ν e.1)
  let A₀ := nativeSphereGradientEnergy (P 0) (hP 0) + nativeSphereGradientEnergy (P 1) (hP 1)
  let D₀ := ∫ θ : UnitTensorSphere, ‖P 0 θ - P 1 θ‖ ^ 2 ∂tensorSphereMeasure
  let coeff : ℝ≥0∞ := 2 * (ENNReal.ofReal (h ^ 3))⁻¹ * (3 * ENNReal.ofReal h)
  have hEN (i : Fin 3) : (∑' z : L, F Eraw i z) ≤ coeff * ENNReal.ofReal (4 * A₀) := by
    have hi := hE i
    simpa only [F, C, Eraw, B, R, coeff, origin, L, basis, sampleFace, Fin.sum_univ_one,
      Function.Embedding.coeFn_mk, Fintype.card_fin, Nat.cast_ofNat, nativeSphereGradientEnergy,
      A₀, Nat.cast_one, pow_one, div_one, Nat.reduceAdd, Nat.reduceSub,
      show (2 : ℝ) + 2 = 4 by norm_num, show (2 : ℝ) + 1 - 2 = 1 by norm_num] using hi
  have hDN (i : Fin 3) : (∑' z : L, F Draw i z) ≤ coeff * ENNReal.ofReal ((64 / 3) * D₀) := by
    have hi := hD i
    simpa only [F, C, Draw, B, R, coeff, origin, L, basis, sampleFace, Fin.sum_univ_one,
      Function.Embedding.coeFn_mk, Fintype.card_fin, Nat.cast_ofNat, D₀,
      pow_one, Nat.reduceAdd, show (2 : ℝ) + 2 = 4 by norm_num,
      show (2 : ℝ) + 1 = 3 by norm_num, show (4 : ℝ) ^ 3 = 64 by norm_num] using hi
  have hTotal (g : Point → ℝ≥0∞) {b : ℝ≥0∞} (hb : ∀ i, (∑' z : L, F g i z) ≤ b) :
      (∑' e : TensorGridEdge, F g e.2 (ν e.1)) ≤ 3 * b := by
    calc
      _ = ∑' z : Fin 3 → ℤ, ∑' i : Fin 3, F g i (ν z) :=
        ENNReal.tsum_prod (f := fun (z : Fin 3 → ℤ) (i : Fin 3) => F g i (ν z))
      _ = ∑ i : Fin 3, ∑' z : Fin 3 → ℤ, F g i (ν z) := by
        rw [ENNReal.tsum_comm, tsum_fintype]
      _ ≤ ∑ _i : Fin 3, b := by
        apply Finset.sum_le_sum
        intro i _
        exact (ENNReal.tsum_comp_le_tsum_of_injective ν.injective (F g i)).trans (hb i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have hETotal := hTotal Eraw hEN
  have hDTotal := hTotal Draw hDN
  have hCoeffFinite : coeff ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos hh 3)).ne'))
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
  have hEF : (∑' e : TensorGridEdge, E e) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top hCoeffFinite ENNReal.ofReal_ne_top))
      hETotal
  have hDF : (∑' e : TensorGridEdge, D e) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top hCoeffFinite ENNReal.ofReal_ne_top))
      hDTotal
  obtain ⟨m, hm, hESel, hDSel⟩ := exists_cubeBoundaryEdges_linear_gain hh hhsmall E D hEF hDF
  have hc (i : Fin 3) : c i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(hOffset i).1, (hOffset i).2.le.trans hhsmall⟩
  obtain ⟨hClosed, _, hCube, _⟩ := shiftedCoordinateCube_geometry hc hm
  have hIn {e : TensorGridEdge} (he : e ∈ cubeBoundaryEdges m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) h) :
      tensorGridEdgePoint c h e t ∈ shiftedCoordinateCube c ((m : ℝ) * h) := by
    rw [← hClosed.closure_eq]
    exact frontier_subset_closure (tensorGridEdgePoint_mem_frontier hh he ht)
  have hImage {e : TensorGridEdge} (he : e ∈ cubeBoundaryEdges m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) h) :
      tensorGridEdgePoint c h e t ∈ B := by
    have hNorm := StratificationTheory.euclidean_norm_le_dim_of_coordinate_bound
      (tensorGridEdgePoint c h e t) (fun j => (abs_lt.mpr (hCube _ (hIn he ht) j)).le)
    exact mem_ball_zero_iff.mpr (hNorm.trans_lt (by norm_num [R]))
  have hSample (g : Point → ℝ≥0∞) (e : TensorGridEdge) :
      (∫⁻ t in Ioo (0 : ℝ) h, g (tensorGridEdgePoint c h e t)) ≤ F g e.2 (ν e.1) := by
    simp_rw [hPT]
    exact StratificationTheory.lintegral_real_edge_le_native_channel _ _ _ _ (fun _ _ => le_rfl)
  have hA₀ : 0 ≤ A₀ := add_nonneg
    (integral_nonneg fun _ => hsNormSq_nonneg _) (integral_nonneg fun _ => hsNormSq_nonneg _)
  have hD₀ : 0 ≤ D₀ := integral_nonneg fun _ => sq_nonneg _
  have hScale (b : ℝ) (hb : 0 ≤ b) : ENNReal.ofReal (32 * h) * (3 * (coeff * ENNReal.ofReal b)) =
      ENNReal.ofReal (576 / h * b) := by
    rw [← mul_assoc (3 : ℝ≥0∞), ← mul_assoc, sampled_edge_mass_scale hh, ENNReal.ofReal_mul]
    positivity
  refine ⟨w, Dw, ?_, hRad, c, m, hOffset, hm, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, show (2 : ℝ) + 2 = 4 by norm_num] using hW
  · intro e he l
    let U : OpenDomain 1 := ⟨{t : Domain 1 | t 0 ∈ Ioo (0 : ℝ) h},
      isOpen_Ioo.preimage (EuclideanSpace.proj 0).continuous⟩
    have hU (t : Domain 1) (ht : t ∈ U.val) :
        origin (ν e.1) + (∑ s : Fin 1, t s • EuclideanSpace.single (sampleFace e.2 s) (1 : ℝ)) ∈
          ball (0 : Point) ((2 : ℝ) + 2) := by
      change t 0 ∈ Ioo (0 : ℝ) h at ht
      simpa only [sampleFace, Fin.sum_univ_one, Function.Embedding.coeFn_mk,
        show (2 : ℝ) + 2 = 4 by norm_num, ← hPT] using hImage he (Ioo_subset_Icc_self ht)
    have hw := hFace (ν e.1) e.2 U hU
    simp_rw [hPT]
    fin_cases l
    · simpa only [sampleFace, Fin.sum_univ_one, Function.Embedding.coeFn_mk, origin] using! hw.1
    · simpa only [sampleFace, Fin.sum_univ_one, Function.Embedding.coeFn_mk, origin] using! hw.2
  · intro e he l
    let i := e.2
    let y := origin (ν e.1)
    let W := StratificationTheory.coordinatePermACLRepresentative (gridAxisPermutation i)
      (-1 : ℝ) 1 (w l) (Dw l)
    let head := (gridSplit ((gridAxisEquiv i).symm y)).1
    let line (r : ℝ) : Point := gridAxisEquiv i (gridSplit.symm (head, EuclideanSpace.single 0 r))
    let g (t : ℝ) := W (line (y i + t))
    have hLine (t : ℝ) : line (y i + t) = tensorGridEdgePoint c h e t := by
      rw [hPT]
      have hLine := StratificationTheory.coordinate_line_eq_add_normal (n := 2)
        (gridAxisPermutation i) y (y i + t)
      simpa only [gridAxisPermutation, Equiv.swap_apply_left, add_sub_cancel_left] using hLine
    have hEnd (t : ℝ) (ht : t ∈ Icc 0 h) (j : Fin 3) :
        tensorGridEdgePoint c h e t j ∈ Ioo (-1 : ℝ) 1 := hCube _ (hIn he ht) j
    have h0 : tensorGridEdgePoint c h e 0 = y := by rw [hPT, zero_smul, add_zero]
    have hStart := hEnd 0 ⟨le_rfl, hh.le⟩
    rw [h0] at hStart
    have hShift (t : ℝ) (ht : t ∈ Icc 0 h) : y i + t ∈ Ioo (-1 : ℝ) 1 := by
      have h := hEnd t ht i
      rw [hPT] at h
      simpa [y, i, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply] using h
    obtain ⟨hLower, _, hLineGrad, hAC, hAE, hValues, _⟩ :=
      hACL (ν e.1) l i (gridSplit_in_unit_box i hStart)
    have hAxis : gridAxisPermutation i (Fin.natAdd 2 (0 : Fin 1)) = i :=
      Equiv.swap_apply_left _ _
    have hInc' (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
        W (line t) - W (line s) = ∫ r in s..t, Dw l (line r) i := by
      calc
        _ = ∫ r in s..t, Dw l (line r) (gridAxisPermutation i (Fin.natAdd 2 (0 : Fin 1))) :=
          StratificationTheory.coordinatePermACLRepresentative_integral_increments_of_memLp
            (n := 2) (gridAxisPermutation i) (by norm_num) (w l) (Dw l) head hLineGrad s hs t ht
        _ = _ := congrArg (fun j => ∫ r in s..t, Dw l (line r) j) hAxis
    obtain ⟨z', hz'⟩ := StratificationTheory.exists_scaled_grid_neighbor hh offset (ν e.1) i
    have hzEnd : origin z' = tensorGridEdgePoint c h e h := hz'.trans (hPT e h).symm
    have hzBox : ∀ j : Fin 3, origin z' j ∈ Ioo (-1 : ℝ) 1 :=
      hzEnd ▸ hEnd h ⟨hh.le, le_rfl⟩
    have hUpper := (hACL z' l i (gridSplit_in_unit_box i hzBox)).1
    change W (origin z') = w l (origin z') at hUpper
    rw [hzEnd] at hUpper
    have hCont := hAC.continuousOn
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hCont
    change ContinuousOn (fun r => W (line r)) (Icc (-1 : ℝ) 1) at hCont
    refine ⟨g, hCont.comp (continuous_const.add continuous_id).continuousOn
      (fun t ht => Ioo_subset_Icc_self (hShift t ht)), ?_, ?_, ?_, ?_, ?_⟩
    · apply (ae_restrict_iff' measurableSet_Ioo).mpr
      change (fun r => W (line r)) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] (fun r => w l (line r)) at hAE
      have hAE' := (measurePreserving_add_left (volume : Measure ℝ) (y i)).quasiMeasurePreserving.ae
        ((ae_restrict_iff' measurableSet_Ioo).mp hAE)
      filter_upwards [hAE'] with t ht hmem
      simpa only [g, hLine] using ht (hShift t (Ioo_subset_Icc_self hmem))
    · change W (line (y i + 0)) = _
      rw [hLine, h0]
      exact hLower
    · change W (line (y i + h)) = _
      rw [hLine]
      exact hUpper
    · intro t ht
      exact hValues (y i + t) (Ioo_subset_Icc_self (hShift t ht))
    · intro s hs t ht
      have hFTC := hInc' (y i + s) (Ioo_subset_Icc_self (hShift s hs))
        (y i + t) (Ioo_subset_Icc_self (hShift t ht))
      rw [← intervalIntegral.integral_comp_add_left (fun r => Dw l (line r) i) (y i)] at hFTC
      simpa only [g, hLine] using hFTC
  · calc
      _ ≤ ∑ e ∈ cubeBoundaryEdges m, E e := by
        apply Finset.sum_le_sum
        intro e he
        refine (setLIntegral_mono' measurableSet_Ioo fun t ht => ?_).trans (hSample Eraw e)
        simp only [Eraw, Set.indicator_of_mem (hImage he (Ioo_subset_Icc_self ht)), le_refl]
      _ ≤ ENNReal.ofReal (32 * h) * (3 * (coeff * ENNReal.ofReal (4 * A₀))) :=
        hESel.trans (mul_le_mul_right hETotal _)
      _ = _ := by
        rw [hScale _ (mul_nonneg (by norm_num) hA₀)]
        rw [show 576 / h * (4 * A₀) = (2304 / h) * A₀ by ring,
          ENNReal.ofReal_mul (by positivity)]
  · calc
      _ ≤ ∑ e ∈ cubeBoundaryEdges m, D e := by
        apply Finset.sum_le_sum
        intro e he
        refine (setLIntegral_mono' measurableSet_Ioo fun t ht => ?_).trans (hSample Draw e)
        simp only [Draw, Set.indicator_of_mem (hImage he (Ioo_subset_Icc_self ht)), le_refl]
      _ ≤ ENNReal.ofReal (32 * h) * (3 * (coeff * ENNReal.ofReal ((64 / 3) * D₀))) :=
        hDSel.trans (mul_le_mul_right hDTotal _)
      _ = _ := by
        rw [hScale _ (mul_nonneg (by norm_num) hD₀)]
        rw [show 576 / h * ((64 / 3) * D₀) = (12288 / h) * D₀ by ring,
          ENNReal.ofReal_mul (by positivity)]

end Thesis

end
