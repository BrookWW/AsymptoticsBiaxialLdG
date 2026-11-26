module

public import Thesis.Interpolation.TerminalCylinderSurfaceMeasure
public import Thesis.MeasureGeometry.MeridianCoordinates
import Thesis.Interpolation.CylinderRadialZeroExtension
import HarmonicMaps.Analysis.EuclideanHausdorffLipschitz
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! Radial disk coordinates on overlapping halves of the physical terminal boundary. -/

@[expose] public section

noncomputable section

open HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace Thesis.MeasureGeometry

/-- An open annulus containing the unit sphere and avoiding the origin. -/
def terminalRoundShell : OpenDomain 3 :=
  ⟨{x | ‖x‖ ∈ Ioo (1 / 2 : ℝ) 2}, isOpen_Ioo.preimage continuous_norm⟩

/-- The signed axial coordinate normalized by the cylinder aspect ratio. -/
def terminalSignedHeight (B : OrthonormalBasis (Fin 3) ℝ Point) (s k : ℝ) (x : Point) : ℝ :=
  (s * k) * cylinderHeight (B 2) x

/-- The common transverse-axial gauge, in the orthonormal frame. -/
def terminalFrameGauge (B : OrthonormalBasis (Fin 3) ℝ Point) (k : ℝ) (x : Point) : ℝ :=
  max ‖axisChartTransverseCoordinates B x‖ (k * |cylinderHeight (B 2) x|)

theorem terminalFrameGauge_eq (B : OrthonormalBasis (Fin 3) ℝ Point) (k : ℝ) (x : Point) :
    terminalFrameGauge B k x = cylinderCapGauge (B 2) k x := by
  unfold terminalFrameGauge cylinderCapGauge
  rw [norm_axisChartTransverseCoordinates_eq]

theorem continuous_terminalFrameGauge (B : OrthonormalBasis (Fin 3) ℝ Point) (k : ℝ) :
    Continuous (terminalFrameGauge B k) :=
  (axisChartTransverseCoordinates B).continuous.norm.max
    (continuous_const.mul (continuous_const.inner continuous_id).abs)

theorem continuous_terminalSignedHeight (B : OrthonormalBasis (Fin 3) ℝ Point) (s k : ℝ) :
    Continuous (terminalSignedHeight B s k) :=
  continuous_const.mul (continuous_const.inner continuous_id)

/-- Each half includes its disk and extends beyond the central wall circle. -/
def terminalHalfShell (B : OrthonormalBasis (Fin 3) ℝ Point) (s k : ℝ) : OpenDomain 3 :=
  ⟨terminalRoundShell.val ∩ {x | terminalSignedHeight B s k x < terminalFrameGauge B k x / 2},
    terminalRoundShell.property.inter
      (isOpen_lt (continuous_terminalSignedHeight B s k) ((continuous_terminalFrameGauge B k).div_const 2))⟩

theorem terminalHalfShell_cover (B : OrthonormalBasis (Fin 3) ℝ Point) {k : ℝ} (hk : 1 ≤ k) :
    (terminalHalfShell B 1 k).val ∪ (terminalHalfShell B (-1) k).val = terminalRoundShell.val := by
  have hpos (x : Point) (hx : x ∈ terminalRoundShell.val) : 0 < terminalFrameGauge B k x := by
    have hN : 0 < ‖x‖ := (by norm_num : (0 : ℝ) < 1 / 2).trans hx.1
    have hP := norm_axisChart_sq B (axisChartTransverseCoordinates B x) (cylinderHeight (B 2) x)
    rw [axisChart_reassemble] at hP
    by_contra! h
    have hY := (le_max_left ‖axisChartTransverseCoordinates B x‖ (k * |cylinderHeight (B 2) x|)).trans h
    have hZ := (le_max_right ‖axisChartTransverseCoordinates B x‖ (k * |cylinderHeight (B 2) x|)).trans h
    have hZ' : cylinderHeight (B 2) x = 0 := abs_eq_zero.mp (le_antisymm
      ((le_mul_of_one_le_left (abs_nonneg _) hk).trans hZ) (abs_nonneg _))
    rw [le_antisymm hY (norm_nonneg _), hZ', zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at hP
    exact (pow_pos hN 2).ne' hP
  refine subset_antisymm (union_subset inter_subset_left inter_subset_left) ?_
  intro x hx
  have hG := hpos x hx
  by_cases hz : 0 ≤ cylinderHeight (B 2) x
  · right
    refine ⟨hx, ?_⟩
    change ((-1 : ℝ) * k) * cylinderHeight (B 2) x < terminalFrameGauge B k x / 2
    have h := mul_nonneg ((zero_le_one : (0 : ℝ) ≤ 1).trans hk) hz
    nlinarith only [hG, h]
  · left
    refine ⟨hx, ?_⟩
    change ((1 : ℝ) * k) * cylinderHeight (B 2) x < terminalFrameGauge B k x / 2
    rw [one_mul]
    exact (mul_nonpos_of_nonneg_of_nonpos (zero_le_one.trans hk) (le_of_not_ge hz)).trans_lt (half_pos hG)

/-- A positive denominator for the lower chart, extended across the opposite cap. -/
def terminalHalfDenominator (B : OrthonormalBasis (Fin 3) ℝ Point) (s k : ℝ) (x : Point) : ℝ :=
  max (1 / 4) (max ‖axisChartTransverseCoordinates B x‖ (-terminalSignedHeight B s k x))

/-- The radial planar parameter of one disk and the adjoining wall. -/
def terminalHalfParameter (B : OrthonormalBasis (Fin 3) ℝ Point) (s k R : ℝ) (x : Point) : Plane :=
  let d := terminalHalfDenominator B s k x
  let z := min (terminalSignedHeight B s k x) d
  R • ((3 / 2 + (z / d) / 2) • (d⁻¹ • axisChartTransverseCoordinates B x))

/-- The same closed disk and wall parameter, with the orientation of the chosen cap. -/
def terminalOrientedFace (B : OrthonormalBasis (Fin 3) ℝ Point) (s R H : ℝ) (y : Plane) : Point :=
  if ‖y‖ ≤ R then axisChart B (y, -s * H)
  else axisChart B (R • NormedSpace.normalize y, s * ((2 * H / R) * (‖y‖ - R) - H))

private theorem terminalFrame_projection_norm (B : OrthonormalBasis (Fin 3) ℝ Point) (x : Point) :
    ‖axisChartTransverseCoordinates B x‖ ≤ ‖x‖ := by
  have h := norm_axisChart_sq B (axisChartTransverseCoordinates B x) (cylinderHeight (B 2) x)
  rw [axisChart_reassemble] at h
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [h]
  exact le_add_of_nonneg_right (sq_nonneg _)

private theorem terminalFrame_projection_lipschitz (B : OrthonormalBasis (Fin 3) ℝ Point) :
    LipschitzWith 1 (axisChartTransverseCoordinates B) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
  exact terminalFrame_projection_norm B (x - y)

private theorem terminalSignedHeight_lipschitz (B : OrthonormalBasis (Fin 3) ℝ Point)
    {s k : ℝ} (hs : |s| = 1) (hk : 0 ≤ k) (hk₄ : k ≤ 4) :
    LipschitzWith 4 (terminalSignedHeight B s k) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, terminalSignedHeight, terminalSignedHeight,
    ← mul_sub, abs_mul, abs_mul, hs, abs_of_nonneg hk, one_mul, NNReal.coe_ofNat, dist_eq_norm]
  rw [show cylinderHeight (B 2) x - cylinderHeight (B 2) y = cylinderHeight (B 2) (x - y) by
    simp only [cylinderHeight, inner_sub_right]]
  have h := abs_real_inner_le_norm (B 2) (x - y)
  rw [B.orthonormal.norm_eq_one, one_mul] at h
  exact mul_le_mul hk₄ h (abs_nonneg _) (by norm_num)

private theorem norm_scaled_difference_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) (a b : ℝ) :
    ‖a • u - b • v‖ ≤ |a| * ‖u - v‖ + |a - b| * ‖v‖ := by
  have h : a • u - b • v = a • (u - v) + (a - b) • v := by
    rw [smul_sub, sub_smul, sub_add_sub_cancel]
  rw [h]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs])

/-- Divide the two vectors by positive radii with a bound on the second norm. -/
theorem norm_inverse_smul_difference_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hv : ‖v‖ ≤ b) :
    ‖a⁻¹ • u - b⁻¹ • v‖ ≤ a⁻¹ * (‖u - v‖ + |a - b|) := by
  apply (norm_scaled_difference_le u v a⁻¹ b⁻¹).trans
  rw [abs_of_nonneg (inv_nonneg.mpr ha.le), inv_sub_inv ha.ne' hb.ne', abs_div,
    abs_of_pos (mul_pos ha hb), abs_sub_comm b a, mul_add]
  apply add_le_add le_rfl
  have h := mul_le_mul_of_nonneg_left hv (div_nonneg (abs_nonneg (a-b)) (mul_pos ha hb).le)
  have hEq : |a - b| / (a * b) * b = a⁻¹ * |a - b| := by field_simp
  exact h.trans_eq hEq

private theorem terminalHalfDenominator_lipschitz
    (B : OrthonormalBasis (Fin 3) ℝ Point) {s k : ℝ} (hs : |s| = 1) (hk : 0 ≤ k) (hk₄ : k ≤ 4) :
    LipschitzWith 4 (terminalHalfDenominator B s k) := by
  have hp : LipschitzWith 4 (fun x => ‖axisChartTransverseCoordinates B x‖) :=
    (lipschitzWith_one_norm.comp (terminalFrame_projection_lipschitz B)).weaken (by norm_num)
  have hz : LipschitzWith 4 (fun x => -terminalSignedHeight B s k x) :=
    (terminalSignedHeight_lipschitz B hs hk hk₄).neg
  have hEq : terminalHalfDenominator B s k =
      fun x => max (max ‖axisChartTransverseCoordinates B x‖ (-terminalSignedHeight B s k x)) (1 / 4) :=
    funext fun _ => max_comm _ _
  rw [hEq]
  exact (by simpa only [max_self] using (hp.max hz).max_const (1 / 4))

private theorem terminalHalfDenominator_bounds (B : OrthonormalBasis (Fin 3) ℝ Point) (s k : ℝ) (x : Point) :
    let d := terminalHalfDenominator B s k x
    1 / 4 ≤ d ∧ ‖axisChartTransverseCoordinates B x‖ ≤ d ∧ |min (terminalSignedHeight B s k x) d| ≤ d := by
  intro d
  have hd : 1 / 4 ≤ d := le_max_left _ _
  have hZ : -terminalSignedHeight B s k x ≤ d := le_trans (le_max_right _ _) (le_max_right _ _)
  have hN : 0 ≤ d := (by norm_num : (0 : ℝ) ≤ 1 / 4).trans hd
  exact ⟨hd, (le_max_left _ _).trans (le_max_right _ _),
    abs_le.mpr ⟨le_min (neg_le.mp hZ) (neg_le_self hN), min_le_right _ _⟩⟩

/-- The planar parameter has a uniform Lipschitz bound on its full ambient carrier. -/
theorem terminalHalfParameter_lipschitz (B : OrthonormalBasis (Fin 3) ℝ Point)
    {s k R : ℝ} (hs : |s| = 1) (hk : 0 ≤ k) (hk₄ : k ≤ 4) (hR : 0 < R) :
    LipschitzWith (Real.toNNReal (56 * R)) (terminalHalfParameter B s k R) := by
  let d := terminalHalfDenominator B s k
  let Z := terminalSignedHeight B s k
  let p := axisChartTransverseCoordinates B
  let w (x : Point) := min (Z x) (d x)
  let α (x : Point) := 3 / 2 + (w x / d x) / 2
  let v (x : Point) := (d x)⁻¹ • p x
  have hD := terminalHalfDenominator_lipschitz B hs hk hk₄
  have hZ := terminalSignedHeight_lipschitz B hs hk hk₄
  have hW : LipschitzWith 4 w := by simpa only [max_self] using hZ.min hD
  have hd (x : Point) := terminalHalfDenominator_bounds B s k x
  have hd₀ (x : Point) : 0 < d x := (by norm_num : (0 : ℝ) < 1 / 4).trans_le (hd x).1
  have hd₄ (x : Point) : (d x)⁻¹ ≤ 4 := by
    have h := inv_le_inv₀ (hd₀ x) (by norm_num : (0 : ℝ) < 1 / 4)
    exact (h.mpr (hd x).1).trans_eq (by norm_num)
  have ha (x : Point) : |α x| ≤ 2 := by
    have hx := abs_le.mp (hd x).2.2
    have h₀ : -1 ≤ w x / d x := (le_div_iff₀ (hd₀ x)).2 (by simpa only [neg_one_mul] using hx.1)
    have h₁ : w x / d x ≤ 1 := (div_le_iff₀ (hd₀ x)).2 (by simpa only [one_mul] using hx.2)
    have hPos : 0 ≤ α x := by dsimp only [α]; linarith only [h₀]
    rw [abs_of_nonneg hPos]
    dsimp only [α]
    linarith only [h₁]
  have hv (x : Point) : ‖v x‖ ≤ 1 := by
    rw [show v x = (d x)⁻¹ • p x from rfl, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hd₀ x).le)]
    exact (mul_le_mul_of_nonneg_left (hd x).2.1 (inv_nonneg.mpr (hd₀ x).le)).trans_eq
      (inv_mul_cancel₀ (hd₀ x).ne')
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  have hdxy : |d x - d y| ≤ 4 * ‖x - y‖ := by
    simpa only [Real.dist_eq, NNReal.coe_ofNat, dist_eq_norm, Real.norm_eq_abs] using hD.dist_le_mul x y
  have hwxy : |w x - w y| ≤ 4 * ‖x - y‖ := by
    simpa only [Real.dist_eq, NNReal.coe_ofNat, dist_eq_norm, Real.norm_eq_abs] using hW.dist_le_mul x y
  have hPxy : ‖p x - p y‖ ≤ ‖x - y‖ := by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using (terminalFrame_projection_lipschitz B).dist_le_mul x y
  have hvxy : ‖v x - v y‖ ≤ 20 * ‖x - y‖ := by
    calc
      _ ≤ (d x)⁻¹ * (‖p x - p y‖ + |d x - d y|) :=
        norm_inverse_smul_difference_le _ _ (hd₀ x) (hd₀ y) (hd y).2.1
      _ ≤ 4 * (‖x - y‖ + 4 * ‖x - y‖) :=
        mul_le_mul (hd₄ x) (add_le_add hPxy hdxy)
          (add_nonneg (norm_nonneg _) (abs_nonneg _)) (by norm_num)
      _ = _ := by ring
  have hαxy : |α x - α y| ≤ 16 * ‖x - y‖ := by
    have h := norm_inverse_smul_difference_le (w x) (w y) (hd₀ x) (hd₀ y)
      (by simpa only [Real.norm_eq_abs] using (hd y).2.2)
    rw [show (d x)⁻¹ • w x - (d y)⁻¹ • w y = w x / d x - w y / d y by
      simp only [smul_eq_mul, div_eq_mul_inv, mul_comm], Real.norm_eq_abs, Real.norm_eq_abs] at h
    have h' : |w x / d x - w y / d y| ≤ 4 * (4 * ‖x - y‖ + 4 * ‖x - y‖) :=
      h.trans (mul_le_mul (hd₄ x) (add_le_add hwxy hdxy)
        (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num))
    rw [show α x - α y = (w x / d x - w y / d y) / 2 by dsimp only [α]; ring, abs_div,
      abs_of_pos (show (0 : ℝ) < 2 from zero_lt_two : (0 : ℝ) < 2)]
    linarith only [h']
  change ‖R • (α x • v x) - R • (α y • v y)‖ ≤ _
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg hR.le]
  have h := (norm_scaled_difference_le (v x) (v y) (α x) (α y)).trans
    (add_le_add (mul_le_mul (ha x) hvxy (norm_nonneg _) (by norm_num))
      (mul_le_mul hαxy (hv y) (norm_nonneg _) (by positivity)))
  exact (mul_le_mul_of_nonneg_left h hR.le).trans_eq (by ring)

private theorem terminalFrameGauge_ge_half_norm
    (B : OrthonormalBasis (Fin 3) ℝ Point) {k : ℝ} (hk : 1 ≤ k) (x : Point) :
    ‖x‖ ≤ 2 * terminalFrameGauge B k x := by
  have hP : ‖axisChartTransverseCoordinates B x‖ ≤ terminalFrameGauge B k x := le_max_left _ _
  have hZ : |cylinderHeight (B 2) x| ≤ terminalFrameGauge B k x :=
    (le_mul_of_one_le_left (abs_nonneg _) hk).trans (le_max_right _ _)
  have h := norm_add_le (axisChartPlane B (axisChartTransverseCoordinates B x))
    (cylinderHeight (B 2) x • B 2)
  rw [axisChart_decompose, norm_axisChartPlane, norm_smul, B.orthonormal.norm_eq_one,
    mul_one, Real.norm_eq_abs] at h
  linarith only [h, hP, hZ]

private theorem axisChart_pair_smul (B : OrthonormalBasis (Fin 3) ℝ Point) (t : ℝ)
    (y : Plane) (z : ℝ) : axisChart B (t • y, t * z) = t • axisChart B (y, z) := by
  rw [axisChart_eq_plane_add_axis B (t • y) (t*z), axisChart_eq_plane_add_axis B y z,
    map_smul, smul_add, smul_smul]

/-- On a terminal half of the round annulus, the chosen chart recovers
the actual cylinder boundary along the original ray. -/
theorem terminalHalfParameter_reconstruct (B : OrthonormalBasis (Fin 3) ℝ Point)
    {s R H : ℝ} (hs : |s| = 1) (hR : 0 < R) (hH : 0 < H) (hk : 1 ≤ R / H)
    {x : Point} (hx : x ∈ (terminalHalfShell B s (R / H)).val) :
    let m := terminalFrameGauge B (R / H) x
    let y := terminalHalfParameter B s (R / H) R x
    0 < m ∧ y ∈ ball (0 : Plane) (2 * R) ∧
      terminalOrientedFace B s R H y = (R / m) • x := by
  intro m y
  let p := axisChartTransverseCoordinates B x
  let z := cylinderHeight (B 2) x
  let Z := terminalSignedHeight B s (R / H) x
  have hxNorm : ‖x‖ ∈ Ioo (1/2 : ℝ) 2 := hx.1
  have hX : ‖x‖ ≤ 2 * m := terminalFrameGauge_ge_half_norm B hk x
  have hm₄ : 1 / 4 < m := by linarith only [hX, hxNorm.1]
  have hm : 0 < m := (by norm_num : (0 : ℝ) < 1 / 4).trans hm₄
  have hK : 0 ≤ R / H := div_nonneg hR.le hH.le
  have hZabs : |Z| = (R / H) * |z| := by
    change |s * (R / H) * z| = _
    rw [abs_mul, abs_mul, hs, abs_of_nonneg hK, one_mul]
  have hmEq : m = max ‖p‖ |Z| := by
    rw [hZabs]
    rfl
  have hZhalf : Z < m / 2 := hx.2
  have hMNeg : max ‖p‖ (-Z) = m := by
    by_cases hz : Z ≤ 0
    · rw [hmEq, abs_of_nonpos hz]
    · have hp : |Z| ≤ ‖p‖ := by
        by_contra! hp
        have hme : m = Z := hmEq.trans ((max_eq_right hp.le).trans (abs_of_pos (lt_of_not_ge hz)))
        rw [hme] at hm₄ hZhalf
        linarith only [hm₄, hZhalf]
      rw [max_eq_left ((neg_le_abs Z).trans hp), hmEq, max_eq_left hp]
  have hd : terminalHalfDenominator B s (R / H) x = m := by
    change max (1 / 4 : ℝ) (max ‖p‖ (-Z)) = m
    rw [hMNeg, max_eq_right hm₄.le]
  have hMin : min Z m = Z := min_eq_left (by linarith only [hZhalf, hm])
  let a : ℝ := 3 / 2 + (Z / m) / 2
  have hY : y = (R * a / m) • p := by
    change R • ((3 / 2 + (min Z (terminalHalfDenominator B s (R/H) x) /
      terminalHalfDenominator B s (R/H) x) / 2) •
      ((terminalHalfDenominator B s (R/H) x)⁻¹ • p)) = _
    rw [hd, hMin, smul_smul, smul_smul, mul_assoc, div_eq_mul_inv]
    dsimp only [a]
    congr 1
    ring
  have hs₂ : s * s = 1 := by
    have h := congrArg (fun t : ℝ => t ^ 2) hs
    change |s| ^ 2 = 1 ^ 2 at h
    rw [sq_abs, one_pow, pow_two] at h
    exact h
  have hSZ : s * (H * Z) = R * z := by
    calc
      _ = (s*s) * ((R/H)*H) * z := by dsimp only [Z, terminalSignedHeight, z]; ring
      _ = _ := by rw [hs₂, div_mul_cancel₀ _ hH.ne', one_mul]
  have hHeight : s * (H * (Z/m)) = (R/m) * z := by
    calc
      _ = (s * (H * Z)) / m := by ring
      _ = _ := by rw [hSZ]; ring
  have hVec : axisChart B ((R/m) • p, (R/m) * z) = (R/m) • x := by
    rw [axisChart_pair_smul, axisChart_reassemble]
  refine ⟨hm, ?_⟩
  by_cases hCap : ‖p‖ ≤ -Z
  · have hMN : m = -Z := hMNeg.symm.trans (max_eq_right hCap)
    have hZD : Z / m = -1 := by
      apply (div_eq_iff hm.ne').2
      rw [hMN]
      ring
    have hA : a = 1 := by dsimp only [a]; rw [hZD]; norm_num
    have hy : y = (R/m) • p := by rw [hY, hA, mul_one]
    have hyR : ‖y‖ ≤ R := by
      rw [hy, norm_smul, Real.norm_of_nonneg (div_nonneg hR.le hm.le)]
      refine (mul_le_mul_of_nonneg_left (hCap.trans_eq hMN.symm) (div_nonneg hR.le hm.le)).trans_eq ?_
      exact div_mul_cancel₀ _ hm.ne'
    refine ⟨mem_ball_zero_iff.2 (hyR.trans_lt (by linarith only [hR])), ?_⟩
    have hz : -s * H = (R/m) * z := by
      rw [hZD] at hHeight
      linarith only [hHeight]
    rw [terminalOrientedFace, if_pos hyR, hy, hz, hVec]
  · have hRho : m = ‖p‖ := hMNeg.symm.trans (max_eq_left (le_of_lt (lt_of_not_ge hCap)))
    have ha₁ : 1 < a := by
      have h := (lt_div_iff₀ hm).2 (show (-1 : ℝ) * m < Z by
        rw [hRho, neg_one_mul]
        linarith only [lt_of_not_ge hCap])
      dsimp only [a]
      linarith only [h]
    have ha₂ : a < 2 := by
      have h := (div_lt_iff₀ hm).2 (show Z < (1/2 : ℝ) * m by linarith only [hZhalf])
      dsimp only [a]
      linarith only [h]
    have ha₀ : 0 < a := zero_lt_one.trans ha₁
    have hyNorm : ‖y‖ = R * a := by
      rw [hY, norm_smul, Real.norm_of_nonneg (by positivity), ← hRho, div_mul_cancel₀ _ hm.ne']
    have hyGt : R < ‖y‖ := by
      rw [hyNorm]
      simpa only [mul_one] using mul_lt_mul_of_pos_left ha₁ hR
    have hyLt : ‖y‖ < 2 * R := by
      rw [hyNorm, mul_comm 2 R]
      exact mul_lt_mul_of_pos_left ha₂ hR
    refine ⟨mem_ball_zero_iff.2 hyLt, ?_⟩
    have hNorm : R • NormedSpace.normalize y = (R/m) • p := by
      rw [hY, NormedSpace.normalize_smul_of_pos (by positivity : 0 < R * a / m),
        NormedSpace.normalize, ← hRho, smul_smul, div_eq_mul_inv]
    have hCoord : s * (2 * H / R * (‖y‖ - R) - H) = (R/m) * z := by
      rw [hyNorm, ← hHeight]
      dsimp only [a]
      field_simp
      ring
    rw [terminalOrientedFace, if_neg (not_le_of_gt hyGt), hNorm, hCoord, hVec]

private theorem axisChart_pair_sub (B : OrthonormalBasis (Fin 3) ℝ Point)
    (y z : Plane) (u v : ℝ) : axisChart B (y - z, u - v) = axisChart B (y, u) - axisChart B (z, v) := by
  rw [axisChart_eq_plane_add_axis B (y-z) (u-v), axisChart_eq_plane_add_axis B y u,
    axisChart_eq_plane_add_axis B z v, map_sub, sub_smul, add_sub_add_comm]

private theorem terminalAxisOrientation_isometry
    (B : OrthonormalBasis (Fin 3) ℝ Point) {s : ℝ} (hs : |s| = 1) :
    Isometry (fun x => axisChart B (axisChartTransverseCoordinates B x, s * cylinderHeight (B 2) x)) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← axisChart_pair_sub, ← map_sub, ← mul_sub]
  rw [show cylinderHeight (B 2) x - cylinderHeight (B 2) y = cylinderHeight (B 2) (x-y) from
    (inner_sub_right _ _ _).symm]
  have h := norm_axisChart_sq B (axisChartTransverseCoordinates B (x-y)) (cylinderHeight (B 2) (x-y))
  rw [axisChart_reassemble] at h
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_axisChart_sq, h,
    mul_pow, ← sq_abs s, hs, one_pow, one_mul]

private theorem norm_axisChart_height_lower
    (B : OrthonormalBasis (Fin 3) ℝ Point) (p : Plane) (t : ℝ) :
    |t| ≤ ‖axisChart B (p, t)‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [sq_abs, norm_axisChart_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

private theorem norm_axisChart_transverse_lower
    (B : OrthonormalBasis (Fin 3) ℝ Point) (p : Plane) (t : ℝ) :
    ‖p‖ ≤ ‖axisChart B (p, t)‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [norm_axisChart_sq]
  exact le_add_of_nonneg_right (sq_nonneg _)

private theorem terminalOrientedFace_norm_lower
    (B : OrthonormalBasis (Fin 3) ℝ Point) {s R H : ℝ}
    (hs : |s| = 1) (hR : 0 < R) (hH : 0 < H) (hHigh : H ≤ R) (y : Plane) :
    H ≤ ‖terminalOrientedFace B s R H y‖ := by
  unfold terminalOrientedFace
  split_ifs with hy
  · have h := norm_axisChart_height_lower B y (-s*H)
    rw [abs_mul, abs_neg, hs, abs_of_nonneg hH.le, one_mul] at h
    exact h
  · have hy₀ : y ≠ 0 := norm_pos_iff.mp (hR.trans (lt_of_not_ge hy))
    have h := norm_axisChart_transverse_lower B (R • NormedSpace.normalize y)
      (s * (2 * H / R * (‖y‖ - R) - H))
    rw [norm_smul, NormedSpace.norm_normalize hy₀, Real.norm_of_nonneg hR.le, mul_one] at h
    exact hHigh.trans h

private theorem terminalOrientedFace_lipschitzOn
    (B : OrthonormalBasis (Fin 3) ℝ Point) {s R H : ℝ}
    (hs : |s| = 1) (hR : 0 < R) (hH : 0 < H) (hHigh : H ≤ R) :
    LipschitzOnWith 4 (terminalOrientedFace B s R H) (closedBall (0 : Plane) (2 * R)) := by
  let f (y : Plane) := axisChart B (y, -s * H)
  let g (y : Plane) := axisChart B (R • NormedSpace.normalize y, s * (2 * H / R * (‖y‖ - R) - H))
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro x y
    change dist (axisChart B (x, -s*H)) (axisChart B (y, -s*H)) = dist x y
    rw [axisChart_eq_plane_add_axis B x _, axisChart_eq_plane_add_axis B y _,
      dist_add_right, dist_eq_norm, dist_eq_norm, ← map_sub, norm_axisChartPlane]
  have hg : LipschitzOnWith 4 g (closedPlanarRadialCollar R (2 * R)) := by
    let Q (x : Point) := axisChart B (axisChartTransverseCoordinates B x, s * cylinderHeight (B 2) x)
    have hQ : Isometry Q := terminalAxisOrientation_isometry B hs
    have hEq : g = Q ∘ terminalWallChart B 0 R H := by
      funext y
      change g y = Q (0 + axisChart B (R • NormedSpace.normalize y, 2 * H / R * (‖y‖ - R) - H))
      rw [zero_add]
      unfold Q g
      rw [axisChartTransverseCoordinates_axisChart, cylinderHeight_axisChart]
    rw [hEq]
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change dist (Q (terminalWallChart B 0 R H x)) (Q (terminalWallChart B 0 R H y)) ≤ _
    rw [hQ.dist_eq]
    exact (terminalWallChart_lipschitzOn_closedCollar B 0 hR hH.le hHigh).dist_le_mul x hx y hy
  have hJoin (y : Plane) (hy : ‖y‖ = R) : f y = g y := by
    have hy₀ : y ≠ 0 := norm_pos_iff.mp (hy.symm ▸ hR)
    change axisChart B (y, -s * H) =
      axisChart B (R • NormedSpace.normalize y, s * (2 * H / R * (‖y‖ - R) - H))
    rw [hy, sub_self, mul_zero, zero_sub, NormedSpace.normalize, hy, smul_inv_smul₀ hR.ne', mul_neg, neg_mul]
  let u := terminalOrientedFace B s R H
  have hMix (x y : Plane) (hx : ‖x‖ ≤ R) (hy : R < ‖y‖) (hy₂ : ‖y‖ ≤ 2 * R) :
      dist (u x) (u y) ≤ 4 * dist x y := by
    let γ : ℝ → Plane := AffineMap.lineMap x y
    have hc : ContinuousOn (fun t => ‖γ t‖) (Icc (0 : ℝ) 1) :=
      (lipschitzWith_lineMap (𝕜 := ℝ) x y).continuous.norm.continuousOn
    have hI : R ∈ Icc ‖γ 0‖ ‖γ 1‖ := by
      change R ∈ Icc ‖AffineMap.lineMap x y (0 : ℝ)‖ ‖AffineMap.lineMap x y (1 : ℝ)‖
      rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
      exact ⟨hx, hy.le⟩
    obtain ⟨t, ht, htR⟩ := intermediate_value_Icc zero_le_one hc hI
    let z := γ t
    have hz : ‖z‖ = R := htR
    have hxz : dist x z = t * dist x y := by
      rw [show z = AffineMap.lineMap x y t from rfl, dist_left_lineMap,
        Real.norm_of_nonneg ht.1]
    have hzy : dist z y = (1 - t) * dist x y := by
      rw [show z = AffineMap.lineMap x y t from rfl, dist_lineMap_right,
        Real.norm_of_nonneg (sub_nonneg.2 ht.2)]
    change dist (terminalOrientedFace B s R H x) (terminalOrientedFace B s R H y) ≤ _
    rw [terminalOrientedFace, if_pos hx, terminalOrientedFace, if_neg (not_le_of_gt hy)]
    change dist (f x) (g y) ≤ _
    have hD := hg.dist_le_mul z (show z ∈ closedPlanarRadialCollar R (2 * R) from
      ⟨hz.ge, hz.le.trans (by linarith only [hR])⟩) y ⟨hy.le, hy₂⟩
    rw [← hJoin z hz, NNReal.coe_ofNat] at hD
    calc
      _ ≤ dist (f x) (f z) + dist (f z) (g y) := dist_triangle _ _ _
      _ ≤ 4 * dist x z + 4 * dist z y := add_le_add
        (by rw [hf.dist_eq]; exact le_mul_of_one_le_left dist_nonneg (by norm_num)) hD
      _ = _ := by rw [hxz, hzy]; ring
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [NNReal.coe_ofNat]
  have hx₂ := mem_closedBall_zero_iff.1 hx
  have hy₂ := mem_closedBall_zero_iff.1 hy
  by_cases hX : ‖x‖ ≤ R <;> by_cases hY : ‖y‖ ≤ R
  · change dist (terminalOrientedFace B s R H x) (terminalOrientedFace B s R H y) ≤ _
    rw [terminalOrientedFace, if_pos hX, terminalOrientedFace, if_pos hY]
    change dist (f x) (f y) ≤ _
    rw [hf.dist_eq]
    exact le_mul_of_one_le_left dist_nonneg (by norm_num)
  · exact hMix x y hX (lt_of_not_ge hY) hy₂
  · rw [dist_comm (terminalOrientedFace B s R H x), dist_comm x y]
    exact hMix y x hY (lt_of_not_ge hX) hx₂
  · rw [terminalOrientedFace, if_neg hX, terminalOrientedFace, if_neg hY]
    exact hg.dist_le_mul x ⟨(lt_of_not_ge hX).le, hx₂⟩ y ⟨(lt_of_not_ge hY).le, hy₂⟩

private def terminalAxisChartHomeomorph (B : OrthonormalBasis (Fin 3) ℝ Point) : (Plane × ℝ) ≃ₜ Point where
  toFun := axisChart B
  invFun := cylinderRecoveryCoordinates B 0
  left_inv p := by simpa only [zero_add] using cylinderRecoveryCoordinates_axisChart B 0 p
  right_inv x := by simpa only [zero_add] using axisChart_cylinderRecoveryCoordinates B 0 x
  continuous_toFun := continuous_axisChart B
  continuous_invFun := (contDiff_cylinderKernelCoordinates B 0).continuous

private def terminalHalfChartInverse (B : OrthonormalBasis (Fin 3) ℝ Point) (s R H : ℝ) (p : Point) : Point :=
  let y := (cylinderRecoveryCoordinates B 0 p).1
  let t := (cylinderRecoveryCoordinates B 0 p).2
  (t / R) • NormedSpace.normalize (terminalOrientedFace B s R H y)

private theorem terminalHalfChartInverse_lipschitzOn
    (B : OrthonormalBasis (Fin 3) ℝ Point) {s R H : ℝ}
    (hs : |s| = 1) (hR : 0 < R) (hLow : R/4 ≤ H) (hHigh : H ≤ R) :
    LipschitzOnWith (Real.toNNReal (65 / R)) (terminalHalfChartInverse B s R H)
      (axisChart B '' (closedBall (0 : Plane) (2 * R) ×ˢ Icc (R / 2) (2 * R))) := by
  have hH := (div_pos hR (by norm_num : (0 : ℝ) < 4)).trans_le hLow
  let g := terminalOrientedFace B s R H
  have hg := terminalOrientedFace_lipschitzOn B hs hR hH hHigh
  apply LipschitzOnWith.of_dist_le_mul
  rintro _ ⟨⟨y,t⟩, hy, rfl⟩ _ ⟨⟨z,u⟩, hz, rfl⟩
  have hyB : y ∈ closedBall (0 : Plane) (2 * R) := hy.1
  have hzB : z ∈ closedBall (0 : Plane) (2 * R) := hz.1
  have ht : t ∈ Icc (R/2) (2*R) := hy.2
  have hu : u ∈ Icc (R/2) (2*R) := hz.2
  have hC (p : Plane × ℝ) : cylinderRecoveryCoordinates B 0 (axisChart B p) = p := by
    simpa only [zero_add] using cylinderRecoveryCoordinates_axisChart B 0 p
  unfold terminalHalfChartInverse
  rw [hC, hC, Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm, ← axisChart_pair_sub]
  change ‖(t/R) • NormedSpace.normalize (g y) - (u/R) • NormedSpace.normalize (g z)‖ ≤ _
  have hnY := terminalOrientedFace_norm_lower B hs hR hH hHigh y
  have hnZ := terminalOrientedFace_norm_lower B hs hR hH hHigh z
  have hNz : ‖NormedSpace.normalize (g z)‖ = 1 := NormedSpace.norm_normalize
    (norm_pos_iff.mp (hH.trans_le hnZ))
  have hR4 := div_pos hR (by norm_num : (0 : ℝ) < 4)
  have hN := norm_normalize_sub_le_of_radius hR4 (hLow.trans hnY) (hLow.trans hnZ)
  have hG : ‖g y - g z‖ ≤ 4 * ‖y-z‖ := by
    simpa only [dist_eq_norm, NNReal.coe_ofNat] using hg.dist_le_mul y hyB z hzB
  have hN' := hN.trans (mul_le_mul_of_nonneg_left hG (by positivity))
  have hT : |t/R| ≤ 2 := by
    rw [abs_of_nonneg (div_nonneg ((half_pos hR).le.trans ht.1) hR.le)]
    exact (div_le_iff₀ hR).2 ht.2
  have hulim : |t/R - u/R| ≤ R⁻¹ * ‖axisChart B (y-z,t-u)‖ := by
    rw [← sub_div, abs_div, abs_of_nonneg hR.le, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_axisChart_height_lower B _ _) (inv_nonneg.mpr hR.le)
  have hN'' : ‖NormedSpace.normalize (g y) - NormedSpace.normalize (g z)‖ ≤
      (32 / R) * ‖axisChart B (y-z,t-u)‖ := by
    refine hN'.trans ?_
    have hEq : 2 * (R / 4)⁻¹ * (4 * ‖y-z‖) = (32 / R) * ‖y-z‖ := by
      field_simp
      ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_left (norm_axisChart_transverse_lower B _ _) (by positivity)
  calc
    _ ≤ |t/R| * ‖NormedSpace.normalize (g y) - NormedSpace.normalize (g z)‖ +
        |t/R-u/R| * ‖NormedSpace.normalize (g z)‖ :=
      norm_scaled_difference_le _ _ _ _
    _ ≤ 2 * ((32 / R) * ‖axisChart B (y-z,t-u)‖) + R⁻¹ * ‖axisChart B (y-z,t-u)‖ := by
      rw [hNz, mul_one]
      exact add_le_add (mul_le_mul hT hN'' (norm_nonneg _) (by norm_num)) hulim
    _ = _ := by ring

/-- Inverse radial coordinates recover the original point of the round shell. -/
private theorem terminalHalfChartInverse_reconstruct
    (B : OrthonormalBasis (Fin 3) ℝ Point) {s R H : ℝ}
    (hs : |s| = 1) (hR : 0 < R) (hH : 0 < H) (hk : 1 ≤ R / H)
    {x : Point} (hx : x ∈ (terminalHalfShell B s (R / H)).val) :
    terminalHalfChartInverse B s R H (axisChart B (terminalHalfParameter B s (R / H) R x, R * ‖x‖)) = x := by
  have h := terminalHalfParameter_reconstruct B hs hR hH hk hx
  have hxPos : 0 < ‖x‖ := (by norm_num : (0 : ℝ) < 1/2).trans hx.1.1
  have hC : cylinderRecoveryCoordinates B 0
      (axisChart B (terminalHalfParameter B s (R / H) R x, R * ‖x‖)) =
        (terminalHalfParameter B s (R / H) R x, R * ‖x‖) := by
    simpa only [zero_add] using cylinderRecoveryCoordinates_axisChart B 0
      (terminalHalfParameter B s (R / H) R x, R * ‖x‖)
  unfold terminalHalfChartInverse
  rw [hC]
  dsimp only [Prod.fst, Prod.snd]
  rw [h.2.2, NormedSpace.normalize_smul_of_pos (div_pos hR h.1), NormedSpace.normalize, smul_smul]
  have hr : (R * ‖x‖) / R * ‖x‖⁻¹ = 1 := by
    field_simp
  rw [hr, one_smul]

/-- The physical half chart on the round annulus pushes volume into the
original disk with uniform distortion proportional to the inverse square radius. -/
theorem map_terminalHalfParameter_volume_le (B : OrthonormalBasis (Fin 3) ℝ Point)
    {s R H : ℝ} (hs : |s| = 1) (hR : 0 < R) (hLow : R/4 ≤ H) (hHigh : H ≤ R) :
    Measure.map (terminalHalfParameter B s (R/H) R)
      (volume.restrict (terminalHalfShell B s (R/H)).val) ≤
        ENNReal.ofReal (549250 / R ^ 2) • volume.restrict (ball (0 : Plane) (2*R)) := by
  let P := terminalHalfParameter B s (R/H) R
  let Q := terminalHalfChartInverse B s R H
  let V := (terminalHalfShell B s (R/H)).val
  let W := closedBall (0 : Plane) (2*R) ×ˢ Icc (R/2) (2*R)
  let K : ℝ≥0 := Real.toNNReal (65 / R)
  have hH := (div_pos hR (by norm_num : (0 : ℝ) < 4)).trans_le hLow
  have hk : 1 ≤ R / H := (one_le_div₀ hH).2 hHigh
  have hk₄ : R / H ≤ 4 := (div_le_iff₀ hH).2 (by linarith only [hLow])
  have hP := (terminalHalfParameter_lipschitz B hs (div_nonneg hR.le hH.le) hk₄ hR).continuous.measurable
  have hQ : LipschitzOnWith K Q (axisChart B '' W) := terminalHalfChartInverse_lipschitzOn B hs hR hLow hHigh
  apply Measure.le_iff.2
  intro A hA
  rw [Measure.map_apply hP hA, Measure.restrict_apply (hP hA), Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hA]
  let S := A ∩ ball (0 : Plane) (2*R)
  let I := Icc (R/2) (2*R)
  let E := axisChart B '' (S ×ˢ I)
  have hIn : P ⁻¹' A ∩ V ⊆ Q '' E := by
    rintro x ⟨hxA,hxV⟩
    have h := terminalHalfParameter_reconstruct B hs hR hH hk hxV
    have hxN : ‖x‖ ∈ Ioo (1/2 : ℝ) 2 := hxV.1
    have hT : R * ‖x‖ ∈ I := by
      have hxL := mul_le_mul_of_nonneg_left hxN.1.le hR.le
      have hxU := mul_le_mul_of_nonneg_left hxN.2.le hR.le
      unfold I
      constructor <;> linarith only [hxL, hxU]
    refine ⟨axisChart B (P x, R * ‖x‖), ⟨(P x, R*‖x‖), ⟨⟨hxA, h.2.1⟩, hT⟩, rfl⟩, ?_⟩
    exact terminalHalfChartInverse_reconstruct B hs hR hH hk hxV
  have hEsub : E ⊆ axisChart B '' W := image_mono (prod_mono
    (inter_subset_right.trans ball_subset_closedBall) (Subset.rfl))
  have hQmeasure := euclideanHausdorff_lipschitzOn_image_le_volume hQ hEsub
  have hVol : (Measure.euclideanHausdorffMeasure 3 : Measure Point) = volume := by
    simpa only [finrank_euclideanSpace_fin] using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Point))
  rw [finrank_euclideanSpace_fin, hVol] at hQmeasure
  have hProd : (volume : Measure Point) E = ((volume : Measure Plane).prod (volume : Measure ℝ)) (S ×ˢ I) := by
    have hEmb : MeasurableEmbedding (axisChart B) := (terminalAxisChartHomeomorph B).toMeasurableEquiv.measurableEmbedding
    change (volume : Measure Point) (axisChart B '' (S ×ˢ I)) = _
    rw [← (measurePreserving_axisChart B).map_eq,
      Measure.map_apply hEmb.measurable (hEmb.measurableSet_image.mpr ((hA.inter measurableSet_ball).prod measurableSet_Icc)),
      hEmb.injective.preimage_image]
  have hIvol : (volume : Measure ℝ) I ≤ ENNReal.ofReal (2 * R) := by
    rw [show I = Icc (R/2) (2*R) from rfl, Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hR])
  have hScale : (K : ℝ≥0∞) ^ 3 * ENNReal.ofReal (2*R) = ENNReal.ofReal (549250 / R^2) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow K.coe_nonneg,
      ← ENNReal.ofReal_mul (by positivity), show (K : ℝ) = 65/R from Real.coe_toNNReal _ (by positivity)]
    congr 1
    field_simp
    ring
  calc
    _ ≤ (volume : Measure Point) (Q '' E) := measure_mono hIn
    _ ≤ (K : ℝ≥0∞) ^ 3 * (volume : Measure Point) E := hQmeasure
    _ = (K : ℝ≥0∞) ^ 3 * ((volume : Measure Plane) S * (volume : Measure ℝ) I) := by
      rw [hProd, Measure.prod_prod]
    _ ≤ (K : ℝ≥0∞) ^ 3 * ((volume : Measure Plane) S * ENNReal.ofReal (2*R)) := by gcongr
    _ = _ := by rw [mul_comm ((volume : Measure Plane) S), ← mul_assoc, hScale]

end Thesis.MeasureGeometry

end
