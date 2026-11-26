module

public import Thesis.Interpolation.CylinderCapSurface
import Thesis.Interpolation.CylinderBoundaryMeasure
import HarmonicMaps.Analysis.EuclideanHausdorffLipschitz

/-! Uniform area domination from the three actual planar terminal face charts. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Thesis.MeasureGeometry

/-- Normalization is quantitatively Lipschitz away from the origin. -/
theorem norm_normalize_sub_le_of_radius {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) {x y : E} (hx : R ≤ ‖x‖) (hy : R ≤ ‖y‖) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * R⁻¹ * ‖x - y‖ := by
  have hx₀ : 0 < ‖x‖ := hR.trans_le hx
  have hy₀ : 0 < ‖y‖ := hR.trans_le hy
  have hEq : NormedSpace.normalize x - NormedSpace.normalize y =
      ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by
    rw [NormedSpace.normalize, NormedSpace.normalize, sub_smul, smul_sub]
    abel
  rw [hEq]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hx₀.le), Real.norm_eq_abs,
    inv_sub_inv hx₀.ne' hy₀.ne', abs_div, abs_of_pos (mul_pos hx₀ hy₀)]
  have hCancel : |‖y‖ - ‖x‖| / (‖x‖ * ‖y‖) * ‖y‖ = ‖x‖⁻¹ * |‖x‖ - ‖y‖| := by
    rw [abs_sub_comm ‖y‖ ‖x‖]
    field_simp
  rw [hCancel]
  calc
    _ ≤ ‖x‖⁻¹ * ‖x - y‖ + ‖x‖⁻¹ * ‖x - y‖ :=
      add_le_add_right (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (inv_nonneg.mpr hx₀.le)) _
    _ = 2 * ‖x‖⁻¹ * ‖x - y‖ := by ring
    _ ≤ _ := by gcongr

/-- The physical wall parameterization has one scale-independent bound on
its literal closed annulus. -/
theorem terminalWallChart_lipschitzOn_closedCollar
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hH : 0 ≤ H) (hHigh : H ≤ R) :
    LipschitzOnWith 4 (terminalWallChart B c R H) (closedPlanarRadialCollar R (2 * R)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let a : ℝ := 2 * H / R
  have ha₀ : 0 ≤ a := div_nonneg (mul_nonneg zero_le_two hH) hR.le
  have ha₂ : a ≤ 2 := (div_le_iff₀ hR).2 (mul_le_mul_of_nonneg_left hHigh zero_le_two)
  have hN := mul_le_mul_of_nonneg_left
    (norm_normalize_sub_le_of_radius hR (show R ≤ ‖x‖ from hx.1) (show R ≤ ‖y‖ from hy.1)) hR.le
  have hSc : R * (2 * R⁻¹ * ‖x - y‖) = 2 * ‖x - y‖ := by field_simp
  rw [hSc] at hN
  have hEq : terminalWallChart B c R H x - terminalWallChart B c R H y =
      axisChartPlane B (R • (NormedSpace.normalize x - NormedSpace.normalize y)) +
        (a * (‖x‖ - ‖y‖)) • B 2 := by
    unfold terminalWallChart
    rw [axisChart_add_axis B (R • NormedSpace.normalize x) (2 * H / R * (‖x‖ - R) - H),
      axisChart_add_axis B (R • NormedSpace.normalize y) (2 * H / R * (‖y‖ - R) - H),
      ← axisChartPlane_apply, ← axisChartPlane_apply]
    have hLin : axisChartPlane B (R • (NormedSpace.normalize x - NormedSpace.normalize y)) =
        axisChartPlane B (R • NormedSpace.normalize x) -
          axisChartPlane B (R • NormedSpace.normalize y) := by
      rw [smul_sub, map_sub]
    have hT : a * (‖x‖ - ‖y‖) =
        (2 * H / R * (‖x‖ - R) - H) - (2 * H / R * (‖y‖ - R) - H) := by dsimp [a]; ring
    rw [add_sub_add_left_eq_sub, add_sub_add_comm, ← sub_smul, ← hLin, ← hT]
  rw [dist_eq_norm, hEq, dist_eq_norm]
  apply (norm_add_le _ _).trans
  rw [norm_axisChartPlane, norm_smul, norm_smul, Real.norm_of_nonneg hR.le,
    B.orthonormal.norm_eq_one, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg ha₀]
  have hz : a * |‖x‖ - ‖y‖| ≤ 2 * ‖x - y‖ :=
    mul_le_mul ha₂ (abs_norm_sub_norm_le x y) (abs_nonneg _) zero_le_two
  have hAdd := add_le_add hN hz
  norm_num at *
  linarith only [hAdd]

private theorem terminalDiskChart_isometry (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (z : ℝ) :
    Isometry (fun y : Plane => c + axisChart B (y, z)) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_add_left, axisChart_add_axis B x z, axisChart_add_axis B y z,
    ← axisChartPlane_apply, ← axisChartPlane_apply, dist_add_right, dist_eq_norm,
    dist_eq_norm, ← map_sub, norm_axisChartPlane]

private theorem mem_terminal_frontier_of_closedCoordinates
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R H : ℝ} (hR : 0 < R) (hH : 0 < H)
    {y : Plane} {z : ℝ} (hy : y ∈ closedBall (0 : Plane) R) (hz : z ∈ Icc (-H) H)
    (hf : y ∉ ball (0 : Plane) R ∨ z ∉ Ioo (-H) H) :
    c + axisChart B (y, z) ∈ frontier (terminalCylinderCap (B 2) c R H) :=
  physical_cylinder_frontier_of_parameter B c hR (lt_trans (neg_lt_zero.mpr hH) hH) hy hz hf

private theorem terminalWallChart_mem_frontier
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R H : ℝ} (hR : 0 < R) (hH : 0 < H)
    {y : Plane} (hy : y ∈ closedPlanarRadialCollar R (2 * R)) :
    terminalWallChart B c R H y ∈ frontier (terminalCylinderCap (B 2) c R H) := by
  let z := (2 * H / R) * (‖y‖ - R) - H
  have hN : ‖R • NormedSpace.normalize y‖ = R := by
    rw [norm_smul, NormedSpace.norm_normalize (norm_pos_iff.mp (hR.trans_le hy.1)),
      Real.norm_of_nonneg hR.le, mul_one]
  have hs : 0 ≤ 2 * H / R := by positivity
  have h₁ : -H ≤ z := by
    dsimp only [z]
    have := mul_nonneg hs (sub_nonneg.2 hy.1)
    linarith only [this]
  have h₂ : z ≤ H := by
    have h := mul_le_mul_of_nonneg_left
      (show ‖y‖ - R ≤ R by linarith only [hy.2]) hs
    rw [div_mul_cancel₀ _ hR.ne'] at h
    dsimp only [z]
    linarith only [h]
  apply mem_terminal_frontier_of_closedCoordinates B c hR hH (mem_closedBall_zero_iff.2 hN.le)
    ⟨h₁, h₂⟩
  exact Or.inl (fun h => (mem_ball_zero_iff.1 h).ne hN)

private theorem terminalClosedFaces_cover_frontier
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R)
    {x : Point} (hx : x ∈ frontier (terminalCylinderCap (B 2) c R H)) :
    (∃ y ∈ closedBall (0 : Plane) R, c + axisChart B (y, -H) = x) ∨
    (∃ y ∈ closedBall (0 : Plane) R, c + axisChart B (y, H) = x) ∨
    (∃ y ∈ closedPlanarRadialCollar R (2 * R), terminalWallChart B c R H y = x) := by
  let e := B 2
  have he : ‖e‖ = 1 := B.orthonormal.norm_eq_one 2
  have hH : 0 < H := (div_pos hR (by norm_num : (0 : ℝ) < 4)).trans_le hLow
  let yz := cylinderRecoveryCoordinates B c x
  let y := yz.1
  let z := yz.2
  have heq : c + axisChart B (y, z) = x := axisChart_cylinderRecoveryCoordinates B c x
  have hChart : ‖terminalCylinderBallChart he c hR hLow hHigh x‖ = R := by
    rw [terminalCylinderCap_frontier_eq_preimage_sphere he c hR hLow hHigh] at hx
    exact mem_sphere_zero_iff_norm.1 hx
  rw [terminalCylinderBallChart_norm, ← heq, add_sub_cancel_left, cylinderCapGauge,
    cylinderTransverseRadius_axisChart, cylinderHeight_axisChart] at hChart
  have hy : ‖y‖ ≤ R := hChart ▸ le_max_left _ _
  have hZH : |z| ≤ H := by
    have hK : (R / H) * |z| ≤ R :=
      (le_max_right ‖y‖ ((R / H) * |z|)).trans_eq hChart
    have h : (R / H) * |z| ≤ (R / H) * H :=
      hK.trans_eq (div_mul_cancel₀ _ hH.ne').symm
    exact (mul_le_mul_iff_right₀ (div_pos hR hH)).1 h
  have hZ := abs_le.mp hZH
  by_cases h₁ : z = -H
  · exact Or.inl ⟨y, mem_closedBall_zero_iff.2 hy, h₁ ▸ heq⟩
  by_cases h₂ : z = H
  · exact Or.inr (Or.inl ⟨y, mem_closedBall_zero_iff.2 hy, h₂ ▸ heq⟩)
  have hz : z ∈ Ioo (-H) H := ⟨lt_of_le_of_ne hZ.1 (Ne.symm h₁), lt_of_le_of_ne hZ.2 h₂⟩
  have hz' : (R / H) * |z| < R :=
    (mul_lt_mul_of_pos_left (abs_lt.mpr hz) (div_pos hR hH)).trans_eq (div_mul_cancel₀ _ hH.ne')
  have hyR : ‖y‖ = R := by
    by_contra h
    exact (max_lt_iff.mpr ⟨lt_of_le_of_ne hy h, hz'⟩).ne hChart
  let ρ := terminalWallParameterRadius R H z
  have hρ : ρ ∈ Icc R (2 * R) := by
    have h t (ht : 0 ≤ t) : 0 ≤ R / (2 * H) * t :=
      mul_nonneg (div_nonneg hR.le (by positivity)) ht
    have hZs := h (z + H) (by linarith only [hz.1])
    have hZt := h (H - z) (by linarith only [hz.2])
    have hRmul : R / (2 * H) * (2 * H) = R := div_mul_cancel₀ _ (by positivity)
    have hFrac : ρ = R + R / (2 * H) * (z + H) := by
      unfold ρ terminalWallParameterRadius
      ring
    rw [hFrac]
    refine ⟨le_add_of_nonneg_right hZs, ?_⟩
    linarith only [hZt, hRmul]
  let y' := ρ • NormedSpace.normalize y
  have hy₀ : y ≠ 0 := norm_pos_iff.1 (hyR.symm ▸ hR)
  have hρ₀ : 0 < ρ := hR.trans_le hρ.1
  have hy' : ‖y'‖ = ρ := by
    rw [show y' = ρ • NormedSpace.normalize y from rfl, norm_smul, Real.norm_of_nonneg hρ₀.le,
      NormedSpace.norm_normalize hy₀, mul_one]
  have hNorm : R • NormedSpace.normalize y' = y := by
    rw [show y' = ρ • NormedSpace.normalize y from rfl, NormedSpace.normalize_smul_of_pos hρ₀,
      NormedSpace.normalize_eq_self_of_norm_eq_one (NormedSpace.norm_normalize hy₀),
      NormedSpace.normalize, hyR, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hZ' : (2 * H / R) * (ρ - R) - H = z := by
    unfold ρ terminalWallParameterRadius
    field_simp
    ring
  exact Or.inr (Or.inr ⟨y', by
    change ‖y'‖ ∈ Icc R (2 * R)
    rwa [hy'], by rw [terminalWallChart, hNorm, hy', hZ', heq]⟩)

private theorem terminalFace_direction_measure
    {F : Point ≃ₜ Point} (hF : LipschitzWith 12 (F : Point → Point))
    {R : ℝ} (hR : 0 < R) {f : Plane → Point} (hf : Measurable f)
    {V : Set Plane} (hLip : LipschitzOnWith 4 f V)
    (hSphere : ∀ y ∈ V, F (f y) ∈ sphere (0 : Point) R) :
    let θ := cylinderBoundaryDirection F ∘ f
    ∀ A : Set UnitTensorSphere, MeasurableSet A →
      tensorSphereMeasure (θ '' (θ ⁻¹' A ∩ V)) ≤ ENNReal.ofReal (2304 / R ^ 2) *
        Measure.map θ (volume.restrict V) A := by
  intro θ A hA
  have hθ : Measurable θ := (measurable_cylinderBoundaryDirection F).comp hf
  have hθR (y : Plane) (hy : y ∈ V) : R • (θ y).val = F (f y) := by
    have h := congrArg F (cylinderBoundaryDirection_reconstruct hR (hSphere y hy))
    rwa [F.apply_symm_apply] at h
  have hθEq (y : Plane) (hy : y ∈ V) : (θ y).val = R⁻¹ • F (f y) := by
    rw [← hθR y hy, inv_smul_smul₀ hR.ne']
  let L : ℝ≥0 := Real.toNNReal (48 / R)
  have hL : (L : ℝ) = 48 / R := Real.coe_toNNReal _ (by positivity)
  have hLipθ : LipschitzOnWith L θ V := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change dist (θ x).val (θ y).val ≤ _
    rw [hθEq x hx, hθEq y hy, hL, dist_eq_norm, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hR.le), ← dist_eq_norm]
    have hDistF := (hF.dist_le_mul (f x) (f y)).trans
      (mul_le_mul_of_nonneg_left (hLip.dist_le_mul x hx y hy) (by norm_num))
    refine (mul_le_mul_of_nonneg_left hDistF (inv_nonneg.mpr hR.le)).trans_eq ?_
    push_cast
    ring
  have hImage := euclideanHausdorff_lipschitzOn_image_le_volume hLipθ
    (inter_subset_right : θ ⁻¹' A ∩ V ⊆ V)
  simp only [finrank_euclideanSpace_fin] at hImage
  have hMap : volume (θ ⁻¹' A ∩ V) = Measure.map θ (volume.restrict V) A := by
    rw [Measure.map_apply hθ hA, Measure.restrict_apply (hθ hA)]
  have hScale : (L : ℝ≥0∞) ^ 2 = ENNReal.ofReal (2304 / R ^ 2) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow L.coe_nonneg, hL]
    congr 1
    ring
  rw [hScale, hMap] at hImage
  exact hImage

private theorem ae_planar_norm_ne (r : ℝ) : ∀ᵐ y : Plane ∂volume, ‖y‖ ≠ r := by
  rw [ae_iff]
  simpa only [not_not, ← mem_sphere_zero_iff_norm, setOf_mem_eq] using
    (Measure.addHaar_sphere volume (0 : Plane) r)

private theorem restrict_closedDisk_eq (R : ℝ) :
    (volume : Measure Plane).restrict (closedBall 0 R) = volume.restrict (ball 0 R) := by
  apply Measure.restrict_congr_set
  filter_upwards [ae_planar_norm_ne R] with y hy
  change (y ∈ closedBall (0 : Plane) R) = (y ∈ ball (0 : Plane) R)
  simp only [mem_closedBall_zero_iff, mem_ball_zero_iff]
  exact propext ⟨fun h => lt_of_le_of_ne h hy, le_of_lt⟩

private theorem restrict_closedWallAnnulus_eq (R : ℝ) :
    (volume : Measure Plane).restrict (closedPlanarRadialCollar R (2 * R)) =
      volume.restrict (terminalWallAnnulus R).val := by
  apply Measure.restrict_congr_set
  filter_upwards [ae_planar_norm_ne R, ae_planar_norm_ne (2 * R)] with y hy₁ hy₂
  change (‖y‖ ∈ Icc R (2 * R)) = (‖y‖ ∈ Ioo R (2 * R))
  exact propext ⟨fun h => ⟨lt_of_le_of_ne h.1 hy₁.symm, lt_of_le_of_ne h.2 hy₂⟩,
    fun h => Ioo_subset_Icc_self h⟩

private theorem terminal_face_measure_domination
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R) :
    let F := terminalCylinderBallChart (B.orthonormal.norm_eq_one 2) c hR hLow hHigh
    let L := cylinderBoundaryDirection F ∘ (fun y : Plane => c + axisChart B (y, -H))
    let U := cylinderBoundaryDirection F ∘ (fun y : Plane => c + axisChart B (y, H))
    let W := cylinderBoundaryDirection F ∘ terminalWallChart B c R H
    let μ := (volume : Measure Plane).restrict (closedBall 0 R)
    let ν := (volume : Measure Plane).restrict (closedPlanarRadialCollar R (2 * R))
    tensorSphereMeasure ≤ ENNReal.ofReal (2304 / R ^ 2) •
      (Measure.map L μ + Measure.map U μ + Measure.map W ν) := by
  intro F L U W μ ν
  let C := ENNReal.ofReal (2304 / R ^ 2)
  let V := closedBall (0 : Plane) R
  let Q := closedPlanarRadialCollar R (2 * R)
  let f (z : ℝ) (y : Plane) := c + axisChart B (y, z)
  let g := terminalWallChart B c R H
  have hH : 0 < H := (div_pos hR (by norm_num : (0 : ℝ) < 4)).trans_le hLow
  have hFront := terminalCylinderCap_frontier_eq_preimage_sphere (B.orthonormal.norm_eq_one 2) c hR hLow hHigh
  have hLipF : LipschitzWith 12 (F : Point → Point) :=
    lipschitz_terminalCylinderBallChart _ c hR hLow hHigh
  have hLipDisk (z : ℝ) : LipschitzOnWith 4 (f z) V :=
    ((terminalDiskChart_isometry B c z).lipschitz.weaken (by norm_num : (1 : ℝ≥0) ≤ 4)).lipschitzOnWith
  have hLipWall : LipschitzOnWith 4 g Q := terminalWallChart_lipschitzOn_closedCollar B c hR hH.le hHigh
  have hf (z : ℝ) : Measurable (f z) := (terminalDiskChart_isometry B c z).continuous.measurable
  have hg : Measurable g := by
    have hN : Measurable (fun y : Plane => NormedSpace.normalize y) := measurable_norm.inv.smul measurable_id
    have hP : Measurable (fun y : Plane => R • NormedSpace.normalize y) := hN.const_smul R
    have hZ : Measurable (fun y : Plane => (2 * H / R) * (‖y‖ - R) - H) :=
      (measurable_const.mul (measurable_norm.sub measurable_const)).sub measurable_const
    exact measurable_const.add ((continuous_axisChart B).measurable.comp (hP.prodMk hZ))
  have hSphereAt (z : ℝ) (hz : z = -H ∨ z = H) (y : Plane) (hy : y ∈ V) : F (f z y) ∈ sphere 0 R := by
    have hAt : f z y ∈ frontier (terminalCylinderCap (B 2) c R H) := by
      apply mem_terminal_frontier_of_closedCoordinates B c hR hH hy
      · rcases hz with hz | hz <;> rw [hz] <;> exact ⟨by linarith only [hH], by linarith only [hH]⟩
      · right
        rintro ⟨hlo, hhi⟩
        rcases hz with hz | hz
        · exact hlo.ne hz.symm
        · exact hhi.ne hz
    rwa [hFront] at hAt
  have hSphereWall (y : Plane) (hy : y ∈ Q) : F (g y) ∈ sphere 0 R := by
    have hAt := terminalWallChart_mem_frontier B c hR hH hy
    rwa [hFront] at hAt
  apply Measure.le_iff.2
  intro A hA
  let I := L '' (L ⁻¹' A ∩ V)
  let J := U '' (U ⁻¹' A ∩ V)
  let K := W '' (W ⁻¹' A ∩ Q)
  have hCover : A ⊆ I ∪ J ∪ K := by
    intro θ hθ
    let x := F.symm (R • θ.val)
    have hxF : F x = R • θ.val := F.apply_symm_apply _
    have hFθ : F x ∈ sphere (0 : Point) R := by
      rw [hxF, mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg hR.le,
        mem_sphere_zero_iff_norm.mp θ.property, mul_one]
    have hx : x ∈ frontier (terminalCylinderCap (B 2) c R H) := by rw [hFront]; exact hFθ
    have hDir : cylinderBoundaryDirection F x = θ := by
      have h := congrArg F (cylinderBoundaryDirection_reconstruct hR hFθ)
      rw [F.apply_symm_apply, hxF] at h
      exact Subtype.ext (smul_right_injective Point hR.ne' h)
    rcases terminalClosedFaces_cover_frontier B c hR hLow hHigh hx with h | h | h
    · obtain ⟨y, hy, hxy⟩ := h
      have h : L y = θ := (congrArg (cylinderBoundaryDirection F) hxy).trans hDir
      exact Or.inl (Or.inl ⟨y, ⟨show L y ∈ A by rwa [h], hy⟩, h⟩)
    · obtain ⟨y, hy, hxy⟩ := h
      have h : U y = θ := (congrArg (cylinderBoundaryDirection F) hxy).trans hDir
      exact Or.inl (Or.inr ⟨y, ⟨show U y ∈ A by rwa [h], hy⟩, h⟩)
    · obtain ⟨y, hy, hxy⟩ := h
      have h : W y = θ := (congrArg (cylinderBoundaryDirection F) hxy).trans hDir
      exact Or.inr ⟨y, ⟨show W y ∈ A by rwa [h], hy⟩, h⟩
  have hLower : tensorSphereMeasure I ≤ C * Measure.map L μ A :=
    terminalFace_direction_measure hLipF hR (hf (-H)) (hLipDisk (-H))
      (hSphereAt (-H) (Or.inl rfl)) A hA
  have hUpper : tensorSphereMeasure J ≤ C * Measure.map U μ A :=
    terminalFace_direction_measure hLipF hR (hf H) (hLipDisk H)
      (hSphereAt H (Or.inr rfl)) A hA
  have hWall : tensorSphereMeasure K ≤ C * Measure.map W ν A :=
    terminalFace_direction_measure hLipF hR hg hLipWall hSphereWall A hA
  calc
    _ ≤ tensorSphereMeasure (I ∪ J ∪ K) := measure_mono hCover
    _ ≤ (tensorSphereMeasure I + tensorSphereMeasure J) + tensorSphereMeasure K :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ C * Measure.map L μ A + C * Measure.map U μ A + C * Measure.map W ν A :=
      add_le_add (add_le_add hLower hUpper) hWall
    _ = _ := by simp only [C, Measure.smul_apply, Measure.add_apply, smul_eq_mul, mul_add]

private theorem terminalWallValue_lintegral_le {q : ℕ} {R H : ℝ}
    (hR : 0 < R) (hLow : R / 4 ≤ H) (D : TerminalCylinderBoundaryData q R hR)
    (φ : Ambient q → ℝ≥0∞) :
    (∫⁻ y in (terminalWallAnnulus R).val, φ (D.wall y)) ≤
      4 * ∫⁻ y in (terminalWallAnnulus R).val, ENNReal.ofReal (2 * H / ‖y‖) * φ (D.wall y) := by
  rw [← lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (terminalWallAnnulus R).property.measurableSet] with y hy
  have hY : ‖y‖ ∈ Ioo R (2 * R) := hy
  have hA : (1 / 4 : ℝ) ≤ 2 * H / ‖y‖ := by
    apply (le_div_iff₀ (hR.trans hY.1)).2
    linarith only [hY.2, hLow]
  rw [← mul_assoc]
  exact le_mul_of_one_le_left (zero_le) (by
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.one_le_ofReal.mpr (by linarith only [hA]))

/-- The original weighted face measure dominates all nonnegative value
integrals on the uniformly charted sphere. -/
theorem terminalSphereValue_lintegral_le {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    {R H : ℝ} (hR : 0 < R) (hLow : R / 4 ≤ H) (hHigh : H ≤ R)
    (D : TerminalCylinderBoundaryData q R hR) (φ : Ambient q → ℝ≥0∞) :
    let F := terminalCylinderBallChart (B.orthonormal.norm_eq_one 2) c hR hLow hHigh
    let b (θ : UnitTensorSphere) := terminalCylinderSurfaceValue B c H D (F.symm (R • θ.val))
    (∫⁻ θ, φ (b θ) ∂tensorSphereMeasure) ≤
      ENNReal.ofReal (9216 / R ^ 2) * terminalCylinderSurfaceValueIntegral H D φ := by
  intro F b
  let L := cylinderBoundaryDirection F ∘ (fun y : Plane => c + axisChart B (y, -H))
  let U := cylinderBoundaryDirection F ∘ (fun y : Plane => c + axisChart B (y, H))
  let W := cylinderBoundaryDirection F ∘ terminalWallChart B c R H
  let μ := (volume : Measure Plane).restrict (closedBall 0 R)
  let ν := (volume : Measure Plane).restrict (closedPlanarRadialCollar R (2 * R))
  let C := ENNReal.ofReal (2304 / R ^ 2)
  have hDom : tensorSphereMeasure ≤ C • (Measure.map L μ + Measure.map U μ + Measure.map W ν) :=
    terminal_face_measure_domination B c hR hLow hHigh
  have hH : 0 < H := (div_pos hR (by norm_num : (0 : ℝ) < 4)).trans_le hLow
  have hFront := terminalCylinderCap_frontier_eq_preimage_sphere (B.orthonormal.norm_eq_one 2) c hR hLow hHigh
  have hLower (y : Plane) (hy : y ∈ closedBall (0 : Plane) R) :
      b (L y) = D.lower y := by
    have hx := mem_terminal_frontier_of_closedCoordinates B c hR hH hy
      (z := -H) ⟨le_rfl, by linarith only [hH]⟩ (Or.inr fun hz => (lt_irrefl _ hz.1))
    rw [hFront] at hx
    dsimp only [b, L, Function.comp_apply]
    rw [cylinderBoundaryDirection_reconstruct hR hx, terminalCylinderSurfaceValue_lower]
  have hUpper (y : Plane) (hy : y ∈ closedBall (0 : Plane) R) :
      b (U y) = D.upper y := by
    have hx := mem_terminal_frontier_of_closedCoordinates B c hR hH hy
      (z := H) ⟨by linarith only [hH], le_rfl⟩ (Or.inr fun hz => (lt_irrefl _ hz.2))
    rw [hFront] at hx
    dsimp only [b, U, Function.comp_apply]
    rw [cylinderBoundaryDirection_reconstruct hR hx, terminalCylinderSurfaceValue_upper B c hH]
  have hWall (y : Plane) (hy : y ∈ (terminalWallAnnulus R).val) :
      b (W y) = D.wall y := by
    have hy' : y ∈ closedPlanarRadialCollar R (2 * R) := Ioo_subset_Icc_self (show ‖y‖ ∈ Ioo R (2 * R) from hy)
    have hx := terminalWallChart_mem_frontier B c hR hH hy'
    rw [hFront] at hx
    dsimp only [b, W, Function.comp_apply]
    rw [cylinderBoundaryDirection_reconstruct hR hx, terminalCylinderSurfaceValue_wall B c hH D hy]
  have hLval : (∫⁻ θ, φ (b θ) ∂Measure.map L μ) ≤ ∫⁻ y in ball (0 : Plane) R, φ (D.lower y) := by
    refine (lintegral_map_le (fun θ => φ (b θ)) L).trans_eq ?_
    change (∫⁻ y, φ (b (L y)) ∂μ) = _
    rw [lintegral_congr_ae ((ae_restrict_mem measurableSet_closedBall).mono
      (fun y hy => congrArg φ (hLower y hy))), restrict_closedDisk_eq R]
  have hUval : (∫⁻ θ, φ (b θ) ∂Measure.map U μ) ≤ ∫⁻ y in ball (0 : Plane) R, φ (D.upper y) := by
    refine (lintegral_map_le (fun θ => φ (b θ)) U).trans_eq ?_
    change (∫⁻ y, φ (b (U y)) ∂μ) = _
    rw [lintegral_congr_ae ((ae_restrict_mem measurableSet_closedBall).mono
      (fun y hy => congrArg φ (hUpper y hy))), restrict_closedDisk_eq R]
  have hWval : (∫⁻ θ, φ (b θ) ∂Measure.map W ν) ≤ ∫⁻ y in (terminalWallAnnulus R).val, φ (D.wall y) := by
    refine (lintegral_map_le (fun θ => φ (b θ)) W).trans_eq ?_
    change (∫⁻ y, φ (b (W y)) ∂ν) = _
    rw [show ν = volume.restrict (terminalWallAnnulus R).val from restrict_closedWallAnnulus_eq R]
    exact lintegral_congr_ae ((ae_restrict_mem (terminalWallAnnulus R).property.measurableSet).mono
      (fun y hy => congrArg φ (hWall y hy)))
  calc
    _ ≤ ∫⁻ θ, φ (b θ) ∂(C • (Measure.map L μ + Measure.map U μ + Measure.map W ν)) :=
      lintegral_mono' hDom (fun _ => le_rfl)
    _ ≤ (C * 4) * terminalCylinderSurfaceValueIntegral H D φ := by
      rw [lintegral_smul_measure, lintegral_add_measure, lintegral_add_measure, smul_eq_mul, mul_assoc]
      refine mul_le_mul_right ?_ C
      rw [terminalCylinderSurfaceValueIntegral, mul_add, mul_add]
      refine add_le_add (add_le_add (hLval.trans (le_mul_of_one_le_left zero_le (by norm_num)))
        (hUval.trans (le_mul_of_one_le_left zero_le (by norm_num)))) ?_
      exact hWval.trans (terminalWallValue_lintegral_le hR hLow D φ)
    _ = _ := by
      dsimp only [C]
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

end Thesis.MeasureGeometry

end
