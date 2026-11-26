module

public import Thesis.Interpolation.CylinderBoundaryTrace
import Thesis.Interpolation.CylinderRadialZeroExtension
import Thesis.Interpolation.QuaternionSphereSobolevLift
import StratificationTheory.Foundation.CylinderSurfaceProductMeasure
import StratificationTheory.Foundation.AngularL2Membership
import HarmonicMaps.Analysis.EuclideanHausdorffLipschitz

/-! Physical boundary measure bounds for the actual cylinder-to-ball chart. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal NNReal Topology

namespace Thesis.MeasureGeometry

private def cylinderBoundaryBase : UnitTensorSphere :=
  ⟨EuclideanSpace.single 0 1, mem_sphere_zero_iff_norm.2 (by simp)⟩

/-- The normalized spherical direction of the image of the physical boundary point. -/
def cylinderBoundaryDirection (F : Point ≃ₜ Point) (x : Point) : UnitTensorSphere :=
  sphereRadialDirection cylinderBoundaryBase (F x)

theorem measurable_cylinderBoundaryDirection (F : Point ≃ₜ Point) : Measurable (cylinderBoundaryDirection F) := by
  have hN : Measurable (fun y : Point => ‖y‖⁻¹ • y) := measurable_norm.inv.smul measurable_id
  have hA : MeasurableSet ({0}ᶜ : Set Point) := (measurableSet_singleton (0 : Point)).compl
  have hEq : (fun y : Point => (sphereRadialDirection cylinderBoundaryBase y).val) =
      ({0}ᶜ : Set Point).piecewise (fun y => ‖y‖⁻¹ • y) (fun _ => cylinderBoundaryBase.val) := by
    funext y
    by_cases hy : y = 0 <;> simp [sphereRadialDirection, NormedSpace.normalize, hy]
  have hVal : Measurable (fun y : Point => (sphereRadialDirection cylinderBoundaryBase y).val) := by
    rw [hEq]
    exact hN.piecewise hA measurable_const
  have hB : Measurable (fun y : Point => sphereRadialDirection cylinderBoundaryBase y) := hVal.subtype_mk
  change Measurable ((fun y : Point => sphereRadialDirection cylinderBoundaryBase y) ∘ F)
  exact hB.comp F.continuous.measurable

/-- At a true boundary point the normalized direction recovers the exact chart value. -/
theorem cylinderBoundaryDirection_reconstruct
    {F : Point ≃ₜ Point} {R : ℝ} (hR : 0 < R) {x : Point} (hx : F x ∈ sphere (0 : Point) R) :
    F.symm (R • (cylinderBoundaryDirection F x).val) = x := by
  have hN := mem_sphere_zero_iff_norm.mp hx
  have hn : F x ≠ 0 := norm_pos_iff.mp (hN.symm ▸ hR)
  change F.symm (R • (sphereRadialDirection cylinderBoundaryBase (F x)).val) = x
  rw [sphereRadialDirection, dif_pos hn]
  change F.symm (R • (‖F x‖⁻¹ • F x)) = x
  rw [hN, smul_smul, mul_inv_cancel₀ hR.ne', one_smul, F.symm_apply_apply]

private def cylinderBoundaryAxisHomeomorph (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) : (Plane × ℝ) ≃ₜ Point where
  toFun p := c + axisChart B p
  invFun x := cylinderRecoveryCoordinates B c x
  left_inv p := cylinderRecoveryCoordinates_axisChart B c p
  right_inv x := axisChart_cylinderRecoveryCoordinates B c x
  continuous_toFun := continuous_const.add (continuous_axisChart B)
  continuous_invFun := (contDiff_cylinderKernelCoordinates B c).continuous

/-- A boundary point of the original product disk and height interval
is sent to the actual physical cylinder frontier. -/
theorem physical_cylinder_frontier_of_parameter
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hR : 0 < R) (hI : lo < hi)
    {y : Plane} {z : ℝ} (hy : y ∈ closedBall (0 : Plane) R) (hz : z ∈ Icc lo hi)
    (hFace : y ∉ ball (0 : Plane) R ∨ z ∉ Ioo lo hi) :
    c + axisChart B (y, z) ∈ frontier (translatedAxisCylinder c (B 2) R lo hi) := by
  let T := cylinderBoundaryAxisHomeomorph B c
  have hU : translatedAxisCylinder c (B 2) R lo hi = T.symm ⁻¹' (ball (0 : Plane) R ×ˢ Ioo lo hi) :=
    translatedAxisCylinder_eq_recoveryCoordinates_preimage B c R lo hi
  rw [hU, ← T.symm.preimage_frontier]
  change T.symm (T (y, z)) ∈ frontier (ball (0 : Plane) R ×ˢ Ioo lo hi)
  rw [T.symm_apply_apply, frontier, (isOpen_ball.prod isOpen_Ioo).interior_eq, closure_prod_eq,
    closure_ball _ hR.ne', closure_Ioo hI.ne]
  exact ⟨⟨hy, hz⟩, fun hp => hFace.elim (fun h => h hp.1) (fun h => h hp.2)⟩

private theorem chart_image_frontier_mem_sphere {F : Point ≃ₜ Point} {R : ℝ} (hR : 0 < R)
    {U : Set Point} (hU : U = F ⁻¹' ball (0 : Point) R) {x : Point} (hx : x ∈ frontier U) :
    F x ∈ sphere (0 : Point) R := by
  rw [hU, ← F.preimage_frontier, frontier_ball (0 : Point) hR.ne'] at hx
  exact hx

private theorem normalizedHausdorff_two_lipschitz_image_le {E : Type*}
    [EMetricSpace E] [MeasurableSpace E] [BorelSpace E] {K : ℝ≥0}
    {f : UnitTensorSphere → E} (hf : LipschitzWith K f) (A : Set UnitTensorSphere) :
    (Measure.euclideanHausdorffMeasure 2 : Measure E) (f '' A) ≤ (K : ℝ≥0∞) ^ 2 * tensorSphereMeasure A := by
  have h := hf.hausdorffMeasure_image_le (d := ((2 : ℕ) : ℝ)) (by positivity) A
  simp only [ENNReal.rpow_natCast] at h
  simp only [tensorSphereMeasure, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  exact (mul_le_mul_right h _).trans_eq (mul_left_comm _ _ _)

private theorem map_boundary_direction_measure_le {X E : Type*} [MeasurableSpace X]
    [EMetricSpace E] [MeasurableSpace E] [BorelSpace E] (μ : Measure X) {s : Set X} (hs : MeasurableSet s)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) {θ : X → UnitTensorSphere} (hθ : Measurable θ) (f : X → E)
    (hMeasure : ∀ A : Set X, MeasurableSet A → A ⊆ s → μ A ≤ (Measure.euclideanHausdorffMeasure 2 : Measure E) (f '' A))
    {K : ℝ≥0} {g : UnitTensorSphere → E} (hg : LipschitzWith K g) (hInv : ∀ x ∈ s, g (θ x) = f x) :
    Measure.map θ μ ≤ (K : ℝ≥0∞) ^ 2 • tensorSphereMeasure := by
  apply Measure.le_iff.2
  intro A hA
  let T := θ ⁻¹' A ∩ s
  have hT : MeasurableSet T := (hθ hA).inter hs
  have hEq : μ (θ ⁻¹' A) = μ T := by
    conv_lhs => rw [← Measure.restrict_eq_self_of_ae_mem hμ]
    exact Measure.restrict_apply (hθ hA)
  have hCover : f '' T ⊆ g '' A := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨θ x, hx.1, hInv x hx.2⟩
  rw [Measure.map_apply hθ hA, hEq]
  exact (hMeasure T hT inter_subset_right).trans
    ((measure_mono hCover).trans (normalizedHausdorff_two_lipschitz_image_le hg A))

private theorem exists_cylinderRecoveryCoordinates_lipschitz
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) :
    ∃ K : ℝ≥0, LipschitzWith K (cylinderRecoveryCoordinates B c) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let A := (ContinuousLinearMap.fst ℝ Plane (Domain 1)).comp e.toContinuousLinearMap
  let J := (EuclideanSpace.proj (0 : Fin 1)).comp
    ((ContinuousLinearMap.snd ℝ Plane (Domain 1)).comp e.toContinuousLinearMap)
  let L := (A.prod J).comp B.repr.toContinuousLinearMap
  have hs : Isometry (fun x : Point => x - c) := Isometry.of_dist_eq fun _ _ => dist_sub_right _ _ _
  refine ⟨‖L‖₊, ?_⟩
  change LipschitzWith ‖L‖₊ (L ∘ fun x => x - c)
  simpa only [mul_one] using L.lipschitz.comp hs.lipschitz

private theorem lipschitz_scaled_boundaryPoint (R : ℝ) :
    LipschitzWith ‖R‖₊ (fun θ : UnitTensorSphere => R • θ.val) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (R • x.val) (R • y.val) ≤ (‖R‖₊ : ℝ) * dist x.val y.val
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul]
  exact le_rfl

/-- The original disk trace measure pulls back the sphere boundary classes
through the true cap boundary chart with a finite measure bound. -/
theorem map_cylinder_disk_boundary_direction_le
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi z : ℝ}
    (hR : 0 < R) (hI : lo < hi) (hz : z = lo ∨ z = hi) (F : Point ≃ₜ Point)
    (hInv : LipschitzWith 20 (F.symm : Point → Point))
    (hU : translatedAxisCylinder c (B 2) R lo hi = F ⁻¹' ball (0 : Point) R) :
    let θ (y : Plane) := cylinderBoundaryDirection F (c + axisChart B (y, z))
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ Measure.map θ (volume.restrict (ball (0 : Plane) R)) ≤ C • tensorSphereMeasure ∧
      ∀ y ∈ ball (0 : Plane) R, F.symm (R • (θ y).val) = c + axisChart B (y, z) := by
  intro θ
  let μ := (volume : Measure Plane).restrict (ball (0 : Plane) R)
  have hθ : Measurable θ := (measurable_cylinderBoundaryDirection F).comp
    ((continuous_const.add ((continuous_axisChart B).comp (continuous_id.prodMk continuous_const))).measurable)
  have hReconstruct (y : Plane) (hy : y ∈ ball (0 : Plane) R) :
      F.symm (R • (θ y).val) = c + axisChart B (y, z) := by
    apply cylinderBoundaryDirection_reconstruct hR
    apply chart_image_frontier_mem_sphere hR hU
    apply physical_cylinder_frontier_of_parameter B c hR hI (ball_subset_closedBall hy)
    · rcases hz with h | h
      · rw [h]; exact ⟨le_rfl, hI.le⟩
      · rw [h]; exact ⟨hI.le, le_rfl⟩
    · right
      rcases hz with h | h
      · rw [h]; exact fun ht => (lt_irrefl _ ht.1)
      · rw [h]; exact fun ht => (lt_irrefl _ ht.2)
  let g (θ : UnitTensorSphere) := (cylinderRecoveryCoordinates B c (F.symm (R • θ.val))).1
  obtain ⟨K, hK⟩ := exists_cylinderRecoveryCoordinates_lipschitz B c
  have hfst : LipschitzWith 1 (Prod.fst : Plane × ℝ → Plane) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, Prod.dist_eq]
    exact le_max_left _ _
  have hg : LipschitzWith (1 * (K * (20 * ‖R‖₊))) g := by
    change LipschitzWith (1 * (K * (20 * ‖R‖₊)))
      ((Prod.fst : Plane × ℝ → Plane) ∘ (cylinderRecoveryCoordinates B c ∘ (F.symm ∘ fun θ : UnitTensorSphere => R • θ.val)))
    exact hfst.comp (hK.comp (hInv.comp (lipschitz_scaled_boundaryPoint R)))
  refine ⟨((1 * (K * (20 * ‖R‖₊)) : ℝ≥0) : ℝ≥0∞) ^ 2, ENNReal.pow_ne_top ENNReal.coe_ne_top, ?_, hReconstruct⟩
  refine map_boundary_direction_measure_le μ measurableSet_ball (ae_restrict_mem measurableSet_ball) hθ id ?_ hg ?_
  · intro A hA hSub
    rw [image_id, Measure.restrict_apply hA, inter_eq_left.mpr hSub]
    have hH : (Measure.euclideanHausdorffMeasure 2 : Measure Plane) = volume := by
      simpa only [finrank_euclideanSpace_fin] using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Plane))
    rw [hH]
  · intro y hy
    change (cylinderRecoveryCoordinates B c (F.symm (R • (θ y).val))).1 = y
    rw [hReconstruct y hy, cylinderRecoveryCoordinates_axisChart]

private def referenceCylinderWall (p : NativeCircle × ℝ) : Point :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).symm (p.1.val, EuclideanSpace.single 0 p.2)

private theorem referenceCylinderWall_measurableEmbedding : MeasurableEmbedding referenceCylinderWall := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let T := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ Plane) τ.symm).trans e.symm
  have h := T.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe (s := sphere (0 : Plane) 1) isClosed_sphere.measurableSet).prodMap
      MeasurableEmbedding.id)
  have hT : referenceCylinderWall = T ∘ Prod.map Subtype.val id := by
    funext p
    change e.symm (p.1.val, EuclideanSpace.single (0 : Fin 1) p.2) = e.symm (p.1.val, τ.symm p.2)
    congr 2
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [τ, PiLp.equivOfUnique]
  rw [hT]
  exact h

private theorem cylinderSideTraceMeasure_le_reference_hausdorff (lo hi : ℝ)
    (A : Set (NativeCircle × ℝ)) (hA : MeasurableSet A) :
    cylinderSideTraceMeasure lo hi A ≤ (Measure.euclideanHausdorffMeasure 2 : Measure Point) (referenceCylinderWall '' A) := by
  let ν := ((volume : Measure Plane).toSphere).prod (volume : Measure ℝ)
  have hLe : cylinderSideTraceMeasure lo hi ≤ ν := Measure.prod_mono le_rfl Measure.restrict_le_self
  have hMap := map_cylinder_surface_product_eq_native (n := 2) (by decide : 0 < 2)
  have hSphere : unitBoundarySurface 2 = (volume : Measure Plane).toSphere :=
    euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 2)
  have hMapLe : Measure.map referenceCylinderWall ν ≤ (Measure.euclideanHausdorffMeasure 2 : Measure Point) := by
    change Measure.map referenceCylinderWall (((volume : Measure Plane).toSphere).prod (volume : Measure ℝ)) ≤ _
    rw [← hSphere]
    exact hMap.le.trans Measure.restrict_le_self
  calc
    _ ≤ ν A := hLe A
    _ = Measure.map referenceCylinderWall ν (referenceCylinderWall '' A) := by
      have hE := referenceCylinderWall_measurableEmbedding
      rw [Measure.map_apply hE.measurable (hE.measurableSet_image.mpr hA), hE.injective.preimage_image]
    _ ≤ _ := hMapLe _

private def wallReferenceRescale (R : ℝ) (p : Plane × ℝ) : Point :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).symm (R⁻¹ • p.1, EuclideanSpace.single 0 p.2)

private theorem exists_lipschitz_wallReferenceRescale (R : ℝ) : ∃ K : ℝ≥0, LipschitzWith K (wallReferenceRescale R) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let τ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let L := e.symm.toContinuousLinearMap.comp
    ((R⁻¹ • ContinuousLinearMap.fst ℝ Plane ℝ).prod (τ.symm.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ Plane ℝ)))
  refine ⟨‖L‖₊, ?_⟩
  have hEq : wallReferenceRescale R = L := by
    funext p
    change e.symm (R⁻¹ • p.1, EuclideanSpace.single (0 : Fin 1) p.2) = e.symm (R⁻¹ • p.1, τ.symm p.2)
    congr 2
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [τ, PiLp.equivOfUnique]
  rw [hEq]
  exact L.lipschitz

/-- The original lateral trace measure pulls back the sphere boundary
classes through the true wall chart with a finite measure bound. -/
theorem map_cylinder_wall_boundary_direction_le
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ}
    (hR : 0 < R) (hI : lo < hi) (F : Point ≃ₜ Point)
    (hInv : LipschitzWith 20 (F.symm : Point → Point))
    (hU : translatedAxisCylinder c (B 2) R lo hi = F ⁻¹' ball (0 : Point) R) :
    let θ (p : NativeCircle × ℝ) := cylinderBoundaryDirection F (c + axisChart B (R • p.1.val, p.2))
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ Measure.map θ (cylinderSideTraceMeasure lo hi) ≤ C • tensorSphereMeasure ∧
      ∀ p : NativeCircle × ℝ, p.2 ∈ Ioo lo hi → F.symm (R • (θ p).val) = c + axisChart B (R • p.1.val, p.2) := by
  intro θ
  let μ := cylinderSideTraceMeasure lo hi
  let s := {p : NativeCircle × ℝ | p.2 ∈ Ioo lo hi}
  let T (p : NativeCircle × ℝ) := c + axisChart B (R • p.1.val, p.2)
  have hT : Continuous T := by
    have hMap : Continuous (fun p : NativeCircle × ℝ => (R • p.1.val, p.2)) := by fun_prop
    exact continuous_const.add ((continuous_axisChart B).comp hMap)
  have hθ : Measurable θ := (measurable_cylinderBoundaryDirection F).comp hT.measurable
  have hReconstruct (p : NativeCircle × ℝ) (hp : p ∈ s) : F.symm (R • (θ p).val) = T p := by
    apply cylinderBoundaryDirection_reconstruct hR
    apply chart_image_frontier_mem_sphere hR hU
    have hRim : ‖R • p.1.val‖ = R := by
      rw [norm_smul, Real.norm_of_nonneg hR.le, mem_sphere_zero_iff_norm.mp p.1.property, mul_one]
    apply physical_cylinder_frontier_of_parameter B c hR hI
      (mem_closedBall_zero_iff.2 hRim.le) (Ioo_subset_Icc_self hp)
    exact Or.inl fun h => ((mem_ball_zero_iff.1 h).ne hRim)
  let g (θ : UnitTensorSphere) := wallReferenceRescale R (cylinderRecoveryCoordinates B c (F.symm (R • θ.val)))
  obtain ⟨K, hK⟩ := exists_cylinderRecoveryCoordinates_lipschitz B c
  obtain ⟨L, hL⟩ := exists_lipschitz_wallReferenceRescale R
  have hg : LipschitzWith (L * (K * (20 * ‖R‖₊))) g := by
    change LipschitzWith (L * (K * (20 * ‖R‖₊)))
      (wallReferenceRescale R ∘ (cylinderRecoveryCoordinates B c ∘ (F.symm ∘ fun θ : UnitTensorSphere => R • θ.val)))
    exact hL.comp (hK.comp (hInv.comp (lipschitz_scaled_boundaryPoint R)))
  refine ⟨((L * (K * (20 * ‖R‖₊)) : ℝ≥0) : ℝ≥0∞) ^ 2,
    ENNReal.pow_ne_top ENNReal.coe_ne_top, ?_, hReconstruct⟩
  have hs : MeasurableSet s := measurable_snd measurableSet_Ioo
  apply map_boundary_direction_measure_le μ hs (ae_cylinderSideTraceMeasure_height_mem lo hi) hθ referenceCylinderWall
    (fun A hA _ => cylinderSideTraceMeasure_le_reference_hausdorff lo hi A hA) hg
  intro p hp
  dsimp only [g]
  rw [hReconstruct p hp]
  change wallReferenceRescale R (cylinderRecoveryCoordinates B c (c + axisChart B (R • p.1.val, p.2))) = _
  rw [cylinderRecoveryCoordinates_axisChart]
  unfold wallReferenceRescale referenceCylinderWall
  rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]

end Thesis.MeasureGeometry

end
