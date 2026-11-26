module

public import Thesis.MeasureGeometry.CompactifiedPlanarPunctures
public import Thesis.MeasureGeometry.CompactifiedSphericalChart
public import Thesis.MeasureGeometry.SphericalDiskInterior

/-! Smooth spherical meridians with an even total light character. -/

public section

noncomputable section

open Function Metric OnePoint Set
open scoped BigOperators ContDiff RealInnerProductSpace Topology

namespace Thesis.MeasureGeometry

private theorem exists_ordered_compactifiedSphericalCoordinates
    {c : Point} {R : ℝ} (hR : 0 < R) {n : ℕ}
    (z : Fin n → sphere c R) (hz : Injective z) :
    ∃ (J : CompactifiedSphericalChart c R) (order : Equiv.Perm (Fin n)) (p : Fin n → ℝ × ℝ),
      (∀ i, J.homeo (p i) = z (order i)) ∧ StrictMono (fun i => (p i).1) := by
  let E : OnePoint Plane ≃ₜ sphere (0 : Point) 1 :=
    onePointEquivSphereOfFinrankEq (ι := Fin 3) (V := Plane) (by simp)
  let A := E.trans (positiveSphereNormalize c R hR).symm
  letI : Infinite (sphere c R) := Infinite.of_injective A A.injective
  obtain ⟨pole,hPole⟩ := (Set.finite_range z).exists_notMem
  obtain ⟨J,hJ⟩ := exists_compactifiedSphericalChart hR pole
  have hImage (i : Fin n) : ∃ x : ℝ × ℝ, J.homeo x = z i := by
    obtain ⟨w,hw⟩ := J.homeo.surjective (z i)
    induction w using OnePoint.rec with
    | infty => exact (hPole ⟨i,hw.symm.trans hJ⟩).elim
    | coe w => exact ⟨w,hw⟩
  choose p hp using hImage
  have hP : Injective p := fun i j he => hz
    ((hp i).symm.trans ((congrArg (fun x : ℝ × ℝ => J.homeo x) he).trans (hp j)))
  obtain ⟨s,hs⟩ := exists_planarShear_fst_injective hP
  let S := planarShear s
  obtain ⟨order,hOrder⟩ := exists_order_by_firstCoordinate (fun i => S (p i)) hs
  let J' := J.precompose S.symm
  refine ⟨J',order,fun i => S (p (order i)),?_,hOrder⟩
  intro i
  change (J.precompose S.symm).homeo (S (p (order i))) = _
  rw [CompactifiedSphericalChart.precompose_coe,S.symm_apply_apply]
  exact hp (order i)

private def stereographicMeridianDisk {c : Point} {R : ℝ} (J : CompactifiedSphericalChart c R)
    (x : ℝ × ℝ) (δ : ℝ) (y : Plane) : Point :=
  (J.homeo (x + δ • planePairCoordinates y : ℝ × ℝ)).val

private theorem stereographicMeridianDisk_smoothEmbedding {c : Point} {R : ℝ}
    (J : CompactifiedSphericalChart c R) (x : ℝ × ℝ) {δ : ℝ} (hδ : 0 < δ) :
    IsSmoothDiskEmbedding (stereographicMeridianDisk J x δ) := by
  let L : Plane →L[ℝ] (ℝ × ℝ) := δ • planePairCoordinates.toContinuousLinearMap
  let G (y : Plane) := x + L y
  let F (z : ℝ × ℝ) := (J.homeo z).val
  let d := stereographicMeridianDisk J x δ
  have hd : d = F ∘ G := rfl
  have hLI : Injective L := (smul_right_injective _ hδ.ne').comp planePairCoordinates.injective
  have hGI : Injective G := fun y z h => hLI (add_left_cancel h)
  have hFI : Injective F := by
    intro y z h
    exact OnePoint.coe_injective (J.homeo.injective (Subtype.ext h))
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := contDiff_const.add L.contDiff
  have hD : ContDiff ℝ (⊤ : ℕ∞) d := hd ▸ J.smooth.comp hG
  have hK : (interior Disk).Nonempty :=
    ⟨0,interior_maximal ball_subset_closedBall isOpen_ball (mem_ball_self zero_lt_one)⟩
  refine ⟨hD.contDiffOn,fun _ _ _ _ h => hGI (hFI h),?_⟩
  intro y hy
  have hFDer : DifferentiableAt ℝ F (G y) := J.smooth.differentiable (by simp) _
  have hGDer : HasFDerivAt G L y := L.hasFDerivAt.const_add _
  have hFD : HasFDerivAt d ((fderiv ℝ F (G y)).comp L) y :=
    hd ▸ hFDer.hasFDerivAt.comp y hGDer
  rw [fderivWithin_eq_fderiv (uniqueDiffOn_convex (convex_closedBall _ _) hK y hy) hFD.differentiableAt,
    hFD.fderiv]
  exact (J.derivative_injective (G y)).comp hLI

/-- A finite family of distinct spherical punctures admits actual smooth
meridian disks. Their circle traces have zero total light character. -/
theorem exists_spherical_meridians_lightParity_zero (a : BulkCoefficients) (v : Sphere3)
    {c : Point} {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 0 < n)
    (z : Fin n → sphere c R) (hz : Injective z)
    (Q : C(↥(sphere c R \ range (fun i => (z i).val)),vacuum a)) :
    ∃ (d : Fin n → Plane → Point) (b : Fin n → C(NativeCircle,vacuum a)),
      (∀ i, IsSmoothDiskEmbedding (d i) ∧ MapsTo (d i) Disk (sphere c R) ∧
        d i 0 = (z i).val ∧
        (d i '' Disk ∩ range (fun j => (z j).val) = {d i 0}) ∧
        d i 0 - c ∉ LinearMap.range (fderiv ℝ (d i) 0).toLinearMap) ∧
      (∀ i θ, ∃ h : d i θ.val ∈ sphere c R \ range (fun j => (z j).val),
        b i θ = Q ⟨_,h⟩) ∧
      (∑ i, if nativeVacuumCircleCost a (b i) = kappaStar a then (1 : ZMod 2) else 0) = 0 := by
  classical
  obtain ⟨J,order,p,hJ,hP⟩ := exists_ordered_compactifiedSphericalCoordinates hR z hz
  let W := compactifiedPlanarPunctures p
  let U := sphere c R \ range (fun i => (z i).val)
  have hF (x : W) : (J.homeo x.val).val ∈ U := by
    refine ⟨(J.homeo x.val).property,?_⟩
    rintro ⟨i, hi⟩
    have he : J.homeo (p (order.symm i)) = J.homeo x.val := by
      rw [hJ,order.apply_symm_apply]
      exact Subtype.ext hi
    exact x.property ⟨order.symm i,J.homeo.injective he⟩
  let F : C(W,U) :=
    ⟨fun x => ⟨(J.homeo x.val).val,hF x⟩,Continuous.subtype_mk
      (continuous_subtype_val.comp (J.homeo.continuous.comp continuous_subtype_val)) hF⟩
  let Q₀ := Q.comp F
  obtain ⟨δ,b,hδ,hDisk,hB,hSum⟩ := exists_compactifiedPlanarPeripheralCircles v hn p hP Q₀
  let d (i : Fin n) := stereographicMeridianDisk J (p i) (δ i)
  have hD0 (i : Fin n) : d i 0 = (z (order i)).val := by
    change (J.homeo (p i + δ i • planePairCoordinates 0 : ℝ × ℝ)).val = (z (order i)).val
    rw [map_zero,smul_zero,add_zero,hJ]
  have hEmb (i : Fin n) : IsSmoothDiskEmbedding (d i) :=
    stereographicMeridianDisk_smoothEmbedding J (p i) (hδ i)
  have hSp (i : Fin n) : MapsTo (d i) Disk (sphere c R) :=
    fun y _ => (J.homeo (p i + δ i • planePairCoordinates y : ℝ × ℝ)).property
  have hInt (i : Fin n) : d i '' Disk ∩ range (fun j => (z j).val) = {d i 0} := by
    ext y
    constructor
    · rintro ⟨⟨u,hu,he⟩,⟨j,hj⟩⟩
      let k := order.symm j
      have hP_eq : p i + δ i • planePairCoordinates u = p k := by
        apply OnePoint.coe_injective
        apply J.homeo.injective
        apply Subtype.ext
        change d i u = (J.homeo (p k)).val
        rw [hJ,show order k = j from order.apply_symm_apply j]
        exact he.trans hj.symm
      exact mem_singleton_iff.mpr (((hDisk i k u hu hP_eq).2 ▸ he).symm)
    · intro h
      obtain rfl := mem_singleton_iff.mp h
      exact ⟨⟨0,mem_closedBall_self zero_le_one,rfl⟩,⟨order i,(hD0 i).symm⟩⟩
  have hTrans (i : Fin n) : d i 0-c ∉ LinearMap.range (fderiv ℝ (d i) 0).toLinearMap := by
    rintro ⟨u,hu⟩
    have hn0 : (0 : Plane) ∈ ball 0 1 := mem_ball_self zero_lt_one
    have h := sphericalDisk_fderiv_orthogonal_radius (hEmb i) (hSp i) hn0 u
    change fderiv ℝ (d i) 0 u = d i 0-c at hu
    have hN : ‖d i 0-c‖ = R := by
      simpa only [mem_sphere,dist_eq_norm] using hSp i (mem_closedBall_self zero_le_one)
    rw [hu,real_inner_self_eq_norm_sq,hN] at h
    exact (pow_pos hR 2).ne' h
  refine ⟨d ∘ order.symm,b ∘ order.symm,?_,?_,?_⟩
  · intro i
    let j := order.symm i
    exact ⟨hEmb j,hSp j,(hD0 j).trans (congrArg (fun k => (z k).val) (order.apply_symm_apply i)),
      hInt j,hTrans j⟩
  · intro i θ
    let j := order.symm i
    obtain ⟨hJ',he⟩ := hB j θ
    exact ⟨(F ⟨_,hJ'⟩).property,he⟩
  · exact (Equiv.sum_comp order.symm
      (fun i => if nativeVacuumCircleCost a (b i) = kappaStar a then (1 : ZMod 2) else 0)).trans hSum

end Thesis.MeasureGeometry
