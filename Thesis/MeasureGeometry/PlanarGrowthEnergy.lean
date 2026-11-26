module

public import Thesis.MeasureGeometry.PerforatedVacuumDisk

/-! Energy estimates for the growth and merger phases outside a planar defect set. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set Topology
open scoped ContDiff Matrix.Norms.Frobenius

namespace Thesis

/-- The circle trace at the boundary of a disk on which the ambient map takes vacuum values. -/
def vacuumDiskCircleTrace (a : BulkCoefficients) (Q : Plane → S0) (hQ : Continuous Q)
    (B : PlanarDisk) (hB : ∀ x ∈ sphere B.center B.radius, Q x ∈ vacuum a) :
    C(NativeCircle, vacuum a) :=
  planarVacuumCircleTrace a Q hQ B.center B.radius fun z =>
    hB _ (mem_sphere.mpr (dist_planarCircle B.center B.radius_pos.le z))

/-- The Dirichlet energy inside the open disk, outside the prescribed defect set. -/
def planarDiskExteriorEnergy (Q : Plane → S0) (K : Set Plane) (B : PlanarDisk) : ℝ :=
  ∫ x in B.interior \ K, planarSmoothDirichletDensity Q x

private theorem integrableOn_of_subset_closedDisk {Q : Plane → S0} (hQ : ContDiff ℝ 1 Q)
    (B : PlanarDisk) {S : Set Plane} (hS : S ⊆ B.closed) :
    IntegrableOn (planarSmoothDirichletDensity Q) S :=
  ((continuous_planarSmoothDirichletDensity hQ).continuousOn.integrableOn_compact
    (isCompact_closedBall B.center B.radius)).mono_set hS

theorem PlanarDisk.radius_le_grow (B : PlanarDisk) {t : ℝ} (ht : 0 ≤ t) : B.radius ≤ (B.grow t).radius := by
  simpa only [PlanarDisk.grow, Real.exp_zero, one_mul] using B.grow_radius_mono ht

/-- A defect-free swept annulus advances the charge-energy invariant by its logarithmic duration. -/
theorem planarDisk_growth_energy_invariant (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) (K : Set Plane) (B : PlanarDisk) (s t : ℝ) (ht : 0 ≤ t)
    (hClear : Disjoint ((B.grow t).interior \ B.interior) K)
    (hVac : ∀ x, dist x B.center ∈ Icc B.radius (B.grow t).radius → Q x ∈ vacuum a) :
    let f := planarVacuumAnnulusTrace a Q hQ.continuous B.center B.radius_pos.le hVac B.radius
      ⟨le_rfl, B.radius_le_grow ht⟩
    let g := planarVacuumAnnulusTrace a Q hQ.continuous B.center B.radius_pos.le hVac (B.grow t).radius
      ⟨B.radius_le_grow ht, le_rfl⟩
    s * nativeVacuumCircleCost a f ≤ planarDiskExteriorEnergy Q K B →
      (s + t) * nativeVacuumCircleCost a g ≤ planarDiskExteriorEnergy Q K (B.grow t) := by
  intro f g hOld
  have hHom : f.Homotopic g :=
    planarVacuumAnnulusTrace_homotopic a Q hQ.continuous B.center B.radius_pos.le hVac
      ⟨le_rfl, B.radius_le_grow ht⟩ ⟨B.radius_le_grow ht, le_rfl⟩
  have hEq := nativeVacuumCircleCost_homotopic a hHom
  obtain ⟨v, hv⟩ := vacuumQuaternionProjection_surjective a (g nativeCircleLoopBase)
  have hAnn : t * nativeVacuumCircleCost a g ≤
      ∫ x in (B.grow t).interior \ B.interior, planarSmoothDirichletDensity Q x := by
    rw [nativeVacuumCircleCost_eq a g v hv]
    exact planarVacuumDiskGrowth_energy_ge_splittingCost a Q hQ B ht hVac v hv
  have hSet : (B.grow t).interior \ K =
      (B.interior \ K) ∪ ((B.grow t).interior \ B.interior) := by
    ext x
    simp only [Set.mem_sdiff, mem_union]
    have hsub : x ∈ B.interior → x ∈ (B.grow t).interior := fun hx =>
      (PlanarDisk.subset_grow ht B).1 hx
    have hdisj : x ∈ (B.grow t).interior \ B.interior → x ∉ K :=
      fun hx hK => Set.disjoint_left.mp hClear hx hK
    tauto
  rw [planarDiskExteriorEnergy, hSet, setIntegral_union]
  · rw [add_mul]
    exact add_le_add (by rwa [← hEq]) hAnn
  · exact Set.disjoint_left.mpr fun _ hx hy => hy.2 hx.1
  · exact measurableSet_ball.diff measurableSet_ball
  · exact integrableOn_of_subset_closedDisk hQ B (sdiff_subset.trans ball_subset_closedBall)
  · exact integrableOn_of_subset_closedDisk hQ (B.grow t) (sdiff_subset.trans ball_subset_closedBall)

theorem closed_subset_of_interior_subset {B D : PlanarDisk} (h : B.interior ⊆ D.interior) :
    B.closed ⊆ D.closed := by
  simpa only [PlanarDisk.interior, PlanarDisk.closed, closure_ball _ B.radius_pos.ne',
    closure_ball _ D.radius_pos.ne'] using closure_mono h

private theorem closed_disjoint_interior_of_interior_disjoint {B D : PlanarDisk}
    (h : Disjoint B.interior D.interior) : Disjoint B.closed D.interior := by
  have hsub : B.interior ⊆ D.interiorᶜ :=
    fun _ hx hy => Set.disjoint_left.mp h hx hy
  have hc : closure B.interior ⊆ D.interiorᶜ :=
    closure_minimal hsub isOpen_ball.isClosed_compl
  have hCl : closure B.interior = B.closed := closure_ball _ B.radius_pos.ne'
  rw [hCl] at hc
  exact Set.disjoint_left.mpr (fun _ hx hy => hc hx hy)

private theorem shrink_closed_subset_interior {A D : PlanarDisk} (hc : D.center = A.center)
    (hr : D.radius < A.radius) : D.closed ⊆ A.interior := by
  change closedBall D.center D.radius ⊆ ball A.center A.radius
  rw [hc]
  exact closedBall_subset_ball hr

theorem outerBoundary_avoids_defect_of_shrunkCover {ι : Type*}
    (B : PlanarDisk) (A D : ι → PlanarDisk) (K : Set Plane)
    (hin : ∀ i, (A i).interior ⊆ B.interior)
    (hc : ∀ i, (D i).center = (A i).center) (hr : ∀ i, (D i).radius < (A i).radius)
    (hcover : K ∩ B.closed ⊆ ⋃ i, (D i).interior) :
    ∀ x ∈ sphere B.center B.radius, x ∉ K := by
  intro x hx hK
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hK, sphere_subset_closedBall hx⟩)
  have hxIn := hin i (shrink_closed_subset_interior (hc i) (hr i) (ball_subset_closedBall hi))
  exact lt_irrefl _ ((mem_sphere.mp hx) ▸ (mem_ball.mp hxIn))

theorem oldAnnulus_avoids_defect_of_shrunkCover {ι : Type*}
    (B : PlanarDisk) (A D : ι → PlanarDisk) (K : Set Plane)
    (hin : ∀ i, (A i).interior ⊆ B.interior)
    (hsep : Pairwise (fun i j => Disjoint (A i).interior (A j).interior))
    (hc : ∀ i, (D i).center = (A i).center) (hr : ∀ i, (D i).radius < (A i).radius)
    (hcover : K ∩ B.closed ⊆ ⋃ i, (D i).interior) :
    ∀ i x, dist x (A i).center ∈ Icc (D i).radius (A i).radius → x ∉ K := by
  intro i x hx hK
  have hxA : x ∈ (A i).closed := hx.2
  have hxB : x ∈ B.closed := closed_subset_of_interior_subset (hin i) hxA
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover ⟨hK, hxB⟩)
  by_cases he : i = j
  · subst j
    have hl : dist x (D i).center < (D i).radius := mem_ball.mp hj
    rw [hc i] at hl
    exact (not_lt_of_ge hx.1) hl
  · exact Set.disjoint_left.mp (closed_disjoint_interior_of_interior_disjoint (hsep he)) hxA
      (shrink_closed_subset_interior (hc j) (hr j) (ball_subset_closedBall hj))

/-- During an instantaneous merger the charge-energy inequality persists. The
strictly smaller disks retain all defects and their circles carry the old charges. -/
theorem planarDisk_grouped_merger_energy_invariant (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) (K : Set Plane) (hK : MeasurableSet K) (B : PlanarDisk)
    {ι : Type*} [Fintype ι] (A D : ι → PlanarDisk)
    (hin : ∀ i, (A i).interior ⊆ B.interior)
    (hsep : Pairwise (fun i j => Disjoint (A i).interior (A j).interior))
    (hc : ∀ i, (D i).center = (A i).center) (hr : ∀ i, (D i).radius < (A i).radius)
    (hcover : K ∩ B.closed ⊆ ⋃ i, (D i).interior)
    (hVac : ∀ x ∈ B.closed, x ∉ K → Q x ∈ vacuum a) (s : ℝ) (hs : 0 ≤ s) :
    let hB := fun x (hx : x ∈ sphere B.center B.radius) =>
      hVac x (sphere_subset_closedBall hx)
        (outerBoundary_avoids_defect_of_shrunkCover B A D K hin hc hr hcover x hx)
    let hA := fun i x (hx : x ∈ sphere (A i).center (A i).radius) =>
      hVac x (closed_subset_of_interior_subset (hin i) (sphere_subset_closedBall hx))
        (oldAnnulus_avoids_defect_of_shrunkCover B A D K hin hsep hc hr hcover i x
        ⟨(hr i).le.trans (mem_sphere.mp hx).symm.le, (mem_sphere.mp hx).le⟩)
    (∀ i, s * nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous (A i) (hA i)) ≤
      planarDiskExteriorEnergy Q K (A i)) →
      s * nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous B hB) ≤
        planarDiskExteriorEnergy Q K B := by
  classical
  intro hB hA hOld
  let S := perforatedPlanarDisk B D Finset.univ
  have hS (x : Plane) (hx : x ∈ S) : Q x ∈ vacuum a := by
    refine hVac x hx.1 fun h => hx.2 ?_
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨h, hx.1⟩)
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_univ _, hi⟩
  let u (x : Plane) : vacuum a :=
    if h : Q x ∈ vacuum a then ⟨Q x, h⟩
    else vacuumQuaternionProjection a (sphereOfQuaternion 1 norm_one)
  have huVal (x : Plane) (hx : x ∈ S) : (u x).val = Q x := by
    change (if h : Q x ∈ vacuum a then (⟨Q x, h⟩ : vacuum a)
      else vacuumQuaternionProjection a (sphereOfQuaternion 1 norm_one)).val = Q x
    rw [dif_pos (hS x hx)]
  have hu : ContinuousOn u S :=
    Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      (hQ.continuous.continuousOn.congr (fun x hx => huVal x hx))
  have hShr (i : ι) : (D i).closed ⊆ (A i).interior := shrink_closed_subset_interior (hc i) (hr i)
  have hDInside (i : ι) : (D i).closed ⊆ B.interior := (hShr i).trans (hin i)
  have hDsep : Pairwise (fun i j => Disjoint (D i).closed (D j).closed) :=
    fun i j hij => (hsep hij).mono (hShr i) (hShr j)
  have hbo : sphere B.center B.radius ⊆ S :=
    outerSphere_subset_perforatedPlanarDisk B D Finset.univ (fun i _ => hDInside i)
  have hbi (i : ι) : sphere (D i).center (D i).radius ⊆ S :=
    innerSphere_subset_perforatedPlanarDisk B D Finset.univ hDInside hDsep i
  have hOuter : planarBoundaryTrace B u hu hbo = vacuumDiskCircleTrace a Q hQ.continuous B hB := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    change (u (diskCone B (0, z)).val).val = Q (B.center + B.radius • z.val)
    rw [huVal _ (hbo (diskCone_boundary_mem_sphere B z)), diskCone_zero_val]
  have hInnerCost (i : ι) : nativeVacuumCircleCost a (planarBoundaryTrace (D i) u hu (hbi i)) =
      nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous (A i) (hA i)) := by
    have hN (x : Plane) (hx : dist x (A i).center ∈ Icc (D i).radius (A i).radius) : Q x ∈ vacuum a :=
      hVac x (closed_subset_of_interior_subset (hin i) hx.2)
        (oldAnnulus_avoids_defect_of_shrunkCover B A D K hin hsep hc hr hcover i x hx)
    let f := planarVacuumAnnulusTrace a Q hQ.continuous (A i).center (D i).radius_pos.le hN
      (D i).radius ⟨le_rfl, (hr i).le⟩
    have he : planarBoundaryTrace (D i) u hu (hbi i) = f := by
      apply ContinuousMap.ext
      intro z
      apply Subtype.ext
      change (u (diskCone (D i) (0, z)).val).val = Q ((A i).center + (D i).radius • z.val)
      rw [huVal _ (hbi i (diskCone_boundary_mem_sphere (D i) z)), diskCone_zero_val, hc i]
    rw [he]
    exact nativeVacuumCircleCost_homotopic a
      (planarVacuumAnnulusTrace_homotopic a Q hQ.continuous (A i).center (D i).radius_pos.le hN
        ⟨le_rfl, (hr i).le⟩ ⟨(hr i).le, le_rfl⟩)
  have hCost : nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous B hB) ≤
      ∑ i, nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous (A i) (hA i)) := by
    have h := perforatedVacuumDisk_outerCost_le_sum a B D hDInside hDsep u hu
    change nativeVacuumCircleCost a (planarBoundaryTrace B u hu hbo) ≤
      ∑ i, nativeVacuumCircleCost a (planarBoundaryTrace (D i) u hu (hbi i)) at h
    simpa only [hOuter, hInnerCost] using h
  let T (i : ι) := (A i).interior \ K
  have hTmeas (i : ι) : MeasurableSet (T i) := measurableSet_ball.diff hK
  have hTdisj : Pairwise (fun i j => Disjoint (T i) (T j)) :=
    fun _ _ hij => (hsep hij).mono sdiff_subset sdiff_subset
  have hTi (i : ι) : IntegrableOn (planarSmoothDirichletDensity Q) (T i) :=
    integrableOn_of_subset_closedDisk hQ (A i) (sdiff_subset.trans ball_subset_closedBall)
  have hFan : (⋃ i, T i) ⊆ B.interior \ K := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨hin i hi.1, hi.2⟩
  calc
    _ ≤ s * ∑ i, nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous (A i) (hA i)) :=
      mul_le_mul_of_nonneg_left hCost hs
    _ ≤ ∑ i, planarDiskExteriorEnergy Q K (A i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hOld i
    _ = ∫ x in ⋃ i, T i, planarSmoothDirichletDensity Q x :=
      (integral_iUnion_fintype hTmeas hTdisj hTi).symm
    _ ≤ _ := setIntegral_mono_set
      (integrableOn_of_subset_closedDisk hQ B (sdiff_subset.trans ball_subset_closedBall))
      (Eventually.of_forall (planarSmoothDirichletDensity_nonneg Q))
      (Eventually.of_forall fun _ hx => hFan hx)

private theorem exists_common_shrink_of_compact_cover {ι : Type*} (K : Set Plane) (hK : IsCompact K)
    (A : ι → PlanarDisk) (hcover : K ⊆ ⋃ i, (A i).interior) :
    ∃ (q : ℝ), q ∈ Ioo 0 1 ∧ K ⊆ ⋃ i, ball (A i).center (q * (A i).radius) := by
  classical
  let U (q : Ioo (0 : ℝ) 1) := ⋃ i, ball (A i).center (q.val * (A i).radius)
  have hU (q : Ioo (0 : ℝ) 1) : IsOpen (U q) := isOpen_iUnion fun _ => isOpen_ball
  have hCov : K ⊆ ⋃ q, U q := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    let d := dist x (A i).center / (A i).radius
    have hd : 0 ≤ d := div_nonneg dist_nonneg (A i).radius_pos.le
    have hd₁ : d < 1 := (div_lt_one (A i).radius_pos).2 (mem_ball.mp hi)
    let q : Ioo (0 : ℝ) 1 := ⟨(1 + d) / 2, by constructor <;> linarith⟩
    have hq : d < q.val := by change d < (1 + d) / 2; linarith
    exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨i,
      mem_ball.mpr ((div_lt_iff₀ (A i).radius_pos).mp hq)⟩⟩
  obtain ⟨L, hL⟩ := hK.elim_finite_subcover U hU hCov
  let L' := insert (⟨1 / 2, by norm_num⟩ : Ioo (0 : ℝ) 1) L
  have hL' : L'.Nonempty := ⟨_, Finset.mem_insert_self _ _⟩
  let q := L'.max' hL'
  refine ⟨q.val, q.property, ?_⟩
  intro x hx
  obtain ⟨p, hp, hpX⟩ := mem_iUnion₂.mp (hL hx)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hpX
  have hpQ : p ≤ q := Finset.le_max' _ _ (Finset.mem_insert_of_mem hp)
  exact mem_iUnion.mpr ⟨i, ball_subset_ball
    (mul_le_mul_of_nonneg_right hpQ (A i).radius_pos.le) hi⟩

theorem outerBoundary_avoids_defect_of_openCover {ι : Type*}
    (B : PlanarDisk) (A : ι → PlanarDisk) (K : Set Plane)
    (hin : ∀ i, (A i).interior ⊆ B.interior)
    (hcover : K ∩ B.closed ⊆ ⋃ i, (A i).interior) :
    ∀ x ∈ sphere B.center B.radius, x ∉ K := by
  intro x hx hK
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover ⟨hK, sphere_subset_closedBall hx⟩)
  exact lt_irrefl _ ((mem_sphere.mp hx) ▸ (mem_ball.mp (hin j hj)))

theorem innerBoundary_avoids_defect_of_openCover {ι : Type*}
    (B : PlanarDisk) (A : ι → PlanarDisk) (K : Set Plane)
    (hin : ∀ i, (A i).interior ⊆ B.interior)
    (hsep : Pairwise (fun i j => Disjoint (A i).interior (A j).interior))
    (hcover : K ∩ B.closed ⊆ ⋃ i, (A i).interior) (i : ι) :
    ∀ x ∈ sphere (A i).center (A i).radius, x ∉ K := by
  intro x hx hK
  have hxA : x ∈ (A i).closed := sphere_subset_closedBall hx
  have hxB : x ∈ B.closed := closed_subset_of_interior_subset (hin i) hxA
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover ⟨hK, hxB⟩)
  by_cases he : i = j
  · subst j
    exact lt_irrefl _ ((mem_sphere.mp hx) ▸ (mem_ball.mp hj))
  · exact Set.disjoint_left.mp (closed_disjoint_interior_of_interior_disjoint (hsep he)) hxA hj

/-- A compact defect strictly covered by the old interiors permits the
grouped merger energy comparison even when old circles touch. -/
theorem planarDisk_merger_energy_invariant (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) (K : Set Plane) (hK : IsCompact K) (B : PlanarDisk)
    {ι : Type*} [Fintype ι] (A : ι → PlanarDisk)
    (hin : ∀ i, (A i).interior ⊆ B.interior)
    (hsep : Pairwise (fun i j => Disjoint (A i).interior (A j).interior))
    (hcover : K ∩ B.closed ⊆ ⋃ i, (A i).interior)
    (hVac : ∀ x ∈ B.closed, x ∉ K → Q x ∈ vacuum a) (s : ℝ) (hs : 0 ≤ s) :
    let hB := fun x (hx : x ∈ sphere B.center B.radius) =>
      hVac x (sphere_subset_closedBall hx)
        (outerBoundary_avoids_defect_of_openCover B A K hin hcover x hx)
    let hA := fun i x (hx : x ∈ sphere (A i).center (A i).radius) =>
      hVac x (closed_subset_of_interior_subset (hin i) (sphere_subset_closedBall hx))
        (innerBoundary_avoids_defect_of_openCover B A K hin hsep hcover i x hx)
    (∀ i, s * nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous (A i) (hA i)) ≤
      planarDiskExteriorEnergy Q K (A i)) →
      s * nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous B hB) ≤
        planarDiskExteriorEnergy Q K B := by
  intro hB hA hOld
  obtain ⟨q, hq, hCov⟩ := exists_common_shrink_of_compact_cover _ (hK.inter_right isClosed_closedBall) A hcover
  let D (i : ι) := (A i).grow (Real.log q)
  have hCenter (i : ι) : (D i).center = (A i).center := rfl
  have hRadius (i : ι) : (D i).radius = q * (A i).radius := by
    change Real.exp (Real.log q) * (A i).radius = q * (A i).radius
    rw [Real.exp_log hq.1]
  have hShr (i : ι) : (D i).radius < (A i).radius := by
    rw [hRadius]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hq.2 (A i).radius_pos
  have hCov' : K ∩ B.closed ⊆ ⋃ i, (D i).interior := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hCov hx)
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change x ∈ ball (D i).center (D i).radius
    rwa [hCenter, hRadius]
  exact planarDisk_grouped_merger_energy_invariant a Q hQ K hK.measurableSet B A D hin hsep
    hCenter hShr hCov' hVac s hs hOld

private theorem list_pairwise_rel_of_mem_of_ne {α : Type*} {R : α → α → Prop}
    (hsymm : ∀ ⦃a b⦄, R a b → R b a) {L : List α} (hL : L.Pairwise R)
    {a b : α} (ha : a ∈ L) (hb : b ∈ L) (hne : a ≠ b) : R a b := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hb
  have hij : i ≠ j := by intro he; exact hne (hi.symm.trans (he ▸ hj))
  rcases lt_or_gt_of_ne hij with he | he
  · exact hi ▸ hj ▸ hL.rel_get_of_lt he
  · exact hi ▸ hj ▸ (hsymm (hL.rel_get_of_lt he))

/-- At logarithmic time s, every disk's energy outside the defect dominates
its own boundary charge multiplied by s. -/
def planarDiskEnergyInvariant (a : BulkCoefficients) (Q : Plane → S0) (hQ : Continuous Q)
    (K : Set Plane) (s : ℝ) (L : List PlanarDisk) : Prop :=
  ∀ B ∈ L, ∃ hB : ∀ x ∈ sphere B.center B.radius, Q x ∈ vacuum a,
    s * nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ B hB) ≤ planarDiskExteriorEnergy Q K B

theorem planarDiskEvolution_preserves_cover {p q : ℝ × List PlanarDisk} {K : Set Plane}
    (h : Relation.ReflTransGen PlanarDiskTransition p q) (hp : K ⊆ ⋃ B ∈ p.2, B.interior) :
    K ⊆ ⋃ B ∈ q.2, B.interior := by
  intro x hx
  obtain ⟨B, hB, hBx⟩ := mem_iUnion₂.mp (hp hx)
  obtain ⟨D, hD, hBD, _⟩ := planarDiskEvolution_successor h B hB
  exact mem_iUnion₂.mpr ⟨D, hD, hBD hBx⟩

/-- The actual charge-energy inequality is preserved through complete growth
and contact-normalization phases. -/
theorem planarDiskPhase_preserves_energyInvariant (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) (K : Set Plane) (hK : IsCompact K) (U : PlanarDisk)
    (hVac : ∀ x ∈ U.closed, x ∉ K → Q x ∈ vacuum a) {p q : ℝ × List PlanarDisk}
    (step : PlanarDiskPhase p q) (hTime : 0 ≤ p.1)
    (hCover : K ⊆ ⋃ B ∈ p.2, B.interior)
    (hInside : ∀ B ∈ q.2, B.closed ⊆ U.closed)
    (hInv : planarDiskEnergyInvariant a Q hQ.continuous K p.1 p.2) :
    planarDiskEnergyInvariant a Q hQ.continuous K q.1 q.2 := by
  classical
  cases step with
  | growth s L t ht hsep =>
      intro D hD
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hD
      have hGsep : L.Pairwise (fun C D => Disjoint (C.grow t).interior (D.grow t).interior) :=
        hsep.imp fun hh => ball_disjoint_ball hh
      have hNoCore (x : Plane) (hx : dist x B.center ∈ Icc B.radius (B.grow t).radius) : x ∉ K := by
        intro hxK
        obtain ⟨C, hC, hCx⟩ := mem_iUnion₂.mp (hCover hxK)
        by_cases he : B = C
        · subst C
          exact (not_lt_of_ge hx.1) (mem_ball.mp hCx)
        · have hBC := list_pairwise_rel_of_mem_of_ne (fun {_ _} hh => hh.symm) hGsep hB hC he
          exact Set.disjoint_left.mp (closed_disjoint_interior_of_interior_disjoint hBC) hx.2
            ((PlanarDisk.subset_grow ht C).1 hCx)
      have hClear : Disjoint ((B.grow t).interior \ B.interior) K := by
        refine Set.disjoint_left.mpr fun x hx => hNoCore x ?_
        exact ⟨le_of_not_gt hx.2, (mem_ball.mp hx.1).le⟩
      have hN (x : Plane) (hx : dist x B.center ∈ Icc B.radius (B.grow t).radius) : Q x ∈ vacuum a :=
        hVac x (hInside (B.grow t) hD hx.2) (hNoCore x hx)
      have hB' (x : Plane) (hx : x ∈ sphere (B.grow t).center (B.grow t).radius) : Q x ∈ vacuum a :=
        hN x ⟨(B.radius_le_grow ht).trans (mem_sphere.mp hx).symm.le, (mem_sphere.mp hx).le⟩
      obtain ⟨hB₀, hOld⟩ := hInv B hB
      exact ⟨hB', planarDisk_growth_energy_invariant a Q hQ K B s t ht hClear hN hOld⟩
  | mergers s hsep hMerge hNew =>
      intro B hB
      rename_i L M
      let J : Finset PlanarDisk := L.toFinset.filter fun D => D.interior ⊆ B.interior
      let A (j : J) := j.val
      have hA (j : J) : A j ∈ L := List.mem_toFinset.mp (Finset.mem_filter.mp j.property).1
      have hin (j : J) : (A j).interior ⊆ B.interior := (Finset.mem_filter.mp j.property).2
      have hpair : Pairwise (fun i j : J => Disjoint (A i).interior (A j).interior) :=
        fun i j hne => list_pairwise_rel_of_mem_of_ne (fun {_ _} h => h.symm) hsep (hA i) (hA j)
          (fun he => hne (Subtype.ext he))
      have hcov : K ∩ B.closed ⊆ ⋃ j : J, (A j).interior := by
        intro x hx
        obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp (hCover hx.1)
        obtain ⟨E, hE, hDE, _⟩ := planarDisk_merges_successor hMerge D hD
        have he : E = B := by
          by_contra h
          have hd := list_pairwise_rel_of_mem_of_ne (fun {_ _} h => h.symm) hNew hE hB h
          exact Set.disjoint_left.mp hd (ball_subset_closedBall (hDE hxD)) hx.2
        subst E
        let j : J := ⟨D, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hD, hDE⟩⟩
        exact mem_iUnion.mpr ⟨j, hxD⟩
      have hV (x : Plane) (hx : x ∈ B.closed) (hxK : x ∉ K) : Q x ∈ vacuum a :=
        hVac x (hInside B hB hx) hxK
      have hout (x : Plane) (hx : x ∈ sphere B.center B.radius) : Q x ∈ vacuum a :=
        hV x (sphere_subset_closedBall hx) (outerBoundary_avoids_defect_of_openCover B A K hin hcov x hx)
      refine ⟨hout, planarDisk_merger_energy_invariant a Q hQ K hK B A hin hpair hcov hV s hTime ?_⟩
      intro j
      obtain ⟨_, hOld⟩ := hInv (A j) (hA j)
      exact hOld

theorem planarDiskPhases_preserve_energyInvariant (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) (K : Set Plane) (hK : IsCompact K) (U : PlanarDisk)
    (hVac : ∀ x ∈ U.closed, x ∉ K → Q x ∈ vacuum a) {p q : ℝ × List PlanarDisk}
    (h : Relation.ReflTransGen PlanarDiskPhase p q) (hTime : 0 ≤ p.1)
    (hCover : K ⊆ ⋃ B ∈ p.2, B.interior)
    (hInside : ∀ r, Relation.ReflTransGen PlanarDiskPhase p r → r.1 ≤ q.1 →
      ∀ B ∈ r.2, B.closed ⊆ U.closed)
    (hInv : planarDiskEnergyInvariant a Q hQ.continuous K p.1 p.2) :
    planarDiskEnergyInvariant a Q hQ.continuous K q.1 q.2 := by
  induction h with
  | refl => exact hInv
  | @tail r q hPrev hStep ih =>
      have hFuture := planarDiskEvolution_time_le hStep.evolves
      have hPref := ih fun u hu ht => hInside u hu (ht.trans hFuture)
      have hPrevGeom := planarDiskPhases_evolve hPrev
      exact planarDiskPhase_preserves_energyInvariant a Q hQ K hK U hVac hStep
        (hTime.trans (planarDiskEvolution_time_le hPrevGeom))
        (planarDiskEvolution_preserves_cover hPrevGeom hCover)
        (hInside q (hPrev.tail hStep) le_rfl) hPref

/-- The unit disk in the scale of the planar logarithmic estimate. -/
def unitPlanarDisk : PlanarDisk := ⟨0, 1, zero_lt_one⟩

theorem unitBoundary_avoids_defect_of_diskCover (K : Set Plane) (L : List PlanarDisk)
    (hL : L ≠ []) (stopRadius : ℝ) (hR : (L.map PlanarDisk.radius).sum < stopRadius)
    (hcenter : ∀ B ∈ L, B.center ∈ closedBall (0 : Plane) (1 - 2 * stopRadius))
    (hcover : K ⊆ ⋃ B ∈ L, B.interior) :
    ∀ x ∈ sphere unitPlanarDisk.center unitPlanarDisk.radius, x ∉ K := by
  intro x hx hxK
  obtain ⟨B, hB, hBx⟩ := mem_iUnion₂.mp (hcover hxK)
  have hSum := sum_disk_radii_pos L hL
  have hT : 0 ≤ Real.log (stopRadius / (L.map PlanarDisk.radius).sum) :=
    Real.log_nonneg ((one_le_div hSum).2 hR.le)
  have hInside := planarDiskEvolution_closed_subset_unitDisk hL hR hcenter
    (Relation.ReflTransGen.refl : Relation.ReflTransGen PlanarDiskTransition (0, L) (0, L)) hT
  have hxb := mem_ball.mp (hInside B hB (ball_subset_closedBall hBx))
  exact lt_irrefl _ ((mem_sphere.mp hx) ▸ hxb)

private theorem diskBoundary_avoids_defect_of_pairwise_cover {K : Set Plane} {L : List PlanarDisk}
    (hsep : L.Pairwise (fun B D => Disjoint B.closed D.closed))
    (hcover : K ⊆ ⋃ B ∈ L, B.interior) {B : PlanarDisk} (hB : B ∈ L) :
    ∀ x ∈ sphere B.center B.radius, x ∉ K := by
  intro x hx hxK
  obtain ⟨D, hD, hDx⟩ := mem_iUnion₂.mp (hcover hxK)
  by_cases h : B = D
  · subst D
    exact lt_irrefl _ ((mem_sphere.mp hx) ▸ mem_ball.mp hDx)
  · have hd := list_pairwise_rel_of_mem_of_ne (fun {_ _} hd => hd.symm) hsep hB hD h
    exact Set.disjoint_left.mp hd (sphere_subset_closedBall hx) (ball_subset_closedBall hDx)

/-- The smooth finite-cover form of the planar exterior logarithmic lower bound.
It uses the actual boundary charge and the initial sum of radii. -/
theorem planarVacuum_exterior_energy_ge_of_finite_cover (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) (K : Set Plane) (hK : IsCompact K)
    (hVac : ∀ x ∈ unitPlanarDisk.closed, x ∉ K → Q x ∈ vacuum a)
    (L : List PlanarDisk) (hL : L ≠ []) (stopRadius : ℝ)
    (hR : (L.map PlanarDisk.radius).sum < stopRadius)
    (hcenter : ∀ B ∈ L, B.center ∈ closedBall (0 : Plane) (1 - 2 * stopRadius))
    (hcover : K ⊆ ⋃ B ∈ L, B.interior) :
    let hBoundary := fun x (hx : x ∈ sphere unitPlanarDisk.center unitPlanarDisk.radius) =>
      hVac x (sphere_subset_closedBall hx)
        (unitBoundary_avoids_defect_of_diskCover K L hL stopRadius hR hcenter hcover x hx)
    Real.log (stopRadius / (L.map PlanarDisk.radius).sum) *
      nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous unitPlanarDisk hBoundary) ≤
        planarDiskExteriorEnergy Q K unitPlanarDisk := by
  classical
  intro hBoundary
  let T := Real.log (stopRadius / (L.map PlanarDisk.radius).sum)
  have hSum := sum_disk_radii_pos L hL
  have hT : 0 ≤ T := Real.log_nonneg ((one_le_div hSum).2 hR.le)
  obtain ⟨L₀, hMerge₀, hSep₀⟩ := exists_pairwise_disjoint_planarDisk_merges L
  have hReach₀ := planarDisk_merges_evolve 0 hMerge₀
  have hCov₀ := planarDiskEvolution_preserves_cover hReach₀ hcover
  have hInside₀ := planarDiskEvolution_closed_subset_unitDisk hL hR hcenter hReach₀ hT
  have hInv₀ : planarDiskEnergyInvariant a Q hQ.continuous K 0 L₀ := by
    intro B hB
    have hb (x : Plane) (hx : x ∈ sphere B.center B.radius) : Q x ∈ vacuum a :=
      hVac x (ball_subset_closedBall (hInside₀ B hB (sphere_subset_closedBall hx)))
        (diskBoundary_avoids_defect_of_pairwise_cover hSep₀ hCov₀ hB x hx)
    refine ⟨hb, ?_⟩
    rw [zero_mul]
    exact integral_nonneg (planarSmoothDirichletDensity_nonneg Q)
  obtain ⟨M, hPhases₀, hSep⟩ := exists_planarDiskPhases_of_pairwise L₀ hSep₀ 0 T hT
  have hPhases : Relation.ReflTransGen PlanarDiskPhase (0, L₀) (T, M) := by rwa [zero_add] at hPhases₀
  have hReach := hReach₀.trans (planarDiskPhases_evolve hPhases)
  have hCov := planarDiskEvolution_preserves_cover hReach hcover
  have hInside : ∀ r : ℝ × List PlanarDisk, Relation.ReflTransGen PlanarDiskPhase (0, L₀) r →
      r.1 ≤ T → ∀ B ∈ r.2, B.closed ⊆ unitPlanarDisk.closed := by
    rintro ⟨t, D⟩ hD ht B hB
    have h := planarDiskEvolution_closed_subset_unitDisk hL hR hcenter
      (hReach₀.trans (planarDiskPhases_evolve hD)) ht
    exact (h B hB).trans ball_subset_closedBall
  have hInv := planarDiskPhases_preserve_energyInvariant a Q hQ K hK unitPlanarDisk hVac hPhases
    le_rfl hCov₀ hInside hInv₀
  let A (j : M.toFinset) := j.val
  have hinClosed := planarDiskEvolution_closed_subset_unitDisk hL hR hcenter hReach le_rfl
  have hin (j : M.toFinset) : (A j).interior ⊆ unitPlanarDisk.interior :=
    ball_subset_closedBall.trans (hinClosed (A j) (List.mem_toFinset.mp j.property))
  have hsep : Pairwise (fun i j : M.toFinset => Disjoint (A i).interior (A j).interior) := by
    intro i j hij
    have hd := list_pairwise_rel_of_mem_of_ne (fun {_ _} hh => hh.symm) hSep
      (List.mem_toFinset.mp i.property) (List.mem_toFinset.mp j.property)
      (fun hh => hij (Subtype.ext hh))
    exact hd.mono ball_subset_closedBall ball_subset_closedBall
  have hFinalCover : K ∩ unitPlanarDisk.closed ⊆ ⋃ j : M.toFinset, (A j).interior := by
    intro x hx
    obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.mp (hCov hx.1)
    exact mem_iUnion.mpr ⟨⟨B, List.mem_toFinset.mpr hB⟩, hxB⟩
  refine planarDisk_merger_energy_invariant a Q hQ K hK unitPlanarDisk A hin hsep hFinalCover hVac T hT ?_
  intro j
  obtain ⟨_, hEnergy⟩ := hInv (A j) (List.mem_toFinset.mp j.property)
  exact hEnergy

end Thesis
