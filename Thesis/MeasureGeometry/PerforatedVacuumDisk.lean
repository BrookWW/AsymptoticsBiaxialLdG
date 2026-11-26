module

public import Thesis.MeasureGeometry.PlanarVacuumAnnulus

/-! Quaternion splitting charges on the boundaries of a perforated planar disk. -/

@[expose] public section

noncomputable section

open HarmonicMaps Metric Set Topology

namespace Thesis

/-- The native conical parametrization of the closed disk. -/
def diskCone (B : PlanarDisk) (p : unitInterval × NativeCircle) : B.closed :=
  ⟨B.center + ((1 - p.1.val) * B.radius) • p.2.val, by
    have hρ : 0 ≤ (1 - p.1.val) * B.radius := mul_nonneg (sub_nonneg.mpr p.1.property.2) B.radius_pos.le
    change dist (B.center + ((1 - p.1.val) * B.radius) • p.2.val) B.center ≤ B.radius
    rw [dist_planarCircle B.center hρ p.2]
    nlinarith [mul_nonneg p.1.property.1 B.radius_pos.le]⟩

theorem continuous_diskCone (B : PlanarDisk) : Continuous (diskCone B) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : unitInterval × NativeCircle => B.center + ((1 - p.1.val) * B.radius) • p.2.val)
  fun_prop

private theorem diskCone_surjective (B : PlanarDisk) : Function.Surjective (diskCone B) := by
  intro x
  by_cases hx : x.val = B.center
  · refine ⟨(1, nativeCircleLoopBase), Subtype.ext ?_⟩
    change B.center + ((1 - 1) * B.radius) • nativeCircleLoopBase.val = x.val
    simp [hx]
  let ρ := dist x.val B.center
  have hρ : 0 < ρ := dist_pos.mpr hx
  have hρr : ρ ≤ B.radius := x.property
  let z : NativeCircle := ⟨ρ⁻¹ • (x.val - B.center), by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le), ← dist_eq_norm]
    exact inv_mul_cancel₀ hρ.ne'⟩
  let t : unitInterval := ⟨1 - ρ / B.radius,
    sub_nonneg.mpr ((div_le_one B.radius_pos).2 hρr), sub_le_self _ (div_nonneg hρ.le B.radius_pos.le)⟩
  refine ⟨(t, z), Subtype.ext ?_⟩
  have hr : (1 - t.val) * B.radius = ρ := by
    change (1 - (1 - ρ / B.radius)) * B.radius = ρ
    rw [sub_sub_cancel, div_mul_cancel₀ _ B.radius_pos.ne']
  change B.center + ((1 - t.val) * B.radius) • (ρ⁻¹ • (x.val - B.center)) = x.val
  rw [hr, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_comm B.center, sub_add_cancel]

private theorem diskCone_homotopy_eq_of_eq {X : Type*} [TopologicalSpace X]
    {f : C(NativeCircle, X)} {q : X} (H : f.Homotopy (ContinuousMap.const NativeCircle q))
    (B : PlanarDisk) (p p' : unitInterval × NativeCircle) (he : diskCone B p = diskCone B p') :
    H p = H p' := by
  have hρ (w : unitInterval × NativeCircle) : dist (diskCone B w).val B.center = (1 - w.1.val) * B.radius :=
    dist_planarCircle B.center (mul_nonneg (sub_nonneg.mpr w.1.property.2) B.radius_pos.le) w.2
  have ht : p.1 = p'.1 := by
    apply Subtype.ext
    have he' := (hρ p).symm.trans ((congrArg (fun z : B.closed => dist z.val B.center) he).trans (hρ p'))
    exact sub_right_injective (mul_right_cancel₀ B.radius_pos.ne' he')
  rcases p with ⟨s, z⟩
  rcases p' with ⟨s', z'⟩
  change s = s' at ht
  subst s'
  by_cases h : s = 1
  · subst s
    exact (H.map_one_left z).trans (H.map_one_left z').symm
  · have hpos : 0 < (1 - s.val) * B.radius := mul_pos
      (sub_pos.mpr (lt_of_le_of_ne s.property.2 (fun he => h (Subtype.ext he)))) B.radius_pos
    have hs := add_left_cancel (congrArg Subtype.val he)
    change ((1 - s.val) * B.radius) • z.val = ((1 - s.val) * B.radius) • z'.val at hs
    have hz : z = z' := by
      apply Subtype.ext
      have hint := congrArg (fun x : Plane => ((1 - s.val) * B.radius)⁻¹ • x) hs
      simpa only [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul] using hint
    rw [hz]

/-- A null-homotopic native circle map extends continuously over the actual closed disk. -/
theorem exists_nativeClosedDisk_fill_of_nullHomotopic {X : Type*} [TopologicalSpace X]
    (B : PlanarDisk) (f : C(NativeCircle, X)) (q : X)
    (hf : f.Homotopic (ContinuousMap.const NativeCircle q)) :
    ∃ U : C(B.closed, X), ∀ z : NativeCircle, U (diskCone B (0, z)) = f z := by
  obtain ⟨H⟩ := hf
  letI : CompactSpace NativeCircle := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hQuot : IsQuotientMap (diskCone B) :=
    (continuous_diskCone B).isClosedMap.isQuotientMap (continuous_diskCone B) (diskCone_surjective B)
  let U (x : B.closed) := H (Classical.choose (diskCone_surjective B x))
  have hU (p : unitInterval × NativeCircle) : U (diskCone B p) = H p :=
    diskCone_homotopy_eq_of_eq H B _ _ (Classical.choose_spec (diskCone_surjective B (diskCone B p)))
  have hcont : Continuous U := hQuot.continuous_iff.2 (by
    rw [show U ∘ diskCone B = H from funext hU]
    exact H.continuous)
  exact ⟨⟨U, hcont⟩, fun z => (hU (0, z)).trans (H.map_zero_left z)⟩

@[simp] theorem diskCone_zero_val (B : PlanarDisk) (z : NativeCircle) :
    (diskCone B (0, z)).val = B.center + B.radius • z.val := by
  change B.center + ((1 - 0) * B.radius) • z.val = B.center + B.radius • z.val
  rw [sub_zero, one_mul]

theorem diskCone_boundary_mem_sphere (B : PlanarDisk) (z : NativeCircle) :
    (diskCone B (0, z)).val ∈ sphere B.center B.radius := by
  rw [diskCone_zero_val, mem_sphere, dist_planarCircle B.center B.radius_pos.le z]

theorem exists_diskCone_boundary_of_mem_sphere (B : PlanarDisk) {x : Plane}
    (hx : x ∈ sphere B.center B.radius) : ∃ z : NativeCircle, (diskCone B (0, z)).val = x := by
  let x' : B.closed := ⟨x, sphere_subset_closedBall hx⟩
  obtain ⟨⟨t, z⟩, h⟩ := diskCone_surjective B x'
  have hρ : dist (diskCone B (t, z)).val B.center = (1 - t.val) * B.radius :=
    dist_planarCircle B.center (mul_nonneg (sub_nonneg.mpr t.property.2) B.radius_pos.le) z
  rw [h] at hρ
  have heq : B.radius = (1 - t.val) * B.radius := (mem_sphere.mp hx).symm.trans hρ
  have ht : t = 0 := by
    apply Subtype.ext
    change t.val = 0
    have hed : t.val * B.radius = 0 := by linarith only [heq]
    exact (mul_eq_zero.mp hed).resolve_right B.radius_pos.ne'
  exact ⟨z, congrArg Subtype.val (ht ▸ h)⟩

/-- The closed outer disk with the specified open inner disks removed. -/
def perforatedPlanarDisk {ι : Type*} (B : PlanarDisk) (D : ι → PlanarDisk) (I : Finset ι) : Set Plane :=
  B.closed \ ⋃ i ∈ I, (D i).interior

private theorem perforatedPlanarDisk_antitone {ι : Type*} (B : PlanarDisk) (D : ι → PlanarDisk)
    {I J : Finset ι} (h : I ⊆ J) :
    perforatedPlanarDisk B D J ⊆ perforatedPlanarDisk B D I := by
  intro x hx
  refine ⟨hx.1, fun hx' => hx.2 ?_⟩
  obtain ⟨i, hi, hi'⟩ := mem_iUnion₂.mp hx'
  exact mem_iUnion₂.mpr ⟨i, h hi, hi'⟩

private theorem perforatedPlanarDisk_insert {ι : Type*} [DecidableEq ι]
    (B : PlanarDisk) (D : ι → PlanarDisk) (I : Finset ι) (i : ι) :
    perforatedPlanarDisk B D (insert i I) = perforatedPlanarDisk B D I \ (D i).interior := by
  ext x
  simp only [perforatedPlanarDisk, mem_sdiff, mem_iUnion₂, Finset.mem_insert]
  grind

theorem outerSphere_subset_perforatedPlanarDisk {ι : Type*}
    (B : PlanarDisk) (D : ι → PlanarDisk) (I : Finset ι)
    (hin : ∀ i ∈ I, (D i).closed ⊆ B.interior) :
    sphere B.center B.radius ⊆ perforatedPlanarDisk B D I := by
  intro x hx
  refine ⟨sphere_subset_closedBall hx, ?_⟩
  intro hh
  obtain ⟨i, hi, hi'⟩ := mem_iUnion₂.mp hh
  have hin' : x ∈ B.interior := hin i hi (ball_subset_closedBall hi')
  exact lt_irrefl _ ((mem_sphere.mp hx) ▸ (mem_ball.mp hin'))

theorem innerSphere_subset_perforatedPlanarDisk {ι : Type*}
    (B : PlanarDisk) (D : ι → PlanarDisk) (I : Finset ι)
    (hin : ∀ i, (D i).closed ⊆ B.interior)
    (hsep : Pairwise (fun i j => Disjoint (D i).closed (D j).closed)) (i : ι) :
    sphere (D i).center (D i).radius ⊆ perforatedPlanarDisk B D I := by
  intro x hx
  have hD : x ∈ (D i).closed := sphere_subset_closedBall hx
  refine ⟨ball_subset_closedBall (hin i hD), ?_⟩
  intro hbad
  obtain ⟨j, hj, hj'⟩ := mem_iUnion₂.mp hbad
  by_cases he : i = j
  · subst j
    exact lt_irrefl _ ((mem_sphere.mp hx) ▸ (mem_ball.mp hj'))
  · exact Set.disjoint_left.mp (hsep he) hD (ball_subset_closedBall hj')

/-- The actual counterclockwise circle trace of a map continuous on a set containing its boundary. -/
def planarBoundaryTrace {X : Type*} [TopologicalSpace X] (B : PlanarDisk)
    (u : Plane → X) {K : Set Plane} (hu : ContinuousOn u K)
    (hB : sphere B.center B.radius ⊆ K) : C(NativeCircle, X) := by
  have hparam : Continuous (fun z : NativeCircle => (diskCone B (0, z)).val) :=
    continuous_subtype_val.comp ((continuous_diskCone B).comp (continuous_const.prodMk continuous_id))
  refine ⟨fun z => u (diskCone B (0, z)).val, ?_⟩
  rw [← continuousOn_univ]
  exact hu.comp hparam.continuousOn (fun z _ => hB (diskCone_boundary_mem_sphere B z))

private theorem exists_fill_one_planarHole {X ι : Type*} [TopologicalSpace X] [DecidableEq ι]
    (B : PlanarDisk) (D : ι → PlanarDisk) (I : Finset ι) (i : ι) (u : Plane → X)
    (hu : ContinuousOn u (perforatedPlanarDisk B D (insert i I)))
    (V : C((D i).closed, X))
    (hV : ∀ z : NativeCircle, V (diskCone (D i) (0, z)) = u (diskCone (D i) (0, z)).val) :
    ∃ v : Plane → X, ContinuousOn v (perforatedPlanarDisk B D I) ∧
      EqOn v u (perforatedPlanarDisk B D (insert i I)) := by
  classical
  let U (x : Plane) := if hx : x ∈ (D i).closed then V ⟨x, hx⟩ else u x
  have hU : ContinuousOn U (D i).closed := by
    rw [continuousOn_iff_continuous_restrict]
    have hEq : (fun x : (D i).closed => U x.val) = V := by
      funext x
      change (if hx : x.val ∈ (D i).closed then V ⟨x.val, hx⟩ else u x.val) = V x
      rw [dif_pos x.property]
    change Continuous (fun x : (D i).closed => U x.val)
    rw [hEq]
    exact V.continuous
  have hBoundary : EqOn U u (sphere (D i).center (D i).radius) := by
    intro x hx
    obtain ⟨z, rfl⟩ := exists_diskCone_boundary_of_mem_sphere (D i) hx
    change (if h : (diskCone (D i) (0, z)).val ∈ (D i).closed then
      V ⟨(diskCone (D i) (0, z)).val, h⟩ else u (diskCone (D i) (0, z)).val) =
        u (diskCone (D i) (0, z)).val
    rw [dif_pos (diskCone (D i) (0, z)).property]
    exact hV z
  let v := (D i).closed.piecewise U u
  have hClosed : IsClosed (D i).closed := isClosed_closedBall
  have hFront : frontier (D i).closed = sphere (D i).center (D i).radius :=
    frontier_closedBall' _ _
  have hCompl : closure (D i).closedᶜ = (D i).interiorᶜ := by
    rw [closure_compl, show interior (D i).closed = (D i).interior from interior_closedBall' _ _]
  have hcts : ContinuousOn v (perforatedPlanarDisk B D I) := by
    apply ContinuousOn.piecewise
    · intro x hx
      exact hBoundary (hFront ▸ hx.2)
    · rw [hClosed.closure_eq]
      exact hU.mono inter_subset_right
    · rw [hCompl, ← Set.sdiff_eq, ← perforatedPlanarDisk_insert]
      exact hu
  refine ⟨v, hcts, ?_⟩
  intro x hx
  by_cases hc : x ∈ (D i).closed
  · have hOutside : x ∉ (D i).interior := by
      rw [perforatedPlanarDisk_insert] at hx
      exact hx.2
    have hs : x ∈ sphere (D i).center (D i).radius := by
      rw [← closedBall_sdiff_ball]
      exact ⟨hc, hOutside⟩
    exact (Set.piecewise_eq_of_mem _ _ _ hc).trans (hBoundary hs)
  · exact Set.piecewise_eq_of_notMem _ _ _ hc

/-- Paste finitely many continuous disk fillings, retaining the map on the original domain. -/
theorem exists_fill_planarHoles {X ι : Type*} [TopologicalSpace X] [DecidableEq ι]
    (B : PlanarDisk) (D : ι → PlanarDisk) (F I : Finset ι) (u : Plane → X)
    (hin : ∀ i, (D i).closed ⊆ B.interior)
    (hsep : Pairwise (fun i j => Disjoint (D i).closed (D j).closed))
    (hu : ContinuousOn u (perforatedPlanarDisk B D (F ∪ I)))
    (hfill : ∀ i ∈ F, ∃ V : C((D i).closed, X),
      ∀ z : NativeCircle, V (diskCone (D i) (0, z)) = u (diskCone (D i) (0, z)).val) :
    ∃ v : Plane → X, ContinuousOn v (perforatedPlanarDisk B D I) ∧
      EqOn v u (perforatedPlanarDisk B D (F ∪ I)) := by
  induction F using Finset.induction_on generalizing I with
  | empty =>
      rw [Finset.empty_union] at hu ⊢
      exact ⟨u, hu, fun _ _ => rfl⟩
  | @insert i F hi ih =>
      have hsets : insert i F ∪ I = F ∪ insert i I := by
        ext j
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      rw [hsets] at hu ⊢
      obtain ⟨w, hw, hwEq⟩ := ih (I := insert i I) hu
        (fun j hj => hfill j (Finset.mem_insert_of_mem hj))
      obtain ⟨V, hV⟩ := hfill i (Finset.mem_insert_self _ _)
      have hV' (z : NativeCircle) : V (diskCone (D i) (0, z)) = w (diskCone (D i) (0, z)).val := by
        refine (hV z).trans (hwEq ?_).symm
        apply innerSphere_subset_perforatedPlanarDisk B D (F ∪ insert i I) hin hsep i
        exact diskCone_boundary_mem_sphere (D i) z
      obtain ⟨v, hv, hvEq⟩ := exists_fill_one_planarHole B D I i w hw V hV'
      have hsub : perforatedPlanarDisk B D (F ∪ insert i I) ⊆ perforatedPlanarDisk B D (insert i I) :=
        perforatedPlanarDisk_antitone B D Finset.subset_union_right
      exact ⟨v, hv, (hvEq.mono hsub).trans hwEq⟩

private theorem radius_add_dist_le_of_closed_subset {B D : PlanarDisk} (hin : D.closed ⊆ B.closed) :
    D.radius + dist D.center B.center ≤ B.radius := by
  by_cases h : D.center = B.center
  · have := hin (diskCone D (0, nativeCircleLoopBase)).property
    have hD := mem_sphere.mp (diskCone_boundary_mem_sphere D nativeCircleLoopBase)
    change dist (diskCone D (0, nativeCircleLoopBase)).val B.center ≤ B.radius at this
    rw [← h, hD] at this
    simpa only [h, dist_self, add_zero] using this
  · let d := dist D.center B.center
    have hd : 0 < d := dist_pos.mpr h
    let z : NativeCircle := ⟨d⁻¹ • (D.center - B.center), by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le), ← dist_eq_norm]
      exact inv_mul_cancel₀ hd.ne'⟩
    have hOut := hin (diskCone D (0, z)).property
    have hvec : (diskCone D (0, z)).val - B.center = (1 + D.radius * d⁻¹) • (D.center - B.center) := by
      rw [diskCone_zero_val]
      change D.center + D.radius • (d⁻¹ • (D.center - B.center)) - B.center = _
      rw [smul_smul]
      module
    have hscalar : 0 ≤ 1 + D.radius * d⁻¹ :=
      add_nonneg zero_le_one (mul_nonneg D.radius_pos.le (inv_nonneg.mpr hd.le))
    change dist (diskCone D (0, z)).val B.center ≤ B.radius at hOut
    rw [dist_eq_norm, hvec, norm_smul, Real.norm_of_nonneg hscalar, ← dist_eq_norm] at hOut
    have hRatio : (1 + D.radius * d⁻¹) * d = D.radius + d := by field_simp [hd.ne']; ring
    change (1 + D.radius * d⁻¹) * d ≤ B.radius at hOut
    rwa [hRatio] at hOut

private def nestedCircularSweep (B D : PlanarDisk) (p : unitInterval × NativeCircle) : Plane :=
  (1 - p.1.val) • D.center + p.1.val • B.center +
    ((1 - p.1.val) * D.radius + p.1.val * B.radius) • p.2.val

private theorem nestedCircularSweep_mem_annulus (B D : PlanarDisk)
    (hin : D.radius + dist D.center B.center ≤ B.radius) (p : unitInterval × NativeCircle) :
    nestedCircularSweep B D p ∈ B.closed \ D.interior := by
  let t := p.1.val
  let s := 1 - t
  let r := s * D.radius + t * B.radius
  have ht : 0 ≤ t := p.1.property.1
  have hs : 0 ≤ s := sub_nonneg.mpr p.1.property.2
  have hr : 0 ≤ r := add_nonneg (mul_nonneg hs D.radius_pos.le) (mul_nonneg ht B.radius_pos.le)
  have hz : ‖p.2.val‖ = 1 := mem_sphere_zero_iff_norm.mp p.2.property
  have hOut : nestedCircularSweep B D p - B.center =
      s • (D.center - B.center) + r • p.2.val := by
    change s • D.center + t • B.center + r • p.2.val - B.center = _
    dsimp only [s]
    module
  have hInn : nestedCircularSweep B D p - D.center =
      t • (B.center - D.center) + r • p.2.val := by
    change s • D.center + t • B.center + r • p.2.val - D.center = _
    dsimp only [s]
    module
  constructor
  · change dist (nestedCircularSweep B D p) B.center ≤ B.radius
    rw [dist_eq_norm, hOut]
    calc
      _ ≤ ‖s • (D.center - B.center)‖ + ‖r • p.2.val‖ := norm_add_le _ _
      _ = s * dist D.center B.center + r := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg hr, hz, mul_one, dist_eq_norm]
      _ = s * (D.radius + dist D.center B.center) + t * B.radius := by dsimp only [r]; ring
      _ ≤ s * B.radius + t * B.radius := add_le_add (mul_le_mul_of_nonneg_left hin hs) le_rfl
      _ = _ := by dsimp only [s]; ring
  · change ¬ dist (nestedCircularSweep B D p) D.center < D.radius
    apply not_lt_of_ge
    have hlower : r ≤ dist (nestedCircularSweep B D p) D.center + t * dist D.center B.center := by
      calc
        _ = ‖r • p.2.val‖ := by rw [norm_smul, Real.norm_of_nonneg hr, hz, mul_one]
        _ = ‖(nestedCircularSweep B D p - D.center) - t • (B.center - D.center)‖ := by
          rw [hInn, add_comm, add_sub_cancel_right]
        _ ≤ ‖nestedCircularSweep B D p - D.center‖ + ‖t • (B.center - D.center)‖ := norm_sub_le _ _
        _ = _ := by rw [norm_smul, Real.norm_of_nonneg ht, ← dist_eq_norm, ← dist_eq_norm,
          dist_comm B.center D.center]
    have hrad : D.radius + t * dist D.center B.center ≤ r := by
      calc
        _ = s * D.radius + t * (D.radius + dist D.center B.center) := by dsimp only [s]; ring
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hin ht)
    exact (add_le_add_iff_right (t * dist D.center B.center)).mp (hrad.trans hlower)

/-- The inner and outer circle traces on a possibly nonconcentric closed annulus are freely homotopic. -/
theorem nestedPlanarBoundaries_homotopic {X : Type*} [TopologicalSpace X] (B D : PlanarDisk)
    (hOuter : sphere B.center B.radius ⊆ B.closed \ D.interior)
    (hInner : sphere D.center D.radius ⊆ B.closed \ D.interior)
    (hin : D.closed ⊆ B.closed) (u : Plane → X) (hu : ContinuousOn u (B.closed \ D.interior)) :
    (planarBoundaryTrace D u hu hInner).Homotopic (planarBoundaryTrace B u hu hOuter) := by
  have hct : Continuous (nestedCircularSweep B D) := by unfold nestedCircularSweep; fun_prop
  have Hcts : Continuous (fun p => u (nestedCircularSweep B D p)) := by
    rw [← continuousOn_univ]
    exact hu.comp hct.continuousOn fun p _ =>
      nestedCircularSweep_mem_annulus B D (radius_add_dist_le_of_closed_subset hin) p
  refine ⟨⟨⟨fun p => u (nestedCircularSweep B D p), Hcts⟩, ?_, ?_⟩⟩
  · intro z
    change u (nestedCircularSweep B D (0, z)) = u (diskCone D (0, z)).val
    rw [diskCone_zero_val]
    congr 1
    change (1 - 0 : ℝ) • D.center + (0 : ℝ) • B.center +
      (((1 - 0 : ℝ) * D.radius + 0 * B.radius) • z.val) = _
    simp
  · intro z
    change u (nestedCircularSweep B D (1, z)) = u (diskCone B (0, z)).val
    rw [diskCone_zero_val]
    congr 1
    change (1 - 1 : ℝ) • D.center + (1 : ℝ) • B.center +
      (((1 - 1 : ℝ) * D.radius + 1 * B.radius) • z.val) = _
    simp

/-- A map continuous on the closed disk contracts its actual boundary trace. -/
theorem planarBoundaryTrace_homotopic_const {X : Type*} [TopologicalSpace X]
    (B : PlanarDisk) (u : Plane → X) (hu : ContinuousOn u B.closed) :
    (planarBoundaryTrace B u hu sphere_subset_closedBall).Homotopic
      (ContinuousMap.const NativeCircle (u B.center)) := by
  have hct : Continuous (fun p : unitInterval × NativeCircle => u (diskCone B p).val) := by
    rw [← continuousOn_univ]
    exact hu.comp (continuous_subtype_val.comp (continuous_diskCone B)).continuousOn
      fun p _ => (diskCone B p).property
  refine ⟨⟨⟨fun p => u (diskCone B p).val, hct⟩, fun _ => rfl, ?_⟩⟩
  intro z
  have hvec : (diskCone B (1, z)).val = B.center := by
    change B.center + ((1 - 1) * B.radius) • z.val = B.center
    simp
  change u (diskCone B (1, z)).val = u B.center
  rw [hvec]

private theorem planarBoundaryTrace_eq_of_eqOn {X : Type*} [TopologicalSpace X]
    (B : PlanarDisk) (u v : Plane → X) {K L : Set Plane}
    (hu : ContinuousOn u K) (hv : ContinuousOn v L) (hB : sphere B.center B.radius ⊆ K)
    (hB' : sphere B.center B.radius ⊆ L) (hEq : EqOn v u K) :
    planarBoundaryTrace B v hv hB' = planarBoundaryTrace B u hu hB :=
  ContinuousMap.ext fun z => hEq (hB (diskCone_boundary_mem_sphere B z))

theorem perforatedOuter_null_of_inner_null {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (B : PlanarDisk) (D : ι → PlanarDisk)
    (hin : ∀ i, (D i).closed ⊆ B.interior)
    (hsep : Pairwise (fun i j => Disjoint (D i).closed (D j).closed))
    (u : Plane → X) (hu : ContinuousOn u (perforatedPlanarDisk B D Finset.univ)) :
    let outer := planarBoundaryTrace B u hu
      (outerSphere_subset_perforatedPlanarDisk B D Finset.univ (fun i _ => hin i))
    let inner (i : ι) := planarBoundaryTrace (D i) u hu
      (innerSphere_subset_perforatedPlanarDisk B D Finset.univ hin hsep i)
    (∀ i, (inner i).Homotopic (ContinuousMap.const NativeCircle (inner i nativeCircleLoopBase))) →
    ∃ q : X, outer.Homotopic (ContinuousMap.const NativeCircle q) := by
  classical
  intro outer inner hNull
  have hFill (i : ι) : ∃ V : C((D i).closed, X),
      ∀ z : NativeCircle, V (diskCone (D i) (0, z)) = u (diskCone (D i) (0, z)).val :=
    exists_nativeClosedDisk_fill_of_nullHomotopic (D i) (inner i)
      (inner i nativeCircleLoopBase) (hNull i)
  have hu' : ContinuousOn u (perforatedPlanarDisk B D (Finset.univ ∪ ∅)) := by simpa using hu
  obtain ⟨v, hv, hEq⟩ := exists_fill_planarHoles B D Finset.univ ∅ u hin hsep hu' (fun i _ => hFill i)
  have hv' : ContinuousOn v B.closed := by simpa [perforatedPlanarDisk] using hv
  have hEq' : EqOn v u (perforatedPlanarDisk B D Finset.univ) := by simpa using hEq
  have he : planarBoundaryTrace B v hv' sphere_subset_closedBall = outer :=
    planarBoundaryTrace_eq_of_eqOn B u v hu hv'
      (outerSphere_subset_perforatedPlanarDisk B D Finset.univ (fun i _ => hin i)) _ hEq'
  exact ⟨v B.center, he ▸ planarBoundaryTrace_homotopic_const B v hv'⟩

theorem perforatedOuter_homotopic_one_inner {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (B : PlanarDisk) (D : ι → PlanarDisk)
    (hin : ∀ i, (D i).closed ⊆ B.interior)
    (hsep : Pairwise (fun i j => Disjoint (D i).closed (D j).closed))
    (u : Plane → X) (hu : ContinuousOn u (perforatedPlanarDisk B D Finset.univ)) (i : ι) :
    let outer := planarBoundaryTrace B u hu
      (outerSphere_subset_perforatedPlanarDisk B D Finset.univ (fun i _ => hin i))
    let inner (j : ι) := planarBoundaryTrace (D j) u hu
      (innerSphere_subset_perforatedPlanarDisk B D Finset.univ hin hsep j)
    (∀ j, j ≠ i → (inner j).Homotopic (ContinuousMap.const NativeCircle (inner j nativeCircleLoopBase))) →
    (inner i).Homotopic outer := by
  classical
  intro outer inner hNull
  let F := (Finset.univ : Finset ι).erase i
  have hall : F ∪ {i} = Finset.univ := by
    ext j
    simp only [F, Finset.mem_union, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_singleton, iff_true]
    tauto
  have hFill (j : ι) (hj : j ∈ F) : ∃ V : C((D j).closed, X),
      ∀ z : NativeCircle, V (diskCone (D j) (0, z)) = u (diskCone (D j) (0, z)).val :=
    exists_nativeClosedDisk_fill_of_nullHomotopic (D j) (inner j)
      (inner j nativeCircleLoopBase) (hNull j (Finset.mem_erase.mp hj).1)
  have hu' : ContinuousOn u (perforatedPlanarDisk B D (F ∪ {i})) := hall ▸ hu
  obtain ⟨v, hv, hEq⟩ := exists_fill_planarHoles B D F {i} u hin hsep hu' hFill
  have hSingleton : perforatedPlanarDisk B D {i} = B.closed \ (D i).interior := by
    simp [perforatedPlanarDisk]
  have hv' : ContinuousOn v (B.closed \ (D i).interior) := hSingleton ▸ hv
  have hEq' : EqOn v u (perforatedPlanarDisk B D Finset.univ) := hall ▸ hEq
  have hoSub : sphere B.center B.radius ⊆ B.closed \ (D i).interior :=
    hSingleton ▸ outerSphere_subset_perforatedPlanarDisk B D {i} (fun j _ => hin j)
  have hiSub : sphere (D i).center (D i).radius ⊆ B.closed \ (D i).interior :=
    hSingleton ▸ innerSphere_subset_perforatedPlanarDisk B D {i} hin hsep i
  have H := nestedPlanarBoundaries_homotopic B (D i) hoSub hiSub
    ((hin i).trans ball_subset_closedBall) v hv'
  have h₀ : planarBoundaryTrace B v hv' hoSub = outer :=
    planarBoundaryTrace_eq_of_eqOn B u v hu hv'
      (outerSphere_subset_perforatedPlanarDisk B D Finset.univ (fun j _ => hin j)) _ hEq'
  have hi : planarBoundaryTrace (D i) v hv' hiSub = inner i :=
    planarBoundaryTrace_eq_of_eqOn (D i) u v hu hv'
      (innerSphere_subset_perforatedPlanarDisk B D Finset.univ hin hsep i) _ hEq'
  rw [h₀, hi] at H
  exact H

private theorem splittingCost_nonneg (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) :
    0 ≤ vacuumSplittingCost a v g := by
  rw [vacuumSplittingCost_eq]
  exact mul_nonneg (kappaStar_pos a).le (Nat.cast_nonneg _)

private theorem splittingCost_le_two (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) :
    vacuumSplittingCost a v g ≤ 2 * kappaStar a := by
  by_cases hi : g = 1
  · rw [hi, vacuumSplittingCost_one]
    positivity [kappaStar_pos a]
  by_cases hl : IsLightQuaternion g
  · rw [vacuumSplittingCost_light a v hl]
    linarith only [(kappaStar_pos a).le]
  rw [vacuumSplittingCost_nontrivial_nonlight a v hi hl]

private theorem kappa_le_splittingCost_of_ne_one (a : BulkCoefficients) (v : Sphere3)
    (g : QuaternionGroup 2) (hg : g ≠ 1) : kappaStar a ≤ vacuumSplittingCost a v g := by
  by_cases hl : IsLightQuaternion g
  · rw [vacuumSplittingCost_light a v hl]
  rw [vacuumSplittingCost_nontrivial_nonlight a v hg hl]
  linarith only [(kappaStar_pos a).le]

private theorem nativeVacuumLoopWord_eq_one_of_const_homotopy (a : BulkCoefficients)
    {f : C(NativeCircle, vacuum a)} (v : Sphere3)
    (hv : vacuumQuaternionProjection a v = f nativeCircleLoopBase)
    (h : ∃ A : vacuum a, f.Homotopic (ContinuousMap.const NativeCircle A)) :
    nativeVacuumLoopWord a f v hv = 1 := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨w, hw⟩ := vacuumQuaternionProjection_surjective a A
  have hConj := (nativeVacuum_homotopic_iff_isConj a f (ContinuousMap.const NativeCircle A) v w hv hw).1 hA
  rw [nativeVacuumLoopWord_const a w A hw] at hConj
  exact isConj_one_left.mp hConj

/-- For an actual continuous map on a perforated disk, the outer splitting
charge is bounded by the sum of the inner splitting charges. -/
theorem perforatedVacuumDisk_outerSplittingCost_le_sum (a : BulkCoefficients)
    {ι : Type*} [Fintype ι] (B : PlanarDisk) (D : ι → PlanarDisk)
    (hin : ∀ i, (D i).closed ⊆ B.interior)
    (hsep : Pairwise (fun i j => Disjoint (D i).closed (D j).closed))
    (u : Plane → vacuum a) (hu : ContinuousOn u (perforatedPlanarDisk B D Finset.univ)) :
    let outer := planarBoundaryTrace B u hu
      (outerSphere_subset_perforatedPlanarDisk B D Finset.univ (fun i _ => hin i))
    let inner (i : ι) := planarBoundaryTrace (D i) u hu
      (innerSphere_subset_perforatedPlanarDisk B D Finset.univ hin hsep i)
    ∀ (v : Sphere3) (hv : vacuumQuaternionProjection a v = outer nativeCircleLoopBase)
      (w : ι → Sphere3) (hw : ∀ i, vacuumQuaternionProjection a (w i) = inner i nativeCircleLoopBase),
      vacuumSplittingCost a v (nativeVacuumLoopWord a outer v hv) ≤
        ∑ i, vacuumSplittingCost a (w i) (nativeVacuumLoopWord a (inner i) (w i) (hw i)) := by
  classical
  intro outer inner v hv w hw
  let g (i : ι) := nativeVacuumLoopWord a (inner i) (w i) (hw i)
  let cost (i : ι) := vacuumSplittingCost a (w i) (g i)
  have hNonNeg (i : ι) : 0 ≤ cost i := splittingCost_nonneg _ _ _
  have hNull (i : ι) (hg : g i = 1) :
      (inner i).Homotopic (ContinuousMap.const NativeCircle (inner i nativeCircleLoopBase)) :=
    (nativeVacuum_homotopic_const_iff a (inner i) (w i) (hw i)).2 hg
  by_cases hAll : ∀ i, g i = 1
  · have hOuter := perforatedOuter_null_of_inner_null B D hin hsep u hu (fun i => hNull i (hAll i))
    rw [nativeVacuumLoopWord_eq_one_of_const_homotopy a v hv hOuter, vacuumSplittingCost_one]
    exact Finset.sum_nonneg fun i _ => hNonNeg i
  push Not at hAll
  obtain ⟨i, hi⟩ := hAll
  by_cases hOnly : ∀ j, j ≠ i → g j = 1
  · have H := perforatedOuter_homotopic_one_inner B D hin hsep u hu i
      (fun j hj => hNull j (hOnly j hj))
    have heq : cost i = vacuumSplittingCost a v (nativeVacuumLoopWord a outer v hv) :=
      nativeVacuumLoop_splittingCost_homotopic a H (w i) v (hw i) hv
    rw [← heq]
    exact Finset.single_le_sum (f := cost) (fun j _ => hNonNeg j) (Finset.mem_univ i)
  push Not at hOnly
  obtain ⟨j, hji, hj⟩ := hOnly
  calc
    _ ≤ 2 * kappaStar a := splittingCost_le_two a v _
    _ = kappaStar a + kappaStar a := two_mul _
    _ ≤ cost i + cost j := add_le_add (kappa_le_splittingCost_of_ne_one a (w i) (g i) hi)
      (kappa_le_splittingCost_of_ne_one a (w j) (g j) hj)
    _ = ∑ k ∈ ({i, j} : Finset ι), cost k := by
      simp [Finset.sum_insert, hji.symm]
    _ ≤ ∑ k, cost k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => hNonNeg k)

/-- If the other holes are trivial, the remaining inner and outer charges agree. -/
theorem perforatedVacuumDisk_singleCharge_eq_outer (a : BulkCoefficients)
    {ι : Type*} [Fintype ι] (B : PlanarDisk) (D : ι → PlanarDisk)
    (hin : ∀ i, (D i).closed ⊆ B.interior)
    (hsep : Pairwise (fun i j => Disjoint (D i).closed (D j).closed))
    (u : Plane → vacuum a) (hu : ContinuousOn u (perforatedPlanarDisk B D Finset.univ)) (i : ι) :
    let outer := planarBoundaryTrace B u hu
      (outerSphere_subset_perforatedPlanarDisk B D Finset.univ (fun i _ => hin i))
    let inner (j : ι) := planarBoundaryTrace (D j) u hu
      (innerSphere_subset_perforatedPlanarDisk B D Finset.univ hin hsep j)
    ∀ (v : Sphere3) (hv : vacuumQuaternionProjection a v = outer nativeCircleLoopBase)
      (w : ι → Sphere3) (hw : ∀ j, vacuumQuaternionProjection a (w j) = inner j nativeCircleLoopBase),
      (∀ j, j ≠ i → nativeVacuumLoopWord a (inner j) (w j) (hw j) = 1) →
      vacuumSplittingCost a (w i) (nativeVacuumLoopWord a (inner i) (w i) (hw i)) =
        vacuumSplittingCost a v (nativeVacuumLoopWord a outer v hv) := by
  intro outer inner v hv w hw hNull
  have H := perforatedOuter_homotopic_one_inner B D hin hsep u hu i fun j hj =>
    (nativeVacuum_homotopic_const_iff a (inner j) (w j) (hw j)).2 (hNull j hj)
  exact nativeVacuumLoop_splittingCost_homotopic a H (w i) v (hw i) hv

theorem perforatedVacuumDisk_outerCost_le_sum (a : BulkCoefficients) {ι : Type*} [Fintype ι]
    (B : PlanarDisk) (D : ι → PlanarDisk)
    (hin : ∀ i, (D i).closed ⊆ B.interior)
    (hsep : Pairwise (fun i j => Disjoint (D i).closed (D j).closed))
    (u : Plane → vacuum a) (hu : ContinuousOn u (perforatedPlanarDisk B D Finset.univ)) :
    let outer := planarBoundaryTrace B u hu
      (outerSphere_subset_perforatedPlanarDisk B D Finset.univ (fun i _ => hin i))
    let inner (i : ι) := planarBoundaryTrace (D i) u hu
      (innerSphere_subset_perforatedPlanarDisk B D Finset.univ hin hsep i)
    nativeVacuumCircleCost a outer ≤ ∑ i, nativeVacuumCircleCost a (inner i) := by
  intro outer inner
  obtain ⟨v, hv⟩ := vacuumQuaternionProjection_surjective a (outer nativeCircleLoopBase)
  choose w hw using fun i : ι => vacuumQuaternionProjection_surjective a (inner i nativeCircleLoopBase)
  rw [nativeVacuumCircleCost_eq a outer v hv]
  simp_rw [show ∀ i, nativeVacuumCircleCost a (inner i) =
    vacuumSplittingCost a (w i) (nativeVacuumLoopWord a (inner i) (w i) (hw i)) from
      fun i => nativeVacuumCircleCost_eq a (inner i) (w i) (hw i)]
  exact perforatedVacuumDisk_outerSplittingCost_le_sum a B D hin hsep u hu v hv w hw

end Thesis
