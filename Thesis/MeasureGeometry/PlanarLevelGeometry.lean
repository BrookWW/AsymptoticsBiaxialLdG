module

public import Thesis.MeasureGeometry.PlanarCoverRadius
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Subpath
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-! The finite disk covering estimate for bounded sublevel regions. -/

@[expose] public section

noncomputable section

open Filter Metric Set MeasureTheory Topology
open scoped ENNReal

namespace Thesis

private theorem plane_rank_gt_one : 1 < Module.rank ℝ Plane := by
  rw [← Module.finrank_eq_rank]
  simp [Plane, finrank_euclideanSpace]

private theorem joinedIn_sdiff_closedBall {U : Set Plane} {x y c : Plane} {r R : ℝ}
    (hxy : JoinedIn U x y) (hr : 0 ≤ r) (hR : r < R) (hx : R < dist x c) (hy : R < dist y c)
    (hsphere : sphere c R ⊆ U) : JoinedIn (U \ closedBall c r) x y := by
  obtain ⟨p, hp⟩ := hxy
  let f : unitInterval → ℝ := fun t => dist (p t) c
  have hf : Continuous f := p.continuous.dist continuous_const
  have h₀ : R < f 0 := by dsimp only [f]; rwa [p.source]
  have h₁ : R < f 1 := by dsimp only [f]; rwa [p.target]
  let T := {t : unitInterval | f t = R}
  have hT : IsCompact T := (isClosed_eq hf continuous_const).isCompact
  have hLeft (t : unitInterval) (ht : f t ≤ r) : ∃ s ∈ T, s < t := by
    have hRmem : R ∈ Icc (f t) (f 0) := ⟨ht.trans hR.le, h₀.le⟩
    obtain ⟨s, hst, hs⟩ := intermediate_value_Icc' (show (0 : unitInterval) ≤ t from t.property.1)
      hf.continuousOn hRmem
    exact ⟨s, hs, lt_of_le_of_ne hst.2 (fun heq => (ht.trans_lt hR).ne (heq ▸ hs))⟩
  have hRight (t : unitInterval) (ht : f t ≤ r) : ∃ s ∈ T, t < s := by
    have hRmem : R ∈ Icc (f t) (f 1) := ⟨ht.trans hR.le, h₁.le⟩
    obtain ⟨s, hst, hs⟩ := intermediate_value_Icc (show t ≤ (1 : unitInterval) from t.property.2)
      hf.continuousOn hRmem
    exact ⟨s, hs, lt_of_le_of_ne hst.1 (fun heq => (ht.trans_lt hR).ne (heq.symm ▸ hs))⟩
  rcases T.eq_empty_or_nonempty with hempty | hne
  · refine ⟨p, fun t => ⟨hp t, fun h => ?_⟩⟩
    obtain ⟨s, hs, _⟩ := hLeft t (mem_closedBall.mp h)
    exact (Set.notMem_empty s) (hempty ▸ hs)
  · obtain ⟨u, hu, humin⟩ := hT.exists_isMinOn hne (f := id) continuous_id.continuousOn
    obtain ⟨v, hv, hvmax⟩ := hT.exists_isMaxOn hne (f := id) continuous_id.continuousOn
    have humin' := isMinOn_iff.mp humin
    have hvmax' := isMaxOn_iff.mp hvmax
    have hOuter : sphere c R ⊆ U \ closedBall c r := by
      intro z hz
      exact ⟨hsphere hz, fun h => ((mem_closedBall.mp h).trans_lt hR).ne (mem_sphere.mp hz)⟩
    have hMiddle : JoinedIn (U \ closedBall c r) (p u) (p v) :=
      ((isPathConnected_sphere plane_rank_gt_one c (hr.trans hR.le)).joinedIn
        (p u) (mem_sphere.mpr hu) (p v) (mem_sphere.mpr hv)).mono hOuter
    have hBefore : JoinedIn (U \ closedBall c r) x (p u) := by
      refine ⟨(p.subpath 0 u).cast p.source.symm rfl, fun t => ?_⟩
      have ht : (p.subpath 0 u).cast p.source.symm rfl t ∈ range (p.subpath 0 u) :=
        ⟨t, rfl⟩
      rw [p.range_subpath_of_le 0 u u.property.1] at ht
      obtain ⟨s, hsu, hst⟩ := ht
      rw [← hst]
      refine ⟨hp s, fun h => ?_⟩
      obtain ⟨s', hs', hlt⟩ := hLeft s (mem_closedBall.mp h)
      exact (hlt.trans_le hsu.2).not_ge (humin' s' hs')
    have hAfter : JoinedIn (U \ closedBall c r) (p v) y := by
      refine ⟨(p.subpath v 1).cast rfl p.target.symm, fun t => ?_⟩
      have ht : (p.subpath v 1).cast rfl p.target.symm t ∈ range (p.subpath v 1) :=
        ⟨t, rfl⟩
      rw [p.range_subpath_of_le v 1 v.property.2] at ht
      obtain ⟨s, hvs, hst⟩ := ht
      rw [← hst]
      refine ⟨hp s, fun h => ?_⟩
      obtain ⟨s', hs', hlt⟩ := hRight s (mem_closedBall.mp h)
      exact (hvs.1.trans_lt hlt).not_ge (hvmax' s' hs')
    exact hBefore.trans (hMiddle.trans hAfter)

/-- The closed union of a finite family of planar disks. -/
def planarDiskClosedUnion (L : List PlanarDisk) : Set Plane :=
  ⋃ B ∈ L, B.closed

theorem isCompact_planarDiskClosedUnion (L : List PlanarDisk) : IsCompact (planarDiskClosedUnion L) := by
  induction L with
  | nil => simp [planarDiskClosedUnion]
  | cons B L ih =>
    rw [show planarDiskClosedUnion (B :: L) = B.closed ∪ planarDiskClosedUnion L by
      ext x
      simp [planarDiskClosedUnion, List.mem_cons]]
    exact (isCompact_closedBall _ _).union ih

private theorem exists_uniform_gap_disk (B : PlanarDisk) (L : List PlanarDisk) (R₀ : ℝ)
    (hR : B.radius < R₀) (hdisj : ∀ D ∈ L, Disjoint B.closed D.closed) :
    ∃ R, B.radius < R ∧ R < R₀ ∧ ∀ D ∈ L, R + D.radius < dist B.center D.center := by
  induction L generalizing R₀ with
  | nil =>
    obtain ⟨R, hBR, hRR₀⟩ := exists_between hR
    exact ⟨R, hBR, hRR₀, by simp⟩
  | cons D L ih =>
    have hBD : B.radius + D.radius < dist B.center D.center :=
      lt_of_not_ge fun h => (not_disjoint_iff_nonempty_inter.2 (PlanarDisk.closed_inter_nonempty_iff.2 h))
        (hdisj D (List.mem_cons_self ..))
    have hmin : B.radius < min R₀ (dist B.center D.center - D.radius) := lt_min hR (by linarith)
    obtain ⟨R, hBR, hRm, hRL⟩ := ih _ hmin (fun E hE => hdisj E (List.mem_cons_of_mem _ hE))
    refine ⟨R, hBR, hRm.trans_le (min_le_left _ _), ?_⟩
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hEL
    · linarith only [hRm.trans_le (min_le_right _ _)]
    · exact hRL E hEL

/-- The exterior of finitely many pairwise disjoint closed disks admits paths
between any two of its points. -/
theorem joinedIn_compl_planarDiskClosedUnion (L : List PlanarDisk)
    (hdisj : L.Pairwise fun B D => Disjoint B.closed D.closed) {x y : Plane}
    (hx : x ∉ planarDiskClosedUnion L) (hy : y ∉ planarDiskClosedUnion L) :
    JoinedIn (planarDiskClosedUnion L)ᶜ x y := by
  induction L with
  | nil => simpa [planarDiskClosedUnion] using
      isPathConnected_univ.joinedIn x (Set.mem_univ x) y (Set.mem_univ y)
  | cons B L ih =>
    have hUnion : planarDiskClosedUnion (B :: L) = B.closed ∪ planarDiskClosedUnion L := by
      ext z
      simp [planarDiskClosedUnion, List.mem_cons]
    rw [hUnion, mem_union, not_or] at hx hy
    rcases List.pairwise_cons.mp hdisj with ⟨hB, hL⟩
    have hx' : B.radius < dist x B.center := lt_of_not_ge fun h => hx.1 (mem_closedBall.2 h)
    have hy' : B.radius < dist y B.center := lt_of_not_ge fun h => hy.1 (mem_closedBall.2 h)
    obtain ⟨R, hBR, hRxy, hRL⟩ := exists_uniform_gap_disk B L _ (lt_min hx' hy') hB
    have hsphere : sphere B.center R ⊆ (planarDiskClosedUnion L)ᶜ := by
      intro z hz hzL
      simp only [planarDiskClosedUnion, mem_iUnion, exists_prop] at hzL
      obtain ⟨D, hD, hzD⟩ := hzL
      have h := dist_triangle_left B.center D.center z
      rw [mem_sphere.mp hz] at h
      linarith only [h, mem_closedBall.mp hzD, hRL D hD]
    have hPath := joinedIn_sdiff_closedBall (ih hL hx.2 hy.2) B.radius_pos.le hBR
      (hRxy.trans_le (min_le_left _ _)) (hRxy.trans_le (min_le_right _ _)) hsphere
    apply hPath.mono
    rw [hUnion]
    exact fun _ h hm => hm.elim h.2 h.1

/-- Pairwise disjoint disks which contain the frontier of a bounded open
region also contain its closure. -/
theorem closure_subset_planarDiskClosedUnion_of_frontier {V : Set Plane} (hV : IsOpen V)
    (hVb : Bornology.IsBounded V) (L : List PlanarDisk)
    (hd : L.Pairwise fun B D => Disjoint B.closed D.closed)
    (hcov : frontier V ⊆ planarDiskClosedUnion L) : closure V ⊆ planarDiskClosedUnion L := by
  have hK := isCompact_planarDiskClosedUnion L
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hxL
  obtain ⟨C, hC⟩ := (hVb.isCompact_closure.union hK).exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun z : Plane => z) _)
  obtain ⟨y, hy⟩ := NormedSpace.exists_lt_norm ℝ Plane C
  have hyOut : y ∉ closure V ∪ planarDiskClosedUnion L := fun hy' => hy.not_ge (hC y hy')
  obtain ⟨p, hp⟩ := joinedIn_compl_planarDiskClosedUnion L hd hxL (fun h => hyOut (Or.inr h))
  have hpre : p ⁻¹' closure V = p ⁻¹' V := by
    rw [closure_eq_self_union_frontier]
    ext t
    exact ⟨fun h => h.elim id (fun ht => (hp t (hcov ht)).elim), Or.inl⟩
  have hclop : IsClopen (p ⁻¹' V) :=
    ⟨hpre ▸ isClosed_closure.preimage p.continuous, hV.preimage p.continuous⟩
  have hzero : (0 : unitInterval) ∈ p ⁻¹' V := by
    change p 0 ∈ V
    rwa [p.source]
  have hone : (1 : unitInterval) ∈ p ⁻¹' V := hclop.eq_univ ⟨0, hzero⟩ ▸ mem_univ _
  change p 1 ∈ V at hone
  rw [p.target] at hone
  exact hyOut (Or.inl (subset_closure hone))

private theorem planarCoverRadius_le_of_cover
    (K : TopologicalSpace.Compacts Plane) (L : List PlanarDisk)
    (hcov : (K : Set Plane) ⊆ ⋃ B ∈ L, B.interior) :
    planarCoverRadius K ≤ (L.map PlanarDisk.radius).sum := by
  have hMem : (L.map PlanarDisk.radius).sum ∈ planarCoverSums K := ⟨L, hcov, rfl⟩
  apply csInf_le _ hMem
  refine ⟨0, ?_⟩
  rintro s ⟨M, -, rfl⟩
  exact List.sum_nonneg (fun r hr => by
    obtain ⟨B, _, rfl⟩ := List.mem_map.mp hr
    exact B.radius_pos.le)

private theorem planarCoverRadius_le_of_closed_disk_cover
    (K : TopologicalSpace.Compacts Plane) (L : List PlanarDisk)
    (hcov : (K : Set Plane) ⊆ planarDiskClosedUnion L) :
    planarCoverRadius K ≤ (L.map PlanarDisk.radius).sum := by
  apply le_of_forall_pos_le_add
  intro η hη
  let δ := η / ((L.length : ℝ) + 1)
  have hδ : 0 < δ := div_pos hη (by positivity)
  let addR (B : PlanarDisk) : PlanarDisk := ⟨B.center, B.radius + δ, add_pos B.radius_pos hδ⟩
  have hcov' : (K : Set Plane) ⊆ ⋃ B ∈ L.map addR, B.interior := by
    intro x hx
    obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.mp (hcov hx)
    exact mem_iUnion₂.mpr ⟨addR B, List.mem_map.mpr ⟨B, hB, rfl⟩,
      mem_ball.mpr ((mem_closedBall.mp hxB).trans_lt (lt_add_of_pos_right _ hδ))⟩
  apply (planarCoverRadius_le_of_cover K (L.map addR) hcov').trans
  have hsum : ((L.map addR).map PlanarDisk.radius).sum =
      (L.map PlanarDisk.radius).sum + (L.length : ℝ) * δ := by
    rw [List.map_map]
    change (L.map (fun B => B.radius + δ)).sum = _
    rw [List.sum_map_add, List.map_const', List.sum_replicate, nsmul_eq_mul]
  rw [hsum]
  apply add_le_add_right
  have hδeq : δ * ((L.length : ℝ) + 1) = η := div_mul_cancel₀ η (by positivity)
  linarith only [hδeq, hδ]

/-- The closure and the frontier of a bounded open planar region have the
same disk-cover radius in the direction needed for the sublevel estimate. -/
theorem planarCoverRadius_closure_le_frontier {V : Set Plane}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) :
    planarCoverRadius ⟨closure V, hVb.isCompact_closure⟩ ≤
      planarCoverRadius ⟨frontier V, hVb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure⟩ := by
  apply le_csInf (planarCoverSums_nonempty _)
  rintro s ⟨L, hcov, rfl⟩
  obtain ⟨M, hm, hd⟩ := exists_pairwise_disjoint_planarDisk_merges L
  rw [← planarDisk_merges_radius_sum hm]
  apply planarCoverRadius_le_of_closed_disk_cover
  apply closure_subset_planarDiskClosedUnion_of_frontier hV hVb M hd
  intro x hx
  obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.mp (hcov hx)
  obtain ⟨D, hD, ho, _⟩ := planarDisk_merges_successor hm B hB
  exact mem_iUnion₂.mpr ⟨D, hD, ball_subset_closedBall (ho hxB)⟩

private theorem exists_hausdorff_length_cover (K : Set Plane) {η : ℝ≥0∞}
    (hη : Measure.hausdorffMeasure 1 K < η) :
    ∃ S : ℕ → Set Plane, K ⊆ ⋃ n, S n ∧
      (∀ n, ediam (S n) ≤ 1) ∧ (∑' n, ediam (S n)) < η := by
  rw [Measure.hausdorffMeasure_apply] at hη
  let F (r : ℝ≥0∞) :=
    ⨅ (S : ℕ → Set Plane) (_ : K ⊆ ⋃ n, S n) (_ : ∀ n, ediam (S n) ≤ r),
      ∑' n, ⨆ _ : (S n).Nonempty, ediam (S n) ^ (1 : ℝ)
  have hη' : (⨆ (r : ℝ≥0∞) (_ : 0 < r), F r) < η := hη
  have hinf : F 1 < η := by
    have hin : F 1 ≤ ⨆ _ : (0 : ℝ≥0∞) < 1, F 1 :=
      le_iSup (fun _ : (0 : ℝ≥0∞) < 1 => F 1) zero_lt_one
    have hout : (⨆ _ : (0 : ℝ≥0∞) < 1, F 1) ≤ ⨆ (r : ℝ≥0∞) (_ : 0 < r), F r :=
      le_iSup (fun r : ℝ≥0∞ => ⨆ _ : 0 < r, F r) 1
    exact (hin.trans hout).trans_lt hη'
  dsimp only [F] at hinf
  obtain ⟨S, hS⟩ := iInf_lt_iff.mp hinf
  obtain ⟨hc, hS⟩ := iInf_lt_iff.mp hS
  obtain ⟨hd, hS⟩ := iInf_lt_iff.mp hS
  refine ⟨S, hc, hd, ?_⟩
  convert hS using 1
  congr 1
  funext n
  by_cases hn : (S n).Nonempty
  · simp [hn]
  · simp [Set.not_nonempty_iff_eq_empty.mp hn]

/-- The disk-cover radius of a compact planar set is bounded by its
one-dimensional Hausdorff measure, with the diameter normalization. -/
theorem ofReal_planarCoverRadius_le_hausdorffMeasure (K : TopologicalSpace.Compacts Plane) :
    ENNReal.ofReal (planarCoverRadius K) ≤ Measure.hausdorffMeasure 1 (K : Set Plane) := by
  classical
  let μ := Measure.hausdorffMeasure 1 (K : Set Plane)
  by_cases hμ : μ = ⊤
  · change ENNReal.ofReal (planarCoverRadius K) ≤ μ
    rw [hμ]
    exact le_top
  suffices h : planarCoverRadius K ≤ μ.toReal by
    change ENNReal.ofReal (planarCoverRadius K) ≤ μ
    rw [← ENNReal.ofReal_toReal hμ]
    exact ENNReal.ofReal_le_ofReal h
  apply le_of_forall_pos_le_add
  intro η hη
  let q := μ.toReal + η / 2
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hq' : μ < ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_toReal hμ, ENNReal.ofReal_lt_ofReal_iff hq]
    dsimp only [q]
    linarith
  obtain ⟨S, hS, hd, hs⟩ := exists_hausdorff_length_cover (K : Set Plane) hq'
  let c (n : ℕ) : Plane :=
    if h : (S n).Nonempty then h.some else 0
  let pad (n : ℕ) := (η / 4) * (1 / 2 : ℝ) ^ n
  have hpad (n : ℕ) : 0 < pad n := by dsimp only [pad]; positivity
  let B (n : ℕ) : PlanarDisk :=
    ⟨c n, (ediam (S n)).toReal + pad n, add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg (hpad n)⟩
  have hcov (n : ℕ) : S n ⊆ (B n).interior := by
    intro x hx
    have hsn : (S n).Nonempty := ⟨x, hx⟩
    have hcn : c n ∈ S n := by simpa only [c, dif_pos hsn] using hsn.some_mem
    have hdiam : dist x (c n) ≤ (ediam (S n)).toReal := by
      exact Metric.dist_le_diam_of_mem (Metric.isBounded_iff_ediam_ne_top.mpr ((hd n).trans_lt ENNReal.one_lt_top).ne) hx hcn
    exact mem_ball.mpr (hdiam.trans_lt (lt_add_of_pos_right _ (hpad n)))
  obtain ⟨J, hJ⟩ := K.isCompact.elim_finite_subcover (fun n => (B n).interior)
    (fun _ => isOpen_ball) (hS.trans (iUnion_mono hcov))
  let L := J.toList.map B
  have hL : (K : Set Plane) ⊆ ⋃ D ∈ L, D.interior := by
    intro x hx
    obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp (hJ hx)
    exact mem_iUnion₂.mpr ⟨B n, List.mem_map.mpr ⟨n, Finset.mem_toList.mpr hn, rfl⟩, hxn⟩
  apply (planarCoverRadius_le_of_cover K L hL).trans
  have hsum : (L.map PlanarDisk.radius).sum =
      ∑ n ∈ J, ((ediam (S n)).toReal + pad n) := by
    dsimp only [L]
    rw [List.map_map]
    change (J.val.toList.map (fun n => (ediam (S n)).toReal + pad n)).sum =
      (J.val.map (fun n => (ediam (S n)).toReal + pad n)).sum
    exact Multiset.sum_map_toList _ _
  have hdiam : (∑ n ∈ J, (ediam (S n)).toReal) < q := by
    apply (ENNReal.ofReal_lt_ofReal_iff hq).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    have hOf (n : ℕ) : ENNReal.ofReal ((ediam (S n)).toReal) = ediam (S n) :=
      ENNReal.ofReal_toReal ((hd n).trans_lt ENNReal.one_lt_top).ne
    simp_rw [hOf]
    exact (ENNReal.sum_le_tsum J).trans_lt hs
  have hsumPad : HasSum pad (η / 2) := by
    have h := (hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (η / 4)
    have h₂ : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
    have hη₂ : η / 4 * 2 = η / 2 := by ring
    rw [h₂, hη₂] at h
    exact h
  have hJpad : (∑ n ∈ J, pad n) ≤ η / 2 := by
    rw [← hsumPad.tsum_eq]
    exact hsumPad.summable.sum_le_tsum J (fun n _ => (hpad n).le)
  rw [hsum, Finset.sum_add_distrib]
  dsimp only [q] at hdiam
  linarith

/-- The radius of a bounded open planar region is bounded by the length of
its frontier. -/
theorem ofReal_planarCoverRadius_closure_le_hausdorff_frontier {V : Set Plane}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) :
    ENNReal.ofReal (planarCoverRadius ⟨closure V, hVb.isCompact_closure⟩) ≤
      Measure.hausdorffMeasure 1 (frontier V) := by
  exact (ENNReal.ofReal_le_ofReal (planarCoverRadius_closure_le_frontier hV hVb)).trans
    (ofReal_planarCoverRadius_le_hausdorffMeasure
      ⟨frontier V, hVb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure⟩)

/-- Disk-cover radii are monotone under inclusion of compact sets. -/
theorem planarCoverRadius_mono {K L : TopologicalSpace.Compacts Plane}
    (hKL : (K : Set Plane) ⊆ L) : planarCoverRadius K ≤ planarCoverRadius L := by
  apply le_csInf (planarCoverSums_nonempty L)
  rintro s ⟨A, hA, rfl⟩
  exact planarCoverRadius_le_of_cover K A (hKL.trans hA)

/-- The closure of the strict sublevel region in a centered disk. -/
def planarSublevelCore (f : Plane → ℝ) (R t : ℝ) : TopologicalSpace.Compacts Plane :=
  ⟨closure (ball (0 : Plane) R ∩ {x | f x < t}), (isBounded_ball.subset inter_subset_left).isCompact_closure⟩

theorem monotone_planarSublevelCore_radius (f : Plane → ℝ) (R : ℝ) :
    Monotone (fun t => planarCoverRadius (planarSublevelCore f R t)) := by
  intro s t hst
  apply planarCoverRadius_mono
  exact closure_mono (inter_subset_inter_right _ (fun _ hx => hx.trans_le hst))

/-- Strict gap on a closed annulus confines the entire sublevel core to
its inner disk. The core's cover radius is controlled by the actual level. -/
theorem planarSublevelCore_inside_and_radius_le {f : Plane → ℝ} {R μ t : ℝ}
    (hf : ContinuousOn f (closedBall (0 : Plane) R)) (hμR : μ ≤ R)
    (hAnn : ∀ x : Plane, μ ≤ ‖x‖ → ‖x‖ ≤ R → t < f x) :
    ((planarSublevelCore f R t : Set Plane) ⊆ ball (0 : Plane) μ) ∧
    ENNReal.ofReal (planarCoverRadius (planarSublevelCore f R t)) ≤
      Measure.hausdorffMeasure 1 (ball (0 : Plane) R ∩ {x | f x = t}) := by
  let V := ball (0 : Plane) R ∩ {x | f x < t}
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hF := (hf.mono ball_subset_closedBall).continuousAt (isOpen_ball.mem_nhds hx.1)
    exact inter_mem (isOpen_ball.mem_nhds hx.1) (hF.preimage_mem_nhds (Iio_mem_nhds hx.2))
  have hVb : Bornology.IsBounded V := isBounded_ball.subset inter_subset_left
  let S := closedBall (0 : Plane) R
  have hVS : V ⊆ S := inter_subset_left.trans ball_subset_closedBall
  have hC : IsClosed (S ∩ {x | f x ≤ t}) := by
    have hSub : IsClosed ((fun z : S => f z.val) ⁻¹' Iic t) :=
      isClosed_Iic.preimage (continuousOn_iff_continuous_restrict.mp hf)
    have hImage := isClosed_closedBall.isClosedMap_subtype_val _ hSub
    rw [show S ∩ {x | f x ≤ t} = Subtype.val '' ((fun z : S => f z.val) ⁻¹' Iic t) by
      ext x
      constructor
      · rintro ⟨hS, hF⟩
        exact ⟨⟨x, hS⟩, hF, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.property, hz⟩]
    exact hImage
  have hCl : closure V ⊆ S ∩ {x | f x ≤ t} := closure_minimal
    (fun x (h : x ∈ V) => ⟨hVS h, (show f x < t from h.2).le⟩) hC
  have hInside : closure V ⊆ ball (0 : Plane) μ := by
    intro x hx
    rw [mem_ball, dist_zero_right]
    by_contra! hn
    have hxR : ‖x‖ ≤ R := by simpa only [S, mem_closedBall, dist_zero_right] using (hCl hx).1
    exact (hAnn x hn hxR).not_ge (hCl hx).2
  refine ⟨hInside, ?_⟩
  apply (ofReal_planarCoverRadius_closure_le_hausdorff_frontier hV hVb).trans
  apply measure_mono
  intro x hx
  have hxb : x ∈ ball (0 : Plane) R := ball_subset_ball hμR (hInside (frontier_subset_closure hx))
  refine ⟨hxb, le_antisymm (hCl (frontier_subset_closure hx)).2 ?_⟩
  rw [← not_lt]
  intro hxt
  apply hx.2
  rw [hV.interior_eq]
  exact ⟨hxb, hxt⟩

/-- The compact image of a planar core under a centered scalar dilation. -/
def planarDilateCore (r : ℝ) (K : TopologicalSpace.Compacts Plane) : TopologicalSpace.Compacts Plane :=
  ⟨(fun x : Plane => r • x) '' (K : Set Plane), K.isCompact.image (by fun_prop)⟩

private theorem planarCoverRadius_dilate_le (r : ℝ) (hr : 0 < r) (K : TopologicalSpace.Compacts Plane) :
    planarCoverRadius (planarDilateCore r K) ≤ r * planarCoverRadius K := by
  have hLE : planarCoverRadius (planarDilateCore r K) / r ≤ planarCoverRadius K := by
    apply le_csInf (planarCoverSums_nonempty K)
    rintro s ⟨L, hL, rfl⟩
    let B' (B : PlanarDisk) : PlanarDisk := ⟨r • B.center, r * B.radius, mul_pos hr B.radius_pos⟩
    have hCover : ((planarDilateCore r K : TopologicalSpace.Compacts Plane) : Set Plane) ⊆
        ⋃ B ∈ L.map B', B.interior := by
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.mp (hL hx)
      refine mem_iUnion₂.mpr ⟨B' B, List.mem_map.mpr ⟨B, hB, rfl⟩, mem_ball.mpr ?_⟩
      change dist (r • x) (r • B.center) < r * B.radius
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hr.le, ← dist_eq_norm]
      exact mul_lt_mul_of_pos_left (mem_ball.mp hxB) hr
    have hsum : ((L.map B').map PlanarDisk.radius).sum = r * (L.map PlanarDisk.radius).sum := by
      rw [List.map_map]
      exact List.sum_map_mul_left L PlanarDisk.radius r
    have hbound := planarCoverRadius_le_of_cover (planarDilateCore r K) (L.map B') hCover
    rw [hsum, mul_comm r] at hbound
    exact (div_le_iff₀ hr).2 hbound
  rw [mul_comm]
  exact (div_le_iff₀ hr).mp hLE

/-- Disk-cover radius scales linearly under positive dilation. -/
theorem planarCoverRadius_dilate (r : ℝ) (hr : 0 < r) (K : TopologicalSpace.Compacts Plane) :
    planarCoverRadius (planarDilateCore r K) = r * planarCoverRadius K := by
  apply le_antisymm (planarCoverRadius_dilate_le r hr K)
  have hclose : planarDilateCore r⁻¹ (planarDilateCore r K) = K := by
    apply TopologicalSpace.Compacts.ext
    change (fun x : Plane => r⁻¹ • x) '' ((fun x : Plane => r • x) '' (K : Set Plane)) = (K : Set Plane)
    rw [Set.image_image]
    simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul, image_id']
  have hI := planarCoverRadius_dilate_le r⁻¹ (inv_pos.mpr hr) (planarDilateCore r K)
  rw [hclose, ← div_eq_inv_mul] at hI
  rw [mul_comm]
  exact (le_div_iff₀ hr).mp hI

end Thesis
