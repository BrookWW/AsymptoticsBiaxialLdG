module

public import Thesis.Definitions

/-! Weighted mergers and geometric invariants of planar disk growth. -/

@[expose] public section

noncomputable section

open Metric Set

namespace Thesis

/-- A planar disk of positive radius. -/
structure PlanarDisk where
  center : Plane
  radius : ℝ
  radius_pos : 0 < radius

namespace PlanarDisk

def interior (B : PlanarDisk) : Set Plane := ball B.center B.radius

def closed (B : PlanarDisk) : Set Plane := closedBall B.center B.radius

/-- The radius-preserving weighted replacement of a pair of disks. -/
def merge (B D : PlanarDisk) : PlanarDisk where
  center := (B.radius / (B.radius + D.radius)) • B.center +
    (D.radius / (B.radius + D.radius)) • D.center
  radius := B.radius + D.radius
  radius_pos := add_pos B.radius_pos D.radius_pos

private theorem merge_ratios_sum (B D : PlanarDisk) :
    B.radius / (B.radius + D.radius) + D.radius / (B.radius + D.radius) = 1 := by
  rw [← add_div, div_self (add_pos B.radius_pos D.radius_pos).ne']

theorem merge_center_mem {K : Set Plane} (hK : Convex ℝ K) {B D : PlanarDisk}
    (hB : B.center ∈ K) (hD : D.center ∈ K) : (merge B D).center ∈ K :=
  convex_iff_add_mem.mp hK hB hD (div_nonneg B.radius_pos.le (merge B D).radius_pos.le)
    (div_nonneg D.radius_pos.le (merge B D).radius_pos.le) (merge_ratios_sum B D)

theorem merge_center_dist_le {B D : PlanarDisk}
    (h : dist B.center D.center ≤ B.radius + D.radius) :
    dist B.center (merge B D).center ≤ D.radius ∧
      dist D.center (merge B D).center ≤ B.radius := by
  let a := B.radius / (B.radius + D.radius)
  let b := D.radius / (B.radius + D.radius)
  have ha : 0 ≤ a := div_nonneg B.radius_pos.le (add_pos B.radius_pos D.radius_pos).le
  have hb : 0 ≤ b := div_nonneg D.radius_pos.le (add_pos B.radius_pos D.radius_pos).le
  have hab : a + b = 1 := merge_ratios_sum B D
  have hB : B.center - (merge B D).center = b • (B.center - D.center) := by
    change B.center - (a • B.center + b • D.center) = _
    calc
      _ = (a + b) • B.center - (a • B.center + b • D.center) := by rw [hab, one_smul]
      _ = _ := by module
  have hD : D.center - (merge B D).center = a • (D.center - B.center) := by
    change D.center - (a • B.center + b • D.center) = _
    calc
      _ = (a + b) • D.center - (a • B.center + b • D.center) := by rw [hab, one_smul]
      _ = _ := by module
  constructor
  · rw [dist_eq_norm, hB, norm_smul, Real.norm_of_nonneg hb, ← dist_eq_norm]
    exact (mul_le_mul_of_nonneg_left h hb).trans_eq
      (div_mul_cancel₀ _ (add_pos B.radius_pos D.radius_pos).ne')
  · rw [dist_eq_norm, hD, norm_smul, Real.norm_of_nonneg ha, ← dist_eq_norm, dist_comm D.center B.center]
    exact (mul_le_mul_of_nonneg_left h ha).trans_eq
      (div_mul_cancel₀ _ (add_pos B.radius_pos D.radius_pos).ne')

theorem closed_inter_nonempty_iff {B D : PlanarDisk} :
    (B.closed ∩ D.closed).Nonempty ↔ dist B.center D.center ≤ B.radius + D.radius := by
  constructor
  · exact dist_le_add_of_nonempty_closedBall_inter_closedBall
  · intro h
    let B' : PlanarDisk := ⟨B.center, D.radius, D.radius_pos⟩
    let D' : PlanarDisk := ⟨D.center, B.radius, B.radius_pos⟩
    have h' : dist B'.center D'.center ≤ B'.radius + D'.radius := by
      simpa only [B', D', add_comm] using h
    obtain ⟨hB, hD⟩ := merge_center_dist_le h'
    exact ⟨(merge B' D').center, mem_closedBall'.mpr hB, mem_closedBall'.mpr hD⟩

theorem union_interior_subset_merge {B D : PlanarDisk} (h : ¬ Disjoint B.closed D.closed) :
    B.interior ∪ D.interior ⊆ (merge B D).interior := by
  have hdist : dist B.center D.center ≤ B.radius + D.radius :=
    dist_le_add_of_nonempty_closedBall_inter_closedBall (not_disjoint_iff_nonempty_inter.mp h)
  obtain ⟨hB, hD⟩ := merge_center_dist_le hdist
  exact union_subset (ball_subset_ball' (by change B.radius + _ ≤ B.radius + D.radius; linarith))
    (ball_subset_ball' (by change D.radius + _ ≤ B.radius + D.radius; linarith))

theorem union_closed_subset_merge {B D : PlanarDisk} (h : ¬ Disjoint B.closed D.closed) :
    B.closed ∪ D.closed ⊆ (merge B D).closed := by
  have hdist : dist B.center D.center ≤ B.radius + D.radius :=
    dist_le_add_of_nonempty_closedBall_inter_closedBall (not_disjoint_iff_nonempty_inter.mp h)
  obtain ⟨hB, hD⟩ := merge_center_dist_le hdist
  exact union_subset (closedBall_subset_closedBall' (by change B.radius + _ ≤ B.radius + D.radius; linarith))
    (closedBall_subset_closedBall' (by change D.radius + _ ≤ B.radius + D.radius; linarith))

end PlanarDisk

/-- One contact merger, with all other disks retained in their original order. -/
inductive PlanarDiskMerge : List PlanarDisk → List PlanarDisk → Prop
  | contact (before : List PlanarDisk) (B : PlanarDisk) (between : List PlanarDisk)
      (D : PlanarDisk) (after : List PlanarDisk) (h : ¬ Disjoint B.closed D.closed) :
      PlanarDiskMerge (before ++ (B :: (between ++ (D :: after))))
        (before ++ (B.merge D :: (between ++ after)))

namespace PlanarDiskMerge

theorem length_lt {L M : List PlanarDisk} (h : PlanarDiskMerge L M) : M.length < L.length := by
  cases h
  simp only [List.length_append, List.length_cons]
  omega

theorem radius_sum {L M : List PlanarDisk} (h : PlanarDiskMerge L M) :
    (M.map PlanarDisk.radius).sum = (L.map PlanarDisk.radius).sum := by
  cases h
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, PlanarDisk.merge]
  ring

theorem centers_mem {K : Set Plane} (hK : Convex ℝ K) {L M : List PlanarDisk}
    (h : PlanarDiskMerge L M) (hL : ∀ B ∈ L, B.center ∈ K) :
    ∀ B ∈ M, B.center ∈ K := by
  cases h with
  | contact before B between D after h =>
      intro A hA
      simp only [List.mem_append, List.mem_cons] at hA
      rcases hA with hA | rfl | hA | hA
      · exact hL A (by simp [hA])
      · exact PlanarDisk.merge_center_mem hK (hL B (by simp)) (hL D (by simp))
      · exact hL A (by simp [hA])
      · exact hL A (by simp [hA])

/-- Every incoming disk is contained in its successor in the merge sequence. -/
theorem successor {L M : List PlanarDisk} (h : PlanarDiskMerge L M) :
    ∀ B ∈ L, ∃ D ∈ M, B.interior ⊆ D.interior ∧ B.closed ⊆ D.closed := by
  cases h with
  | contact before B between D after h =>
      intro A hA
      simp only [List.mem_append, List.mem_cons] at hA
      rcases hA with hA | hEq | hA | hEq | hA
      · exact ⟨A, by simp [hA], Subset.rfl, Subset.rfl⟩
      · subst A
        exact ⟨B.merge D, by simp,
          subset_union_left.trans (PlanarDisk.union_interior_subset_merge h),
          subset_union_left.trans (PlanarDisk.union_closed_subset_merge h)⟩
      · exact ⟨A, by simp [hA], Subset.rfl, Subset.rfl⟩
      · subst A
        exact ⟨B.merge D, by simp,
          subset_union_right.trans (PlanarDisk.union_interior_subset_merge h),
          subset_union_right.trans (PlanarDisk.union_closed_subset_merge h)⟩
      · exact ⟨A, by simp [hA], Subset.rfl, Subset.rfl⟩

end PlanarDiskMerge

private theorem exists_planarDiskMerge_of_not_pairwise {L : List PlanarDisk}
    (h : ¬ L.Pairwise (fun B D => Disjoint B.closed D.closed)) :
    ∃ M, PlanarDiskMerge L M := by
  induction L with
  | nil => exact (h List.Pairwise.nil).elim
  | cons B L ih =>
      by_cases ht : L.Pairwise (fun B D => Disjoint B.closed D.closed)
      · have hf : ¬ ∀ D ∈ L, Disjoint B.closed D.closed := by
          intro hD
          exact h (List.pairwise_cons.mpr ⟨hD, ht⟩)
        push Not at hf
        obtain ⟨D, hD, hd⟩ := hf
        obtain ⟨between, after, rfl⟩ := List.append_of_mem hD
        exact ⟨B.merge D :: (between ++ after), PlanarDiskMerge.contact [] B between D after hd⟩
      · obtain ⟨M, hM⟩ := ih ht
        cases hM with
        | contact before C between D after hc =>
            exact ⟨B :: (before ++ (C.merge D :: (between ++ after))),
              PlanarDiskMerge.contact (B :: before) C between D after hc⟩

/-- Finitely many contact mergers produce pairwise disjoint closed disks. -/
theorem exists_pairwise_disjoint_planarDisk_merges (L : List PlanarDisk) :
    ∃ M, Relation.ReflTransGen PlanarDiskMerge L M ∧
      M.Pairwise (fun B D => Disjoint B.closed D.closed) := by
  have haux (n : ℕ) : ∀ (A : List PlanarDisk), A.length = n →
      ∃ M, Relation.ReflTransGen PlanarDiskMerge A M ∧
        M.Pairwise (fun B D => Disjoint B.closed D.closed) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro A ha
        by_cases hp : A.Pairwise (fun B D => Disjoint B.closed D.closed)
        · exact ⟨A, .refl, hp⟩
        · obtain ⟨A', hm⟩ := exists_planarDiskMerge_of_not_pairwise hp
          obtain ⟨M, hM, hpM⟩ := ih A'.length (ha ▸ hm.length_lt) A' rfl
          exact ⟨M, (Relation.ReflTransGen.single hm).trans hM, hpM⟩
  exact haux L.length L rfl

theorem planarDisk_merges_radius_sum {L M : List PlanarDisk} (h : Relation.ReflTransGen PlanarDiskMerge L M) :
    (M.map PlanarDisk.radius).sum = (L.map PlanarDisk.radius).sum := by
  induction h with
  | refl => rfl
  | tail _ hd ih => exact hd.radius_sum.trans ih

theorem planarDisk_merges_centers_mem {K : Set Plane} (hK : Convex ℝ K) {L M : List PlanarDisk}
    (h : Relation.ReflTransGen PlanarDiskMerge L M) (hL : ∀ B ∈ L, B.center ∈ K) :
    ∀ B ∈ M, B.center ∈ K := by
  induction h with
  | refl => exact hL
  | tail _ hd ih => exact hd.centers_mem hK ih

theorem planarDisk_merges_successor {L M : List PlanarDisk} (h : Relation.ReflTransGen PlanarDiskMerge L M) :
    ∀ B ∈ L, ∃ D ∈ M, B.interior ⊆ D.interior ∧ B.closed ⊆ D.closed := by
  induction h with
  | refl => exact fun B hB => ⟨B, hB, Subset.rfl, Subset.rfl⟩
  | tail _ hd ih =>
      intro B hb
      obtain ⟨D, hD, hBo, hBc⟩ := ih B hb
      obtain ⟨E, hE, hDo, hDc⟩ := hd.successor D hD
      exact ⟨E, hE, hBo.trans hDo, hBc.trans hDc⟩

theorem planarDisk_merges_length_le {L M : List PlanarDisk} (h : Relation.ReflTransGen PlanarDiskMerge L M) :
    M.length ≤ L.length := by
  induction h with
  | refl => exact le_rfl
  | tail _ hd ih => exact hd.length_lt.le.trans ih

namespace PlanarDisk

/-- Common exponential growth fixes the center and changes only the radius. -/
def grow (t : ℝ) (B : PlanarDisk) : PlanarDisk where
  center := B.center
  radius := Real.exp t * B.radius
  radius_pos := mul_pos (Real.exp_pos t) B.radius_pos

theorem grow_radius_mono (B : PlanarDisk) {s t : ℝ} (h : s ≤ t) :
    (B.grow s).radius ≤ (B.grow t).radius :=
  mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h) B.radius_pos.le

theorem subset_grow {t : ℝ} (ht : 0 ≤ t) (B : PlanarDisk) :
    B.interior ⊆ (B.grow t).interior ∧ B.closed ⊆ (B.grow t).closed := by
  have hin : B.radius ≤ (B.grow t).radius := by
    simpa only [grow, Real.exp_zero, one_mul] using B.grow_radius_mono ht
  exact ⟨ball_subset_ball hin, closedBall_subset_closedBall hin⟩

/-- Contact time for a pair of fixed centers under unit exponential growth. -/
def contactTime (B D : PlanarDisk) : ℝ :=
  Real.log (dist B.center D.center / (B.radius + D.radius))

theorem contactTime_pos {B D : PlanarDisk} (h : Disjoint B.closed D.closed) :
    0 < B.contactTime D := by
  have hdist : B.radius + D.radius < dist B.center D.center :=
    lt_of_not_ge (fun hd => not_disjoint_iff_nonempty_inter.mpr (closed_inter_nonempty_iff.mpr hd) h)
  exact Real.log_pos ((one_lt_div (add_pos B.radius_pos D.radius_pos)).mpr hdist)

theorem grow_before_contact {B D : PlanarDisk} (h : Disjoint B.closed D.closed) {t : ℝ}
    (ht : t ≤ B.contactTime D) :
    (B.grow t).radius + (D.grow t).radius ≤ dist B.center D.center := by
  have hd : 0 < dist B.center D.center := by
    have hlt : B.radius + D.radius < dist B.center D.center :=
      lt_of_not_ge (fun hle => not_disjoint_iff_nonempty_inter.mpr (closed_inter_nonempty_iff.mpr hle) h)
    exact (add_pos B.radius_pos D.radius_pos).trans hlt
  have hdiv : 0 < dist B.center D.center / (B.radius + D.radius) :=
    div_pos hd (add_pos B.radius_pos D.radius_pos)
  change Real.exp t * B.radius + Real.exp t * D.radius ≤ _
  rw [← mul_add, ← le_div_iff₀ (add_pos B.radius_pos D.radius_pos)]
  exact (Real.le_log_iff_exp_le hdiv).mp ht

theorem strictly_before_contact {B D : PlanarDisk} {t : ℝ}
    (h : Disjoint (B.grow t).closed (D.grow t).closed) : t < B.contactTime D := by
  have hdist : (B.grow t).radius + (D.grow t).radius < dist B.center D.center :=
    lt_of_not_ge (fun hd => not_disjoint_iff_nonempty_inter.mpr (closed_inter_nonempty_iff.mpr hd) h)
  have hdiv : 0 < dist B.center D.center / (B.radius + D.radius) :=
    div_pos ((add_pos (B.grow t).radius_pos (D.grow t).radius_pos).trans hdist)
      (add_pos B.radius_pos D.radius_pos)
  apply (Real.lt_log_iff_exp_lt hdiv).mpr
  apply (lt_div_iff₀ (add_pos B.radius_pos D.radius_pos)).mpr
  rwa [mul_add]

end PlanarDisk

private def contactTimes : List PlanarDisk → List ℝ
  | [] => []
  | B :: L => L.map (fun D => B.contactTime D) ++ contactTimes L

private theorem pairwise_contactTimes_iff {L : List PlanarDisk} (P : ℝ → Prop) :
    L.Pairwise (fun B D => P (B.contactTime D)) ↔ ∀ t ∈ contactTimes L, P t := by
  induction L with
  | nil => simp [contactTimes]
  | cons B L ih =>
      rw [List.pairwise_cons, ih]
      constructor
      · rintro ⟨hB, hL⟩ t ht
        simp only [contactTimes, List.mem_append, List.mem_map] at ht
        rcases ht with ⟨D, hD, rfl⟩ | ht
        · exact hB D hD
        · exact hL t ht
      · intro h
        refine ⟨fun D hD => h _ ?_, fun t ht => h _ ?_⟩
        · simp only [contactTimes, List.mem_append, List.mem_map]
          exact Or.inl ⟨D, hD, rfl⟩
        · exact List.mem_append_right _ ht

/-- The first contact time clipped to a prescribed nonnegative duration. -/
private theorem exists_next_growth_duration (L : List PlanarDisk)
    (hL : L.Pairwise (fun B D => Disjoint B.closed D.closed)) {T : ℝ} (hT : 0 ≤ T) :
    ∃ t ∈ Icc 0 T,
      L.Pairwise (fun B D => (B.grow t).radius + (D.grow t).radius ≤ dist B.center D.center) ∧
      (t < T → ¬ (L.map (PlanarDisk.grow t)).Pairwise (fun B D => Disjoint B.closed D.closed)) := by
  classical
  let times := insert T (contactTimes L).toFinset
  have hnonempty : times.Nonempty := ⟨T, Finset.mem_insert_self _ _⟩
  let t := times.min' hnonempty
  have ht : t ∈ times := Finset.min'_mem _ _
  have hpos := (pairwise_contactTimes_iff (fun s => 0 < s)).mp (hL.imp PlanarDisk.contactTime_pos)
  have hnonneg : 0 ≤ t := by
    rcases Finset.mem_insert.mp ht with he | he
    · exact he.symm ▸ hT
    · exact (hpos t (List.mem_toFinset.mp he)).le
  have hle : t ≤ T := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hmin : L.Pairwise (fun B D => t ≤ B.contactTime D) :=
    (pairwise_contactTimes_iff _).mpr fun s hs =>
      Finset.min'_le _ _ (Finset.mem_insert_of_mem (List.mem_toFinset.mpr hs))
  refine ⟨t, ⟨hnonneg, hle⟩, (hL.and hmin).imp (fun h => PlanarDisk.grow_before_contact h.1 h.2), ?_⟩
  intro hlt hdisj
  have hstrict : L.Pairwise (fun B D => t < B.contactTime D) := by
    rw [List.pairwise_map] at hdisj
    exact hdisj.imp PlanarDisk.strictly_before_contact
  have hmem := List.mem_toFinset.mp ((Finset.mem_insert.mp ht).resolve_left hlt.ne)
  exact (lt_irrefl t) ((pairwise_contactTimes_iff _).mp hstrict t hmem)

/-- A disk evolution alternates common growth with instantaneous contact mergers.
The growth condition gives disjoint interiors throughout the elapsed interval. -/
inductive PlanarDiskTransition : (ℝ × List PlanarDisk) → (ℝ × List PlanarDisk) → Prop
  | growth (s : ℝ) (L : List PlanarDisk) (t : ℝ) (ht : 0 ≤ t)
      (hsep : L.Pairwise (fun B D => (B.grow t).radius + (D.grow t).radius ≤ dist B.center D.center)) :
      PlanarDiskTransition (s, L) (s + t, L.map (PlanarDisk.grow t))
  | merger (s : ℝ) {L M : List PlanarDisk} (h : PlanarDiskMerge L M) :
      PlanarDiskTransition (s, L) (s, M)

theorem pairwise_growth_interiors {L : List PlanarDisk} {s t : ℝ} (hst : s ≤ t)
    (hsep : L.Pairwise (fun B D => (B.grow t).radius + (D.grow t).radius ≤ dist B.center D.center)) :
    (L.map (PlanarDisk.grow s)).Pairwise (fun B D => Disjoint B.interior D.interior) := by
  rw [List.pairwise_map]
  exact hsep.imp fun h => ball_disjoint_ball
    ((add_le_add (PlanarDisk.grow_radius_mono _ hst) (PlanarDisk.grow_radius_mono _ hst)).trans h)

theorem planarDisk_merges_evolve {L M : List PlanarDisk} (s : ℝ)
    (h : Relation.ReflTransGen PlanarDiskMerge L M) :
    Relation.ReflTransGen PlanarDiskTransition (s, L) (s, M) := by
  induction h with
  | refl => exact .refl
  | tail _ hd ih => exact ih.tail (PlanarDiskTransition.merger s hd)

/-- A growth phase or the complete normalization of the disks at a contact time. -/
inductive PlanarDiskPhase : (ℝ × List PlanarDisk) → (ℝ × List PlanarDisk) → Prop
  | growth (s : ℝ) (L : List PlanarDisk) (t : ℝ) (ht : 0 ≤ t)
      (hsep : L.Pairwise (fun B D => (B.grow t).radius + (D.grow t).radius ≤ dist B.center D.center)) :
      PlanarDiskPhase (s, L) (s + t, L.map (PlanarDisk.grow t))
  | mergers (s : ℝ) {L M : List PlanarDisk}
      (hsep : L.Pairwise (fun B D => Disjoint B.interior D.interior))
      (h : Relation.ReflTransGen PlanarDiskMerge L M)
      (hM : M.Pairwise (fun B D => Disjoint B.closed D.closed)) :
      PlanarDiskPhase (s, L) (s, M)

theorem PlanarDiskPhase.evolves {p q : ℝ × List PlanarDisk} (h : PlanarDiskPhase p q) :
    Relation.ReflTransGen PlanarDiskTransition p q := by
  cases h with
  | growth s L t ht hsep => exact .single (.growth s L t ht hsep)
  | mergers s _ h _ => exact planarDisk_merges_evolve s h

theorem planarDiskPhases_evolve {p q : ℝ × List PlanarDisk} (h : Relation.ReflTransGen PlanarDiskPhase p q) :
    Relation.ReflTransGen PlanarDiskTransition p q := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.trans step.evolves

theorem exists_planarDiskPhases_of_pairwise (L : List PlanarDisk)
    (hL : L.Pairwise (fun B D => Disjoint B.closed D.closed)) (s T : ℝ) (hT : 0 ≤ T) :
    ∃ M, Relation.ReflTransGen PlanarDiskPhase (s, L) (s + T, M) ∧
      M.Pairwise (fun B D => Disjoint B.closed D.closed) := by
  have haux (n : ℕ) : ∀ (A : List PlanarDisk), A.length = n →
      A.Pairwise (fun B D => Disjoint B.closed D.closed) → ∀ (u S : ℝ), 0 ≤ S →
      ∃ M, Relation.ReflTransGen PlanarDiskPhase (u, A) (u + S, M) ∧
        M.Pairwise (fun B D => Disjoint B.closed D.closed) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro A hlen hp u S hS
        obtain ⟨t, ht, hsep, htouch⟩ := exists_next_growth_duration A hp hS
        let A' := A.map (PlanarDisk.grow t)
        have hg : Relation.ReflTransGen PlanarDiskPhase (u, A) (u + t, A') :=
          .single (PlanarDiskPhase.growth u A t ht.1 hsep)
        have hAsep : A'.Pairwise (fun B D => Disjoint B.interior D.interior) :=
          pairwise_growth_interiors le_rfl hsep
        by_cases hLt : t < S
        · obtain ⟨A'', hm⟩ := exists_planarDiskMerge_of_not_pairwise (htouch hLt)
          obtain ⟨A₀, hM, hp₀⟩ := exists_pairwise_disjoint_planarDisk_merges A''
          have hChain : Relation.ReflTransGen PlanarDiskMerge A' A₀ :=
            (Relation.ReflTransGen.single hm).trans hM
          have hlt : A₀.length < n := by
            calc
              A₀.length ≤ A''.length := planarDisk_merges_length_le hM
              _ < A'.length := hm.length_lt
              _ = n := (List.length_map (PlanarDisk.grow t)).trans hlen
          obtain ⟨M, hR, hPm⟩ := ih A₀.length hlt A₀ rfl hp₀ (u + t) (S - t) (sub_nonneg.mpr ht.2)
          have htime : u + t + (S - t) = u + S := by ring
          exact ⟨M, (hg.tail (PlanarDiskPhase.mergers _ hAsep hChain hp₀)).trans (htime ▸ hR), hPm⟩
        · have he : t = S := le_antisymm ht.2 (le_of_not_gt hLt)
          obtain ⟨M, hM, hPm⟩ := exists_pairwise_disjoint_planarDisk_merges A'
          exact ⟨M, he ▸ hg.tail (PlanarDiskPhase.mergers _ hAsep hM hPm), hPm⟩
  exact haux L.length L rfl hL s T hT

/-- Starting with any finite family, contact mergers and disjoint growth phases
reach the prescribed elapsed time with disjoint closed disks. -/
theorem exists_planarDiskEvolution (L : List PlanarDisk) (s T : ℝ) (hT : 0 ≤ T) :
    ∃ M, Relation.ReflTransGen PlanarDiskTransition (s, L) (s + T, M) ∧
      M.Pairwise (fun B D => Disjoint B.closed D.closed) := by
  obtain ⟨A, hm, hp⟩ := exists_pairwise_disjoint_planarDisk_merges L
  obtain ⟨M, hR, hPm⟩ := exists_planarDiskPhases_of_pairwise A hp s T hT
  exact ⟨M, (planarDisk_merges_evolve s hm).trans (planarDiskPhases_evolve hR), hPm⟩

/-- The radius of a disk expressed in the units at time zero. -/
def PlanarDisk.seedRadius (t : ℝ) (B : PlanarDisk) : ℝ := Real.exp (-t) * B.radius

theorem PlanarDisk.seedRadius_grow (s t : ℝ) (B : PlanarDisk) :
    (B.grow t).seedRadius (s + t) = B.seedRadius s := by
  simp only [PlanarDisk.seedRadius, PlanarDisk.grow, ← mul_assoc, ← Real.exp_add]
  rw [show -(s + t) + t = -s by ring]

theorem PlanarDisk.seedRadius_merge (s : ℝ) (B D : PlanarDisk) :
    (B.merge D).seedRadius s = B.seedRadius s + D.seedRadius s := by
  simp only [PlanarDisk.seedRadius, PlanarDisk.merge, mul_add]

private theorem sum_grow_radii (L : List PlanarDisk) (t : ℝ) :
    ((L.map (PlanarDisk.grow t)).map PlanarDisk.radius).sum = Real.exp t * (L.map PlanarDisk.radius).sum := by
  induction L with
  | nil => simp
  | cons B L ih => simp only [List.map_cons, List.sum_cons, ih, PlanarDisk.grow, mul_add]

namespace PlanarDiskTransition

theorem radius_sum {p q : ℝ × List PlanarDisk} (h : PlanarDiskTransition p q) :
    (q.2.map PlanarDisk.radius).sum = Real.exp (q.1 - p.1) * (p.2.map PlanarDisk.radius).sum := by
  cases h with
  | growth s L t ht hsep =>
      simpa only [add_sub_cancel_left] using sum_grow_radii L t
  | merger s h =>
      simpa only [sub_self, Real.exp_zero, one_mul] using h.radius_sum

theorem time_le {p q : ℝ × List PlanarDisk} (h : PlanarDiskTransition p q) : p.1 ≤ q.1 := by
  cases h with
  | growth s L t ht hsep => exact le_add_of_nonneg_right ht
  | merger s h => exact le_rfl

theorem centers_mem {K : Set Plane} (hK : Convex ℝ K) {p q : ℝ × List PlanarDisk}
    (h : PlanarDiskTransition p q) (hp : ∀ B ∈ p.2, B.center ∈ K) :
    ∀ B ∈ q.2, B.center ∈ K := by
  cases h with
  | growth s L t ht hsep =>
      intro B hB
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hB
      exact hp C hC
  | merger s h => exact h.centers_mem hK hp

theorem successor {p q : ℝ × List PlanarDisk} (h : PlanarDiskTransition p q) :
    ∀ B ∈ p.2, ∃ D ∈ q.2, B.interior ⊆ D.interior ∧ B.closed ⊆ D.closed := by
  cases h with
  | growth s L t ht hsep =>
      intro B hB
      exact ⟨B.grow t, List.mem_map_of_mem hB, PlanarDisk.subset_grow ht B⟩
  | merger s h => exact h.successor

end PlanarDiskTransition

theorem planarDiskEvolution_radius_sum {p q : ℝ × List PlanarDisk}
    (h : Relation.ReflTransGen PlanarDiskTransition p q) :
    (q.2.map PlanarDisk.radius).sum = Real.exp (q.1 - p.1) * (p.2.map PlanarDisk.radius).sum := by
  induction h with
  | refl => simp
  | @tail u v _ ht ih =>
      rw [ht.radius_sum, ih, ← mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem planarDiskEvolution_time_le {p q : ℝ × List PlanarDisk}
    (h : Relation.ReflTransGen PlanarDiskTransition p q) : p.1 ≤ q.1 := by
  induction h with
  | refl => exact le_rfl
  | tail _ ht ih => exact ih.trans ht.time_le

theorem planarDiskEvolution_centers_mem {K : Set Plane} (hK : Convex ℝ K) {p q : ℝ × List PlanarDisk}
    (h : Relation.ReflTransGen PlanarDiskTransition p q) (hp : ∀ B ∈ p.2, B.center ∈ K) :
    ∀ B ∈ q.2, B.center ∈ K := by
  induction h with
  | refl => exact hp
  | tail _ ht ih => exact ht.centers_mem hK ih

theorem planarDiskEvolution_successor {p q : ℝ × List PlanarDisk}
    (h : Relation.ReflTransGen PlanarDiskTransition p q) :
    ∀ B ∈ p.2, ∃ D ∈ q.2, B.interior ⊆ D.interior ∧ B.closed ⊆ D.closed := by
  induction h with
  | refl => exact fun B hB => ⟨B, hB, Subset.rfl, Subset.rfl⟩
  | tail _ hd ih =>
      intro B hb
      obtain ⟨D, hD, hBo, hBc⟩ := ih B hb
      obtain ⟨E, hE, hDo, hDc⟩ := hd.successor D hD
      exact ⟨E, hE, hBo.trans hDo, hBc.trans hDc⟩

private theorem sum_disk_radii_nonneg (L : List PlanarDisk) : 0 ≤ (L.map PlanarDisk.radius).sum :=
  List.sum_nonneg fun _ hx => by
    obtain ⟨B, _, rfl⟩ := List.mem_map.mp hx
    exact B.radius_pos.le

theorem sum_disk_radii_pos (L : List PlanarDisk) (hn : L ≠ []) : 0 < (L.map PlanarDisk.radius).sum := by
  cases L with
  | nil => exact (hn rfl).elim
  | cons B L => exact add_pos_of_pos_of_nonneg B.radius_pos (sum_disk_radii_nonneg L)

/-- Growth to the prescribed total radius occurs at the corresponding logarithmic time. -/
theorem exists_planarDiskEvolution_to_radius (L : List PlanarDisk) (hn : L ≠ []) (stopRadius : ℝ)
    (hstopRadius : (L.map PlanarDisk.radius).sum < stopRadius) :
    let T := Real.log (stopRadius / (L.map PlanarDisk.radius).sum)
    ∃ M, Relation.ReflTransGen PlanarDiskTransition (0, L) (T, M) ∧
      M.Pairwise (fun B D => Disjoint B.closed D.closed) ∧ (M.map PlanarDisk.radius).sum = stopRadius := by
  intro T
  have hS := sum_disk_radii_pos L hn
  have hT : 0 ≤ T := Real.log_nonneg ((one_le_div hS).2 hstopRadius.le)
  obtain ⟨M, hM₀, hp⟩ := exists_planarDiskEvolution L 0 T hT
  have hM : Relation.ReflTransGen PlanarDiskTransition (0, L) (T, M) := by rwa [zero_add] at hM₀
  refine ⟨M, hM, hp, ?_⟩
  have h := planarDiskEvolution_radius_sum hM
  change (M.map PlanarDisk.radius).sum = Real.exp (T - 0) * (L.map PlanarDisk.radius).sum at h
  rw [sub_zero, show T = Real.log (stopRadius / (L.map PlanarDisk.radius).sum) from rfl,
    Real.exp_log (div_pos (hS.trans hstopRadius) hS), div_mul_cancel₀ _ hS.ne'] at h
  exact h

private theorem radius_le_sum {L : List PlanarDisk} {B : PlanarDisk} (hB : B ∈ L) :
    B.radius ≤ (L.map PlanarDisk.radius).sum := by
  induction L with
  | nil => simp at hB
  | cons D L ih =>
      simp only [List.mem_cons] at hB
      rcases hB with rfl | hB
      · exact le_add_of_nonneg_right (sum_disk_radii_nonneg L)
      · exact (ih hB).trans (le_add_of_nonneg_left D.radius_pos.le)

/-- Every disk present before the stopping time lies strictly in the unit disk. -/
theorem planarDiskEvolution_closed_subset_unitDisk {L M : List PlanarDisk} {stopRadius t : ℝ}
    (hL : L ≠ []) (hstopRadius : (L.map PlanarDisk.radius).sum < stopRadius)
    (hcenter : ∀ B ∈ L, B.center ∈ closedBall (0 : Plane) (1 - 2 * stopRadius))
    (h : Relation.ReflTransGen PlanarDiskTransition (0, L) (t, M))
    (ht : t ≤ Real.log (stopRadius / (L.map PlanarDisk.radius).sum)) :
    ∀ B ∈ M, B.closed ⊆ ball (0 : Plane) 1 := by
  have hS := sum_disk_radii_pos L hL
  have hstopRadiuspos := hS.trans hstopRadius
  have hbound : (M.map PlanarDisk.radius).sum ≤ stopRadius := by
    have hR := planarDiskEvolution_radius_sum h
    change (M.map PlanarDisk.radius).sum = Real.exp (t - 0) * (L.map PlanarDisk.radius).sum at hR
    rw [hR, sub_zero]
    exact (mul_le_mul_of_nonneg_right ((Real.le_log_iff_exp_le (div_pos hstopRadiuspos hS)).1 ht) hS.le).trans_eq
      (div_mul_cancel₀ _ hS.ne')
  have hC := planarDiskEvolution_centers_mem (convex_closedBall (0 : Plane) (1 - 2 * stopRadius)) h hcenter
  intro B hB
  have hCr := mem_closedBall.mp (hC B hB)
  have hBr := (radius_le_sum hB).trans hbound
  exact closedBall_subset_ball' (by linarith only [hCr, hBr, hstopRadiuspos])

end Thesis
