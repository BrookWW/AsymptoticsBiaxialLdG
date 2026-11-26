module

public import Thesis.MeasureGeometry.PlanarGrowthEnergy

/-! The finite disk-cover radius and the centered initial covers for planar ball growth. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff Matrix.Norms.Frobenius NNReal

namespace Thesis

/-- Radial metric projection onto the closed Euclidean disk of nonnegative radius. -/
def planarCenterProjection (R : ℝ≥0) (x : Plane) : Plane :=
  if ‖x‖ ≤ R then x else ((R : ℝ) / ‖x‖) • x

theorem planarCenterProjection_mem (R : ℝ≥0) (x : Plane) :
    planarCenterProjection R x ∈ closedBall (0 : Plane) R := by
  rw [mem_closedBall, dist_zero_right, planarCenterProjection]
  split_ifs with h
  · exact h
  · have hn : 0 < ‖x‖ := R.property.trans_lt (lt_of_not_ge h)
    have hratio : 0 ≤ (R : ℝ) / ‖x‖ := div_nonneg R.property hn.le
    calc
      _ = ‖(R : ℝ) / ‖x‖‖ * ‖x‖ := norm_smul _ _
      _ = R := by rw [Real.norm_of_nonneg hratio, div_mul_cancel₀ _ hn.ne']
      _ ≤ _ := le_rfl

theorem dist_planarCenterProjection_le (R : ℝ≥0) (x y : Plane) (hy : y ∈ closedBall (0 : Plane) R) :
    dist (planarCenterProjection R x) y ≤ dist x y := by
  rw [planarCenterProjection]
  split_ifs with h
  · exact le_rfl
  · have hx : 0 < ‖x‖ := R.property.trans_lt (lt_of_not_ge h)
    have hy' : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
    let a : ℝ := (R : ℝ) / ‖x‖
    have ha : a ≤ 1 := (div_le_one hx).2 (lt_of_not_ge h).le
    have hinner : 0 ≤ inner ℝ x (a • x - y) := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      have hscale : a * ‖x‖ ^ 2 = (R : ℝ) * ‖x‖ := by
        dsimp only [a]
        field_simp [hx.ne']
      rw [hscale]
      exact sub_nonneg.mpr ((real_inner_le_norm x y).trans
        (by rw [mul_comm (R : ℝ)]; exact mul_le_mul_of_nonneg_left hy' hx.le))
    have hproduct : 0 ≤ inner ℝ (a • x - y) ((1 - a) • x) := by
      rw [real_inner_smul_right, real_inner_comm x (a • x - y)]
      exact mul_nonneg (sub_nonneg.mpr ha) hinner
    have hvec : (a • x - y) + (1 - a) • x = x - y := by module
    rw [dist_eq_norm, dist_eq_norm]
    change ‖a • x - y‖ ≤ ‖x - y‖
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← hvec, norm_add_sq_real]
    nlinarith only [hproduct, sq_nonneg ‖(1 - a) • x‖]

/-- Finite open-disk covers of the compact set, measured by the actual sum of the radii. -/
def planarCoverSums (K : TopologicalSpace.Compacts Plane) : Set ℝ :=
  {s | ∃ L : List PlanarDisk, (K : Set Plane) ⊆ ⋃ B ∈ L, B.interior ∧ (L.map PlanarDisk.radius).sum = s}

/-- The manuscript's disk-cover radius for the compact core. -/
def planarCoverRadius (K : TopologicalSpace.Compacts Plane) : ℝ := sInf (planarCoverSums K)

theorem planarCoverSums_nonempty (K : TopologicalSpace.Compacts Plane) : (planarCoverSums K).Nonempty := by
  obtain ⟨R, hR⟩ := K.isCompact.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun x : Plane => x) K)
  let B : PlanarDisk := ⟨0, max 1 (R + 1), zero_lt_one.trans_le (le_max_left _ _)⟩
  refine ⟨B.radius, [B], ?_, by simp⟩
  intro x hx
  refine mem_iUnion₂.mpr ⟨B, by simp, ?_⟩
  change dist x 0 < max 1 (R + 1)
  rw [dist_zero_right]
  exact (hR x hx).trans_lt ((lt_add_of_pos_right R zero_lt_one).trans_le (le_max_right _ _))

theorem planarCoverRadius_nonneg (K : TopologicalSpace.Compacts Plane) : 0 ≤ planarCoverRadius K := by
  apply le_csInf (planarCoverSums_nonempty K)
  rintro s ⟨L, _, rfl⟩
  exact List.sum_nonneg fun r hr => by
    obtain ⟨B, _, rfl⟩ := List.mem_map.mp hr
    exact B.radius_pos.le

theorem exists_centered_planarCover_below (K : TopologicalSpace.Compacts Plane)
    (hK : (K : Set Plane).Nonempty) {R s : ℝ}
    (hKin : (K : Set Plane) ⊆ closedBall (0 : Plane) R) (hs : planarCoverRadius K < s) :
    ∃ L : List PlanarDisk, L ≠ [] ∧ (K : Set Plane) ⊆ ⋃ B ∈ L, B.interior ∧
      (∀ B ∈ L, B.center ∈ closedBall (0 : Plane) R) ∧ (L.map PlanarDisk.radius).sum < s := by
  obtain ⟨r, ⟨M, hCov, rfl⟩, hRadii⟩ := exists_lt_of_csInf_lt (planarCoverSums_nonempty K) hs
  have hR : 0 ≤ R := by
    obtain ⟨x, hx⟩ := hK
    exact dist_nonneg.trans (mem_closedBall.mp (hKin hx))
  let P : PlanarDisk → PlanarDisk := fun B =>
    ⟨planarCenterProjection ⟨R, hR⟩ B.center, B.radius, B.radius_pos⟩
  let L := M.map P
  have hLcov : (K : Set Plane) ⊆ ⋃ B ∈ L, B.interior := by
    intro x hx
    obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.mp (hCov hx)
    refine mem_iUnion₂.mpr ⟨P B, List.mem_map_of_mem hB, ?_⟩
    have hdist := dist_planarCenterProjection_le ⟨R, hR⟩ B.center x (hKin hx)
    have hdist' : dist x (P B).center ≤ dist x B.center := by
      rw [dist_comm x (P B).center, dist_comm x B.center]
      exact hdist
    exact mem_ball.mpr (hdist'.trans_lt (mem_ball.mp hxB))
  have hLnonempty : L ≠ [] := by
    intro h
    obtain ⟨x, hx⟩ := hK
    have hc := hLcov hx
    rw [h] at hc
    simp at hc
  refine ⟨L, hLnonempty, hLcov, ?_, ?_⟩
  · intro B hB
    obtain ⟨D, _, rfl⟩ := List.mem_map.mp hB
    exact planarCenterProjection_mem ⟨R, hR⟩ D.center
  · change ((M.map P).map PlanarDisk.radius).sum < s
    rw [List.map_map]
    exact hRadii

theorem unitBoundary_avoids_centered_compactCore {K : TopologicalSpace.Compacts Plane} {R : ℝ}
    (hR : 0 < R) (hKin : (K : Set Plane) ⊆ closedBall (0 : Plane) (1 - 2 * R)) :
    ∀ x ∈ sphere unitPlanarDisk.center unitPlanarDisk.radius, x ∉ (K : Set Plane) := by
  intro x hx hxK
  have h := mem_closedBall.mp (hKin hxK)
  change dist x 0 = 1 at hx
  rw [hx] at h
  linarith only [h, hR]

/-- Every positive radius strictly above the cover-radius infimum yields a
logarithmic exterior-energy estimate. -/
theorem planarVacuum_exterior_energy_ge_of_radius_lt (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) (K : TopologicalSpace.Compacts Plane) (hK : (K : Set Plane).Nonempty)
    (hVac : ∀ x ∈ unitPlanarDisk.closed, x ∉ (K : Set Plane) → Q x ∈ vacuum a)
    (R : ℝ) (hR : 0 < R) (hKin : (K : Set Plane) ⊆ closedBall (0 : Plane) (1 - 2 * R))
    {s : ℝ} (hs : planarCoverRadius K < s) (hsR : s < R) :
    let hB := fun x (hx : x ∈ sphere unitPlanarDisk.center unitPlanarDisk.radius) =>
      hVac x (sphere_subset_closedBall hx) (unitBoundary_avoids_centered_compactCore hR hKin x hx)
    Real.log (R / s) *
      nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous unitPlanarDisk hB) ≤
        planarDiskExteriorEnergy Q K unitPlanarDisk := by
  intro hB
  obtain ⟨L, hne, hcov, hcent, hsum⟩ := exists_centered_planarCover_below K hK hKin hs
  have hL := sum_disk_radii_pos L hne
  have hsPos := hL.trans hsum
  have e := planarVacuum_exterior_energy_ge_of_finite_cover a Q hQ K K.isCompact hVac
    L hne R (hsum.trans hsR) hcent hcov
  have hLog : Real.log (R / s) ≤ Real.log (R / (L.map PlanarDisk.radius).sum) :=
    Real.log_le_log (div_pos hR hsPos) (div_le_div_of_nonneg_left hR.le hL hsum.le)
  exact (mul_le_mul_of_nonneg_right hLog (nativeVacuumCircleCost_nonneg a _)).trans e

/-- The cover-radius logarithmic lower bound for smooth ambient maps vacuum-valued off the core. -/
theorem planarVacuum_exterior_energy_ge_of_coverRadius (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) (K : TopologicalSpace.Compacts Plane)
    (hVac : ∀ x ∈ unitPlanarDisk.closed, x ∉ (K : Set Plane) → Q x ∈ vacuum a)
    (R : ℝ) (hR : 0 < R) (hKin : (K : Set Plane) ⊆ closedBall (0 : Plane) (1 - 2 * R)) :
    let hB := fun x (hx : x ∈ sphere unitPlanarDisk.center unitPlanarDisk.radius) =>
      hVac x (sphere_subset_closedBall hx) (unitBoundary_avoids_centered_compactCore hR hKin x hx)
    Real.log (R / planarCoverRadius K) *
      nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous unitPlanarDisk hB) ≤
        planarDiskExteriorEnergy Q K unitPlanarDisk := by
  intro hB
  let d := planarCoverRadius K
  let E := planarDiskExteriorEnergy Q K unitPlanarDisk
  let e := nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous unitPlanarDisk hB)
  have hE : 0 ≤ E := integral_nonneg (planarSmoothDirichletDensity_nonneg Q)
  have he : 0 ≤ e := nativeVacuumCircleCost_nonneg a _
  have hd₀ : 0 ≤ d := planarCoverRadius_nonneg K
  by_cases hd : d = 0
  · change Real.log (R / d) * e ≤ E
    simpa only [hd, div_zero, Real.log_zero, zero_mul] using hE
  have hdPos : 0 < d := lt_of_le_of_ne hd₀ (Ne.symm hd)
  by_cases hlarge : R ≤ d
  · have hLog := Real.log_nonpos (div_nonneg hR.le hd₀) ((div_le_one hdPos).2 hlarge)
    exact (mul_nonpos_of_nonpos_of_nonneg hLog he).trans hE
  have hSmall : d < R := lt_of_not_ge hlarge
  have hK : (K : Set Plane).Nonempty := by
    by_contra h
    have hem : (K : Set Plane) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hzero : 0 ∈ planarCoverSums K := ⟨[], by rw [hem]; exact empty_subset _, rfl⟩
    have hbb : BddBelow (planarCoverSums K) := by
      refine ⟨0, ?_⟩
      rintro s ⟨L, _, rfl⟩
      exact List.sum_nonneg (fun _ hL => by
        obtain ⟨B, _, rfl⟩ := List.mem_map.mp hL
        exact B.radius_pos.le)
    exact (not_le_of_gt hdPos) (csInf_le hbb hzero)
  let F (s : ℝ) := Real.log (R / max s (d / 2)) * e
  have hdenPos (s : ℝ) : 0 < max s (d / 2) :=
    (div_pos hdPos (by norm_num)).trans_le (le_max_right _ _)
  have hfrac : Continuous (fun s : ℝ => R / max s (d / 2)) :=
    continuous_const.div (continuous_id.max continuous_const) fun s => (hdenPos s).ne'
  have hF : Continuous F :=
    (hfrac.log (fun s => (div_pos hR (hdenPos s)).ne')).mul continuous_const
  let C : Set ℝ := {s | F s ≤ E}
  have hC : IsClosed C := isClosed_le hF continuous_const
  have hSub : Ioo d R ⊆ C := by
    intro s hs
    change Real.log (R / max s (d / 2)) * e ≤ E
    rw [max_eq_left (by linarith only [hs.1, hdPos])]
    exact planarVacuum_exterior_energy_ge_of_radius_lt a Q hQ K hK hVac R hR hKin hs.1 hs.2
  have hEnd : d ∈ closure (Ioo d R) := by rw [closure_Ioo hSmall.ne]; exact ⟨le_rfl, hSmall.le⟩
  have hlim := (hC.closure_subset_iff.2 hSub) hEnd
  change Real.log (R / max d (d / 2)) * e ≤ E at hlim
  rwa [max_eq_left (by linarith only [hd₀])] at hlim

/-- A zero-radius defect cannot support a nontrivial boundary charge in the smooth exterior estimate. -/
theorem planarVacuum_outerCost_eq_zero_of_coverRadius_zero (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) (K : TopologicalSpace.Compacts Plane)
    (hVac : ∀ x ∈ unitPlanarDisk.closed, x ∉ (K : Set Plane) → Q x ∈ vacuum a)
    (R : ℝ) (hR : 0 < R) (hKin : (K : Set Plane) ⊆ closedBall (0 : Plane) (1 - 2 * R))
    (hzero : planarCoverRadius K = 0) :
    let hB := fun x (hx : x ∈ sphere unitPlanarDisk.center unitPlanarDisk.radius) =>
      hVac x (sphere_subset_closedBall hx) (unitBoundary_avoids_centered_compactCore hR hKin x hx)
    nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous unitPlanarDisk hB) = 0 := by
  classical
  intro hB
  let e := nativeVacuumCircleCost a (vacuumDiskCircleTrace a Q hQ.continuous unitPlanarDisk hB)
  by_cases hem : (K : Set Plane).Nonempty
  · by_contra hne
    have he : 0 < e := lt_of_le_of_ne (nativeVacuumCircleCost_nonneg a _) (Ne.symm hne)
    let E := planarDiskExteriorEnergy Q K unitPlanarDisk
    have hE : 0 ≤ E := integral_nonneg (planarSmoothDirichletDensity_nonneg Q)
    let w := E / e + 1
    have hw : 0 < w := add_pos_of_nonneg_of_pos (div_nonneg hE he.le) zero_lt_one
    let s := R / Real.exp w
    have hs : 0 < s := div_pos hR (Real.exp_pos _)
    have hsR : s < R := by
      apply (div_lt_iff₀ (Real.exp_pos _)).2
      have he₁ : 1 < Real.exp w := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hw
      simpa only [mul_one] using mul_lt_mul_of_pos_left he₁ hR
    have hLog : Real.log (R / s) = w := by
      have hRatio : R / s = Real.exp w := by
        dsimp only [s]
        field_simp [hR.ne', (Real.exp_pos w).ne']
      rw [hRatio, Real.log_exp]
    have hEst := planarVacuum_exterior_energy_ge_of_radius_lt a Q hQ K hem hVac R hR hKin
      (show planarCoverRadius K < s by rwa [hzero]) hsR
    change Real.log (R / s) * e ≤ E at hEst
    rw [hLog, show w * e = E + e by dsimp only [w]; field_simp [he.ne']] at hEst
    linarith only [hEst, he]
  · have hEmpty := Set.not_nonempty_iff_eq_empty.mp hem
    have hU (x : Plane) (hx : x ∈ unitPlanarDisk.closed) : Q x ∈ vacuum a :=
      hVac x hx (by simp [hEmpty])
    let v (x : Plane) : vacuum a :=
      if h : Q x ∈ vacuum a then ⟨Q x, h⟩
      else vacuumQuaternionProjection a (sphereOfQuaternion 1 norm_one)
    have hvVal (x : Plane) (hx : x ∈ unitPlanarDisk.closed) : (v x).val = Q x := by
      change (if h : Q x ∈ vacuum a then (⟨Q x, h⟩ : vacuum a)
        else vacuumQuaternionProjection a (sphereOfQuaternion 1 norm_one)).val = Q x
      rw [dif_pos (hU x hx)]
    have hv : ContinuousOn v unitPlanarDisk.closed :=
      Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
        (hQ.continuous.continuousOn.congr (fun x hx => hvVal x hx))
    have hf : vacuumDiskCircleTrace a Q hQ.continuous unitPlanarDisk hB =
        planarBoundaryTrace unitPlanarDisk v hv sphere_subset_closedBall := by
      apply ContinuousMap.ext
      intro z
      apply Subtype.ext
      change Q (unitPlanarDisk.center + unitPlanarDisk.radius • z.val) =
        (v (diskCone unitPlanarDisk (0, z)).val).val
      rw [hvVal _ (diskCone unitPlanarDisk (0, z)).property, diskCone_zero_val]
    rw [hf, nativeVacuumCircleCost_homotopic a (planarBoundaryTrace_homotopic_const unitPlanarDisk v hv),
      nativeVacuumCircleCost_const]

end Thesis
