module

public import Thesis.MeasureGeometry.PlanarLevelGeometry
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Localizing and scaling the exterior estimate on centered planar disks. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff Matrix.Norms.Frobenius

namespace Thesis

/-- A C^n function on an open neighborhood of a compact set agrees
near that set with a global C^n function. -/
theorem exists_contDiff_eq_near_compact_of_order {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞} {U K : Set Plane} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {q : Plane → F} (hq : ContDiffOn ℝ n q U) :
    ∃ Q : Plane → F, ContDiff ℝ n Q ∧ ∀ x ∈ K, Q =ᶠ[𝓝 x] q := by
  obtain ⟨g, hgSupp, hg, hgRange⟩ := hU.exists_contDiff_support_eq (n := n)
  have hgPos (x : Plane) (hx : x ∈ U) : 0 < g x := by
    have hgz : g x ≠ 0 := Function.mem_support.mp (hgSupp ▸ hx)
    exact lt_of_le_of_ne (hgRange (mem_range_self x)).1 hgz.symm
  obtain ⟨δ, hδ, hGδ⟩ := hK.exists_forall_le' hg.continuous.continuousOn (fun x hx => hgPos x (hKU hx))
  let η (x : Plane) := Real.smoothTransition ((g x - δ / 4) / (δ / 4))
  let Q (x : Plane) : F := η x • q x
  have hη : ContDiff ℝ n η :=
    Real.smoothTransition.contDiff.comp ((hg.sub contDiff_const).div_const _)
  refine ⟨Q, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · exact hη.contDiffAt.smul ((hq x hx).contDiffAt (hU.mem_nhds hx))
    · have hgz : g x = 0 := Function.notMem_support.mp (hgSupp ▸ hx)
      have hh : {y | g y < δ / 4} ∈ 𝓝 x :=
        (isOpen_lt hg.continuous continuous_const).mem_nhds (by change g x < δ / 4; rw [hgz]; positivity)
      refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq (f₁ := Q) ?_
      filter_upwards [hh] with y hy
      have hy' : (g y - δ / 4) / (δ / 4) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy.le) (by positivity)
      change η y • q y = 0
      dsimp only [η]
      rw [Real.smoothTransition.zero_of_nonpos hy', zero_smul]
  · intro x hx
    have hgt : δ / 2 < δ := by linarith
    have hN : {y | δ / 2 < g y} ∈ 𝓝 x :=
      (isOpen_lt continuous_const hg.continuous).mem_nhds (hgt.trans_le (hGδ x hx))
    change ∀ᶠ y in 𝓝 x, η y • q y = q y
    filter_upwards [hN] with y hy
    have hy' : 1 ≤ (g y - δ / 4) / (δ / 4) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith only [show δ / 2 < g y from hy])
    dsimp only [η]
    rw [Real.smoothTransition.one_of_one_le hy', one_smul]

theorem exists_contDiff_eq_near_compact {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set Plane} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {q : Plane → F} (hq : ContDiffOn ℝ 1 q U) :
    ∃ Q : Plane → F, ContDiff ℝ 1 Q ∧ ∀ x ∈ K, Q =ᶠ[𝓝 x] q :=
  exists_contDiff_eq_near_compact_of_order (n := 1) hU hK hKU hq

theorem scaled_planarSmoothDirichletDensity (Q : Plane → S0) (hQ : ContDiff ℝ 1 Q)
    (r : ℝ) (hr : 0 < r) (x : Plane) :
    planarSmoothDirichletDensity (fun y => Q (r • y)) x =
      r ^ 2 * planarSmoothDirichletDensity Q (r • x) := by
  let L : Plane →L[ℝ] Plane := r • ContinuousLinearMap.id ℝ Plane
  have hDer (j : Fin 2) :
      fderiv ℝ (fun y => (Q (r • y) : Tensor)) x (EuclideanSpace.single j 1) =
        r • fderiv ℝ (fun y => (Q y : Tensor)) (r • x) (EuclideanSpace.single j 1) := by
    let T (y : Plane) : Tensor := (Q y).val
    have hF : DifferentiableAt ℝ T (L x) :=
      ((symmetricTraceless.subtypeL.contDiff.comp hQ).contDiffAt.differentiableAt one_ne_zero)
    have hD : fderiv ℝ (T ∘ L) x = (fderiv ℝ T (L x)).comp L := by
      calc
        _ = (fderiv ℝ T (L x)).comp (fderiv ℝ (⇑L) x) :=
          fderiv_comp x hF L.differentiableAt
        _ = _ := congrArg ((fderiv ℝ T (L x)).comp) L.fderiv
    have hJ := congrArg (fun D : Plane →L[ℝ] Tensor => D (EuclideanSpace.single j 1)) hD
    change fderiv ℝ (T ∘ L) x (EuclideanSpace.single j 1) =
      fderiv ℝ T (r • x) (r • EuclideanSpace.single j 1) at hJ
    exact hJ.trans (map_smul _ _ _)
  simp_rw [planarSmoothDirichletDensity, hDer, norm_smul, Real.norm_of_nonneg hr.le, mul_pow,
    ← Finset.mul_sum]
  ring

private theorem scaled_planarDiskExteriorEnergy (Q : Plane → S0) (hQ : ContDiff ℝ 1 Q)
    (r : ℝ) (hr : 0 < r) (K : TopologicalSpace.Compacts Plane) :
    planarDiskExteriorEnergy (fun y => Q (r • y)) (planarDilateCore r⁻¹ K) unitPlanarDisk =
      planarDiskExteriorEnergy Q K ⟨0, r, hr⟩ := by
  classical
  let A := ball (0 : Plane) r \ (K : Set Plane)
  let B := ball (0 : Plane) 1 \ (planarDilateCore r⁻¹ K : Set Plane)
  have hA : MeasurableSet A := measurableSet_ball.diff K.isCompact.isClosed.measurableSet
  have hB : MeasurableSet B := measurableSet_ball.diff (planarDilateCore r⁻¹ K).isCompact.isClosed.measurableSet
  have hPre : ∀ x : Plane, x ∈ B ↔ r • x ∈ A := by
    intro x
    have hK : x ∈ (planarDilateCore r⁻¹ K : Set Plane) ↔ r • x ∈ (K : Set Plane) := by
      change x ∈ (fun y : Plane => r⁻¹ • y) '' (K : Set Plane) ↔ _
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using hy
      · intro h
        exact ⟨r • x, h, by simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]⟩
    simp only [A, B, Set.mem_sdiff, mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le, hK]
    have hlt : r * ‖x‖ < r ↔ ‖x‖ < 1 := by
      simpa only [mul_one] using (mul_lt_mul_iff_right₀ hr : r * ‖x‖ < r * 1 ↔ ‖x‖ < 1)
    rw [hlt]
  have hInd : (fun x : Plane => B.indicator (fun y => planarSmoothDirichletDensity Q (r • y)) x) =
      fun x => A.indicator (planarSmoothDirichletDensity Q) (r • x) := by
    funext x
    simp only [indicator_apply, hPre x]
  have hDim : Module.finrank ℝ Plane = 2 := by simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  change (∫ x in B, planarSmoothDirichletDensity (fun y => Q (r • y)) x) =
    ∫ x in A, planarSmoothDirichletDensity Q x
  simp_rw [scaled_planarSmoothDirichletDensity Q hQ r hr]
  rw [integral_const_mul, ← integral_indicator hB, hInd,
    Measure.integral_comp_smul_of_nonneg volume _ r (hR := hr.le), hDim, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul, integral_indicator hA]

/-- The logarithmic exterior estimate on a disk of any positive radius.
A nonzero boundary charge also forces its compact core to have positive
disk-cover radius. -/
theorem planarVacuum_centered_exterior_lower (a : BulkCoefficients) (Q : Plane → S0)
    (hQ : ContDiff ℝ 1 Q) (K : TopologicalSpace.Compacts Plane) {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ)
    (hKin : (K : Set Plane) ⊆ closedBall (0 : Plane) (r - 2 * ℓ))
    (hVac : ∀ x ∈ closedBall (0 : Plane) r, x ∉ (K : Set Plane) → Q x ∈ vacuum a)
    (hB : ∀ z : NativeCircle, Q (0 + r • z.val) ∈ vacuum a) :
    let e := nativeVacuumCircleCost a (planarVacuumCircleTrace a Q hQ.continuous 0 r hB)
    (0 < e → 0 < planarCoverRadius K) ∧
    Real.log (ℓ / planarCoverRadius K) * e ≤ planarDiskExteriorEnergy Q K ⟨0, r, hr⟩ := by
  let P (x : Plane) := Q (r • x)
  have hP : ContDiff ℝ 1 P := hQ.comp ((r • ContinuousLinearMap.id ℝ Plane).contDiff)
  let J := planarDilateCore r⁻¹ K
  have hJin : (J : Set Plane) ⊆ closedBall (0 : Plane) (1 - 2 * (ℓ / r)) := by
    intro y hy
    change y ∈ (fun x : Plane => r⁻¹ • x) '' (K : Set Plane) at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : ‖x‖ ≤ r - 2 * ℓ := by
      simpa only [dist_zero_right] using mem_closedBall.mp (hKin hx)
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
      ← div_eq_inv_mul, div_le_iff₀ hr]
    have hEq : (1 - 2 * (ℓ / r)) * r = r - 2 * ℓ := by
      field_simp [hr.ne']
    rwa [hEq]
  have hPVac : ∀ x ∈ unitPlanarDisk.closed, x ∉ (J : Set Plane) → P x ∈ vacuum a := by
    intro x hx hxJ
    have hx' : ‖x‖ ≤ 1 := by simpa only [unitPlanarDisk, PlanarDisk.closed, dist_zero_right] using mem_closedBall.mp hx
    apply hVac (r • x)
    · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hx' hr.le
    · intro h
      apply hxJ
      exact ⟨r • x, h, by simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]⟩
  have hℓr : 0 < ℓ / r := div_pos hℓ hr
  let hPB := fun x (hx : x ∈ sphere unitPlanarDisk.center unitPlanarDisk.radius) =>
    hPVac x (sphere_subset_closedBall hx) (unitBoundary_avoids_centered_compactCore hℓr hJin x hx)
  have hTrace : vacuumDiskCircleTrace a P hP.continuous unitPlanarDisk hPB =
      planarVacuumCircleTrace a Q hQ.continuous 0 r hB := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    simp only [vacuumDiskCircleTrace, planarVacuumCircleTrace, unitPlanarDisk, one_smul, zero_add, P,
      ContinuousMap.coe_mk]
  let e := nativeVacuumCircleCost a (planarVacuumCircleTrace a Q hQ.continuous 0 r hB)
  have hBound := planarVacuum_exterior_energy_ge_of_coverRadius a P hP J hPVac (ℓ / r) hℓr hJin
  change Real.log ((ℓ / r) / planarCoverRadius J) *
    nativeVacuumCircleCost a (vacuumDiskCircleTrace a P hP.continuous unitPlanarDisk hPB) ≤ _ at hBound
  rw [hTrace] at hBound
  have hrad : planarCoverRadius J = r⁻¹ * planarCoverRadius K :=
    planarCoverRadius_dilate r⁻¹ (inv_pos.mpr hr) K
  have hquot : (ℓ / r) / planarCoverRadius J = ℓ / planarCoverRadius K := by
    by_cases hz : planarCoverRadius K = 0
    · simp only [hrad, hz, mul_zero, div_zero]
    · rw [hrad]
      field_simp [hr.ne', hz]
  change (0 < e → 0 < planarCoverRadius K) ∧ _
  refine ⟨?_, ?_⟩
  · intro he
    by_contra! h
    have hz : planarCoverRadius K = 0 := le_antisymm h (planarCoverRadius_nonneg K)
    have hJz : planarCoverRadius J = 0 := by rw [hrad, hz, mul_zero]
    have hZero := planarVacuum_outerCost_eq_zero_of_coverRadius_zero a P hP J hPVac (ℓ / r) hℓr hJin hJz
    change nativeVacuumCircleCost a (vacuumDiskCircleTrace a P hP.continuous unitPlanarDisk hPB) = 0 at hZero
    rw [hTrace] at hZero
    exact he.ne' hZero
  · rw [hquot] at hBound
    exact hBound.trans_eq (scaled_planarDiskExteriorEnergy Q hQ r hr K)

end Thesis
