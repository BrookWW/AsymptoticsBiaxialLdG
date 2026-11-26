module

public import HarmonicMaps.Frozen.TubularProjection
public import Thesis.Foundation.VacuumTarget

/-! Nearest-point projection and quadratic bulk bounds near the biaxial vacuum. -/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Filter Set
open scoped BigOperators ContDiff Matrix.Norms.Frobenius Topology

namespace Thesis

/-- The open Frobenius neighborhood of the vacuum of radius `r`. -/
def vacuumTube (a : BulkCoefficients) (r : ℝ) : Set S0 :=
  {A | Metric.infDist A (vacuum a) < r}

theorem isOpen_vacuumTube (a : BulkCoefficients) (r : ℝ) : IsOpen (vacuumTube a r) :=
  isOpen_lt (Metric.continuous_infDist_pt (vacuum a)) continuous_const

theorem vacuum_subset_vacuumTube (a : BulkCoefficients) {r : ℝ} (hr : 0 < r) :
    vacuum a ⊆ vacuumTube a r := by
  intro A hA
  change Metric.infDist A (vacuum a) < r
  rw [Metric.infDist_zero_of_mem hA]
  exact hr

theorem infDist_frobeniusCoordinateEquiv_vacuum (a : BulkCoefficients) (A : S0) :
    Metric.infDist (frobeniusCoordinateEquiv A) (vacuumCompactSmoothEmbeddedTarget a).carrierSet =
      Metric.infDist A (vacuum a) := by
  rw [vacuumCompactSmoothEmbeddedTarget_carrierSet]
  exact Metric.infDist_image frobeniusCoordinateEquiv.isometry

/-- The nearest vacuum point is defined on its tube, with a smooth ambient extension. -/
structure VacuumTubularProjection (a : BulkCoefficients) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  project : vacuumTube a radius → vacuum a
  nearest (A : vacuumTube a radius) (P : vacuum a) : dist A.val (project A).val ≤ dist A.val P.val
  unique (A : vacuumTube a radius) (P : vacuum a) :
    (∀ P' : vacuum a, dist A.val P.val ≤ dist A.val P'.val) → P = project A
  extend : S0 → S0
  contDiff_extend : ContDiff ℝ ∞ extend
  extend_eq (A : vacuumTube a radius) : extend A.val = (project A).val

namespace VacuumTubularProjection

variable {a : BulkCoefficients} (p : VacuumTubularProjection a)

theorem dist_eq_infDist (A : vacuumTube a p.radius) :
    dist A.val (p.project A).val = Metric.infDist A.val (vacuum a) := by
  apply le_antisymm
  · exact (Metric.le_infDist (vacuum_nonempty a)).2 (fun _ hP => p.nearest A ⟨_, hP⟩)
  · exact Metric.infDist_le_dist_of_mem (p.project A).property

theorem strict_nearest (A : vacuumTube a p.radius) {P : vacuum a} (hP : P ≠ p.project A) :
    dist A.val (p.project A).val < dist A.val P.val := by
  apply lt_of_le_of_ne (p.nearest A P)
  intro h
  exact hP (p.unique A P fun P' => h ▸ p.nearest A P')

theorem project_of_mem {A : S0} (hA : A ∈ vacuum a) :
    p.project ⟨A, vacuum_subset_vacuumTube a p.radius_pos hA⟩ = ⟨A, hA⟩ := by
  symm
  apply p.unique
  intro P
  simpa only [dist_self] using dist_nonneg (x := A) (y := P.val)

end VacuumTubularProjection

theorem nonempty_vacuumTubularProjection (a : BulkCoefficients) :
    Nonempty (VacuumTubularProjection a) := by
  let N := vacuumCompactSmoothEmbeddedTarget a
  let e := frobeniusCoordinateEquiv
  obtain ⟨r, hr, _, hsub, _, hnear, _, _, _, _, _, _, _, Q, hQ, hQeq, _⟩ :=
    HarmonicMaps.tubularProjection_complete 5 N
  let d := min r (1 / 2)
  have hd : 0 < d := lt_min hr (by norm_num)
  have hdr : d ≤ r := min_le_left _ _
  have hd₁ : d < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let toCoord (P : vacuum a) : N.Carrier :=
    ⟨e P.val, mem_vacuumCompactSmoothEmbeddedTarget_iff.2 (by
      change e.symm (e P.val) ∈ vacuum a
      rw [e.symm_apply_apply]
      exact P.property)⟩
  let toTensor (P : N.Carrier) : vacuum a :=
    ⟨e.symm P.val, mem_vacuumCompactSmoothEmbeddedTarget_iff.1 P.property⟩
  have hround (P : vacuum a) : toTensor (toCoord P) = P :=
    Subtype.ext (LinearIsometryEquiv.symm_apply_apply e P.val)
  let narrow (A : vacuumTube a d) : {z | Metric.infDist z N.carrierSet < 2 * r} :=
    ⟨e A.val, by
      change Metric.infDist (e A.val) N.carrierSet < 2 * r
      rw [infDist_frobeniusCoordinateEquiv_vacuum]
      exact (A.property.trans_le hdr).trans (by linarith only [hr])⟩
  let upstream (A : vacuumTube a d) : HarmonicMaps.tubularTube 5 N :=
    ⟨(narrow A).val, hsub (narrow A).property⟩
  let project (A : vacuumTube a d) : vacuum a :=
    toTensor (HarmonicMaps.tubularProjection 5 N (upstream A))
  have hdist (A : vacuumTube a d) (P : N.Carrier) :
      dist A.val (toTensor P).val = dist (narrow A).val P.val := by
    rw [← e.isometry.dist_eq A.val (toTensor P).val]
    change dist (e A.val) (e (e.symm P.val)) = dist (e A.val) P.val
    rw [e.apply_symm_apply]
  refine ⟨{
    radius := d
    radius_pos := hd
    radius_lt_one := hd₁
    project := project
    nearest := ?_
    unique := ?_
    extend := e.symm ∘ Q ∘ e
    contDiff_extend := ?_
    extend_eq := ?_ }⟩
  · intro A P
    rw [← hround P, hdist, hdist]
    exact (hnear (narrow A)).1 (toCoord P)
  · intro A P hP
    have hMin (P' : N.Carrier) : dist (narrow A).val (toCoord P).val ≤ dist (narrow A).val P'.val := by
      rw [← hdist, ← hdist, hround]
      exact hP (toTensor P')
    have hUnique := (hnear (narrow A)).2 (toCoord P) hMin
    exact (hround P).symm.trans (congrArg toTensor hUnique)
  · exact e.symm.toContinuousLinearEquiv.contDiff.comp (hQ.comp e.toContinuousLinearEquiv.contDiff)
  · intro A
    have hA : Metric.infDist (upstream A).val N.carrierSet < r := by
      change Metric.infDist (e A.val) N.carrierSet < r
      rw [infDist_frobeniusCoordinateEquiv_vacuum]
      exact A.property.trans_le hdr
    exact congrArg e.symm (hQeq (upstream A) hA)

/-- A nearest-point projection on a positive open tube around the actual vacuum. -/
@[no_expose] def vacuumTubularProjection (a : BulkCoefficients) : VacuumTubularProjection a :=
  Classical.choice (nonempty_vacuumTubularProjection a)

/-- The trace-invariant error from the level defining the vacuum. -/
def vacuumInvariantError (a : BulkCoefficients) (A : S0) : ℝ :=
  ‖vacuumInvariants A - (2 * vacuumRadius a ^ 2, 0)‖

private theorem exists_local_levelSet_error_bound
    {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup T] [NormedSpace ℝ T]
    [CompleteSpace E] {f : E → F} {x : E} (L : E ≃L[ℝ] F × T) (hCont : Continuous f)
    (hf : HasStrictFDerivAt f ((ContinuousLinearMap.fst ℝ F T).comp L.toContinuousLinearMap) x) :
    ∃ (K : ℝ) (U : Set E), 0 < K ∧ IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, Metric.infDist y (f ⁻¹' {f x}) ≤ K * ‖f y - f x‖ := by
  let Tcoord := (ContinuousLinearMap.snd ℝ F T).comp L.toContinuousLinearMap
  let g (y : E) := (f y, Tcoord y)
  have hg : HasStrictFDerivAt g L.toContinuousLinearMap x := by
    refine (hf.prodMk (Tcoord.hasStrictFDerivAt (x := x))).congr_fderiv ?_
    ext y <;> rfl
  let e := hg.toOpenPartialHomeomorph (f' := L) g
  have hx : x ∈ e.source := hg.mem_toOpenPartialHomeomorph_source (f' := L)
  have hgx : g x ∈ e.target := hg.image_mem_toOpenPartialHomeomorph_target (f' := L)
  obtain ⟨K, s, hs, hLip⟩ := (hg.to_localInverse (f' := L)).exists_lipschitzOnWith
  have hLip' : LipschitzOnWith K e.symm s := hLip
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp (inter_mem hs (e.open_target.mem_nhds hgx))
  let U := e.source ∩ g ⁻¹' Metric.ball (g x) ε
  have hgCont : Continuous g := hCont.prodMk Tcoord.continuous
  refine ⟨(K : ℝ) + 1, U, by positivity, e.open_source.inter (Metric.isOpen_ball.preimage hgCont),
    ⟨hx, Metric.mem_ball_self hε⟩, ?_⟩
  intro y hy
  have hySource : y ∈ e.source := hy.1
  have hgy : g y ∈ Metric.ball (g x) ε := hy.2
  let q : F × T := ((g x).1, (g y).2)
  have hqBall : q ∈ Metric.ball (g x) ε := by
    rw [Metric.mem_ball, Prod.dist_eq]
    change max (dist (g x).1 (g x).1) (dist (g y).2 (g x).2) < ε
    rw [dist_self, max_eq_right dist_nonneg]
    rw [Metric.mem_ball, Prod.dist_eq] at hgy
    exact (le_max_right _ _).trans_lt hgy
  let p := e.symm q
  have hp : p ∈ f ⁻¹' {f x} := congrArg Prod.fst (e.right_inv (hBall hqBall).2)
  have hyInv : e.symm (g y) = y := e.left_inv hySource
  have hDist : dist (g y) q = ‖f y - f x‖ := by
    rw [Prod.dist_eq]
    change max (dist (f y) (f x)) (dist (Tcoord y) (Tcoord y)) = _
    rw [dist_self, max_eq_left dist_nonneg, dist_eq_norm]
  have hLipDist := hLip'.dist_le_mul (g y) (hBall hgy).1 q (hBall hqBall).1
  rw [hyInv, hDist] at hLipDist
  calc
    Metric.infDist y (f ⁻¹' {f x}) ≤ dist y p := Metric.infDist_le_dist_of_mem hp
    _ ≤ (K : ℝ) * ‖f y - f x‖ := hLipDist
    _ ≤ ((K : ℝ) + 1) * ‖f y - f x‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

private theorem exists_vacuumInvariantErrorBound_at {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) :
    ∃ (K : ℝ) (U : Set S0), 0 < K ∧ IsOpen U ∧ A ∈ U ∧
      ∀ B ∈ U, Metric.infDist B (vacuum a) ≤ K * vacuumInvariantError a B := by
  letI : FiniteDimensional ℝ S0 := Module.Finite.of_basis frobeniusBasis
  let E := EuclideanSpace ℝ (Fin 5)
  let T := EuclideanSpace ℝ (Fin 3)
  let e := frobeniusCoordinateEquiv
  let eInv : E →L[ℝ] S0 := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let t : ↥(vacuumInvariantDerivative A).ker ≃L[ℝ] T :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := ↥(vacuumInvariantDerivative A).ker) (F := T)
      ((vacuumInvariantKernel_finrank hA).trans finrank_euclideanSpace_fin.symm)
  let L : E ≃L[ℝ] (ℝ × ℝ) × T :=
    e.symm.toContinuousLinearEquiv.trans ((vacuumInvariantSplit hA).trans
      ((ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)).prodCongr t))
  let f : E → ℝ × ℝ := vacuumInvariants ∘ eInv
  have hDeriv : HasStrictFDerivAt f
      ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) T).comp L.toContinuousLinearMap) (e A) := by
    have hCenter : eInv (e A) = A := e.symm_apply_apply A
    have hI : HasStrictFDerivAt vacuumInvariants (vacuumInvariantDerivative A) (eInv (e A)) :=
      hCenter.symm ▸ hasStrictFDerivAt_vacuumInvariants A
    refine (hI.comp (e A) (eInv.hasStrictFDerivAt (x := e A))).congr_fderiv ?_
    ext w <;> rfl
  have hCont : Continuous f := contDiff_vacuumInvariants.continuous.comp eInv.continuous
  obtain ⟨K, W, hK, hW, hAW, hEst⟩ := exists_local_levelSet_error_bound L hCont hDeriv
  have hLevel : vacuumInvariants A = (2 * vacuumRadius a ^ 2, 0) := by
    simpa only [vacuum_eq_invariant_level, mem_preimage, mem_singleton_iff] using hA
  have hCarrier : f ⁻¹' {f (e A)} = (vacuumCompactSmoothEmbeddedTarget a).carrierSet := by
    ext w
    rw [mem_vacuumCompactSmoothEmbeddedTarget_iff, vacuum_eq_invariant_level]
    change (vacuumInvariants (e.symm w) = vacuumInvariants (e.symm (e A))) ↔
      vacuumInvariants (e.symm w) = (2 * vacuumRadius a ^ 2, 0)
    rw [e.symm_apply_apply, hLevel]
  refine ⟨K, e ⁻¹' W, hK, hW.preimage e.continuous, hAW, ?_⟩
  intro B hB
  have h := hEst (e B) hB
  rw [hCarrier, infDist_frobeniusCoordinateEquiv_vacuum] at h
  change _ ≤ K * ‖vacuumInvariants (e.symm (e B)) - vacuumInvariants (e.symm (e A))‖ at h
  rw [e.symm_apply_apply, e.symm_apply_apply, hLevel] at h
  exact h

/-- A uniform local error bound for the two trace invariants. -/
theorem exists_vacuumInvariantErrorBound (a : BulkCoefficients) :
    ∃ (K δ : ℝ), 0 < K ∧ 0 < δ ∧ ∀ B ∈ vacuumTube a δ,
      Metric.infDist B (vacuum a) ≤ K * vacuumInvariantError a B := by
  classical
  have hLocal (A : vacuum a) := exists_vacuumInvariantErrorBound_at A.property
  choose K U hK hU hMem hEst using hLocal
  have hCover : vacuum a ⊆ ⋃ A : vacuum a, U A := fun A hA => mem_iUnion.2 ⟨⟨A, hA⟩, hMem _⟩
  obtain ⟨S, hS⟩ := (isCompact_vacuum a).elim_finite_subcover U hU hCover
  let V := ⋃ A ∈ S, U A
  have hV : IsOpen V := isOpen_iUnion fun A => isOpen_iUnion fun _ => hU A
  obtain ⟨δ, hδ, hδV⟩ := (isCompact_vacuum a).exists_thickening_subset_open hV hS
  let K₀ := 1 + ∑ i ∈ S, K i
  have hK₀ : 0 < K₀ := by
    have hsum : 0 ≤ ∑ i ∈ S, K i := Finset.sum_nonneg fun i _ => (hK i).le
    dsimp only [K₀]
    linarith
  refine ⟨K₀, δ, hK₀, hδ, ?_⟩
  intro B hB
  have hBV : B ∈ V := hδV ((Metric.mem_thickening_iff_infDist_lt (vacuum_nonempty a)).2 hB)
  obtain ⟨i, hi⟩ := mem_iUnion.1 hBV
  obtain ⟨hiS, hi⟩ := mem_iUnion.1 hi
  have hle : K i ≤ K₀ := by
    have hsum : K i ≤ ∑ j ∈ S, K j := Finset.single_le_sum (fun j _ => (hK j).le) hiS
    dsimp only [K₀]
    linarith
  exact (hEst i B hi).trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))

private theorem vacuumInvariantError_eq (a : BulkCoefficients) (A : S0) :
    vacuumInvariantError a A =
      max |((A : Tensor) ^ 2).trace - preferredTraceSq a| |((A : Tensor) ^ 3).trace| := by
  simp [vacuumInvariantError, vacuumInvariants, Prod.norm_def, Real.norm_eq_abs,
    two_mul_vacuumRadius_sq]

theorem bulkPotential_ge_invariantError_sq (a : BulkCoefficients) (A : S0) :
    min (a.a4 / 4) (a.a6' / 6) * vacuumInvariantError a A ^ 2 ≤ bulkPotential a A := by
  let x := ((A : Tensor) ^ 2).trace - preferredTraceSq a
  let y := ((A : Tensor) ^ 3).trace
  let c := min (a.a4 / 4) (a.a6' / 6)
  let w := a.a4 / 4 + a.a6 / 6 * (((A : Tensor) ^ 2).trace + 2 * preferredTraceSq a)
  have hw : a.a4 / 4 ≤ w := by
    have := A.trace_sq_nonneg
    have := preferredTraceSq_pos a
    have := a.a6_pos
    dsimp only [w]
    exact le_add_of_nonneg_right (by positivity)
  have hcx : c * x ^ 2 ≤ x ^ 2 * w := by
    rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hw) (sq_nonneg _)
  have hcy : c * y ^ 2 ≤ (a.a6' / 6) * y ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
  have ha4 := a.a4_pos
  have ha6' := a.a6'_pos
  have hLeft : 0 ≤ x ^ 2 * w := mul_nonneg (sq_nonneg _) ((by positivity : 0 ≤ a.a4 / 4).trans hw)
  have hRight : 0 ≤ (a.a6' / 6) * y ^ 2 := by positivity
  rw [vacuumInvariantError_eq, bulkPotential_factorization]
  change c * max |x| |y| ^ 2 ≤ x ^ 2 * w + (a.a6' / 6) * y ^ 2
  rcases le_total |x| |y| with h | h
  · rw [max_eq_right h, sq_abs]
    linarith only [hcy, hLeft]
  · rw [max_eq_left h, sq_abs]
    linarith only [hcx, hRight]

private theorem bulkPotential_le_invariantError_sq_of_norm_le (a : BulkCoefficients) (A : S0)
    {R : ℝ} (hA : ‖A‖ ≤ R) :
    bulkPotential a A ≤
      (a.a4 / 4 + a.a6 / 6 * (R ^ 2 + 2 * preferredTraceSq a) + a.a6' / 6) *
        vacuumInvariantError a A ^ 2 := by
  let x := ((A : Tensor) ^ 2).trace - preferredTraceSq a
  let y := ((A : Tensor) ^ 3).trace
  let w := a.a4 / 4 + a.a6 / 6 * (((A : Tensor) ^ 2).trace + 2 * preferredTraceSq a)
  let W := a.a4 / 4 + a.a6 / 6 * (R ^ 2 + 2 * preferredTraceSq a)
  let D := vacuumInvariantError a A
  have hD : D = max |x| |y| := vacuumInvariantError_eq a A
  have hx : x ^ 2 ≤ D ^ 2 := by
    rw [hD, ← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) 2
  have hy : y ^ 2 ≤ D ^ 2 := by
    rw [hD, ← sq_abs y]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) 2
  have ha4 := a.a4_pos
  have ha6 := a.a6_pos
  have ha6' := a.a6'_pos
  have hμ := preferredTraceSq_pos a
  have htr := A.trace_sq_nonneg
  have htrR : ((A : Tensor) ^ 2).trace ≤ R ^ 2 := by
    rw [← norm_sq_eq_trace_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hw : w ≤ W := by
    dsimp only [w, W]
    gcongr
  have hw₀ : 0 ≤ w := by
    dsimp only [w]
    positivity
  rw [bulkPotential_factorization]
  change x ^ 2 * w + (a.a6' / 6) * y ^ 2 ≤ (W + a.a6' / 6) * D ^ 2
  calc
    _ ≤ D ^ 2 * W + (a.a6' / 6) * D ^ 2 :=
      add_le_add (mul_le_mul hx hw hw₀ (sq_nonneg _)) (mul_le_mul_of_nonneg_left hy (by positivity))
    _ = _ := by ring

theorem exists_bulkPotential_local_upper (a : BulkCoefficients) :
    ∃ C : ℝ, 0 < C ∧ ∀ P ∈ vacuum a, ∀ B : S0,
      ‖B - P‖ ≤ 1 → bulkPotential a B ≤ C * ‖B - P‖ ^ 2 := by
  let E := EuclideanSpace ℝ (Fin 5)
  let e := frobeniusCoordinateEquiv
  let f : E → ℝ × ℝ := vacuumInvariants ∘ e.symm
  have hf : ContDiff ℝ ∞ f :=
    contDiff_vacuumInvariants.comp e.symm.toContinuousLinearEquiv.contDiff
  let R := Real.sqrt 2 * vacuumRadius a + 1
  have hR : 0 < R := by
    have := vacuumRadius_pos a
    dsimp only [R]
    positivity
  let ball := Metric.closedBall (0 : E) R
  have hDerivCont : Continuous (fun z : E => ‖fderiv ℝ f z‖) :=
    ((hf.fderiv_right (m := 0) (by simp)).continuous).norm
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : E) R).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self hR.le⟩ hDerivCont.continuousOn
  let L := ‖fderiv ℝ f z‖ + 1
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  have hLBound (w : E) (hw : w ∈ ball) : ‖fderiv ℝ f w‖ ≤ L :=
    (hz hw).trans (by dsimp only [L]; linarith)
  let W := a.a4 / 4 + a.a6 / 6 * (R ^ 2 + 2 * preferredTraceSq a) + a.a6' / 6
  have hW : 0 < W := by
    have := a.a4_pos
    have := a.a6_pos
    have := a.a6'_pos
    have := preferredTraceSq_pos a
    dsimp only [W]
    positivity
  refine ⟨W * L ^ 2, by positivity, ?_⟩
  intro P hP B hBP
  have hPnorm := vacuum_norm hP
  have hPR : e P ∈ ball := by
    change dist (e P) 0 ≤ R
    rw [dist_zero_right, e.norm_map, hPnorm]
    dsimp only [R]
    linarith
  have hBNorm : ‖B‖ ≤ R := calc
    ‖B‖ = ‖(B - P) + P‖ := by rw [sub_add_cancel]
    _ ≤ ‖B - P‖ + ‖P‖ := norm_add_le _ _
    _ ≤ R := by rw [hPnorm]; dsimp only [R]; linarith
  have hBR : e B ∈ ball := by
    simpa only [ball, Metric.mem_closedBall, dist_zero_right, e.norm_map] using hBNorm
  have hLip := (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
    (fun Q _ => hf.differentiable (by simp) Q)
    hLBound hPR hBR
  have hLevel : vacuumInvariants P = (2 * vacuumRadius a ^ 2, 0) := by
    simpa only [vacuum_eq_invariant_level, mem_preimage, mem_singleton_iff] using hP
  change ‖vacuumInvariants (e.symm (e B)) - vacuumInvariants (e.symm (e P))‖ ≤
    L * ‖e B - e P‖ at hLip
  rw [e.symm_apply_apply, e.symm_apply_apply, ← map_sub, e.norm_map, hLevel] at hLip
  calc
    bulkPotential a B ≤ W * vacuumInvariantError a B ^ 2 :=
      bulkPotential_le_invariantError_sq_of_norm_le a B hBNorm
    _ ≤ W * (L * ‖B - P‖) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hLip 2) hW.le
    _ = W * L ^ 2 * ‖B - P‖ ^ 2 := by ring

/-- The bulk potential controls squared distance on a uniform open vacuum tube. -/
theorem exists_bulkPotential_quadratic_lower (a : BulkCoefficients) :
    ∃ (c δ : ℝ), 0 < c ∧ 0 < δ ∧ ∀ A ∈ vacuumTube a δ,
      c * Metric.infDist A (vacuum a) ^ 2 ≤ bulkPotential a A := by
  obtain ⟨K, δ, hK, hδ, hError⟩ := exists_vacuumInvariantErrorBound a
  let m := min (a.a4 / 4) (a.a6' / 6)
  have hm : 0 < m := lt_min (div_pos a.a4_pos (by norm_num)) (div_pos a.a6'_pos (by norm_num))
  refine ⟨m / K ^ 2, δ, by positivity, hδ, ?_⟩
  intro A hA
  have hSq := pow_le_pow_left₀ Metric.infDist_nonneg (hError A hA) 2
  calc
    (m / K ^ 2) * Metric.infDist A (vacuum a) ^ 2 ≤
        (m / K ^ 2) * (K * vacuumInvariantError a A) ^ 2 :=
      mul_le_mul_of_nonneg_left hSq (by positivity)
    _ = m * vacuumInvariantError a A ^ 2 := by field_simp [hK.ne']
    _ ≤ bulkPotential a A := bulkPotential_ge_invariantError_sq a A

/-- The bulk potential grows quadratically from the vacuum and decays quadratically along a nearest-point segment. -/
theorem bulkPotential_tubular_estimates (a : BulkCoefficients) :
    let p := vacuumTubularProjection a
    ∃ (c C δ : ℝ), 0 < c ∧ 0 < C ∧ 0 < δ ∧ δ ≤ p.radius ∧
      ∀ A : vacuumTube a p.radius, A.val ∈ vacuumTube a δ →
        c * Metric.infDist A.val (vacuum a) ^ 2 ≤ bulkPotential a A.val ∧
        ∀ t ∈ Icc (0 : ℝ) 1, bulkPotential a
          (t • A.val + (1 - t) • (p.project A).val) ≤ C * t ^ 2 * bulkPotential a A.val := by
  let p := vacuumTubularProjection a
  obtain ⟨c, d, hc, hd, hLower⟩ := exists_bulkPotential_quadratic_lower a
  obtain ⟨C, hC, hUpper⟩ := exists_bulkPotential_local_upper a
  let δ := min d p.radius
  refine ⟨c, C / c, δ, hc, div_pos hC hc, lt_min hd p.radius_pos, min_le_right _ _, ?_⟩
  intro A hA
  have hAd : A.val ∈ vacuumTube a d := by
    change Metric.infDist A.val (vacuum a) < δ at hA
    exact hA.trans_le (min_le_left _ _)
  have hl := hLower A.val hAd
  refine ⟨hl, ?_⟩
  intro t ht
  let P := (p.project A).val
  let B := t • A.val + (1 - t) • P
  have hAP : ‖A.val - P‖ = Metric.infDist A.val (vacuum a) := by
    rw [← dist_eq_norm]
    exact p.dist_eq_infDist A
  have hAPle : ‖A.val - P‖ ≤ 1 := by
    rw [hAP]
    exact (A.property.trans p.radius_lt_one).le
  have hSub : B - P = t • (A.val - P) := by
    apply Subtype.ext
    ext i j
    change t * (A.val : Tensor) i j + (1 - t) * (P : Tensor) i j - (P : Tensor) i j =
      t * ((A.val : Tensor) i j - (P : Tensor) i j)
    ring
  have hBP : ‖B - P‖ = t * ‖A.val - P‖ := by
    rw [hSub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hBPle : ‖B - P‖ ≤ 1 := by
    rw [hBP]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hAPle
  calc
    bulkPotential a B ≤ C * ‖B - P‖ ^ 2 := hUpper P (p.project A).property B hBPle
    _ = (C / c) * t ^ 2 * (c * Metric.infDist A.val (vacuum a) ^ 2) := by
      rw [hBP, hAP]
      field_simp [hc.ne']
    _ ≤ (C / c) * t ^ 2 * bulkPotential a A.val := mul_le_mul_of_nonneg_left hl (by positivity)

end Thesis

end

end
