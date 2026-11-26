module

public import Thesis.Variational.SmoothDomainEpigraphBoxes
import HarmonicMaps.Analysis.AffineBallMeasure
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.MeasureTheory.Constructions.Pi

/-! Unit-ball coordinates and reflected volume control near a smooth wall. -/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal

namespace Thesis

/-- Reflection in the horizontal two-dimensional coordinate plane. -/
@[expose] def normalReflection : Point ≃ₗᵢ[ℝ] Point where
  toFun x := WithLp.toLp 2 ![x 0, x 1, -(x 2)]
  invFun x := WithLp.toLp 2 ![x 0, x 1, -(x 2)]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' t x := by ext i; fin_cases i <;> simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
      Fin.sum_univ_three]
    simp

private def normalFold (x : Point) : Point := WithLp.toLp 2 ![x 0, x 1, |x 2|]

private theorem normalFold_eq_self (x : Point) (hx : 0 ≤ x 2) : normalFold x = x := by
  ext i
  fin_cases i <;> simp [normalFold, abs_of_nonneg hx]

private theorem normalFold_eq_reflection (x : Point) (hx : x 2 ≤ 0) : normalFold x = normalReflection x := by
  ext i
  fin_cases i <;> simp [normalFold, normalReflection, abs_of_nonpos hx]

private theorem normalFold_norm (x : Point) : ‖normalFold x‖ = ‖x‖ := by
  by_cases hx : 0 ≤ x 2
  · rw [normalFold_eq_self x hx]
  · rw [normalFold_eq_reflection x (le_of_not_ge hx), LinearIsometryEquiv.norm_map]

private theorem normalFold_lipschitz : LipschitzWith 1 normalFold := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    Fin.sum_univ_three]
  have h := pow_le_pow_left₀ (abs_nonneg (|x 2| - |y 2|))
    (abs_abs_sub_abs_le_abs_sub (x 2) (y 2)) 2
  rw [sq_abs, sq_abs] at h
  simpa [normalFold] using
    add_le_add_left h (((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2))

theorem normal_plane_volume_zero : (volume : Measure Point) {x | x 2 = 0} = 0 := by
  let L : Point →L[ℝ] ℝ := EuclideanSpace.proj 2
  have hker : L.ker ≠ ⊤ := by
    intro h
    have hx : axis 2 ∈ L.ker := h ▸ mem_univ _
    have he : L (axis 2) = 0 := LinearMap.mem_ker.mp hx
    have hn : L (axis 2) = 1 := by simp [L, axis]
    linarith only [he, hn]
  exact Measure.addHaar_submodule volume L.ker hker

private theorem map_normalFold_ball_le :
    Measure.map normalFold (volume.restrict (ball (0 : Point) 1)) ≤
      (2 : ℝ≥0∞) • volume.restrict (ball (0 : Point) 1 ∩ {x | 0 < x 2}) := by
  apply Measure.le_iff.mpr
  intro S hS
  let P := ball (0 : Point) 1 ∩ {x | 0 < x 2}
  have hP : MeasurableSet P := measurableSet_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 2).continuous).measurableSet
  let T := S ∩ P
  have hT : MeasurableSet T := hS.inter hP
  rw [Measure.map_apply normalFold_lipschitz.continuous.measurable hS,
    Measure.restrict_apply (hS.preimage normalFold_lipschitz.continuous.measurable),
    Measure.smul_apply, Measure.restrict_apply hS]
  have hsub : normalFold ⁻¹' S ∩ ball (0 : Point) 1 ⊆
      (T ∪ normalReflection ⁻¹' T) ∪ {x | x 2 = 0} := by
    rintro x ⟨hxS, hxB⟩
    have hxS' : normalFold x ∈ S := hxS
    rcases lt_trichotomy 0 (x 2) with hpos | hzero | hneg
    · have hself := normalFold_eq_self x hpos.le
      rw [hself] at hxS'
      exact Or.inl (Or.inl ⟨hxS', hxB, hpos⟩)
    · exact Or.inr hzero.symm
    · have hR := normalFold_eq_reflection x hneg.le
      rw [hR] at hxS'
      apply Or.inl
      right
      refine ⟨hxS', ?_, ?_⟩
      · rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
        exact mem_ball_zero_iff.mp hxB
      · change 0 < -(x 2)
        linarith
  calc
    _ ≤ volume ((T ∪ normalReflection ⁻¹' T) ∪ {x | x 2 = 0}) := measure_mono hsub
    _ ≤ volume (T ∪ normalReflection ⁻¹' T) + volume {x : Point | x 2 = 0} := measure_union_le _ _
    _ ≤ (2 : ℝ≥0∞) • volume T := by
      rw [normal_plane_volume_zero, add_zero, two_smul]
      refine (measure_union_le _ _).trans_eq ?_
      rw [normalReflection.measurePreserving.measure_preimage hT.nullMeasurableSet]

private theorem map_restrict_of_homeomorph_le
    {U P : Set Point} (F : Point ≃ₜ Point) (hInt : MapsTo F P U)
    {c : ℝ≥0∞} (hMap : Measure.map F volume = c • volume) :
    Measure.map F (volume.restrict P) ≤ c • volume.restrict U := by
  calc
    _ ≤ Measure.map F (volume.restrict (F ⁻¹' U)) :=
      Measure.map_mono (Measure.restrict_mono_set volume hInt) F.continuous.measurable
    _ = _ := by
      have hM : MeasurableEmbedding (F : Point → Point) := F.isClosedEmbedding.measurableEmbedding
      rw [← hM.restrict_map volume U, hMap, Measure.restrict_smul]

private def pointEpigraphCoordinates : Point ≃L[ℝ] EpigraphCoordinates :=
  (show Point ≃ₗ[ℝ] EpigraphCoordinates from
    { toFun := fun x => ((x 0, x 1), x 2)
      invFun := fun p => WithLp.toLp 2 ![p.1.1, p.1.2, p.2]
      left_inv := fun x => by ext i; fin_cases i <;> rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearEquiv

private theorem pointEpigraphCoordinates_norm (x : Point) : ‖pointEpigraphCoordinates x‖ ≤ ‖x‖ := by
  change ‖((x 0, x 1), x 2)‖ ≤ ‖x‖
  rw [Prod.norm_def, Prod.norm_def, max_le_iff, max_le_iff]
  exact ⟨⟨PiLp.norm_apply_le x 0, PiLp.norm_apply_le x 1⟩, PiLp.norm_apply_le x 2⟩

private theorem pointEpigraphCoordinates_volume :
    MeasurePreserving pointEpigraphCoordinates (volume : Measure Point) volume := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)).comp
    (PiLp.volume_preserving_ofLp (Fin 3))
  have hh := ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_finTwoArrow ℝ)).comp hp
  have ht := Measure.measurePreserving_swap.comp hh
  have hFn : (pointEpigraphCoordinates : Point → EpigraphCoordinates) =
      Prod.swap ∘ Prod.map id MeasurableEquiv.finTwoArrow ∘
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3) ∘ WithLp.ofLp := by
    funext x
    apply Prod.ext
    · apply Prod.ext <;> rfl
    · rfl
  rw [hFn]
  with_unfolding_all exact ht

private theorem scaled_pointEpigraphCoordinates_measure (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ≥0, Measure.map (fun x : Point => r • pointEpigraphCoordinates x) volume =
      (c : ℝ≥0∞) • (volume : Measure EpigraphCoordinates) := by
  let c := Real.toNNReal ((r ^ (3 : ℕ))⁻¹)
  refine ⟨c, ?_⟩
  have hfun : (fun x : Point => r • pointEpigraphCoordinates x) =
      (pointEpigraphCoordinates : Point → EpigraphCoordinates) ∘ (fun x => r • x) := by
    funext x
    exact (pointEpigraphCoordinates.map_smul r x).symm
  have hScale : Measure.map (fun x : Point => r • x) volume = (c : ℝ≥0∞) • volume := by
    simpa only [ENNReal.ofReal, zero_add, sub_zero, c] using
      (HarmonicMaps.affineBall_map_volume (n := 3) 0 0 hr)
  rw [hfun, ← Measure.map_map pointEpigraphCoordinates_volume.measurable
    (by fun_prop : Measurable (fun x : Point => r • x)), hScale, Measure.map_smul,
    pointEpigraphCoordinates_volume.map_eq]

/-- A closed convex core of a unit coordinate ball that maps into the closed
domain. Flattened wall patches use the closed upper half of the ball.
The normal fold controls the whole-ball Lebesgue pullback. -/
structure MorreyDomainChart (U : Set Point) where
  chart : Point ≃ₜ Point
  smooth : ContDiff ℝ ∞ (chart : Point → Point)
  lip : ℝ≥0
  lipschitz : LipschitzOnWith lip chart (closedBall 0 1)
  inverseLip : ℝ≥0
  inverse_lipschitz : LipschitzOnWith inverseLip chart.symm (chart '' closedBall 0 1)
  core : Set Point
  core_compact : IsCompact core
  core_convex : Convex ℝ core
  core_subset : core ⊆ closedBall 0 1
  mapsClosure : MapsTo chart core (closure U)
  capturesClosure : ∀ x ∈ ball (0 : Point) (1 / 2), chart x ∈ closure U → x ∈ core
  fold : Point → Point
  fold_lipschitz : LipschitzWith 1 fold
  fold_maps : MapsTo fold (closedBall 0 1) core
  fold_fixes : EqOn fold id core
  density : ℝ≥0
  map_fold_le : Measure.map (chart ∘ fold) (volume.restrict (ball (0 : Point) 1)) ≤
    (density : ℝ≥0∞) • volume.restrict U

private theorem exists_interior_morreyDomainChart {U : Set Point} (hU : IsOpen U) {a : Point} (ha : a ∈ U) :
    ∃ A : MorreyDomainChart U, A.chart 0 = a := by
  obtain ⟨b, hb, hB⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let r := b / 2
  have hr : 0 < r := half_pos hb
  let F : Point ≃ₜ Point := (Homeomorph.smul (Units.mk0 r hr.ne')).trans (Homeomorph.addLeft a)
  have hF (x : Point) : F x = a + r • x := rfl
  have hInto : MapsTo F (closedBall 0 1) U := fun x hx => hB (by
    apply mem_ball.2
    rw [hF, dist_eq_norm, add_comm a, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg hr.le]
    have h := mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.mp hx)
    exact h.trans_lt (half_lt_self hb))
  have hDist (x y : Point) : dist (F x) (F y) = r * dist x y := by
    rw [hF, hF, dist_add_left, dist_eq_norm, ← smul_sub, norm_smul, ← dist_eq_norm,
      Real.norm_of_nonneg hr.le]
  have hLip : LipschitzWith (Real.toNNReal r) F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hDist, Real.coe_toNNReal r hr.le]
  have hLipInv : LipschitzWith (Real.toNNReal r⁻¹) F.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    obtain ⟨x, rfl⟩ := F.surjective x
    obtain ⟨y, rfl⟩ := F.surjective y
    rw [F.symm_apply_apply, F.symm_apply_apply, hDist, Real.coe_toNNReal _ (inv_nonneg.mpr hr.le),
      ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hV : Measure.map F volume = (Real.toNNReal ((r ^ 3)⁻¹) : ℝ≥0∞) • volume := by
    rw [show (F : Point → Point) = fun x => a + r • (x - (0 : Point)) by funext x; simp [hF],
      HarmonicMaps.affineBall_map_volume a 0 hr, ENNReal.ofReal]
  refine ⟨{ chart := F
            smooth := by rw [show (F : Point → Point) = fun x => a + r • x from funext hF]; fun_prop
            lip := _
            lipschitz := hLip.lipschitzOnWith
            inverseLip := _
            inverse_lipschitz := hLipInv.lipschitzOnWith
            core := closedBall 0 1
            core_compact := isCompact_closedBall _ _
            core_convex := convex_closedBall _ _
            core_subset := subset_rfl
            mapsClosure := fun _ h => subset_closure (hInto h)
            capturesClosure := fun _ h _ => ball_subset_closedBall (ball_subset_ball (by norm_num) h)
            fold := id
            fold_lipschitz := LipschitzWith.id
            fold_maps := mapsTo_id _
            fold_fixes := fun _ _ => rfl
            density := _
            map_fold_le := map_restrict_of_homeomorph_le F
              (hInto.mono_left ball_subset_closedBall) hV }, by simp [hF]⟩

private theorem exists_boundary_morreyDomainChart {U : Set Point} (hU : IsSmoothDomain U)
    {a : Point} (ha : a ∈ frontier U) : ∃ A : MorreyDomainChart U, A.chart 0 = a := by
  obtain ⟨B, hBa⟩ := hU.exists_epigraph_box ha
  let r := B.radius / 2
  have hr : 0 < r := half_pos B.radius_pos
  let L : Point ≃L[ℝ] EpigraphCoordinates :=
    pointEpigraphCoordinates.trans (LinearEquiv.smulOfNeZero ℝ _ r hr.ne').toContinuousLinearEquiv
  let E : Point ≃ₜ EpigraphCoordinates := L.toHomeomorph
  let F : Point ≃ₜ Point := E.trans B.chart
  have hE (x : Point) : E x = r • pointEpigraphCoordinates x := rfl
  have hF (x : Point) : F x = B.chart (E x) := rfl
  have hE_B : MapsTo E (closedBall (0 : Point) 1) (closedBall (0 : EpigraphCoordinates) B.radius) := by
    intro x hx
    rw [mem_closedBall_zero_iff, hE, norm_smul, Real.norm_of_nonneg hr.le]
    have h := (pointEpigraphCoordinates_norm x).trans (mem_closedBall_zero_iff.mp hx)
    exact (mul_le_of_le_one_right hr.le h).trans (half_lt_self B.radius_pos).le
  have hHeight (x : Point) : (E x).2 = r * x 2 := rfl
  have hInt (x : Point) (hx : x ∈ closedBall (0 : Point) 1) :
      F x ∈ U ↔ 0 < x 2 := by
    rw [hF, B.mem_domain _ (hE_B hx), hHeight, mul_pos_iff_of_pos_left hr]
  have hWall (x : Point) (hx : x ∈ closedBall (0 : Point) 1) :
      F x ∈ frontier U ↔ x 2 = 0 := by
    rw [hF, B.frontier_iff _ (hE_B hx), hHeight, mul_eq_zero, or_iff_right hr.ne']
  have hCl (x : Point) (hx : x ∈ closedBall (0 : Point) 1) :
      F x ∈ closure U ↔ 0 ≤ x 2 := by
    rw [closure_eq_self_union_frontier, mem_union, hWall x hx, hInt x hx, le_iff_eq_or_lt, or_comm,
      eq_comm (a := x 2)]
  have hL : LipschitzWith ‖L.toContinuousLinearMap‖₊ E := L.lipschitz
  have hI : LipschitzWith ‖L.symm.toContinuousLinearMap‖₊ E.symm := L.symm.lipschitz
  have hLip : LipschitzOnWith (B.lip * ‖L.toContinuousLinearMap‖₊) F (closedBall 0 1) :=
    B.chart_lipschitz.comp hL.lipschitzOnWith hE_B
  have hLipInv : LipschitzOnWith (‖L.symm.toContinuousLinearMap‖₊ * B.inverseLip) F.symm
      (F '' closedBall 0 1) := by
    apply hI.comp_lipschitzOnWith
    apply B.chart_inverse_lipschitz.mono
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨E p, hE_B hp, rfl⟩
  let P := ball (0 : Point) 1 ∩ {x | 0 < x 2}
  have hP : MapsTo F P U := fun x hx => (hInt x (ball_subset_closedBall hx.1)).2 hx.2
  obtain ⟨c, hc⟩ := scaled_pointEpigraphCoordinates_measure r hr
  have hV : Measure.map F volume = (c : ℝ≥0∞) • volume := by
    change Measure.map ((B.chart : EpigraphCoordinates → Point) ∘ E) volume = _
    rw [← Measure.map_map B.chart.continuous.measurable E.continuous.measurable,
      show Measure.map E volume = _ from hc, Measure.map_smul, B.chart_volume.map_eq]
  have hFoldMeasure : Measure.map ((F : Point → Point) ∘ normalFold)
        (volume.restrict (ball (0 : Point) 1)) ≤
      ((2 * c : ℝ≥0) : ℝ≥0∞) • volume.restrict U := by
    rw [← Measure.map_map F.continuous.measurable normalFold_lipschitz.continuous.measurable]
    refine (Measure.map_mono map_normalFold_ball_le F.continuous.measurable).trans ?_
    rw [Measure.map_smul, ENNReal.coe_mul, ENNReal.coe_ofNat, mul_smul]
    exact smul_le_smul_left _ (map_restrict_of_homeomorph_le F hP hV)
  let K := closedBall (0 : Point) 1 ∩ {x | 0 ≤ x 2}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 2).continuous)
  have hConvK : Convex ℝ K := (convex_closedBall _ _).inter
    (convex_halfSpace_ge (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).toLinearMap.isLinear 0)
  refine ⟨{ chart := F
            smooth := B.chart_smooth.comp L.contDiff
            lip := _
            lipschitz := hLip
            inverseLip := _
            inverse_lipschitz := hLipInv
            core := K
            core_compact := hK
            core_convex := hConvK
            core_subset := inter_subset_left
            mapsClosure := fun x hx => (hCl x hx.1).2 hx.2
            capturesClosure := fun x hx hFx => by
              have hx' : x ∈ closedBall (0 : Point) 1 :=
                ball_subset_closedBall (ball_subset_ball (by norm_num) hx)
              exact ⟨hx', (hCl x hx').1 hFx⟩
            fold := normalFold
            fold_lipschitz := normalFold_lipschitz
            fold_maps := fun x hx => by
              refine ⟨?_, ?_⟩
              · rwa [mem_closedBall_zero_iff, normalFold_norm, ← mem_closedBall_zero_iff]
              · change 0 ≤ normalFold x 2
                simp [normalFold]
            fold_fixes := fun x hx => normalFold_eq_self x hx.2
            density := _
            map_fold_le := hFoldMeasure }, ?_⟩
  change B.chart (L 0) = a
  rw [map_zero, hBa]

theorem IsSmoothDomain.exists_morreyDomainChart {U : Set Point} (hU : IsSmoothDomain U)
    {a : Point} (ha : a ∈ closure U) : ∃ A : MorreyDomainChart U, A.chart 0 = a := by
  by_cases h : a ∈ U
  · exact exists_interior_morreyDomainChart hU.1.1 h
  · apply exists_boundary_morreyDomainChart hU
    rw [frontier, hU.1.1.interior_eq]
    exact ⟨ha, h⟩

end Thesis
