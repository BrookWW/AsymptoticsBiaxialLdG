module

public import Thesis.MeasureGeometry.JunctionCaps
public import Thesis.MeasureGeometry.JunctionSphereSelection

/-! Parity for the actual finite segment network and its regular meridians. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

theorem segment_direction_not_in_range_of_outward
    {m : ℕ} {p q : Fin m → Point} {x : Point} (i : ↥(incidentSegments p q x))
    (D : Plane →L[ℝ] Point) (h : outwardDirection p q x i ∉ LinearMap.range D.toLinearMap) :
    q i - p i ∉ LinearMap.range D.toLinearMap := by
  intro hIn
  apply h
  let N := LinearMap.range D.toLinearMap
  let y := if x = p i then q i else p i
  change ‖y - x‖⁻¹ • (y - x) ∈ N
  apply N.smul_mem
  by_cases hx : x = p i
  · have hy : y = q i := if_pos hx
    have hDiff : y - x = q i - p i := congrArg₂ (· - ·) hy hx
    exact hDiff.symm ▸ hIn
  · have hq := ((Finset.mem_filter.mp i.property).2 : x = p i ∨ x = q i).resolve_left hx
    have hy : y = p i := if_neg hx
    have hDiff : y - x = -(q i - p i) :=
      (congrArg₂ (· - ·) hy hq).trans (neg_sub _ _).symm
    exact hDiff.symm ▸ N.neg_mem hIn

/-- The actual junction has an even number of light incident weights,
once the meridian comparison with each incident segment is available. -/
theorem even_incident_light_weights_of_meridian_cost
    (hCut : External.PuncturedSphereWord) (a : BulkCoefficients)
    {Ω U K S Spt : Set Point} (hΩ : IsOpen Ω) (hS : IsClosed S)
    (hK : IsOpen K) (hKU : K ⊆ U) (hKΩ : K ⊆ Ω)
    (hSpt : Spt ⊆ Ω \ S) (hLoc : LocallyFiniteIn (Ω \ S) Spt)
    (hRopen : IsOpen ((Ω \ S) \ Spt))
    {Q₀ : Point → S0} (hQ : ContinuousOn Q₀ ((Ω \ S) \ Spt))
    (hVac : TakesVacuumValues a (Ω \ S) Q₀)
    {m : ℕ} (p q : Fin m → Point) (θ : Fin m → ℝ) (hn : ∀ i, p i ≠ q i) (hθ : ∀ i, 0 < θ i)
    (hRep : S ∩ closure U = ⋃ i : Fin m, segment ℝ (p i) (q i))
    (hMeet : ∀ i j : Fin m, i ≠ j → ∀ z ∈ segment ℝ (p i) (q i) ∩ segment ℝ (p j) (q j),
      (z = p i ∨ z = q i) ∧ (z = p j ∨ z = q j))
    (hWeight : ∀ (i : Fin m) (d : Plane → Point), IsSmoothDiskEmbedding d → d '' Disk ⊆ K →
      ∀ y ∈ ball (0 : Plane) 1, d '' Disk ∩ S = {d y} →
        d y ∈ openSegment ℝ (p i) (q i) →
        q i - p i ∉ LinearMap.range (fderiv ℝ d y).toLinearMap →
        Disjoint (d '' sphere (0 : Plane) 1) Spt →
        ∀ b : C(NativeCircle, vacuum a), (∀ z, (b z).val = Q₀ (d z.val)) →
          θ i = nativeVacuumCircleCost a b)
    {x : Point} (hx : x ∈ K) (hI : (incidentSegments p q x).Nonempty) :
    Even ((Finset.univ.filter fun i : ↥(incidentSegments p q x) => θ i = kappaStar a).card) := by
  classical
  obtain ⟨R, hR, hSections⟩ := exists_small_junction_sphere_sections hK hKU p q hn hRep hMeet hx hI
  have hSptCount := locallyFiniteIn_countable (hΩ.sdiff hS) hSpt hLoc
  obtain ⟨r, hr, hSptSphere⟩ := exists_sphere_disjoint_countable hSptCount x hR
  obtain ⟨hSphere, hLine, hShort⟩ := hSections hr
  let I := incidentSegments p q x
  let n := Fintype.card (↥I)
  let order : Fin n ≃ ↥I := (Fintype.equivFin (↥I)).symm
  have hn₀ : 0 < n := by
    obtain ⟨i, hi⟩ := hI
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  let v (i : Fin n) := outwardDirection p q x (order i)
  have hv (i : Fin n) : ‖v i‖ = 1 := norm_outwardDirection hn (order i)
  have hInj : Function.Injective v := (outwardDirection_injective_of_endpoint_intersections hn hMeet).comp order.injective
  obtain ⟨d, hd, hDisj⟩ := exists_disjoint_transverse_junction_caps x hr.1 v hv hInj
  let F := puncturedCapSphere x r d
  have hFS (u : F) : u.val ∈ sphere x r := u.property.1
  have hFR (u : F) : u.val ∈ (Ω \ S) \ Spt := by
    refine ⟨⟨hKΩ (hSphere (hFS u)), ?_⟩, fun hp => (disjoint_left.mp hSptSphere) (hFS u) hp⟩
    intro h
    have hmem : u.val ∈ S ∩ sphere x r := ⟨h, hFS u⟩
    rw [hLine] at hmem
    obtain ⟨i, hi⟩ := hmem
    have hD : d (order.symm i) 0 = u.val := by
      rw [(hd (order.symm i)).2.2.1]
      simpa only [v, order.apply_symm_apply] using hi
    exact u.property.2 (mem_iUnion.mpr ⟨order.symm i, 0, mem_ball_self zero_lt_one, hD⟩)
  have hVacPoint : MapsTo Q₀ ((Ω \ S) \ Spt) (vacuum a) :=
    mapsTo_vacuum_of_continuousOn_of_takesVacuumValues a hRopen hQ
      (ae_restrict_of_ae_restrict_of_subset sdiff_subset hVac)
  let Q : C(F, vacuum a) :=
    ⟨fun y => ⟨Q₀ y.val, hVacPoint (hFR y)⟩,
      (hQ.comp_continuous continuous_subtype_val hFR).subtype_mk _⟩
  have hQVal (u : F) : (Q u).val = Q₀ u.val := rfl
  have hEach (j : Fin n) (b : C(NativeCircle, vacuum a))
      (hb : ∀ z, (b z).val = Q₀ (d j z.val)) :
      θ (order j).val = nativeVacuumCircleCost a b := by
    have hDΩ : d j '' Disk ⊆ K := image_subset_iff.mpr ((hd j).2.1.mono_right hSphere)
    have hDSp : d j '' sphere (0 : Plane) 1 ⊆ sphere x r := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hd j).2.1 (sphere_subset_closedBall hz)
    have hDSpt : Disjoint (d j '' sphere (0 : Plane) 1) Spt := hSptSphere.mono_left hDSp
    have hOne : d j '' Disk ∩ S = {d j 0} := by
      ext y
      constructor
      · rintro ⟨hDy, hy⟩
        have hySphere : y ∈ sphere x r := (image_subset_iff.mpr (hd j).2.1) hDy
        have hmem : y ∈ S ∩ sphere x r := ⟨hy, hySphere⟩
        rw [hLine] at hmem
        obtain ⟨i, hi⟩ := hmem
        let k := order.symm i
        have hEq : d k 0 = y := by
          rw [(hd k).2.2.1]
          simpa only [v, k, order.apply_symm_apply] using hi
        have hk : k = j := by
          by_contra hkj
          exact (disjoint_left.mp (hDisj hkj)) ⟨0, mem_closedBall_self zero_le_one, hEq⟩ hDy
        exact mem_singleton_iff.mpr ((congrArg (fun j => d j 0) hk.symm).trans hEq).symm
      · intro hy
        have hE : y = d j 0 := mem_singleton_iff.mp hy
        subst y
        have hMem : d j 0 ∈ S ∩ sphere x r := by
          rw [hLine, (hd j).2.2.1]
          exact ⟨order j, rfl⟩
        exact ⟨⟨0, mem_closedBall_self zero_le_one, rfl⟩, hMem.1⟩
    have hOpen : d j 0 ∈ openSegment ℝ (p (order j)) (q (order j)) := by
      rw [(hd j).2.2.1]
      exact openSegment_of_outward_step hn (order j) hr.1 (hShort (order j))
    exact hWeight (order j) (d j) (hd j).1 hDΩ 0 (mem_ball_self zero_lt_one) hOne hOpen
      (segment_direction_not_in_range_of_outward (order j) _ (hd j).2.2.2) hDSpt b hb
  have hEven := even_light_weights_of_actual_junction_caps hCut a x hr.1 hn₀ d
    (fun j => (hd j).1) (fun j => (hd j).2.1) hDisj Q₀ Q hQVal
    (fun j => θ (order j).val) (fun j => hθ _) hEach
  have hCount :
      (Finset.univ.filter fun j : Fin n => θ (order j).val = kappaStar a).card =
      (Finset.univ.filter fun j : ↥I => θ j.val = kappaStar a).card := by
    apply Finset.card_bij (fun i _ => order i)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · intro i hi j hj h
      exact order.injective h
    · intro i hi
      refine ⟨order.symm i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, order.apply_symm_apply i⟩
      rw [order.apply_symm_apply]
      exact (Finset.mem_filter.mp hi).2
  rwa [hCount] at hEven

end Thesis.MeasureGeometry
