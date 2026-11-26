module

public import Thesis.MeasureGeometry.JunctionParity
public import Thesis.MeasureGeometry.StereographicJunctionMeridians

/-! The light-weight parity of the actual finite segment network. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

/-- Stereographic meridians on the actual junction sphere give even parity
of its light incident weights under the original disk comparison. -/
theorem even_incident_light_weights_of_meridian_cost_stereographic
    (a : BulkCoefficients)
    {Ω U K S Spt : Set Point} (hΩ : IsOpen Ω) (hS : IsClosed S)
    (hK : IsOpen K) (hKU : K ⊆ U) (hKΩ : K ⊆ Ω)
    (hSpt : Spt ⊆ Ω \ S) (hLoc : LocallyFiniteIn (Ω \ S) Spt)
    (hRopen : IsOpen ((Ω \ S) \ Spt))
    {Q₀ : Point → S0} (hQ : ContinuousOn Q₀ ((Ω \ S) \ Spt))
    (hVac : TakesVacuumValues a (Ω \ S) Q₀)
    {m : ℕ} (p q : Fin m → Point) (θ : Fin m → ℝ) (hn : ∀ i, p i ≠ q i) (_hθ : ∀ i, 0 < θ i)
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
  let z (i : Fin n) : sphere x r := ⟨x + r • v i, by
    rw [mem_sphere,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hr.1.le,hv,mul_one]⟩
  have hz : Function.Injective z := by
    intro i j h
    have hEq : x + r • v i = x + r • v j := congrArg Subtype.val h
    exact hInj (smul_right_injective Point hr.1.ne' (add_left_cancel hEq))
  have hPoints : range (fun i => (z i).val) = S ∩ sphere x r := by
    rw [hLine]
    ext y
    constructor
    · rintro ⟨i,he⟩
      exact ⟨order i,he⟩
    · rintro ⟨i,he⟩
      refine ⟨order.symm i,?_⟩
      change x + r • outwardDirection p q x (order (order.symm i)) = y
      rwa [order.apply_symm_apply]
  let F := sphere x r \ range (fun i => (z i).val)
  have hFR (y : F) : y.val ∈ (Ω \ S) \ Spt := by
    refine ⟨⟨hKΩ (hSphere y.property.1),fun h => y.property.2 ?_⟩,
      fun h => (disjoint_left.mp hSptSphere) y.property.1 h⟩
    rw [hPoints]
    exact ⟨h,y.property.1⟩
  have hVacPoint : MapsTo Q₀ ((Ω \ S) \ Spt) (vacuum a) :=
    mapsTo_vacuum_of_continuousOn_of_takesVacuumValues a hRopen hQ
      (ae_restrict_of_ae_restrict_of_subset sdiff_subset hVac)
  let Q : C(F,vacuum a) :=
    ⟨fun y => ⟨Q₀ y.val,hVacPoint (hFR y)⟩,
      (hQ.comp_continuous continuous_subtype_val hFR).subtype_mk _⟩
  let v₀ : Sphere3 := ⟨EuclideanSpace.single (0 : Fin 4) 1,by simp [Sphere3]⟩
  obtain ⟨d,b,hd,hb,hSum⟩ := exists_spherical_meridians_lightParity_zero a v₀ hr.1 hn₀ z hz Q
  have hCost (i : Fin n) : θ (order i).val = nativeVacuumCircleCost a (b i) := by
    obtain ⟨hEmb,hDSp,hCenter,hIntersection,hTrans⟩ := hd i
    have hDK : d i '' Disk ⊆ K := image_subset_iff.mpr (hDSp.mono_right hSphere)
    have hBSp : d i '' sphere (0 : Plane) 1 ⊆ sphere x r := by
      rintro _ ⟨y,hy,rfl⟩
      exact hDSp (sphere_subset_closedBall hy)
    have hDisj : Disjoint (d i '' sphere (0 : Plane) 1) Spt :=
      hSptSphere.mono_left hBSp
    have hOne : d i '' Disk ∩ S = {d i 0} := by
      rw [hPoints] at hIntersection
      rw [← hIntersection,← inter_assoc,(inter_comm (d i '' Disk) S),inter_assoc,
        inter_eq_left.mpr (image_subset_iff.mpr hDSp),inter_comm]
    have hCenter' : d i 0 = x + r • v i := hCenter
    have hOpen : d i 0 ∈ openSegment ℝ (p (order i)) (q (order i)) := by
      rw [hCenter']
      exact openSegment_of_outward_step hn (order i) hr.1 (hShort (order i))
    have hDirection : v i ∉ LinearMap.range (fderiv ℝ (d i) 0).toLinearMap := by
      intro h
      apply hTrans
      rw [hCenter',add_sub_cancel_left]
      exact Submodule.smul_mem _ r h
    refine hWeight (order i) (d i) hEmb hDK 0 (mem_ball_self zero_lt_one) hOne hOpen
      (segment_direction_not_in_range_of_outward (order i) _ hDirection) hDisj (b i) ?_
    intro w
    obtain ⟨h,he⟩ := hb i w
    exact congrArg Subtype.val he
  have hSum' : (∑ i : Fin n, if θ (order i).val = kappaStar a then (1 : ZMod 2) else 0) = 0 := by
    simpa only [hCost] using hSum
  have hSum'' : (∑ i : ↥I, if θ i.val = kappaStar a then (1 : ZMod 2) else 0) = 0 :=
    (Equiv.sum_comp order
      (fun i : ↥I => if θ i.val = kappaStar a then (1 : ZMod 2) else 0)).symm.trans hSum'
  have hCard : (((Finset.univ.filter fun i : ↥I => θ i.val = kappaStar a).card : ℕ) : ZMod 2) = 0 := by
    rwa [← Finset.sum_filter,Finset.sum_const,nsmul_one] at hSum''
  exact ZMod.natCast_eq_zero_iff_even.mp hCard

end Thesis.MeasureGeometry
