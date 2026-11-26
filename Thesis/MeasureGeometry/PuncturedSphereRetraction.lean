module

public import Thesis.MeasureGeometry.SphericalDiskInterior
public import Thesis.MeasureGeometry.JunctionWord

/-! Radial deformation from point punctures to the actual embedded caps. -/

@[expose] public section

noncomputable section

open Filter Metric Set
open scoped Topology

namespace Thesis.MeasureGeometry

/-- The metric sphere punctured at the center of every given disk. -/
def puncturedCenterSphere (c : Point) (R : ℝ) {q : ℕ} (d : Fin q → Plane → Point) : Set Point :=
  sphere c R \ range (fun i => d i 0)

private def embeddedDiskHomeomorph {d : Plane → Point} (hd : IsSmoothDiskEmbedding d) :
    Disk ≃ₜ (d '' Disk) := by
  letI : CompactSpace Disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let f := Equiv.Set.imageOfInjOn d Disk hd.2.1
  have hf : Continuous f := hd.1.continuousOn.restrict.subtype_mk _
  exact hf.homeoOfEquivCompactToT2

private theorem embeddedDiskHomeomorph_symm_val {d : Plane → Point} (hd : IsSmoothDiskEmbedding d)
    (x : d '' Disk) : d ((embeddedDiskHomeomorph hd).symm x).val = x.val :=
  congrArg Subtype.val ((embeddedDiskHomeomorph hd).apply_symm_apply x)

private def pushDiskRadius (t : unitInterval) (y : Plane) : Plane :=
  (1-t.val + t.val*‖y‖⁻¹) • y

private theorem norm_pushDiskRadius (t : unitInterval) {y : Plane} (hy : y ≠ 0) :
    ‖pushDiskRadius t y‖ = (1-t.val)*‖y‖+t.val := by
  have h₀ : 0 ≤ t.val := t.property.1
  have h₁ : 0 ≤ 1-t.val := sub_nonneg.mpr t.property.2
  have hS := add_nonneg h₁ (mul_nonneg h₀ (inv_nonneg.mpr (norm_nonneg y)))
  rw [pushDiskRadius,norm_smul,Real.norm_of_nonneg hS,add_mul,mul_assoc,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy),mul_one]

private theorem pushDiskRadius_mem_disk (t : unitInterval) {y : Plane} (hy : y ∈ Disk) (h₀ : y ≠ 0) :
    pushDiskRadius t y ∈ Disk := by
  apply mem_closedBall_zero_iff.mpr
  rw [norm_pushDiskRadius t h₀]
  have h := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hy) (sub_nonneg.mpr t.property.2)
  linarith only [h]

private theorem pushDiskRadius_nonzero (t : unitInterval) {y : Plane} (hy : y ≠ 0) :
    pushDiskRadius t y ≠ 0 := by
  have hY := norm_pos_iff.mpr hy
  have hT := t.property
  apply norm_ne_zero_iff.mp
  rw [norm_pushDiskRadius t hy]
  by_cases ht : t.val = 0
  · simp [ht, hY.ne']
  · exact (add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hT.2) hY.le)
      (lt_of_le_of_ne hT.1 (Ne.symm ht))).ne'

private theorem pushDiskRadius_zero (y : Plane) : pushDiskRadius 0 y = y := by
  change (1 - 0 + 0*‖y‖⁻¹) • y = y
  simp

private theorem pushDiskRadius_eq_of_norm_eq_one (t : unitInterval) {y : Plane} (hy : ‖y‖ = 1) :
    pushDiskRadius t y = y := by
  unfold pushDiskRadius
  rw [hy,inv_one,mul_one,sub_add_cancel,one_smul]

theorem puncturedCapSphere_subset_puncturedCenterSphere (c : Point) (R : ℝ)
    {q : ℕ} (d : Fin q → Plane → Point) :
    puncturedCapSphere c R d ⊆ puncturedCenterSphere c R d := by
  intro x hx
  refine ⟨hx.1,?_⟩
  rintro ⟨i,hi⟩
  exact hx.2 (mem_iUnion.mpr ⟨i,0,mem_ball_self zero_lt_one,hi⟩)

/-- Push each punctured closed cap radially onto its own boundary and
fix the exterior throughout. The whole homotopy stays on the same
sphere punctured at the original centers. -/
theorem exists_puncturedSphere_radial_deformation
    {c : Point} {R : ℝ} (hR : 0 < R) {q : ℕ} (d : Fin q → Plane → Point)
    (hd : ∀ i, IsSmoothDiskEmbedding (d i)) (hs : ∀ i, MapsTo (d i) Disk (sphere c R))
    (hDisj : Pairwise (fun i j => Disjoint (d i '' Disk) (d j '' Disk))) :
    ∃ F : C(unitInterval × puncturedCenterSphere c R d, puncturedCenterSphere c R d),
      (∀ x, F (0,x) = x) ∧
      (∀ x, (F (1,x)).val ∈ puncturedCapSphere c R d) ∧
      (∀ t x, x.val ∈ puncturedCapSphere c R d → F (t,x) = x) := by
  classical
  let X := puncturedCenterSphere c R d
  let A := puncturedCapSphere c R d
  let Z := unitInterval × X
  let val (z : Z) : Point := z.2.val
  let on (i : Fin q) := {z : Z | val z ∈ d i '' Disk}
  let out := {z : Z | val z ∈ A}
  let Y (i : Fin q) (z : on i) : Plane :=
    ((embeddedDiskHomeomorph (hd i)).symm ⟨val z.val,z.property⟩).val
  have hYmem (i : Fin q) (z : on i) : Y i z ∈ Disk :=
    ((embeddedDiskHomeomorph (hd i)).symm ⟨val z.val,z.property⟩).property
  have hDecode (i : Fin q) (z : on i) : d i (Y i z) = val z.val :=
    embeddedDiskHomeomorph_symm_val (hd i) ⟨val z.val,z.property⟩
  have hYne (i : Fin q) (z : on i) : Y i z ≠ 0 := by
    intro h
    exact z.val.2.property.2 ⟨i,h ▸ hDecode i z⟩
  have hYout (i : Fin q) (z : on i) (hz : z.val ∈ out) : ‖Y i z‖ = 1 := by
    apply le_antisymm (mem_closedBall_zero_iff.mp (hYmem i z))
    by_contra! h
    exact hz.2 (mem_iUnion.mpr ⟨i,Y i z,mem_ball_zero_iff.mpr h,hDecode i z⟩)
  let G (z : Z) : Point := if h : ∃ i, z ∈ on i then
    let i := Classical.choose h
    d i (pushDiskRadius z.1 (Y i ⟨z,Classical.choose_spec h⟩))
  else val z
  have hGon (i : Fin q) (z : Z) (hz : z ∈ on i) :
      G z = d i (pushDiskRadius z.1 (Y i ⟨z,hz⟩)) := by
    have h : ∃ j, z ∈ on j := ⟨i,hz⟩
    dsimp only [G]
    rw [dif_pos h]
    have he : i = Classical.choose h := by
      by_contra hij
      exact (disjoint_left.mp (hDisj hij)) hz (Classical.choose_spec h)
    subst i
    rfl
  have hGout (z : Z) (hz : z ∈ out) : G z = val z := by
    by_cases h : ∃ i, z ∈ on i
    · obtain ⟨i,hi⟩ := h
      rw [hGon i z hi, pushDiskRadius_eq_of_norm_eq_one z.1 (hYout i ⟨z,hi⟩ hz), hDecode]
    · exact dif_neg h
  have hVal : Continuous val := continuous_subtype_val.comp continuous_snd
  have hClosedOn (i : Fin q) : IsClosed (on i) :=
    ((isCompact_closedBall _ _).image_of_continuousOn (hd i).1.continuousOn).isClosed.preimage hVal
  let σ (z : Z) : sphere c R := ⟨val z,z.2.property.1⟩
  have hσ : Continuous σ := hVal.subtype_mk _
  have hClosedOut : IsClosed out := by
    have hOpen : IsOpen (⋃ i, ((↑) : sphere c R → Point) ⁻¹' (d i '' ball (0 : Plane) 1)) :=
      isOpen_iUnion fun i => isOpen_sphericalDiskInterior hR (hd i) (hs i)
    have hOut : out = σ ⁻¹' (⋃ i, ((↑) : sphere c R → Point) ⁻¹' (d i '' ball (0 : Plane) 1))ᶜ := by
      ext z
      change val z ∈ sphere c R \ ⋃ i, d i '' ball (0 : Plane) 1 ↔ _
      simp only [Set.mem_sdiff,mem_iUnion,mem_preimage,mem_compl_iff]
      exact and_iff_right z.2.property.1
    rw [hOut]
    exact hOpen.isClosed_compl.preimage hσ
  have hContOn (i : Fin q) : ContinuousOn G (on i) := by
    apply continuousOn_iff_continuous_restrict.mpr
    let z₀ (z : ↥(on i)) : d i '' Disk := ⟨val z.val,z.property⟩
    have hZ₀ : Continuous z₀ := (hVal.comp continuous_subtype_val).subtype_mk _
    have hY : Continuous (Y i) := continuous_subtype_val.comp
      ((embeddedDiskHomeomorph (hd i)).symm.continuous.comp hZ₀)
    have ht : Continuous (fun z : ↥(on i) => z.val.1.val) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
    let F (z : ↥(on i)) := pushDiskRadius z.val.1 (Y i z)
    have hContF : Continuous F := by
      dsimp only [F,pushDiskRadius]
      exact ((continuous_const.sub ht).add (ht.mul (hY.norm.inv₀ fun z => norm_ne_zero_iff.mpr (hYne i z)))).smul hY
    have hG := (hd i).1.continuousOn.comp_continuous hContF
      (fun z => pushDiskRadius_mem_disk z.val.1 (hYmem i z) (hYne i z))
    exact hG.congr (fun z => (hGon i z.val z.property).symm)
  let patches : Option (Fin q) → Set Z := fun i => i.elim out on
  have hCover : ⋃ i, patches i = univ := by
    refine eq_univ_iff_forall.mpr fun z => ?_
    by_cases h : ∃ i, z ∈ on i
    · obtain ⟨i,hi⟩ := h
      exact mem_iUnion.mpr ⟨some i, hi⟩
    · refine mem_iUnion.mpr ⟨none, z.2.property.1, ?_⟩
      intro hZ
      obtain ⟨i,y,hy,he⟩ := mem_iUnion.mp hZ
      exact h ⟨i,y,ball_subset_closedBall hy,he⟩
  have hG : Continuous G := (locallyFinite_of_finite patches).continuous hCover
    (fun i => i.casesOn hClosedOut hClosedOn)
    (fun i => i.casesOn (hVal.continuousOn.congr hGout) hContOn)
  have hGdisk (i : Fin q) (z : on i) :
      pushDiskRadius z.val.1 (Y i z) ∈ Disk :=
    pushDiskRadius_mem_disk z.val.1 (hYmem i z) (hYne i z)
  have hMaps (z : Z) : G z ∈ X := by
    by_cases h : ∃ i, z ∈ on i
    · obtain ⟨i,hi⟩ := h
      let z' : on i := ⟨z,hi⟩
      let y := pushDiskRadius z.1 (Y i z')
      rw [hGon i z hi]
      change d i y ∈ X
      refine ⟨hs i (hGdisk i z'),?_⟩
      rintro ⟨j,hj⟩
      have h0 : (0 : Plane) ∈ Disk := mem_closedBall_self zero_le_one
      by_cases hij : j = i
      · subst j
        exact pushDiskRadius_nonzero z.1 (hYne i z') ((hd i).2.1 h0 (hGdisk i z') hj).symm
      · exact (disjoint_left.mp (hDisj hij))
          ⟨0,h0,hj⟩ ⟨y,hGdisk i z',rfl⟩
    · change (if hh : ∃ i, z ∈ on i then _ else val z) ∈ X
      rw [dif_neg h]
      exact z.2.property
  refine ⟨⟨fun z => ⟨G z,hMaps z⟩,hG.subtype_mk _⟩,?_,?_,?_⟩
  · intro x
    apply Subtype.ext
    change G (0,x) = x.val
    by_cases h : ∃ i, (0,x) ∈ on i
    · obtain ⟨i,hi⟩ := h
      rw [hGon i (0,x) hi, pushDiskRadius_zero, hDecode]
    · exact dif_neg h
  · intro x
    change G (1,x) ∈ A
    by_cases h : ∃ i, (1,x) ∈ on i
    · obtain ⟨i,hi⟩ := h
      let z : on i := ⟨(1,x),hi⟩
      let y := pushDiskRadius 1 (Y i z)
      have hy : y ∈ Disk := hGdisk i z
      have hyN : ‖y‖ = 1 := by
        change ‖pushDiskRadius 1 (Y i z)‖ = 1
        rw [norm_pushDiskRadius 1 (hYne i z)]
        change (1 - (1 : ℝ)) * ‖Y i z‖ + 1 = 1
        simp
      rw [hGon i (1,x) hi]
      change d i y ∈ A
      refine ⟨hs i hy,?_⟩
      intro hA
      obtain ⟨j,w,hw,he⟩ := mem_iUnion.mp hA
      by_cases hij : j = i
      · subst j
        obtain rfl := (hd i).2.1 (ball_subset_closedBall hw) hy he
        exact (mem_ball_zero_iff.mp hw).ne hyN
      · exact (disjoint_left.mp (hDisj hij)) ⟨w,ball_subset_closedBall hw,he⟩ ⟨y,hy,rfl⟩
    · change (if hh : ∃ i, (1,x) ∈ on i then _ else x.val) ∈ A
      rw [dif_neg h]
      refine ⟨x.property.1,?_⟩
      intro hA
      obtain ⟨i,w,hw,he⟩ := mem_iUnion.mp hA
      exact h ⟨i,w,ball_subset_closedBall hw,he⟩
  · intro t x hx
    apply Subtype.ext
    exact hGout (t,x) hx

/-- Include the complement of the caps into the sphere punctured at
their centers. -/
def puncturedCapSphere_inclusion (c : Point) (R : ℝ)
    {q : ℕ} (d : Fin q → Plane → Point) :
    C(puncturedCapSphere c R d, puncturedCenterSphere c R d) :=
  ⟨fun x => ⟨x.val,puncturedCapSphere_subset_puncturedCenterSphere c R d x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Removing the open caps admits a continuous retraction that fixes
their peripheral boundaries pointwise. -/
theorem exists_puncturedSphere_retraction
    {c : Point} {R : ℝ} (hR : 0 < R) {q : ℕ} (d : Fin q → Plane → Point)
    (hd : ∀ i, IsSmoothDiskEmbedding (d i)) (hs : ∀ i, MapsTo (d i) Disk (sphere c R))
    (hDisj : Pairwise (fun i j => Disjoint (d i '' Disk) (d j '' Disk))) :
    ∃ F : C(puncturedCenterSphere c R d, puncturedCapSphere c R d),
      Function.LeftInverse F (puncturedCapSphere_inclusion c R d) := by
  obtain ⟨H,_,hA,hFix⟩ := exists_puncturedSphere_radial_deformation hR d hd hs hDisj
  let D (x : puncturedCenterSphere c R d) := (H (1,x)).val
  have hD : Continuous D := continuous_subtype_val.comp
    (H.continuous.comp (continuous_const.prodMk continuous_id))
  let F : C(puncturedCenterSphere c R d, puncturedCapSphere c R d) :=
    ⟨fun x => ⟨D x,hA x⟩,hD.subtype_mk _⟩
  refine ⟨F, fun x => Subtype.ext ?_⟩
  exact congrArg (fun z : puncturedCenterSphere c R d => z.val)
    (hFix 1 (puncturedCapSphere_inclusion c R d x) x.property)

/-- A based homotopy in the point-punctured sphere between paths in the
cap complement can be retracted to the cap complement with fixed endpoints. -/
theorem puncturedCapSphere_pathHomotopic_iff
    {c : Point} {R : ℝ} (hR : 0 < R) {q : ℕ} (d : Fin q → Plane → Point)
    (hd : ∀ i, IsSmoothDiskEmbedding (d i)) (hs : ∀ i, MapsTo (d i) Disk (sphere c R))
    (hDisj : Pairwise (fun i j => Disjoint (d i '' Disk) (d j '' Disk)))
    {x y : puncturedCapSphere c R d} (p r : Path x y) :
    p.Homotopic r ↔ (p.map (puncturedCapSphere_inclusion c R d).continuous).Homotopic
      (r.map (puncturedCapSphere_inclusion c R d).continuous) := by
  let j := puncturedCapSphere_inclusion c R d
  constructor
  · exact fun h => h.map j
  · intro h
    obtain ⟨F,hF⟩ := exists_puncturedSphere_retraction hR d hd hs hDisj
    have hMap (s : Path x y) : ((s.map j.continuous).map F.continuous).cast
        (hF x).symm (hF y).symm = s := by
      apply Path.ext
      funext t
      exact hF (s t)
    have h' := (h.map F).pathCast (hF x).symm (hF y).symm
    rwa [hMap p,hMap r] at h'

end Thesis.MeasureGeometry
