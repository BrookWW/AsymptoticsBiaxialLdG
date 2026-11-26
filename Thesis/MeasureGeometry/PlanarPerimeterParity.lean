module

public import Thesis.MeasureGeometry.VacuumPathParity
public import Mathlib.Analysis.Convex.PathConnected

/-! Perimeter parity and cancellation on a finite family of planar strips. -/

public section

noncomputable section

open Set
open scoped BigOperators Topology unitInterval

namespace Thesis.MeasureGeometry

/-- A rectangle traversed counterclockwise from its upper-right corner, with
one quarter of the unit interval assigned to each edge. -/
@[expose] def rectangularPerimeter (l r b t : ℝ) : Path ((r,t) : ℝ × ℝ) (r,t) :=
  (((Path.segment (r,t) (l,t)).trans (Path.segment (l,t) (l,b))).trans
    ((Path.segment (l,b) (r,b)).trans (Path.segment (r,b) (r,t))))

private theorem segment_horizontal (h : ℝ) (x y : ℝ) (s : unitInterval) :
    (Path.segment ((x,h) : ℝ × ℝ) (y,h) s).2 = h := by
  rw [Path.segment_apply, AffineMap.lineMap_apply_module]
  change (1 - (s : ℝ)) * h + (s : ℝ) * h = h
  ring

private theorem segment_vertical (x y z : ℝ) (s : unitInterval) :
    (Path.segment ((x,y) : ℝ × ℝ) (x,z) s).1 = x := by
  rw [Path.segment_apply, AffineMap.lineMap_apply_module]
  change (1 - (s : ℝ)) * x + (s : ℝ) * x = x
  ring

private theorem mem_of_snd_eq {U : Set (ℝ × ℝ)} {p : ℝ × ℝ} {h : ℝ}
    (hp : p.2 = h) (hU : (p.1,h) ∈ U) : p ∈ U := by
  rcases p with ⟨x,y⟩
  change y = h at hp
  subst y
  exact hU

private theorem mem_of_fst_eq {U : Set (ℝ × ℝ)} {p : ℝ × ℝ} {h : ℝ}
    (hp : p.1 = h) (hU : (h,p.2) ∈ U) : p ∈ U := by
  rcases p with ⟨x,y⟩
  change x = h at hp
  subst x
  exact hU

/-- The actual perimeter is contained in the closed rectangle. -/
theorem rectangularPerimeter_mem_closed {l r b t : ℝ} (hx : l ≤ r) (hy : b ≤ t)
    (s : unitInterval) : rectangularPerimeter l r b t s ∈ Icc l r ×ˢ Icc b t := by
  have hConv : Convex ℝ (Icc l r ×ˢ Icc b t) := (convex_Icc _ _).prod (convex_Icc _ _)
  have hTR : ((r,t) : ℝ × ℝ) ∈ Icc l r ×ˢ Icc b t := ⟨⟨hx,le_rfl⟩,⟨hy,le_rfl⟩⟩
  have hTL : ((l,t) : ℝ × ℝ) ∈ Icc l r ×ˢ Icc b t := ⟨⟨le_rfl,hx⟩,⟨hy,le_rfl⟩⟩
  have hBL : ((l,b) : ℝ × ℝ) ∈ Icc l r ×ˢ Icc b t := ⟨⟨le_rfl,hx⟩,⟨le_rfl,hy⟩⟩
  have hBR : ((r,b) : ℝ × ℝ) ∈ Icc l r ×ˢ Icc b t := ⟨⟨hx,le_rfl⟩,⟨le_rfl,hy⟩⟩
  have hSub : range (rectangularPerimeter l r b t) ⊆ Icc l r ×ˢ Icc b t := by
    simp only [rectangularPerimeter, Path.trans_range, Path.range_segment, union_subset_iff]
    exact ⟨⟨hConv.segment_subset hTR hTL,hConv.segment_subset hTL hBL⟩,
      ⟨hConv.segment_subset hBL hBR,hConv.segment_subset hBR hTR⟩⟩
  exact hSub (mem_range_self s)

/-- A domain containing the four sides contains the actual perimeter. -/
theorem rectangularPerimeter_mem_from_sides
    {U : Set (ℝ × ℝ)} {l r b t : ℝ} (hy : b ≤ t)
    (hTop : ∀ x, (x,t) ∈ U) (hBottom : ∀ x, (x,b) ∈ U)
    (hLeft : ∀ y ∈ Icc b t, (l,y) ∈ U) (hRight : ∀ y ∈ Icc b t, (r,y) ∈ U)
    (s : unitInterval) : rectangularPerimeter l r b t s ∈ U := by
  have hP : range (rectangularPerimeter l r b t) ⊆ U := by
    simp only [rectangularPerimeter, Path.trans_range, union_subset_iff]
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
    · rintro _ ⟨u,rfl⟩
      exact mem_of_snd_eq (segment_horizontal t r l u) (hTop _)
    · rintro _ ⟨u,rfl⟩
      have hConv : Convex ℝ ({l} ×ˢ Icc b t) := (convex_singleton l).prod (convex_Icc _ _)
      have hMem := hConv.segment_subset (show (l,t) ∈ {l} ×ˢ Icc b t from ⟨rfl,hy,le_rfl⟩)
        (show (l,b) ∈ {l} ×ˢ Icc b t from ⟨rfl,le_rfl,hy⟩)
      have h := hMem (by rw [← Path.range_segment]; exact mem_range_self u)
      exact mem_of_fst_eq (segment_vertical l t b u) (hLeft _ h.2)
    · rintro _ ⟨u,rfl⟩
      exact mem_of_snd_eq (segment_horizontal b l r u) (hBottom _)
    · rintro _ ⟨u,rfl⟩
      have hConv : Convex ℝ ({r} ×ˢ Icc b t) := (convex_singleton r).prod (convex_Icc _ _)
      have hMem := hConv.segment_subset (show (r,b) ∈ {r} ×ˢ Icc b t from ⟨rfl,le_rfl,hy⟩)
        (show (r,t) ∈ {r} ×ˢ Icc b t from ⟨rfl,hy,le_rfl⟩)
      have h := hMem (by rw [← Path.range_segment]; exact mem_range_self u)
      exact mem_of_fst_eq (segment_vertical r b t u) (hRight _ h.2)
  exact hP (mem_range_self s)

/-- The vacuum path obtained by applying a continuous map on a subset to a
path lying wholly in that subset. -/
@[expose] def mappedPathOn {X : Type*} [TopologicalSpace X] {a : BulkCoefficients}
    {U : Set X} (Q : C(U,vacuum a)) {x y : X} (p : Path x y) (hp : ∀ s, p s ∈ U) :
    Path (Q ⟨x,p.source ▸ hp 0⟩) (Q ⟨y,p.target ▸ hp 1⟩) where
  toFun s := Q ⟨p s,hp s⟩
  continuous_toFun := Q.continuous.comp (p.continuous.subtype_mk _)
  source' := congrArg Q (Subtype.ext p.source)
  target' := congrArg Q (Subtype.ext p.target)

theorem mappedPathOn_apply {X : Type*} [TopologicalSpace X] {a : BulkCoefficients}
    {U : Set X} (Q : C(U,vacuum a)) {x y : X} (p : Path x y) (hp : ∀ s, p s ∈ U)
    (s : unitInterval) : mappedPathOn Q p hp s = Q ⟨p s,hp s⟩ := rfl

private theorem mappedPathOn_parity_trans {X : Type*} [TopologicalSpace X] {a : BulkCoefficients}
    (v : Sphere3) {U : Set X} (Q : C(U,vacuum a)) {x y z : X}
    (p : Path x y) (q : Path y z) (hp : ∀ s, p s ∈ U) (hq : ∀ s, q s ∈ U)
    (h : ∀ s, (p.trans q) s ∈ U) :
    vacuumPathLightParity a v (mappedPathOn Q (p.trans q) h) =
      vacuumPathLightParity a v (mappedPathOn Q p hp) + vacuumPathLightParity a v (mappedPathOn Q q hq) := by
  have he : mappedPathOn Q (p.trans q) h = (mappedPathOn Q p hp).trans (mappedPathOn Q q hq) := by
    apply Path.ext
    funext s
    by_cases hs : (s : ℝ) ≤ 1/2
    · rw [mappedPathOn_apply, Path.trans_apply (mappedPathOn Q p hp), dif_pos hs, mappedPathOn_apply]
      apply congrArg Q
      apply Subtype.ext
      change (p.trans q) s = _
      rw [Path.trans_apply,dif_pos hs]
    · rw [mappedPathOn_apply, Path.trans_apply (mappedPathOn Q p hp), dif_neg hs, mappedPathOn_apply]
      apply congrArg Q
      apply Subtype.ext
      change (p.trans q) s = _
      rw [Path.trans_apply,dif_neg hs]
  rw [he,vacuumPathLightParity_trans]

private theorem mappedPathOn_parity_eq_of_convex {a : BulkCoefficients} (v : Sphere3)
    {U V : Set (ℝ × ℝ)} (Q : C(U,vacuum a)) (hV : Convex ℝ V) (hVU : V ⊆ U)
    {x y : ℝ × ℝ} (p q : Path x y) (hp : ∀ s, p s ∈ V) (hq : ∀ s, q s ∈ V)
    (hpU : ∀ s, p s ∈ U) (hqU : ∀ s, q s ∈ U) :
    vacuumPathLightParity a v (mappedPathOn Q p hpU) =
      vacuumPathLightParity a v (mappedPathOn Q q hqU) := by
  let F (s : unitInterval × unitInterval) := (1 - s.1.val) • p s.2 + s.1.val • q s.2
  have hF (s : unitInterval × unitInterval) : F s ∈ U := hVU
    (hV (hp s.2) (hq s.2) (sub_nonneg.mpr s.1.property.2) s.1.property.1 (sub_add_cancel _ _))
  have hc : Continuous F := by
    dsimp only [F]
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (p.continuous.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul (q.continuous.comp continuous_snd))
  let G : C(unitInterval × unitInterval,vacuum a) :=
    ⟨fun s => Q ⟨F s,hF s⟩,Q.continuous.comp (hc.subtype_mk _)⟩
  apply vacuumPathLightParity_homotopic
  refine ⟨{ toContinuousMap := G
            map_zero_left := fun s => ?_
            map_one_left := fun s => ?_
            prop' := fun s t ht => ?_ }⟩
  · have he : F (0,s) = p s := by simp [F]
    exact congrArg Q (Subtype.ext he)
  · have he : F (1,s) = q s := by simp [F]
    exact congrArg Q (Subtype.ext he)
  · rcases ht with h | h
    · have he : F (s,t) = p t := by
        have ht0 : t = 0 := h
        subst t
        rw [show F (s,0) = (1 - s.val) • p 0 + s.val • q 0 from rfl, p.source,q.source,
          ← add_smul,sub_add_cancel,one_smul]
      exact congrArg Q (Subtype.ext he)
    · have he : F (s,t) = p t := by
        have ht1 : t = 1 := h
        subst t
        rw [show F (s,1) = (1 - s.val) • p 1 + s.val • q 1 from rfl, p.target,q.target,
          ← add_smul,sub_add_cancel,one_smul]
      exact congrArg Q (Subtype.ext he)

private theorem mappedHorizontal_parity_add {a : BulkCoefficients} (v : Sphere3)
    {U : Set (ℝ × ℝ)} (Q : C(U,vacuum a)) (h : ℝ) (a₀ a₁ a₂ : ℝ)
    (h01 : a₀ ≤ a₁) (h12 : a₁ ≤ a₂) (hU : ∀ x, (x,h) ∈ U) :
    vacuumPathLightParity a v (mappedPathOn Q (Path.segment (a₀,h) (a₁,h))
      (fun s => mem_of_snd_eq (segment_horizontal h a₀ a₁ s) (hU _))) +
    vacuumPathLightParity a v (mappedPathOn Q (Path.segment (a₁,h) (a₂,h))
      (fun s => mem_of_snd_eq (segment_horizontal h a₁ a₂ s) (hU _))) =
    vacuumPathLightParity a v (mappedPathOn Q (Path.segment (a₀,h) (a₂,h))
      (fun s => mem_of_snd_eq (segment_horizontal h a₀ a₂ s) (hU _))) := by
  let V : Set (ℝ × ℝ) := Icc a₀ a₂ ×ˢ {h}
  have hV : Convex ℝ V := (convex_Icc _ _).prod (convex_singleton h)
  have hVU : V ⊆ U := by
    rintro ⟨x,z⟩ ⟨_,hz⟩
    have hz' : z = h := mem_singleton_iff.mp hz
    subst z
    exact hU _
  have hx₀ : (a₀,h) ∈ V := ⟨⟨le_rfl,h01.trans h12⟩,rfl⟩
  have hx₁ : (a₁,h) ∈ V := ⟨⟨h01,h12⟩,rfl⟩
  have hx₂ : (a₂,h) ∈ V := ⟨⟨h01.trans h12,le_rfl⟩,rfl⟩
  let p := Path.segment (a₀,h) (a₁,h)
  let q := Path.segment (a₁,h) (a₂,h)
  let r := Path.segment (a₀,h) (a₂,h)
  have hp : ∀ s, p s ∈ V := fun s => hV.segment_subset hx₀ hx₁
    (by rw [← Path.range_segment]; exact mem_range_self s)
  have hq : ∀ s, q s ∈ V := fun s => hV.segment_subset hx₁ hx₂
    (by rw [← Path.range_segment]; exact mem_range_self s)
  have hr : ∀ s, r s ∈ V := fun s => hV.segment_subset hx₀ hx₂
    (by rw [← Path.range_segment]; exact mem_range_self s)
  have hpq : ∀ s, (p.trans q) s ∈ V := by
    have hSub : range (p.trans q) ⊆ V := by
      rw [Path.trans_range,union_subset_iff]
      exact ⟨range_subset_iff.mpr hp,range_subset_iff.mpr hq⟩
    exact fun s => hSub (mem_range_self s)
  calc
    _ = vacuumPathLightParity a v (mappedPathOn Q (p.trans q) (fun s => hVU (hpq s))) :=
      (mappedPathOn_parity_trans v Q p q
        (fun s => hVU (hp s)) (fun s => hVU (hq s)) (fun s => hVU (hpq s))).symm
    _ = _ := mappedPathOn_parity_eq_of_convex v Q hV hVU _ _ hpq hr _ _

private theorem mappedHorizontal_parity_symm {a : BulkCoefficients} (v : Sphere3)
    {U : Set (ℝ × ℝ)} (Q : C(U,vacuum a)) (h : ℝ) (x y : ℝ) (hU : ∀ z, (z,h) ∈ U) :
    vacuumPathLightParity a v (mappedPathOn Q (Path.segment (y,h) (x,h))
      (fun s => mem_of_snd_eq (segment_horizontal h y x s) (hU _))) =
      vacuumPathLightParity a v (mappedPathOn Q (Path.segment (x,h) (y,h))
        (fun s => mem_of_snd_eq (segment_horizontal h x y s) (hU _))) := by
  let p := Path.segment ((x,h) : ℝ × ℝ) (y,h)
  have he : p.symm = Path.segment (y,h) (x,h) := Path.segment_symm _ _
  have hp : ∀ s, p s ∈ U :=
    fun s => mem_of_snd_eq (segment_horizontal h x y s) (hU _)
  have hc : mappedPathOn Q (Path.segment (y,h) (x,h))
        (fun s => mem_of_snd_eq (segment_horizontal h y x s) (hU _)) =
      (mappedPathOn Q p hp).symm := by
    apply Path.ext
    funext s
    exact congrArg Q (Subtype.ext (congrArg (fun q : Path ((y,h) : ℝ × ℝ) (x,h) => q s) he.symm))
  rw [hc,vacuumPathLightParity_symm]

private theorem mappedVertical_parity_symm {a : BulkCoefficients} (v : Sphere3)
    {U : Set (ℝ × ℝ)} (Q : C(U,vacuum a)) (x b t : ℝ)
    (hUp : ∀ s, Path.segment ((x,b) : ℝ × ℝ) (x,t) s ∈ U)
    (hDown : ∀ s, Path.segment ((x,t) : ℝ × ℝ) (x,b) s ∈ U) :
    vacuumPathLightParity a v (mappedPathOn Q (Path.segment (x,t) (x,b)) hDown) =
      vacuumPathLightParity a v (mappedPathOn Q (Path.segment (x,b) (x,t)) hUp) := by
  let p := Path.segment ((x,b) : ℝ × ℝ) (x,t)
  have he : p.symm = Path.segment (x,t) (x,b) := Path.segment_symm _ _
  have hc : mappedPathOn Q (Path.segment (x,t) (x,b)) hDown = (mappedPathOn Q p hUp).symm := by
    apply Path.ext
    funext s
    exact congrArg Q (Subtype.ext (congrArg (fun q : Path ((x,t) : ℝ × ℝ) (x,b) => q s) he.symm))
  rw [hc,vacuumPathLightParity_symm]

private theorem mappedVertical_mem {U : Set (ℝ × ℝ)} (x : ℝ) {b t : ℝ} (hbt : b ≤ t)
    (hU : ∀ y ∈ Icc b t, (x,y) ∈ U) (s : unitInterval) :
    Path.segment ((x,b) : ℝ × ℝ) (x,t) s ∈ U := by
  have hConv : Convex ℝ ({x} ×ˢ Icc b t) := (convex_singleton _).prod (convex_Icc _ _)
  have h := hConv.segment_subset (show (x,b) ∈ {x} ×ˢ Icc b t from ⟨rfl,le_rfl,hbt⟩)
    (show (x,t) ∈ {x} ×ˢ Icc b t from ⟨rfl,hbt,le_rfl⟩)
    (by rw [← Path.range_segment]; exact mem_range_self s)
  exact mem_of_fst_eq (segment_vertical x b t s) (hU _ h.2)

private theorem mappedVertical_reverse_mem {U : Set (ℝ × ℝ)} (x : ℝ) {b t : ℝ} (hbt : b ≤ t)
    (hU : ∀ y ∈ Icc b t, (x,y) ∈ U) (s : unitInterval) :
    Path.segment ((x,t) : ℝ × ℝ) (x,b) s ∈ U := by
  rw [← Path.segment_symm]
  exact mappedVertical_mem x hbt hU _

/-- The sum of the characters of the strip perimeters is the character of the
outer rectangle. Internal vertical sides appear twice with opposite orientations. -/
theorem rectangularLightParity_sum_strips {a : BulkCoefficients} (v : Sphere3)
    {U : Set (ℝ × ℝ)} (Q : C(U,vacuum a)) (x : ℕ → ℝ) (hx : Monotone x) {b t : ℝ} (hbt : b ≤ t)
    (hTop : ∀ y, (y,t) ∈ U) (hBottom : ∀ y, (y,b) ∈ U)
    (hSides : ∀ (i : ℕ) (y : ℝ), y ∈ Icc b t → (x i,y) ∈ U)
    (n : ℕ) :
    (∑ i ∈ Finset.range n, vacuumPathLightParity a v
      (mappedPathOn Q (rectangularPerimeter (x i) (x (i+1)) b t)
        (rectangularPerimeter_mem_from_sides hbt hTop hBottom (hSides i) (hSides (i+1))))) =
    vacuumPathLightParity a v (mappedPathOn Q (rectangularPerimeter (x 0) (x n) b t)
      (rectangularPerimeter_mem_from_sides hbt hTop hBottom (hSides 0) (hSides n))) := by
  let B (i j : ℕ) := vacuumPathLightParity a v (mappedPathOn Q (Path.segment (x i,b) (x j,b))
    (fun s => mem_of_snd_eq (segment_horizontal b (x i) (x j) s) (hBottom _)))
  let T (i j : ℕ) := vacuumPathLightParity a v (mappedPathOn Q (Path.segment (x i,t) (x j,t))
    (fun s => mem_of_snd_eq (segment_horizontal t (x i) (x j) s) (hTop _)))
  let V (i : ℕ) := vacuumPathLightParity a v (mappedPathOn Q (Path.segment (x i,b) (x i,t))
    (mappedVertical_mem _ hbt (hSides i)))
  let W (i j : ℕ) := vacuumPathLightParity a v (mappedPathOn Q (rectangularPerimeter (x i) (x j) b t)
    (rectangularPerimeter_mem_from_sides hbt hTop hBottom (hSides i) (hSides j)))
  have hW (i j : ℕ) : W i j = T i j + V i + B i j + V j := by
    let p := Path.segment ((x j,t) : ℝ × ℝ) (x i,t)
    let q := Path.segment ((x i,t) : ℝ × ℝ) (x i,b)
    let r := Path.segment ((x i,b) : ℝ × ℝ) (x j,b)
    let s := Path.segment ((x j,b) : ℝ × ℝ) (x j,t)
    have hp : ∀ z, p z ∈ U := fun z =>
      mem_of_snd_eq (segment_horizontal t (x j) (x i) z) (hTop _)
    have hq : ∀ z, q z ∈ U := mappedVertical_reverse_mem _ hbt (hSides i)
    have hr : ∀ z, r z ∈ U := fun z =>
      mem_of_snd_eq (segment_horizontal b (x i) (x j) z) (hBottom _)
    have hs : ∀ z, s z ∈ U := mappedVertical_mem _ hbt (hSides j)
    have hTrans {p₁ p₂ p₃ : ℝ × ℝ} (u : Path p₁ p₂) (w : Path p₂ p₃)
        (hu : ∀ z, u z ∈ U) (hw : ∀ z, w z ∈ U) (z : unitInterval) : u.trans w z ∈ U := by
      by_cases hz : (z : ℝ) ≤ 1/2
      · rw [Path.trans_apply, dif_pos hz]
        exact hu _
      · rw [Path.trans_apply, dif_neg hz]
        exact hw _
    change vacuumPathLightParity a v (mappedPathOn Q ((p.trans q).trans (r.trans s)) _) = _
    rw [mappedPathOn_parity_trans v Q _ _ (hTrans p q hp hq) (hTrans r s hr hs) _,
      mappedPathOn_parity_trans v Q p q hp hq _, mappedPathOn_parity_trans v Q r s hr hs _,
      mappedHorizontal_parity_symm v Q t (x i) (x j) hTop,
      mappedVertical_parity_symm v Q (x i) b t (mappedVertical_mem _ hbt (hSides i)) hq]
    change (T i j + V i) + (B i j + V j) = T i j + V i + B i j + V j
    simp only [add_assoc]
  have hV₂ (i : ℕ) : V i + V i = 0 := by
    exact (congrArg (fun x => V i + x) (ZMod.neg_eq_self_mod_two (V i)).symm).trans (add_neg_cancel _)
  have hAdd (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) : W i j + W j k = W i k := by
    have hb := mappedHorizontal_parity_add v Q b (x i) (x j) (x k) (hx hij) (hx hjk) hBottom
    have ht := mappedHorizontal_parity_add v Q t (x i) (x j) (x k) (hx hij) (hx hjk) hTop
    change B i j + B j k = B i k at hb
    change T i j + T j k = T i k at ht
    rw [hW,hW,hW,← ht,← hb]
    calc
      _ = (T i j + T j k) + V i + (B i j + B j k) + V k + (V j + V j) := by abel
      _ = _ := by rw [hV₂,add_zero]
  have hDiag : W 0 0 = 0 := by
    have h : W 0 0 + W 0 0 = W 0 0 := hAdd 0 0 0 le_rfl le_rfl
    exact add_left_cancel (h.trans (add_zero _).symm)
  change (∑ i ∈ Finset.range n, W i (i+1)) = W 0 n
  induction n with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty] using hDiag.symm
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    exact hAdd 0 n (n+1) (Nat.zero_le _) (Nat.le_succ _)

end Thesis.MeasureGeometry
