module

public import Thesis.Definitions
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Finset.Max

/-! Subdivision of finitely many straight segments at their actual vertices. -/

public section

noncomputable section

open Set

namespace Thesis.MeasureGeometry

private def AdjacentCut (T : Finset ℝ) (s t : ℝ) : Prop :=
  s ∈ T ∧ t ∈ T ∧ s < t ∧ ∀ u ∈ T, u ∉ Ioo s t

private theorem exists_adjacentCut_of_mem_Icc (T : Finset ℝ) {a b x : ℝ}
    (ha : a ∈ T) (hb : b ∈ T) (hab : a < b) (hx : x ∈ Icc a b) :
    ∃ s t : ℝ, AdjacentCut T s t ∧ Icc s t ⊆ Icc a b ∧ x ∈ Icc s t := by
  classical
  by_cases hxb : x < b
  · let A := T.filter (fun t => t ≤ x)
    let B := T.filter (fun t => x < t)
    have hA : A.Nonempty := ⟨a, Finset.mem_filter.2 ⟨ha, hx.1⟩⟩
    have hB : B.Nonempty := ⟨b, Finset.mem_filter.2 ⟨hb, hxb⟩⟩
    let s := A.max' hA
    let t := B.min' hB
    have hs := Finset.mem_filter.1 (A.max'_mem hA)
    have ht := Finset.mem_filter.1 (B.min'_mem hB)
    have has : a ≤ s := A.le_max' a (Finset.mem_filter.2 ⟨ha, hx.1⟩)
    have htb : t ≤ b := B.min'_le b (Finset.mem_filter.2 ⟨hb, hxb⟩)
    refine ⟨s, t, ⟨hs.1, ht.1, hs.2.trans_lt ht.2, ?_⟩, Icc_subset_Icc has htb, hs.2, ht.2.le⟩
    intro u hu huI
    by_cases hux : u ≤ x
    · exact huI.1.not_ge (A.le_max' u (Finset.mem_filter.2 ⟨hu, hux⟩))
    · exact huI.2.not_ge (B.min'_le u (Finset.mem_filter.2 ⟨hu, lt_of_not_ge hux⟩))
  · have hEq : x = b := hx.2.antisymm (le_of_not_gt hxb)
    subst x
    let A := T.filter (· < b)
    have hA : A.Nonempty := ⟨a, Finset.mem_filter.2 ⟨ha, hab⟩⟩
    let s := A.max' hA
    have hs := Finset.mem_filter.1 (A.max'_mem hA)
    have has : a ≤ s := A.le_max' a (Finset.mem_filter.2 ⟨ha, hab⟩)
    refine ⟨s, b, ⟨hs.1, hb, hs.2, ?_⟩, Icc_subset_Icc has le_rfl, hs.2.le, le_rfl⟩
    exact fun u hu huI => huI.1.not_ge (A.le_max' u (Finset.mem_filter.2 ⟨hu, huI.2⟩))

private theorem eq_of_adjacentCut_inter_interior {T : Finset ℝ} {a b c d x : ℝ}
    (h₁ : AdjacentCut T a b) (h₂ : AdjacentCut T c d)
    (hA : x ∈ Ioo a b) (hB : x ∈ Icc c d) : a = c ∧ b = d := by
  have hca : c ≤ a := le_of_not_gt fun h => h₁.2.2.2 c h₂.1 ⟨h, hB.1.trans_lt hA.2⟩
  have hbd : b ≤ d := le_of_not_gt fun h => h₁.2.2.2 d h₂.2.1 ⟨hA.1.trans_le hB.2, h⟩
  refine ⟨(le_of_not_gt fun h => h₂.2.2.2 a h₁.1 ⟨h, hA.1.trans_le hB.2⟩).antisymm hca, ?_⟩
  exact hbd.antisymm (le_of_not_gt fun h => h₂.2.2.2 b h₁.2.1 ⟨hB.1.trans_lt hA.2, h⟩)

private theorem image_lineMap_Icc (p q : Point) {a b : ℝ} (hab : a ≤ b) :
    AffineMap.lineMap p q '' Icc a b = segment ℝ (AffineMap.lineMap p q a) (AffineMap.lineMap p q b) := by
  rw [← segment_eq_Icc hab, image_segment]

private theorem segment_subset_line (p q : Point) :
    segment ℝ p q ⊆ (line[ℝ, p, q] : Set Point) := by
  rw [segment_eq_image_lineMap]
  rintro _ ⟨t, _, rfl⟩
  exact AffineMap.lineMap_mem_affineSpan_pair t p q

private theorem subsingleton_inter_distinct_lines {p q v w : Point}
    (hpq : p ≠ q) (hvw : v ≠ w) (h : line[ℝ, p, q] ≠ line[ℝ, v, w]) :
    ((line[ℝ, p, q] : Set Point) ∩ (line[ℝ, v, w] : Set Point)).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hP := collinear_insert_insert_of_mem_affineSpan_pair hx.1 hy.1
  have hQ := collinear_insert_insert_of_mem_affineSpan_pair hx.2 hy.2
  have he₁ : line[ℝ, x, y] = line[ℝ, p, q] :=
    (hP.affineSpan_eq_of_ne (by simp) (by simp) hxy).trans
      (hP.affineSpan_eq_of_ne (by simp) (by simp) hpq).symm
  have he₂ : line[ℝ, x, y] = line[ℝ, v, w] :=
    (hQ.affineSpan_eq_of_ne (by simp) (by simp) hxy).trans
      (hQ.affineSpan_eq_of_ne (by simp) (by simp) hvw).symm
  exact h (he₁.symm.trans he₂)

/-- A finite straight segment family has a subdivision with the same
carrier, supported in the original segments and meeting only at endpoints. -/
theorem exists_finite_segment_subdivision {ι : Type*} [Fintype ι] (p q : ι → Point)
    (hn : ∀ i, p i ≠ q i) :
    ∃ (m : ℕ) (x y : Fin m → Point) (owner : Fin m → ι),
      (∀ j, x j ≠ y j ∧ segment ℝ (x j) (y j) ⊆ segment ℝ (p (owner j)) (q (owner j))) ∧
      (⋃ j, segment ℝ (x j) (y j)) = (⋃ i, segment ℝ (p i) (q i)) ∧
      ∀ j k, j ≠ k → ∀ z ∈ segment ℝ (x j) (y j) ∩ segment ℝ (x k) (y k),
        (z = x j ∨ z = y j) ∧ (z = x k ∨ z = y k) := by
  classical
  let ℓ (i : ι) := line[ℝ, p i, q i]
  let J := range ℓ
  letI : Fintype J := (Set.finite_range ℓ).fintype
  let i₀ (j : J) : ι := Classical.choose j.property
  have hi₀ (j : J) : ℓ (i₀ j) = j.val := Classical.choose_spec j.property
  let F (j : J) : ℝ →ᵃ[ℝ] Point := AffineMap.lineMap (p (i₀ j)) (q (i₀ j))
  have hF (j : J) : Function.Injective (F j) := AffineMap.lineMap_injective ℝ (hn (i₀ j))
  have hFRange (j : J) : range (F j : ℝ → Point) = (j.val : Set Point) := by
    ext z
    rw [← hi₀ j]
    exact mem_affineSpan_pair_iff_exists_lineMap_eq.symm
  let T (i j : ι) : Set Point := if ℓ i = ℓ j then ∅ else (ℓ i : Set Point) ∩ (ℓ j : Set Point)
  have hT (i j : ι) : (T i j).Finite := by
    by_cases h : ℓ i = ℓ j
    · simp only [T, h, if_true, finite_empty]
    · simpa only [T, h, if_false] using (subsingleton_inter_distinct_lines (hn i) (hn j) h).finite
  let P := (range p ∪ range q) ∪ ⋃ i, ⋃ j, T i j
  have hP : P.Finite := ((finite_range p).union (finite_range q)).union
    (finite_iUnion fun i => finite_iUnion fun j => hT i j)
  let C (j : J) : Finset ℝ := (hP.preimage (hF j).injOn).toFinset
  have hC (j : J) (t : ℝ) : t ∈ C j ↔ F j t ∈ P := (Set.Finite.mem_toFinset _)
  let E (j : J) : Finset (ℝ × ℝ) := ((C j).product (C j)).filter fun u =>
    AdjacentCut (C j) u.1 u.2 ∧ ∃ i, segment ℝ (F j u.1) (F j u.2) ⊆ segment ℝ (p i) (q i)
  let I := Σ j : J, ↥(E j)
  let r (i : I) : ℝ × ℝ := i.2.val
  let X (i : I) : Point := F i.1 (r i).1
  let Y (i : I) : Point := F i.1 (r i).2
  have hi (i : I) : AdjacentCut (C i.1) (r i).1 (r i).2 ∧
      ∃ l, segment ℝ (X i) (Y i) ⊆ segment ℝ (p l) (q l) :=
    (Finset.mem_filter.1 i.2.property).2
  let owner (i : I) := Classical.choose (hi i).2
  have hOwner (i : I) : segment ℝ (X i) (Y i) ⊆ segment ℝ (p (owner i)) (q (owner i)) :=
    Classical.choose_spec (hi i).2
  have hXY (i : I) : X i ≠ Y i := (hF i.1).ne (hi i).1.2.2.1.ne
  have hSeg (i : I) : segment ℝ (X i) (Y i) = F i.1 '' Icc (r i).1 (r i).2 :=
    (image_lineMap_Icc _ _ (hi i).1.2.2.1.le).symm
  have hCarrier : (⋃ i : I, segment ℝ (X i) (Y i)) = (⋃ i, segment ℝ (p i) (q i)) := by
    apply subset_antisymm
    · exact iUnion_subset fun i => (hOwner i).trans (subset_iUnion (fun i => segment ℝ (p i) (q i)) (owner i))
    · intro z hz
      obtain ⟨i, hzi⟩ := mem_iUnion.1 hz
      let j : J := ⟨ℓ i, mem_range_self i⟩
      have hpL : p i ∈ (j.val : Set Point) := left_mem_affineSpan_pair ℝ _ _
      have hqL : q i ∈ (j.val : Set Point) := right_mem_affineSpan_pair ℝ _ _
      obtain ⟨s, hs⟩ := hFRange j ▸ hpL
      obtain ⟨t, ht⟩ := hFRange j ▸ hqL
      let a := min s t
      let b := max s t
      have hST : s ≠ t := fun h => hn i (hs.symm.trans (h ▸ ht))
      have hab : a < b := min_lt_max.2 hST
      have hRaw : segment ℝ (p i) (q i) = F j '' Icc a b := by
        rw [← hs, ← ht, ← image_segment, segment_eq_Icc']
      have hS : s ∈ C j := (hC j s).2 (hs.symm ▸ Or.inl (Or.inl (mem_range_self i)))
      have hT : t ∈ C j := (hC j t).2 (ht.symm ▸ Or.inl (Or.inr (mem_range_self i)))
      have ha : a ∈ C j := by
        change min s t ∈ C j
        rcases min_choice s t with he | he <;> rw [he] <;> assumption
      have hb : b ∈ C j := by
        change max s t ∈ C j
        rcases max_choice s t with he | he <;> rw [he] <;> assumption
      rw [hRaw] at hzi
      obtain ⟨u, hu, huz⟩ := hzi
      obtain ⟨c, d, hcd, hSub, huc⟩ := exists_adjacentCut_of_mem_Icc (C j) ha hb hab hu
      have hSubset : segment ℝ (F j c) (F j d) ⊆ segment ℝ (p i) (q i) := by
        rw [← image_lineMap_Icc _ _ hcd.2.2.1.le, hRaw]
        exact image_mono hSub
      let k : I := ⟨j, ⟨(c, d), Finset.mem_filter.2
        ⟨Finset.mem_product.2 ⟨hcd.1, hcd.2.1⟩, hcd, i, hSubset⟩⟩⟩
      exact mem_iUnion.2 ⟨k, (hSeg k).symm ▸ ⟨u, huc, huz⟩⟩
  have hEndpoint (i k : I) (hik : i ≠ k) (z : Point)
      (hz : z ∈ segment ℝ (X i) (Y i)) (hzk : z ∈ segment ℝ (X k) (Y k)) : z = X i ∨ z = Y i := by
    rw [hSeg i] at hz
    rw [hSeg k] at hzk
    obtain ⟨t, ht, htz⟩ := hz
    obtain ⟨u, hu, huz⟩ := hzk
    by_contra hEnd
    push Not at hEnd
    have htI : t ∈ Ioo (r i).1 (r i).2 :=
      ⟨lt_of_le_of_ne ht.1 (fun h => hEnd.1 (htz.symm.trans (congrArg (F i.1) h.symm))),
       lt_of_le_of_ne ht.2 (fun h => hEnd.2 (htz.symm.trans (congrArg (F i.1) h)))⟩
    by_cases hL : i.1 = k.1
    · obtain ⟨i, iSeg⟩ := i
      obtain ⟨k, kSeg⟩ := k
      change i = k at hL
      subst k
      have htu := hF i (htz.trans huz.symm)
      rw [← htu] at hu
      have hEq := eq_of_adjacentCut_inter_interior (hi ⟨i, iSeg⟩).1 (hi ⟨i, kSeg⟩).1 htI hu
      exact hik (congrArg (Sigma.mk i) (Subtype.ext (Prod.ext hEq.1 hEq.2)))
    · have hin₁ : z ∈ (i.1.val : Set Point) := hFRange i.1 ▸ (show z ∈ range (F i.1 : ℝ → Point) from ⟨t, htz⟩)
      have hin₂ : z ∈ (k.1.val : Set Point) := hFRange k.1 ▸ (show z ∈ range (F k.1 : ℝ → Point) from ⟨u, huz⟩)
      have hneq : ℓ (i₀ i.1) ≠ ℓ (i₀ k.1) := fun h =>
        hL (Subtype.ext ((hi₀ i.1).symm.trans (h.trans (hi₀ k.1))))
      have hCross : z ∈ T (i₀ i.1) (i₀ k.1) := by
        dsimp only [T]
        rw [if_neg hneq, hi₀, hi₀]
        exact ⟨hin₁, hin₂⟩
      have hPz : z ∈ P := Or.inr (mem_iUnion.2 ⟨i₀ i.1, mem_iUnion.2 ⟨i₀ k.1, hCross⟩⟩)
      exact (hi i).1.2.2.2 t ((hC i.1 t).2 (htz.symm ▸ hPz)) htI
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, X ∘ e.symm, Y ∘ e.symm, owner ∘ e.symm,
    fun j => ⟨hXY (e.symm j), hOwner (e.symm j)⟩, ?_, ?_⟩
  · rw [← hCarrier]
    ext z
    simp only [Function.comp_apply, mem_iUnion]
    exact ⟨fun ⟨j, hj⟩ => ⟨e.symm j, hj⟩, fun ⟨i, hi⟩ => ⟨e i, by simpa only [Equiv.symm_apply_apply] using hi⟩⟩
  · intro j k hjk z hz
    exact ⟨hEndpoint (e.symm j) (e.symm k) (e.symm.injective.ne hjk) z hz.1 hz.2,
      hEndpoint (e.symm k) (e.symm j) (e.symm.injective.ne hjk.symm) z hz.2 hz.1⟩

end Thesis.MeasureGeometry
