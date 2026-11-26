module

public import Thesis.Definitions
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! Geometry of junctions with balanced discrete weights and even light-edge parity. -/

public section

open scoped BigOperators InnerProductSpace

namespace Thesis.MeasureGeometry

private theorem unit_pair_of_balance {u v : Point} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h : a • u + b • v = 0) : a = b ∧ u = -v := by
  have hs : a • u = -(b • v) := add_eq_zero_iff_eq_neg.1 h
  have hab := congrArg norm hs
  rw [norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg ha.le, Real.norm_of_nonneg hb.le,
    hu, hv, mul_one, mul_one] at hab
  refine ⟨hab, smul_right_injective Point hb.ne' ?_⟩
  change b • u = b • (-v)
  rw [smul_neg]
  exact hab ▸ hs

private theorem unit_pair_eq_of_double_balance {u v z : Point}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) (hs : u + v + (2 : ℝ) • z = 0) : u = v := by
  have h := congrArg (fun p : Point => ‖p‖ ^ 2) (add_eq_zero_iff_eq_neg.1 hs)
  rw [norm_add_sq_real, norm_neg, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    hu, hv, hz, mul_one] at h
  have hdist : ‖u - v‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hu, hv]
    linarith only [h]
  exact sub_eq_zero.1 (norm_eq_zero.1 (by nlinarith only [hdist, norm_nonneg (u - v)]))

private theorem unit_triple_inner {u v z : Point}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) (hs : u + v + z = 0) :
    inner ℝ u v = -(1 / 2 : ℝ) := by
  have h := congrArg (fun p : Point => ‖p‖ ^ 2) (add_eq_zero_iff_eq_neg.1 hs)
  rw [norm_add_sq_real, norm_neg, hu, hv, hz] at h
  linarith only [h]

private theorem unit_triple_angle {u v z : Point}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) (hs : u + v + z = 0) :
    InnerProductGeometry.angle u v = 2 * Real.pi / 3 := by
  have hArc : Real.arccos (1 / 2 : ℝ) = Real.pi / 3 := by
    rw [← Real.cos_pi_div_three]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  rw [InnerProductGeometry.angle, unit_triple_inner hu hv hz hs, hu, hv, mul_one, div_one,
    Real.arccos_neg, hArc]
  ring

private theorem unit_triple_independent_first_two {u v z : Point}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) (hs : u + v + z = 0) :
    LinearIndependent ℝ ![u, v] := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  apply (LinearIndependent.pair_iff' hu0).2
  intro t h
  have ht := congrArg (inner ℝ u) h
  have ht' : t = -(1 / 2 : ℝ) := by
    simpa only [real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one,
      unit_triple_inner hu hv hz hs] using ht
  have hnorm := congrArg norm h
  rw [norm_smul, hu, hv, mul_one, ht'] at hnorm
  norm_num at hnorm

private theorem exists_third {ι : Type*} [Fintype ι] {i j : ι} (hij : i ≠ j) (h3 : Fintype.card ι = 3) :
    ∃ k : ι, k ≠ i ∧ k ≠ j := by
  classical
  have hCard : ({i, j} : Finset ι).card < (Finset.univ : Finset ι).card := by
    rw [Finset.card_pair hij, Finset.card_univ, h3]
    decide
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hCard
  exact ⟨k, fun h => hk (by simp [h]), fun h => hk (by simp [h])⟩

private theorem triple_eq_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (h3 : Fintype.card ι = 3) :
    ({i, j, k} : Finset ι) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_insert_of_notMem (by simp [hij, hik]), Finset.card_pair hjk, h3]

private theorem sum_eq_triple {ι : Type*} [Fintype ι] {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (h3 : Fintype.card ι = 3)
    {M : Type*} [AddCommMonoid M] (f : ι → M) :
    ∑ l, f l = f i + f j + f k := by
  classical
  rw [← triple_eq_univ hij hik hjk h3, Finset.sum_insert (by simp [hij, hik]),
    Finset.sum_pair hjk, add_assoc]

/-- For a nonempty finite junction with distinct unit directions, balance
and even light-edge parity give the degree and direction conclusions. -/
theorem balanced_junction_geometry {ι : Type*} [Fintype ι] (hne : Nonempty ι)
    {κ : ℝ} (hκ : 0 < κ) (v : ι → Point) (θ : ι → ℝ)
    (hv : ∀ i, ‖v i‖ = 1) (hvInj : Function.Injective v)
    (hθ : ∀ i, θ i = κ ∨ θ i = 2 * κ)
    (hBal : ∑ i, θ i • v i = 0)
    (hEven : Even ((Finset.univ.filter fun i => θ i = κ).card)) :
    2 ≤ Fintype.card ι ∧ (∑ i, θ i • v i) = 0 ∧
      Even ((Finset.univ.filter fun i => θ i = κ).card) ∧
      (Fintype.card ι = 2 → ∀ i j, i ≠ j → v i = -v j) ∧
      (Fintype.card ι = 3 → (∀ i, θ i = 2 * κ) ∧
        (∃ P : Submodule ℝ Point, Module.finrank ℝ P = 2 ∧ ∀ i, v i ∈ P) ∧
        ∀ i j, i ≠ j → InnerProductGeometry.angle (v i) (v j) = 2 * Real.pi / 3) := by
  classical
  have hθPos (i : ι) : 0 < θ i := by
    rcases hθ i with h | h
    · rwa [h]
    · rw [h]
      positivity
  have hTwo : 2 ≤ Fintype.card ι := by
    by_contra hn
    have hCard := Fintype.card_pos_iff.2 hne
    have hOne : Fintype.card ι = 1 := by omega
    obtain ⟨i, _⟩ := Fintype.card_eq_one_iff.1 hOne
    have hU : ({i} : Finset ι) = Finset.univ := Finset.eq_univ_of_card _ (by simp [hOne])
    have h := hBal
    rw [← hU, Finset.sum_singleton] at h
    have hne : v i ≠ 0 := by
      intro hz
      have hUnit := hv i
      rw [hz, norm_zero] at hUnit
      norm_num at hUnit
    exact (hθPos i).ne' ((smul_eq_zero.1 h).resolve_right hne)
  refine ⟨hTwo, hBal, hEven, ?_, ?_⟩
  · intro h2 i j hij
    have hU : ({i, j} : Finset ι) = Finset.univ := Finset.eq_univ_of_card _
      ((Finset.card_pair hij).trans h2.symm)
    have h := hBal
    rw [← hU, Finset.sum_pair hij] at h
    exact (unit_pair_of_balance (hθPos i) (hθPos j) (hv i) (hv j) h).2
  intro h3
  have hHeavy (l : ι) : θ l = 2 * κ := by
    let light := Finset.univ.filter fun i => θ i = κ
    have hLightCard : light.card ≤ 3 := by
      simpa only [Finset.card_univ, h3] using Finset.card_le_card (Finset.subset_univ light)
    have hParity : Even light.card := hEven
    obtain ⟨p, hp⟩ := hParity
    have hCases : light.card = 0 ∨ light.card = 2 := by omega
    rcases hCases with hNone | hPair
    · apply (hθ l).resolve_left
      intro hl
      have hlMem : l ∈ light := Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩
      rw [Finset.card_eq_zero.1 hNone] at hlMem
      exact Finset.notMem_empty _ hlMem
    · obtain ⟨i, j, hij, hPairEq⟩ := Finset.card_eq_two.1 hPair
      obtain ⟨k, hki, hkj⟩ := exists_third hij h3
      have hi : θ i = κ := (Finset.mem_filter.1 (show i ∈ light by rw [hPairEq]; simp)).2
      have hj : θ j = κ := (Finset.mem_filter.1 (show j ∈ light by rw [hPairEq]; simp)).2
      have hk : θ k = 2 * κ := (hθ k).resolve_left fun h => by
        have hkMem : k ∈ light := Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
        simp only [hPairEq, Finset.mem_insert, Finset.mem_singleton, hki, hkj, or_self] at hkMem
      have h := (sum_eq_triple hij hki.symm hkj.symm h3 (fun t => θ t • v t)).symm.trans hBal
      rw [hi, hj, hk] at h
      have hs : κ • (v i + v j + (2 : ℝ) • v k) = 0 := by
        rwa [smul_add, smul_add, smul_smul, mul_comm κ]
      have hDirs := unit_pair_eq_of_double_balance (hv i) (hv j) (hv k)
        ((smul_eq_zero.1 hs).resolve_left hκ.ne')
      exact (hij (hvInj hDirs)).elim
  have hSum : ∑ i, v i = 0 := by
    have hs : (2 * κ) • (∑ i, v i) = 0 := by
      rw [Finset.smul_sum]
      simpa only [hHeavy] using hBal
    exact (smul_eq_zero.1 hs).resolve_left (mul_pos zero_lt_two hκ).ne'
  refine ⟨hHeavy, ?_, ?_⟩
  · obtain ⟨i, _, j, _, hij⟩ := Finset.one_lt_card.1
      (show 1 < (Finset.univ : Finset ι).card by rw [Finset.card_univ, h3]; decide)
    obtain ⟨k, hki, hkj⟩ := exists_third hij h3
    have hs : v i + v j + v k = 0 := (sum_eq_triple hij hki.symm hkj.symm h3 v).symm.trans hSum
    let P := Submodule.span ℝ (Set.range ![v i, v j])
    have hP : Module.finrank ℝ P = 2 := by
      rw [show Module.finrank ℝ P = _ from finrank_span_eq_card
        (unit_triple_independent_first_two (hv i) (hv j) (hv k) hs), Fintype.card_fin]
    have hiP : v i ∈ P := Submodule.subset_span ⟨(0 : Fin 2), rfl⟩
    have hjP : v j ∈ P := Submodule.subset_span ⟨(1 : Fin 2), rfl⟩
    have hkP : v k ∈ P := by
      have h' : v k + (v i + v j) = 0 := by rw [add_comm]; exact hs
      have hk : v k = -(v i + v j) := add_eq_zero_iff_eq_neg.1 h'
      rw [hk]
      exact P.neg_mem (P.add_mem hiP hjP)
    refine ⟨P, hP, fun l => ?_⟩
    have hl : l ∈ ({i, j, k} : Finset ι) := triple_eq_univ hij hki.symm hkj.symm h3 ▸ Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact hiP
    · exact hjP
    · exact hkP
  · intro i j hij
    obtain ⟨k, hki, hkj⟩ := exists_third hij h3
    exact unit_triple_angle (hv i) (hv j) (hv k)
      ((sum_eq_triple hij hki.symm hkj.symm h3 v).symm.trans hSum)

/-- Junction geometry for a finite set of incident segment indices. -/
theorem balanced_incident_geometry {ι : Type*} (I : Finset ι) (hne : I.Nonempty)
    {κ : ℝ} (hκ : 0 < κ) (v : ↥I → Point) (θ : ↥I → ℝ)
    (hv : ∀ i, ‖v i‖ = 1) (hvInj : Function.Injective v)
    (hθ : ∀ i, θ i = κ ∨ θ i = 2 * κ)
    (hBal : ∑ i, θ i • v i = 0)
    (hEven : Even ((Finset.univ.filter fun i => θ i = κ).card)) :
    2 ≤ I.card ∧ (∑ i, θ i • v i) = 0 ∧
      Even ((Finset.univ.filter fun i => θ i = κ).card) ∧
      (I.card = 2 → ∀ i j, i ≠ j → v i = -v j) ∧
      (I.card = 3 → (∀ i, θ i = 2 * κ) ∧
        (∃ P : Submodule ℝ Point, Module.finrank ℝ P = 2 ∧ ∀ i, v i ∈ P) ∧
        ∀ i j, i ≠ j → InnerProductGeometry.angle (v i) (v j) = 2 * Real.pi / 3) := by
  have hNonempty : Nonempty (↥I) := by obtain ⟨i, hi⟩ := hne; exact ⟨⟨i, hi⟩⟩
  simpa only [Fintype.card_coe] using
    balanced_junction_geometry hNonempty hκ v θ hv hvInj hθ hBal hEven

theorem incident_otherEndpoint_ne {m : ℕ} {p q : Fin m → Point} {x : Point}
    (hn : ∀ i, p i ≠ q i) (i : ↥(incidentSegments p q x)) :
    (if x = p i then q i else p i) ≠ x := by
  have hx : x = p i ∨ x = q i := (Finset.mem_filter.1 i.property).2
  by_cases hp : x = p i
  · rw [if_pos hp]
    exact fun h => hn i (hp.symm.trans h.symm)
  · rw [if_neg hp]
    exact fun h => hn i (h.trans (hx.resolve_left hp))

/-- Normalizing the displacement to the other endpoint gives a unit
outgoing direction for every nondegenerate incident segment. -/
theorem norm_outwardDirection {m : ℕ} {p q : Fin m → Point} {x : Point}
    (hn : ∀ i, p i ≠ q i) (i : ↥(incidentSegments p q x)) : ‖outwardDirection p q x i‖ = 1 := by
  let y := if x = p i then q i else p i
  have hnorm : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2
    (sub_ne_zero.2 (incident_otherEndpoint_ne hn i))
  change ‖‖y - x‖⁻¹ • (y - x)‖ = 1
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _)), inv_mul_cancel₀ hnorm]

theorem openSegment_of_outward_step {m : ℕ} {p q : Fin m → Point} {x : Point}
    (hn : ∀ i, p i ≠ q i) (i : ↥(incidentSegments p q x)) {t : ℝ}
    (ht : 0 < t) (htr : t < ‖(if x = p i then q i else p i) - x‖) :
    x + t • outwardDirection p q x i ∈ openSegment ℝ (p i) (q i) := by
  let y := if x = p i then q i else p i
  have hr : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (incident_otherEndpoint_ne hn i))
  have hCoef : t / ‖y - x‖ ∈ Set.Ioo (0 : ℝ) 1 := ⟨div_pos ht hr,
    (div_lt_iff₀ hr).2 (by simpa only [one_mul] using htr)⟩
  have hLine := lineMap_mem_openSegment ℝ x y hCoef
  have hPoint : AffineMap.lineMap x y (t / ‖y - x‖) = x + t • outwardDirection p q x i := by
    rw [AffineMap.lineMap_apply_module']
    change (t / ‖y - x‖) • (y - x) + x = x + t • (‖y - x‖⁻¹ • (y - x))
    rw [smul_smul, div_eq_mul_inv, add_comm]
  rw [hPoint] at hLine
  by_cases hp : x = p i
  · exact (congrArg₂ (openSegment ℝ) hp (if_pos hp)) ▸ hLine
  · have hq : x = q i := ((Finset.mem_filter.1 i.property).2 : x = p i ∨ x = q i).resolve_left hp
    have hOpen : openSegment ℝ x y = openSegment ℝ (p i) (q i) := by
      exact (congrArg₂ (openSegment ℝ) hq (if_neg hp)).trans (openSegment_symm ℝ _ _)
    exact hOpen ▸ hLine

/-- Endpoint-only intersections force the actual outgoing directions of
the distinct incident segments to be distinct. -/
theorem outwardDirection_injective_of_endpoint_intersections {m : ℕ} {p q : Fin m → Point}
    {x : Point} (hn : ∀ i, p i ≠ q i)
    (hMeet : ∀ i j : Fin m, i ≠ j → ∀ z ∈ segment ℝ (p i) (q i) ∩ segment ℝ (p j) (q j),
      (z = p i ∨ z = q i) ∧ (z = p j ∨ z = q j)) :
    Function.Injective (outwardDirection p q x) := by
  intro i j heq
  by_contra hij
  have hIJ : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  let r (k : ↥(incidentSegments p q x)) := ‖(if x = p k then q k else p k) - x‖
  have hr (k : ↥(incidentSegments p q x)) : 0 < r k :=
    norm_pos_iff.2 (sub_ne_zero.2 (incident_otherEndpoint_ne hn k))
  let t := min (r i) (r j) / 2
  have ht : 0 < t := half_pos (lt_min (hr i) (hr j))
  have htmin : t < min (r i) (r j) := half_lt_self (lt_min (hr i) (hr j))
  have hi := openSegment_of_outward_step hn i ht (htmin.trans_le (min_le_left (r i) (r j)))
  have hj := openSegment_of_outward_step hn j ht (htmin.trans_le (min_le_right (r i) (r j)))
  rw [← heq] at hj
  have hEnds := (hMeet i j hIJ _
    ⟨openSegment_subset_segment ℝ _ _ hi, openSegment_subset_segment ℝ _ _ hj⟩).1
  rcases hEnds with hp | hq
  · exact hn i (left_mem_openSegment_iff.1 (hp ▸ hi))
  · exact hn i (right_mem_openSegment_iff.1 (hq ▸ hi))

end Thesis.MeasureGeometry

end
