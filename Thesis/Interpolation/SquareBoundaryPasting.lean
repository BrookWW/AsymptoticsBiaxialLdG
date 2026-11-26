module

public import Thesis.Interpolation.SquareCircleTrace

/-! Compatible four-edge data on the actual closed square boundary. -/

public section

noncomputable section

open HarmonicMaps Set Topology

namespace Thesis

abbrev SquareParameterInterval := Icc (-1 : ℝ) 1

@[expose] def squareSideSign (positive : Bool) : ℝ := if positive then 1 else -1

@[expose] def squareSideEndpoint (positive : Bool) : SquareParameterInterval :=
  ⟨squareSideSign positive, by cases positive <;> norm_num [squareSideSign]⟩

private theorem squareSideSign_injective : Function.Injective squareSideSign := by
  intro x y h
  cases x <;> cases y
  · rfl
  · norm_num [squareSideSign] at h
  · norm_num [squareSideSign] at h
  · rfl

theorem unitSquareSideParameter_val (i : Fin 2) (positive : Bool) (t : SquareParameterInterval) :
    (unitSquareSideParameter i positive t.val).val =
      if i = 0 then WithLp.toLp 2 ![squareSideSign positive, t.val] else WithLp.toLp 2 ![t.val, squareSideSign positive] := by
  have h : (projIcc (-1 : ℝ) 1 (by norm_num) t.val).val = t.val :=
    congrArg Subtype.val (projIcc_of_mem (by norm_num) t.property)
  change unitCellFaceSlice i (EuclideanSpace.single 0 (projIcc (-1 : ℝ) 1 (by norm_num) t.val).val)
    (squareSideSign positive) = _
  rw [h, unitCellFaceSlice_coordinates]
  simp only [PiLp.single_apply, ite_true]

private theorem continuous_unitSquareSideParameter_restrict (i : Fin 2) (positive : Bool) :
    Continuous (fun t : SquareParameterInterval => unitSquareSideParameter i positive t.val) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : SquareParameterInterval => (unitSquareSideParameter i positive t.val).val)
  simp_rw [unitSquareSideParameter_val]
  by_cases hi : i = 0 <;> simp [hi]
  all_goals
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    exact continuous_pi fun j => by fin_cases j <;> first | exact continuous_const | exact continuous_subtype_val

theorem exists_unitSquareSideParameter (x : UnitSquareBoundary) :
    ∃ (i : Fin 2) (positive : Bool) (t : SquareParameterInterval), unitSquareSideParameter i positive t.val = x := by
  have hx := (mem_unitSquareBoundary_iff x.val).1 x.property
  have hcoord : ∀ i : Fin 2, |x.val i| ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).1 hx.le
  have ht (i : Fin 2) : x.val i ∈ Icc (-1 : ℝ) 1 := abs_le.1 (hcoord i)
  have hOne : |x.val 0| = 1 ∨ |x.val 1| = 1 := by
    by_contra! h
    have hlt (i : Fin 2) : |x.val i| < 1 := by
      fin_cases i
      · exact lt_of_le_of_ne (hcoord 0) h.1
      · exact lt_of_le_of_ne (hcoord 1) h.2
    have hV : x.val ∈ (unitCellCube 2).val := by
      simp only [unitCellCube, mem_iInter, mem_preimage]
      exact fun i => abs_lt.1 (hlt i)
    have h : x.val ∈ planarSquare 1 := planarSquare_one_eq_unitCellCube.symm ▸ hV
    exact (show ‖WithLp.ofLp x.val‖ < 1 from h).ne hx
  have hSign (z : ℝ) (hz : |z| = 1) : ∃ b : Bool, z = squareSideSign b := by
    by_cases h : 0 ≤ z
    · exact ⟨true, by simpa [squareSideSign, abs_of_nonneg h] using hz⟩
    · exact ⟨false, by rw [abs_of_neg (lt_of_not_ge h)] at hz; simp [squareSideSign]; linarith⟩
  rcases hOne with h₀ | h₁
  · obtain ⟨b, hb⟩ := hSign _ h₀
    refine ⟨0, b, ⟨x.val 1, ht 1⟩, Subtype.ext ?_⟩
    rw [unitSquareSideParameter_val]
    ext i
    fin_cases i <;> simp [hb]
  · obtain ⟨b, hb⟩ := hSign _ h₁
    refine ⟨1, b, ⟨x.val 0, ht 0⟩, Subtype.ext ?_⟩
    rw [unitSquareSideParameter_val]
    ext i
    fin_cases i <;> simp [hb]

/-- Four continuous edge data with the same corner values determine the actual boundary map. -/
theorem exists_unitSquareBoundary_map {X : Type*} [TopologicalSpace X]
    (e : Fin 2 → Bool → C(SquareParameterInterval, X))
    (hCorner : ∀ i j : Bool, e 0 i (squareSideEndpoint j) = e 1 j (squareSideEndpoint i)) :
    ∃ b : C(UnitSquareBoundary, X), ∀ (i : Fin 2) (p : Bool) (t : SquareParameterInterval),
      b (unitSquareSideParameter i p t.val) = e i p t := by
  let E := (Fin 2 × Bool) × SquareParameterInterval
  let π (z : E) := unitSquareSideParameter z.1.1 z.1.2 z.2.val
  let F (z : E) := e z.1.1 z.1.2 z.2
  have hPis : Function.Surjective π := by
    intro x
    obtain ⟨i, p, t, ht⟩ := exists_unitSquareSideParameter x
    exact ⟨((i,p),t), ht⟩
  have hP : Continuous π := continuous_prod_of_discrete_left.2 fun p =>
    continuous_unitSquareSideParameter_restrict p.1 p.2
  have hF : Continuous F := continuous_prod_of_discrete_left.2 fun p => (e p.1 p.2).continuous
  have hFiber (x y : E) (hxy : π x = π y) : F x = F y := by
    obtain ⟨⟨i, p⟩, t⟩ := x
    obtain ⟨⟨j, q⟩, s⟩ := y
    have h := congrArg Subtype.val hxy
    change (unitSquareSideParameter i p t.val).val = (unitSquareSideParameter j q s.val).val at h
    rw [unitSquareSideParameter_val, unitSquareSideParameter_val] at h
    have h₀ := congrArg (fun z : Plane => z 0) h
    have h₁ := congrArg (fun z : Plane => z 1) h
    fin_cases i <;> fin_cases j
    · have hsign : squareSideSign p = squareSideSign q := by simpa using h₀
      have ht : t = s := Subtype.ext (by simpa using h₁)
      rw [squareSideSign_injective hsign, ht]
    · have ht : t = squareSideEndpoint q := Subtype.ext (by simpa [squareSideEndpoint] using h₁)
      have hs : s = squareSideEndpoint p := Subtype.ext (by simpa [squareSideEndpoint] using h₀.symm)
      rw [ht, hs]
      exact hCorner p q
    · have ht : t = squareSideEndpoint q := Subtype.ext (by simpa [squareSideEndpoint] using h₀)
      have hs : s = squareSideEndpoint p := Subtype.ext (by simpa [squareSideEndpoint] using h₁.symm)
      rw [ht, hs]
      exact (hCorner q p).symm
    · have hsign : squareSideSign p = squareSideSign q := by simpa using h₁
      have ht : t = s := Subtype.ext (by simpa using h₀)
      rw [squareSideSign_injective hsign, ht]
  let b (x : UnitSquareBoundary) := F (Classical.choose (hPis x))
  have hEq : b ∘ π = F := funext fun z => hFiber _ z (Classical.choose_spec (hPis (π z)))
  letI : CompactSpace SquareParameterInterval := isCompact_iff_compactSpace.1 isCompact_Icc
  have hQuot : IsQuotientMap π := hP.isClosedMap.isQuotientMap hP hPis
  have hb : Continuous b := hQuot.continuous_iff.2 (hEq ▸ hF)
  exact ⟨⟨b, hb⟩, fun i p t => congrFun hEq ((i,p),t)⟩

end Thesis
