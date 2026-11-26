module

public import Thesis.Foundation.QuaternionThirdClass

/-! The energies of finite ordered factorizations of vacuum loop classes. -/

@[expose] public section

noncomputable section

namespace Thesis

/-- The number of light factors needed to represent a quaternion class at minimal splitting cost. -/
def quaternionSplittingWeight (g : QuaternionGroup 2) : ℕ :=
  if g = 1 then 0 else if IsLightQuaternion g then 1 else 2

private theorem quaternionSplittingWeight_one : quaternionSplittingWeight 1 = 0 := by
  simp [quaternionSplittingWeight]

private theorem quaternionSplittingWeight_light {g : QuaternionGroup 2} (h : IsLightQuaternion g) :
    quaternionSplittingWeight g = 1 := by
  have hg : g ≠ 1 := by intro heq; subst g; exact (by decide : ¬ IsLightQuaternion 1) h
  simp [quaternionSplittingWeight, hg, h]

private theorem quaternionSplittingWeight_other {g : QuaternionGroup 2} (hn : g ≠ 1)
    (h : ¬ IsLightQuaternion g) : quaternionSplittingWeight g = 2 := by
  simp [quaternionSplittingWeight, hn, h]

private theorem quaternionSplittingWeight_le_two (g : QuaternionGroup 2) :
    quaternionSplittingWeight g ≤ 2 := by
  unfold quaternionSplittingWeight
  split
  · decide
  · split <;> decide

private theorem one_le_quaternionSplittingWeight {g : QuaternionGroup 2} (hn : g ≠ 1) :
    1 ≤ quaternionSplittingWeight g := by
  unfold quaternionSplittingWeight
  rw [if_neg hn]
  split <;> decide

private theorem quaternionSplittingWeight_mul_le (g h : QuaternionGroup 2) :
    quaternionSplittingWeight (g * h) ≤ quaternionSplittingWeight g + quaternionSplittingWeight h := by
  by_cases hg : g = 1
  · simp [hg, quaternionSplittingWeight_one]
  by_cases hh : h = 1
  · simp [hh, quaternionSplittingWeight_one]
  exact (quaternionSplittingWeight_le_two _).trans
    (Nat.add_le_add (one_le_quaternionSplittingWeight hg) (one_le_quaternionSplittingWeight hh))

private theorem quaternion_other_cases {g : QuaternionGroup 2} (hn : g ≠ 1)
    (hl : ¬ IsLightQuaternion g) :
    g = QuaternionGroup.a 2 ∨ g = QuaternionGroup.xa 1 ∨ g = QuaternionGroup.xa 3 := by
  suffices ∀ h : QuaternionGroup 2, h = 1 ∨ IsLightQuaternion h ∨
      h = QuaternionGroup.a 2 ∨ h = QuaternionGroup.xa 1 ∨ h = QuaternionGroup.xa 3 by
    exact ((this g).resolve_left hn).resolve_left hl
  rintro (⟨i⟩ | ⟨i⟩) <;> fin_cases i <;> decide

/-- Each nontrivial nonlight quaternion word is an ordered product of
two actual light words. -/
theorem exists_two_light_factors_of_nontrivial_nonlight {g : QuaternionGroup 2}
    (hg : g ≠ 1) (hLight : ¬ IsLightQuaternion g) :
    ∃ f : Fin 2 → QuaternionGroup 2, (∀ i, IsLightQuaternion (f i)) ∧ f 0 * f 1 = g := by
  rcases quaternion_other_cases hg hLight with rfl | rfl | rfl
  · refine ⟨![QuaternionGroup.a 1, QuaternionGroup.a 1], ?_, by decide⟩
    intro i
    fin_cases i <;> decide
  · refine ⟨![QuaternionGroup.xa 0, QuaternionGroup.a 1], ?_, by decide⟩
    intro i
    fin_cases i <;> decide
  · refine ⟨![QuaternionGroup.a 1, QuaternionGroup.xa 0], ?_, by decide⟩
    intro i
    fin_cases i <;> decide

theorem kappaStar_pos (a : BulkCoefficients) : 0 < kappaStar a := by
  unfold kappaStar
  exact div_pos (mul_pos Real.pi_pos (sq_pos_of_pos (vacuumRadius_pos a))) (by norm_num)

theorem vacuumClassCost_ge_splittingWeight (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) :
    kappaStar a * (quaternionSplittingWeight g : ℝ) ≤ vacuumClassCost a v g := by
  by_cases hn : g = 1
  · subst g
    simp [quaternionSplittingWeight_one, vacuumClassCost_one]
  by_cases hl : IsLightQuaternion g
  · simp [quaternionSplittingWeight_light hl, vacuumClassCost_light a v hl]
  rw [quaternionSplittingWeight_other hn hl]
  rw [Nat.cast_ofNat, mul_comm (kappaStar a)]
  rcases quaternion_other_cases hn hl with ha | hk
  · rw [ha, vacuumClassCost_antipodal]
    linarith only [(kappaStar_pos a).le]
  · exact (vacuumClassCost_third_strict a v hk).le

private theorem classCosts_list_ge (a : BulkCoefficients) (cost : QuaternionGroup 2 → ℝ)
    (hCost : ∀ g, kappaStar a * (quaternionSplittingWeight g : ℝ) ≤ cost g)
    (l : List (QuaternionGroup 2)) :
    kappaStar a * (quaternionSplittingWeight l.prod : ℝ) ≤ (l.map cost).sum := by
  induction l with
  | nil =>
      simp [quaternionSplittingWeight_one]
  | cons g l ih =>
      have hwmul : (quaternionSplittingWeight (g * l.prod) : ℝ) ≤
          (quaternionSplittingWeight g : ℝ) + (quaternionSplittingWeight l.prod : ℝ) := by
        exact_mod_cast quaternionSplittingWeight_mul_le g l.prod
      simp only [List.prod_cons, List.map_cons, List.sum_cons]
      calc
        _ ≤ kappaStar a * ((quaternionSplittingWeight g : ℝ) + (quaternionSplittingWeight l.prod : ℝ)) :=
          mul_le_mul_of_nonneg_left hwmul (kappaStar_pos a).le
        _ ≤ _ := by
          rw [mul_add]
          exact add_le_add (hCost g) ih

private theorem exists_shortest_ordered_word (a : BulkCoefficients) (cost : QuaternionGroup 2 → ℝ)
    (hOne : cost 1 = 0) (hLight : ∀ g, IsLightQuaternion g → cost g = kappaStar a)
    (g : QuaternionGroup 2) :
    ∃ l : List (QuaternionGroup 2), l ≠ [] ∧ l.prod = g ∧
      (l.map cost).sum = kappaStar a * (quaternionSplittingWeight g : ℝ) := by
  by_cases hn : g = 1
  · subst g
    exact ⟨[1], by simp, by simp, by simp [hOne, quaternionSplittingWeight_one]⟩
  by_cases hl : IsLightQuaternion g
  · exact ⟨[g], by simp, by simp, by simp [hLight g hl, quaternionSplittingWeight_light hl]⟩
  rw [quaternionSplittingWeight_other hn hl]
  have hI := hLight (QuaternionGroup.a 1) (by decide)
  have hJ := hLight (QuaternionGroup.xa 0) (by decide)
  rcases quaternion_other_cases hn hl with rfl | rfl | rfl
  · exact ⟨[QuaternionGroup.a 1, QuaternionGroup.a 1], by simp, by decide,
      by simp [hI, mul_two]⟩
  · exact ⟨[QuaternionGroup.xa 0, QuaternionGroup.a 1], by simp, by decide,
      by simp [hI, hJ, mul_two]⟩
  · exact ⟨[QuaternionGroup.a 1, QuaternionGroup.xa 0], by simp, by decide,
      by simp [hI, hJ, mul_two]⟩

/-- The total class costs of nonempty ordered words with the prescribed product. -/
def vacuumSplittingEnergies (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) : Set ℝ :=
  {E | ∃ l : List (QuaternionGroup 2), l ≠ [] ∧ l.prod = g ∧ (l.map (vacuumClassCost a v)).sum = E}

theorem vacuumSplittingEnergies_isLeast (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) :
    IsLeast (vacuumSplittingEnergies a v g) (kappaStar a * (quaternionSplittingWeight g : ℝ)) := by
  refine ⟨exists_shortest_ordered_word a (vacuumClassCost a v) (vacuumClassCost_one a v)
    (fun _ => vacuumClassCost_light a v) g, ?_⟩
  intro E hE
  obtain ⟨l, _, hprod, hsum⟩ := hE
  rw [← hprod, ← hsum]
  exact classCosts_list_ge a (vacuumClassCost a v) (vacuumClassCost_ge_splittingWeight a v) l

/-- The singular energy obtained by allowing finite ordered splitting. -/
def vacuumSplittingCost (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) : ℝ :=
  sInf (vacuumSplittingEnergies a v g)

theorem vacuumSplittingCost_eq (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) :
    vacuumSplittingCost a v g = kappaStar a * (quaternionSplittingWeight g : ℝ) :=
  (vacuumSplittingEnergies_isLeast a v g).csInf_eq

theorem vacuumSplittingCost_one (a : BulkCoefficients) (v : Sphere3) :
    vacuumSplittingCost a v 1 = 0 := by
  simp [vacuumSplittingCost_eq, quaternionSplittingWeight_one]

theorem vacuumSplittingCost_light (a : BulkCoefficients) (v : Sphere3)
    {g : QuaternionGroup 2} (hg : IsLightQuaternion g) :
    vacuumSplittingCost a v g = kappaStar a := by
  simp [vacuumSplittingCost_eq, quaternionSplittingWeight_light hg]

theorem vacuumSplittingCost_nontrivial_nonlight (a : BulkCoefficients) (v : Sphere3)
    {g : QuaternionGroup 2} (hn : g ≠ 1) (hg : ¬ IsLightQuaternion g) :
    vacuumSplittingCost a v g = 2 * kappaStar a := by
  simp [vacuumSplittingCost_eq, quaternionSplittingWeight_other hn hg, mul_comm]

theorem vacuumSplittingCost_third_strict (a : BulkCoefficients) (v : Sphere3)
    {g : QuaternionGroup 2} (h : g = QuaternionGroup.xa 1 ∨ g = QuaternionGroup.xa 3) :
    vacuumSplittingCost a v g < vacuumClassCost a v g := by
  have hn : g ≠ 1 := by rcases h with rfl | rfl <;> decide
  have hl : ¬ IsLightQuaternion g := by rcases h with rfl | rfl <;> decide
  rw [vacuumSplittingCost_nontrivial_nonlight a v hn hl]
  exact vacuumClassCost_third_strict a v h

theorem vacuumSplittingCost_antipodal (a : BulkCoefficients) (v : Sphere3) :
    vacuumSplittingCost a v (QuaternionGroup.a 2) = 2 * kappaStar a :=
  vacuumSplittingCost_nontrivial_nonlight a v (by decide) (by decide)

/-- The based loop factorization costs agree with the costs of their quaternion-word images. -/
theorem vacuumBasedSplittingEnergies_eq (a : BulkCoefficients) (v : Sphere3)
    (p : FundamentalGroup (vacuum a) (vacuumQuaternionProjection a v)) :
    {E | ∃ l : List (FundamentalGroup (vacuum a) (vacuumQuaternionProjection a v)),
      l ≠ [] ∧ l.prod = p ∧
      (l.map (fun q => vacuumClassCost a v (vacuumFundamentalGroupEquiv a v q))).sum = E} =
      vacuumSplittingEnergies a v (vacuumFundamentalGroupEquiv a v p) := by
  ext E
  let φ := vacuumFundamentalGroupEquiv a v
  constructor
  · rintro ⟨l, hn, hp, hE⟩
    refine ⟨l.map φ, ?_, ?_, ?_⟩
    · intro he
      exact hn (List.map_eq_nil_iff.mp he)
    · rw [← map_list_prod, hp]
    · change (l.map (fun q => vacuumClassCost a v (φ q))).sum = E at hE
      rw [List.map_map]
      exact hE
  · rintro ⟨l, hn, hp, hE⟩
    refine ⟨l.map φ.symm, ?_, ?_, ?_⟩
    · intro he
      exact hn (List.map_eq_nil_iff.mp he)
    · rw [← map_list_prod, hp, MulEquiv.symm_apply_apply]
    · change ((l.map φ.symm).map (fun q => vacuumClassCost a v (φ q))).sum = E
      rw [List.map_map]
      have hF : (fun q => vacuumClassCost a v (φ q)) ∘ φ.symm = vacuumClassCost a v := by
        funext q
        rw [Function.comp_apply, MulEquiv.apply_symm_apply]
      rwa [hF]

/-- The splitting value depends on the model coefficients and the word class, for any chosen lift. -/
theorem vacuumSplittingCost_basepoint_independent (a : BulkCoefficients) (v w : Sphere3)
    (g : QuaternionGroup 2) : vacuumSplittingCost a v g = vacuumSplittingCost a w g := by
  rw [vacuumSplittingCost_eq, vacuumSplittingCost_eq]

private theorem quaternion_conj_labels (h g : QuaternionGroup 2) :
    (h * g * h⁻¹ = 1 ↔ g = 1) ∧
    (IsLightQuaternion (h * g * h⁻¹) ↔ IsLightQuaternion g) ∧
    (h * g * h⁻¹ = QuaternionGroup.a 2 ↔ g = QuaternionGroup.a 2) := by
  rcases h with ⟨i⟩ | ⟨i⟩ <;> rcases g with ⟨j⟩ | ⟨j⟩ <;>
    fin_cases i <;> fin_cases j <;> decide

private theorem isConj_labels {g h : QuaternionGroup 2} (hh : IsConj g h) :
    (g = 1 ↔ h = 1) ∧
    (IsLightQuaternion g ↔ IsLightQuaternion h) ∧
    (g = QuaternionGroup.a 2 ↔ h = QuaternionGroup.a 2) := by
  obtain ⟨k, rfl⟩ := isConj_iff.mp hh
  obtain ⟨h₁, h₂, h₃⟩ := quaternion_conj_labels k g
  exact ⟨h₁.symm, h₂.symm, h₃.symm⟩

theorem quaternionSplittingWeight_conj {g h : QuaternionGroup 2} (hh : IsConj g h) :
    quaternionSplittingWeight g = quaternionSplittingWeight h := by
  obtain ⟨h₁, h₂, _⟩ := isConj_labels hh
  simp only [quaternionSplittingWeight, h₁, h₂]

/-- The energies of Sobolev loops whose word belongs to the specified conjugacy class. -/
def vacuumConjugacyEnergies (a : BulkCoefficients) (g : QuaternionGroup 2) : Set ℝ :=
  {E | ∃ (v : Sphere3) (h : QuaternionGroup 2), IsConj h g ∧ E ∈ vacuumClassEnergies a v h}

theorem vacuumConjugacyEnergies_conj (a : BulkCoefficients) {g h : QuaternionGroup 2}
    (hh : IsConj g h) : vacuumConjugacyEnergies a g = vacuumConjugacyEnergies a h := by
  ext E
  constructor
  · rintro ⟨v, w, hw, hE⟩
    exact ⟨v, w, hw.trans hh, hE⟩
  · rintro ⟨v, w, hw, hE⟩
    exact ⟨v, w, hw.trans hh.symm, hE⟩

private theorem vacuumClassEnergies_nonempty (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) :
    (vacuumClassEnergies a v g).Nonempty := by
  by_cases h₁ : g = 1
  · subst g
    exact ⟨0, (vacuumClassEnergies_isLeast_one a v).1⟩
  by_cases hl : IsLightQuaternion g
  · exact ⟨kappaStar a, (vacuumClassEnergies_isLeast_light a v hl).1⟩
  rcases quaternion_other_cases h₁ hl with rfl | hk
  · exact ⟨4 * kappaStar a, (vacuumClassEnergies_isLeast_antipodal a v).1⟩
  · exact ⟨4 * kappaStar a, exists_vacuumLoop_third_class_competitor a v hk⟩

private theorem vacuumClassEnergies_bddBelow (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) :
    BddBelow (vacuumClassEnergies a v g) := by
  refine ⟨0, ?_⟩
  rintro E ⟨γ, _, _, rfl⟩
  exact vacuumLoopEnergy_nonneg γ

private def identityLift : Sphere3 := sphereOfQuaternion 1 norm_one

private theorem vacuumConjugacyEnergies_nonempty (a : BulkCoefficients) (g : QuaternionGroup 2) :
    (vacuumConjugacyEnergies a g).Nonempty := by
  obtain ⟨E, hE⟩ := vacuumClassEnergies_nonempty a identityLift g
  exact ⟨E, identityLift, g, IsConj.refl g, hE⟩

/-- The loop-energy infimum in the specified conjugacy class, over all bases. -/
def vacuumConjugacyCost (a : BulkCoefficients) (g : QuaternionGroup 2) : ℝ :=
  sInf (vacuumConjugacyEnergies a g)

private theorem splittingWeight_le_conjugacy_energies (a : BulkCoefficients) (g : QuaternionGroup 2)
    {E : ℝ} (hE : E ∈ vacuumConjugacyEnergies a g) :
    kappaStar a * (quaternionSplittingWeight g : ℝ) ≤ E := by
  obtain ⟨v, h, hh, hE⟩ := hE
  rw [← quaternionSplittingWeight_conj hh]
  exact (vacuumClassCost_ge_splittingWeight a v h).trans
    (csInf_le (vacuumClassEnergies_bddBelow a v h) hE)

theorem vacuumConjugacyCost_ge_splittingWeight (a : BulkCoefficients) (g : QuaternionGroup 2) :
    kappaStar a * (quaternionSplittingWeight g : ℝ) ≤ vacuumConjugacyCost a g :=
  le_csInf (vacuumConjugacyEnergies_nonempty a g) (fun _ => splittingWeight_le_conjugacy_energies a g)

theorem vacuumConjugacyCost_one (a : BulkCoefficients) : vacuumConjugacyCost a 1 = 0 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨identityLift, 1, IsConj.refl 1, (vacuumClassEnergies_isLeast_one a identityLift).1⟩, ?_⟩
  intro E hE
  simpa only [quaternionSplittingWeight_one, Nat.cast_zero, mul_zero] using
    splittingWeight_le_conjugacy_energies a 1 hE

theorem vacuumConjugacyCost_light (a : BulkCoefficients) {g : QuaternionGroup 2} (hg : IsLightQuaternion g) :
    vacuumConjugacyCost a g = kappaStar a := by
  apply IsLeast.csInf_eq
  refine ⟨⟨identityLift, g, IsConj.refl g, (vacuumClassEnergies_isLeast_light a identityLift hg).1⟩, ?_⟩
  intro E hE
  simpa only [quaternionSplittingWeight_light hg, Nat.cast_one, mul_one] using
    splittingWeight_le_conjugacy_energies a g hE

theorem vacuumConjugacyCost_antipodal (a : BulkCoefficients) :
    vacuumConjugacyCost a (QuaternionGroup.a 2) = 4 * kappaStar a := by
  apply IsLeast.csInf_eq
  refine ⟨⟨identityLift, _, IsConj.refl _, (vacuumClassEnergies_isLeast_antipodal a identityLift).1⟩, ?_⟩
  rintro E ⟨v, h, hh, hE⟩
  have heq : h = QuaternionGroup.a 2 := (isConj_labels hh).2.2.mpr rfl
  subst h
  exact (vacuumClassEnergies_isLeast_antipodal a v).2 hE

theorem vacuumConjugacyCost_third (a : BulkCoefficients) {g : QuaternionGroup 2}
    (hg : g = QuaternionGroup.xa 1 ∨ g = QuaternionGroup.xa 3) :
    2 * kappaStar a < vacuumConjugacyCost a g ∧ vacuumConjugacyCost a g ≤ 4 * kappaStar a := by
  have hmem : 4 * kappaStar a ∈ vacuumConjugacyEnergies a g :=
    ⟨identityLift, g, IsConj.refl g, exists_vacuumLoop_third_class_competitor a identityLift hg⟩
  have hLower : ∀ E ∈ vacuumConjugacyEnergies a g,
      Real.pi * vacuumRadius a ^ 2 / (2 * (707 / 1000 : ℝ) ^ 2) ≤ E := by
    rintro E ⟨v, h, hh, γ, hc, hsob, rfl⟩
    obtain ⟨h₁, h₂, h₃⟩ := isConj_labels hh
    have hnotOne : h ≠ 1 := by
      intro he
      have hf := h₁.mp he
      rcases hg with rfl | rfl <;> exact (by decide : _ ≠ _) hf
    have hnotLight : ¬ IsLightQuaternion h := by
      intro he
      have hf := h₂.mp he
      rcases hg with rfl | rfl <;> exact (by decide : ¬ IsLightQuaternion _) hf
    have hnotCenter : h ≠ QuaternionGroup.a 2 := by
      intro he
      have hf := h₃.mp he
      rcases hg with rfl | rfl <;> exact (by decide : _ ≠ _) hf
    exact vacuumLoop_energy_ge_third_gap a v γ hsob
      ((quaternion_other_cases hnotOne hnotLight).resolve_left hnotCenter) hc
  exact ⟨(two_kappaStar_lt_third_gap a).trans_le (le_csInf ⟨_, hmem⟩ hLower), csInf_le ⟨_, hLower⟩ hmem⟩

/-- The factorization costs with conjugacy-class energies and prescribed product class. -/
def vacuumConjugacySplittingEnergies (a : BulkCoefficients) (g : QuaternionGroup 2) : Set ℝ :=
  {E | ∃ l : List (QuaternionGroup 2), l ≠ [] ∧ IsConj l.prod g ∧ (l.map (vacuumConjugacyCost a)).sum = E}

theorem vacuumConjugacySplittingEnergies_isLeast (a : BulkCoefficients) (g : QuaternionGroup 2) :
    IsLeast (vacuumConjugacySplittingEnergies a g) (kappaStar a * (quaternionSplittingWeight g : ℝ)) := by
  obtain ⟨l, hn, hp, hE⟩ := exists_shortest_ordered_word a (vacuumConjugacyCost a)
    (vacuumConjugacyCost_one a) (fun _ => vacuumConjugacyCost_light a) g
  refine ⟨⟨l, hn, hp.symm ▸ IsConj.refl l.prod, hE⟩, ?_⟩
  rintro E ⟨m, _, hm, rfl⟩
  rw [← quaternionSplittingWeight_conj hm]
  exact classCosts_list_ge a (vacuumConjugacyCost a) (vacuumConjugacyCost_ge_splittingWeight a) m

theorem vacuumConjugacySplittingCost_eq (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) :
    sInf (vacuumConjugacySplittingEnergies a g) = vacuumSplittingCost a v g := by
  rw [(vacuumConjugacySplittingEnergies_isLeast a g).csInf_eq, vacuumSplittingCost_eq]

end Thesis
