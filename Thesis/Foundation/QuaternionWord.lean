module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.Real.Basic

/-! The index-two character of the ordered quaternion word at a junction. -/

public section

open scoped BigOperators Quaternion

namespace Thesis

private def reduceFour : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

/-- The quotient character is additive modulo two, with `a 1 = i` and
`xa 0 = j`. Since `xa r = j * i^r`, `xa 1 = -k` and `xa 3 = k`. -/
@[expose] def quaternionLightCharacter : QuaternionGroup 2 →* Multiplicative (ZMod 2) where
  toFun
    | .a r => Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) r)
    | .xa r => Multiplicative.ofAdd (1 + ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) r)
  map_one' := by
    change Multiplicative.ofAdd (reduceFour 0) = 1
    rw [map_zero]
    rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · change Multiplicative.ofAdd (reduceFour (i + j)) =
        Multiplicative.ofAdd (reduceFour i) * Multiplicative.ofAdd (reduceFour j)
      rw [map_add, ofAdd_add]
    · change Multiplicative.ofAdd (1 + reduceFour (j - i)) =
        Multiplicative.ofAdd (reduceFour i) * Multiplicative.ofAdd (1 + reduceFour j)
      rw [map_sub, sub_eq_add_neg, ZMod.neg_eq_self_mod_two, ← ofAdd_add]
      congr 1
      ac_rfl
    · change Multiplicative.ofAdd (1 + reduceFour (i + j)) =
        Multiplicative.ofAdd (1 + reduceFour i) * Multiplicative.ofAdd (reduceFour j)
      rw [reduceFour.map_add i j, ← ofAdd_add, add_assoc]
    · change Multiplicative.ofAdd (reduceFour (2 + j - i)) =
        Multiplicative.ofAdd (1 + reduceFour i) * Multiplicative.ofAdd (1 + reduceFour j)
      have h2 : reduceFour 2 = 0 := by decide
      have h12 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [map_sub, map_add, h2, zero_add, sub_eq_add_neg, ZMod.neg_eq_self_mod_two, ← ofAdd_add]
      congr 1
      rw [show (1 : ZMod 2) + reduceFour i + (1 + reduceFour j) =
          (1 + 1) + (reduceFour j + reduceFour i) by ac_rfl, h12, zero_add]

/-- Light quaternion factors are the two conjugacy classes `±i` and `±j`
under the standard ordered-word convention. -/
@[expose] def IsLightQuaternion (g : QuaternionGroup 2) : Prop :=
  g = .a 1 ∨ g = .a 3 ∨ g = .xa 0 ∨ g = .xa 2

instance : DecidablePred IsLightQuaternion := fun g => by
  unfold IsLightQuaternion
  infer_instance

theorem quaternionLightCharacter_eq_indicator (g : QuaternionGroup 2) :
    (quaternionLightCharacter g).toAdd = if IsLightQuaternion g then 1 else 0 := by
  rcases g with ⟨i⟩ | ⟨i⟩ <;> fin_cases i <;> decide

theorem quaternionLightCharacter_eq_zero_iff (g : QuaternionGroup 2) :
    (quaternionLightCharacter g).toAdd = 0 ↔
      g = .a 0 ∨ g = .a 2 ∨ g = .xa 1 ∨ g = .xa 3 := by
  rcases g with ⟨i⟩ | ⟨i⟩ <;> fin_cases i <;> decide

theorem quaternionLightCharacter_surjective : Function.Surjective quaternionLightCharacter := by
  have h (t : ZMod 2) : t = 0 ∨ t = 1 := by
    fin_cases t
    · exact Or.inl rfl
    · exact Or.inr rfl
  intro t
  rcases h t.toAdd with ht | ht
  · refine ⟨1, Multiplicative.toAdd.injective ?_⟩
    rw [map_one]
    exact ht.symm
  · refine ⟨.a 1, Multiplicative.toAdd.injective ?_⟩
    exact (show (quaternionLightCharacter (.a 1)).toAdd = (1 : ZMod 2) by decide).trans ht.symm

/-- The character of the original ordered word is the sum of its
light-factor indicators. -/
theorem quaternionLightCharacter_ordered_product (w : List (QuaternionGroup 2)) :
    (quaternionLightCharacter w.prod).toAdd = (w.map fun g =>
      if IsLightQuaternion g then (1 : ZMod 2) else 0).sum := by
  induction w with
  | nil => simp
  | cons g w ih =>
      simp only [List.prod_cons, map_mul, toAdd_mul, List.map_cons, List.sum_cons,
        ih, quaternionLightCharacter_eq_indicator g]

/-- The light-weight factors are even in number when the original ordered
quaternion word multiplies to one and its factors have the assigned classes. -/
theorem even_light_weights_of_ordered_quaternion_product {q : ℕ} {κ : ℝ}
    (g : Fin q → QuaternionGroup 2) (θ : Fin q → ℝ)
    (hClass : ∀ i, θ i = κ ↔ IsLightQuaternion (g i))
    (hProd : (List.ofFn g).prod = 1) :
    Even ((Finset.univ.filter fun i => θ i = κ).card) := by
  classical
  have h := quaternionLightCharacter_ordered_product (List.ofFn g)
  rw [hProd, map_one, List.map_ofFn, List.sum_ofFn] at h
  change (0 : ZMod 2) = _ at h
  have hSum : (∑ i, if θ i = κ then (1 : ZMod 2) else 0) = 0 := by
    simpa only [Function.comp_apply, ← hClass] using h.symm
  have hCast : (((Finset.univ.filter fun i => θ i = κ).card : ℕ) : ZMod 2) = 0 := by
    rwa [← Finset.sum_filter, Finset.sum_const, nsmul_one] at hSum
  exact ZMod.natCast_eq_zero_iff_even.1 hCast

/-- The quaternion group with the ordered-word convention `a = i`, `x = j`
inside the integral quaternions. The coordinates are `(1, i, j, k)`. -/
@[expose] def quaternionWordInteger : QuaternionGroup 2 →* ℍ[ℤ] where
  toFun
    | .a r => (![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨-1, 0, 0, 0⟩, ⟨0, -1, 0, 0⟩] : Fin 4 → ℍ[ℤ])
      ((ZMod.finEquiv 4).symm r)
    | .xa r => (![⟨0, 0, 1, 0⟩, ⟨0, 0, 0, -1⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 1⟩] : Fin 4 → ℍ[ℤ])
      ((ZMod.finEquiv 4).symm r)
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;>
      simp only [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a,
        QuaternionGroup.xa_mul_xa] <;>
      fin_cases i <;> fin_cases j <;> rfl

private noncomputable def quaternionIntegerCastReal : ℍ[ℤ] →* ℍ[ℝ] where
  toFun q := ⟨q.re, q.imI, q.imJ, q.imK⟩
  map_one' := by
    ext <;> simp only [Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one, Int.cast_one, Int.cast_zero]
  map_mul' p q := by
    ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, Int.cast_add, Int.cast_sub, Int.cast_mul]

/-- The signed coordinate realization of the ordered quaternion word in
the real quaternions. -/
noncomputable def quaternionWordReal : QuaternionGroup 2 →* ℍ[ℝ] :=
  quaternionIntegerCastReal.comp quaternionWordInteger

theorem quaternionWordReal_i : quaternionWordReal (.a 1) = (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) := by
  change (⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ)⟩ : ℍ[ℝ]) = _
  simp only [Int.cast_zero, Int.cast_one]

theorem quaternionWordReal_j : quaternionWordReal (.xa 0) = (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) := by
  change (⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ)⟩ : ℍ[ℝ]) = _
  simp only [Int.cast_zero, Int.cast_one]

theorem quaternionWordReal_k : quaternionWordReal (.xa 3) = (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) := by
  change (⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ)⟩ : ℍ[ℝ]) = _
  simp only [Int.cast_zero, Int.cast_one]

theorem quaternionWordReal_negative_i : quaternionWordReal (.a 3) = (⟨0, -1, 0, 0⟩ : ℍ[ℝ]) := by
  change (⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ)⟩ : ℍ[ℝ]) = _
  simp only [Int.cast_zero, Int.cast_neg, Int.cast_one]

theorem quaternionWordReal_negative_j : quaternionWordReal (.xa 2) = (⟨0, 0, -1, 0⟩ : ℍ[ℝ]) := by
  change (⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ)⟩ : ℍ[ℝ]) = _
  simp only [Int.cast_zero, Int.cast_neg, Int.cast_one]

theorem quaternionWordReal_negative_k : quaternionWordReal (.xa 1) = (⟨0, 0, 0, -1⟩ : ℍ[ℝ]) := by
  change (⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ)⟩ : ℍ[ℝ]) = _
  simp only [Int.cast_zero, Int.cast_neg, Int.cast_one]

theorem quaternionWordReal_negative_one : quaternionWordReal (.a 2) = (-1 : ℍ[ℝ]) := by
  change (⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)⟩ : ℍ[ℝ]) = _
  ext <;> simp [Int.cast_zero, Int.cast_neg, Int.cast_one]

private theorem quaternionWordInteger_normSq (g : QuaternionGroup 2) :
    Quaternion.normSq (quaternionWordInteger g) = 1 := by
  rcases g with ⟨i⟩ | ⟨i⟩ <;> fin_cases i <;> decide

/-- Every value of the quaternion word realization is a unit quaternion. -/
theorem quaternionWordReal_normSq (g : QuaternionGroup 2) : Quaternion.normSq (quaternionWordReal g) = 1 := by
  have h (q : ℍ[ℤ]) : Quaternion.normSq (quaternionIntegerCastReal q) =
      ((Quaternion.normSq q : ℤ) : ℝ) := by
    rw [Quaternion.normSq_def', Quaternion.normSq_def']
    simp only [Int.cast_add, Int.cast_pow]
    rfl
  rw [quaternionWordReal, MonoidHom.comp_apply, h, quaternionWordInteger_normSq, Int.cast_one]

private theorem quaternionWordInteger_injective : Function.Injective quaternionWordInteger := by
  let coords (q : ℍ[ℤ]) : Fin 4 → ℤ := ![q.re, q.imI, q.imJ, q.imK]
  suffices ∀ g h : QuaternionGroup 2, coords (quaternionWordInteger g) = coords (quaternionWordInteger h) →
      g = h from fun g h hEq => this g h (congrArg coords hEq)
  rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> decide

/-- The signed-coordinate realization preserves the distinct group elements. -/
theorem quaternionWordReal_injective : Function.Injective quaternionWordReal := by
  have hCast : Function.Injective quaternionIntegerCastReal := by
    intro p q hEq
    apply QuaternionAlgebra.ext
    · exact Int.cast_inj.1 (congrArg (fun q : ℍ[ℝ] => q.re) hEq)
    · exact Int.cast_inj.1 (congrArg (fun q : ℍ[ℝ] => q.imI) hEq)
    · exact Int.cast_inj.1 (congrArg (fun q : ℍ[ℝ] => q.imJ) hEq)
    · exact Int.cast_inj.1 (congrArg (fun q : ℍ[ℝ] => q.imK) hEq)
  exact hCast.comp quaternionWordInteger_injective

end Thesis

end
