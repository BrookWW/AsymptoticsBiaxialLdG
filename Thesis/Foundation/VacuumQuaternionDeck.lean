module

public import Thesis.Foundation.QuaternionFrameCover
public import Thesis.Foundation.QuaternionWord
public import Thesis.Foundation.VacuumFrameCover

/-! The action by right multiplication on the quaternion sphere over the vacuum. -/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContDiff Matrix.Norms.Frobenius Quaternion

namespace Thesis

/-- The vacuum-valued form of the original sphere map. -/
def vacuumQuaternionProjection (a : BulkCoefficients) (v : Sphere3) : vacuum a :=
  vacuumFrameProjection a (quaternionFrame v)

theorem vacuumQuaternionProjection_val (a : BulkCoefficients) (v : Sphere3) :
    (vacuumQuaternionProjection a v).val = cover a v :=
  (cover_eq_quaternionFrameProjection a v).symm

theorem vacuumQuaternionProjection_surjective (a : BulkCoefficients) :
    Function.Surjective (vacuumQuaternionProjection a) :=
  (vacuumFrameProjection_surjective a).comp quaternionFrame_surjective

theorem norm_quaternionWordReal (g : QuaternionGroup 2) : ‖quaternionWordReal g‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1
  rw [pow_two ‖quaternionWordReal g‖, ← Quaternion.normSq_eq_norm_mul_self, quaternionWordReal_normSq,
    one_pow]

/-- The left action is right multiplication by the inverse, preserving
the order of group composition. -/
instance quaternionWordSphereAction : MulAction (QuaternionGroup 2) Sphere3 where
  smul g v := sphereOfQuaternion
    (Quaternion.linearIsometryEquivTuple.symm v.val * quaternionWordReal g⁻¹)
    (by rw [norm_mul, quaternionTuple_symm_norm_eq_one, norm_quaternionWordReal, mul_one])
  one_smul v := by
    apply Subtype.ext
    change Quaternion.linearIsometryEquivTuple
      (Quaternion.linearIsometryEquivTuple.symm v.val * quaternionWordReal (1 : QuaternionGroup 2)⁻¹) = v.val
    simp only [inv_one, map_one, mul_one, LinearIsometryEquiv.apply_symm_apply]
  mul_smul g h v := by
    apply Subtype.ext
    change Quaternion.linearIsometryEquivTuple
      (Quaternion.linearIsometryEquivTuple.symm v.val * quaternionWordReal (g * h)⁻¹) =
      Quaternion.linearIsometryEquivTuple (Quaternion.linearIsometryEquivTuple.symm
        (Quaternion.linearIsometryEquivTuple (Quaternion.linearIsometryEquivTuple.symm v.val *
          quaternionWordReal h⁻¹)) * quaternionWordReal g⁻¹)
    simp only [LinearIsometryEquiv.symm_apply_apply, mul_inv_rev, map_mul, mul_assoc]

theorem quaternionSphereAction_val (g : QuaternionGroup 2) (v : Sphere3) :
    (g • v).val = Quaternion.linearIsometryEquivTuple
      (Quaternion.linearIsometryEquivTuple.symm v.val * quaternionWordReal g⁻¹) := rfl

theorem quaternionTuple_symm_smul (g : QuaternionGroup 2) (v : Sphere3) :
    Quaternion.linearIsometryEquivTuple.symm (g • v).val =
      Quaternion.linearIsometryEquivTuple.symm v.val * quaternionWordReal g⁻¹ := by
  rw [quaternionSphereAction_val, LinearIsometryEquiv.symm_apply_apply]

instance quaternionWordSphereContinuous : ContinuousConstSMul (QuaternionGroup 2) Sphere3 where
  continuous_const_smul g := by
    apply Continuous.subtype_mk
    exact Quaternion.linearIsometryEquivTuple.continuous.comp
      ((Quaternion.linearIsometryEquivTuple.symm.continuous.comp continuous_subtype_val).mul continuous_const)

instance quaternionWordSphereFree : IsCancelSMul (QuaternionGroup 2) Sphere3 where
  right_cancel' g h v hEq := by
    have hq : Quaternion.linearIsometryEquivTuple.symm v.val ≠ 0 := by
      intro hz
      have hn := quaternionTuple_symm_norm_eq_one v
      rw [hz, norm_zero] at hn
      exact zero_ne_one hn
    have hMul := congrArg (fun u : Sphere3 => Quaternion.linearIsometryEquivTuple.symm u.val) hEq
    simp only [quaternionTuple_symm_smul] at hMul
    exact inv_injective (quaternionWordReal_injective (mul_left_cancel₀ hq hMul))

theorem contDiff_quaternionSphereAction_ambient (g : QuaternionGroup 2) :
    ContDiff ℝ ∞ (fun v : QuaternionCoordinates => Quaternion.linearIsometryEquivTuple
      (Quaternion.linearIsometryEquivTuple.symm v * quaternionWordReal g⁻¹)) :=
  Quaternion.linearIsometryEquivTuple.toContinuousLinearEquiv.contDiff.comp
    (Quaternion.linearIsometryEquivTuple.symm.toContinuousLinearEquiv.contDiff.mul contDiff_const)

/-- Right multiplication by `i` in the frozen order of the four real coordinates. -/
theorem quaternionSphereAction_right_i_coordinates (v : Sphere3) :
    ((QuaternionGroup.a 1 : QuaternionGroup 2)⁻¹ • v).val =
      WithLp.toLp 2 ![-v.val 1, v.val 0, v.val 3, -v.val 2] := by
  apply Quaternion.linearIsometryEquivTuple.symm.injective
  rw [quaternionTuple_symm_smul, inv_inv, quaternionWordReal_i]
  change (⟨v.val 0, v.val 1, v.val 2, v.val 3⟩ : ℍ) * ⟨0, 1, 0, 0⟩ =
    ⟨-v.val 1, v.val 0, v.val 3, -v.val 2⟩
  ext <;> simp

private theorem pureQuaternion_smul (s : ℝ) (x : Point) : pureQuaternion (s • x) = s • pureQuaternion x := by
  ext <;> simp [pureQuaternion]

private theorem quaternionConjugate_smul (s : ℝ) (q z : ℍ) :
    quaternionConjugate q (s • z) = s • quaternionConjugate q z := by
  simp only [quaternionConjugate, mul_smul_comm, smul_mul_assoc]

private theorem firstQuaternionUnit_conjugations :
    quaternionConjugate firstQuaternionUnit firstQuaternionUnit = firstQuaternionUnit ∧
    quaternionConjugate firstQuaternionUnit secondQuaternionUnit = (-1 : ℝ) • secondQuaternionUnit := by
  constructor <;> ext <;> norm_num [quaternionConjugate, firstQuaternionUnit, secondQuaternionUnit]

private theorem secondQuaternionUnit_conjugations :
    quaternionConjugate secondQuaternionUnit firstQuaternionUnit = (-1 : ℝ) • firstQuaternionUnit ∧
    quaternionConjugate secondQuaternionUnit secondQuaternionUnit = secondQuaternionUnit := by
  constructor <;> ext <;> norm_num [quaternionConjugate, firstQuaternionUnit, secondQuaternionUnit]

private theorem quaternionSphereAction_firstFrame_of_conjugate (g : QuaternionGroup 2) (v : Sphere3)
    (s : ℝ) (h : quaternionConjugate (quaternionWordReal g⁻¹) firstQuaternionUnit = s • firstQuaternionUnit) :
    firstFrameVector (g • v).val = s • firstFrameVector v.val := by
  apply pureQuaternion_injective
  rw [pureQuaternion_smul, firstFrameVector_pureQuaternion, firstFrameVector_pureQuaternion,
    quaternionTuple_symm_smul, quaternionConjugate_comp, h, quaternionConjugate_smul]

private theorem quaternionSphereAction_secondFrame_of_conjugate (g : QuaternionGroup 2) (v : Sphere3)
    (s : ℝ) (h : quaternionConjugate (quaternionWordReal g⁻¹) secondQuaternionUnit = s • secondQuaternionUnit) :
    secondFrameVector (g • v).val = s • secondFrameVector v.val := by
  apply pureQuaternion_injective
  rw [pureQuaternion_smul, secondFrameVector_pureQuaternion, secondFrameVector_pureQuaternion,
    quaternionTuple_symm_smul, quaternionConjugate_comp, h, quaternionConjugate_smul]

theorem quaternionSphereAction_right_i_signs (v : Sphere3) :
    let w := (QuaternionGroup.a 1 : QuaternionGroup 2)⁻¹ • v
    firstFrameVector w.val = firstFrameVector v.val ∧ secondFrameVector w.val = -secondFrameVector v.val := by
  constructor
  · rw [← one_smul ℝ (firstFrameVector v.val)]
    exact quaternionSphereAction_firstFrame_of_conjugate _ _ 1 (by
      rw [inv_inv, quaternionWordReal_i, one_smul]
      exact firstQuaternionUnit_conjugations.1)
  · rw [← neg_one_smul ℝ (secondFrameVector v.val)]
    exact quaternionSphereAction_secondFrame_of_conjugate _ _ (-1) (by
      rw [inv_inv, quaternionWordReal_i]
      exact firstQuaternionUnit_conjugations.2)

theorem quaternionSphereAction_right_j_signs (v : Sphere3) :
    let w := (QuaternionGroup.xa 0 : QuaternionGroup 2)⁻¹ • v
    firstFrameVector w.val = -firstFrameVector v.val ∧ secondFrameVector w.val = secondFrameVector v.val := by
  constructor
  · rw [← neg_one_smul ℝ (firstFrameVector v.val)]
    exact quaternionSphereAction_firstFrame_of_conjugate _ _ (-1) (by
      rw [inv_inv, quaternionWordReal_j]
      exact secondQuaternionUnit_conjugations.1)
  · rw [← one_smul ℝ (secondFrameVector v.val)]
    exact quaternionSphereAction_secondFrame_of_conjugate _ _ 1 (by
      rw [inv_inv, quaternionWordReal_j, one_smul]
      exact secondQuaternionUnit_conjugations.2)

theorem quaternionSphereAction_right_k_signs (v : Sphere3) :
    let w := (QuaternionGroup.xa 3 : QuaternionGroup 2)⁻¹ • v
    firstFrameVector w.val = -firstFrameVector v.val ∧ secondFrameVector w.val = -secondFrameVector v.val := by
  have hIJ : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 = QuaternionGroup.xa 3 := by decide
  dsimp only
  rw [← hIJ, mul_inv_rev, mul_smul]
  obtain ⟨hi₁, hi₂⟩ := quaternionSphereAction_right_i_signs v
  obtain ⟨hj₁, hj₂⟩ := quaternionSphereAction_right_j_signs ((QuaternionGroup.a 1 : QuaternionGroup 2)⁻¹ • v)
  exact ⟨hj₁.trans (congrArg Neg.neg hi₁), hj₂.trans hi₂⟩

theorem quaternionSphereAction_minusOne_val (v : Sphere3) :
    ((QuaternionGroup.a 2 : QuaternionGroup 2) • v).val = -v.val := by
  have h : (QuaternionGroup.a 2 : QuaternionGroup 2)⁻¹ = QuaternionGroup.a 2 := by decide
  rw [quaternionSphereAction_val, h, quaternionWordReal_negative_one, mul_neg, mul_one,
    map_neg, LinearIsometryEquiv.apply_symm_apply]

private theorem vacuumQuaternionProjection_eq_of_frame_signs (a : BulkCoefficients) {v w : Sphere3}
    (h₁ : firstFrameVector v.val = firstFrameVector w.val ∨ firstFrameVector v.val = -firstFrameVector w.val)
    (h₂ : secondFrameVector v.val = secondFrameVector w.val ∨ secondFrameVector v.val = -secondFrameVector w.val) :
    vacuumQuaternionProjection a v = vacuumQuaternionProjection a w :=
  (vacuumFrameProjection_eq_iff_signs a (quaternionFrame v) (quaternionFrame w)).2 ⟨h₁, h₂⟩

/-- Right multiplication by a quaternion word element preserves the exact
vacuum tensor, with the two director signs as above. -/
theorem vacuumQuaternionProjection_smul (a : BulkCoefficients) (g : QuaternionGroup 2) (v : Sphere3) :
    vacuumQuaternionProjection a (g • v) = vacuumQuaternionProjection a v := by
  have hI (w : Sphere3) : vacuumQuaternionProjection a ((QuaternionGroup.a 1 : QuaternionGroup 2) • w) =
      vacuumQuaternionProjection a w := by
    obtain ⟨h₁, h₂⟩ := quaternionSphereAction_right_i_signs ((QuaternionGroup.a 1 : QuaternionGroup 2) • w)
    have h := vacuumQuaternionProjection_eq_of_frame_signs a (Or.inl h₁) (Or.inr h₂)
    simpa only [inv_smul_smul] using h.symm
  have hJ (w : Sphere3) : vacuumQuaternionProjection a ((QuaternionGroup.xa 0 : QuaternionGroup 2) • w) =
      vacuumQuaternionProjection a w := by
    obtain ⟨h₁, h₂⟩ := quaternionSphereAction_right_j_signs ((QuaternionGroup.xa 0 : QuaternionGroup 2) • w)
    have h := vacuumQuaternionProjection_eq_of_frame_signs a (Or.inr h₁) (Or.inl h₂)
    simpa only [inv_smul_smul] using h.symm
  have hPow (k : ℕ) (w : Sphere3) :
      vacuumQuaternionProjection a (((QuaternionGroup.a 1 : QuaternionGroup 2) ^ k) • w) =
        vacuumQuaternionProjection a w := by
    induction k with
    | zero => rw [pow_zero, one_smul]
    | succ k hk => rw [pow_succ', mul_smul, hI, hk]
  have hA (r : ZMod (2 * 2)) (w : Sphere3) :
      vacuumQuaternionProjection a ((QuaternionGroup.a r : QuaternionGroup 2) • w) =
        vacuumQuaternionProjection a w := by
    simpa only [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val] using hPow r.val w
  rcases g with ⟨r⟩ | ⟨r⟩
  · exact hA r v
  · have hXa : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a r = QuaternionGroup.xa r := by
      rw [QuaternionGroup.xa_mul_a, zero_add]
    rw [← hXa, mul_smul, hJ, hA]

private theorem quaternionFrame_eq_of_columns {v w : Sphere3}
    (h₁ : firstFrameVector v.val = firstFrameVector w.val)
    (h₂ : secondFrameVector v.val = secondFrameVector w.val) : quaternionFrame v = quaternionFrame w :=
  Subtype.ext (Prod.ext h₁ h₂)

private theorem exists_smul_quaternionFrame_eq_of_vacuumProjection_eq (a : BulkCoefficients)
    {v w : Sphere3} (h : vacuumQuaternionProjection a v = vacuumQuaternionProjection a w) :
    ∃ g : QuaternionGroup 2, quaternionFrame v = quaternionFrame (g • w) := by
  obtain ⟨h₁, h₂⟩ := (vacuumFrameProjection_eq_iff_signs a (quaternionFrame v) (quaternionFrame w)).1 h
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · refine ⟨1, ?_⟩
    rw [one_smul]
    exact quaternionFrame_eq_of_columns h₁ h₂
  · obtain ⟨hi₁, hi₂⟩ := quaternionSphereAction_right_i_signs w
    exact ⟨(QuaternionGroup.a 1)⁻¹,
      quaternionFrame_eq_of_columns (h₁.trans hi₁.symm) (h₂.trans hi₂.symm)⟩
  · obtain ⟨hj₁, hj₂⟩ := quaternionSphereAction_right_j_signs w
    exact ⟨(QuaternionGroup.xa 0)⁻¹,
      quaternionFrame_eq_of_columns (h₁.trans hj₁.symm) (h₂.trans hj₂.symm)⟩
  · obtain ⟨hk₁, hk₂⟩ := quaternionSphereAction_right_k_signs w
    exact ⟨(QuaternionGroup.xa 3)⁻¹,
      quaternionFrame_eq_of_columns (h₁.trans hk₁.symm) (h₂.trans hk₂.symm)⟩

/-- The two antipodal lifts of each of the four possible signed frames are
exactly the orbit under the action by the eight quaternion elements. -/
theorem vacuumQuaternionProjection_eq_iff_orbit (a : BulkCoefficients) {v w : Sphere3} :
    vacuumQuaternionProjection a v = vacuumQuaternionProjection a w ↔
      v ∈ MulAction.orbit (QuaternionGroup 2) w := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := exists_smul_quaternionFrame_eq_of_vacuumProjection_eq a h
    rcases (quaternionFrame_eq_iff_antipodal v (g • w)).1 hg with he | he
    · exact ⟨g, he.symm⟩
    · refine ⟨(QuaternionGroup.a 2 : QuaternionGroup 2) * g, Subtype.ext ?_⟩
      change (((QuaternionGroup.a 2 : QuaternionGroup 2) * g) • w).val = v.val
      rw [mul_smul, quaternionSphereAction_minusOne_val]
      exact he.symm
  · rintro ⟨g, rfl⟩
    exact vacuumQuaternionProjection_smul a g w

theorem continuous_vacuumQuaternionProjection (a : BulkCoefficients) :
    Continuous (vacuumQuaternionProjection a) :=
  (continuous_vacuumFrameProjection a).comp continuous_quaternionFrame

/-- The original vacuum map is the quotient covering for the free finite
action of right multiplication by inverses of quaternion words. -/
theorem vacuumQuaternionProjection_isQuotientCoveringMap (a : BulkCoefficients) :
    IsQuotientCoveringMap (vacuumQuaternionProjection a) (QuaternionGroup 2) := by
  letI : CompactSpace Sphere3 := isCompact_iff_compactSpace.1 (isCompact_sphere _ _)
  have hCont := continuous_vacuumQuaternionProjection a
  have hQuot : IsQuotientMap (vacuumQuaternionProjection a) :=
    hCont.isClosedMap.isQuotientMap hCont (vacuumQuaternionProjection_surjective a)
  exact hQuot.isQuotientCoveringMap_of_properlyDiscontinuousSMul (vacuumQuaternionProjection_eq_iff_orbit a)

theorem vacuumQuaternionProjection_isCoveringMap (a : BulkCoefficients) :
    IsCoveringMap (vacuumQuaternionProjection a) :=
  (vacuumQuaternionProjection_isQuotientCoveringMap a).isCoveringMap

theorem vacuumQuaternionProjection_card_fiber (a : BulkCoefficients) (A : vacuum a) :
    Nat.card ((vacuumQuaternionProjection a) ⁻¹' {A}) = 8 := by
  obtain ⟨v, hv⟩ := vacuumQuaternionProjection_surjective a A
  have h := (vacuumQuaternionProjection_isQuotientCoveringMap a).fiberEquivGroup
    (⟨v, hv⟩ : (vacuumQuaternionProjection a) ⁻¹' {A})
  rw [Nat.card_congr h, Nat.card_eq_fintype_card, QuaternionGroup.card]

end Thesis

end
