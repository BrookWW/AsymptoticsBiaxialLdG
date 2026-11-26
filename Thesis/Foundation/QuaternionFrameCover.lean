module

public import Thesis.Foundation.QuaternionFrameLift
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Thesis.Foundation.VacuumFrameCover

/-! The two sheets of the actual quaternion map to ordered frames. -/

@[expose] public section

noncomputable section

open Set Topology
open scoped Quaternion Matrix.Norms.Frobenius

namespace Thesis

private theorem quaternionConjugate_neg (q x : ℍ) :
    quaternionConjugate (-q) x = quaternionConjugate q x := by
  simp only [quaternionConjugate, star_neg, neg_mul, mul_neg, neg_neg]

private theorem commutes_of_quaternionConjugate_eq {q p x : ℍ}
    (hq : ‖q‖ = 1) (hp : ‖p‖ = 1) (h : quaternionConjugate q x = quaternionConjugate p x) :
    (star p * q) * x = x * (star p * q) := by
  have hL : star p * quaternionConjugate q x * q = (star p * q) * x := calc
    _ = ((star p * q) * x) * (star q * q) := by simp only [quaternionConjugate, mul_assoc]
    _ = _ := by rw [quaternionUnit_star_mul hq, mul_one]
  have hR : star p * quaternionConjugate p x * q = x * (star p * q) := calc
    _ = ((star p * p) * x) * (star p * q) := by simp only [quaternionConjugate, mul_assoc]
    _ = _ := by rw [quaternionUnit_star_mul hp, one_mul]
  exact hL.symm.trans ((congrArg (fun z => star p * z * q) h).trans hR)

private theorem quaternion_eq_coe_re_of_commutes_units (q : ℍ)
    (hi : q * firstQuaternionUnit = firstQuaternionUnit * q)
    (hj : q * secondQuaternionUnit = secondQuaternionUnit * q) : q = q.re := by
  have hiJ := congrArg (fun z : ℍ => z.imJ) hi
  have hiK := congrArg (fun z : ℍ => z.imK) hi
  have hjK := congrArg (fun z : ℍ => z.imK) hj
  simp [firstQuaternionUnit] at hiJ hiK
  simp [secondQuaternionUnit] at hjK
  have hI : q.imI = 0 := by linarith only [hjK]
  have hJ : q.imJ = 0 := by linarith only [hiK]
  have hK : q.imK = 0 := by linarith only [hiJ]
  ext <;> simp only [Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe, hI, hJ, hK]

private theorem unit_quaternion_eq_or_neg_of_conjugations {q p : ℍ} (hq : ‖q‖ = 1) (hp : ‖p‖ = 1)
    (hi : quaternionConjugate q firstQuaternionUnit = quaternionConjugate p firstQuaternionUnit)
    (hj : quaternionConjugate q secondQuaternionUnit = quaternionConjugate p secondQuaternionUnit) :
    q = p ∨ q = -p := by
  let z := star p * q
  have hz : ‖z‖ = 1 := by rw [show z = star p * q from rfl, norm_mul, Quaternion.norm_star, hp, hq, one_mul]
  have he := quaternion_eq_coe_re_of_commutes_units z
    (commutes_of_quaternionConjugate_eq hq hp hi) (commutes_of_quaternionConjugate_eq hq hp hj)
  have ha : |z.re| = 1 := by
    rwa [he, Quaternion.norm_coe, Real.norm_eq_abs] at hz
  rcases abs_choice z.re with hp' | hn'
  · left
    have heq : z = 1 := by rw [he, ← hp', ha]; rfl
    have h := congrArg (p * ·) heq
    simpa only [z, ← mul_assoc, quaternionUnit_mul_star hp, one_mul, mul_one] using h
  · right
    have hr : z.re = -1 := by linarith only [ha, hn']
    have heq : z = -1 := by rw [he, hr, Quaternion.coe_neg, Quaternion.coe_one]
    have h := congrArg (p * ·) heq
    simpa only [z, ← mul_assoc, quaternionUnit_mul_star hp, one_mul, mul_neg, mul_one] using h

/-- The actual polynomial frame map has precisely antipodal fibers. -/
theorem quaternionFrame_eq_iff_antipodal (v w : Sphere3) :
    quaternionFrame v = quaternionFrame w ↔ v = w ∨ v.val = -w.val := by
  let q := Quaternion.linearIsometryEquivTuple.symm v.val
  let p := Quaternion.linearIsometryEquivTuple.symm w.val
  constructor
  · intro h
    have h₁ := congrArg (fun f : VacuumFrame => pureQuaternion f.val.1) h
    have h₂ := congrArg (fun f : VacuumFrame => pureQuaternion f.val.2) h
    change pureQuaternion (firstFrameVector v) = pureQuaternion (firstFrameVector w) at h₁
    change pureQuaternion (secondFrameVector v) = pureQuaternion (secondFrameVector w) at h₂
    rw [firstFrameVector_pureQuaternion, firstFrameVector_pureQuaternion] at h₁
    rw [secondFrameVector_pureQuaternion, secondFrameVector_pureQuaternion] at h₂
    rcases unit_quaternion_eq_or_neg_of_conjugations (quaternionTuple_symm_norm_eq_one v)
      (quaternionTuple_symm_norm_eq_one w) h₁ h₂ with he | he
    · exact Or.inl (Subtype.ext (Quaternion.linearIsometryEquivTuple.symm.injective he))
    · right
      apply Quaternion.linearIsometryEquivTuple.symm.injective
      rw [map_neg]
      exact he
  · rintro (rfl | h)
    · rfl
    · have hqp : q = -p := by
        dsimp only [q, p]
        rw [h, map_neg]
      apply Subtype.ext
      apply Prod.ext
      · change firstFrameVector v = firstFrameVector w
        apply pureQuaternion_injective
        rw [firstFrameVector_pureQuaternion, firstFrameVector_pureQuaternion]
        change quaternionConjugate q _ = quaternionConjugate p _
        rw [hqp, quaternionConjugate_neg]
      · change secondFrameVector v = secondFrameVector w
        apply pureQuaternion_injective
        rw [secondFrameVector_pureQuaternion, secondFrameVector_pureQuaternion]
        change quaternionConjugate q _ = quaternionConjugate p _
        rw [hqp, quaternionConjugate_neg]

private theorem continuous_quaternionImaginaryVector : Continuous quaternionImaginaryVector := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact Quaternion.continuous_imI
  · exact Quaternion.continuous_imJ
  · exact Quaternion.continuous_imK

theorem continuous_quaternionFrame : Continuous quaternionFrame := by
  apply Continuous.subtype_mk
  have h (x : ℍ) : Continuous (fun v : Sphere3 => quaternionImaginaryVector
      (quaternionConjugate (Quaternion.linearIsometryEquivTuple.symm v.val) x)) := by
    apply continuous_quaternionImaginaryVector.comp
    have hv : Continuous (fun v : Sphere3 => Quaternion.linearIsometryEquivTuple.symm v.val) :=
      Quaternion.linearIsometryEquivTuple.symm.continuous.comp continuous_subtype_val
    exact (hv.mul continuous_const).mul hv.star
  have h₁ : (fun v : Sphere3 => firstFrameVector v) = fun v => quaternionImaginaryVector
      (quaternionConjugate (Quaternion.linearIsometryEquivTuple.symm v.val) firstQuaternionUnit) := by
    funext v
    rw [← firstFrameVector_pureQuaternion, quaternionImaginaryVector_pureQuaternion]
  have h₂ : (fun v : Sphere3 => secondFrameVector v) = fun v => quaternionImaginaryVector
      (quaternionConjugate (Quaternion.linearIsometryEquivTuple.symm v.val) secondQuaternionUnit) := by
    funext v
    rw [← secondFrameVector_pureQuaternion, quaternionImaginaryVector_pureQuaternion]
  exact (h₁.symm ▸ h firstQuaternionUnit).prodMk (h₂.symm ▸ h secondQuaternionUnit)

private theorem norm_sphere3_value (v : Sphere3) : ‖v.val‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using v.property

instance sphere3SignAction : MulAction ℤˣ Sphere3 where
  smul g v := ⟨directorSign g • v.val, by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, norm_directorSign,
      norm_sphere3_value, mul_one]⟩
  one_smul v := Subtype.ext (show directorSign 1 • v.val = v.val from by simp [directorSign])
  mul_smul g h v := Subtype.ext (show directorSign (g * h) • v.val =
    directorSign g • (directorSign h • v.val) from by
      simp only [directorSign, Units.val_mul, Int.cast_mul, smul_smul])

instance sphere3ContinuousSign : ContinuousConstSMul ℤˣ Sphere3 where
  continuous_const_smul g :=
    (continuous_subtype_val.const_smul (directorSign g)).subtype_mk _

instance sphere3FreeSign : IsCancelSMul ℤˣ Sphere3 where
  right_cancel' g h v he := by
    have hv : v.val ≠ 0 := by
      intro h0
      have hNorm := norm_sphere3_value v
      rw [h0, norm_zero] at hNorm
      exact zero_ne_one hNorm
    have heq : directorSign g • v.val = directorSign h • v.val := congrArg Subtype.val he
    exact directorSign_injective (smul_left_injective ℝ hv heq)

theorem quaternionFrame_eq_iff_orbit {v w : Sphere3} :
    quaternionFrame v = quaternionFrame w ↔ v ∈ MulAction.orbit ℤˣ w := by
  constructor
  · intro h
    have hs : v.val = w.val ∨ v.val = -w.val := by
      rcases (quaternionFrame_eq_iff_antipodal v w).1 h with rfl | h'
      · exact Or.inl rfl
      · exact Or.inr h'
    obtain ⟨g, hg⟩ := exists_directorSign_smul_of_sign hs
    exact ⟨g, Subtype.ext hg⟩
  · rintro ⟨g, rfl⟩
    apply (quaternionFrame_eq_iff_antipodal _ _).2
    rcases directorSign_smul_eq_or_neg g w.val with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr he

/-- The two polynomial frame columns give the quotient covering by antipodal signs. -/
theorem quaternionFrame_isQuotientCoveringMap : IsQuotientCoveringMap quaternionFrame ℤˣ := by
  have hq : IsQuotientMap quaternionFrame := continuous_quaternionFrame.isClosedMap.isQuotientMap
    continuous_quaternionFrame quaternionFrame_surjective
  exact hq.isQuotientCoveringMap_of_properlyDiscontinuousSMul quaternionFrame_eq_iff_orbit

theorem quaternionFrame_isCoveringMap : IsCoveringMap quaternionFrame :=
  quaternionFrame_isQuotientCoveringMap.isCoveringMap

theorem quaternionFrame_card_fiber (f : VacuumFrame) : Nat.card (quaternionFrame ⁻¹' {f}) = 2 := by
  obtain ⟨v, hv⟩ := quaternionFrame_surjective f
  have he := quaternionFrame_isQuotientCoveringMap.fiberEquivGroup (⟨v, hv⟩ : quaternionFrame ⁻¹' {f})
  rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_units_int]

end Thesis
