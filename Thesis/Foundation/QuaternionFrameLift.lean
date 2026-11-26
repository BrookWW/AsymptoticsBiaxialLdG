module

public import Thesis.Foundation.QuaternionFrame
import Mathlib.Analysis.Normed.Module.Normalize

/-! Lifting each actual ordered orthonormal pair to the unit quaternion sphere. -/

@[expose] public section

noncomputable section

open scoped Quaternion Matrix.Norms.Frobenius

namespace Thesis

private theorem conjugate_eq_of_intertwine {q x y : ℍ} (hq : ‖q‖ = 1) (h : q * x = y * q) :
    quaternionConjugate q x = y := by
  rw [quaternionConjugate, h, mul_assoc, quaternionUnit_mul_star hq, mul_one]

private theorem one_sub_mul_ne_zero {x y : ℍ} (hx : x * x = -1) (hy : y ≠ -x) : 1 - y * x ≠ 0 := by
  intro h
  have hMul : y * x = 1 := (sub_eq_zero.mp h).symm
  have hVec := congrArg (· * x) hMul
  rw [mul_assoc, hx, mul_neg, mul_one, one_mul] at hVec
  exact hy (neg_eq_iff_eq_neg.mp hVec)

private theorem one_sub_mul_intertwines {x y : ℍ} (hx : x * x = -1) (hy : y * y = -1) :
    (1 - y * x) * x = y * (1 - y * x) := by
  calc
    _ = x + y := by rw [sub_mul, one_mul, mul_assoc y x x, hx, mul_neg, mul_one, sub_neg_eq_add]
    _ = y + x := add_comm _ _
    _ = _ := by rw [mul_sub, mul_one, ← mul_assoc y y x, hy, neg_mul, one_mul, sub_neg_eq_add]

private theorem normalize_intertwines {q x y : ℍ} (h : q * x = y * q) :
    NormedSpace.normalize q * x = y * NormedSpace.normalize q := by
  rw [NormedSpace.normalize, smul_mul_assoc, mul_smul_comm, h]

private theorem exists_unitQuaternion_conjugate_of_squares {x y z : ℍ}
    (hx : x * x = -1) (hy : y * y = -1) (hz : ‖z‖ = 1) (hAnti : z * x = -(x * z)) :
    ∃ q : ℍ, ‖q‖ = 1 ∧ quaternionConjugate q x = y := by
  by_cases he : y = -x
  · refine ⟨z, hz, conjugate_eq_of_intertwine hz ?_⟩
    rw [he, neg_mul]
    exact hAnti
  · let q := NormedSpace.normalize (1 - y * x)
    have hq : ‖q‖ = 1 := NormedSpace.norm_normalize (one_sub_mul_ne_zero hx he)
    exact ⟨q, hq, conjugate_eq_of_intertwine hq (normalize_intertwines (one_sub_mul_intertwines hx hy))⟩

private theorem exists_unitQuaternion_fixingAxis {x y z : ℍ}
    (hx : x * x = -1) (hy : y * y = -1) (hz : ‖z‖ = 1)
    (hX : z * x = -(x * z)) (hY : z * y = -(y * z)) :
    ∃ q : ℍ, ‖q‖ = 1 ∧ quaternionConjugate q x = y ∧ quaternionConjugate q z = z := by
  by_cases he : y = -x
  · refine ⟨z, hz, conjugate_eq_of_intertwine hz ?_, conjugate_eq_of_intertwine hz rfl⟩
    rw [he, neg_mul]
    exact hX
  · let q := NormedSpace.normalize (1 - y * x)
    have hq : ‖q‖ = 1 := NormedSpace.norm_normalize (one_sub_mul_ne_zero hx he)
    have hZX : z * (y * x) = (y * x) * z := calc
      _ = (z * y) * x := (mul_assoc _ _ _).symm
      _ = -(y * (z * x)) := by rw [hY, neg_mul, mul_assoc]
      _ = _ := by rw [hX, mul_neg, neg_neg, mul_assoc]
    have hZ : (1 - y * x) * z = z * (1 - y * x) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, hZX]
    exact ⟨q, hq, conjugate_eq_of_intertwine hq (normalize_intertwines (one_sub_mul_intertwines hx hy)),
      conjugate_eq_of_intertwine hq (normalize_intertwines hZ)⟩

/-- The actual point of the unit three-sphere obtained from a unit quaternion. -/
def sphereOfQuaternion (q : ℍ) (hq : ‖q‖ = 1) : Sphere3 :=
  ⟨Quaternion.linearIsometryEquivTuple q, by
    simp only [Sphere3, Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map, hq]⟩

theorem quaternion_of_sphereOfQuaternion (q : ℍ) (hq : ‖q‖ = 1) :
    Quaternion.linearIsometryEquivTuple.symm ((sphereOfQuaternion q hq : Sphere3) : QuaternionCoordinates) = q :=
  Quaternion.linearIsometryEquivTuple.symm_apply_apply q

private theorem exists_unitQuaternion_frame (f : VacuumFrame) :
    ∃ q : ℍ, ‖q‖ = 1 ∧
      quaternionConjugate q firstQuaternionUnit = pureQuaternion f.val.1 ∧
      quaternionConjugate q secondQuaternionUnit = pureQuaternion f.val.2 := by
  let n := f.val.1
  let m := f.val.2
  have hi : firstQuaternionUnit * firstQuaternionUnit = -1 :=
    imaginaryUnit_square rfl norm_firstQuaternionUnit
  have hn : ‖pureQuaternion n‖ = 1 := (norm_pureQuaternion n).trans f.property.1
  have hn₂ : pureQuaternion n * pureQuaternion n = -1 := imaginaryUnit_square rfl hn
  have hji : secondQuaternionUnit * firstQuaternionUnit = -(firstQuaternionUnit * secondQuaternionUnit) := by
    ext <;> norm_num [firstQuaternionUnit, secondQuaternionUnit]
  obtain ⟨p, hp, hpN⟩ := exists_unitQuaternion_conjugate_of_squares hi hn₂ norm_secondQuaternionUnit hji
  let v := sphereOfQuaternion p hp
  let m₀ := secondFrameVector v
  have hN : firstFrameVector v = n := by
    apply pureQuaternion_injective
    rw [firstFrameVector_pureQuaternion, quaternion_of_sphereOfQuaternion]
    exact hpN
  have hM : quaternionConjugate p secondQuaternionUnit = pureQuaternion m₀ := by
    dsimp only [m₀]
    rw [secondFrameVector_pureQuaternion, quaternion_of_sphereOfQuaternion]
  have hm₀ : ‖pureQuaternion m₀‖ = 1 := (norm_pureQuaternion m₀).trans (quaternionFrame v).property.2.1
  have hm : ‖pureQuaternion m‖ = 1 := (norm_pureQuaternion m).trans f.property.2.1
  have hm₀₂ : pureQuaternion m₀ * pureQuaternion m₀ = -1 := imaginaryUnit_square rfl hm₀
  have hm₂ : pureQuaternion m * pureQuaternion m = -1 := imaginaryUnit_square rfl hm
  have hn₀ : inner ℝ n m₀ = 0 := by
    rw [← hN]
    exact (quaternionFrame v).property.2.2
  obtain ⟨r, hr, hrM, hrN⟩ := exists_unitQuaternion_fixingAxis hm₀₂ hm₂ hn
    (pureQuaternion_anticommute_of_inner_eq_zero hn₀)
    (pureQuaternion_anticommute_of_inner_eq_zero f.property.2.2)
  refine ⟨r * p, by rw [norm_mul, hr, hp, mul_one], ?_, ?_⟩
  · rw [quaternionConjugate_comp, hpN, hrN]
  · rw [quaternionConjugate_comp, hM, hrM]

/-- The actual two polynomial columns are surjective onto the ordered
orthonormal pair manifold. -/
theorem quaternionFrame_surjective : Function.Surjective quaternionFrame := by
  intro f
  obtain ⟨q, hq, h₁, h₂⟩ := exists_unitQuaternion_frame f
  let v := sphereOfQuaternion q hq
  refine ⟨v, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change firstFrameVector v = f.val.1
    apply pureQuaternion_injective
    rw [firstFrameVector_pureQuaternion, quaternion_of_sphereOfQuaternion]
    exact h₁
  · change secondFrameVector v = f.val.2
    apply pureQuaternion_injective
    rw [secondFrameVector_pureQuaternion, quaternion_of_sphereOfQuaternion]
    exact h₂

end Thesis
