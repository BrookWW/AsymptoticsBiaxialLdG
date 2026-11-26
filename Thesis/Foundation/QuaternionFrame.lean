module

public import Mathlib.Analysis.Quaternion
public import Thesis.Foundation.VacuumFrame

/-! Quaternion conjugation and the actual two director columns. -/

@[expose] public section

noncomputable section

open scoped Matrix.Norms.Frobenius Quaternion

namespace Thesis

/-- A spatial vector as an imaginary quaternion. -/
def pureQuaternion (x : Point) : ℍ := ⟨0, x 0, x 1, x 2⟩

/-- Imaginary coefficients, in the order of the spatial coordinates. -/
def quaternionImaginaryVector (q : ℍ) : Point := WithLp.toLp 2 ![q.imI, q.imJ, q.imK]

theorem quaternionImaginaryVector_pureQuaternion (x : Point) :
    quaternionImaginaryVector (pureQuaternion x) = x := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

theorem pureQuaternion_quaternionImaginaryVector {q : ℍ} (hq : q.re = 0) :
    pureQuaternion (quaternionImaginaryVector q) = q := by
  ext <;> simp [pureQuaternion, quaternionImaginaryVector, hq]

theorem pureQuaternion_injective : Function.Injective pureQuaternion :=
  (show Function.LeftInverse quaternionImaginaryVector pureQuaternion from
    quaternionImaginaryVector_pureQuaternion).injective

theorem norm_pureQuaternion (x : Point) : ‖pureQuaternion x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [pow_two ‖pureQuaternion x‖, ← Quaternion.normSq_eq_norm_mul_self,
    Quaternion.normSq_def', EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [pureQuaternion, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, add_assoc]

theorem inner_eq_neg_re_pureQuaternion_mul (x y : Point) :
    inner ℝ x y = -(pureQuaternion x * pureQuaternion y).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm, dotProduct, Fin.sum_univ_three]
  simp only [pureQuaternion, Quaternion.re_mul, mul_zero, zero_sub]
  ring

theorem pureQuaternion_anticommute_of_inner_eq_zero {x y : Point} (h : inner ℝ x y = 0) :
    pureQuaternion x * pureQuaternion y = -(pureQuaternion y * pureQuaternion x) := by
  have hre : (pureQuaternion x * pureQuaternion y).re = 0 := by
    have h' := inner_eq_neg_re_pureQuaternion_mul x y
    linarith only [h, h']
  ext
  · rw [hre]
    have hyx := (inner_eq_neg_re_pureQuaternion_mul y x)
    rw [real_inner_comm, h] at hyx
    rw [Quaternion.re_neg]
    exact hyx
  · simp only [pureQuaternion, Quaternion.imI_mul, Quaternion.imI_neg]; ring
  · simp only [pureQuaternion, Quaternion.imJ_mul, Quaternion.imJ_neg]; ring
  · simp only [pureQuaternion, Quaternion.imK_mul, Quaternion.imK_neg]; ring

/-- The first two quaternion units agree with the first two coordinate vectors. -/
def firstQuaternionUnit : ℍ := ⟨0, 1, 0, 0⟩

def secondQuaternionUnit : ℍ := ⟨0, 0, 1, 0⟩

theorem norm_firstQuaternionUnit : ‖firstQuaternionUnit‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1
  rw [pow_two ‖firstQuaternionUnit‖, ← Quaternion.normSq_eq_norm_mul_self]
  norm_num [Quaternion.normSq_def', firstQuaternionUnit]

theorem norm_secondQuaternionUnit : ‖secondQuaternionUnit‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1
  rw [pow_two ‖secondQuaternionUnit‖, ← Quaternion.normSq_eq_norm_mul_self]
  norm_num [Quaternion.normSq_def', secondQuaternionUnit]

theorem imaginaryUnit_square {q : ℍ} (hre : q.re = 0) (hNorm : ‖q‖ = 1) : q * q = -1 := by
  have hStar := Quaternion.star_eq_neg.2 hre
  have h := Quaternion.self_mul_star q
  rw [hStar, mul_neg, Quaternion.normSq_eq_norm_mul_self, hNorm, mul_one] at h
  exact neg_eq_iff_eq_neg.mp h

theorem quaternionUnit_star_mul {q : ℍ} (hNorm : ‖q‖ = 1) : star q * q = 1 := by
  rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, hNorm, mul_one]
  rfl

theorem quaternionUnit_mul_star {q : ℍ} (hNorm : ‖q‖ = 1) : q * star q = 1 := by
  rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self, hNorm, mul_one]
  rfl

/-- Conjugation by a unit quaternion, using its star inverse. -/
def quaternionConjugate (q x : ℍ) : ℍ := q * x * star q

theorem quaternionConjugate_re_eq_zero (q : ℍ) {x : ℍ} (hx : x.re = 0) :
    (quaternionConjugate q x).re = 0 := by
  apply Quaternion.star_eq_neg.1
  simp only [quaternionConjugate, star_mul, star_star, Quaternion.star_eq_neg.2 hx,
    mul_neg, neg_mul, mul_assoc]

theorem quaternionConjugate_mul (q : ℍ) (hq : ‖q‖ = 1) (x y : ℍ) :
    quaternionConjugate q (x * y) = quaternionConjugate q x * quaternionConjugate q y := by
  unfold quaternionConjugate
  rw [show q * x * star q * (q * y * star q) =
    q * x * (star q * q) * y * star q by simp only [mul_assoc], quaternionUnit_star_mul hq, mul_one, mul_assoc q x y]

theorem quaternionConjugate_comp (q p x : ℍ) :
    quaternionConjugate (q * p) x = quaternionConjugate q (quaternionConjugate p x) := by
  simp only [quaternionConjugate, star_mul, mul_assoc]

/-- The frozen first column is quaternion conjugation of the first unit. -/
theorem firstFrameVector_pureQuaternion (v : QuaternionCoordinates) :
    pureQuaternion (firstFrameVector v) =
      quaternionConjugate (Quaternion.linearIsometryEquivTuple.symm v) firstQuaternionUnit := by
  rw [show Quaternion.linearIsometryEquivTuple.symm v = (⟨v 0, v 1, v 2, v 3⟩ : ℍ) from rfl]
  ext <;> simp [firstFrameVector, pureQuaternion, quaternionConjugate, firstQuaternionUnit] <;> ring

/-- The frozen second column is quaternion conjugation of the second unit. -/
theorem secondFrameVector_pureQuaternion (v : QuaternionCoordinates) :
    pureQuaternion (secondFrameVector v) =
      quaternionConjugate (Quaternion.linearIsometryEquivTuple.symm v) secondQuaternionUnit := by
  rw [show Quaternion.linearIsometryEquivTuple.symm v = (⟨v 0, v 1, v 2, v 3⟩ : ℍ) from rfl]
  ext <;> simp [secondFrameVector, pureQuaternion, quaternionConjugate, secondQuaternionUnit] <;> ring

theorem quaternionTuple_symm_norm_eq_one (v : Sphere3) :
    ‖Quaternion.linearIsometryEquivTuple.symm (v : QuaternionCoordinates)‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map]
  simpa only [Metric.mem_sphere, dist_zero_right] using v.property

/-- The exact ordered frame of a point of the frozen unit three-sphere. -/
def quaternionFrame (v : Sphere3) : VacuumFrame := by
  let q := Quaternion.linearIsometryEquivTuple.symm (v : QuaternionCoordinates)
  have hq : ‖q‖ = 1 := quaternionTuple_symm_norm_eq_one v
  refine ⟨(firstFrameVector v, secondFrameVector v), ?_, ?_, ?_⟩
  · rw [← norm_pureQuaternion, firstFrameVector_pureQuaternion]
    simp only [quaternionConjugate, ← show q = Quaternion.linearIsometryEquivTuple.symm
      (v : QuaternionCoordinates) from rfl, norm_mul, Quaternion.norm_star, hq, norm_firstQuaternionUnit,
      mul_one]
  · rw [← norm_pureQuaternion, secondFrameVector_pureQuaternion]
    simp only [quaternionConjugate, ← show q = Quaternion.linearIsometryEquivTuple.symm
      (v : QuaternionCoordinates) from rfl, norm_mul, Quaternion.norm_star, hq, norm_secondQuaternionUnit,
      mul_one]
  · rw [inner_eq_neg_re_pureQuaternion_mul, firstFrameVector_pureQuaternion, secondFrameVector_pureQuaternion]
    change -(quaternionConjugate q firstQuaternionUnit * quaternionConjugate q secondQuaternionUnit).re = 0
    rw [← quaternionConjugate_mul q hq, quaternionConjugate_re_eq_zero q (show
      (firstQuaternionUnit * secondQuaternionUnit).re = 0 from by norm_num [firstQuaternionUnit, secondQuaternionUnit]),
      neg_zero]

theorem cover_eq_quaternionFrameProjection (a : BulkCoefficients) (v : Sphere3) :
    cover a v = (vacuumFrameProjection a (quaternionFrame v)).val := by
  exact traceFreeSymmetricPart_of_S0 (vacuumFrameProjection a (quaternionFrame v)).val

end Thesis
