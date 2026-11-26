module

public import Thesis.MeasureGeometry.StressBounds
public import Mathlib.Analysis.Matrix.Spectrum

/-! Frobenius duality and the rank-one stress projection. -/

public section

open Matrix Unitary
open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace Thesis

theorem abs_tensor_entry_le_frobenius_norm (T : Tensor) (i j : Fin 3) : |T i j| ≤ ‖T‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1
  rw [sq_abs, norm_sq_eq_frobenius, frobenius_eq_sum]
  calc
    (T i j) ^ 2 ≤ ∑ l, T i l * T i l := by
      rw [pow_two]
      exact Finset.single_le_sum (fun l _ => mul_self_nonneg (T i l)) (Finset.mem_univ j)
    _ ≤ ∑ k, ∑ l, T k l * T k l :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => mul_self_nonneg (T k l))
        (Finset.mem_univ i)

theorem abs_frobenius_le_norm_mul_norm (A B : Tensor) : |frobenius A B| ≤ ‖A‖ * ‖B‖ := by
  let coordinates (T : Tensor) : EuclideanSpace ℝ (Fin 3 × Fin 3) :=
    WithLp.toLp 2 fun i => T i.1 i.2
  have hnorm (T : Tensor) : ‖coordinates T‖ = ‖T‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.real_norm_sq_eq, norm_sq_eq_frobenius, frobenius_eq_sum, Fintype.sum_prod_type]
    simp only [coordinates, pow_two]
  have hpair : inner ℝ (coordinates A) (coordinates B) = frobenius A B := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, frobenius_eq_sum]
    simp only [coordinates, star_trivial, dotProduct, Fintype.sum_prod_type, mul_comm]
  rw [← hpair, ← hnorm A, ← hnorm B]
  exact abs_real_inner_le_norm _ _

theorem frobenius_one_left (T : Tensor) : frobenius (1 : Tensor) T = T.trace := by
  simp [frobenius]

theorem frobenius_norm_one : ‖(1 : Tensor)‖ = Real.sqrt 3 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
  rw [norm_sq_eq_frobenius, frobenius_one_left, Real.sq_sqrt (by norm_num)]
  simp

theorem trace_le_sqrt_three_mul_norm (T : Tensor) : T.trace ≤ Real.sqrt 3 * ‖T‖ := by
  have h := abs_frobenius_le_norm_mul_norm (1 : Tensor) T
  rw [frobenius_one_left, frobenius_norm_one] at h
  exact (le_abs_self _).trans h

theorem tensorQuadratic_eq_dotProduct (T : Tensor) (v : Point) :
    tensorQuadratic T v = v.ofLp ⬝ᵥ (T *ᵥ v.ofLp) := by
  simp only [tensorQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem tensorQuadratic_of_mulVec_eq_smul {T : Tensor} {v : Point} {l : ℝ}
    (h : T *ᵥ v.ofLp = l • v.ofLp) : tensorQuadratic T v = l * ‖v‖ ^ 2 := by
  rw [tensorQuadratic_eq_dotProduct, h, EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, pow_two]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem tensorQuadratic_smul (k : ℝ) (T : Tensor) (v : Point) :
    tensorQuadratic (k • T) v = k * tensorQuadratic T v := by
  simp only [tensorQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem tensorQuadratic_one (v : Point) : tensorQuadratic (1 : Tensor) v = ‖v‖ ^ 2 := by
  rw [tensorQuadratic_eq_dotProduct, Matrix.one_mulVec, EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct, pow_two]

/-- Stress relative to the energy density. The identity is chosen on the
set of zero energy, which has zero mass for the weighted energy measure. -/
@[expose] noncomputable def elasticStressDensity (a : BulkCoefficients) (ε : ElasticScale)
    (A : S0) (D : Gradient) : Tensor :=
  let e := energyDensity a ε A D
  if e = 0 then 1 else e⁻¹ • elasticStress a ε A D

theorem elasticStressDensity_bounds (a : BulkCoefficients) (ε : ElasticScale) (A : S0)
    (D : Gradient) :
    let T := elasticStressDensity a ε A D
    Tᵀ = T ∧ 1 ≤ T.trace ∧ ‖T‖ ≤ 2 ∧
      ∀ v : Point, tensorQuadratic T v ≤ ‖v‖ ^ 2 := by
  let e := energyDensity a ε A D
  obtain ⟨hs, ht, hn, hq⟩ := elasticStress_bounds a ε A D
  have he : 0 ≤ e := by linarith only [hn, norm_nonneg (elasticStress a ε A D)]
  change let T := if e = 0 then (1 : Tensor) else e⁻¹ • elasticStress a ε A D
    Tᵀ = T ∧ 1 ≤ T.trace ∧ ‖T‖ ≤ 2 ∧ ∀ v : Point, tensorQuadratic T v ≤ ‖v‖ ^ 2
  by_cases heq : e = 0
  · simp only [heq, if_true, Matrix.transpose_one, true_and, frobenius_norm_one, tensorQuadratic_one,
      le_refl, forall_const, and_true]
    constructor
    · simp
    · exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  · simp only [if_neg heq]
    have h0 := inv_nonneg.mpr he
    have hcancel : e⁻¹ * e = 1 := inv_mul_cancel₀ heq
    refine ⟨by rw [Matrix.transpose_smul, hs], ?_, ?_, ?_⟩
    · rw [Matrix.trace_smul, smul_eq_mul, ← hcancel]
      exact mul_le_mul_of_nonneg_left ht h0
    · rw [norm_smul, Real.norm_of_nonneg h0, ← mul_one (2 : ℝ), ← hcancel]
      rw [← mul_assoc, mul_comm 2, mul_assoc]
      exact mul_le_mul_of_nonneg_left hn h0
    · intro v
      rw [tensorQuadratic_smul]
      calc
        _ ≤ e⁻¹ * (e * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left (hq v) h0
        _ = _ := by rw [← mul_assoc, hcancel, one_mul]

theorem energyDensity_smul_elasticStressDensity (a : BulkCoefficients) (ε : ElasticScale)
    (A : S0) (D : Gradient) :
    energyDensity a ε A D • elasticStressDensity a ε A D = elasticStress a ε A D := by
  let e := energyDensity a ε A D
  change e • (if e = 0 then (1 : Tensor) else e⁻¹ • elasticStress a ε A D) = _
  by_cases he : e = 0
  · have hn := (elasticStress_bounds a ε A D).2.2.1
    change ‖elasticStress a ε A D‖ ≤ 2 * e at hn
    rw [he, mul_zero] at hn
    rw [he, zero_smul, norm_le_zero_iff.mp hn]
  · rw [if_neg he, smul_smul, mul_inv_cancel₀ he, one_smul]

/-- A symmetric rank-one stress with trace at least one and quadratic form
bounded above by the identity is itself an orthogonal line projection. -/
theorem isLineProjection_of_rank_one_stress (T : Tensor) (hs : Tᵀ = T)
    (htr : 1 ≤ T.trace) (hq : ∀ v : Point, tensorQuadratic T v ≤ ‖v‖ ^ 2)
    (hr : T.rank = 1) : T * T = T ∧ T.trace = 1 ∧ ‖T‖ = 1 := by
  classical
  have hT : T.IsHermitian := (Matrix.conjTranspose_eq_transpose_of_trivial T).trans hs
  let e : Fin 3 → ℝ := hT.eigenvalues
  have hcard : Fintype.card {i // e i ≠ 0} = 1 := hT.rank_eq_card_non_zero_eigs ▸ hr
  obtain ⟨j, hj⟩ := Fintype.card_eq_one_iff.1 hcard
  have hzero {i : Fin 3} (hi : i ≠ j.val) : e i = 0 := by
    by_contra h
    exact hi (congrArg Subtype.val (hj ⟨i, h⟩))
  have htrace : T.trace = e j.val := by
    rw [hT.trace_eq_sum_eigenvalues]
    change (∑ i, e i) = e j.val
    exact Finset.sum_eq_single j.val (fun i _ hi => hzero hi) (fun h => (h (Finset.mem_univ _)).elim)
  let v : Point := hT.eigenvectorBasis j.val
  have hv : ‖v‖ = 1 := hT.eigenvectorBasis.orthonormal.norm_eq_one j.val
  have hqj := hq v
  rw [tensorQuadratic_of_mulVec_eq_smul (hT.mulVec_eigenvectorBasis j.val), hv,
    one_pow, mul_one] at hqj
  have hej : e j.val = 1 := le_antisymm hqj (htrace ▸ htr)
  let d : Tensor := Matrix.diagonal e
  have hdd : d * d = d := by
    rw [show d = Matrix.diagonal e by rfl, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i = j.val
    · subst i
      simp [hej]
    · simp [hzero hi]
  have hspec : T = conjStarAlgAut ℝ _ hT.eigenvectorUnitary d := by
    simpa only [d, e, RCLike.ofReal_real_eq_id, Function.id_comp] using hT.spectral_theorem
  have hproj : T * T = T := by
    calc
      T * T = conjStarAlgAut ℝ _ hT.eigenvectorUnitary (d * d) :=
        (congrArg₂ (· * ·) hspec hspec).trans (map_mul _ _ _).symm
      _ = T := (congrArg (conjStarAlgAut ℝ _ hT.eigenvectorUnitary) hdd).trans hspec.symm
  have htrace₁ := htrace.trans hej
  refine ⟨hproj, htrace₁, ?_⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1)).1
  rw [norm_sq_eq_frobenius, frobenius, hs, hproj, htrace₁, one_pow]

end Thesis

end
