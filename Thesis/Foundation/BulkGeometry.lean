module

public import Thesis.Definitions

/-! The material radius and the zero set of the normalized sextic potential. -/

public section

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace Thesis

theorem preferredTraceSq_pos (a : BulkCoefficients) : 0 < preferredTraceSq a := by
  have h2 := a.a2_pos
  have h6 := a.a6_pos
  have hdisc : a.a4 ^ 2 < a.a4 ^ 2 + 4 * a.a2 * a.a6 :=
    lt_add_of_pos_right _ (by positivity)
  have hsqrt : a.a4 < Real.sqrt (a.a4 ^ 2 + 4 * a.a2 * a.a6) :=
    (Real.lt_sqrt a.a4_pos.le).2 hdisc
  exact div_pos (by linarith only [hsqrt]) (by positivity)

theorem preferredTraceSq_equation (a : BulkCoefficients) :
    a.a6 * preferredTraceSq a ^ 2 + a.a4 * preferredTraceSq a = a.a2 := by
  have h2 := a.a2_pos
  have h6 := a.a6_pos
  let d := Real.sqrt (a.a4 ^ 2 + 4 * a.a2 * a.a6)
  have hsqrt : d ^ 2 = a.a4 ^ 2 + 4 * a.a2 * a.a6 := Real.sq_sqrt (by positivity)
  change a.a6 * ((-a.a4 + d) / (2 * a.a6)) ^ 2 +
    a.a4 * ((-a.a4 + d) / (2 * a.a6)) = a.a2
  field_simp [a.a6_pos.ne']
  nlinarith only [hsqrt]

theorem vacuumRadius_pos (a : BulkCoefficients) : 0 < vacuumRadius a :=
  Real.sqrt_pos.2 (half_pos (preferredTraceSq_pos a))

theorem two_mul_vacuumRadius_sq (a : BulkCoefficients) :
    2 * vacuumRadius a ^ 2 = preferredTraceSq a := by
  rw [vacuumRadius, Real.sq_sqrt (half_pos (preferredTraceSq_pos a)).le]
  ring

theorem vacuumRadius_equation (a : BulkCoefficients) :
    4 * a.a6 * vacuumRadius a ^ 4 + 2 * a.a4 * vacuumRadius a ^ 2 - a.a2 = 0 := by
  have h := preferredTraceSq_equation a
  rw [← two_mul_vacuumRadius_sq a] at h
  linear_combination h

theorem vacuumRadius_eq_of_pos_of_equation (a : BulkCoefficients) {r : ℝ} (hr : 0 < r)
    (heq : 4 * a.a6 * r ^ 4 + 2 * a.a4 * r ^ 2 - a.a2 = 0) :
    r = vacuumRadius a := by
  have hprod : (r - vacuumRadius a) *
      ((r + vacuumRadius a) * (4 * a.a6 * (r ^ 2 + vacuumRadius a ^ 2) + 2 * a.a4)) = 0 := by
    linear_combination heq - vacuumRadius_equation a
  have hfactor : 0 <
      (r + vacuumRadius a) * (4 * a.a6 * (r ^ 2 + vacuumRadius a ^ 2) + 2 * a.a4) := by
    have := vacuumRadius_pos a
    have h4 := a.a4_pos
    have h6 := a.a6_pos
    positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hfactor.ne')

theorem S0.trace_sq_eq_sum_sq (A : S0) :
    ((A : Tensor) ^ 2).trace = ∑ i, ∑ j, ((A : Tensor) i j) ^ 2 := by
  rw [pow_two]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hsymm : (A : Tensor) j i = (A : Tensor) i j :=
    congrFun (congrFun A.transpose_eq i) j
  rw [hsymm, pow_two]

theorem S0.trace_sq_nonneg (A : S0) : 0 ≤ ((A : Tensor) ^ 2).trace := by
  rw [A.trace_sq_eq_sum_sq]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem bulkPotential_factorization (a : BulkCoefficients) (A : S0) :
    bulkPotential a A =
      (((A : Tensor) ^ 2).trace - preferredTraceSq a) ^ 2 *
        (a.a4 / 4 + a.a6 / 6 * (((A : Tensor) ^ 2).trace + 2 * preferredTraceSq a)) +
      (a.a6' / 6) * (((A : Tensor) ^ 3).trace) ^ 2 := by
  simp only [bulkPotential]
  rw [← preferredTraceSq_equation a]
  ring

theorem bulkPotential_nonneg (a : BulkCoefficients) (A : S0) : 0 ≤ bulkPotential a A := by
  rw [bulkPotential_factorization]
  have htr := A.trace_sq_nonneg
  have hμ := preferredTraceSq_pos a
  have h4 := a.a4_pos
  have h6 := a.a6_pos
  have h6' := a.a6'_pos
  positivity

theorem bulkPotential_eq_zero_iff_traces (a : BulkCoefficients) (A : S0) :
    bulkPotential a A = 0 ↔
      ((A : Tensor) ^ 2).trace = 2 * vacuumRadius a ^ 2 ∧ ((A : Tensor) ^ 3).trace = 0 := by
  rw [two_mul_vacuumRadius_sq, bulkPotential_factorization]
  constructor
  · intro h
    have htr := A.trace_sq_nonneg
    have hμ := preferredTraceSq_pos a
    have h4 := a.a4_pos
    have h6 := a.a6_pos
    have h6' := a.a6'_pos
    have hcoefficient : 0 <
        a.a4 / 4 + a.a6 / 6 * (((A : Tensor) ^ 2).trace + 2 * preferredTraceSq a) :=
      by positivity
    have hprime : 0 < a.a6' / 6 := by positivity
    have h1 : 0 ≤ (((A : Tensor) ^ 2).trace - preferredTraceSq a) ^ 2 *
        (a.a4 / 4 + a.a6 / 6 * (((A : Tensor) ^ 2).trace + 2 * preferredTraceSq a)) :=
      mul_nonneg (sq_nonneg _) hcoefficient.le
    have h2 : 0 ≤ (a.a6' / 6) * (((A : Tensor) ^ 3).trace) ^ 2 :=
      mul_nonneg hprime.le (sq_nonneg _)
    have h1z : (((A : Tensor) ^ 2).trace - preferredTraceSq a) ^ 2 *
        (a.a4 / 4 + a.a6 / 6 * (((A : Tensor) ^ 2).trace + 2 * preferredTraceSq a)) = 0 :=
      le_antisymm (by linarith only [h, h2]) h1
    have h2z : (a.a6' / 6) * (((A : Tensor) ^ 3).trace) ^ 2 = 0 :=
      le_antisymm (by linarith only [h, h1]) h2
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp h1z).resolve_right
      hcoefficient.ne')), sq_eq_zero_iff.mp ((mul_eq_zero.mp h2z).resolve_left hprime.ne')⟩
  · rintro ⟨h2, h3⟩
    simp [h2, h3]

theorem S0.isHermitian (A : S0) : (A : Tensor).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr A.transpose_eq

theorem trace_pow_eq_sum_eigenvalues_pow {A : Tensor} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, hA.eigenvalues i ^ k := by
  let U := hA.eigenvectorUnitary
  have hdiag : A = Unitary.conjStarAlgAut ℝ Tensor U (Matrix.diagonal hA.eigenvalues) :=
    hA.spectral_theorem
  calc
    (A ^ k).trace = (Unitary.conjStarAlgAut ℝ Tensor U ((Matrix.diagonal hA.eigenvalues) ^ k)).trace := by
      rw [map_pow, ← hdiag]
    _ = ((Matrix.diagonal hA.eigenvalues) ^ k).trace := by
      rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
    _ = _ := by rw [Matrix.diagonal_pow, Matrix.trace_diagonal]; rfl

private theorem real_inner_eq_dotProduct (n m : Point) :
    inner ℝ n m = (fun i => n i) ⬝ᵥ (fun i => m i) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

private theorem orthogonal_rank_one_identities {n m : Point}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hnm : inner ℝ n m = 0) :
    let P := Matrix.vecMulVec (fun i => n i) (fun i => n i)
    let R := Matrix.vecMulVec (fun i => m i) (fun i => m i)
    P * P = P ∧ R * R = R ∧ P * R = 0 ∧ R * P = 0 ∧ P.trace = 1 ∧ R.trace = 1 := by
  have hnn : (fun i => n i) ⬝ᵥ (fun i => n i) = 1 := by
    rw [← real_inner_eq_dotProduct, real_inner_self_eq_norm_sq, hn, one_pow]
  have hmm : (fun i => m i) ⬝ᵥ (fun i => m i) = 1 := by
    rw [← real_inner_eq_dotProduct, real_inner_self_eq_norm_sq, hm, one_pow]
  rw [real_inner_eq_dotProduct] at hnm
  have hmn : (fun i => m i) ⬝ᵥ (fun i => n i) = 0 := by rwa [dotProduct_comm]
  dsimp
  simp only [Matrix.vecMulVec_mul_vecMulVec, hnn, hmm, hnm, hmn, one_smul, zero_smul,
    Matrix.vecMulVec_zero, Matrix.trace_vecMulVec, and_self]

theorem biaxialTensor_sq (a : BulkCoefficients) {n m : Point}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hnm : inner ℝ n m = 0) :
    biaxialTensor a n m ^ 2 =
      vacuumRadius a ^ 2 • (Matrix.vecMulVec (fun i => n i) (fun i => n i) +
        Matrix.vecMulVec (fun i => m i) (fun i => m i)) := by
  obtain ⟨hPP, hRR, hPR, hRP, _, _⟩ := orthogonal_rank_one_identities hn hm hnm
  rw [biaxialTensor, pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two]
  simp only [Matrix.sub_mul, Matrix.mul_sub, hPP, hRR, hPR, hRP, sub_zero, zero_sub,
    sub_neg_eq_add]

theorem biaxialTensor_cube (a : BulkCoefficients) {n m : Point}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hnm : inner ℝ n m = 0) :
    biaxialTensor a n m ^ 3 = vacuumRadius a ^ 2 • biaxialTensor a n m := by
  obtain ⟨hPP, hRR, hPR, hRP, _, _⟩ := orthogonal_rank_one_identities hn hm hnm
  rw [pow_succ, biaxialTensor_sq a hn hm hnm, biaxialTensor, Matrix.smul_mul, Matrix.mul_smul]
  simp only [Matrix.add_mul, Matrix.mul_sub, hPP, hRR, hPR, hRP, add_zero, zero_add]

theorem vacuum_traces {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    ((A : Tensor) ^ 2).trace = 2 * vacuumRadius a ^ 2 ∧ ((A : Tensor) ^ 3).trace = 0 := by
  obtain ⟨n, m, hn, hm, hnm, heq⟩ := hA
  obtain ⟨_, _, _, _, hntr, hmtr⟩ := orthogonal_rank_one_identities hn hm hnm
  constructor
  · rw [heq, biaxialTensor_sq a hn hm hnm, Matrix.trace_smul, Matrix.trace_add, hntr, hmtr]
    ring
  · rw [heq, biaxialTensor_cube a hn hm hnm, Matrix.trace_smul, ← heq, A.trace_eq_zero, smul_zero]

theorem vacuum_cube {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    (A : Tensor) ^ 3 = vacuumRadius a ^ 2 • (A : Tensor) := by
  obtain ⟨n, m, hn, hm, hnm, heq⟩ := hA
  rw [heq, biaxialTensor_cube a hn hm hnm]

private theorem opposite_pair_of_three_moments {r x y z : ℝ}
    (hz : z = 0) (hs : x + y + z = 0) (hsq : x ^ 2 + y ^ 2 + z ^ 2 = 2 * r ^ 2) :
    (x = r ∧ y = -r) ∨ (y = r ∧ x = -r) := by
  have hy : y = -x := by linarith only [hz, hs]
  have hx2 : x ^ 2 = r ^ 2 := by
    rw [hz, hy] at hsq
    nlinarith only [hsq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx2 with hpos | hneg
  · exact Or.inl ⟨hpos, by rw [hy, hpos]⟩
  · exact Or.inr ⟨by rw [hy, hneg, neg_neg], hneg⟩

private theorem spectrum_indices_of_three_moments (eig : Fin 3 → ℝ) (r : ℝ)
    (h1 : ∑ i, eig i = 0) (h2 : ∑ i, eig i ^ 2 = 2 * r ^ 2) (h3 : ∑ i, eig i ^ 3 = 0) :
    ∃ i j : Fin 3, i ≠ j ∧ ∀ k, eig k = (if k = i then r else 0) - (if k = j then r else 0) := by
  simp only [Fin.sum_univ_three] at h1 h2 h3
  have hpoly : eig 0 ^ 3 + eig 1 ^ 3 + eig 2 ^ 3 - 3 * (eig 0 * eig 1 * eig 2) =
      (eig 0 + eig 1 + eig 2) *
        (eig 0 ^ 2 + eig 1 ^ 2 + eig 2 ^ 2 - eig 0 * eig 1 - eig 0 * eig 2 - eig 1 * eig 2) := by
    ring
  have hzero : eig 0 * eig 1 * eig 2 = 0 := by
    rw [h1, h3, zero_mul] at hpoly
    linarith only [hpoly]
  have present (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hcover : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k)
      (hi : eig i = r) (hj : eig j = -r) (hk : eig k = 0) :
      ∃ i j : Fin 3, i ≠ j ∧ ∀ l, eig l = (if l = i then r else 0) - (if l = j then r else 0) := by
    refine ⟨i, j, hij, fun l => ?_⟩
    rcases hcover l with rfl | rfl | rfl
    · simp only [hi, if_true, if_neg hij, sub_zero]
    · simp only [hj, if_neg hij.symm, if_true, zero_sub]
    · simp only [hk, if_neg hik.symm, if_neg hjk.symm, sub_self]
  have ofZero (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hcover : ∀ l : Fin 3, l = i ∨ l = j ∨ l = k)
      (hk : eig k = 0) (hs : eig i + eig j + eig k = 0)
      (hsq : eig i ^ 2 + eig j ^ 2 + eig k ^ 2 = 2 * r ^ 2) :
      ∃ i j : Fin 3, i ≠ j ∧ ∀ l, eig l = (if l = i then r else 0) - (if l = j then r else 0) := by
    rcases opposite_pair_of_three_moments hk hs hsq with ⟨hi, hj⟩ | ⟨hj, hi⟩
    · exact present i j k hij hik hjk hcover hi hj hk
    · have hcover' : ∀ l : Fin 3, l = j ∨ l = i ∨ l = k := by
        intro l
        rcases hcover l with hi' | hj' | hk'
        · exact Or.inr (Or.inl hi')
        · exact Or.inl hj'
        · exact Or.inr (Or.inr hk')
      exact present j i k hij.symm hjk hik hcover' hj hi hk
  rcases mul_eq_zero.mp hzero with h01 | h2z
  · rcases mul_eq_zero.mp h01 with h0z | h1z
    · exact ofZero 1 2 0 (by decide) (by decide) (by decide) (by decide) h0z
        (by linarith only [h1]) (by linarith only [h2])
    · exact ofZero 0 2 1 (by decide) (by decide) (by decide) (by decide) h1z
        (by linarith only [h1]) (by linarith only [h2])
  · exact ofZero 0 1 2 (by decide) (by decide) (by decide) (by decide) h2z h1 h2

private theorem hermitian_eq_sum_spectral_projectors {A : Tensor} (hA : A.IsHermitian) :
    A = ∑ i, hA.eigenvalues i •
      Matrix.vecMulVec (fun j => hA.eigenvectorBasis i j) (fun j => hA.eigenvectorBasis i j) := by
  calc
    A = Unitary.conjStarAlgAut ℝ Tensor hA.eigenvectorUnitary (Matrix.diagonal hA.eigenvalues) :=
      hA.spectral_theorem
    _ = _ := by
      ext j k
      rw [Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
      simp only [Matrix.sum_apply, Matrix.mul_diagonal, Matrix.star_apply,
        star_trivial, Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.smul_apply,
        Matrix.vecMulVec_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => by ring

theorem mem_vacuum_of_traces {a : BulkCoefficients} {A : S0}
    (h2 : ((A : Tensor) ^ 2).trace = 2 * vacuumRadius a ^ 2)
    (h3 : ((A : Tensor) ^ 3).trace = 0) : A ∈ vacuum a := by
  have hA := A.isHermitian
  have h1 := trace_pow_eq_sum_eigenvalues_pow hA 1
  simp only [pow_one, A.trace_eq_zero] at h1
  rw [trace_pow_eq_sum_eigenvalues_pow hA 2] at h2
  rw [trace_pow_eq_sum_eigenvalues_pow hA 3] at h3
  obtain ⟨i, j, hij, heigs⟩ := spectrum_indices_of_three_moments hA.eigenvalues
    (vacuumRadius a) h1.symm h2 h3
  refine ⟨hA.eigenvectorBasis i, hA.eigenvectorBasis j,
    hA.eigenvectorBasis.orthonormal.norm_eq_one i, hA.eigenvectorBasis.orthonormal.norm_eq_one j,
    hA.eigenvectorBasis.inner_eq_zero hij, ?_⟩
  let P (k : Fin 3) := Matrix.vecMulVec (fun l => hA.eigenvectorBasis k l)
    (fun l => hA.eigenvectorBasis k l)
  calc
    (A : Tensor) = ∑ k, hA.eigenvalues k • P k := hermitian_eq_sum_spectral_projectors hA
    _ = ∑ k, ((if k = i then vacuumRadius a • P k else 0) -
      (if k = j then vacuumRadius a • P k else 0)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [heigs k, sub_smul]
        by_cases hi : k = i <;> by_cases hj : k = j <;> simp [hi, hj]
    _ = vacuumRadius a • P i - vacuumRadius a • P j := by
      simp [Finset.sum_sub_distrib]
    _ = _ := by rw [biaxialTensor, smul_sub]

theorem mem_vacuum_iff_traces (a : BulkCoefficients) (A : S0) :
    A ∈ vacuum a ↔
      ((A : Tensor) ^ 2).trace = 2 * vacuumRadius a ^ 2 ∧ ((A : Tensor) ^ 3).trace = 0 :=
  ⟨vacuum_traces, fun h => mem_vacuum_of_traces h.1 h.2⟩

theorem bulkPotential_eq_zero_iff (a : BulkCoefficients) (A : S0) :
    bulkPotential a A = 0 ↔ A ∈ vacuum a :=
  (bulkPotential_eq_zero_iff_traces a A).trans (mem_vacuum_iff_traces a A).symm

theorem vacuum_nonempty (a : BulkCoefficients) : (vacuum a).Nonempty := by
  have horth : Orthonormal ℝ axis :=
    EuclideanSpace.orthonormal_single
  have hn := horth.norm_eq_one (0 : Fin 3)
  have hm := horth.norm_eq_one (1 : Fin 3)
  have hnm := horth.inner_eq_zero (show (0 : Fin 3) ≠ 1 by decide)
  obtain ⟨_, _, _, _, hntr, hmtr⟩ := orthogonal_rank_one_identities hn hm hnm
  let P := biaxialTensor a (axis 0) (axis 1)
  have hP : P ∈ symmetricTraceless := by
    change Pᵀ = P ∧ P.trace = 0
    constructor
    · simp only [P, biaxialTensor, Matrix.transpose_smul, Matrix.transpose_sub,
        Matrix.transpose_vecMulVec]
    · change (biaxialTensor a (axis 0) (axis 1)).trace = 0
      rw [biaxialTensor, Matrix.trace_smul, Matrix.trace_sub, hntr, hmtr, sub_self, smul_zero]
  exact ⟨⟨P, hP⟩, axis 0, axis 1, hn, hm, hnm, rfl⟩

theorem bulkPotential_isLeast (a : BulkCoefficients) :
    IsLeast (Set.range (bulkPotential a)) 0 := by
  obtain ⟨A, hA⟩ := vacuum_nonempty a
  exact ⟨⟨A, (bulkPotential_eq_zero_iff a A).2 hA⟩,
    fun _ ⟨B, hB⟩ => hB ▸ bulkPotential_nonneg a B⟩

end Thesis

end
