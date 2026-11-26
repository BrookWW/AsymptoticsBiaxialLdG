module

public import HarmonicMaps.Target
public import Thesis.Foundation.BulkGeometry
public import Thesis.Foundation.Frobenius

/-! Compactness and local coordinates of the biaxial vacuum. -/

@[expose] public section

set_option autoImplicit false
noncomputable section

open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius

namespace Thesis

/-- The matrix trace as a continuous linear functional for the Frobenius norm. -/
def tensorTraceCLM : Tensor →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap

/-- The two polynomial trace invariants on the symmetric traceless subspace. -/
def vacuumInvariants (A : S0) : ℝ × ℝ :=
  (((A : Tensor) ^ 2).trace, ((A : Tensor) ^ 3).trace)

theorem contDiff_vacuumInvariants : ContDiff ℝ ∞ vacuumInvariants := by
  change ContDiff ℝ ∞ (fun A : S0 => (tensorTraceCLM (symmetricTraceless.subtypeL A ^ 2),
    tensorTraceCLM (symmetricTraceless.subtypeL A ^ 3)))
  fun_prop

theorem vacuum_eq_invariant_level (a : BulkCoefficients) :
    vacuum a = vacuumInvariants ⁻¹' {(2 * vacuumRadius a ^ 2, 0)} := by
  ext A
  rw [mem_vacuum_iff_traces]
  change _ ↔ vacuumInvariants A = (2 * vacuumRadius a ^ 2, 0)
  exact ⟨fun ⟨h1, h2⟩ => Prod.ext h1 h2, fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

theorem isClosed_vacuum (a : BulkCoefficients) : IsClosed (vacuum a) := by
  rw [vacuum_eq_invariant_level]
  exact isClosed_singleton.preimage contDiff_vacuumInvariants.continuous

theorem norm_sq_eq_trace_sq (A : S0) : ‖A‖ ^ 2 = ((A : Tensor) ^ 2).trace := by
  rw [norm_sq_eq_frobeniusS0, frobeniusS0, frobenius, A.transpose_eq, pow_two]

theorem vacuum_norm {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    ‖A‖ = Real.sqrt 2 * vacuumRadius a := by
  have hr := vacuumRadius_pos a
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_sq_eq_trace_sq, (vacuum_traces hA).1, mul_pow, Real.sq_sqrt (by norm_num)]

theorem isCompact_coordinateVacuum (a : BulkCoefficients) :
    IsCompact (frobeniusCoordinateEquiv '' vacuum a) := by
  let e := frobeniusCoordinateEquiv
  have hClosedImage : IsClosed (e '' vacuum a) :=
    e.toHomeomorph.isClosedMap _ (isClosed_vacuum a)
  have hInBall : e '' vacuum a ⊆ Metric.closedBall 0 (Real.sqrt 2 * vacuumRadius a) := by
    rintro _ ⟨A, hA, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, e.norm_map, vacuum_norm hA]
  exact (isCompact_closedBall _ _).of_isClosed_subset hClosedImage hInBall

theorem isCompact_vacuum (a : BulkCoefficients) : IsCompact (vacuum a) := by
  let e := frobeniusCoordinateEquiv
  have hInv : Continuous (fun x => e.symm x) := by
    simp only [e, frobeniusCoordinateEquiv_symm_apply]
    apply Continuous.subtype_mk
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> fun_prop
  simpa only [e, Set.image_image, LinearIsometryEquiv.symm_apply_apply, Set.image_id'] using
    (isCompact_coordinateVacuum a).image hInv

/-- The differential of the two trace invariants at a tensor. -/
def vacuumInvariantDerivative (A : S0) : S0 →L[ℝ] (ℝ × ℝ) :=
  ((2 : ℝ) • tensorTraceCLM.comp ((ContinuousLinearMap.mul ℝ Tensor (A : Tensor)).comp
      symmetricTraceless.subtypeL)).prod
    ((3 : ℝ) • tensorTraceCLM.comp ((ContinuousLinearMap.mul ℝ Tensor ((A : Tensor) ^ 2)).comp
      symmetricTraceless.subtypeL))

theorem vacuumInvariantDerivative_apply (A B : S0) :
    vacuumInvariantDerivative A B =
      (2 * ((A : Tensor) * (B : Tensor)).trace,
        3 * (((A : Tensor) ^ 2) * (B : Tensor)).trace) := rfl

theorem hasStrictFDerivAt_vacuumInvariants (A : S0) :
    HasStrictFDerivAt vacuumInvariants (vacuumInvariantDerivative A) A := by
  let inclusion := symmetricTraceless.subtypeL
  have hA := inclusion.hasStrictFDerivAt (x := A)
  have hSq := tensorTraceCLM.hasStrictFDerivAt.comp A (hA.mul' hA)
  have hCube := tensorTraceCLM.hasStrictFDerivAt.comp A ((hA.mul' hA).mul' hA)
  have hprod := hSq.prodMk hCube
  rw [show vacuumInvariants = (fun B : S0 =>
      (tensorTraceCLM (inclusion B * inclusion B),
        tensorTraceCLM (inclusion B * inclusion B * inclusion B))) by
    funext B
    simp only [vacuumInvariants, pow_succ, pow_zero, one_mul]
    rfl]
  refine hprod.congr_fderiv ?_
  ext B
  · change ((A : Tensor) * (B : Tensor) + (B : Tensor) * (A : Tensor)).trace =
      2 * ((A : Tensor) * (B : Tensor)).trace
    rw [Matrix.trace_add, Matrix.trace_mul_comm (B : Tensor) (A : Tensor)]
    ring
  · change (((A : Tensor) * (A : Tensor) * (B : Tensor)
      + ((A : Tensor) * (B : Tensor) + (B : Tensor) * (A : Tensor)) * (A : Tensor)).trace) =
        3 * (((A : Tensor) ^ 2) * (B : Tensor)).trace
    have hCycle₁ := Matrix.trace_mul_cycle (A : Tensor) (B : Tensor) (A : Tensor)
    have hCycle₂ : ((B : Tensor) * A * A).trace = ((A : Tensor) * A * B).trace :=
      (Matrix.trace_mul_cycle (B : Tensor) (A : Tensor) (A : Tensor)).trans hCycle₁
    rw [Matrix.add_mul, Matrix.trace_add, Matrix.trace_add, hCycle₁, hCycle₂, pow_two]
    ring

theorem fderiv_vacuumInvariants (A : S0) :
    fderiv ℝ vacuumInvariants A = vacuumInvariantDerivative A :=
  (hasStrictFDerivAt_vacuumInvariants A).hasFDerivAt.fderiv

/-- The trace-free square is the second normal direction at a vacuum tensor. -/
def traceFreeSquare (A : S0) : S0 :=
  traceFreeSymmetricPart ((A : Tensor) ^ 2)

theorem traceFreeSquare_coe (A : S0) :
    (traceFreeSquare A : Tensor) =
      (A : Tensor) ^ 2 - ((((A : Tensor) ^ 2).trace / 3) • (1 : Tensor)) := by
  have hsym : ((A : Tensor) ^ 2)ᵀ = (A : Tensor) ^ 2 := by
    rw [pow_two, Matrix.transpose_mul, A.transpose_eq]
  change (1 / 2 : ℝ) • ((A : Tensor) ^ 2 + ((A : Tensor) ^ 2)ᵀ) -
    ((((A : Tensor) ^ 2).trace / 3) • (1 : Tensor)) = _
  rw [hsym, ← two_smul ℝ ((A : Tensor) ^ 2), smul_smul]
  norm_num

theorem traceFreeSquare_coe_eq_biaxialQuadratic {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) : (traceFreeSquare A : Tensor) = biaxialQuadratic a (A : Tensor) := by
  rw [traceFreeSquare_coe, (vacuum_traces hA).1, biaxialQuadratic]

theorem vacuumInvariantDerivative_apply_frobenius (A B : S0) :
    vacuumInvariantDerivative A B = (2 * frobeniusS0 A B, 3 * frobeniusS0 (traceFreeSquare A) B) := by
  have hSq : frobeniusS0 (traceFreeSquare A) B = (((A : Tensor) ^ 2) * (B : Tensor)).trace := by
    rw [frobeniusS0, frobenius, (traceFreeSquare A).transpose_eq, traceFreeSquare_coe]
    simp only [Matrix.sub_mul, Matrix.smul_mul, one_mul, Matrix.trace_sub,
      Matrix.trace_smul, B.trace_eq_zero, smul_zero, sub_zero]
  rw [hSq, vacuumInvariantDerivative_apply, frobeniusS0, frobenius, A.transpose_eq]

theorem mem_vacuumInvariantKernel_iff (A B : S0) :
    B ∈ (vacuumInvariantDerivative A).ker ↔
      frobeniusS0 A B = 0 ∧ frobeniusS0 (traceFreeSquare A) B = 0 := by
  change vacuumInvariantDerivative A B = 0 ↔ _
  rw [vacuumInvariantDerivative_apply_frobenius]
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    change 2 * frobeniusS0 A B = 0 at h₁
    change 3 * frobeniusS0 (traceFreeSquare A) B = 0 at h₂
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h₁, h₂⟩
    simp [h₁, h₂]

theorem vacuum_trace_pow_four {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    ((A : Tensor) ^ 4).trace = 2 * vacuumRadius a ^ 4 := by
  rw [show (A : Tensor) ^ 4 = (A : Tensor) ^ 3 * (A : Tensor) by rfl, vacuum_cube hA,
    Matrix.smul_mul, ← pow_two, Matrix.trace_smul, (vacuum_traces hA).1, smul_eq_mul]
  ring

theorem vacuumInvariantDerivative_self {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) :
    vacuumInvariantDerivative A A = (4 * vacuumRadius a ^ 2, 0) := by
  rw [vacuumInvariantDerivative_apply, ← pow_two, ← pow_succ, (vacuum_traces hA).1,
    (vacuum_traces hA).2, mul_zero]
  congr 1
  ring

theorem vacuumInvariantDerivative_traceFreeSquare {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) :
    vacuumInvariantDerivative A (traceFreeSquare A) = (0, 2 * vacuumRadius a ^ 4) := by
  have h4 : (((A : Tensor) ^ 2) * ((A : Tensor) ^ 2)).trace = 2 * vacuumRadius a ^ 4 := by
    rw [← pow_add]
    exact vacuum_trace_pow_four hA
  rw [vacuumInvariantDerivative_apply, traceFreeSquare_coe]
  refine Prod.ext ?_ ?_
  · change 2 * ((A : Tensor) * ((A : Tensor) ^ 2 -
      ((((A : Tensor) ^ 2).trace / 3) • (1 : Tensor)))).trace = 0
    rw [Matrix.mul_sub, Matrix.mul_smul, mul_one, Matrix.trace_sub, Matrix.trace_smul,
      A.trace_eq_zero, ← pow_succ', (vacuum_traces hA).2, smul_zero, sub_zero, mul_zero]
  · change 3 * (((A : Tensor) ^ 2) * ((A : Tensor) ^ 2 -
      ((((A : Tensor) ^ 2).trace / 3) • (1 : Tensor)))).trace = 2 * vacuumRadius a ^ 4
    rw [Matrix.mul_sub, Matrix.mul_smul, mul_one, Matrix.trace_sub, Matrix.trace_smul,
      smul_eq_mul, h4, (vacuum_traces hA).1]
    ring

/-- The right inverse uses the two orthogonal normal directions. -/
def vacuumInvariantRightInverse (a : BulkCoefficients) (A : S0) : (ℝ × ℝ) →L[ℝ] S0 :=
  ((1 / (4 * vacuumRadius a ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight A +
    ((1 / (2 * vacuumRadius a ^ 4)) • ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (traceFreeSquare A)

theorem vacuumInvariantRightInverse_apply (a : BulkCoefficients) (A : S0) (p : ℝ × ℝ) :
    vacuumInvariantRightInverse a A p =
      (p.1 / (4 * vacuumRadius a ^ 2)) • A +
        (p.2 / (2 * vacuumRadius a ^ 4)) • traceFreeSquare A := by
  change ((1 / (4 * vacuumRadius a ^ 2)) * p.1) • A +
    ((1 / (2 * vacuumRadius a ^ 4)) * p.2) • traceFreeSquare A = _
  rw [one_div, one_div, mul_comm ((4 * vacuumRadius a ^ 2)⁻¹) p.1,
    mul_comm ((2 * vacuumRadius a ^ 4)⁻¹) p.2, ← div_eq_mul_inv, ← div_eq_mul_inv]

theorem vacuumInvariantRightInverse_isRightInverse {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) :
    Function.RightInverse (vacuumInvariantRightInverse a A) (vacuumInvariantDerivative A) := by
  intro p
  have hr := (vacuumRadius_pos a).ne'
  rw [vacuumInvariantRightInverse_apply, map_add, map_smul, map_smul,
    vacuumInvariantDerivative_self hA, vacuumInvariantDerivative_traceFreeSquare hA]
  apply Prod.ext <;> simp [smul_eq_mul] <;> field_simp [hr]

theorem vacuumInvariantDerivative_surjective {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) : Function.Surjective (vacuumInvariantDerivative A) :=
  (vacuumInvariantRightInverse_isRightInverse hA).surjective

theorem fderiv_vacuumInvariants_surjective {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) : Function.Surjective (fderiv ℝ vacuumInvariants A) := by
  rw [fderiv_vacuumInvariants]
  exact vacuumInvariantDerivative_surjective hA

/-- The first coordinate is the invariant differential, and the second lies in its kernel. -/
def vacuumInvariantSplit {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    S0 ≃L[ℝ] (ℝ × ℝ) × (vacuumInvariantDerivative A).ker :=
  ContinuousLinearEquiv.equivOfRightInverse _ _ (vacuumInvariantRightInverse_isRightInverse hA)

@[simp] theorem vacuumInvariantSplit_fst {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) (B : S0) :
    (vacuumInvariantSplit hA B).1 = vacuumInvariantDerivative A B := rfl

@[simp] theorem vacuumInvariantSplit_snd_coe {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) (B : S0) :
    ((vacuumInvariantSplit hA B).2 : S0) =
      B - vacuumInvariantRightInverse a A (vacuumInvariantDerivative A B) := rfl

/-- The action of a biaxial tensor on a vector in coordinate form. -/
theorem biaxialTensor_mulVec (a : BulkCoefficients) (n m : Point) (v : Fin 3 → ℝ) :
    biaxialTensor a n m *ᵥ v =
      vacuumRadius a • ((n.ofLp ⬝ᵥ v) • n.ofLp - (m.ofLp ⬝ᵥ v) • m.ofLp) := by
  rw [biaxialTensor, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
  simp only [op_smul_eq_smul]

theorem vacuum_eigenvectors {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    ∃ n m p : Fin 3 → ℝ, n ⬝ᵥ n = 1 ∧ m ⬝ᵥ m = 1 ∧ p ⬝ᵥ p = 1 ∧
      n ⬝ᵥ m = 0 ∧ n ⬝ᵥ p = 0 ∧ m ⬝ᵥ p = 0 ∧
      (A : Tensor) *ᵥ n = vacuumRadius a • n ∧
      (A : Tensor) *ᵥ m = (-vacuumRadius a) • m ∧
      (A : Tensor) *ᵥ p = 0 := by
  obtain ⟨n, m, hn, hm, hnm, hQ⟩ := hA
  have hnn : n.ofLp ⬝ᵥ n.ofLp = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, hn, one_pow] using
      real_inner_self_eq_norm_sq n
  have hmm : m.ofLp ⬝ᵥ m.ofLp = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, hm, one_pow] using
      real_inner_self_eq_norm_sq m
  have hmn : m.ofLp ⬝ᵥ n.ofLp = 0 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hnm
  have hnm' : n.ofLp ⬝ᵥ m.ofLp = 0 := (dotProduct_comm _ _).trans hmn
  let p := n.ofLp ⨯₃ m.ofLp
  have hnp : n.ofLp ⬝ᵥ p = 0 := dot_self_cross _ _
  have hmp : m.ofLp ⬝ᵥ p = 0 := dot_cross_self _ _
  have hpp : p ⬝ᵥ p = 1 := by
    change n.ofLp ⨯₃ m.ofLp ⬝ᵥ n.ofLp ⨯₃ m.ofLp = 1
    rw [cross_dot_cross, hnn, hmm, hnm', hmn, one_mul, mul_zero, sub_zero]
  refine ⟨n.ofLp, m.ofLp, p, hnn, hmm, hpp, hnm', hnp, hmp, ?_, ?_, ?_⟩
  · rw [hQ, biaxialTensor_mulVec, hnn, hmn, zero_smul, sub_zero, one_smul]
  · rw [hQ, biaxialTensor_mulVec, hnm', hmm, zero_smul, one_smul, zero_sub, smul_neg,
      neg_smul]
  · rw [hQ, biaxialTensor_mulVec, hnp, hmp, zero_smul, zero_smul, sub_zero, smul_zero]

private theorem isRoot_minpoly_of_mulVec {A : Tensor} {v : Fin 3 → ℝ} {l : ℝ}
    (hv : v ≠ 0) (he : A *ᵥ v = l • v) :
    (minpoly ℝ A).IsRoot l := by
  rw [← Matrix.minpoly_toLin']
  apply Module.End.isRoot_of_hasEigenvalue
  exact Module.End.hasEigenvalue_of_hasEigenvector
    (show Module.End.HasEigenvector (Matrix.toLin' A) l v from
      ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩)

theorem vacuum_minpoly {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    minpoly ℝ (A : Tensor) =
      Polynomial.X ^ 3 - Polynomial.C (vacuumRadius a ^ 2) * Polynomial.X := by
  classical
  open Polynomial in
  let r := vacuumRadius a
  let p : Polynomial ℝ := X ^ 3 - C (r ^ 2) * X
  have hr : 0 < r := vacuumRadius_pos a
  have hpAnn : aeval (A : Tensor) p = 0 := by
    simp only [p, map_sub, map_pow, aeval_X, map_mul, aeval_C, sub_eq_zero]
    rw [← map_pow (algebraMap ℝ Tensor), Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul]
    exact vacuum_cube hA
  have hPowDeg : (X ^ 3 : Polynomial ℝ).natDegree = 3 := natDegree_X_pow 3
  have hLinearDeg : (C (r ^ 2) * X).natDegree = 1 := natDegree_C_mul_X _ (pow_ne_zero _ hr.ne')
  have hNatLt : (C (r ^ 2) * X).natDegree < (X ^ 3 : Polynomial ℝ).natDegree := by
    rw [hLinearDeg, hPowDeg]
    decide
  have hpDeg : p.natDegree = 3 := (natDegree_sub_eq_left_of_natDegree_lt hNatLt).trans hPowDeg
  have hpMonic : p.Monic := (monic_X_pow 3).sub_of_left (degree_lt_degree hNatLt)
  have hMinMonic : (minpoly ℝ (A : Tensor)).Monic := minpoly.monic (Matrix.isIntegral _)
  obtain ⟨n, m, z, hnn, hmm, hzz, _, _, _, hEn, hEm, hEz⟩ := vacuum_eigenvectors hA
  have hnRoot := isRoot_minpoly_of_mulVec (by rintro rfl; simp at hnn) hEn
  have hmRoot := isRoot_minpoly_of_mulVec (by rintro rfl; simp at hmm) hEm
  have hzRoot := isRoot_minpoly_of_mulVec (by rintro rfl; simp at hzz)
    (show (A : Tensor) *ᵥ z = (0 : ℝ) • z by rw [hEz, zero_smul])
  have hRoots : ({r, -r, 0} : Finset ℝ) ⊆ (minpoly ℝ (A : Tensor)).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hMinMonic.ne_zero]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hnRoot
    · exact hmRoot
    · exact hzRoot
  have hcard : ({r, -r, 0} : Finset ℝ).card = 3 := by
    have hSign : r ≠ -r := by linarith only [hr]
    have hNeg : -r ≠ 0 := neg_ne_zero.mpr hr.ne'
    simp [Finset.card_insert_of_notMem, hSign, hr.ne', hNeg]
  have hMinDeg : 3 ≤ (minpoly ℝ (A : Tensor)).natDegree := by
    calc
      3 = ({r, -r, 0} : Finset ℝ).card := hcard.symm
      _ ≤ (minpoly ℝ (A : Tensor)).roots.toFinset.card := Finset.card_le_card hRoots
      _ ≤ (minpoly ℝ (A : Tensor)).roots.card := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots' _
  exact (eq_of_monic_of_dvd_of_natDegree_le hMinMonic hpMonic
    (minpoly.dvd ℝ _ hpAnn) (hpDeg.le.trans hMinDeg)).symm

theorem vacuum_hasEigenvalue_iff {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) (μ : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' (A : Tensor)) μ ↔
      μ = vacuumRadius a ∨ μ = -vacuumRadius a ∨ μ = 0 := by
  rw [Module.End.hasEigenvalue_iff_isRoot, Matrix.minpoly_toLin', vacuum_minpoly hA]
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C]
  rw [show μ ^ 3 - vacuumRadius a ^ 2 * μ =
    (μ - vacuumRadius a) * ((μ + vacuumRadius a) * μ) by ring]
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- In an orthonormal eigenframe of a vacuum tensor, each eigenspace is the indicated line. -/
theorem vacuum_eigenspaces {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    ∃ n m p : Fin 3 → ℝ, n ⬝ᵥ n = 1 ∧ m ⬝ᵥ m = 1 ∧ p ⬝ᵥ p = 1 ∧
      n ⬝ᵥ m = 0 ∧ n ⬝ᵥ p = 0 ∧ m ⬝ᵥ p = 0 ∧
      Module.End.eigenspace (Matrix.toLin' (A : Tensor)) (vacuumRadius a) = Submodule.span ℝ {n} ∧
      Module.End.eigenspace (Matrix.toLin' (A : Tensor)) (-vacuumRadius a) = Submodule.span ℝ {m} ∧
      Module.End.eigenspace (Matrix.toLin' (A : Tensor)) 0 = Submodule.span ℝ {p} := by
  let f : Module.End ℝ (Fin 3 → ℝ) := Matrix.toLin' (A : Tensor)
  let r := vacuumRadius a
  have hr : 0 < r := vacuumRadius_pos a
  obtain ⟨n, m, p, hnn, hmm, hpp, hnm, hnp, hmp, hn, hm, hp⟩ := vacuum_eigenvectors hA
  have hn₀ : n ≠ 0 := by rintro rfl; simp at hnn
  have hm₀ : m ≠ 0 := by rintro rfl; simp at hmm
  have hp₀ : p ≠ 0 := by rintro rfl; simp at hpp
  have hnMem : n ∈ f.eigenspace r := Module.End.mem_eigenspace_iff.mpr hn
  have hmMem : m ∈ f.eigenspace (-r) := Module.End.mem_eigenspace_iff.mpr hm
  have hpMem : p ∈ f.eigenspace 0 := by
    apply Module.End.mem_eigenspace_iff.mpr
    rw [zero_smul]
    exact hp
  have h₁₂ : Disjoint (f.eigenspace r) (f.eigenspace (-r)) :=
    f.eigenspaces_iSupIndep.pairwiseDisjoint (show r ≠ -r by linarith only [hr])
  have h₀ : Disjoint (f.eigenspace 0) (f.eigenspace r ⊔ f.eigenspace (-r)) := by
    have hz : (0 : ℝ) ∉ ({r, -r} : Set ℝ) := by simp [hr.ne, hr.ne']
    simpa only [iSup_pair] using f.eigenspaces_iSupIndep.disjoint_biSup hz
  have hSum := Submodule.finrank_sup_add_finrank_inf_eq (f.eigenspace r) (f.eigenspace (-r))
  rw [h₁₂.eq_bot, finrank_bot, add_zero] at hSum
  have hBound := Submodule.finrank_add_finrank_le_of_disjoint h₀
  rw [hSum, Module.finrank_pi, Fintype.card_fin] at hBound
  have hPos {v : Fin 3 → ℝ} {μ : ℝ} (hv : v ∈ f.eigenspace μ) (hv₀ : v ≠ 0) :
      0 < Module.finrank ℝ (f.eigenspace μ) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hv⟩, fun h => hv₀ (congrArg Subtype.val h)⟩
  have hnPos := hPos hnMem hn₀
  have hmPos := hPos hmMem hm₀
  have hpPos := hPos hpMem hp₀
  have hnDim : Module.finrank ℝ (f.eigenspace r) = 1 := by omega
  have hmDim : Module.finrank ℝ (f.eigenspace (-r)) = 1 := by omega
  have hpDim : Module.finrank ℝ (f.eigenspace 0) = 1 := by omega
  exact ⟨n, m, p, hnn, hmm, hpp, hnm, hnp, hmp,
    eq_span_singleton_of_mem_of_finrank_eq_one hnDim hnMem hn₀,
    eq_span_singleton_of_mem_of_finrank_eq_one hmDim hmMem hm₀,
    eq_span_singleton_of_mem_of_finrank_eq_one hpDim hpMem hp₀⟩

theorem vacuumInvariantKernel_finrank {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    Module.finrank ℝ (vacuumInvariantDerivative A).ker = 3 := by
  letI : FiniteDimensional ℝ S0 := Module.Finite.of_basis frobeniusBasis
  have hS0 : Module.finrank ℝ S0 = 5 :=
    frobeniusCoordinateEquiv.toLinearEquiv.finrank_eq.trans finrank_euclideanSpace_fin
  let d : S0 →ₗ[ℝ] (ℝ × ℝ) := (vacuumInvariantDerivative A).toLinearMap
  have hTop : d.range = ⊤ := LinearMap.range_eq_top.mpr (vacuumInvariantDerivative_surjective hA)
  have hRank := LinearMap.finrank_range_add_finrank_ker d
  rw [hTop, finrank_top, Module.finrank_prod, Module.finrank_self, hS0] at hRank
  change Module.finrank ℝ d.ker = 3
  omega

section LocalCharts

open Set Filter
open scoped Manifold Topology

private abbrev VacuumAmbient := EuclideanSpace ℝ (Fin 5)
private abbrev VacuumModel := EuclideanSpace ℝ (Fin 3)
private abbrev VacuumNormals := ℝ × ℝ

private theorem mem_coordinateVacuum_iff {a : BulkCoefficients} {x : VacuumAmbient} :
    x ∈ frobeniusCoordinateEquiv '' vacuum a ↔ frobeniusCoordinateEquiv.symm x ∈ vacuum a :=
  ⟨fun ⟨A, hA, he⟩ => by rwa [← he, LinearIsometryEquiv.symm_apply_apply],
    fun h => ⟨_, h, LinearIsometryEquiv.apply_symm_apply _ _⟩⟩

private def kernelModelEquiv {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    (vacuumInvariantDerivative A).ker ≃L[ℝ] VacuumModel := by
  letI : FiniteDimensional ℝ S0 := Module.Finite.of_basis frobeniusBasis
  exact ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ)
    (E := ↥(vacuumInvariantDerivative A).ker) (F := VacuumModel)
    ((vacuumInvariantKernel_finrank hA).trans finrank_euclideanSpace_fin.symm)

private def vacuumChartLinearEquiv {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    VacuumAmbient ≃L[ℝ] VacuumModel × VacuumNormals :=
  frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.trans
    ((vacuumInvariantSplit hA).trans ((ContinuousLinearEquiv.prodComm ℝ VacuumNormals
      (vacuumInvariantDerivative A).ker).trans ((kernelModelEquiv hA).prodCongr
        (ContinuousLinearEquiv.refl ℝ VacuumNormals))))

private def vacuumChartMap {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a)
    (x : VacuumAmbient) : VacuumModel × VacuumNormals :=
  ((vacuumChartLinearEquiv hA x).1,
    vacuumInvariants (frobeniusCoordinateEquiv.symm x) - (2 * vacuumRadius a ^ 2, 0))

private theorem contDiff_vacuumChartMap {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    ContDiff ℝ ∞ (vacuumChartMap hA) := by
  unfold vacuumChartMap
  exact (vacuumChartLinearEquiv hA).contDiff.fst.prodMk
    ((contDiff_vacuumInvariants.comp
      frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.contDiff).sub contDiff_const)

private theorem hasFDerivAt_vacuumChartMap {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) :
    HasFDerivAt (vacuumChartMap hA)
      (vacuumChartLinearEquiv hA : VacuumAmbient →L[ℝ] VacuumModel × VacuumNormals)
      (frobeniusCoordinateEquiv A) := by
  let x := frobeniusCoordinateEquiv A
  let eInv : VacuumAmbient →L[ℝ] S0 :=
    frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let P : VacuumAmbient →L[ℝ] VacuumModel :=
    (ContinuousLinearMap.fst ℝ VacuumModel VacuumNormals).comp
      (vacuumChartLinearEquiv hA).toContinuousLinearMap
  have hi := eInv.hasFDerivAt (x := x)
  have hA' : eInv x = A := LinearIsometryEquiv.symm_apply_apply _ _
  have hD :
      HasFDerivAt vacuumInvariants (vacuumInvariantDerivative A) (eInv x) :=
    hA'.symm ▸ (hasStrictFDerivAt_vacuumInvariants A).hasFDerivAt
  have hk := (P.hasFDerivAt (x := x)).prodMk ((hD.comp x hi).sub_const (2 * vacuumRadius a ^ 2, 0))
  refine hk.congr_fderiv ?_
  ext y <;> rfl

private theorem exists_vacuumAmbientChart {a : BulkCoefficients} {x : VacuumAmbient}
    (hx : x ∈ frobeniusCoordinateEquiv '' vacuum a) :
    ∃ e : OpenPartialHomeomorph VacuumAmbient (VacuumModel × VacuumNormals),
      x ∈ e.source ∧
      (∀ y : VacuumAmbient, (e y).2 = vacuumInvariants (frobeniusCoordinateEquiv.symm y) -
        (2 * vacuumRadius a ^ 2, 0)) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let A := frobeniusCoordinateEquiv.symm x
  have hA : A ∈ vacuum a := mem_coordinateVacuum_iff.1 hx
  let f := vacuumChartMap hA
  let L := vacuumChartLinearEquiv hA
  have hf : ContDiff ℝ ∞ f := contDiff_vacuumChartMap hA
  have hfd : HasFDerivAt f (L : VacuumAmbient →L[ℝ] VacuumModel × VacuumNormals) x := by
    have hh := hasFDerivAt_vacuumChartMap hA
    have hAx : frobeniusCoordinateEquiv A = x := LinearIsometryEquiv.apply_symm_apply _ _
    exact hAx ▸ hh
  let e := hf.contDiffAt.toOpenPartialHomeomorph _ hfd (by simp)
  have hex : x ∈ e.source :=
    hf.contDiffAt.mem_toOpenPartialHomeomorph_source hfd (by simp)
  have hfder : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := 0) (by simp)).continuous
  have hnhds : {y : VacuumAmbient | (fderiv ℝ f y).IsInvertible} ∈ 𝓝 x := by
    have hL := L.nhds
    rw [← hfd.fderiv] at hL
    exact hfder.continuousAt.preimage_mem_nhds hL
  obtain ⟨s, hs, hOpen, hxs⟩ := mem_nhds_iff.1 hnhds
  let e' := e.restrOpen s hOpen
  have heSource : e'.source = e.source ∩ s := e.restrOpen_source s hOpen
  have heCoe : (e' : VacuumAmbient → VacuumModel × VacuumNormals) = f := rfl
  refine ⟨e', heSource ▸ ⟨hex, hxs⟩, ?_, heCoe.symm ▸ hf.contDiffOn, ?_⟩
  · intro y
    rw [heCoe]
    rfl
  · intro z hz
    have hzSource : e'.symm z ∈ s := (show e'.symm z ∈ e.source ∩ s from
      heSource ▸ e'.map_target hz).2
    obtain ⟨Lz, hLz⟩ := hs hzSource
    have hDz := (hf.differentiable (by simp) (e'.symm z)).hasFDerivAt
    apply ContDiffAt.contDiffWithinAt
    apply e'.contDiffAt_symm (f₀' := Lz) hz
    · simpa only [heCoe, hLz] using hDz
    · rw [heCoe]
      exact hf.contDiffAt

private abbrev VacuumCarrier (a : BulkCoefficients) :=
  ↥(frobeniusCoordinateEquiv '' vacuum a)

private def vacuumAmbientChart {a : BulkCoefficients} (x : VacuumCarrier a) :
    OpenPartialHomeomorph VacuumAmbient (VacuumModel × VacuumNormals) :=
  Classical.choose (exists_vacuumAmbientChart x.property)

private theorem vacuumAmbientChart_spec {a : BulkCoefficients} (x : VacuumCarrier a) :
    x.val ∈ (vacuumAmbientChart x).source ∧
      (∀ y : VacuumAmbient, (vacuumAmbientChart x y).2 =
        vacuumInvariants (frobeniusCoordinateEquiv.symm y) - (2 * vacuumRadius a ^ 2, 0)) ∧
      ContDiffOn ℝ ∞ (vacuumAmbientChart x) (vacuumAmbientChart x).source ∧
      ContDiffOn ℝ ∞ (vacuumAmbientChart x).symm (vacuumAmbientChart x).target :=
  Classical.choose_spec (exists_vacuumAmbientChart x.property)

private theorem mem_coordinateVacuum_iff_chart_snd_eq_zero {a : BulkCoefficients}
    (x : VacuumCarrier a) (y : VacuumAmbient) :
    y ∈ frobeniusCoordinateEquiv '' vacuum a ↔ (vacuumAmbientChart x y).2 = 0 := by
  rw [mem_coordinateVacuum_iff, vacuum_eq_invariant_level, (vacuumAmbientChart_spec x).2.1 y]
  exact sub_eq_zero.symm

private def vacuumSliceInverse {a : BulkCoefficients} (x : VacuumCarrier a) (u : VacuumModel) :
    VacuumCarrier a := by
  classical
  exact if h : (u, (0 : VacuumNormals)) ∈ (vacuumAmbientChart x).target then
    ⟨(vacuumAmbientChart x).symm (u, 0), (mem_coordinateVacuum_iff_chart_snd_eq_zero x _).2
      (congrArg Prod.snd ((vacuumAmbientChart x).right_inv h))⟩
  else x

private theorem vacuumSliceInverse_coe {a : BulkCoefficients} {x : VacuumCarrier a}
    {u : VacuumModel} (hu : (u, (0 : VacuumNormals)) ∈ (vacuumAmbientChart x).target) :
    (vacuumSliceInverse x u).val = (vacuumAmbientChart x).symm (u, 0) := by
  simp only [vacuumSliceInverse, dif_pos hu]

/-- The chart of the vacuum is the zero-normal slice of an ambient chart. -/
private def vacuumSliceChart {a : BulkCoefficients} (x : VacuumCarrier a) :
    OpenPartialHomeomorph (VacuumCarrier a) VacuumModel := by
  let e := vacuumAmbientChart x
  refine {
    toFun := fun y => (e y.val).1
    invFun := vacuumSliceInverse x
    source := Subtype.val ⁻¹' e.source
    target := (fun u => (u, (0 : VacuumNormals))) ⁻¹' e.target
    map_source' := ?_
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    continuousOn_toFun := ?_
    continuousOn_invFun := ?_
    open_source := e.open_source.preimage continuous_subtype_val
    open_target := e.open_target.preimage (continuous_id.prodMk continuous_const) }
  · intro y hy
    change ((e y.val).1, 0) ∈ e.target
    rw [← (mem_coordinateVacuum_iff_chart_snd_eq_zero x y.val).1 y.property, Prod.eta]
    exact e.map_source hy
  · intro u hu
    change (vacuumSliceInverse x u).val ∈ e.source
    rw [vacuumSliceInverse_coe hu]
    exact e.map_target hu
  · intro y hy
    apply Subtype.ext
    have hsnd := (mem_coordinateVacuum_iff_chart_snd_eq_zero x y.val).1 y.property
    have ht : ((e y.val).1, (0 : VacuumNormals)) ∈ e.target := by
      rw [← hsnd, Prod.eta]
      exact e.map_source hy
    rw [vacuumSliceInverse_coe ht, ← hsnd, Prod.eta]
    exact e.left_inv hy
  · intro u hu
    rw [vacuumSliceInverse_coe hu]
    exact congrArg Prod.fst (e.right_inv hu)
  · exact continuous_fst.comp_continuousOn
      (e.continuousOn.comp continuous_subtype_val.continuousOn (mapsTo_preimage _ _))
  · rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact (e.symm.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (mapsTo_preimage _ _)).congr (fun _ hu => vacuumSliceInverse_coe hu)

@[implicit_reducible] private def vacuumChartedSpace (a : BulkCoefficients) :
    ChartedSpace VacuumModel (VacuumCarrier a)
    where
  atlas := range vacuumSliceChart
  chartAt := vacuumSliceChart
  mem_chart_source x := (vacuumAmbientChart_spec x).1
  chart_mem_atlas x := ⟨x, rfl⟩

private theorem contDiffOn_vacuumTransition {a : BulkCoefficients} (x y : VacuumCarrier a) :
    ContDiffOn ℝ ∞ ((vacuumSliceChart x).symm ≫ₕ vacuumSliceChart y)
      ((vacuumSliceChart x).symm ≫ₕ vacuumSliceChart y).source := by
  let s := ((vacuumSliceChart x).symm ≫ₕ vacuumSliceChart y).source
  have hx : MapsTo (fun u : VacuumModel => (u, (0 : VacuumNormals))) s
      (vacuumAmbientChart x).target := fun _ hu => hu.1
  have hy : MapsTo (fun u : VacuumModel => (vacuumAmbientChart x).symm (u, 0)) s
      (vacuumAmbientChart y).source := by
    intro u hu
    change (vacuumAmbientChart x).symm (u, 0) ∈ (vacuumAmbientChart y).source
    rw [← vacuumSliceInverse_coe (hx hu)]
    exact hu.2
  have hinv := (vacuumAmbientChart_spec x).2.2.2.comp
    (contDiff_id.prodMk contDiff_const).contDiffOn hx
  refine ((vacuumAmbientChart_spec y).2.2.1.fst.comp hinv hy).congr ?_
  intro u hu
  change (vacuumAmbientChart y (vacuumSliceInverse x u).val).1 = _
  rw [vacuumSliceInverse_coe (hx hu)]
  rfl

private theorem vacuumIsManifold (a : BulkCoefficients) :
    letI := vacuumChartedSpace a
    IsManifold 𝓘(ℝ, VacuumModel) ∞ (VacuumCarrier a) := by
  letI := vacuumChartedSpace a
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ : e ∈ range vacuumSliceChart := he
  obtain ⟨y, rfl⟩ : e' ∈ range vacuumSliceChart := he'
  simpa only [mfld_simps, inter_univ] using contDiffOn_vacuumTransition x y

private theorem vacuumAmbient_maximalAtlas {a : BulkCoefficients} (x : VacuumCarrier a)
    (L : VacuumAmbient ≃L[ℝ] VacuumModel × VacuumNormals) :
    (vacuumAmbientChart x).transHomeomorph L.symm.toHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℝ, VacuumAmbient) ∞ VacuumAmbient := by
  apply (contDiffGroupoid ∞ 𝓘(ℝ, VacuumAmbient)).mem_maximalAtlas_of_mem_groupoid
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · simp only [contDiffPregroupoid, mfld_simps, inter_univ]
    change ContDiffOn ℝ ∞ (L.symm ∘ vacuumAmbientChart x) (vacuumAmbientChart x).source
    exact L.symm.contDiff.comp_contDiffOn (vacuumAmbientChart_spec x).2.2.1
  · simp only [contDiffPregroupoid, mfld_simps, inter_univ]
    change ContDiffOn ℝ ∞ ((vacuumAmbientChart x).symm ∘ L) (L ⁻¹' (vacuumAmbientChart x).target)
    exact (vacuumAmbientChart_spec x).2.2.2.comp L.contDiff.contDiffOn
      (mapsTo_preimage L (vacuumAmbientChart x).target)

private theorem vacuumIsSmoothEmbedding (a : BulkCoefficients) :
    letI := vacuumChartedSpace a
    Manifold.IsSmoothEmbedding 𝓘(ℝ, VacuumModel) 𝓘(ℝ, VacuumAmbient) ∞
      (Subtype.val : VacuumCarrier a → VacuumAmbient) := by
  letI := vacuumChartedSpace a
  letI := vacuumIsManifold a
  refine ⟨Manifold.IsImmersionOfComplement.isImmersion (F := VacuumNormals) ?_,
    Topology.IsEmbedding.subtypeVal⟩
  intro x
  let L := vacuumChartLinearEquiv (mem_coordinateVacuum_iff.1 x.property)
  let e := vacuumAmbientChart x
  let codChart := e.transHomeomorph L.symm.toHomeomorph
  have hx := (vacuumAmbientChart_spec x).1
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts L.symm (vacuumSliceChart x) codChart
    hx hx (IsManifold.chart_mem_maximalAtlas x) (vacuumAmbient_maximalAtlas x L) (fun _ h => h) ?_
  intro u hu
  have huChart : u ∈ (vacuumSliceChart x).target := by
    simpa only [OpenPartialHomeomorph.extend_target, mfld_simps, inter_univ] using hu
  have hu' : (u, (0 : VacuumNormals)) ∈ e.target := huChart
  change L.symm (e (vacuumSliceInverse x u).val) = L.symm (u, 0)
  rw [vacuumSliceInverse_coe hu', e.right_inv hu']

/-- The actual vacuum in Frobenius coordinates is a compact smooth embedded 3-manifold. -/
@[no_expose] def vacuumCompactSmoothEmbeddedTarget (a : BulkCoefficients) :
    HarmonicMaps.CompactSmoothEmbeddedTarget 5 where
  dimension := 3
  carrierSet := frobeniusCoordinateEquiv '' vacuum a
  nonempty := (vacuum_nonempty a).image _
  isCompact := isCompact_coordinateVacuum a
  chartedSpace := vacuumChartedSpace a
  isManifold := vacuumIsManifold a
  isSmoothEmbedding := vacuumIsSmoothEmbedding a

@[simp] theorem vacuumCompactSmoothEmbeddedTarget_dimension (a : BulkCoefficients) :
    (vacuumCompactSmoothEmbeddedTarget a).dimension = 3 := by
  unfold vacuumCompactSmoothEmbeddedTarget
  rfl

@[simp] theorem vacuumCompactSmoothEmbeddedTarget_carrierSet (a : BulkCoefficients) :
    (vacuumCompactSmoothEmbeddedTarget a).carrierSet = frobeniusCoordinateEquiv '' vacuum a := by
  unfold vacuumCompactSmoothEmbeddedTarget
  rfl

theorem mem_vacuumCompactSmoothEmbeddedTarget_iff {a : BulkCoefficients}
    {x : EuclideanSpace ℝ (Fin 5)} :
    x ∈ (vacuumCompactSmoothEmbeddedTarget a).carrierSet ↔
      frobeniusCoordinateEquiv.symm x ∈ vacuum a := by
  rw [vacuumCompactSmoothEmbeddedTarget_carrierSet, mem_coordinateVacuum_iff]

end LocalCharts

end Thesis

end

end
